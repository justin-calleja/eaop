%%
%% Copyright (C) 2013 by calleja.justin@gmail.com (Justin Calleja)
%%
%% Licensed under the Apache License, Version 2.0 (the "License");
%% you may not use this file except in compliance with the License.
%% You may obtain a copy of the License at
%%
%%     http://www.apache.org/licenses/LICENSE-2.0
%%
%% Unless required by applicable law or agreed to in writing, software
%% distributed under the License is distributed on an "AS IS" BASIS,
%% WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
%% See the License for the specific language governing permissions and
%% limitations under the License. 
%%

%% Author: Justin Calleja
%% Description: All other modules are meant to use this module for access/creation/manipulation of the
%% data structures used in this project.

-module(eaopcore).

%% -export([get_globals/1, prepare_aspects_for_weaving/1, is_instrumentable_fun/1, exists_send_ptcut/1]).

-compile(export_all).

-include("../include/eaopglobals.hrl").
-include("../include/unit_testing.hrl").

-define(casetf(Expr, True, False), case Expr of true -> True; false -> False end).

-export_type([aop_el/0, aspect/0, globals/0]).
-export_type([advice_t/0]).

-record(id, {val :: string()}).
-record(mf, {m :: atom(), f :: atom()}).
-record(send_msg, {msg :: string()}).
-record(receive_msg, {msg :: string()}).
-record(functiondef, {
	m :: string() | atom(), f :: string() | atom(), a :: string() | integer()
}).
-record(args, {
	exp :: string(), condition :: str_undef()
}).
-record(within, {scope :: scope()}).
-record(not_within, {scope :: scope()}).
-record(spawned, {scope :: scope()}).
-record(registered, {names :: [str_atom()]}).
-record(trap_exit, {val = false :: boolean()}).
-record(visibility, {val = global :: visibility()}).
-record(type, {val :: advice_t()}).
-record(ptcuts,	{val :: [str_pointcut()]}).

-record(aspect, {attribs = [] :: [aspect_attr()]}).
-record(advice, {attribs = [] :: [advice_attr()]}).
-record(pointcut, {attribs = [] :: [pointcut_attr()]}).

-record(globals, {
	aspects = [] :: [aspect()],
	advices = [] :: [advice()],
	pointcuts = [] :: [pointcut()]
}).

-type advice_t() :: before | 'after' | after_throw | after_final | around.

-type str_atom() :: string() | atom().
-type str_byte() :: string() | byte().
-type str_undef() :: string() | undefined.
-type scope() :: [{Module::str_atom(), Function::str_atom(), Arity::str_byte()}].
-type visibility() :: local | public | global.
-type str_pointcut() :: string() | pointcut().
%% -type mf() :: #mf{}.

-type aspect_attr() ::
		  #id{} 			|
		  advice() 			|
		  pointcut().

-type advice_attr() ::
		  #id{} 			|
		  #type{} 			|
		  #mf{} 			|
		  #ptcuts{}.

%% Note: the following are mutually exclusive: call, send_msg, or receive_msg. They determine the pointcut's type.
%% Note: within, not_within, spawned, registered, trap_exit, and visibility are not yet implemented. They may be used but they will be ignored.
-type pointcut_attr() ::
		  #id{} 			|	%%		The id is used to refer to the pointcut.
		  #send_msg{}		|	%% 		Defines which sent messages to advice.
		  #receive_msg{} 	| 	%% 		Defines which received messages to advice.
		  #functiondef{} 			|	%% 		Defines which function definitions to advise
		  #args{} 			| 	%% 		Defines the format in which the argument/s of the functiondef/send/recieve need to
								%% 	be in in order for the advice to take place. Optionally, a condition may be
								%% 	specified over the variables defined in the format.
		  #within{} 		|	%%		Defines the scope within which this pointcut applies. Any join points outside
								%% 	of the defined scope which match this pointcut will be ignored.
		  #not_within{} 	|	%%		Defines the scope within which this pointcut is not allowed to apply.
								%% 	Any join points inside the defined scope which match this pointcut will be ignored.
		  #spawned{} 		|	%%		Defines a set of functions. Assuming a join point matches this pointcut,
								%%	the join point will not be adviced unless the process executing the join point
								%% 	was spawned by one of the functions defined in this set.
		  #registered{} 	|	%%		Defines a set of registered names. Assuming a join point matches this pointcut,
								%%	the join point will not be adviced unless the process executing the join point is
								%% 	registered under a name in this set.
		  #trap_exit{}		|	%%		Requires the process executing the join point to be a system process.
								%%	Assuming a join point matches this pointcut, the join point will not be
								%%	adviced unless the process executing the join point is trapping exits.
		  #visibility{}.		%%		Only applicable to functiondef pointcuts. Determines whether the functiondef being selected must be
								%% 	local to the module, exported from the module (public), or it can be both (global).

-opaque aspect() :: #aspect{}.
-opaque advice() :: #advice{}.
-opaque pointcut() :: #pointcut{}.

-opaque aop_el() :: aspect() | advice() | pointcut().
-opaque aop_attr() :: aspect_attr() | advice_attr() | pointcut_attr().

-opaque globals() :: #globals{}.

%%
%% Exported functions:
%%

get_advice_module(Advice) when is_record(Advice, advice) ->
	Fun = fun_advice_attrib_selector(mf),
	case Fun(Advice) of
		no_attr ->
			undefined;
		MFAttr ->
			MFAttr#mf.m
	end.

get_advice_function(Advice) when is_record(Advice, advice) ->
	Fun = fun_advice_attrib_selector(mf),
	case Fun(Advice) of
		no_attr ->
			undefined;
		MFAttr ->
			MFAttr#mf.f
	end.

-spec get_applicable_advices(StrModuleName::string(), StrFunctionName::string(), Arity::integer(), Aspects::[aspect()]) -> ApplicableAdvices::[advice()].
%% @doc Returns the advices in Aspects which are applicable to the function with name StrFunctionName, in the module with name StrModuleName, with an arity of Arity.
%% Applicability is determined by the functiondef attribute in pointcuts.
get_applicable_advices(StrModuleName, StrFunctionName, Arity, Aspects) ->
	FdAdvicePointcut = foldl_pointcuts(fun fd_advice_pointcut/4, Aspects),
	lists:foldl(
		fun({FdAdvice, FdPointcut}, ApplicableAdvicesAcc) ->
				case mfa_satisfies_fdpointcut(StrModuleName, StrFunctionName, Arity, FdPointcut) of
					true ->
						[FdAdvice | ApplicableAdvicesAcc];
					false ->
						ApplicableAdvicesAcc
				end
		end, [], FdAdvicePointcut).

get_advices_by_type(Advices, Type) ->
	Fun = fun_advice_attrib_selector(type),
	lists:foldl(
		fun(Advice, SameTypeAdvicesAcc) ->
				case Fun(Advice) of
					no_attr ->
						SameTypeAdvicesAcc;
					TypeAttr ->
						case TypeAttr#type.val == Type of
							true ->
								[Advice | SameTypeAdvicesAcc];
							false ->
								SameTypeAdvicesAcc
						end
				end
		end, [], Advices).

-spec fd_advice_pointcut(aspect(), advice(), pointcut(), [{advice(), pointcut()}]) -> [{advice(), pointcut()}].
%% @doc This function is passed to foldl_pointcuts/2. If Pointcut is of type functiondef, {Advice, Pointcut} is appended to the accumulator PointcutAcc. Otherwise the accumulator is returned.
fd_advice_pointcut(_Aspect, Advice, Pointcut, PointcutAcc) ->
	Fun = fun_pointcut_attrib_selector(functiondef),
	case Fun(Pointcut) of
		no_attr ->
			PointcutAcc;
		_FunctiondefAttr ->
			[{Advice, Pointcut} | PointcutAcc]
	end.

mfa_satisfies_fdpointcut(StrModuleName, StrFunctionName, Arity, FdPointcut) ->
	Fun = fun_pointcut_attrib_selector(functiondef),
	FdAttr = Fun(FdPointcut),
	case m_satisfies_fdpointcut(StrModuleName, FdAttr#functiondef.m) of
		true ->
			case f_satisfies_fdpointcut(StrFunctionName, FdAttr#functiondef.f) of
				true ->
					a_satisfies_fdpointcut(Arity, FdAttr#functiondef.a);
				false ->
					false
			end;
		false ->
			false
	end.

m_satisfies_fdpointcut(StrModuleName, FdModule) when is_atom(FdModule) ->
	list_to_atom(StrModuleName) == FdModule;
m_satisfies_fdpointcut(StrModuleName, FdModule) when is_list(FdModule) ->
	match(StrModuleName, FdModule).

f_satisfies_fdpointcut(StrFunctionName, FdFunction) when is_atom(FdFunction) ->
	list_to_atom(StrFunctionName) == FdFunction;
f_satisfies_fdpointcut(StrFunctionName, FdFunction) when is_list(FdFunction) ->
	match(StrFunctionName, FdFunction).

-spec a_satisfies_fdpointcut(Arity::integer(), FdArity::integer()) -> boolean();
		(integer(), string()) -> boolean().
%% @doc When FdArity is a string(), it is assumed that it is a regex
a_satisfies_fdpointcut(Arity, FdArity) when is_integer(FdArity) ->
	Arity == FdArity;
a_satisfies_fdpointcut(Arity, FdArity) when is_list(FdArity) ->
	match(integer_to_list(Arity), FdArity).

match(Str, Regex) ->
	{ok, Pattern} = re:compile(Regex),
	Options = [notempty,{capture,none}],
	re:run(Str, Pattern, Options) == match.

%% @doc Applies Fun to every pointcut within every advice within every aspect in the given Aspects.
foldl_pointcuts(Fun, Aspects) ->
	Result = lists:foldl(
		fun(Aspect, AspectAcc) ->
				Advices = aadvice(Aspect),
				FoldlOverAdvices = lists:foldl(
					fun(Advice, AdviceAcc) ->
							Pointcuts = advpointcuts(Advice),
							FoldlOverPointcuts = lists:foldl(
									fun(Pointcut, PointcutAcc) ->
											Fun(Aspect, Advice, Pointcut, PointcutAcc)
									end, [], Pointcuts),
							[FoldlOverPointcuts | AdviceAcc]
					end, [], Advices),
				[FoldlOverAdvices | AspectAcc]
		end, [], Aspects),
	lists:flatten(Result).


is_aspect(Aspect) -> is_record(Aspect, aspect).

is_advice(Advice) -> is_record(Advice, advice).

is_pointcut(Pointcut) -> is_record(Pointcut, pointcut).

is_aspect_attrib(Attrib) when not is_tuple(Attrib) -> false;
is_aspect_attrib(Attrib) ->	lists:member(element(1, Attrib), [id, advice, pointcut]).

is_advice_attrib(Attrib) when not is_tuple(Attrib) -> false;
is_advice_attrib(Attrib) -> lists:member(element(1, Attrib), [id, type, mf, ptcuts]).

is_pointcut_attrib(Attrib) when not is_tuple(Attrib) -> false;
is_pointcut_attrib(Attrib) -> lists:member(element(1, Attrib), [id, send_msg, receive_msg, functiondef, args, within, not_within, spawned, registered, trap_exit, visibility]).

-spec add(AopEl::aop_el(), Attrib::aop_attr()) -> aop_el();
			(AopEl::aop_el(), Attribs::[aop_attr()]) -> aop_el().
%% @doc Adds Attrib to AopEl if the Attrib is a valid attribute of AopEl, and returns the new aop_el().
%% Returns AopEl otherwise. Can also handle a list of aop_attr(). In this case, the attributes are added
%% from left to right.
add(AopEl, []) ->
	AopEl;
add(AopEl, [Attrib | Attribs]) ->
	add(add(AopEl, Attrib), Attribs);
add(#aspect{attribs = AspectAttribs} = Aspect, AspectAttrib) ->
	?casetf(is_aspect_attrib(AspectAttrib), #aspect{attribs = [AspectAttrib | AspectAttribs]}, Aspect);
add(#advice{attribs = AdviceAttribs} = Advice, AdviceAttrib) ->
	?casetf(is_advice_attrib(AdviceAttrib), #advice{attribs = [AdviceAttrib | AdviceAttribs]}, Advice);
add(#pointcut{attribs = PointcutAttribs} = Pointcut, PointcutAttrib) ->
	?casetf(is_pointcut_attrib(PointcutAttrib), #pointcut{attribs = [PointcutAttrib | PointcutAttribs]}, Pointcut).

-spec aspect() -> aspect().
aspect() -> #aspect{}.

-spec advice() -> advice().
advice() -> #advice{}.

-spec pointcut() -> pointcut().
pointcut() -> #pointcut{}.

aspect(Attribs) when is_list(Attribs) ->
	?casetf(lists:all(fun is_aspect_attrib/1, Attribs), #aspect{attribs = Attribs}, invalid).

advice(Attribs) when is_list(Attribs) ->
	?casetf(lists:all(fun is_advice_attrib/1, Attribs), #advice{attribs = Attribs}, invalid).

pointcut(Attribs) when is_list(Attribs) ->
	?casetf(lists:all(fun is_pointcut_attrib/1, Attribs), #pointcut{attribs = Attribs}, invalid).

id(Id) when is_atom(Id) -> #id{val = atom_to_list(Id)};
id(Id) when is_integer(Id) -> #id{val = integer_to_list(Id)};
id(Id) -> #id{val = Id}.

mf(Module, Function) -> #mf{m = Module, f = Function}.

send_msg(Msg) -> #send_msg{msg = Msg}.

receive_msg(Msg) -> #receive_msg{msg = Msg}.

%% call(Module, Function, Arity) -> #call{m = Module, f = Function, a = Arity}.

functiondef(Module, Function, Arity) -> #functiondef{m = Module, f = Function, a = Arity}.

args(Exp, Condition) -> #args{exp = Exp, condition = Condition}.

within(Scope) -> #within{scope = Scope}.

not_within(Scope) -> #not_within{scope = Scope}.

spawned(Scope) -> #spawned{scope = Scope}.

registered(Names) -> #registered{names = Names}.

trap_exit(Bool) -> #trap_exit{val = Bool}.

visibility(Visibility) -> #visibility{val = Visibility}.

type(Type) -> #type{val = Type}.

ptcuts(Ptcuts) -> #ptcuts{val = Ptcuts}.

%% -spec is_instrumentable_fun(Aspect::aspect()) -> fun((Form::erl_parse:abstract_form()) -> boolean()).
%% %% @doc Returns a function which when applied to an abstract_form() determines whether that form needs to be
%% %% instrumented. This decision is taken according to the information encapsulated within the given Aspect.
%% is_instrumentable_fun(Aspect = #aspect{attribs = AspectAttribs}) ->
%% 	fun({function, _LineNum, FunName, Arity, Clauses}) ->
%% 			todo;
%% 	   (SendForm = {op, _LineNum, '!', Pid, Msg}) ->
%% 			%% Get all send_msg attribs in all pointcuts within all advices of given Aspect.
%% 			%% These send_msg attribs have a value - a string() encoding the format in which a message must be in order for it to be instrumented.
%% 			%% Pass these values to SRMATCHER and if the matcher returns true at least once, then SendForm needs to be instrumented.
%% 			Advices = aadvice(AspectAttribs),
%% 			FunAttribSelector = fun_pointcut_attrib_selector(send_msg),
%% 			SendMsgAttribs = apply_attr_selector(FunAttribSelector, Advices),
%% 			lists:any(
%% 				fun(#send_msg{msg = SendMsg}) ->
%% 						?SRMATCHER:send_matcher(Msg, SendMsg, [srmatcher:send_form(SendForm)])
%% 				end, SendMsgAttribs);
%% 	   (ReceiveForm = {'receive', _LineNum, _Clauses}) ->
%% 			todo;
%% 	   (_Form) ->
%% 			false
%% 	end.

exists_send_ptcut(#aspect{attribs = AspectAttribs}) ->
	lists:any(fun(Advice) -> exists_ptcut_attr(Advice, send_msg) end, aadvice(AspectAttribs));
exists_send_ptcut(Advice) when is_record(Advice, advice) ->
	exists_ptcut_attr(Advice, send_msg).

exists_receive_ptcut(#aspect{attribs = AspectAttribs}) ->
	lists:any(fun(Advice) -> exists_ptcut_attr(Advice, receive_msg) end, aadvice(AspectAttribs));
exists_receive_ptcut(Advice) when is_record(Advice, advice) ->
	exists_ptcut_attr(Advice, receive_msg).

exists_functiondef_ptcut(#aspect{attribs = AspectAttribs}) ->
	lists:any(fun(Advice) -> exists_ptcut_attr(Advice, functiondef) end, aadvice(AspectAttribs));
exists_functiondef_ptcut(Advice) when is_record(Advice, advice) ->
	exists_ptcut_attr(Advice, functiondef).

-spec exists_ptcut_attr(Aspect::aspect(), Attr::atom()) -> boolean();
			(Advice::advice(), Attr::atom()) -> boolean().
%% @doc Returns 'true' when at least one advice in the given Aspect has a pointcut which contains an attribute of type Attr.
%% Returns 'true' if the given Advice has a pointcut which contains an attribute of type Attr. Returns 'false' otherwise.
exists_ptcut_attr(#aspect{attribs = AspectAttribs}, Attr) ->
	lists:any(fun(Advice) -> exists_ptcut_attr(Advice, Attr) end, aadvice(AspectAttribs));
exists_ptcut_attr(#advice{attribs = AdviceAttribs}, Attr) ->
	Fun_PtcutAttribSelector = fun_pointcut_attrib_selector(Attr),
	Pointcuts = advpointcuts(AdviceAttribs),
	Pred =
		fun(Pointcut) ->
			case Fun_PtcutAttribSelector(Pointcut) of
				no_attr -> false;
				_ -> true
			end
		end,
	lists:any(Pred, Pointcuts).

-spec remove_non_pointcuts(List::[term()]) -> [pointcut()].
%% @doc Removes anything which is not a pointcut() in the given List and returns the result.
remove_non_pointcuts(StrPointcuts) ->
	lists:filter(
		fun(StrPointcut) ->	is_record(StrPointcut, pointcut) end,
		StrPointcuts).

-spec get_globals([aop_el()]) -> globals().
get_globals(AopEls) ->
	get_globals(AopEls, #globals{}).


-spec prepare_aspects_for_weaving(globals()) -> [aspect()].
prepare_aspects_for_weaving(Globals) ->
	[prepare_aspect_for_weaving(Aspect, Globals) || Aspect <- gaspects(Globals)].

%%
%% Not sure whether to export or make local:
%%

-spec gaspects(globals()) -> [aspect()].
gaspects(#globals{aspects = Aspects}) ->
	Aspects.

-spec gadvices(globals()) -> [advice()].
gadvices(#globals{advices = Advices}) ->
	Advices.

-spec gpointcuts(globals()) -> [pointcut()].
gpointcuts(#globals{pointcuts = Pointcuts}) ->
	Pointcuts.

-spec apointcuts(aspect()) -> [pointcut()];
			([aspect_attr()]) -> [pointcut()].
apointcuts(#aspect{attribs = AspectAttribs}) ->
	apointcuts(AspectAttribs);
apointcuts(AspectAttribs) ->
	[P || P <- AspectAttribs, is_record(P, pointcut)].

-spec aadvice(aspect()) -> [advice()];
			([aspect_attr()]) -> [advice()].
aadvice(#aspect{attribs = AspectAttribs}) ->
	aadvice(AspectAttribs);
aadvice(AspectAttribs) ->
	[Adv || Adv <- AspectAttribs, is_record(Adv, advice)].

-spec advpointcuts_with_refs(advice()) -> [str_pointcut()];
			([advice_attr()]) -> [str_pointcut()].
%% @doc Extracts the value of the ptcuts attribute in the given advice.
advpointcuts_with_refs(#advice{attribs = AdviceAttribs}) ->
	advpointcuts_with_refs(AdviceAttribs);
advpointcuts_with_refs(AdviceAttribs) ->
	case lists:keyfind(ptcuts, 1, AdviceAttribs) of
		#ptcuts{val = PtcutsValue} ->
			PtcutsValue;
		false ->
			[]
	end.

-spec advpointcuts(advice()) -> [pointcut()];
			([advice_attr()]) -> [pointcut()].
%% @doc Extracts the value of the ptcuts attribute in the given advice.
advpointcuts(Advice) ->
	remove_non_pointcuts(advpointcuts_with_refs(Advice)).

-spec fun_pointcut_attrib_selector(Attrib::atom()) -> fun((Pointcut::pointcut()) -> pointcut_attr() | no_attr).
%% @doc Returns a function which takes a Pointcut as an argument and returns a pointcut_attr() or no_attr.
%% pointcut_attr() is returned if the given Pointcut contains an attribute with key Attrib. no_attr is returned
%% if Pointcut does not contain an attribute with key Attrib.
fun_pointcut_attrib_selector(AttribName) ->
	fun(#pointcut{attribs = PointcutAttribs}) ->
			case lists:keyfind(AttribName, 1, PointcutAttribs) of
				false ->
					no_attr;
				Attrib ->
					Attrib
			end
	end.

fun_advice_attrib_selector(AttribName) ->
	fun(#advice{attribs = AdviceAttribs}) ->
			case lists:keyfind(AttribName, 1, AdviceAttribs) of
				false ->
					no_attr;
				Attrib ->
					Attrib
			end
	end.

%% get_send_msg/1 and get_receive_msg/1 can probably be deleted later. Their use is suppose to have been substituted by get_msg_format/1.
-spec get_send_msg(Pointcut::pointcut()) -> string() | undefined.
%% @doc Returns the given Pointcut's send_msg format string or 'undefined' if the Pointcut does not have the send_msg attribute.
get_send_msg(Pointcut) when is_record(Pointcut, pointcut) ->
	Selector = fun_pointcut_attrib_selector(send_msg),
	case Selector(Pointcut) of
		no_attr ->
			undefined;
		SendMsg ->
			SendMsg#send_msg.msg
	end.

-spec get_msg_format(Pointcut::pointcut()) -> string() | undefined.
%% @doc Returns the message format of the given Pointcut's first occurrence of send_msg or receive_msg or undefined if Pointcut does not contain neither a send_msg attribute nor a receive_msg attribute.
get_msg_format(#pointcut{attribs = PointcutAttribs} = Pointcut) when is_record(Pointcut, pointcut) ->
	case ?UTIL:find_first(fun(Attrib) -> is_record(Attrib, send_msg) orelse is_record(Attrib, receive_msg) end, PointcutAttribs) of
		undefined ->
			undefined;
		FoundAttrib when is_record(FoundAttrib, send_msg) ->
			FoundAttrib#send_msg.msg;
		FoundAttrib when is_record(FoundAttrib, receive_msg) ->
			FoundAttrib#receive_msg.msg
	end.

-spec get_type(Advice::advice()) -> advice_t() | undefined.
get_type(Advice) when is_record(Advice, advice) ->
	Selector = fun_advice_attrib_selector(type),
	case Selector(Advice) of
		no_attr ->
			undefined;
		Type ->
			Type#type.val
	end.

-spec get_mf(Advice::advice()) -> {Module::atom(), Function::atom()} | undefined.
get_mf(Advice) when is_record(Advice, advice) ->
	Selector = fun_advice_attrib_selector(mf),
	case Selector(Advice) of
		no_attr ->
			undefined;
		Mf ->
			{Mf#mf.m, Mf#mf.f}
	end.

%%
%% Local functions:
%%

%% fun((Elem::T) -> boolean()),

%% apply_attr_selector

-spec to_remove_apply_attr_selector(AttrSelector::fun((pointcut()) -> pointcut_attr() | no_attr), Advices::[advice()]) -> [pointcut_attr()].
%% @doc Applies AttrSelector to each pointcut within each advice of the given Advices and returns a list containing
%% the result of each application of AttrSelector when such a result is not the atom 'no_attr'.
to_remove_apply_attr_selector(Fun, Advices) ->
	DirtyPointcutAttribs =
		[hd(hd([[Fun(Pointcut) || Pointcut <- Pointcuts, is_record(Pointcut, pointcut)] || Pointcuts <- advpointcuts(Advice)]))
			|| Advice <- Advices],
	lists:filter(fun(PointcutAttrib) -> PointcutAttrib =/= no_attr end, DirtyPointcutAttribs).

-spec get_globals([aop_el()], globals()) -> globals().
get_globals([], Globals) ->
	Globals;
get_globals([GAspect | AopEls], Globals) when is_record(GAspect, aspect) ->
	get_globals(AopEls, Globals#globals{aspects = lists:append(gaspects(Globals), [GAspect])});
get_globals([GAdvice | AopEls], Globals) when is_record(GAdvice, advice) ->
	get_globals(AopEls, Globals#globals{advices = lists:append(gadvices(Globals), [GAdvice])});
get_globals([GPointcut | AopEls], Globals) when is_record(GPointcut, pointcut) ->
	get_globals(AopEls, Globals#globals{pointcuts = lists:append(gpointcuts(Globals), [GPointcut])}).

-spec prepare_aspect_for_weaving(aspect(), globals()) -> aspect().
%% @doc Preparing an aspect for weaving involves carrying out two operations on an aspect.
%% <ol>
%% 		<li>Importing global configuration of local pointcuts and advices - the pointcut/advice import stage.</li>
%%		<li>Resolving the local/global pointcuts to which local advices refer to by id - the pointcut resolution stage.</li>
%% 	</ol>
%% @throws {unresolvable_ptcut, string()}
prepare_aspect_for_weaving(Aspect, Globals) ->
	AspectAttribsWithImports =
		lists:map(
		  	fun(Advice) when is_record(Advice, advice) ->
					import_global_conf(Advice, Globals);
			   (Pointcut) when is_record(Pointcut, pointcut) ->
					import_global_conf(Pointcut, Globals);
			   (AspectAttrib) ->
					AspectAttrib
		  	end,
			get_attribs(Aspect)),
	PreparedAspectAttribs =
		lists:map(
		  	fun(Advice) when is_record(Advice, advice) ->
				  resolve_advice_ref_to_pointcut(Advice, #aspect{attribs = AspectAttribsWithImports}, Globals);
			   (AspectAttrib) ->
					AspectAttrib
		  	end,
			AspectAttribsWithImports),
	#aspect{attribs = PreparedAspectAttribs}.

-spec import_global_conf(advice(), globals()) -> advice();
			(pointcut(), globals()) -> pointcut().
%% @doc Advice and pointcut attributes in an aspect are eligible for importing global configuration.
%% This means that if the advice or pointcut in question has an id attribute, the following algorithm
%% takes place (the same applies for pointcut attributes):
%% <ul>
%% 		<li>Find the global advice with the same id.
%% 			<ul>
%% 				<li>If there is no such global advice then the given attribute needs no importing.</li>
%% 				<li>If there is a global advice with the same id, the local advice will take the global's
%% 					attributes except for any attributes which the local advice defines itself.
%% 				</li>
%% 			</ul>
%% 		</li>
%% </ul>
import_global_conf(Advice = #advice{attribs = AdviceAttribs}, Globals) ->
	case get_id(AdviceAttribs) of
		undefined ->
			Advice;
		Id ->
			case ?UTIL:find_first(fun(GlobalAdvice) -> get_id(GlobalAdvice) =:= Id end, gadvices(Globals)) of
				undefined ->
					Advice;
				GAdviceSameId ->
					#advice{attribs = overwrite_attribs(AdviceAttribs, get_attribs(GAdviceSameId))}
			end
	end;
import_global_conf(Pointcut = #pointcut{attribs = PointcutAttribs}, Globals) ->
	case get_id(PointcutAttribs) of
		undefined ->
			Pointcut;
		Id ->
			case ?UTIL:find_first(fun(GlobalPointcut) -> get_id(GlobalPointcut) =:= Id end, gpointcuts(Globals)) of
				undefined ->
					Pointcut;
				GPointcutSameId ->
					#pointcut{attribs = overwrite_attribs(PointcutAttribs, get_attribs(GPointcutSameId))}
			end
	end.

-spec overwrite_attribs([aop_attr()], [aop_attr()]) -> [aop_attr()].
%% @spec overwrite_attribs(PriorityAttribs::[aop_attr()], Attribs::[aop_attr()]) -> [aop_attr()]
%% @doc The attributes of PriorityAttribs and Attribs are merged into one [aop_attr()] with the condition that
%% no attributes in Attribs are included in the resulting [aop_attr()] if their key matches a key already present in
%% any attribute from PriorityAttribs.
overwrite_attribs(PriorityAttribs, Attribs) ->
	lists:append(PriorityAttribs,
				lists:filter(
					fun(Attr) ->
							not lists:keymember(element(1, Attr), 1, PriorityAttribs)
					end , Attribs)).

-spec resolve_advice_ref_to_pointcut(advice(), aspect(), globals()) -> advice().
%% @doc Local/global pointcut resolution by id involves:
%% <ul>
%% 		<li>Identifiying all the pointcuts to which the given advice refers to by id.</li>
%% 		<li>For each such id reference:
%% 			<ul>
%% 				<li>Check the pointcuts local to the given aspect (and within which the given advice is defined).
%% 				If a pointcut with the same id as the advice's id reference is found, that pointcut definition is
%% 				included in the advice's definition instead of the id reference.
%% 				</li>
%% 				<li>If a local pointcut is not found, check the global pointcuts. If a pointcut
%% 				with the same id as the advice's id reference is found, that pointcut definition is
%% 				included in the advice's definition instead of the id reference.
%% 				</li>
%% 			</ul>
%% 		</li>
%% </ul>
%% @throws {advice_has_no_ptcuts, AdviceId::str_undef()} |
%% 			{unresolvable_ptcut_ref, {advice, AdviceId::str_undef()}, {pointcut_id, PointcutId::string()}} |
%%			{non_pointcut_value_in, Pointcuts::list()}
 resolve_advice_ref_to_pointcut(Advice = #advice{attribs = AdviceAttribs}, Aspect, Globals) ->
	PtcutsRefOrDef = get_pointcuts_ref_or_def(AdviceAttribs),
	LocalPointcuts = apointcuts(Aspect),
	GlobalPointcuts = gpointcuts(Globals),
	ResolvedPointcuts =
		lists:map(
		  fun(Pointcut) when is_record(Pointcut, pointcut) ->
				  Pointcut;
			 (PointcutIdRef) ->
				  Pred = fun(Pointcut) -> get_id(Pointcut) =:= PointcutIdRef end,
				  case ?UTIL:find_first(Pred, LocalPointcuts) of
					  undefined ->
						  	case ?UTIL:find_first(Pred, GlobalPointcuts) of
							  	undefined ->
								  	erlang:throw({unresolvable_ptcut_ref, {advice, get_id(Advice)}, {pointcut_id, PointcutIdRef}});
								ResolvedGlobalPointcut ->
									ResolvedGlobalPointcut
							end;
					  ResolvedLocalPointcut ->
						  ResolvedLocalPointcut
				  end
		  end, PtcutsRefOrDef),
	replace_ptcuts(ResolvedPointcuts, Advice).

-spec replace_ptcuts(Pointcuts::[pointcut()], Advice::advice()) -> advice().
%% @doc Replaces the given Advice's ptcuts attribute with one which has Pointcuts for its value.
%% It is assumed that the given Pointcuts list is a list of pointcut(), i.e. no references to pointcut ids should
%% be present in Pointcuts, only pointcut() values. If a value in Pointcuts is not a pointcut(), an exception is thrown.
%% @throws {non_pointcut_value_in, Pointcuts::list()}
replace_ptcuts(Pointcuts, Advice = #advice{attribs = AdviceAttribs}) ->
	?casetf(lists:all(fun(Pointcut) -> is_record(Pointcut, pointcut) end, Pointcuts), ok, erlang:throw({non_pointcut_value_in, Pointcuts})),
	NewAdviceAttribs = lists:keyreplace(ptcuts, 1, AdviceAttribs, #ptcuts{val = Pointcuts}),
	Advice#advice{attribs=NewAdviceAttribs}.

-spec get_pointcuts_ref_or_def(advice()) -> [advice_attr()];
				([advice_attr()]) -> [advice_attr()].
%% @doc Returns the list of point cut id references and actual pointcuts (i.e. the value of the advice attribute, #ptcuts{})
%% within the given advice() or [advice_attr()]. Throws an exception if the #ptcuts{} attribute cannot be found or
%% it's value is an empty list.
%% @throws {advice_has_no_ptcuts, AdviceId::str_undef()}
get_pointcuts_ref_or_def(#advice{attribs = AdviceAttribs}) ->
	get_pointcuts_ref_or_def(AdviceAttribs);
get_pointcuts_ref_or_def(AdviceAttribs) ->
	case lists:keyfind(ptcuts, 1, AdviceAttribs) of
		false ->
			erlang:throw({advice_has_no_ptcuts, get_id(AdviceAttribs)});
		#ptcuts{val = []} ->
			erlang:throw({advice_has_no_ptcuts, get_id(AdviceAttribs)});
		#ptcuts{val = PtcutsValue} ->
			PtcutsValue
	end.

-spec get_id(aop_el()) -> string() | undefined
		; ([aop_attr()]) -> string() | undefined.
get_id(AopEl) when is_record(AopEl, aspect) orelse is_record(AopEl, advice) orelse is_record(AopEl, pointcut) ->
	get_id(get_attribs(AopEl));
get_id(AopAttribs) ->
	proplists:get_value(id, AopAttribs).

-spec get_attribs(aop_el()) -> [aop_attr()].
get_attribs(AopEl) ->
	element(2, AopEl).

