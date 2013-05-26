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
%% Description: TODO: Add description to eaopweaver

-module(eaopweaver).
%% -export([make_options/2]).
-compile(export_all).

-include("../include/eaopglobals.hrl").
-include("../include/unit_testing.hrl").

-export_type([eaop_compile_opt/0]).

-define(ASPECTS_KEY, aspects).
-define(ES, erl_syntax).
-define(SUFFIX, "@EAOP").
-define(TARGET_SUFFIX, "@EAOP_target").

-type eaop_compile_opt() :: compile:option() | {?ASPECTS_KEY, [?CORE:aspect()]}.

parse_transform(Forms, Options) ->
	Aspects = get_aspects_from_options(Options),
	SendPtcutExists = lists:any(fun ?CORE:exists_send_ptcut/1, Aspects),
	ReceivePtcutExists = lists:any(fun ?CORE:exists_receive_ptcut/1, Aspects),
	FunctiondefPtcutExists = lists:any(fun ?CORE:exists_functiondef_ptcut/1, Aspects),
	TransFun = create_trans_fun(SendPtcutExists, ReceivePtcutExists, FunctiondefPtcutExists, Aspects),
	{Module, NewForms} = transform(Forms, TransFun),
	case print_gen_src(Options) of
		{true, Path} ->
			Filename = Module ++ ".erl",
			file:write_file(filename:join([Path, Filename]), ?UTIL:forms_to_binary(NewForms));
		_ ->
			ok
	end,
	NewForms.

-spec transform(Forms::[erl_parse:abstract_form()], F::fun((?ES:syntaxTree(), pid()) -> ?ES:syntaxTree())) -> {Module::atom(), [erl_parse:abstract_form()]}.
transform(Forms, F) ->
	Tree = ?ES:form_list(Forms),
	Pid = start_weaver_notes(),
	ModifiedTree = postorder(F, Tree, Pid),
	Module = ?ES:atom_literal(get_current_module(Pid)),
	stop_weaver_notes(Pid),
	{Module, ?ES:revert_forms(ModifiedTree)}.

postorder(F, Tree, WeaverNotesPid) ->
	case get_current_mod_name(Tree) of
		undefined ->
			ok;
		CurrentModName ->
			set_current_module(WeaverNotesPid, CurrentModName)
	end,
	case get_current_fun_name(Tree) of
		undefined ->
			ok;
		CurrentFunName ->
			set_current_function(WeaverNotesPid, CurrentFunName),
			Arity = ?ES:function_arity(Tree),
			set_current_function_arity(WeaverNotesPid, Arity)
	end,
	SubTrees =
		case ?ES:subtrees(Tree) of
			[] ->
				Tree;
			List ->
				?ES:update_tree(Tree, [[postorder(F, Subtree, WeaverNotesPid) || Subtree <- Group] || Group <- List])
		end,
	F(SubTrees, WeaverNotesPid).

-spec get_current_mod_name(?ES:syntaxTree()) -> ?ES:syntaxTree() | undefined.
get_current_mod_name(Tree)  ->
	case ?ES:type(Tree) of
		attribute ->
			case ?ES:atom_value(?ES:attribute_name(Tree)) of
				module ->
					[TreeCurrentModName] = ?ES:attribute_arguments(Tree),
					TreeCurrentModName;
				_ ->
					undefined
			end;
		_ ->
			undefined
	end.

-spec get_current_fun_name(?ES:syntaxTree()) -> ?ES:syntaxTree() | undefined.
get_current_fun_name(Tree) ->
	case ?ES:type(Tree) of
		function ->
			?ES:function_name(Tree);
		_ ->
			undefined
	end.

print_gen_src(Options) ->
	case proplists:get_value(print_gen_src, Options) of
		undefined ->
			undefined;
		Path ->
			{true, Path}
	end.

make_options(Aspects, Options) ->
	lists:append([{parse_transform, ?MODULE}, return, report, {?ASPECTS_KEY, Aspects}], Options).

-spec get_aspects_from_options([term()]) -> [?CORE:aspect()].
%% @spec get_aspects_from_options([term()]) -> [aspect()]
%% @doc Retrieves the aspects from the given options.
get_aspects_from_options(Options) ->
	proplists:get_value(?ASPECTS_KEY, Options, []).

-record(adv_grps, {
	before = [] :: [?CORE:advice()],
	'after' = [] :: [?CORE:advice()],
	after_throw = [] :: [?CORE:advice()],
	after_final = [] :: [?CORE:advice()],
	around = [] :: [?CORE:advice()]
}).

-spec group_advices([?CORE:advice()]) -> #adv_grps{}.
group_advices(Advices) ->
	#adv_grps {
		before = ?CORE:get_advices_by_type(Advices, before),
		'after' = ?CORE:get_advices_by_type(Advices, 'after'),
		after_throw = ?CORE:get_advices_by_type(Advices, after_throw),
		after_final = ?CORE:get_advices_by_type(Advices, after_final),
		around = ?CORE:get_advices_by_type(Advices, around)
	}.

%% SendPtcutExists::boolean(), ReceivePtcutExists::boolean(), FunctiondefPtcutExists::boolean(), Aspects
%% @doc create_trans_fun/4 returns a function which will be used when transforming each Node in the abstract syntax tree.
create_trans_fun(SendPtcutExists, ReceivePtcutExists, FunctiondefPtcutExists, Aspects) ->
	fun(Node, WeaverNotesPid) ->
			NodeType = ?ES:type(Node),
			if
				SendPtcutExists == true andalso NodeType == infix_expr ->
					case ?ES:operator_name(?ES:infix_expr_operator(Node)) == '!' of
						true ->
							transform_send(Node, WeaverNotesPid);
						false ->
							Node
					end;
				SendPtcutExists == true andalso NodeType == eof_marker andalso ReceivePtcutExists == false ->
					?ES:form_list([msg_info_function(send_msg_info_function_name(), Aspects), Node]);
				SendPtcutExists == true andalso NodeType == eof_marker andalso ReceivePtcutExists == true ->
					?ES:form_list([msg_info_function(send_msg_info_function_name(), Aspects), msg_info_function(receive_msg_info_function_name(), Aspects), Node]);
				ReceivePtcutExists == true andalso NodeType == receive_expr ->
					transform_receive(Node, WeaverNotesPid);
				ReceivePtcutExists == true andalso NodeType == eof_marker andalso SendPtcutExists == false ->
					?ES:form_list([msg_info_function(receive_msg_info_function_name(), Aspects), Node]);
				FunctiondefPtcutExists == true andalso NodeType == function ->
					TreeModuleName = get_current_module(WeaverNotesPid),
					case get_applicable_advices(Node, TreeModuleName, Aspects) of
						[] ->
							Node;
						ApplicableAdvices ->
							AG = group_advices(ApplicableAdvices),
							transform_functiondef(Node, TreeModuleName, AG)
					end;
				true ->
					Node
			end
	end.

-spec get_applicable_advices(TreeFunction::?ES:syntaxTree(), TreeModuleName::?ES:syntaxTree(), Aspects::[?CORE:aspect()]) -> Advices::[?CORE:advice()].
get_applicable_advices(TreeFunction, TreeModuleName, Aspects) ->
	StrModuleName = ?ES:atom_name(TreeModuleName),
	StrFunctionName = ?ES:atom_name(?ES:function_name(TreeFunction)),
	Arity = ?ES:function_arity(TreeFunction),
	?CORE:get_applicable_advices(StrModuleName, StrFunctionName, Arity, Aspects).

-spec get_target_function_details_var() -> ?ES:syntaxTree().
get_target_function_details_var() ->
	?ES:variable("TargetFunctionDetails").

%% TreeF is the original syntax tree node of type 'function' which is being transformed.
%% TreeTargetFName is a syntax tree of an atom with the name of the target function which the proxy function needs to call.
proxy_function(TreeF, TreeModuleName, TreeTargetFName, #adv_grps{before = BAdvs, 'after' = AftAdvs, after_throw = ATAdvs, after_final = AFAdvs, around = ArAdvs}) ->
	Arity = ?ES:function_arity(TreeF),
	TreeTargetFArgs = generate_vars(Arity),
	TreeTargetFDetails = ?ES:list([TreeModuleName, TreeTargetFName, ?ES:list(TreeTargetFArgs)]),
	TreeDetailsVar = get_target_function_details_var(),
	TreeBindDetailsVar = ?ES:match_expr(TreeDetailsVar, TreeTargetFDetails),
	TreeTargetFCall = ?ES:application(TreeTargetFName, TreeTargetFArgs),
	BAdvCalls = before_advice_calls(BAdvs),
	ArAndAftAdvCalls = around_and_after_advice_calls(ArAdvs, AftAdvs, TreeTargetFCall),
	ProxyClauseBody = 
		if
			ATAdvs == [] andalso AFAdvs == [] ->
				[TreeBindDetailsVar | BAdvCalls] ++ ArAndAftAdvCalls;
			true ->
				CatchClauseList = after_throw_catch_clauses(ATAdvs),
				AFAdvCalls = after_final_advice_calls(AFAdvs),
				[TreeBindDetailsVar | BAdvCalls] ++ [?ES:try_expr(ArAndAftAdvCalls, [], CatchClauseList, AFAdvCalls)]
		end,
	ProxyClause = ?ES:clause(TreeTargetFArgs, [], ProxyClauseBody),
	?ES:function(?ES:function_name(TreeF), [ProxyClause]).

-spec after_throw_catch_clauses([]) -> [];
		(ATAdvs::[?CORE:advice()]) -> ClauseList::[?ES:syntaxTree()].
after_throw_catch_clauses([]) ->
	[];
after_throw_catch_clauses(ATAdvs) ->
	TreeDetailsVar = get_target_function_details_var(),
	TreeExClassVar = ?ES:variable("ExClass"),
	TreeExPatternVar = ?ES:variable("ExPattern"),
	%% TreeCatchClausePattern = ?ES:module_qualifier(TreeExClassVar, TreeExPatternVar),
	TreeCatchClausePattern = ?ES:class_qualifier(TreeExClassVar, TreeExPatternVar),
	TreeTuple = ?ES:tuple([TreeExClassVar, TreeExPatternVar]),
	TreeCatchClauseBody = [?ES:application(?ES:atom(?CORE:get_advice_module(ATAdv)), ?ES:atom(?CORE:get_advice_function(ATAdv)), [TreeDetailsVar, TreeTuple]) || ATAdv <- ATAdvs],
	[?ES:clause([TreeCatchClausePattern], [], TreeCatchClauseBody)].

-spec after_final_advice_calls([?CORE:advice()]) -> [?ES:syntaxTree()].
after_final_advice_calls(AFAdvs) ->
	TreeDetailsVar = get_target_function_details_var(),
	[?ES:application(?ES:atom(?CORE:get_advice_module(AFAdv)), ?ES:atom(?CORE:get_advice_function(AFAdv)), [TreeDetailsVar]) || AFAdv <- AFAdvs].

-spec before_advice_calls([?CORE:advice()]) -> [?ES:syntaxTree()].
before_advice_calls(BAdvs) ->
	TreeDetailsVar = get_target_function_details_var(),
	[?ES:application(?ES:atom(?CORE:get_advice_module(BAdv)), ?ES:atom(?CORE:get_advice_function(BAdv)), [TreeDetailsVar]) || BAdv <- BAdvs].

-spec after_advice_calls([?CORE:advice()]) -> [?ES:syntaxTree()].
after_advice_calls(AftAdvs) ->
	TreeRVar = get_target_function_result_var(),
	TreeDetailsVar = get_target_function_details_var(),
	[?ES:application(?ES:atom(?CORE:get_advice_module(AftAdv)), ?ES:atom(?CORE:get_advice_function(AftAdv)), [TreeDetailsVar, TreeRVar]) || AftAdv <- AftAdvs].

-spec apply_args([?CORE:advice()]) -> [?ES:syntaxTree()].
%% These are the arguments passed to erlang:apply in:
%% ?ES:application(?ES:atom('erlang'), ?ES:atom('apply'), apply_args(ArAdvs));
apply_args(ArAdvs) ->
	TreeDetailsVar = get_target_function_details_var(),
	lists:foldl(
		fun (AroundAdvice, []) ->
				[?ES:atom(?CORE:get_advice_module(AroundAdvice)), ?ES:atom(?CORE:get_advice_function(AroundAdvice)), ?ES:list([TreeDetailsVar])];
			(AroundAdvice, Acc) ->
				[?ES:atom(?CORE:get_advice_module(AroundAdvice)), ?ES:atom(?CORE:get_advice_function(AroundAdvice)),  Acc]
		end, [], ArAdvs).

-spec get_target_function_result_var() -> ?ES:syntaxTree().
get_target_function_result_var() ->
	?ES:variable("R").

-spec around_and_after_advice_calls(ArAdvs::[?CORE:advice()], AftAdvs::[?CORE:advice()], TreeTargetFCall::?ES:syntaxTree()) -> [?ES:syntaxTree()].
around_and_after_advice_calls([], [], TreeTargetFCall) ->
	%% no need for apply, no need for R
	%% call target function
	[TreeTargetFCall];
around_and_after_advice_calls(ArAdvs, [], _) ->
	%% no need for R
	%% need to apply; target function will be called by user in around advice
	[?ES:application(?ES:atom('erlang'), ?ES:atom('apply'), apply_args(ArAdvs))];
around_and_after_advice_calls([], AftAdvs, TreeTargetFCall) ->
	%% no need for apply
	%% call target function and bind result to R, then pass R to AftAdvs
	TreeMatchR = ?ES:match_expr(get_target_function_result_var(), TreeTargetFCall),
	[TreeMatchR | after_advice_calls(AftAdvs)];
around_and_after_advice_calls(ArAdvs, AftAdvs, _) ->
	%% need apply; need to bind result of apply to R, and then pass R to AftAdvs
	TreeMatchR = ?ES:match_expr(get_target_function_result_var(), ?ES:application(?ES:atom('erlang'), ?ES:atom('apply'), apply_args(ArAdvs))),
	[TreeMatchR | after_advice_calls(AftAdvs)].

%% TargetFDetails = [TargetFunctionModule, TargetFunctionName, [P1, .., PN]]
-spec transform_functiondef(TreeF::?ES:syntaxTree(), TreeModuleName::?ES:syntaxTree(), AG::#adv_grps{}) -> TreeTransformedFunction::?ES:syntaxTree().
transform_functiondef(TreeF, TreeModuleName, AG) ->
	TreeTargetFName = ?ES:atom(?ES:atom_name(?ES:function_name(TreeF)) ++ ?TARGET_SUFFIX),
	TreeProxyF = proxy_function(TreeF, TreeModuleName, TreeTargetFName, AG),
	case AG#adv_grps.around of
		[] ->
			?ES:form_list([TreeProxyF, ?ES:function(TreeTargetFName, ?ES:function_clauses(TreeF))]);
		_ ->
			TreeFA = ?ES:arity_qualifier(TreeTargetFName, ?ES:integer(?ES:function_arity(TreeF))),
			TreeExportAttr = ?ES:attribute(?ES:atom(export), [?ES:list([TreeFA])]),
			?ES:form_list([TreeExportAttr, TreeProxyF, ?ES:function(TreeTargetFName, ?ES:function_clauses(TreeF))])
	end.

-spec generate_vars(N::integer()) -> Vars::[?ES:syntaxTree()].
%% @doc Vars is a list of syntaxTree() variables generated by erl_syntax:variable/1. They are named sequentially from P1 up to PN
generate_vars(N) ->
	[?ES:variable("P" ++ integer_to_list(X)) || X <- lists:seq(1, N)].

-spec foldlfun(?ES:syntaxTree(), ?ES:syntaxTree(), Arity::?ES:syntaxTree(), ?ES:syntaxTree(), pid()) -> ?ES:syntaxTree().
foldlfun(ModName, FunName, Arity, MsgFormatVar, WeaverNotesPid) ->
	%% ---------------------
	%% generated variables:
	DeltaAfterAdvicesVar = generate_variable("DeltaAfterAdvices", WeaverNotesPid),
	MsgInfoFunVar = generate_variable("MsgInfoFun", WeaverNotesPid),
	AdviceIdVar = generate_variable("AdviceId", WeaverNotesPid),
	AdviceModuleVar = generate_variable("AdviceModule", WeaverNotesPid),
	AdviceFunctionVar = generate_variable("AdviceFunction", WeaverNotesPid),
	AfterAdviceVar = generate_variable("AfterAdvice", WeaverNotesPid),
	%% ---------------------
	?ES:fun_expr([
		?ES:clause([MsgInfoFunVar, DeltaAfterAdvicesVar], none, [
			?ES:case_expr(?ES:application(MsgInfoFunVar, [MsgFormatVar]), [
				?ES:clause([?ES:atom(undefined)], none, [DeltaAfterAdvicesVar]),
				?ES:clause([?ES:tuple([AdviceIdVar, ?ES:atom(before), AdviceModuleVar, AdviceFunctionVar])], none, [
					?ES:application(AdviceModuleVar, AdviceFunctionVar, [ ?ES:list([AdviceIdVar, ModName, FunName, Arity, MsgFormatVar]) ]),
					DeltaAfterAdvicesVar
				]),
				?ES:clause([AfterAdviceVar], none, [?ES:list([AfterAdviceVar], DeltaAfterAdvicesVar)])
			]) %% case end
		]) %% fun clause end
	]).

-spec foreachfun(?ES:syntaxTree(), ?ES:syntaxTree(), Arity::?ES:syntaxTree(), ?ES:syntaxTree(), pid()) -> ?ES:syntaxTree().
foreachfun(ModName, FunName, Arity, MsgFormatVar, WeaverNotesPid) ->
	%% ---------------------
	%% generated variables:
	AdviceIdVar = generate_variable("AdviceId", WeaverNotesPid),
	AdviceModuleVar = generate_variable("AdviceModule", WeaverNotesPid),
	AdviceFunctionVar = generate_variable("AdviceFunction", WeaverNotesPid),
	%% ---------------------
	?ES:fun_expr([
		?ES:clause([?ES:tuple([AdviceIdVar, ?ES:atom('after'), AdviceModuleVar, AdviceFunctionVar])], none, [
			?ES:application(AdviceModuleVar, AdviceFunctionVar, [ ?ES:list([AdviceIdVar, ModName, FunName, Arity, MsgFormatVar]) ])
		]),
		%% This catch-all clause should never be used
		?ES:clause([?ES:underscore()], none, [?ES:atom(ok)])
	]).

%% Assumes Node is an infix_expr node with an ?ES::operator_name(?ES:infix_expr_operator(Node)) == '!'
transform_send(Node, WeaverNotesPid) ->
	%% ---------------------
	%% generated variables:
	MsgFormatVar = generate_variable("MsgFormat", WeaverNotesPid),
	AfterAdvicesListVar = generate_variable("AfterAdvicesList", WeaverNotesPid),
	%% ---------------------
	GetSendMsgInfo = ?ES:application(?ES:atom(send_msg_info_function_name()), []),
	TreeCurrentModule = get_current_module(WeaverNotesPid),
	TreeCurrentFunction = get_current_function(WeaverNotesPid),
	TreeCurrentFunctionArity = ?ES:integer(get_current_function_arity(WeaverNotesPid)),
	%% Replace Node with a block expression
	?ES:block_expr([
		%% bind right operand to variable so that any expressions in right operand are only evaluated once
		?ES:match_expr(MsgFormatVar, ?ES:infix_expr_right(Node)),
		?ES:match_expr(AfterAdvicesListVar,
			?ES:application(?ES:atom(lists), ?ES:atom(foldl), [foldlfun(TreeCurrentModule, TreeCurrentFunction, TreeCurrentFunctionArity, MsgFormatVar, WeaverNotesPid),
				?ES:nil(), GetSendMsgInfo])
		),
		?ES:infix_expr(?ES:infix_expr_left(Node), ?ES:infix_expr_operator(Node), MsgFormatVar),
		?ES:application(?ES:atom(lists), ?ES:atom(foreach), [foreachfun(TreeCurrentModule, TreeCurrentFunction, TreeCurrentFunctionArity, MsgFormatVar, WeaverNotesPid),
			AfterAdvicesListVar]),
		%% return result of !
		MsgFormatVar
	]).

%% Assumes Node is of type receive_expr
transform_receive(Node, WeaverNotesPid) ->
	GetReceiveMsgInfo = ?ES:application(?ES:atom(receive_msg_info_function_name()), []),
	TreeCurrentModule = get_current_module(WeaverNotesPid),
	TreeCurrentFunction = get_current_function(WeaverNotesPid),
	Arity = get_current_function_arity(WeaverNotesPid),
	TreeCurrentFunctionArity = ?ES:integer(Arity),
	ReceiveClauses = ?ES:receive_expr_clauses(Node),
	TransformedReceiveClauses = lists:reverse(lists:foldl(
		fun(ReceiveClause, DeltaTransformedReceiveClauses) ->
				%% ---------------------
				%% generated variables:
				MsgFormatVar = generate_variable("MsgFormat", WeaverNotesPid),
				AfterAdvicesListVar = generate_variable("AfterAdvicesList", WeaverNotesPid),
				%% ---------------------
				Patterns = ?ES:clause_patterns(ReceiveClause),
				Pattern = hd(Patterns),
				NewClausePattern = ?ES:match_expr(MsgFormatVar, Pattern),
				Body = ?ES:clause_body(ReceiveClause),
				LastExpr = lists:last(Body),
				%% transform body
				NewBody =
					case is_tail_recursive_call(LastExpr, ?ES:atom_value(TreeCurrentModule), ?ES:atom_value(TreeCurrentFunction), Arity) of
						true ->
							%% remove LastExpr from Body
							BodyNoTailRecursion = lists:reverse(tl(lists:reverse(Body))),
							[
								?ES:match_expr(AfterAdvicesListVar,
									?ES:application(?ES:atom(lists), ?ES:atom(foldl), [foldlfun(TreeCurrentModule, TreeCurrentFunction, TreeCurrentFunctionArity, MsgFormatVar, WeaverNotesPid),
										?ES:nil(), GetReceiveMsgInfo])
								),
								?ES:block_expr(BodyNoTailRecursion),
								?ES:application(?ES:atom(lists), ?ES:atom(foreach), [foreachfun(TreeCurrentModule, TreeCurrentFunction, TreeCurrentFunctionArity, MsgFormatVar, WeaverNotesPid),
									AfterAdvicesListVar]),
								%% make tail recursive call
								LastExpr
							];
						false ->
							%% ---------------------
							%% generated variables:
							ReturnValVar = generate_variable("ReturnVal", WeaverNotesPid),
							%% ---------------------
							[
								?ES:match_expr(AfterAdvicesListVar,
									?ES:application(?ES:atom(lists), ?ES:atom(foldl), [foldlfun(TreeCurrentModule, TreeCurrentFunction, TreeCurrentFunctionArity, MsgFormatVar, WeaverNotesPid),
										?ES:nil(), GetReceiveMsgInfo])
								),
								?ES:match_expr(ReturnValVar, ?ES:block_expr(Body)),
								?ES:application(?ES:atom(lists), ?ES:atom(foreach), [foreachfun(TreeCurrentModule, TreeCurrentFunction, TreeCurrentFunctionArity, MsgFormatVar, WeaverNotesPid),
									AfterAdvicesListVar]),
								ReturnValVar
							]
					end,
				[?ES:clause([NewClausePattern], ?ES:clause_guard(ReceiveClause), NewBody) | DeltaTransformedReceiveClauses]
		end, [], ReceiveClauses)),
	?ES:receive_expr(TransformedReceiveClauses, ?ES:receive_expr_timeout(Node), ?ES:receive_expr_action(Node)).

-spec is_tail_recursive_call(?ES:syntaxTree(), ModuleName::atom(), FunctionName::atom(), Arity::integer()) -> boolean().
%% @doc Checks whether the given Node is an application of the form ModuleName:FunctionName/Arity or FunctionName/Arity
is_tail_recursive_call(Node, ModuleName, FunctionName, Arity) ->
	case ?ES:type(Node) of
		application ->
			is_application_tail_recursive_call(Node, ModuleName, FunctionName, Arity);
		_ ->
			false
	end.

-spec is_application_tail_recursive_call(Node::?ES:syntaxTree(), ModuleName::atom(), FunctionName::atom(), Arity::integer()) -> boolean().
%% @doc Checks whether the given Node is an application of the form ModuleName:FunctionName/Arity or FunctionName/Arity. Assumes erl_syntax:type(Node) == 'application'
is_application_tail_recursive_call(Node, ModuleName, FunctionName, Arity) ->
	%% Check both the arity and the correct function being called
	AppOpNode = ?ES:application_operator(Node),
	case is_correct_mod_fun_for_tail_recursive_call(AppOpNode, ModuleName, FunctionName) of
		true ->
			length(?ES:application_arguments(Node)) =:= Arity;
		false ->
			false
	end.

-spec is_correct_mod_fun_for_tail_recursive_call(AppOpNode::?ES:syntaxTree(), ModuleName::atom(), FunctionName::atom()) -> boolean().
%% @doc Determines whether AppOpNode is an application operator of the form ModuleName:FunctionName or FunctionName
is_correct_mod_fun_for_tail_recursive_call(AppOpNode, ModuleName, FunctionName) ->
	case ?ES:type(AppOpNode) of
		atom ->
			?ES:atom_value(AppOpNode) =:= FunctionName;
		module_qualifier ->
			?ES:atom_value(?ES:module_qualifier_argument(AppOpNode)) =:= ModuleName andalso ?ES:atom_value(?ES:module_qualifier_body(AppOpNode)) =:= FunctionName;
		_ ->
			false
	end.

-spec generate_variable(atom(), pid()) -> ?ES:syntaxTree();
	(string(), pid()) -> ?ES:syntaxTree().
generate_variable(Name, WeaverNotesPid) when is_atom(Name) ->
	generate_variable(atom_to_list(Name), WeaverNotesPid);
generate_variable(Name, WeaverNotesPid) when is_list(Name) ->
	GenVarId = get_gen_var_id(WeaverNotesPid),
	VarName = Name ++ integer_to_list(GenVarId) ++ ?SUFFIX,
	?ES:variable(VarName).

send_msg_info_function_name() ->
	list_to_atom("get_send_msg_info" ++ ?SUFFIX).

receive_msg_info_function_name() ->
	list_to_atom("get_receive_msg_info" ++ ?SUFFIX).

-spec msg_info_function(FunctionName::atom(), [?CORE:aspect()]) -> Function::?ES:syntaxTree();
			(atom(), ?CORE:aspect()) -> ?ES:syntaxTree().
%% @doc Given an aspect or list of aspects, returns a syntaxTree() representation of the following:
%% 	FunctionName() ->
%% 		[fun(..) -> .. ; (_) -> undefined end, fun(..) -> .. ; (_) -> undefined end].
msg_info_function(FunctionName, Aspects) when is_list(Aspects) ->
	%% Collect all tuples to put in the list returned by get_send_msg_info
	ForEachAdviceInAspect =
		fun(Aspect) ->
				ForEachPointcutInAdvice =
					fun(Advice) ->
							[msg_info_fun(Advice, Pointcut) || Pointcut <- ?CORE:advpointcuts(Advice)]
					end,
				[ForEachPointcutInAdvice(Advice) || Advice <- ?CORE:aadvice(Aspect)]
		end,
	MsgInfoFunList = ?UTIL:filter_out(undefined, lists:flatten([ForEachAdviceInAspect(Aspect) || Aspect <- Aspects])),
	?ES:function(?ES:atom(FunctionName), [
		?ES:clause([], none, [?ES:list(MsgInfoFunList)])
	]);
msg_info_function(FunctionName, Aspect) ->
	msg_info_function(FunctionName, [Aspect]).

%% You might later add, PassContainingFunctionArguments, a boolean() which determines whether to pass the arguments passed to the function containing the send/receive to the advice or not.
-spec msg_info_fun(Advice::?CORE:advice(), Pointcut::?CORE:pointcut()) -> ?ES:syntaxTree() | undefined.
%% @doc Returns a syntaxTree() encoding the following:
%% 	fun(SendMsgFormat) ->
%%			{PointcutId, AdviceType, AdviceModule, AdviceFunction};
%%		(_) ->
%%			undefined
%%	end.
%% Where:
%%		SendMsgFormat = to_form(?CORE:get_send_msg(Pointcut)) %% i.e. the form representation of the string send_msg
%%		PointcutId = ?CORE:get_id(Pointcut)
%%		AdviceType = ?CORE:get_type(Advice)
%%		{AdviceModule, AdviceFunction} = ?CORE:get_mf(Advice)
msg_info_fun(Advice, Pointcut) ->
	case ?CORE:get_msg_format(Pointcut) of
		undefined ->
			undefined;
		MsgFormat ->
			AdviceType = ?CORE:get_type(Advice),
			{ModuleName, FunctionName} = ?CORE:get_mf(Advice),
			Clause1Body = ?ES:tuple([?ES:atom(?CORE:get_id(Pointcut)), ?ES:atom(AdviceType),
												?ES:atom(ModuleName), ?ES:atom(FunctionName)]),
			Clause1 = ?ES:clause([to_form(MsgFormat)], none, [Clause1Body]),
			CatchAllClause = ?ES:clause([?ES:underscore()], none, [?ES:atom('undefined')]),
			?ES:fun_expr([Clause1, CatchAllClause])
	end.

%% to_form(string()) -> abstract form
to_form(MsgFStr) ->
	{_, Tokens, _} = erl_scan:string(end_with_period(MsgFStr)),
	{_, Exprs} = erl_parse:parse_exprs(Tokens),
	hd(Exprs).

end_with_period(String) ->
	case lists:last(String) of
		$. -> String;
		_ -> String ++ "."
	end.

%%
%% Weaver notes: A process to help with weaving
%%

-record(notes,{
	current_mod 		:: ?ES:syntaxTree(),
	current_fun			:: ?ES:syntaxTree(),
	current_fun_arity	:: integer(),
	gen_var_id = 0		:: integer(),
	parent_pid			:: pid()
}).

%% @doc Used to keep track of some state while traversing the abstract syntax tree.
weaver_notes(State = #notes{current_mod = CurrentMod, current_fun = CurrentFun, current_fun_arity = CurrentArity, gen_var_id = GenVarId, parent_pid = ParentPid}) ->
	receive
		{Pid, current_mod, NewCurrentModule} ->
			Pid ! {self(), ok},
			weaver_notes(State#notes{current_mod = NewCurrentModule});
		{Pid, current_fun, NewCurrentFunction} ->
			Pid ! {self(), ok},
			weaver_notes(State#notes{current_fun = NewCurrentFunction});
		{Pid, current_fun_arity, NewCurrentArity} ->
			Pid ! {self(), ok},
			weaver_notes(State#notes{current_fun_arity = NewCurrentArity});
		{Pid, current_mod} ->
			Pid ! {self(), current_mod, CurrentMod},
			weaver_notes(State);
		{Pid, current_fun} ->
			Pid ! {self(), current_fun, CurrentFun},
			weaver_notes(State);
		{Pid, current_fun_arity} ->
			Pid ! {self(), current_fun_arity, CurrentArity},
			weaver_notes(State);
		{Pid, gen_var_id} ->
			Pid ! {self(), gen_var_id, GenVarId},
			weaver_notes(State#notes{gen_var_id = GenVarId + 1});
		{Pid, exit} ->
			Pid ! {self(), ok};
		{'EXIT', ParentPid, normal} ->
			ok
		after 10000 ->
			case erlang:is_process_alive(ParentPid) of
				true ->
					weaver_notes(State);
				false ->
					io:format("Stopping orphan weaver_notes with pid ~p and parent pid ~p\n", [self(), ParentPid])
			end
	end.

-spec start_weaver_notes() -> pid().
start_weaver_notes() ->
	Pid = self(),
	erlang:spawn_link(fun() -> weaver_notes(#notes{parent_pid = Pid}) end).

-spec get_current_module(pid()) -> ?ES:syntaxTree().
get_current_module(Pid) ->
	Pid ! {self(), current_mod},
	receive {Pid, current_mod, CurrentModule} -> CurrentModule end.

-spec get_current_function(pid()) -> ?ES:syntaxTree().
get_current_function(Pid) ->
	Pid ! {self(), current_fun},
	receive {Pid, current_fun, CurrentFunction} -> CurrentFunction end.

-spec get_current_function_arity(pid()) -> integer().
get_current_function_arity(Pid) ->
	Pid ! {self(), current_fun_arity},
	receive {Pid, current_fun_arity, Arity} -> Arity end.

-spec set_current_module(pid(), ?ES:syntaxTree()) -> ok.
set_current_module(Pid, Module) ->
	Pid ! {self(), current_mod, Module},
	receive {Pid, ok} -> ok end.

-spec set_current_function(pid(), ?ES:syntaxTree()) -> ok.
set_current_function(Pid, Function) ->
	Pid ! {self(), current_fun, Function},
	receive {Pid, ok} -> ok end.

-spec set_current_function_arity(pid(), integer()) -> ok.
set_current_function_arity(Pid, Arity) ->
	Pid ! {self(), current_fun_arity, Arity},
	receive {Pid, ok} -> ok end.

-spec get_gen_var_id(pid()) -> integer().
get_gen_var_id(Pid) ->
	Pid ! {self(), gen_var_id},
	receive {Pid, gen_var_id, GenVarId} -> GenVarId end.

-spec stop_weaver_notes(pid()) -> ok.
stop_weaver_notes(Pid) ->
	Pid ! {self(), exit},
	receive {Pid, ok} -> ok end.

