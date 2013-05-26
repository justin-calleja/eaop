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
%% Description: Utilitly functions. 

-module(eaoputil).

-export([find_first/2, filter_out/2, forms_to_binary/1]).

-include("../include/unit_testing.hrl").

%%
%% API functions:
%%

-spec find_first(Pred::fun((Elem::T) -> boolean()), List::[T]) -> T | undefined.
%% @doc Given a predicate function Pred, this function iterates (head-to-tail) through List of type T, applying
%% each element in List to Pred. The first element in List to satisfy Pred is returned by the function and no more
%% processing is done by the function. undefined is returned if all the elements in List do not satisfy Pred.
find_first(_, []) ->
	undefined;
find_first(Pred, [Head | Tail]) ->
	case Pred(Head) of
		true ->
			Head;
		false ->
			find_first(Pred, Tail)
	end.

-spec filter_out(T::term(), List::list()) -> list().
%% @doc Removes any elements in List which are exactly equal to T.
filter_out(Term, List) ->
	lists:filter(
		fun(El) ->
				El =/= Term
		end, List).

-spec forms_to_binary([erl_parse:abstract_form()]) -> binary();
			(erl_parse:abstract_form()) -> binary().
forms_to_binary(Forms) when is_list(Forms) ->
	list_to_binary(lists:flatten([erl_pp:form(Form) || Form <- Forms]));
forms_to_binary(Form) ->
	forms_to_binary([Form]).

