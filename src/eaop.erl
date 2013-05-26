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
%% Description: This module is an interface to the user of eaop. Compilation is done through this module.
-module(eaop).

-include("../include/eaopglobals.hrl").
-include("../include/unit_testing.hrl").

%%
%% Exported Functions
%%
%% -export([]).
-compile(export_all).

%%
%% API Functions
%%

-spec compile(Srcs::[string()], Configs::[string()]) -> ok.
%% @todo Add the throws which can be thrown by functions executed within this function
%% ( e.g. {ambiguous_ptcut_type, [ptcut_t()]} ).
%% @doc
%%		Srcs = list of directory names containing source files and/or file names.
%%		Configs = list of directory names containing config files and/or config file names.
%% Compiles the source files (*.erl) explicitly listed or found in the directories listed in Srcs.
%% AOP weaving is done during the compilation stage using the configuration found in the config files
%% explicitly listed or found within the directories listed in Configs. The default file suffix to identify
%% a file as being a config file is .adf.
%% (Note: given any directory, all sub-directories are searched recursively for source/config files to use in
%% the compilation).
compile(Srcs, Configs) ->
	compile(Srcs, Configs, []).

-spec compile(Srcs::[string()], Configs::[string()], Options::[term()]) -> ok.
%% @throws TODO
%% @doc
%%		Srcs = list of directory names containing source files and/or file names.
%%		Configs = list of directory names containing config files and/or config file names.
%%		Options = Options determine the behavior of the compiler as defined in compile:file/2.
%%			Additional options include:
%%				{config_suffix, Suffix}: used to change the default (.adf) suffix of aspect definition files for this compilation. 
%%				{print_gen_src, Dir}: this option prints the transformed source files after weaving in the directory Dir. 
%% Same as eaop:compile/2 but takes a list of options.
compile([], _, _) ->
	ok;
compile(Srcs, Configs, Options) ->
	SrcFiles = get_files(Srcs, ".*\.erl$"),
	Suffix =
		case lists:keyfind(config_suffix, 1, Options) of
			false ->
				".*\.adf$";
			{_, ConfigSuffix} ->
				".*\." ++ ConfigSuffix ++ "$"
		end,
	ConfigFiles = get_files(Configs, Suffix),
	Aspects = read_aspects(ConfigFiles),
	Opts = ?WEAVER:make_options(Aspects, Options),
	compile_files(SrcFiles, Opts).

%% @doc compile_aspects/2 can be used when you have the aspects themselves and don't need to process .adf files. If building the aspects programmatically, this is probably the function you'd want to use.
compile_aspects(Srcs, Aspects) ->
	compile_aspects(Srcs, Aspects, []).

%% @doc Similar to compile_aspects/2 but with options.
compile_aspects(Srcs, Aspects, Options) ->
	SrcFiles = get_files(Srcs, ".*\.erl$"),
	Weaver = get_weaver_module(Options),
	Opts = Weaver:make_options(Aspects, Options),
	compile_files(SrcFiles, Opts).

get_weaver_module(Options) ->
	proplists:get_value(weaver, Options, ?WEAVER).

-type file_or_dir() :: filelib:filename() | filelib:dirname().
-spec get_files([FileOrDirName::file_or_dir()], SuffixRegex::string()) -> [filelib:filename()].
get_files(FilesAndOrDirs, Suffix) ->
	lists:append(
	  [	case filelib:is_dir(FileOrDir) of
			true ->
				filelib:fold_files(FileOrDir, Suffix, true, fun(F, Acc) -> [F | Acc] end, []);
			false ->
				[FileOrDir]
		end || FileOrDir <- FilesAndOrDirs	]).

%% Note: the type compile_res() is actually whatever compile:file/2 is capable of returning.
-type compile_res() ::  {ok, module()} | {ok, module(), Warnings::[term()]} | {ok, module(), binary()} | {ok, module(), binary(), Warnings::[term()]} | {error, Errors::[term()], Warnings::[term()]} | error.
-spec compile_files(SrcFiles::[file:name()], Options::[?WEAVER:eaop_compile_opt()]) -> [{SrcFile::file:name(), CompileResult::compile_res()}].
compile_files(SrcFiles, Options) ->
	lists:foldl(
		fun(S, Results) ->
				CompileRes = compile:file(S, Options),
				[{S, CompileRes} | Results]
		end, [], SrcFiles).


%%
%% Local Functions
%%

-spec read_aspects(ConfigFiles::[file:name()]) -> [?CORE:aspect()].
read_aspects(ConfigFiles) ->
	?CORE:prepare_aspects_for_weaving(read_globals(ConfigFiles)).

-spec read_globals(ConfigFiles::[file:name()]) -> ?CORE:globals().
read_globals(ConfigFiles) ->
	?CORE:get_globals(read_configs(ConfigFiles)).

-spec read_configs([file:name()]) -> [?CORE:aop_el()].
read_configs(Files) ->
	lists:foldl(
		fun(File, Adfs) ->
				{ok, Adf} = file:consult(File),
				lists:append(Adfs, Adf)
		end, [], Files).
