%% Commenting NOTEST will remove tests when compiling. Keep this definition before the inclusion of eunit.hrl.
-define(NOTEST, true).

-ifdef(EUNIT).
-include_lib("eunit/include/eunit.hrl").
-endif.
