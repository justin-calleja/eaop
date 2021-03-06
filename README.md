eaop
====

Compile time AOP implementation for Erlang.

This project was inspired by [ErlAOP](http://sourceforge.net/projects/erlaop/), which was written by Alexei Krasnopolski. Most of the ErlAOP documentation is relevant to this project.

eaop re-implements the functionality of ErlAOP using [erl_syntax](http://erlang.org/doc/man/erl_syntax.html) and should not be dependent on the abstract forms generated by the Erlang compiler. However, both ErlAOP and eaop are implemented using Erlang's [parse_transform/2](http://www.erlang.org/doc/man/erl_id_trans.html) mechanism, making both of them limited to compile time weaving of code.

eaop also extends the expressiveness of pointcut definitions, allowing the specification of send and receive operations in Erlang code to be eligible points for code weaving.

---

Note: this project is no longer under development or in any way used or maintained. The last remaining remnants of some kind of documentation: https://github.com/justin-calleja/eaop/wiki/_pages

This was just a pet project. If anyone else sees any value in it and decides to build on it, please get in touch.
