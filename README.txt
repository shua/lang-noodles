Noodling around with programming language.

I'm going to dump any language experiments here.

mostly complete:
- strand.rs: minimal strand implementation http://www.call-with-current-continuation.org/strand/strand.html
- bidir_typeck.rs: https://arxiv.org/abs/1306.6032 "Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism"
- ctl_star.rs: model checker for CTL* https://en.wikipedia.org/wiki/CTL*
- hottest_dep.rs: https://www.youtube.com/watch?v=DEj-_k2Nx6o "HoTTEST Summer School 2022: How to code your own Type Theory"
- ukanren.rs: micro-kanren http://minikanren.org/

incomplete:
- graphck: attempt to understand TLA+ by writing my own https://lamport.azurewebsites.net/tla/tla.html
- ecmtt.rs: https://arxiv.org/abs/1202.0904 "Denotation of syntax and metaprogramming in contextual modal type theory (CMTT)"
- fomega.rs: system-f-omega https://en.wikipedia.org/wiki/System_F#System_F%CF%89

experiments:
- f_cap.rs: system-f but capabilities to limit availalable syntax
- l0612.rs: gradually typed assembly
- record.rs: every block is a record type, no need for 'let's, "|- {x=1, y=2, x} : {x:N, y:N, N}"
- spaced.rs: use spacing instead of parentheses "x + y  *  z" = "(x+y)*z"

