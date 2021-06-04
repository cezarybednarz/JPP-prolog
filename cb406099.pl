:- ensure_loaded(library(lists)).

verify :-
    current_prolog_flag(argv, [N,Program|_]),
    verify(N, Program).

verify(N, Program) :-
    see(Program),
    read(Term1),
    Term1 =.. [_, Variables],
    read(Term2),
    Term2 =.. [_, Arrays],
    read(Term3),
    Term3 =.. [_, Prog],
    seen.

