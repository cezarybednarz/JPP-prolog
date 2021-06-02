
verify :-
    current_prolog_flag(argv, Arguments),
    verify(Arguments).

verify(Argv) :-
    concat_atom(Argv, ' ', SingleArg),
    term_to_atom(Term, SingleArg),
    Val is Term,
    format('~w~n', [Val]).
