:- ensure_loaded(library(lists)).

verify :-
    current_prolog_flag(argv, [N,Program|_]),
    verify(N, Program).

verify(N, Program) :-
    seeing(OldStream),
    see(Program),
    repeat,
    read(Term1),
    read(Term2),
    read(Term3),

    write(N),
    write("\n"),
    write(Term1),
    write("\n"),
    write(Term2),
    write("\n"),
    write(Term3),
    write("\n"),

    seen,
    see(OldStream).

% initState(+Program, +N, -StanPoczątkowy)

% step(+Program, +StanWe, ?PrId, -StanWy)


