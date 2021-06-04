:- ensure_loaded(library(lists)).

verify :-
    debug,
    current_prolog_flag(argv, [N,Program|_]),
    atom_number(N, N_num),
    verify(N_num, Program).

verify(N, Program) :-
    see(Program),
    read(Term1),
    read(Term2),
    read(Term3),
    Term1 =.. [_, Variables],
    Term2 =.. [_, Arrays],
    Term3 =.. [_, Prog],
    initState(N, Prog, InitState),
    write(InitState),
    seen.

storage(vars, arrs, line).

state(n, prog, storages, visitedStorages).

build(X, N, List) :- 
    length(List, N), 
    maplist(=(X), List).

initState(N, Prog, State) :-
    build(storage([], [], 0), N, InitStorages),
    State = state(N, Prog, InitStorages, []).

