:- ensure_loaded(library(lists)).

verify :-
    debug,
    current_prolog_flag(argv, [N,Program|_]),
    atom_number(N, N_num),
    verify(N_num, Program).

verify(N, Program) :-
    (   N =< 0 
    ->
        write('Error: parametr '),
        write(N),
        write(' powinien byc liczba > 0'),nl
    ; 
        set_prolog_flag(fileerrors, off),
        see(Program),
        !,
        read(Term1),
        read(Term2),
        read(Term3),
        Term1 =.. [_, Variables],
        Term2 =.. [_, Arrays],
        Term3 =.. [_, Stmts],
        initState(program(Variables, Arrays, Stmts), N, InitState),
        write(InitState),
        seen
    ).
verify(_, Program) :-
    format('Error: brak pliku o nazwie - ~s', [Program]),nl.

storage(vars, arrs, lines).
state(n, currentStorage, visitedStorages).

build(X, N, List) :- 
    length(List, N), 
    maplist(=(X), List).

mergeLists([], [], []).
mergeLists([X|L1], [Y|L2], [[X,Y]|List]) :-
    mergeLists(L1, L2, List).

initState(Program, N, StanPoczatkowy) :-
    Program =.. [_, Variables, Arrays, _],

    length(Variables, VariablesLen),
    build(0, VariablesLen, InitVariables),
    mergeLists(Variables, InitVariables, VariablesList),

    N1 is N+1,
    length(Arrays, ArraysLen),
    build(0, N1, ZeroArray),
    build(ZeroArray, ArraysLen, InitArrays),
    mergeLists(Arrays, InitArrays, ArraysList),

    build(1, N, LinesList),

    Storage = storage(VariablesList, ArraysList, LinesList),
    StanPoczatkowy = state(N, Storage, []). 

getElemFromPairList([], _, Val) :-
    Val is -1.
getElemFromPairList([[N,V]|PairList], Name, Val) :-
    (   N = Name
    ->  
        Val = V
    ;
        getElemFromPairList(PairList, Name, Val)
    ).

getVariable(Storage, VarName, Value) :-
    Storage =.. [_, Vars, _, _],
    getElemFromPairList(Vars, VarName, Value).

getArrayElem(Storage, ArrName, Id, Value) :-
    Storage =.. [_, _, Arrs, _],
    getElemFromPairList(Arrs, ArrName, Array),
    nth0(Id, Array, Value).

step(Program, StanWe, PrId, StanWy) :-
    Program =.. [_, _, _, Stmts],
    StanWe =.. [_, N, Storage, VisitedStorages],
    Storage =.. [_, Variables, Arrays, Lines],
    nth0(PrId, Lines, Line),
    nth1(Line, Stmts, Stmt).
    