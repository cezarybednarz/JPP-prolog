:- ensure_loaded(library(lists)).
:- op(700, xfx, <>).

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
        length(Stmts, StmtsLen),
        LastStmtLine is StmtsLen+1,
        append(Stmts, [goto(LastStmtLine)], NewStmts),  % finished prcesses will loop at the end
        TermProg = program(Variables, Arrays, NewStmts),
        initState(TermProg, N, InitState),

        write('TermProg:  '),write(TermProg),nl,
        write('InitState: '),write(InitState),nl,

        step(TermProg, InitState, 0, State1),
        write(State1),nl,
        % step(TermProg, State1, 1, State2),
        % write(State2),nl,
        % step(TermProg, State2, 0, State3),
        % write(State3),nl,
        % step(TermProg, State3, 1, State4),
        % write(State4),nl,
        write('----------------------'),nl,


        checkState(TermProg, InitState, _, Result),
        Result =.. [_, Valid, PrId1, PrId2],
        (   Valid
        ->
            write('Program jest poprawny (bezpieczny).'),nl
        ;
            write('Program jest niepoprawny.'),nl,
            format('Procesy w sekcji: ~d, ~d.', [PrId1, PrId2])
        ),
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
    StanPoczatkowy = state(N, Storage, [Storage]). 


getElemFromPairList([], _, Val) :-
    Val is -1.
getElemFromPairList([[N,V]|PairList], Name, Val) :-
    (   N = Name
    ->  
        Val = V
    ;
        getElemFromPairList(PairList, Name, Val)
    ).

removeElemFromPairList(PairList, Name, NewPairList) :-
    getElemFromPairList(PairList, Name, Val),
    delete(PairList, [Name,Val], NewPairList).

getVariable(Storage, VarName, Value) :-
    Storage =.. [_, Vars, _, _],
    getElemFromPairList(Vars, VarName, Value).

getArrayElem(Storage, ArrName, Id, Value) :-
    Storage =.. [_, _, Arrs, _],
    getElemFromPairList(Arrs, ArrName, Array),
    nth0(Id, Array, Value).

setVariable(Storage, VarName, Value, NewStorage) :-
    Storage =..[_, Vars, Arrs, Lines],
    removeElemFromPairList(Vars, VarName, NewVars),
    NewerVars = [[VarName, Value]|NewVars],
    NewStorage = storage(NewerVars, Arrs, Lines).

setArrayElem(Storage, ArrName, Id, Value, NewStorage) :-
    Storage =.. [_, Vars, Arrs, Lines],
    getElemFromPairList(Arrs, ArrName, Arr),
    removeElemFromPairList(Arrs, ArrName, NewArrs),
    nth0(Id, Arr, _, NewArr),
    nth0(Id, NewerArr, Value, NewArr),
    NewerArrs = [[ArrName,NewerArr]|NewArrs],
    NewStorage = storage(Vars, NewerArrs, Lines).


% startBacktrack and step

checkState(Program, State, NewVisitedStorages, Result) :-
    State =.. [_, N, Storage, VisitedStorages],
    checkCriticalSection(Program, State, result(IsValid, PrId1, PrId2)),
    (   IsValid
    ->
        checkAllPrIds(Program, 0, N, Storage, VisitedStorages, NewVisitedStorages, Result)
    ;
        Result = result(false, PrId1, PrId2)
    ).

checkAllPrIds(_, N, N, _, _, _, result(true, -1, -1)).
checkAllPrIds(Program, PrId, N,
              Storage, VisitedStorages, NewVisitedStorages, Result) :-
    PrId < N,
    step(Program, state(N, Storage, VisitedStorages), PrId, state(N, CurrStorage, CurrVisitedStorages)),
    length(VisitedStorages, Len1),
    length(CurrVisitedStorages, Len2),
    (   Len1 \= Len2
    ->
        checkState(Program, state(N, CurrStorage, CurrVisitedStorages), ChildVisistedStorages, TempResult)
    ;
        TempResult = result(true, -1, -1)
    ),
    TempResult =.. [_, Good, _, _],
    (   Good
    ->
        Result = TempResult
    ;
        NextPrId is PrId+1,
        checkAllPrIds(Program, NextPrId, N, Storage, ChildVisistedStorages, NewVisitedStorages, Result)
    ).


checkCriticalSection(Program, State, Result) :-
    State =.. [_, _, Storage, _],
    Storage =.. [_, _, _, Lines],
    Program =.. [_, _, _, Stmts],
    sectionKeywordPrIdList(Stmts, Lines, 0, PrIds),
    length(PrIds, Len),
    (   Len >= 2
    ->
        PrIds = [PrId1, PrId2|_],
        Result = result(false, PrId1, PrId2)
    ;
        Result = result(true, -1, -1)
    ).

sectionKeywordPrIdList(_, [], _, []) :- !.
sectionKeywordPrIdList(Stmts, [L|Lines], PrId, PrIds) :-
    NextPrId is PrId+1,
    sectionKeywordPrIdList(Stmts, Lines, NextPrId, NewPrIds),
    nth1(L, Stmts, Line),
    (   Line = sekcja
    ->  
        PrIds = [PrId|NewPrIds]
    ;
        PrIds = NewPrIds
    ).

step(Program, StanWe, PrId, StanWy) :-
    Program =.. [_, _, _, Stmts],
    StanWe =.. [_, N, Storage, VisitedStorages],
    Storage =.. [_, _, _, Lines],
    nth0(PrId, Lines, Line),
    nth1(Line, Stmts, Stmt),
    write('PrId: '),write(PrId),nl,
    write('evalStmt: '),write(Stmt),nl,
    evalStmt(Stmt, PrId, Storage, Line, NewStorage, NewLine),
    NewStorage =.. [_, NewVars, NewArrs, _],
    delete(VisitedStorages, Storage, NewVisitedStorages),
    NewerVisitedStorages = [Storage|NewVisitedStorages], 
    nth0(PrId, Lines, _, NewLines),
    nth0(PrId, NewerLines, NewLine, NewLines),
    NewerStorage = storage(NewVars, NewArrs, NewerLines),
    StanWy = state(N, NewerStorage, NewerVisitedStorages).

% evalExpr
evalExpr(Var, PrId, Storage, Val) :-
    atom(Var),
    (   Var = pid
    ->
        Val = PrId
    ;   
        getVariable(Storage, Var, Val)
    ).

evalExpr(Num, _, _, Val) :-
    integer(Num),
    Val is Num.

evalExpr(array(ArrName, IdExpr), PrId, Storage, Val) :-
    evalExpr(IdExpr, PrId, Storage, Id),
    getArrayElem(Storage, ArrName, Id, Val).

evalExpr(Expr, PrId, Storage, Val) :-
    Expr =.. [Op, L, R],
    member(Op, [+,-,*,/]),
    evalExpr(L, PrId, Storage, NewL),
    evalExpr(R, PrId, Storage, NewR),
    NewExpr =.. [Op, NewL, NewR],
    Val is NewExpr.

% evalBoolExpr
evalBoolExpr(BExpr, PrId, Storage, BVal) :-
    BExpr =.. [Op, L, R],
    evalExpr(L, PrId, Storage, LVal),
    evalExpr(R, PrId, Storage, RVal),
    NewBExpr =.. [Op, LVal, RVal],
    BVal is NewBExpr.

% evalStmt
evalStmt(assign(VarName, Expr), PrId,
         Storage, Line, NewStorage, NewLine) :-
    atom(VarName),
    evalExpr(Expr, PrId, Storage, Val),
    setVariable(Storage, VarName, Val, NewStorage),
    NewLine is Line+1.

evalStmt(assign(array(ArrName, IdExpr), Expr), PrId,
         Storage, Line, NewStorage, NewLine) :-
    evalExpr(Expr, PrId, Storage, Val),
    evalExpr(IdExpr, PrId, Storage, Id),
    setArrayElem(Storage, ArrName, Id, Val, NewStorage),
    NewLine is Line+1.

evalStmt(goto(LineNr), _,
         Storage, _, NewStorage, NewLine) :-
    NewStorage = Storage,
    NewLine = LineNr.

evalStmt(condGoto(BoolExpr, LineNr), PrId,
         Storage, Line, NewStorage, NewLine) :-
    NewStorage = Storage,
    evalBoolExpr(BoolExpr, PrId, Storage, BVal),
    (   BVal
    ->
        NewLine = LineNr
    ;
        NewLine = Line+1
    ).

evalStmt(sekcja, _, 
         Storage, Line, NewStorage, NewLine) :-
    NewStorage = Storage,
    NewLine is Line+1.

    