% Program security checker in Prolog
% Author: Cezary Bednarz

:- ensure_loaded(library(lists)).
:- op(700, xfx, <>).                                    % zdefiniuj brakujacy
X <> Y :- X \= Y.                                       % operator <>

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
        LastStmtLine is StmtsLen+1,                     % zakonczone procesy
        append(Stmts, [goto(LastStmtLine)], NewStmts),  % beda w petli w goto
        TermProg = program(Variables, Arrays, NewStmts),
        initState(TermProg, N, InitState),
        checkState(TermProg, InitState, _, Result),     % zacznij rekurencje
        Result =.. [_, Valid, PrId1, PrId2, Path],      % odzyskaj wyniki
        (   Valid
        ->
            write('Program jest poprawny (bezpieczny).\n')
        ;
            write('Program jest niepoprawny.\n'),
            write('Niepoprawny przeplot:\n'),
            writePath(Path, LastStmtLine),
            format('Procesy w sekcji: ~d, ~d.\n', 
                   [PrId1, PrId2])
        ),
        seen
    ).
verify(_, Program) :-
    format('Error: brak pliku o nazwie - ~s',           % wywolywane gdy nie ma
           [Program]),nl.                               % pliku o danej nazwie

writePath([], _).                                       % wypisz sciezke
writePath([[Proc,Line]|Path], N1) :-                    % ktora prowadzi do 
    (   Line \= N1                                      % przeplotu (nie 
    ->                                                  % wypisuj ostatniej
        format('   Proces ~d: ~d\n', [Proc,Line])       % instrukcji: goto(N+1))
    ;
        true
    ),
    writePath(Path, N1).


% storage:
%  - vars: zmienne, trzymane jako lista par [Nazwa,Wartosc]
%  - arrs: tablice, trzymane jako lista par [Nazwa,Lista wartosci]
%  - lines: lista licznikow instrukcji dla wszystkich procesow
storage(vars, arrs, lines).
% state: 
%  - n: liczba z zadania (liczba procesow, itd.)
%  - currentStorage: stan pamieci w danym momencie, typ: storage
%  - visitedStorages: odwiedzone stany pamieci, typ: lista storage
state(n, currentStorage, visitedStorages).

build(X, N, List) :-                                    % buduje List jako 
    length(List, N),                                    % powtorzone N razy X
    maplist(=(X), List).

mergeLists([], [], []).                                 % laczy 2 listy w 
mergeLists([X|L1], [Y|L2], [[X,Y]|List]) :-             % jedna liste par
    mergeLists(L1, L2, List).

initState(Program, N, StanPoczatkowy) :-
    Program =.. [_, Variables, Arrays, _],
    length(Variables, VariablesLen),                    
    build(0, VariablesLen, InitVariables),              % zainicjalizuj pusta 
    mergeLists(Variables, InitVariables, VariablesList),% liste zmiennych
    N1 is N+1,
    length(Arrays, ArraysLen),
    build(0, N1, ZeroArray),                            
    build(ZeroArray, ArraysLen, InitArrays),            % zainicjalizuj pusta
    mergeLists(Arrays, InitArrays, ArraysList),         % liste tablic
    build(1, N, LinesList),                             % tablica instrukcji 
    Storage = storage(VariablesList, ArraysList,     
                      LinesList),
    StanPoczatkowy = state(N, Storage, [Storage]). 


getElemFromPairList([], _, Val) :-                      % wyjmij element z listy
    Val is -1.                                          % par stojacy na
getElemFromPairList([[N,V]|PairList], Name, Val) :-     % miejscu Name
    (   N = Name
    ->  
        Val = V
    ;
        getElemFromPairList(PairList, Name, Val)
    ).

removeElemFromPairList(PairList, Name, NewPairList) :-  % usun element z listy
    getElemFromPairList(PairList, Name, Val),           % par stojacy na
    delete(PairList, [Name,Val], NewPairList).          % miejscu name

getVariable(Storage, VarName, Value) :-                 % wyjmij zmienna o
    Storage =.. [_, Vars, _, _],                        % nazwie VarName
    getElemFromPairList(Vars, VarName, Value).

getArrayElem(Storage, ArrName, Id, Value) :-            % wyjmij element z 
    Storage =.. [_, _, Arrs, _],                        % tablicy ArrName
    getElemFromPairList(Arrs, ArrName, Array),          % na miejscu Id
    nth0(Id, Array, Value).

setVariable(Storage, VarName, Value, NewStorage) :-     % ustaw zmienna o nazwie
    Storage =..[_, Vars, Arrs, Lines],                  % Varname na Value
    removeElemFromPairList(Vars, VarName, NewVars),
    NewerVars = [[VarName, Value]|NewVars],
    NewStorage = storage(NewerVars, Arrs, Lines).

setArrayElem(Storage, ArrName, Id, Value, NewStorage) :-% ustaw element Id
    Storage =.. [_, Vars, Arrs, Lines],                 % tablicy ArrName
    getElemFromPairList(Arrs, ArrName, Arr),            % na Value
    removeElemFromPairList(Arrs, ArrName, NewArrs),
    nth0(Id, Arr, _, NewArr),
    nth0(Id, NewerArr, Value, NewArr),
    NewerArrs = [[ArrName,NewerArr]|NewArrs],
    NewStorage = storage(Vars, NewerArrs, Lines).



checkState(Program, State, NewVisitedStorages, Result):-% sprawdz czy dany stan 
    State =.. [_, N, Storage, VisitedStorages],         % prowadzi do pojawienia
    checkCriticalSection(Program, State,                % sie 2 procesow 
                         result(IsValid, PrId1, PrId2,  % w sekcji krytycznej
                                Path)),
    (   IsValid
    ->
        checkAllPrIds(Program, 0, N, Storage, VisitedStorages, 
                      NewVisitedStorages, Result)
    ;
        Result = result(false, PrId1, PrId2, Path)
    ).

checkAllPrIds(_, N, N, _,                               % przeiteruj sie po 
              VisitedStorages, NewVisitedStorages,      % wszystkich procesach 
              result(true, -1, -1, [])) :-              % i wykonaj krok, jesli
    NewVisitedStorages = VisitedStorages.               % prowadzi do nowego 
checkAllPrIds(Program, PrId, N,                         % stanu
              Storage, VisitedStorages, NewVisitedStorages, Result) :-
    PrId < N,
    step(Program, state(N, Storage, VisitedStorages), 
         PrId, state(N, CurrStorage, CurrVisitedStorages)),
    Storage =.. [_, _, _, Lines],
    nth0(PrId, Lines, CurrLine),
    length(VisitedStorages, Len1),
    length(CurrVisitedStorages, Len2),
    (   Len1 \= Len2
    ->
        checkState(Program, state(N, CurrStorage, CurrVisitedStorages), 
                   ChildVisistedStorages, TempResult)
    ;
        TempResult = result(true, -1, -1, []),
        ChildVisistedStorages = CurrVisitedStorages 
    ),
    TempResult =.. [_, Good, PrId1, PrId2, PrevPath],
    (   not(Good)
    ->
        Result = result(false, PrId1, PrId2, 
                        [[PrId, CurrLine]|PrevPath])
    ;
        NextPrId is PrId+1,
        checkAllPrIds(Program, NextPrId, N, Storage, 
                      ChildVisistedStorages, NewVisitedStorages, Result)
    ).


checkCriticalSection(Program, State, Result) :-         % sprawdz czy 2 procesy
    State =.. [_, _, Storage, _],                       % sa w sekcji krytycznej
    Storage =.. [_, _, _, Lines],                       % i jesli tak to zacznij
    Program =.. [_, _, _, Stmts],                       % cofanie sie rekurencji
    sectionKeywordPrIdList(Stmts, Lines, 0, PrIds),     % i tworzenie sciezki
    length(PrIds, Len),                                 % po ktorej mozna
    (   Len >= 2                                        % odtworzyc wynik
    ->
        PrIds = [PrId1, PrId2|_],
        Result = result(false, PrId1, PrId2, [])
    ;
        Result = result(true, -1, -1, [])
    ).

sectionKeywordPrIdList(_, [], _, []) :- !.              % otrzymaj liste
sectionKeywordPrIdList(Stmts, [L|Lines], PrId, PrIds) :-% indeksow instrukcji
    NextPrId is PrId+1,                                 % wskazujacych
    sectionKeywordPrIdList(Stmts, Lines, NextPrId,      % na instrukcje 'sekcja'
                           NewPrIds),
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
    nth1(Line, Stmts, Stmt),                            % wez instrukcje 
    evalStmt(Stmt, PrId, Storage, Line, NewStorage, NewLine),
    NewStorage =.. [_, NewVars, NewArrs, _],
    nth0(PrId, Lines, _, NewLines),                     % przesun wskaznik
    nth0(PrId, NewerLines, NewLine, NewLines),          % instrukcji
    NewerStorage = storage(NewVars, NewArrs, NewerLines),
    delete(VisitedStorages, NewerStorage, NewVisitedStorages),
    NewerVisitedStorages =                              % wrzuc storage do 
        [NewerStorage|NewVisitedStorages],              % zbioru odwiedzonych
    StanWy = state(N, NewerStorage, NewerVisitedStorages).


evalExpr(Var, PrId, Storage, Val) :-                    % ewaluacja wyrazen
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


evalBoolExpr(BExpr, PrId, Storage) :-                   % ewaluacja wyrazen
    BExpr =.. [Op, L, R],                               % boolowskich
    evalExpr(L, PrId, Storage, LVal),
    evalExpr(R, PrId, Storage, RVal),
    call(Op, LVal, RVal).


evalStmt(assign(VarName, Expr), PrId,                   % ewaluacja instrukcji
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
    NewLine is LineNr.

evalStmt(condGoto(BoolExpr, LineNr), PrId,
         Storage, Line, NewStorage, NewLine) :-
    NewStorage = Storage,
    (   evalBoolExpr(BoolExpr, PrId, Storage)
    ->
        NewLine is LineNr
    ;
        NewLine is Line+1
    ).

evalStmt(sekcja, _, 
         Storage, Line, NewStorage, NewLine) :-
    NewStorage = Storage,
    NewLine is Line+1.

    