:- module(sudoku, [
  main/2, main/3,
  example_sudoku/2,
  table_domtype_domain_eqs/4
]).

:- use_module(singular, [
  compile//2,
  check_domain_eqs/2,
  foldl_range/5
]).

:- use_module(library(clpz), [
  label/1,
  (#<)/2, (#=)/2,
  op(700, xfx, #<),
  op(700, xfx, #=),
  op(700, xfx, #\=)
]).
:- use_module(library(lambda), [
  (^)/3, (^)/4, (^)/5,
  (\)/4,
  (+\)/3, (+\)/5,
  op(201, xfx, +\)
]).
:- use_module(library(lists), [
  maplist/2, foldl/4, length/2
]).
:- use_module(library(pio), [phrase_to_stream/2]).

%%% General Sudoku %%%

domtype_length_dom(unityroots, NN, unityroots(w-[NN], [x-[NN, NN]])).
domtype_length_dom(boolean, NN, boolean([x-[NN, NN, NN]])).

domtype_length_domeqs(unityroots, _, Eqs, Eqs).
domtype_length_domeqs(boolean, NN, Eqs0, Eqs) :-
  foldl_range(
    NN+\Idx^E1s0^E1s^foldl_range(
      NN+\Jdx^[boolexprs_count(BEs, 1) | E2s]^E2s^foldl_range(
        \Num^[var(x, [Idx, Jdx, Num]) | BE1s]^BE1s^true,
        0, NN, BEs, []
      ),
      0, NN, E1s0, E1s
    ),
    0, NN, Eqs0, Eqs
  ).

length_size_difpairs(NN, N, Ds) :- length_size_difpairs(NN, N, Ds, []).

length_size_difpairs(NN, N, Ds0, Ds) :-
  % Lines
  foldl_range(
    NN+\Idx^D1s0^D1s^foldl_range(
      NN+\Jdx^D2s0^D2s^(
        Jdx1 #= Jdx + 1,
        foldl_range(
          \Kdx^[dif(Idx, Jdx, Idx, Kdx) | D3s]^D3s^true,
          Jdx1, NN, D2s0, D2s
        )
      ),
      0, NN, D1s0, D1s
    ),
    0, NN, Ds0, Ds1
  ),
  % Columns
  foldl_range(
    NN+\Idx^D1s0^D1s^foldl_range(
      NN+\Jdx^D2s0^D2s^(
        Jdx1 #= Jdx + 1,
        foldl_range(
          \Kdx^[dif(Jdx, Idx, Kdx, Idx) | D3s]^D3s^true,
          Jdx1, NN, D2s0, D2s
        )
      ),
      0, NN, D1s0, D1s
    ),
    0, NN, Ds1, Ds2
  ),
  % Squares
  foldl_range(
    t(NN, N)+\Idx^D1s0^D1s^(
      XBase #= mod(Idx, N)*N,
      YBase #= div(Idx, N)*N,
      foldl_range(
        t(NN, N, XBase, YBase)+\Jdx^D2s0^D2s^(
          XL1 #= mod(Jdx, N),
          YL1 #= div(Jdx, N),
          X1 #= XBase + XL1,
          Y1 #= YBase + YL1,
          Jdx1 #= (YL1 + 1)*N,
          foldl_range(
            t(N, XBase, YBase, X1, Y1)+\Kdx^D3s0^D3s^(
              XL2 #= mod(Kdx, N),
              YL2 #= div(Kdx, N),
              X2 #= XBase + XL2,
              Y2 #= YBase + YL2,
              ( X1 #=  X2, D3s0 = D3s
              ; X1 #\= X2, D3s0 = [dif(X1, Y1, X2, Y2) | D3s]
              )
            ),
            Jdx1, NN, D2s0, D2s
          )
        ),
        0, NN, D1s0, D1s
      )
    ),
    0, NN, Ds2, Ds
  ).

domtype_length_difpair_difeqs(unityroots, _, dif(X1, Y1, X2, Y2), Eqs0, Eqs) :-
  Eqs0 = [
    var_diff(var(x, [X1, Y1]), var(x, [X2, Y2]))
  | Eqs].
domtype_length_difpair_difeqs(boolean, NN, dif(X1, Y1, X2, Y2), Eqs0, Eqs) :-
  foldl_range(
    diff(X1, Y1, X2, Y2)+\Num^[and(var(x, [X1, Y1, Num]), var(x, [X2, Y2, Num])) | Bs]^Bs^true,
    0, NN, BEs, []
  ),
  Eqs0 = [ boolexprs_count(BEs, 0) | Eqs].

difpairs_length_domtype_difeqs(Ds, NN, DomType, Eqs0, Eqs) :-
  foldl(
    domtype_length_difpair_difeqs(DomType, NN),
    Ds, Eqs0, Eqs
  ).

table_domtype_iseqs(Table, DomType, Eqs0, Eqs) :-
  table_domtype_row_iseqs(Table, DomType, 0, Eqs0, Eqs).

table_domtype_row_iseqs([], _, _, Eqs, Eqs).
table_domtype_row_iseqs([Row | Table], DomType, Idx, Eqs0, Eqs) :-
  Idx1 #= Idx + 1,
  row_domtype_row_col_iseqs(Row, DomType, Idx, 0, Eqs0, Eqs1),
  table_domtype_row_iseqs(Table, DomType, Idx1, Eqs1, Eqs).

row_domtype_row_col_iseqs([], _, _, _, Eqs, Eqs).
row_domtype_row_col_iseqs([X | Row], DomType, Idx, Jdx, Eqs0, Eqs) :-
  Jdx1 #= Jdx + 1,
  place_domtype_row_col_iseqs(X, DomType, Idx, Jdx, Eqs0, Eqs1),
  row_domtype_row_col_iseqs(Row, DomType, Idx, Jdx1, Eqs1, Eqs).

place_domtype_row_col_iseqs(x, _, _, _, Eqs, Eqs).
place_domtype_row_col_iseqs(x(Num), DomType, Idx, Jdx, [Eq | Eqs], Eqs) :-
  domtype_row_col_num_iseq(DomType, Idx, Jdx, Num, Eq).

domtype_row_col_num_iseq(unityroots, Idx, Jdx, Num, var_is(var(x, [Idx, Jdx]), var(w, [Num1]))) :- Num1 #= Num - 1.
domtype_row_col_num_iseq(boolean, Idx, Jdx, Num, boolexprs_count([var(x, [Idx, Jdx, Num1])], 1)) :- Num1 #= Num - 1.

table_domtype_domain_eqs(Table, DomType, Dom, Eqs) :-
  length(Table, NN),
  maplist(NN+\L^length(L, NN), Table),
  NN #= N*N,
  0 #< N,
  label([N]),
  domtype_length_dom(DomType, NN, Dom),
  domtype_length_domeqs(DomType, NN, Eqs, Eqs1),
  length_size_difpairs(NN, N, Ds),
  difpairs_length_domtype_difeqs(Ds, NN, DomType, Eqs1, Eqs2),
  table_domtype_iseqs(Table, DomType, Eqs2, []).

%%% Examples %%%

% Um Primeiro Contato com Bases de Gröbner, §6.3.2, p. 114
example_sudoku_small(0, [
  [x   , x(4), x   , x(1)],
  [x(3), x   , x   , x   ],

  [x   , x   , x   , x(4)],
  [x   , x   , x   , x   ]
]).
% Gröbner Bases and Sudoku Puzzles -- Courtney Thomas
example_sudoku_small(1, [
  [x   , x   , x   , x(4)],
  [x(4), x   , x(2), x   ],

  [x   , x(3), x   , x(1)],
  [x(1), x   , x   , x   ]
]).

% Um Primeiro Contato com Bases de Gröbner, §6.3.2, p. 114
example_sudoku_big(0, [
  [x   , x   , x   , x   , x   , x   , x   , x(1), x   ],
  [x(4), x   , x   , x   , x   , x   , x   , x   , x   ],
  [x   , x(2), x   , x   , x   , x   , x   , x   , x   ],

  [x   , x   , x   , x   , x(5), x   , x(4), x   , x(1)],
  [x   , x   , x(8), x   , x   , x   , x(3), x   , x   ],
  [x   , x   , x(1), x   , x(9), x   , x   , x   , x   ],

  [x(3), x   , x   , x(4), x   , x   , x(2), x   , x   ],
  [x   , x(5), x   , x(1), x   , x   , x   , x   , x   ],
  [x   , x   , x   , x(8), x   , x(6), x   , x   , x   ] 
]).

example_sudoku(small(I), Table) :- example_sudoku_small(I, Table).
example_sudoku(big(I)  , Table) :- example_sudoku_big(  I, Table).

%%% Main %%%

main(Example, DomType) :-
  current_output(S),
  main(Example, DomType, S).

main(Example, DomType, S) :-
  example_sudoku(Example, Table),
  table_domtype_domain_eqs(Table, DomType, Dom, Eqs),
  phrase_to_stream(compile(Dom, Eqs), S).
