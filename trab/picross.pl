:- module(picross, [
  main/1, main/2,
  example_picross/2,
  picross_dom_eqs/3
]).

:- use_module(singular, [
  compile//2,
  check_domain_eqs/2,
  foldl_range/5
]).

:- use_module(library(clpz), [
  op(700, xfx, #<),
  op(700, xfx, #=)
]).
:- use_module(library(lambda), [
  (^)/3, (^)/4, (^)/5,
  (\)/4,
  (+\)/5,
  op(201, xfx, +\)
]).
:- use_module(library(lists), [
  maplist/2, foldl/4, length/2
]).
:- use_module(library(pio), [phrase_to_stream/2]).

%%% General Picross %%%

check_size_constrain(N, Cs) :-
  Sum #< N + 1,
  foldl(\X^S0^S^(S #= X + S0 + 1), Cs, -1, Sum).

tag_ij_var(row, Idx, Jdx, var(x, [Idx, Jdx])).
tag_ij_var(col, Idx, Jdx, var(x, [Jdx, Idx])).

constrain_tag_ij_size_expr_bexprs([], _, _, _, _, Expr, [Expr | BEs], BEs).
constrain_tag_ij_size_expr_bexprs([Num | Nums], Tag, Idx, Jdx, N, Expr, BEs0, BEs) :-
  NumJdx #= Num + Jdx,
  ( NumJdx #< N + 1,
    Jdx1 #= Jdx + 1,
    NumJdx1 #= NumJdx + 1,
    foldl_range(
      t(Tag, Idx)+\A^E0^and(E0, V)^tag_ij_var(Tag, Idx, A, V),
      Jdx, NumJdx, Expr, Expr1
    ),
    constrain_tag_ij_size_expr_bexprs(Nums, Tag, Idx, NumJdx1, N, Expr1, BEs0, BEs1),
    constrain_tag_ij_size_expr_bexprs([Num | Nums], Tag, Idx, Jdx1, N, Expr, BEs1, BEs)
  ; N #< NumJdx,
    BEs0 = BEs
  ).

constrains_tag_i_size_eqs([], _, _, _, Eqs, Eqs).
constrains_tag_i_size_eqs([Nums | Cs], Tag, Idx, N, Eqs0, Eqs) :-
  Idx1 #= Idx + 1,
  Eqs0 = [boolexprs_count(BEs, 1) | Eqs1],
  constrain_tag_ij_size_expr_bexprs(Nums, Tag, Idx, 0, N, true, BEs, []),
  constrains_tag_i_size_eqs(Cs, Tag, Idx1, N, Eqs1, Eqs).

countconstrains_tag_i_size_eqs([], _, _, _, Eqs, Eqs).
countconstrains_tag_i_size_eqs([Nums | Cs], Tag, Idx, N, Eqs0, Eqs) :-
  Idx1 #= Idx + 1,
  Eqs0 = [boolexprs_count(BEs, Sum) | Eqs1],
  foldl(\A^B^S^(S #= A + B), Nums, 0, Sum),
  foldl_range(
    t(Tag, Idx)+\Jdx^[V | Bs]^Bs^tag_ij_var(Tag, Idx, Jdx, V),
    0, N, BEs, []
  ),
  countconstrains_tag_i_size_eqs(Cs, Tag, Idx1, N, Eqs1, Eqs).

picross_dom_eqs(Rs-Cs, boolean([x-[N, N]]), Eqs) :-
  length(Rs, N),
  length(Cs, N),
  maplist(check_size_constrain(N), Rs),
  maplist(check_size_constrain(N), Cs),
  constrains_tag_i_size_eqs(Rs, row, 0, N, Eqs, Eqs1),
  constrains_tag_i_size_eqs(Cs, col, 0, N, Eqs1, Eqs2),
  countconstrains_tag_i_size_eqs(Rs, row, 0, N, Eqs2, Eqs3),
  countconstrains_tag_i_size_eqs(Cs, col, 0, N, Eqs3, []).

%%% Examples %%%

example_picross_small(0, [
  [1], [1], [4], [4], [5]
]-[
  [2], [3], [5], [3], [1,1]
]).
example_picross_small(1, [
  [1], [4], [2,2], [4], [1]
]-[
  [1], [3], [1,1], [5], [3]
]).

example_picross_medium(0, [
  [2,2], [2,3,1], [8], [4,1], [1,1,3], [1,1,4], [1,3], [2,2], [3,1], [1,1,3]
]-[
  [2], [2,1], [3,3], [3,1,1], [1,2,2], [3,2], [2,1,2], [7,1], [1,1,4,1], [2,1,2]
]).
example_picross_medium(1, [
  [5], [2,2], [1,1,1], [2,1,1], [4,2], [1,2,1], [1,1,1], [2,1], [1,1,1], [7]
]-[
  [1,1], [4,3], [2,3,1], [1,1,1], [1,2,1], [1,1,2], [2,1,1], [5,1], [1,1], [4]
]).

example_picross(small(I) , Table) :- example_picross_small( I, Table).
example_picross(medium(I), Table) :- example_picross_medium(I, Table).

%%% Main %%%

main(Example) :-
  current_output(S),
  main(Example, S).

main(Example, S) :-
  example_picross(Example, RCs),
  picross_dom_eqs(RCs, Dom, Eqs),
  phrase_to_stream(compile(Dom, Eqs), S).
