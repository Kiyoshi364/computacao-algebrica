:- module(singular, [
  % Top level usage
  compile//2, compile//7,
  % Output primitives
  header//2,
  def_poly_eq_dom_gen//5,
  def_polys_eqs_dom_gen//6,
  def_ideal//2, print_ideal//1,
  % Equation DSL
  equation//2,
  % Domain primitives
  domain_vars/2, domain_roots/2,
  domain_vareqs/2, domain_vareqs/3,
  domain_rooteqs/2, domain_rooteqs/3
]).

:- use_module(library(clpz), [
  op(700, xfx, #<),
  op(700, xfx, #=)
]).
:- use_module(library(dcgs)).
:- use_module(library(lambda)).
:- use_module(library(lists), [foldl/4]).

%%% Domain in Standard Prolog %%%

:- meta_predicate(foldl_range(3, ?, ?, ?, ?)).
foldl_range(Pred, Low, High, A0, A) :-
  ( Low #< High,
    Low1 #= Low + 1,
    call(Pred, Low, A0, A1),
    foldl_range(Pred, Low1, High, A1, A)
  ; Low #= High,
    A0 = A
  ).

domain_vars(unityroots(_, NVars), Vars) :-
  foldl_range(
    \Idx^[var(x, Idx) | Vs]^Vs^true,
    0, NVars, Vars, []).
domain_vars(boolean(BNs), Vars) :-
  foldl(
    \ (B-N)^Vs0^Vs^(
      foldl_range(
        \Idx^[var(B, Idx) | VVs]^VVs^true,
        0, N, Vs0, Vs
      )
    ),
    BNs, Vars, []
  ).

domain_roots(unityroots(N, _), Roots) :-
  foldl_range(
    \Idx^[var(w, Idx) | Vs]^Vs^true,
    0, N, Roots, []
  ).

domain_vareqs(D, Eqs) :- domain_vareqs(D, Eqs, []).

domain_vareqs(D, Eqs0, Eqs) :-
  domain_vars(D, Vars),
  foldl(
    \X^[var_indomain(X) | Es]^Es^true,
    Vars, Eqs0, Eqs
  ).

domain_rooteqs(D, Eqs) :- domain_rooteqs(D, Eqs, []).

domain_rooteqs(unityroots(N, NVars), Eqs0, Eqs) :-
  domain_roots(unityroots(N, NVars), Roots),
  unityroots_rooteqs(Roots, Eqs0, X, X, Eqs).
domain_rooteqs(boolean(_), Eqs, Eqs).

unityroots_rooteqs([], DomEqs, DomEqs, DiffEqs, DiffEqs).
unityroots_rooteqs([Root | Roots], DomEqs0, DomEqs, DiffEqs0, DiffEqs) :-
  DomEqs0 = [var_indomain(Root) | DomEqs1],
  unityroots_diffroots(Roots, Root, DiffEqs0, DiffEqs1),
  unityroots_rooteqs(Roots, DomEqs1, DomEqs, DiffEqs1, DiffEqs).

unityroots_diffroots([], _, DiffEqs, DiffEqs).
unityroots_diffroots([RootB | Roots], RootA, DiffEqs0, DiffEqs) :-
  DiffEqs0 = [var_diff(RootA, RootB) | DiffEqs1],
  unityroots_diffroots(Roots, RootA, DiffEqs1, DiffEqs).

%%% DCGs Hellpers %%%

atom(A) --> { atom_chars(A, Cs) }, Cs.
number(N) --> { number_chars(N, Cs) }, Cs.

%%% BoolExpr %%%

boolexpr(false) --> "0".
boolexpr(true) --> "1".
boolexpr(var(Name, Idx)) --> varname(var(Name, Idx)).
boolexpr(not(A)) --> "1-(", boolexpr(A), ")".
boolexpr(and(A, B)) --> "(", boolexpr(A), ")*(", boolexpr(B), ")".
boolexpr(or(A, B)) -->
  "(", boolexpr(A), ")+(", boolexpr(B), ")-((",
  boolexpr(A), ")*(", boolexpr(B), "))".
boolexpr(xor(A, B)) -->
  "(", boolexpr(A), ")+(", boolexpr(B), ")-(2*(",
  boolexpr(A), ")*(", boolexpr(B), "))".

%%% Equation Helpers %%%

varname(var(Name, Idx)) --> atom(Name), "(", number(Idx), ")".

varname_exp(Var, Exp) --> varname(Var), "^", number(Exp).

varname_isname(Var, Is) --> varname(Var), " - ", varname(Is).

domain_varname_in(unityroots(N, _), Var) -->
  varname_exp(Var, N), " - 1".
domain_varname_in(boolean(_), Var) -->
  varname(Var), "*(", varname(Var), " - 1)".

domain_varname_diffname(D, Var, Diff) -->
  "((", domain_varname_in(D, Var), ") - (", domain_varname_in(D, Diff), "))/(",
  varname_isname(Var, Diff), ")".

domain_boolexprs_count(unityroots(_,_), _, _) --> { false }.
domain_boolexprs_count(boolean(_), [BExpr | BExprs], Count) -->
  boolean_bexpr(BExpr),
  boolean_bexprs_sum(BExprs, Count).

boolean_bexpr(BExpr) --> "(", boolexpr(BExpr), ")".

boolean_bexprs_sum([], Sum) --> " - ", number(Sum).
boolean_bexprs_sum([BExpr | BExprs], Sum) -->
  " + ", boolean_bexpr(BExpr),
  boolean_bexprs_sum(BExprs, Sum).

%%% Equation DSL Interpreter %%%

equation(var_indomain(Var), D) --> domain_varname_in(D, Var).
equation(var_diff(Var, Diff), D) --> domain_varname_diffname(D, Var, Diff).
equation(var_is(Var, Is), _) --> varname_isname(Var, Is).
equation(boolexprs_count(BExprs, Count), D) --> domain_boolexprs_count(D, BExprs, Count).

%%% Singular Helpers %%%

endcmd --> ";\n".

def_var_count(Name, N) -->
  { N1 #= N - 1 },
  atom(Name), "(0..", number(N1), ")".

domain_defvars(unityroots(N, NVars)) -->
  def_var_count(x, NVars), ",",
  def_var_count(w, N).
domain_defvars(boolean([B-N | Bs])) -->
  def_var_count(B, N),
  boolean_domain_defvars(Bs).

boolean_domain_defvars([]) --> [].
boolean_domain_defvars([B-N | Bs]) -->
  ",", def_var_count(B, N),
  boolean_domain_defvars(Bs).

poly_name(prefixed(Prefix, PID)) --> atom(Prefix), number(PID).

polys_names([PName | PNames]) -->
  polys_names_(PNames, PName).

polys_names_([], P) --> poly_name(P).
polys_names_([PName | PNames], P) -->
  poly_name(P), ",", polys_names_(PNames, PName).

ideal_name(prefixed(Prefix, IID)) --> atom(Prefix), number(IID).
ideal_name(name(Name)) --> atom(Name).

%%% Singular Toplevel Commands %%%

header(Dom, Ord) -->
  "option(redSB)", endcmd,
  "ring r = 0,(",
  domain_defvars(Dom),
  "),", atom(Ord), endcmd.

gen_polyname(gen_prefix(Prefix, PID), gen_prefix(Prefix, PID1), prefixed(Prefix, PID)) -->
  { PID1 #= PID + 1 }, poly_name(prefixed(Prefix, PID)).

def_poly_eq_dom_gen(Eq, Dom, PName, Gen0, Gen) -->
  "poly ", gen_polyname(Gen0, Gen, PName), " = ", equation(Eq, Dom), endcmd.

def_polys_eqs_dom_gen([], _, Gen, Gen, PNames, PNames) --> [].
def_polys_eqs_dom_gen([Eq | Eqs], Dom, Gen0, Gen, PNames0, PNames) -->
  { PNames0 = [PName | PNames1] },
  def_poly_eq_dom_gen(Eq, Dom, PName, Gen0, Gen1),
  def_polys_eqs_dom_gen(Eqs, Dom, Gen1, Gen, PNames1, PNames).

def_ideal(IName, PNames) -->
  "ideal ", ideal_name(IName), " = std(ideal(", polys_names(PNames), "))", endcmd.

print_ideal(IName) --> ideal_name(IName), endcmd.

compile(Eqs, Dom) -->
  compile(Eqs, Dom, lp, gen_prefix(d, 0), gen_prefix(k, 0), gen_prefix(h, 0), name(i)).
compile(Eqs, Dom, Ord, Root_gen, Dom_gen, Poly_gen, IName) -->
  header(Dom, Ord),
  { domain_rooteqs(Dom, REqs),
    domain_vareqs(Dom, VEqs) },
  def_polys_eqs_dom_gen(REqs, Dom, Root_gen, _, PNames, PNames1),
  def_polys_eqs_dom_gen(VEqs, Dom, Dom_gen, _, PNames1, PNames2),
  def_polys_eqs_dom_gen(Eqs, Dom, Poly_gen, _, PNames2, []),
  def_ideal(IName, PNames),
  print_ideal(IName).
