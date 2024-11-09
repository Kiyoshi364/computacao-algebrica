:- module(singular, [
  % Top level usage
  compile//3, % compile//6,
  % Output primitives
  header//3,
  % def_poly//2, def_polys//2, gendef_polys//3,
  % def_ideal//2, print_ideal//1,
  % Equation DSL
  equation//2
]).

:- use_module(library(clpz), [
  op(700, xfx, #<),
  op(700, xfx, #=)
]).
:- use_module(library(dcgs)).

%%% DCGs Hellpers %%%

atom(A) --> { atom_chars(A, Cs) }, Cs.
number(N) --> { number_chars(N, Cs) }, Cs.

%%% Equation Helpers %%%

varname(var(Name, Idx)) --> atom(Name), "(", number(Idx), ")".

varname_exp(Var, Exp) --> varname(Var), "^", [Exp].

varname_isname(Var, Is) --> varname(Var), " - ", varname(Is).

domain_varname_in(unityroots(_), Var) --> varname(Var), " - 1".

domain_varname_diffname(D, Var, Diff) -->
  "((", domain_varname_in(D, Var), ") - (", domain_varname_in(D, Diff), "))/(",
  varname_isname(Var, Diff), ")".

%% Std Prolog

domain_varidx_name(_, Idx, var(x, Idx)).
domain_rootidx_name(_, Idx, var(w, Idx)).

domain_rooteqs(D, Eqs) :- domain_rooteqs(D, Eqs, []).

domain_rooteqs(uniyroots(N), Eqs0, Eqs) :-
  unityroots_rooteqs(0, N, Eqs0, X, X, Eqs).

unityroots_rooteqs(Idx, N, DomEqs0, DomEqs, DiffEqs0, DiffEqs) :-
  (
    Idx #< N, Idx1 #= Idx + 1,
    domain_rootidx_name(unityroots(N), Idx, Root),
    DomEqs0 = [var_indomain(Root) | DomEqs1],
    unityroots_rooteqs(Idx1, N, DomEqs1, DomEqs, DiffEqs1, DiffEqs)
  ;
    Idx #= N
  ).

% def_roots_dom_gen_unityroots(Idx, N, Gen0, Gen, PNames0, PNames) -->
%   "poly ", gen_polyname(Gen0, Gen1, PName), " = ",
%   ( { Idx #< N, Idx1 #= Idx + 1 },
%   ).

% def_roots_dom_gen(unityroots(N), Gen0, Gen, PNames0, PNames) --> def_roots_dom_gen_unityroots(0, N, Gen0, Gen, PNames0, PNames).
%   TODO.

%%% Equation DSL Interpreter %%%

equation(var_indomain(Var), D) --> domain_varname_in(D, Var).
equation(var_diff(Var, Diff), D) --> domain_varname_diffname(D, Var, Diff).
equation(var_is(Var, Is), _) --> varname_isname(Var, Is).

%%% Singular Helpers %%%

endcmd --> ";\n".

domain_defvars(unityroots(N), NVars) -->
  { N1 #= N - 1, NVars1 #= NVars -  1 },
  "x(0..", number(NVars1), "),w(0..", number(N1), ")".

poly_name(prefixed(Prefix, PID)) --> atom(Prefix), number(PID).

polys_names([PID | PIDs]) --> polys_names_(PIDs, PID).

polys_names_([], P) --> poly_name(P).
polys_names_([PName | PNames], P) -->
  poly_name(P), ",", polys_names_(PNames, PName).

ideal_name(prefixed(Prefix, IID)) --> atom(Prefix), number(IID).
ideal_name(name(Name)) --> atom(Name).

%%% Singular Toplevel Commands %%%

header(NVars, Dom, Ord) -->
  "option(redSB)", endcmd,
  "ring r = 0,(",
  domain_defvars(Dom, NVars),
  "),", atom(Ord), endcmd.

gen_polyname(gen_prefix(Prefix, PID), gen_prefix(Prefix, PID1), prefixed(Prefix, PID)) -->
  { PID1 #= PID + 1 }, poly_name(prefixed(Prefix, PID)).

def_poly_eq_gen(Eq, Dom, PName, Gen0, Gen) -->
  "poly ", gen_polyname(Gen0, Gen, PName), " = ", equation(Eq, Dom), endcmd.

def_polys_eqs_dom_gen([], _, Gen, Gen, PNames, PNames) --> [].
def_polys_eqs_dom_gen([Eq | Eqs], Dom, Gen0, Gen, PNames0, PNames) -->
  { PNames0 = [PName | PNames1] },
  def_poly_eq_gen(Eq, Dom, PName, Gen0, Gen1),
  def_polys_eqs_dom_gen(Eqs, Dom, Gen1, Gen, PNames1, PNames).

def_ideal(IName, PNames) -->
  "ideal ", ideal_name(IName), " = std(ideal(", polys_names(PNames), "))", endcmd.

print_ideal(IName) --> ideal_name(IName), endcmd.

compile(Eqs, NVars, Dom) -->
  compile(Eqs, NVars, Dom, lp, gen_prefix(k, 0), gen_prefix(h, 0), name(i)).
compile(Eqs, NVars, Dom, Ord, Root_gen, Poly_gen, IName) -->
  header(NVars, Dom, Ord),
  { domain_rooteqs(Dom, REqs) },
  def_polys_eqs_dom_gen(REqs, Dom, Root_gen, _, PNames, PNames1),
  def_polys_eqs_dom_gen(Eqs, Dom, Poly_gen, _, PNames1, []),
  def_ideal(IName, PNames),
  print_ideal(IName).
