:- use_module(library(dcgs)).
:- use_module(library(pio)).

:- use_module(singular).

test(A) :- current_output(S), test(A, S).

test(A, S) :- phrase_to_stream(A, S).

test_unityroots :- current_output(S), test_unityroots(S).
test_unityroots(S) :-
  D = unityroots(w-[4], [x-[2]]),
  Eqs = [
    var_diff(var(x, [0]), var(x, [1])),
    var_is(var(x, [1]), var(w, [3]))
  ],
  test(compile(Eqs, D), S), !,
true.

test_boolean :- current_output(S), test_boolean(S).
test_boolean(S) :-
  D = boolean([x-[1], y-[2], z-[2, 2]]),
  Eqs = [
    var_diff(var(x, [0]), var(y, [1])),
    var_is(var(y, [1]), var(z, [1, 1])),
    boolexprs_count([
      false,
      true,
      var(z, [0, 0]),
      var(z, [0, 1]),
      var(z, [1, 0]),
      var(z, [1, 1]),
      not(var(x, [0])),
      and(var(y, [0]), var(y, [1])),
      or(var(x, [0]), var(y, [0])),
      xor(var(z, [0, 1]), var(y, [1]))
    ], 3)
  ],
  test(compile(Eqs, D), S), !,
true.
