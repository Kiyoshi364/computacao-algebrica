:- use_module(library(dcgs)).
:- use_module(library(pio)).

:- use_module(singular).

test(A) :- current_output(S), phrase_to_stream(A, S).
