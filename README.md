finite-automaton-simulator
==========================

This program simulates three kind of Finite Automata: deterministic, nondeterministic and nondeterministic with epsilon transitions.

Written in Caml Light as a practice to Automata Theory and Formal Languages class in 2004.


How it works:
=============

Create a graph with tuples of values: start state, finish state and transition string. 
 - A, B, 0
 - A, C, 1
 - B, B, 0
 - B, C, 1
 - C, A, 1
 - C, D, 0
 - D, D, 0
 - D, D, 1

Initial state: A

Final state: D
 
Then the user has to write (char to char) an input sequence to test the automaton.
 Example:
 - 1 
 - 0
 - 0 
 - 1
 - 0
 - 1
 - 0
 
 In this case, the input is accepted. (Otherwise doesn't show any message)