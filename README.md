Mad Hatter
===========

This project is a first step towards converting a relational concrete
interpreter into an abstract interpreter using a meta-interpeter in miniKanren.
Or, I heard you liked interpreters so I put some interpreters in your
interpreters dawg.

This is written in Racket using the cKanren library for the relational
programming language miniKanren.

This is still very much a work in progress, currently lacking in test cases :(,
but there are very simple interpreters in Racket and miniKanren for an
environment passing (CE); environment and store passing (CES); and environment,
store, and continuation passing (CESK) style machines.

