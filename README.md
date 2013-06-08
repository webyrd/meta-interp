meta-interp
===========

Playing with meta-interpreters in miniKanren.  Inspired by Nada Amin's miniKanren confo talk at Clojure/West:

https://github.com/namin/minikanren-confo


The files:

* `meta.scm`  The meta-interpreters, translated directly from Nada's `core.logic` code.


* `boolean.scm`  Interpreter (and tests) for a trivial language of Boolean expressions, taken from Pierce's 'Types and Programming Languages'.

* `quines.scm`  Interpreter (and tests) for a relational interpreter capable of generating Scheme quines.  Code taken from https://github.com/webyrd/2012-scheme-workshop-quines-paper-code


* `mk.scm`  Version of miniKanren from https://github.com/webyrd/2012-scheme-workshop-quines-paper-code


* `testcheck.scm`  Simple test macro.

* `test-all.scm`  Load this to run all the tests.



Tested under Petite Chez Scheme 8.4.  To run the tests, just load `test-all.scm`:

> (load "test-all.scm")