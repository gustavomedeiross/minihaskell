Mini-Haskell
============

A project for the French MPRI course on functional programming

---

ML type inference in presence of type classes
-----------------------------------------------

Compile the executable `joujou`:

    make

`joujou` can check two variants of *MH*:

- Explicitly typed programs use the extension `.mle`.

        ./joujou file.mle

- Implicitly typed programs use the extension `.mlt`.

        ./joujou file.mlt

`joujou` infers types (on implicitly typed programs),
type-checks and elaborates *MH* programs into *OCaml* programs,
producing a file with the extension `.ml`.

Samples of *MH* can be found in `test/`.

---

Organization of test files:

- `test/elaboration/`, `test/inference/` contain tests provided with the base
    version of the project (forked from http://github.com/yurug/mpri13)

- `test/custom/` contain tests written by ourselves, some of them redundant
    with the original test suit, but most cover previously untested features.

---

A not-too-verbose-when-it-works test script is available, call it with

    make test

to run `joujou` on all test files in `test/`.

Makefiles with a more verbose behavior are available at the leaves of the
`test/` directory. (based on those originally provided)

---

Note(s) about our work
----------------------

Important modifications have been made to the `Name` module,
`name.mli` contains more explanations.

For the remaining of the project, a `diff` with the original code base
would show modifications *everywhere*, due to our using the tool `ocp-indent`
on the entirety of the repository.

However, relevant changes have remained mostly local to files indicated by the
assignment, others consisting mostly in trimming code unnecessary to our
application.

---

All tasks from the assignment have been carried out.

There are bugs and lacking features, a certain number of which
were already present (resp. absent) and are unrelated to the
topic of type classes themselves.

-   `test/inference/bad/coreml_intermediate_variable.mlt`,
    `test/inference/bad/coreml_value_restriction.mlt`,
    `test/inference/bad/typeclass_use_r.mlt`,
    `test/inference/bad/typeclass_use_rw.mlt`:
    Error during elaboration/type-checking, after type inference,
    it would be desirable to catch it earlier. (The error message
    has no position to report)
