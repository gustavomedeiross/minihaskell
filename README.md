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
