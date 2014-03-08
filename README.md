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
