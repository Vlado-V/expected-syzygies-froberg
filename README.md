# Expected syzygies and Fröberg’s conjecture through degree 2d

Lean formalization of Theorem 1.1 of
[Expected Syzygies and Fröberg’s Conjecture through Degree 2d](Expected_syzygies_and_Froberg_through_degree_2d.pdf).
Assuming the Expected Syzygy Conjecture over a characteristic-zero field,
Fröberg’s predicted positively truncated Hilbert function holds through degree
`2d` for general degree-`d` forms, for every positive number of variables and
degree and every number of generators.

The independent Mathlib-only statement is in [Challenge.lean](Challenge.lean).
[Solution.lean](Solution.lean) proves `ESCtoFrobergPaper.main_result`, using the
development in [ESCtoFroberg/Main.lean](ESCtoFroberg/Main.lean).

The project pins its Lean toolchain, Mathlib revision, and dependency manifest.

```sh
./scripts/build-and-audit.sh
./scripts/verify-comparator.sh --native
```

For Linux verification with the bubblewrap sandbox, run
`./scripts/verify-comparator.sh` without `--native`.

Author and maintainer: Vlado Vojdanovski. Licensed under [Apache-2.0](LICENSE).
