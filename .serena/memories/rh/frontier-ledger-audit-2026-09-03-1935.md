# RH frontier ledger audit — 2026-09-03 19:35 CEST

- Target updated: `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md`.
- Evidence: Lean declarations only via mandatory `scripts/formal_tools.py research`; no cards, papers, literature, computations, or Lean builds.
- Snapshot: commit `2253d70ddadc1446662e47f988e7f88fc0224cba` plus audited unconditional working-tree declarations; incomplete declarations excluded.
- Route E moved: exact global-local-moment inequality, one global moving-support defect, and block-local moment substitution remain recorded. New `MenonHarmonicFinalRangeSchedule` fixes `H=(log x)^10`, literal lower endpoint `Q`, `eta=exp(1/H)-1`, and least ceiling depth `L`; eventual prime-range coverage and all natural cofactor endpoints are formal. `mem_geomBlock_primesRange_of_right_le` identifies nonterminal full prime blocks; Case-I product theorem is prime-family-parametric. Harmonic open core is now specialization to this ladder, choice of `k,V`, and Menon-normalized decay of explicit RHS.
- F2/J local geometry: Meixner–Pollaczek/complex rapidity/boost rows and diagonals recorded. New generic scaled terminating `₂F₁` limit gives `cos(2w)` at `c=1/2` and `sin(2w)/(2w)` at `c=3/2`; no source weld, so no label change.
- Route-neutral HTGeometry: intrinsic Cartan translation vector/norm/bounded-orbit equivalence, rank-one exact minimal polynomial/simple extension, prescribed Newton-edge Puiseux leads, and combined first-order Wiman top-symbol/log-derivative/positive finite slope subsequence recorded. No Xi source/landing, so no route/candidate.
- Counts unchanged: 26 live labels, 33 candidate labels.
- Validation: 1463 lines (<4000); `git diff --check` clean; no diary/update headings; stale Menon schedule language absent; 32 changed/new Lean files since prior cutoff scanned with no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration markers.
- Concurrent non-target edits were preserved. No build run.