# Strict-right HB self-source nonvanishing

- **ID:** HB-SS-NV
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** rh-current-frontier-map.md · HB literal QNM-value/extinction edge
- **Statement:** For every strict-right `q : XiZeroCopy`, `physicalSelfSourceCoefficient q ≠ 0`.

## Goal

Discharge the exact affine-no-collision premise forced by HB-CQ-LS-SS0 for any pointwise
`canonicalQNMValue = 0 ↔ unit-left-source = 0` bridge. This does not prove that bridge; it removes
its newly isolated source-zero obstruction.

## Gates

- [x] 0 → 1  in-progress: corpus-derived statement, full-chain consequence, concrete failure split.
- [ ] 1 → 2  fully-proven.
- [ ] 2 → 3  formalized.
- [ ] 3 → 4  publication-ready.

## Conjecture / proof loop

`physicalSelfSourceCoefficient_zero_iff_xi` reduces a counterexample to one of
`xi(5q/2-1)=0`, `xi(q/2)=0`, `xi(3q/2)=0`.

1. **Half factor — resolved reduction.** `xiHalfDescent` preserves zeroes under repeated
half-collision and converges to real `2/3`; isolation proves a descendant with `xi(q/2)≠0`.
2. **Three-half factor — resolved reduction.** Above `Re q≥2/3` it is zero-free; below it, one
three-half collision moves to a strict-right zero whose own three-half factor is zero-free.
3. **Five-half factor — open survivor.** Outside `[8/15,2/3]`, collision descent finds a zero with
five-half and three-half factors nonzero. Failure to escape is exactly a zero orbit trapped in that
band, with imaginary parts scaled by `(5/2)^n`. Its real trapped set is null and has no interval,
but those theorems do not exclude an atomic Xi-zero orbit. No corpus theorem yet combines this
reduction with half descent, so alternating collision patterns also remain open.

## Full proof chain

`HB-SS-NV` → no self-source-zero mismatch from HB-CQ-LS-SS0 → pointwise literal-QNM/left-source
zero-equivalence remains viable → canonical left-source extinction classification → RH. A trapped
atomic five-half orbit would instead kill that exact pointwise bridge via HB-CQ-LS-SS0.

## Falsifier

One strict-right `q` with any displayed affine Xi collision. An explicit current survivor is the
fully classified singular trapped five-half orbit; alternating collision patterns are also not
excluded. No actual collision witness is known in the corpus.
