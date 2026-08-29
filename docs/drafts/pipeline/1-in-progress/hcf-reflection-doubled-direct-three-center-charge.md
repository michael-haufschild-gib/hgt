# HCF reflected-pair doubled direct three-center charge

- **ID:** HCF-REFLECT-2X-DIRECT-3C
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** `rh-current-frontier-map.md` · Route HCF
- **Statement:** Every finite strict-right Xi multiplicity packet whose nearest three integer feature centres lie in `K` forces corrected HCF lattice budget at least `card(S) * (126976/21125)`.

## Goal

Remove an unused factor two in HCF receiver. Existing corrected budget sums every Xi multiplicity
copy, but existing `63488/21125` theorem charges only strict-right representatives. Critical-line
reflection supplies a disjoint left partner with same height cell. This changes 75%-sufficient
canonical source ceiling from `7936/21125` to `15872/21125` without any analytic hypothesis.

This is receiver strengthening, not source closure. Remaining unconditional task is source-only
upper bound
`CriticalFeatureCanonicalAsymptoticUpper criticalFeaturePoleGammaPlemeljCovariance
  (15872/21125)`.

## Gates

- [x] 0 → 1  in-progress: well-posed; unconditional divisor-side receiver; corpus nonduplication search complete
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, targeted build green, axioms audited
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Let `sigma = xiZeroCopyLineConjEquiv`. Corpus proves
`xiSpectralPoint (sigma q) = conj (xiSpectralPoint q)`. Therefore:

1. `Re (I * xiSpectralPoint (sigma q)) = -Re (I * xiSpectralPoint q)`.
2. If every `q` in `S` is strict-right, `S` and `sigma(S)` are disjoint.
3. Conjugation preserves spectral height, hence nearest integer centre and its two neighbours.
4. Every member of `S union sigma(S)` is off line.
5. Existing pointwise `63488/21125` three-centre holomorphic-square lower bound applies to every
   member of this union.
6. Nonnegativity and summability embed this finite union once into all-copy corrected budget.
7. Union cardinality is `2 card(S)`, yielding `126976/21125` per strict-right representative.

With `N = N0 + 2 card(S)`, budget upper bound
`(15872/21125) N` gives `card(S) <= N/8`, hence `3N/4 <= N0`.

## Corpus audit

- Reused: copy-level critical-line equivalence; centered spectral conjugation; real-centred Cauchy
  feature conjugation; all-copy off-line tsum; pointwise direct three-centre charge.
- Whole-corpus research queries found no reflected finite-packet doubling theorem and no existing
  `126976/21125` or `15872/21125` HCF receiver.
- Earlier Euler-affine Ward and bilateral Möbius producers land in safe continued trace but supply
  no quantitative critical-boundary estimate; not used here.
- All-scale Hellinger diagonal remains von-Mangoldt divergent without height-local renormalization;
  not used here.

## Log

- 2026-08-29 — conjectured from mismatch between strict-right packet receiver and all-copy budget;
  survived copy-encoding and conjugation hostile checks; Lean formalization started.
