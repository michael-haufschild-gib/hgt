# HB cusp finite-part specialization-kernel no-go

- **ID:** HB-C-A.9w-survivor
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/hb-complete-augmented-third-order-source-coefficient.md · C-A.9w
- **Statement:** Analytic-family cusp finite part does not descend through pointwise spectral
  specialization; descent is equivalent to kernel inclusion, which an explicit actual-chamber
  collision violates.

## Goal

Replace an invalid pointwise regularization abstraction by the exact invariant determining when a
family-level functional can descend through specialization.

## Gates

- [x] 0 → 1 in-progress: corpus collision and RH-chain impact recorded
- [x] 1 → 2 fully-proven: exact descent criterion and closed witness proved
- [x] 2 → 3 formalized: module wired; direct Lean, targeted build, axioms, lint audited
- [ ] 3 → 4 publication-ready: standalone exposition not prepared

## Mathematical certificate

For linear maps `f : V → W`, `g : V → ℂ`, Lean proves

`(∃ h : W → ℂ, ∀x, h(f x)=g x) ↔ ker(f) ≤ ker(g)`.

Reporter `h` is an arbitrary function.  Sufficiency chooses any preimage on the range; kernel
inclusion proves independence of that choice.  Necessity compares each kernel vector with zero.

Apply this to affine cusp-family specialization at actual parameters `s=2,t=4` and to analytic
finite part `F ↦ F(0)`.  Difference between unit masses at labels `0` and `(1,2,-1)` specializes
to the zero height profile but has finite part one.  Hence kernel inclusion and factorization both
fail.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinCuspFinitePartSpecializationNoGo`
- Collision exponent: `d4BM_accidentalZeroExponent_specializes_to_zero`
- Identical profiles: `d4BM_zero_and_accidentalZero_families_same_specialized_profile`
- Exact descent criterion: `d4BM_linearReporter_factorsThrough_iff_ker_le`
- Kernel obstruction: `d4BM_cuspSpecialization_ker_not_le_finitePart_ker`
- Closed route kill: `d4BM_cuspAnalyticFamilyFinitePart_not_factorThrough_specializedHeight`
- Verification: direct `lake env lean` pass; targeted `lake build` pass `12477/12477`; headline
  axiom audit only `propext`, `Classical.choice`, `Quot.sound`.  Formal lint sees module through
  `RHTower` and reports no forbidden declaration; unrelated shared unreachable modules remain.

## Consequence

C-A.9v's residual algebra remains valid for abstract height-linear reporters, but no such reporter
is the corpus analytic-family regularization uniformly after specialization.  Surviving HB chain
must begin with a meromorphic family-level pole-filled scalar RSZ theorem:

`family RSZ -> C-A.9u -> balanced source -> negative BM -> left-QNM -> HC94 cocycle -> RH`.

## Log

- 2026-08-29 — exact obstruction paper-proved, Lean-proved, wired, and audited
