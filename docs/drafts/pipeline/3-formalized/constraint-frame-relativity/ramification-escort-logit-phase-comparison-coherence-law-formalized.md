# Ramification escort--logit--phase comparison coherence — formalized

- **ID:** `cfr-ramification-escort-logit-phase-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `ramification-escort-logit-phase-comparison-coherence-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.EscortLogit` | new |
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.SchurCapacity` | shared |

All wired into `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintFrameRelativity`.

Theorem 2.1 — escort semigroup, linearisation, coherence, card `(EL.1)`–`(EL.9)`:

1. `probToOdds`, `oddsToProb`, `oddsToProb_probToOdds`, `probToOdds_oddsToProb` — the odds chart.
2. `escortMap`, `escortMap_eq_oddsToProb`, `escortMap_mem` — the escort map `(EL.2)` and that it
   preserves the open cube.
3. `probToOdds_escortMap` — the boxed odds law `(EL.9)`.
4. `escortMap_one`, `escortMap_comp` — the boxed semigroup law `(EL.6)`.
5. `logitClock`, `logitInv`, `logitInv_logitClock`, `logitClock_logitInv`, `logitInv_mem` — the
   signed log-odds clock `(EL.4)` and its inverse `(EL.5)`, an explicit bijection of `(0,1)`
   with `ℝ`.
6. `logitClock_escortMap` — the boxed conjugation `(EL.7)`, i.e. the commuting square `(EL.8)`.

Corollary 3.1 — source power naturality, card `(EL.10)`–`(EL.12)`:

7. `shellOcc`, `shellOcc_odds`, `shellOcc_mem` — the literal shell Gibbs section.
8. `escortMap_shellOcc` — the boxed first identity of `(EL.11)`.
9. `logitClock_shellOcc` — the boxed second identity of `(EL.11)`; dividing by the depth gives the
   normalised-clock invariance `(EL.12)`.

Theorem 4.1 — Gibbs-to-phase time dilation, card `(EL.13)`–`(EL.15a)`:

10. `phaseObs` — the diagonal phase observer.
11. `phaseObs_dilation`, `phaseObs_logitClock_escortMap` — the boxed square `(EL.14)`, hence
    `(EL.15)` on the literal section.

Section 5 — information loss after scalarisation, card `(EL.15b)`/`(EL.15c)`:

12. `bernoulliVarVec_one_sub`, `schurCapacity_one_sub` — the scalar capacity is invariant under
    `q ↦ 1 - q`.
13. `logitClock_one_sub` — the clock of the reflected state is the negated clock.

Theorem 5.1 — scalar-capacity non-descent, card `(EL.17)`–`(EL.24)`:

14. `bernVar`, `bernVar_escortMap_two` — the boxed variance action `(EL.20)`: `w ↦ w²/(1-2w)²`.
15. `probOfVar`, `probOfVar_mem`, `bernVar_probOfVar` — every variance in `(0,1/4]` is realised by
    a Bernoulli parameter in `(0,1)`, which is the realisability clause after `(EL.21)`.
16. `twoCapacity`, `schurCapacity_two` — the two-site capacity `(EL.18)` in variance coordinates.
17. `no_scalar_descent` — the theorem: for every two-clock aperture there is a pair of variance
    states with equal capacity `(EL.22)` whose second escorts have different capacities, so no
    scalar `ψ₂` as in `(EL.19)` exists.  The strict comparison `(EL.24)` appears as the hypothesis
    `4k²(a+b) < 4a + bk²` derived from `k(2a+b) = 2a`, and the witness `c` is produced by
    continuity at `c = 0` of the two normalised capacity profiles.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintFrameRelativity/EscortLogit.lean  # clean
#print axioms  ⇒  propext, Classical.choice, Quot.sound
```
