# Independent periods are rational source-period independence

- **ID:** independent-periods-fraction-field-connector
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `formal/GaloisForLFunctions/HTGeometry/EllipticGammaConeDivisor.lean`; `formal/GaloisForLFunctions/HTGeometry/MeromorphicRankThreeSourceBoundary.lean`
- **Statement:** For every `a b : ℂ`, `IndepPeriods a b` iff `LinearIndependent ℚ (ellipticGammaSourcePeriods a b)`.

## Goal

Identify the cone-divisor integral-period hypothesis with the rational rank-three source interface.
This lets every concrete source-period independence witness discharge `IndepPeriods` without adding
an analytic or arithmetic premise.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `indepPeriods_iff_linearIndependent_ellipticGammaSourcePeriods`, module build green, axiom audit clean
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Classification

- **Tag:** `[BRIDGE] [PROVED HERE]`
- **Novelty verdict:** `REDISCOVERED` as mathematics; routine finite-family base change from `ℤ` to
  its fraction field `ℚ`. Corpus value is exact interface closure, not a novelty claim.
- **Dependency status:** closed. Required input is the standard fraction-field equivalence for
  linear independence, already present as `LinearIndependent.iff_fractionRing` in this toolchain.

## Paper proof

Fix `a,b ∈ ℂ` and set `v = [1,a,b] : Fin 3 → ℂ`.

First, `IndepPeriods a b` is equivalent to `LinearIndependent ℤ v`. By the finite-family criterion,
the latter says that for every coefficient vector `g : Fin 3 → ℤ`,

`∑ i, g i • v i = 0`

implies `g i = 0` for every `i`. Expanding the three-term sum and writing
`p = g 0`, `q = g 1`, `r = g 2`, its premise is exactly

`(p : ℂ) + q * a + r * b = 0`,

and its conclusion is exactly `p = 0 ∧ q = 0 ∧ r = 0`. The converse uses the same expansion and
the three conclusions to prove the coefficient function is zero.

Second, `ℚ` is the fraction field of `ℤ`, and the scalar actions on `ℂ` form the required scalar
tower. Fraction-field base change therefore gives

`LinearIndependent ℤ v ↔ LinearIndependent ℚ v`.

Composing the two equivalences proves the claim. No conjectural hypothesis, choice of special
periods, numerical evidence, or analytic premise enters the argument. `[PROVED HERE]`

## Hostile review

- **Circularity:** none; neither direction invokes a cone-divisor theorem consuming
  `IndepPeriods`.
- **Scope:** exact for arbitrary complex `a,b`, not merely an existence result.
- **Potential mismatch:** excluded by expanding `ellipticGammaSourcePeriods a b = ![1,a,b]` and
  using `ℤ`-scalar multiplication in `ℂ`.
- **Overclaim check:** theorem identifies two independence interfaces only. It does not prove that
  arbitrary periods are independent.
- **Immediate corollary:** the existing theorem
  `linearIndependent_ellipticGammaSourcePeriods_I_I_sqrtTwo` yields unconditional
  `IndepPeriods I (I * sqrt 2)`.

## Door passport

- **Door-1:** closes a corpus interface gap used by cone-divisor, triptic divisor, and correction
  modules.
- **Door-2:** no external novelty claimed; mathematical content is standard localization.
- **Door-3:** formalized; see the Lean certificate below.

## Log

- 2026-08-13 — source audit found `IndepPeriods` as highest apparent unproduced project Prop head.
- 2026-08-13 — prior-corpus search found rational source independence and fraction-field machinery,
  but no `IndepPeriods` connector.
- 2026-08-13 — complete paper proof and hostile review; advanced to `2-fully-proven`.

## Lean certificate

Module: `GaloisForLFunctions.HTGeometry.IndepPeriodsFractionFieldConnector`, wired into the
`GaloisForLFunctions.HTGeometry` umbrella.

| Card statement | Lean declaration |
|---|---|
| integral criterion as finite independence | `indepPeriods_iff_linearIndependent_int` |
| fraction-field base change | `indepPeriods_iff_linearIndependent_ellipticGammaSourcePeriods` |
| unconditional corollary at `i`, `i√2` | `indepPeriods_I_I_sqrtTwo` |

Every listed declaration reports exactly `propext`, `Classical.choice`, `Quot.sound`.
