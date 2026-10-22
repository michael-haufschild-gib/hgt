# S6F five-point even positivity from scalar angle concavity

- **ID:** S6F-5E-ANGLE
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `../1-in-progress/theta-rank-three-direct-parabolic-determinant.md` · finite-order-five survivor
- **Statement:** Normalization, global concavity, strict increase, and the physical range of a correlation angle do not force positive semidefiniteness of its five-point reflection-even cosine block.

## Goal

Test the proposed proof arrow

```text
theta reflected correlation-angle concavity
→ five-point reflection-even Toeplitz PSD
→ confluent native rank-three D1 nonnegativity
→ finite TCD/S6F gate
→ cofinal all-order landing
→ Weil positivity
→ RH.
```

The card addresses only the first arrow. The active route-closing core remains
`TCD-D1-BOUNDARY-FLUX`; theta-specific source dynamics may still prove the required finite-section
positivity or orient D1 directly.

## Gates

- [x] 0 → 1 in-progress: exact finite matrix, exact source premises, and RH proof-chain placement
- [x] 1 → 2 fully-proven: symbolic determinant identity and explicit counterexample
- [x] 2 → 3 formalized: closed Lean capstone and positive-survivor classifier
- [ ] 3 → 4 publication-ready: priority review and integration into a standalone S6F no-go note

## Approach

Compress the palindromic five-node Toeplitz matrix to its reflection-even three-dimensional block.
On the saturated first angular face

```text
c₂ = 2c₁² - 1,
```

its determinant is exactly

```text
-4(c₁ + c₃ - 2c₁c₂)².
```

Use an explicit globally concave, strictly increasing angle with values

```text
α(0)=0, α(1)=π/6, α(2)=π/3, α(3)=5π/12, α(4)=11π/24.
```

The first three values saturate the face. Positive semidefiniteness would therefore force the
third-channel coupling identity, but that identity reduces to `cos(5π/12)=0`, contradicting
strict positivity.

## No-go closure

- **Exact killing theorem/mechanism:** `exists_strictMono_concave_angle_with_nonPSD_toeplitzFiveEvenBlock` supplies a closed counterexample satisfying every scalar angle premise. The obstruction is not a loose bound: on a saturated head the determinant is a negative square.
- **Strongest positive survivor:** `toeplitzFiveEvenBlock_boundary_coupling_eq_zero_of_posSemidef` classifies every positive semidefinite saturated-head extension by the exact rigidity law `c₁ + c₃ = 2c₁c₂`. Any viable finite-section proof must derive this three-channel null coupling, or a strict-interior replacement, from theta dynamics.
- **New insight:** Scalar one-variable correlation geometry cannot control the first genuinely rank-three reflected channel. The missing D1 information is a coupling law across lags `1,2,3`, not stronger concavity of the same angle. This removes angle-only strengthening from the S6F queue and redirects work to source-specific singular-face/null-line transport.
- **Status:** `[PROVED HERE][LEAN-PROVED][ROUTE KILLED]`. Formal module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspReflectedFivePointEvenAngleConcavityNoGo`. Literature search through 2026-08-31 found general Toeplitz/PSD completion and singular-face theory, but no result asserting or refuting this specific correlation-angle implication. Planat--Solé (arXiv:2608.19160) proves second-level theta-kernel concavity and explicitly stops at necessary Laguerre--Turán consequences, not five-point reflected rank-three positivity. Priority for the source-specific counterexample remains provisional because the negative-square mechanism is an instance of standard PSD facial rigidity.

## Log

- 2026-08-31 — Corpus search identified five-point reflection-even positivity as the finite survivor feeding native D1 and identified scalar angle concavity as a possible producer.
- 2026-08-31 — Exact determinant reduction found the saturated-face negative square and the null-coupling survivor.
- 2026-08-31 — Explicit angle counterexample and survivor classifier formalized without computations, added axioms, or unresolved premises; angle-only proof arrow retired.
