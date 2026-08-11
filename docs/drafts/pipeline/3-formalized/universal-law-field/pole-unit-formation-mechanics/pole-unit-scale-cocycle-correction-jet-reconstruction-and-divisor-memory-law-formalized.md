# Pole-unit scale cocycle, correction-jet reconstruction, and divisor memory — formalized

- **ID:** ULF-PUFM-2-LEAN
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper parent:** `pole-unit-scale-cocycle-correction-jet-reconstruction-and-divisor-memory-law.md`
  (moved into this folder)
- **Lean modules:**
  - `GaloisForLFunctions.HTGeometry.PoleUnitFormationMechanics`
  - `GaloisForLFunctions.HTGeometry.PoleUnitFormationAnalytic`
  - `GaloisForLFunctions.HTGeometry.PoleUnitGammaBase`
  - `GaloisForLFunctions.HTGeometry.PoleUnitEulerShell`
- **Status:** `[LEAN-CERTIFIED]` `[UMBRELLA WIRED]` `[NO AXIOMS ADDED]` `[UNCONDITIONAL]`
  `[EXACT COCYCLE]` `[ONE-RAY RECONSTRUCTION]` `[GAMMA BASE + HANKEL]` `[DIVISOR MEMORY]`
  `[FINITE-DEPTH NO-GO]` `[EULER-SHELL SPECIALIZATION]` `[NOT RH]`

## Certified surface

| Paper item | Lean declaration |
|---|---|
| `(PUF.3)` polar splitting | `polar_corrected_split` |
| `(PUF.4)` exact scale cocycle | `correctedScaleResponse_cocycle`, `polarScaleResponse_cocycle` |
| scalar-gauge invariance | `correctedScaleResponse_smul`, `polarScaleResponse_smul` |
| `(PUF.5)` distinguished logarithm | `exists_unitLog` |
| `(PUF.7)` exact ghost law | `correctedScaleResponse_eq_exp_sub`, `finiteCorrectionExponent_cocycle`, `finiteLogUnit_response` |
| `(PUF.8)` one-ray coefficient inversion | `iteratedDeriv_correctionRay`, `iteratedDeriv_of_correctionRay`, `correctionJetPolynomial_reconstruct` |
| §3 germ reconstruction from one ray | `eventuallyEq_of_oneRay` |
| `(PUF.11)` universal Gamma base | `tendsto_correctedScaleResponse_one`, `tendsto_polarScaleResponse_gammaBase` |
| `(PUF.12)` ascending-factorial moments | `iteratedDeriv_gammaBaseTransform`, `gammaShapeLaw_moment` |
| `(PUF.13)` Gamma Hankel positive definiteness | `gammaShapeMoment_positiveMomentForm`, `gammaShapeMoment_momentHankelMatrix_posDef` |
| `(PUF.14)` complete correction/cumulant law | `logDeriv_polarScaleResponse`, `deriv_logDeriv_polarScaleResponse` |
| Theorem 5.1 complete divisor memory | `eqOn_of_eventuallyEq`, `divisorMemory_of_oneRay` |
| Theorem 5.2 finite-depth divisor blindness | `finiteCorrectionDepth_divisorBlind`, `lateDivisorFactor_eval_self` |
| `(PUF.18)` shell relative response | `shellSource_relative_response` |
| `(PUF.20)` first shell correction coefficient | `logDeriv_shellUnit_zero`, `tendsto_logDeriv_shellUnit` |
| `(PUF.21)` shell clock mean and variance | `shellClock_mean`, `shellClock_variance` |

The mean and variance are certified in their exact cumulant form,
`mean(ε) = r − ε·logDeriv U ε` and `var(ε) = r + ε²·(logDeriv U)′ ε`, together with continuity of
`logDeriv U` at the pole; the paper's `O(ε²)` and `O(ε³)` expansions are the first-order readings
of those identities with `r = 1` and `logDeriv U 0 = γ + H_m′(1)/H_m(1)`.

## Exact boundary

Certified: the algebraic formation cocycle, the analytic distinguished logarithm and its exact
ghost law, one-ray coefficient inversion and germ rigidity, propagation of germ equality through a
connected continuation domain and the resulting divisor equality, the universal Gamma base limit
with its complete moment and Hankel structure, the exact cumulant slope and curvature laws, and the
Euler-shell specialization with its first constitutive coefficient.

Not claimed: any order law selecting zero-free continued units, hence no RH statement.  The card's
own §7 records that gap as the open selector problem.

## Verification

- direct elaboration: `lake env lean GaloisForLFunctions/HTGeometry/PoleUnitFormationAnalytic.lean`,
  `.../PoleUnitGammaBase.lean`, `.../PoleUnitEulerShell.lean`;
- umbrella build: `lake build GaloisForLFunctions.HTGeometry.UniversalLawField` — 11,632 jobs, success;
- axiom audit through a temporary `#print axioms` file: every listed declaration depends only on
  `propext`, `Classical.choice`, `Quot.sound`;
- `scripts/formal_tools.py lint --check-generated` reports no reachability or proof-debt error for
  these modules; indexes regenerated.

## Log

- 2026-08-11 — algebraic core certified.
- 2026-08-11 — analytic logarithm, one-ray reconstruction and germ rigidity, divisor memory,
  Gamma base moments and Hankel positive definiteness, exact cumulant laws, and Euler-shell
  specialization certified; paper card promoted to stage 3.
