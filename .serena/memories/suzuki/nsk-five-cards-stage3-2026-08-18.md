# Suzuki `not_new_scientific_knowledge` five-card stage-3 promotion (2026-08-18)

All five cards moved `2-fully-proven/not_new_scientific_knowledge` →
`3-formalized/not_new_scientific_knowledge`.  Every new declaration has
`#print axioms = [propext, Classical.choice, Quot.sound]`; all modules wired into their umbrella.

## New modules

| Card | Module(s) |
|---|---|
| archimedean-primitive-forced-sign-change | `HTGeometry/EndpointIntegralAsymptotics.lean`, `RHTower/SuzukiRealKernelForm.lean`, `RHTower/SuzukiArchimedeanPrimitiveSignChange.lean` |
| bounded-seam-half-log-rigidity | `HTGeometry/BoundedSeamHalfLogRigidity.lean` |
| euler-pole-archimedean-moment-annihilation | `RHTower/SuzukiEulerPoleArchimedeanMomentAnnihilation.lean` |
| screw-characteristic-meromorphic-limit-correction | `RHTower/SuzukiCharacteristicMeromorphicLimit.lean` (+ existing `SuzukiCharacteristicEntireLimitNoGo`) |
| tail-is-exact-summatory-error-transform | `RHTower/SuzukiTailSummatoryErrorTransform.lean` (+ two ℂ lemmas appended to `HTGeometry/CountableWeightedDirac.lean`) |

## Reusable assets this left behind

- `HTGeometry.tendsto_rpow_mul_intervalIntegral_nhdsGT_zero` / `..._nhdsLT`: endpoint asymptotics of
  a primitive `x ↦ ∫_x^b f` when `f y / y^α → L` (`α < -1`, divergent) or `h y/(b-y)^β → L`
  (`β > -1`, convergent).  Pure ε-δ, only local interval integrability assumed.
- `HTGeometry.integrable_complex_countableWeightedDirac` / `integral_complex_countableWeightedDirac`
  (ℂ analogues of the ℝ Dirac lemmas; a *third* copy already exists as
  `GaloisForLFunctions.HTGeometry.integral_countableWeightedDirac_complex` in
  `HerglotzDiscreteSupportSeries` — different namespace, expensive to import).
- `RHTower.suzukiRealSourceG` / `suzukiRealSourceGOne` / `suzukiRealBetaTail`: real forms of the
  literal Suzuki kernel with `ofReal_*` bridges; kernel endpoint constants
  `A_ω=(2π)^ω/Γ(ω)`, `B_ω=4ωπ^{ω-1/2}Γ(3/2-ω)` proved from the Euler beta value.
- `RHTower.suzukiShiftedAtomicMeasure` (Stieltjes measure of the shifted-Euler summatory function,
  built on `HTGeometry.countableWeightedDirac`) with its exact interval mass.
- `RHTower.eventually_exists_zero_closedBall_of_tendstoLocallyUniformlyOn` /
  `mem_closed_of_tendstoLocallyUniformlyOn`: Hurwitz zero transfer on an arbitrary open set
  (the entire-case versions live in `RHTower/LocallyUniformZeroTransfer.lean`).
- `HTGeometry.BoundedSeamData`: bounded-coupling boundary Volterra system; Gronwall is replaced by a
  maximum-point bootstrap on `[L₁,L]` with tail mass ≤ 1/4 — no operator inverse, no Neumann series
  (the trick: `U' = -(1/2)L^{-3/2} T(L)F(L)` follows from the equation itself).

## Boundary that is NOT Lean-internal

Card `suzuki-screw-characteristic-meromorphic-limit-correction` proves its *pole* remark from
Hardy's theorem (infinitely many real zeros of `ξ(1/2+it)`), which is in neither mathlib nor this
tree.  Lean has the implication `two distinct positive real XiC zeros → pole`
(`exists_pole_suzukiXiCharacteristicTarget_of_two_positive_real_XiC_zeros`) and the card's
*conclusion* unconditionally by an independent route (`not_suzukiXiCharacteristicLimitWall`:
wall → RH → two real zeros → Rolle → pole → contradiction).  Attempts at a Hardy-free pole fail in
exactly one case: `Ξ > 0` on ℝ with `Ξ'` nonvanishing off the origin; the complex route needs
Hadamard factorization of the meromorphic `Ξ'/Ξ`.
