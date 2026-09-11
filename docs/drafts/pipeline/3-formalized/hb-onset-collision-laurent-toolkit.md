# HB open-core burden reduction: onset pulse transform, affine collision control, Laurent interchange

- **ID:** HB-ONSET-COLLISION-LAURENT-TOOLKIT
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/notes.md (2026-09-11 corpus sweep of the HB open steps 31–40)
- **Statement:** Three unconditional Lean toolkits that lower the HB open-core burden: (i) the cleared onset factor is the Laplace transform of the onset derivative pulse, generically nonzero in the onset duration and positive at real exponents; (ii) two of the three affine Xi collision factors of the strict-right angular source are controlled by the zero-free half-plane and a half-descent; (iii) residue extraction commutes with the first-endpoint Mellin horizon finite part under the corpus's uniform Lipschitz bound.

## Goal
Reduce the open radiative core of route HB (frontier-map steps 31, 33, 34) without touching the
RH-bearing producer. None of the results below evaluates a physical current, proves extinction, or
selects the critical line. The chain is unchanged: literal theta-cusp source → Xi occurrence →
retained spin-two source → physical causal radial/left-QNM action → common Hawking-clock
extinction → RH. RH remains unproved.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure
- [x] 1 → 2  fully-proven: paper proofs are one integration by parts, the zero-free half-plane
  `Re s ≥ 1`, isolation of zeros of the entire function `xi`, and the corpus theorem
  `firstEndpointMellinRemainder_differentiableAt`
- [x] 2 → 3  formalized: five modules, `lake env lean` clean (no errors, no warnings), oleans
  published, umbrella imports added; axioms: see Log
- [ ] 3 → 4  not applicable (no stage 4 by user directive)

## Approach

### (i) Onset factor — `ThetaCuspHawkingBMOnsetPulseTransform`, `ThetaCuspHawkingBMClearedOnsetPulseTransform`
`clearedOnset s w = 1 + (w - 2s) · onsetCorrection (2s) w` with
`onsetCorrection v w = ∫₀¹ (χ(u) − 1) e^{(v−w)u} du`, `χ = Real.smoothTransition`. Integrating by
parts (`u := χ − 1`, `v := e^{(v−w)u}`) with `χ(0) = 0`, `χ(1) = 1`:

```
clearedOnset s w = onsetPulseTransform (2s − w),   onsetPulseTransform z := ∫₀¹ χ'(u) e^{zu} du.
```
Lean: `onsetPulseTransform_sub`, `clearedOnset_eq_onsetPulseTransform`.

Consequences: `onsetPulseTransform 0 = 1`; entire in `z` (`differentiable_onsetPulseTransform`,
from `onsetCorrection_entire`); along every ray `L ↦ L z₀` zeros are isolated
(`onsetPulseTransform_ray_eventually_ne_zero`, identity theorem on `ℂ` against the value `1` at
`L = 0`); every real duration has arbitrarily close real durations with nonzero transform
(`exists_real_near_onsetPulseTransform_ne_zero`); at real exponents the transform is a strictly
positive real (`onsetPulseTransform_ofReal_re_pos`, from `χ' ≥ 0` and `∫χ' = 1`).

Physical reading. `clearedOnsetDuration s w L := onsetPulseTransform (L (2s − w))` is the cleared
onset of the stretched transition `u ↦ χ(u/L)`; `clearedOnsetDuration s w 1 = clearedOnset s w`.
Hence the fifth factor in `continuedPhysicalSelfResponse_nonremovable_iff_elementary` can be made
nonzero by a generic choice of onset duration. At the physical point
`Im (2s − w) = ±(7/2) Im ρ` or `±(9/2) Im ρ`, so the real-exponent positivity does not apply to the
fixed unit duration; only the genericity statement does. Re-deriving the fixed-duration pipeline
with a stretched transition is not done here.

### (ii) Affine collisions — `XiAffineCollisionControl`, `ThetaCuspHawkingBMAngularSourceCollisionControl`
For a strict-right zero `ρ` the angular source vanishes iff `xi(5ρ/2−1) = 0 ∨ xi(ρ/2) = 0 ∨ xi(3ρ/2) = 0`
(`physicalSelfSourceCoefficient_zero_iff_xi`). Using `xi_ne_zero_of_one_le_re`:
- `xi(3ρ/2) ≠ 0` for `Re ρ ≥ 2/3`; for `Re ρ < 2/3` a collision partner `3ρ/2` is strict-right with
  `3/4 < Re < 1` and its own `3/2`-partner is zero-free (`xi_three_half_collision_partner`).
- `xi(5ρ/2−1) ≠ 0` for `Re ρ ≥ 4/5`.
- Half-descent: `xiHalfDescent ρ n = 2/3 + (−1/2)^n (ρ − 2/3)`, `xi(1 − ρ/2) = xi(ρ/2)`. If every
  half-value along the orbit vanished, every orbit point would be a zero accumulating at the real
  point `2/3`, contradicting isolation of zeros of the entire nonzero function `xi`
  (`xi_analyticOnNhd_univ`, `xi_zero = 1/2`). Hence `exists_xi_zero_half_ne_zero`: from every
  strict-right nonreal zero one reaches a strict-right nonreal zero `ρ'` with `xi(ρ'/2) ≠ 0`.
- Copy level: `physicalSelfSourceCoefficient_zero_iff_half_of_four_fifths_le`,
  `physicalSelfSourceCoefficient_ne_zero_of_four_fifths_le`,
  `exists_strict_right_zero_half_ne_zero_of_copy` (for copies with `Re ≠ 1/2`).

Not controlled: `xi(5ρ/2 − 1)` for `1/2 < Re ρ < 4/5`. At `Re ρ = 3/5` the partner lies on the
critical line, so no descent applies; the reflected map `σ ↦ 2 − 5σ/2` has a repelling 2-cycle at
`σ = 4/7`, so a collision chain need not terminate. This is a genuine residual sub-problem.

### (iii) Laurent interchange — `FirstEndpointMellinLaurentInterchange`
With the uniform horizon Lipschitz hypotheses of the existing
`firstEndpointMellinRemainder_differentiableAt`, the full finite part
`firstEndpointMellin F b w = F w 0 · b^{w+1}/(w+1) + remainder` is holomorphic
(`firstEndpointMellin_differentiableAt`, needs `w + 1 ≠ 0`) and analytic on a ball avoiding `−1`
(`firstEndpointMellin_analyticAt`). Scalars pass through (`firstEndpointMellin_const_mul`), so the
finite part of `F u t/(u − w)` is `firstEndpointMellin F b u/(u − w)` and
```
laurentCoeff (fun u => firstEndpointMellin (fun v t => F v t/(v − w)) b u) w (−1) = firstEndpointMellin F b w
```
(`laurentCoeff_firstEndpointMellin_div_sub`, via `laurentCoeff_analytic_div_sub`). This is the
abstract "residue of the finite part equals the finite part of the residue". Supplying the actual
projected temporal current's uniform Lipschitz constant (available in
`ThetaCuspHawkingBMIncomingHorizonExpansion`) and the angular/cusp half remain open.

### Recorded, not new
- The stationary `+−` arm of the causal cut already drops under cyclic Peierls skewness:
  `ThetaCuspHawkingHBPeierlsStationaryChannelElimination`.
- Ordering: steps 33/34 (moment/onset nonvanishing, collision control) are consequences of step 39
  (identification of the physical residue with the reduced cokernel `−Σ|D|²` through a nowhere-zero
  transducer). Attack 39 first.

## Log
- 2026-09-11 — created directly in 3-formalized; five modules compiled with `lake env lean`
  (0 errors, 0 warnings), oleans published, umbrella imports inserted in place.
- 2026-09-11 — `#print axioms` on the sixteen main theorems: only `propext`, `Classical.choice`,
  `Quot.sound`. `lake build <module>` audit: `XiAffineCollisionControl` (8746 jobs replayed, 33 s),
  `ThetaCuspHawkingBMOnsetPulseTransform` (87 s), `ThetaCuspHawkingBMClearedOnsetPulseTransform`
  (62 s), `FirstEndpointMellinLaurentInterchange` (11 s) all green;
  `ThetaCuspHawkingBMAngularSourceCollisionControl` green (13004 jobs; lake rebuilt stale
  dependency oleans of the `PhysicalAngularSourceXi` cone on the way). All five modules pass the
  `lake build` gate.
