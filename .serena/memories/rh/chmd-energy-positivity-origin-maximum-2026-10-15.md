# CHMD loop step 4: Klein–Gordon energy positivity and the origin maximum (2026-10-15, MUST-1532)

Module `formal/GaloisForLFunctions/RHTower/CHMDKleinGordonEnergyPositivityAndOriginMaximum.lean`
(namespace `RHTower.CHMDEnergyPositivity`; imports the forced-measure module; wired after it; standard axioms).

Producer-side (unconditional positivity, no RH equivalence, no bound):
- `re_sq_add_two_mul_conj_cosh_half_sq_pos`, `re_energyDensity_pos`: `Re((z²+2)·sech²(z/2)) > 0` for `|Im z| < ½`
  via `Re((z²+2)conj(cosh²(z/2))) = (a²−b²+2)(cos²(b/2)+sinh²(a/2)cos b) + a sinh a · b sin b`.
- `kgEnergyTerm_pos`: `m_ρ Re(ρ_ρ² w_ρ) > 0` at every nontrivial zero.
- `goodDensity_sq_add_two_sq_mul_specSq_sechHalf`, `summable_quartic`, `kgQuarticMass` (`Σ m‖w‖‖ρ‖⁴`).
- `mode_lower_bound` (`Complex.cos_bound` for `|yρ| ≤ 1`; `‖cos‖ ≤ 2` beyond, with `|Im(yρ)| ≤ ¼`),
  `chmdWave_zero_sub_ge`: `φ_Λ(0) − φ_Λ(y) ≥ (y²/2)E_y − 3y⁴Q` for `|y| ≤ ½`.
- `exists_origin_maximum`: `∃ y₀ > 0, ∀ |y| ≤ y₀, φ_Λ(y) ≤ φ_Λ(0)`; `exists_twoPointDiff_nonneg_near_origin`.
- `kgEnergyMoment_eq_evenWeilDensity` (energy moment = `evenWeilDensity Λ (specSq (rhoC·sechHalf))`, `evenStrip_energyTest`),
  `prime_energy_le_pole_add_arch` (energy-weighted explicit-formula inequality, pole value `7/(2cos²¼)`).

Why it matters: first unconditional positivity of RH-sensitive 2×2 packets on an open set of shifts; strip-sector positivity
of a multiplier `m(z)sech²(z/2)` propagates to the jet of the causal wave at the origin. The radius is explicit in one zero's
energy and frequency and the quartic mass; the obstruction beyond it is the first resonance `y ≈ 2π/Re ρ_{ρ₁}`.

Not overlapping: the other agent's Stages 18–22 bound packet summands per zero (sector cone, sinh defect), which fail at resonant
shifts of high zeros; the uniform radius needs the summed argument with exponentially small weights.

Lean traps: `GaloisForLFunctions.HTGeometry.kgFreq/kgWeight` clash with `CHMDGrowthCollapse.*` (qualify in `unfold`);
`le_or_lt → le_or_gt`; `Real.sin_nonpos_of_…` renamed (use `Real.sin_neg`); `pow_le_pow_left₀`; `Complex.im_ofReal_mul`;
`Real.pow_div_factorial_le_exp` for polynomial ≤ exponential; nonempty subtype via `haveI` + `Classical.arbitrary`.
