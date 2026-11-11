import GaloisForLFunctions.MultiscaleMollifiedZetaField.OnlyComparablyDeepZerosCompete

/-!
# The strip pays the very-deep camera noise

At low camera centre `2c log T`, a depth cutoff `A ≥ 3c log T / 2`
puts every putative very-deep competitor outside the critical strip.
Combining this with the Lorentzian-mass theorem removes the remaining
noise premise in the hyperbolic camera. Only the geometric Blaschke
product among comparably deep zeros remains.
-/

noncomputable section

open Complex Set MeasureTheory Filter
open scoped Real
open RHTower Zeta23

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The very-deep exterior family is empty when its depth threshold reaches
the edge of the critical strip. -/
theorem veryDeep_family_eq_empty {c L A : ℝ} (hc : 0 < c) (hL : 0 < L)
    (hA : 3 * c * L / 2 ≤ A) (V : Finset zetaZeroConfig.carrier)
    (hV : ∀ ρ ∈ V, A / (3 * c * L) < (ρ : ℂ).re - 1 / 2) : V = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro ρ hρ
  have hcut : 1 / 2 ≤ A / (3 * c * L) := by
    rw [le_div_iff₀ (by positivity)]
    linarith only [hA]
  have hstrip := (abs_le.mp (abs_re_sub_half_le ρ)).2
  exact (not_lt_of_ge (hstrip.trans hcut)) (hV ρ hρ)

/-- The low-centre mass condition is automatic above the strip threshold. -/
theorem veryDeep_camera_mass_eq_zero {c L A : ℝ} (hc : 0 < c) (hL : 0 < L)
    (hA : 3 * c * L / 2 ≤ A) (v : ℝ → ℝ) (t : ℝ)
    (V : Finset zetaZeroConfig.carrier)
    (hV : ∀ ρ ∈ V, A / (3 * c * L) < (ρ : ℂ).re - 1 / 2) :
    profileMass v * ∑ ρ ∈ V, (zetaZeroConfig.mult ρ : ℝ) *
      companionWeight (c * L) (2 * (c * L)) t ρ = 0 := by
  rw [veryDeep_family_eq_empty hc hL hA V hV, Finset.sum_empty, mul_zero]

/-- Above depth `3c/(1-3c)`, the hyperbolic-camera density estimate needs
no outside-mass or low-centre-mass hypothesis. Its remaining condition is
the Blaschke product over zeros at least `(1-3c)/2` as deep as the target. -/
theorem exists_card_hyperbolic_zeros_le_without_noise
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    (hv0 : ∀ u, 0 ≤ v u) (hI : 0 < ∫ u, v u) {c : ℝ}
    (hc : 0 < c) (hc1 : c < 1 / 9) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ α B₀ : ℝ, 0 ≤ α →
      3 * c * Real.log T ≤ (1 - 3 * c) * α →
      Real.exp (-((1 - 3 * c) * α / 8)) ≤ B₀ → B₀ ≤ 1 →
      ∀ S : Finset zetaZeroConfig.carrier,
      (∀ ρ ∈ S,
        α / Real.log T ≤ (ρ : ℂ).re - 1 / 2 ∧
        (ρ : ℂ).re - 1 / 2 ≤ (α + 1) / Real.log T ∧
        T + 1 ≤ (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ 2 * T - 1 ∧
        ∀ D : Finset zetaZeroConfig.carrier, ρ ∈ D →
          (∀ ρ' ∈ D, ((1 - 3 * c) * α / 2) / Real.log T ≤ (ρ' : ℂ).re - 1 / 2) →
          B₀ ≤ ∏ ρ' ∈ D.erase ρ, hyperbolicRatio (ρ : ℂ) (ρ' : ℂ)) →
      (∀ ρ ∈ S, ∀ ρ' ∈ S, ρ ≠ ρ' →
        1 / (5 * (c * Real.log T)) ≤ |(ρ : ℂ).im - (ρ' : ℂ).im|) →
      (S.card : ℝ) ≤
        C * (α + 1) * T * Real.log T * Real.exp (-(2 * (1 - 3 * c) * α)) / B₀ ^ 2 +
        C * (Real.log T * ((Real.log T + 1) * T ^ ((1 : ℝ) / 2))) := by
  obtain ⟨C, hC, hmain⟩ := exists_card_hyperbolically_isolated_zeros_le
    hv hsupp hv0 hI hc (by linarith only [hc1])
  refine ⟨C, hC, ?_⟩
  filter_upwards [hmain, Real.tendsto_log_atTop.eventually_ge_atTop (2 / (3 * c))]
    with T hT hL α B₀ hα hdepth hB₀ hB₀1 S hS hsep
  have hL0 : 0 < Real.log T := (by positivity : 0 < 2 / (3 * c)).trans_le hL
  have hscale : 2 ≤ 3 * c * Real.log T := by
    have h := mul_le_mul_of_nonneg_left hL (show 0 ≤ 3 * c by positivity)
    have he : (3 * c) * (2 / (3 * c)) = 2 := by field_simp
    linarith only [h, he]
  have hA : 1 ≤ (1 - 3 * c) * α / 2 := by linarith only [hscale, hdepth]
  have hBpos : 0 < B₀ := (Real.exp_pos _).trans_le hB₀
  have h := hT α ((1 - 3 * c) * α / 2) B₀ hα hA le_rfl hB₀ hB₀1
    0 le_rfl ∅ (by simp) S (fun ρ hρ => ?_) hsep
  · simpa only [zero_mul, add_zero] using h
  · obtain ⟨hd1, hd2, ht1, ht2, hprod⟩ := hS ρ hρ
    refine ⟨hd1, hd2, ht1, ht2, hprod, ?_⟩
    intro t _ _ V hV
    rw [veryDeep_camera_mass_eq_zero hc hL0
      (by linarith only [hdepth]) v t V hV]
    have hαp : 0 < α + 1 := by linarith only [hα]
    positivity

end GaloisForLFunctions.MultiscaleMollifiedZetaField
