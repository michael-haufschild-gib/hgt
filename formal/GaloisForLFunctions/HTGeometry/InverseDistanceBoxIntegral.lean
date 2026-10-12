import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The inverse distance to a point is integrable over a box

For `ρ ∈ ℂ` the function `w ↦ 1/|w − ρ|` is locally integrable in the plane.  We record the
elementary box bound used for logarithmic derivatives with poles.

* `lintegral_Ioc_rpow_neg_half`: `∫₀^M u^{−1/2} du = 2√M`.
* `lintegral_Icc_abs_sub_rpow_neg_half_le`: `∫_{c−M}^{c+M} |x − c|^{−1/2} dx ≤ 4√M`.
* `inv_norm_sub_le_rpow`: `1/|σ + ix − ρ| ≤ 2^{−1/2} |σ − Re ρ|^{−1/2} |x − Im ρ|^{−1/2}` off the two
  lines through `ρ`, since `a² + b² ≥ 2|a||b|`.
* `lintegral_box_inv_norm_sub_le`: for `0 ≤ Re ρ ≤ 1` and `M ≥ 0`,
  `∫_{1/2}^{1} ∫_{Im ρ − M}^{Im ρ + M} |σ + ix − ρ|^{−1} dx dσ ≤ 2^{−1/2} · 4 · 4√M`.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem lintegral_Ioc_rpow_neg_half {M : ℝ} (hM : 0 ≤ M) :
    ∫⁻ u in Ioc 0 M, ENNReal.ofReal (u ^ (-(1 / 2 : ℝ))) = ENNReal.ofReal (2 * Real.sqrt M) := by
  have hint : IntegrableOn (fun u : ℝ => u ^ (-(1 / 2 : ℝ))) (Ioc 0 M) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hM).mp
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun u hu => Real.rpow_nonneg hu.1.le _))]
  · congr 1
    rw [← intervalIntegral.integral_of_le hM, integral_rpow (Or.inl (by norm_num))]
    rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, Real.zero_rpow (by norm_num), Real.sqrt_eq_rpow]
    ring

theorem integral_zero_rpow_neg_half (M : ℝ) :
    ∫ u in (0 : ℝ)..M, u ^ (-(1 / 2 : ℝ)) = 2 * Real.sqrt M := by
  rw [integral_rpow (Or.inl (by norm_num)), show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num,
    Real.zero_rpow (by norm_num), Real.sqrt_eq_rpow]
  ring

theorem lintegral_Ioc_abs_sub_rpow_neg_half (c : ℝ) {M : ℝ} (hM : 0 ≤ M) :
    ∫⁻ x in Ioc c (c + M), ENNReal.ofReal (|x - c| ^ (-(1 / 2 : ℝ))) =
      ENNReal.ofReal (2 * Real.sqrt M) := by
  have hcongr : EqOn (fun x : ℝ => ENNReal.ofReal (|x - c| ^ (-(1 / 2 : ℝ))))
      (fun x => ENNReal.ofReal ((x - c) ^ (-(1 / 2 : ℝ)))) (Ioc c (c + M)) := by
    intro x hx
    simp only
    rw [abs_of_pos (sub_pos.mpr hx.1)]
  rw [setLIntegral_congr_fun measurableSet_Ioc hcongr]
  have hII : IntervalIntegrable (fun x : ℝ => (x - c) ^ (-(1 / 2 : ℝ))) volume c (c + M) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := M)
      (show (-1 : ℝ) < -(1 / 2) by norm_num)).comp_sub_right c
    simpa [add_comm] using this
  have hint : IntegrableOn (fun x : ℝ => (x - c) ^ (-(1 / 2 : ℝ))) (Ioc c (c + M)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp hII
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun x hx => Real.rpow_nonneg (sub_pos.mpr hx.1).le _))]
  congr 1
  rw [← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_comp_sub_right (fun u => u ^ (-(1 / 2 : ℝ))) c,
    show c - c = 0 by ring, show c + M - c = M by ring, integral_zero_rpow_neg_half M]

theorem lintegral_Icc_left_abs_sub_rpow_neg_half (c : ℝ) {M : ℝ} (hM : 0 ≤ M) :
    ∫⁻ x in Icc (c - M) c, ENNReal.ofReal (|x - c| ^ (-(1 / 2 : ℝ))) ≤
      ENNReal.ofReal (2 * Real.sqrt M) := by
  have hcongr : EqOn (fun x : ℝ => ENNReal.ofReal (|x - c| ^ (-(1 / 2 : ℝ))))
      (fun x => ENNReal.ofReal ((c - x) ^ (-(1 / 2 : ℝ)))) (Icc (c - M) c) := by
    intro x hx
    simp only
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hx.2)]
  rw [setLIntegral_congr_fun measurableSet_Icc hcongr]
  have hII : IntervalIntegrable (fun x : ℝ => (c - x) ^ (-(1 / 2 : ℝ))) volume (c - M) c := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := M)
      (show (-1 : ℝ) < -(1 / 2) by norm_num)).comp_sub_left c
    simpa using this.symm
  have hint : IntegrableOn (fun x : ℝ => (c - x) ^ (-(1 / 2 : ℝ))) (Icc (c - M) c) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp hII
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Icc).mpr
      (Filter.Eventually.of_forall fun x hx => Real.rpow_nonneg (sub_nonneg.mpr hx.2) _))]
  apply le_of_eq
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_comp_sub_left (fun u => u ^ (-(1 / 2 : ℝ))) c,
    show c - c = 0 by ring, show c - (c - M) = M by ring, integral_zero_rpow_neg_half M]

theorem lintegral_Icc_abs_sub_rpow_neg_half_le (c : ℝ) {M : ℝ} (hM : 0 ≤ M) :
    ∫⁻ x in Icc (c - M) (c + M), ENNReal.ofReal (|x - c| ^ (-(1 / 2 : ℝ))) ≤
      ENNReal.ofReal (4 * Real.sqrt M) := by
  have hsplit : Icc (c - M) (c + M) ⊆ Icc (c - M) c ∪ Ioc c (c + M) := by
    intro x hx
    by_cases h : x ≤ c
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨lt_of_not_ge h, hx.2⟩
  calc _ ≤ ∫⁻ x in Icc (c - M) c ∪ Ioc c (c + M), ENNReal.ofReal (|x - c| ^ (-(1 / 2 : ℝ))) :=
        lintegral_mono_set hsplit
    _ ≤ _ := lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal (2 * Real.sqrt M) + ENNReal.ofReal (2 * Real.sqrt M) := by
        rw [lintegral_Ioc_abs_sub_rpow_neg_half c hM]
        gcongr
        exact lintegral_Icc_left_abs_sub_rpow_neg_half c hM
    _ = ENNReal.ofReal (4 * Real.sqrt M) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

/-- `1/|σ + ix − ρ| ≤ |σ − Re ρ|^{−1/2} |x − Im ρ|^{−1/2}` off the two lines through `ρ`. -/
theorem inv_norm_sub_le_rpow (ρ : ℂ) {σ x : ℝ} (hσ : σ ≠ ρ.re) (hx : x ≠ ρ.im) :
    1 / ‖(σ : ℂ) + x * Complex.I - ρ‖ ≤
      |σ - ρ.re| ^ (-(1 / 2 : ℝ)) * |x - ρ.im| ^ (-(1 / 2 : ℝ)) := by
  set a := σ - ρ.re
  set b := x - ρ.im
  have ha : 0 < |a| := abs_pos.mpr (sub_ne_zero.mpr hσ)
  have hb : 0 < |b| := abs_pos.mpr (sub_ne_zero.mpr hx)
  have hnorm : ‖(σ : ℂ) + x * Complex.I - ρ‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
    rw [show (σ : ℂ) + x * Complex.I - ρ = ((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * Complex.I by
      apply Complex.ext <;> simp [a, b]]
    rw [Complex.norm_def, Complex.normSq_add_mul_I]
  have hab : |a| * |b| ≤ a ^ 2 + b ^ 2 := by
    nlinarith [sq_abs a, sq_abs b, sq_nonneg (|a| - |b|), abs_nonneg a, abs_nonneg b]
  have hprod : |a| ^ (-(1 / 2 : ℝ)) * |b| ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt (|a| * |b|) := by
    rw [← Real.mul_rpow ha.le hb.le, Real.sqrt_eq_rpow, Real.rpow_neg (mul_nonneg ha.le hb.le)]
    exact (one_div _).symm
  rw [hnorm, hprod]
  apply one_div_le_one_div_of_le (Real.sqrt_pos.mpr (mul_pos ha hb))
  exact Real.sqrt_le_sqrt hab

/-- **Box bound.**  For `0 ≤ Re ρ ≤ 1` and `M ≥ 0`,
`∫_{1/2}^{1} ∫_{Im ρ − M}^{Im ρ + M} |σ + ix − ρ|^{−1} dx dσ ≤ 16 √M`. -/
theorem lintegral_box_inv_norm_sub_le (ρ : ℂ) (h0 : 0 ≤ ρ.re) (h1 : ρ.re ≤ 1) {M : ℝ}
    (hM : 0 ≤ M) :
    ∫⁻ σ in Icc (1 / 2 : ℝ) 1, ∫⁻ x in Icc (ρ.im - M) (ρ.im + M),
        ENNReal.ofReal (1 / ‖(σ : ℂ) + x * Complex.I - ρ‖) ≤
      ENNReal.ofReal (16 * Real.sqrt M) := by
  have hne : ∀ c : ℝ, ∀ᵐ y ∂(volume : Measure ℝ), y ≠ c := fun c => by
    rw [ae_iff]; simp
  have hmeas : ∀ c : ℝ, Measurable fun y : ℝ => ENNReal.ofReal (|y - c| ^ (-(1 / 2 : ℝ))) :=
    fun c => by fun_prop
  calc ∫⁻ σ in Icc (1 / 2 : ℝ) 1, ∫⁻ x in Icc (ρ.im - M) (ρ.im + M),
        ENNReal.ofReal (1 / ‖(σ : ℂ) + x * Complex.I - ρ‖)
      ≤ ∫⁻ σ in Icc (1 / 2 : ℝ) 1, ∫⁻ x in Icc (ρ.im - M) (ρ.im + M),
          ENNReal.ofReal (|σ - ρ.re| ^ (-(1 / 2 : ℝ))) *
            ENNReal.ofReal (|x - ρ.im| ^ (-(1 / 2 : ℝ))) := by
        refine lintegral_mono_ae (ae_restrict_of_ae ?_)
        filter_upwards [hne ρ.re] with σ hσ
        refine lintegral_mono_ae (ae_restrict_of_ae ?_)
        filter_upwards [hne ρ.im] with x hx
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (inv_norm_sub_le_rpow ρ hσ hx)
    _ = (∫⁻ σ in Icc (1 / 2 : ℝ) 1, ENNReal.ofReal (|σ - ρ.re| ^ (-(1 / 2 : ℝ)))) *
          ∫⁻ x in Icc (ρ.im - M) (ρ.im + M), ENNReal.ofReal (|x - ρ.im| ^ (-(1 / 2 : ℝ))) := by
        simp_rw [lintegral_const_mul _ (hmeas ρ.im)]
        rw [lintegral_mul_const _ (hmeas ρ.re)]
    _ ≤ ENNReal.ofReal (4 * Real.sqrt 1) * ENNReal.ofReal (4 * Real.sqrt M) := by
        gcongr
        · calc _ ≤ ∫⁻ σ in Icc (ρ.re - 1) (ρ.re + 1),
                ENNReal.ofReal (|σ - ρ.re| ^ (-(1 / 2 : ℝ))) :=
                lintegral_mono_set (Icc_subset_Icc (by linarith) (by linarith))
            _ ≤ _ := lintegral_Icc_abs_sub_rpow_neg_half_le ρ.re zero_le_one
        · exact lintegral_Icc_abs_sub_rpow_neg_half_le ρ.im hM
    _ = ENNReal.ofReal (16 * Real.sqrt M) := by
        rw [Real.sqrt_one, ← ENNReal.ofReal_mul (by norm_num)]; ring_nf

end

end GaloisForLFunctions.HTGeometry
