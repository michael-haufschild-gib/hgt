import GaloisForLFunctions.HTGeometry.VerticalShiftTailEstimate
import GaloisForLFunctions.HTGeometry.DigammaHorizontalVanishing
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# The second-order digamma asymptotic on a vertical line

Subtracting `log z - 1/(2z)` from the digamma function leaves a remainder whose unit-shift defect is
`1/z - log(1+1/z) - 1/(2z(z+1))`, an elementary function of `1/z` vanishing to third order.  The
telescoping estimate converts that into a remainder of order two:

`ψ(σ+it) = log(σ+it) - 1/(2(σ+it)) + O(t^{-2})`

uniformly in the abscissa.  This is the first step of the order-by-order expansion; the same pattern
with one more Taylor coefficient gives each subsequent order.
-/

open Filter Topology Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The logarithm of a unit shift splits off in the right half plane. -/
theorem log_add_one_eq (z : ℂ) (hre : 0 < z.re) (hz : 2 ≤ ‖z‖) :
    Complex.log (z + 1) = Complex.log z + Complex.log (1 + 1 / z) := by
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0] at hz
    simp at hz
    linarith
  have hw : ‖1 / z‖ ≤ 1 / 2 := by
    rw [norm_div, norm_one]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hwre : 0 < (1 + 1 / z).re := by
    have hle : |(1 / z).re| ≤ ‖1 / z‖ := Complex.abs_re_le_norm _
    have : (1 / z).re ≥ -(1 / 2) := by
      have := abs_le.mp (le_trans hle hw)
      linarith [this.1]
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hwne : (1 + 1 / z) ≠ 0 := by
    intro h0
    rw [h0] at hwre
    simp at hwre
  have hargz : |Complex.arg z| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have hargw : |Complex.arg (1 + 1 / z)| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hwre)
  have hsum : Complex.arg z + Complex.arg (1 + 1 / z) ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor
    · have h1 := (abs_lt.mp hargz).1
      have h2 := (abs_lt.mp hargw).1
      linarith
    · have h1 := (abs_lt.mp hargz).2
      have h2 := (abs_lt.mp hargw).2
      linarith
  have hmul : z * (1 + 1 / z) = z + 1 := by
    field_simp
  rw [← hmul, Complex.log_mul_eq_add_log_iff hz0 hwne |>.mpr hsum]

/-- The unit-shift defect of the second-order digamma remainder. -/
theorem digamma_second_defect {z : ℂ} (hre : 0 < z.re) (hz : 2 ≤ ‖z‖) :
    (Complex.digamma (z + 1) - Complex.log (z + 1) + 1 / (2 * (z + 1)))
        - (Complex.digamma z - Complex.log z + 1 / (2 * z))
      = 1 / z - Complex.log (1 + 1 / z) - 1 / (2 * z * (z + 1)) := by
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0] at hre
    simp at hre
  have hz1 : z + 1 ≠ 0 := by
    intro h0
    have : (z + 1).re = 0 := by rw [h0]; simp
    simp only [Complex.add_re, Complex.one_re] at this
    linarith
  have hpole : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m hm
    have : z.re = -(m : ℝ) := by rw [hm]; simp
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith [hre, ‹z.re = -(m : ℝ)›]
  rw [Complex.digamma_apply_add_one z hpole, log_add_one_eq z hre hz]
  field_simp
  ring

/-- The defect vanishes to third order. -/
theorem norm_digamma_second_defect_le {z : ℂ} (hre : 0 < z.re) (hz : 2 ≤ ‖z‖) :
    ‖1 / z - Complex.log (1 + 1 / z) - 1 / (2 * z * (z + 1))‖ ≤ (5 / 3) / ‖z‖ ^ 3 := by
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0] at hre
    simp at hre
  have hnormpos : (0 : ℝ) < ‖z‖ := by linarith
  set w : ℂ := 1 / z with hw
  have hwnorm : ‖w‖ = 1 / ‖z‖ := by rw [hw, norm_div, norm_one]
  have hwle : ‖w‖ ≤ 1 / 2 := by
    rw [hwnorm, div_le_div_iff₀ hnormpos (by norm_num)]
    linarith
  have hwlt : ‖w‖ < 1 := by linarith
  have honeaddw : (1 : ℝ) - ‖w‖ ≥ 1 / 2 := by linarith
  have hden : ‖1 + w‖ ≥ 1 / 2 := by
    have h := norm_sub_norm_le (1 : ℂ) (-w)
    rw [norm_neg, sub_neg_eq_add, norm_one] at h
    linarith
  -- the exact decomposition
  have hdecomp : 1 / z - Complex.log (1 + 1 / z) - 1 / (2 * z * (z + 1))
      = -(Complex.log (1 + w) - Complex.logTaylor 3 w) + w ^ 3 / (2 * (1 + w)) := by
    have hz1 : z + 1 ≠ 0 := by
      intro h0
      have : (z + 1).re = 0 := by rw [h0]; simp
      simp only [Complex.add_re, Complex.one_re] at this
      linarith
    have htay : Complex.logTaylor 3 w = w - w ^ 2 / 2 := by
      rw [Complex.logTaylor]
      simp [Finset.sum_range_succ]
      ring
    have honew : (1 : ℂ) + w = (z + 1) / z := by
      rw [hw]
      field_simp
    rw [htay, honew]
    rw [hw]
    field_simp
    ring
  rw [hdecomp]
  have hlog : ‖Complex.log (1 + w) - Complex.logTaylor 3 w‖
      ≤ ‖w‖ ^ 3 * (1 - ‖w‖)⁻¹ / 3 := by
    have := Complex.norm_log_sub_logTaylor_le 2 hwlt
    norm_num at this ⊢
    exact this
  have hcube : ‖w ^ 3 / (2 * (1 + w))‖ ≤ ‖w‖ ^ 3 := by
    rw [norm_div, norm_mul, norm_pow]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg w, pow_nonneg (norm_nonneg w) 3]
  have hlog' : ‖Complex.log (1 + w) - Complex.logTaylor 3 w‖ ≤ (2 / 3) * ‖w‖ ^ 3 := by
    refine le_trans hlog ?_
    have hinv : (1 - ‖w‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    have hnn : (0 : ℝ) ≤ ‖w‖ ^ 3 := by positivity
    nlinarith
  calc ‖-(Complex.log (1 + w) - Complex.logTaylor 3 w) + w ^ 3 / (2 * (1 + w))‖
      ≤ ‖(-(Complex.log (1 + w) - Complex.logTaylor 3 w))‖ + ‖w ^ 3 / (2 * (1 + w))‖ :=
        norm_add_le _ _
    _ ≤ (2 / 3) * ‖w‖ ^ 3 + ‖w‖ ^ 3 := by
        rw [norm_neg]
        exact add_le_add hlog' hcube
    _ = (5 / 3) * ‖w‖ ^ 3 := by ring
    _ = (5 / 3) / ‖z‖ ^ 3 := by
        rw [hwnorm]
        field_simp


/-- **The second-order digamma asymptotic on a vertical line.**  Uniformly in the abscissa,
`ψ(σ+it) = log(σ+it) − 1/(2(σ+it)) + O(t^{-2})`. -/
theorem norm_digamma_sub_log_add_half_inv_le {σ t : ℝ} (hσ : 0 < σ) (ht : 2 ≤ t) :
    ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)
        - Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)
        + 1 / (2 * ((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ (20 / 3) / t ^ 2 := by
  have htpos : (0 : ℝ) < t := by linarith
  set R : ℂ → ℂ := fun z => Complex.digamma z - Complex.log z + 1 / (2 * z) with hR
  set E : ℂ → ℂ := fun z => 1 / z - Complex.log (1 + 1 / z) - 1 / (2 * z * (z + 1)) with hE
  have hzre : ∀ n : ℕ, (0 : ℝ) < ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)).re := by
    intro n
    have : ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)).re = σ + n := by simp
    rw [this]
    positivity
  have hznorm : ∀ n : ℕ, (2 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ := by
    intro n
    exact le_trans ht (norm_vertical_add_nat_ge_im (σ := σ) t n)
  have hbound := norm_le_of_shift_defect (R := R) (E := E) (C := 5 / 3) hσ (by norm_num)
    (p := 3) (by norm_num) ht ?_ ?_ ?_
  · have hz0 : (σ : ℂ) + (t : ℂ) * Complex.I + (0 : ℂ) = (σ : ℂ) + (t : ℂ) * Complex.I := by ring
    have hb : ‖R ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 4 * (5 / 3 : ℝ) / t ^ (3 - 1) := hbound
    rw [show (4 : ℝ) * (5 / 3) = 20 / 3 by norm_num] at hb
    simpa [hR] using hb
  · intro n
    have hshift : (σ : ℂ) + (t : ℂ) * Complex.I + ((n : ℂ) + 1)
        = ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) + 1 := by ring
    rw [hshift, hR, hE]
    exact digamma_second_defect (hzre n) (hznorm n)
  · intro n
    rw [hE]
    exact norm_digamma_second_defect_le (hzre n) (hznorm n)
  · have hdig : Tendsto (fun n : ℕ => Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))
        - Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))) atTop (nhds 0) := by
      refine tendsto_digamma_sub_log_horizontal ?_
      have : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
      rw [this]
      exact hσ
    have hinv : Tendsto (fun n : ℕ =>
        1 / (2 * ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)))) atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
        (g := fun n : ℕ => 1 / (2 * (σ + n))) ?_
      · have hpos : (0 : ℝ) < σ + n := by positivity
        have hge : σ + n ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ := by
          have := norm_vertical_add_nat_ge_re (σ := σ) t n
          simpa using this
        have hznpos : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ :=
          lt_of_lt_of_le hpos hge
        rw [norm_div, norm_one, norm_mul]
        have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
        rw [h2]
        have h2z : (0 : ℝ) < 2 * ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ := by linarith
        have h2s : (0 : ℝ) < 2 * (σ + n) := by linarith
        rw [div_le_div_iff₀ h2z h2s]
        nlinarith
      · have hdiv : Tendsto (fun n : ℕ => 2 * (σ + (n : ℝ))) atTop atTop := by
          refine Filter.tendsto_atTop_mono (fun n => ?_)
            (tendsto_atTop_add_const_left atTop (2 * σ) (by
              simpa using (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop
                (by norm_num : (0:ℝ) < 2)))
          have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          nlinarith
        exact Tendsto.congr (fun n => by simp [one_div]) hdiv.inv_tendsto_atTop
    have := hdig.add hinv
    rw [add_zero] at this
    refine this.congr fun n => ?_
    rw [hR]

end

end GaloisForLFunctions.HTGeometry
