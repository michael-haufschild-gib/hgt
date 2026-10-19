import GaloisForLFunctions.HTGeometry.LogTrigPowerPrimitives
import GaloisForLFunctions.HTGeometry.RiemannSumCell

/-!
# Integer-window variance of resonant logarithmic oscillations

An exact weighted annular integral gives macroscopic variance.
The existing quadrature theorem transfers it to integers with error at most twice the frequency.
-/

open scoped BigOperators
open Set MeasureTheory

namespace GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
noncomputable section
set_option autoImplicit false

private def variancePrimitive (t a c x : ℝ) : ℝ :=
  (1 / 2 + c ^ 2) * Real.log x + Real.sin (2 * (t * Real.log x + a)) / (4 * t) -
    2 * c * Real.sin (t * Real.log x + a) / t

private theorem hasDerivAt_variancePrimitive (t a c x : ℝ) (ht : t ≠ 0) (hx : 0 < x) :
    HasDerivAt (variancePrimitive t a c)
      ((Real.cos (t * Real.log x + a) - c) ^ 2 / x) x := by
  have hphase := (GaloisForLFunctions.HTGeometry.hasDerivAt_mul_log (b := t) hx).add_const a
  have hs := hphase.sin
  have hs2 := (hphase.const_mul 2).sin
  have hl := (Real.hasDerivAt_log hx.ne').const_mul (1 / 2 + c ^ 2)
  have hh := (hl.add (hs2.div_const (4 * t))).sub ((hs.const_mul (2 * c)).div_const t)
  refine hh.congr_deriv ?_
  rw [Real.cos_two_mul]
  field_simp
  ring

private theorem continuousOn_variance (t a c : ℝ) :
    ContinuousOn (fun x : ℝ => (Real.cos (t * Real.log x + a) - c) ^ 2) (Ioi 0) := by
  have hl : ContinuousOn Real.log (Ioi (0 : ℝ)) :=
    Real.continuousOn_log.mono (fun x hx => ne_of_gt hx)
  have hc : ContinuousOn (fun x : ℝ => Real.cos (t * Real.log x + a)) (Ioi 0) :=
    Real.continuous_cos.comp_continuousOn ((hl.const_mul t).add_const a)
  exact (hc.sub continuousOn_const).pow 2

/-- An exact weighted variance integral, evaluated on the positive ray. -/
theorem weighted_log_variance_integral (t a c u v : ℝ) (ht : t ≠ 0)
    (hu : 0 < u) (hv : 0 < v) :
    (∫ x in u..v, (Real.cos (t * Real.log x + a) - c) ^ 2 / x) =
      variancePrimitive t a c v - variancePrimitive t a c u := by
  have hsubset := GaloisForLFunctions.HTGeometry.uIcc_subset_Ioi hu hv
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hasDerivAt_variancePrimitive t a c x ht (hsubset hx))
  exact (((continuousOn_variance t a c).div continuousOn_id
    (fun x hx => ne_of_gt hx)).mono hsubset).intervalIntegrable

/-- A resonant logarithmic annulus carries a full number of periods. -/
theorem weighted_annular_variance (q : ℕ) (t M c : ℝ) (ht : t ≠ 0) (hM : 0 < M)
    (hres : t * Real.log 2 = (q : ℝ) * (2 * Real.pi)) :
    (∫ x in M..(2 * M),
      (Real.cos (t * Real.log x + -(t * Real.log (2 * M))) - c) ^ 2 / x) =
      Real.log 2 * (1 / 2 + c ^ 2) := by
  have hhi : t * Real.log (2 * M) + -(t * Real.log (2 * M)) = 0 := by ring
  have hlo : t * Real.log M + -(t * Real.log (2 * M)) =
      0 - (q : ℝ) * (2 * Real.pi) := by
    rw [Real.log_mul (by norm_num) hM.ne']
    nlinarith [hres]
  have hdouble : 2 * (0 - (q : ℝ) * (2 * Real.pi)) =
      0 - ((2 * q : ℕ) : ℝ) * (2 * Real.pi) := by push_cast; ring
  rw [weighted_log_variance_integral t _ c M (2 * M) ht hM (by positivity)]
  unfold variancePrimitive
  rw [hhi, hlo, hdouble, Real.sin_sub_nat_mul_two_pi,
    Real.sin_sub_nat_mul_two_pi, Real.log_mul (by norm_num) hM.ne']
  simp only [mul_zero, Real.sin_zero, zero_div, sub_zero, add_zero]
  ring

/-- Every center has macroscopic continuous variance on the final dyadic annulus. -/
theorem annular_variance_lower_bound (q : ℕ) (t M c : ℝ) (ht : t ≠ 0) (hM : 0 < M)
    (hres : t * Real.log 2 = (q : ℝ) * (2 * Real.pi)) :
    M * Real.log 2 / 2 ≤ ∫ x in M..(2 * M),
      (Real.cos (t * Real.log x + -(t * Real.log (2 * M))) - c) ^ 2 := by
  let a := -(t * Real.log (2 * M))
  have hsubset := GaloisForLFunctions.HTGeometry.uIcc_subset_Ioi hM
    (show 0 < 2 * M by positivity)
  have hi : IntervalIntegrable (fun x : ℝ => (Real.cos (t * Real.log x + a) - c) ^ 2)
      volume M (2 * M) := ((continuousOn_variance t a c).mono hsubset).intervalIntegrable
  have hw : IntervalIntegrable (fun x : ℝ => (Real.cos (t * Real.log x + a) - c) ^ 2 / x)
      volume M (2 * M) :=
    (((continuousOn_variance t a c).div continuousOn_id
      (fun x hx => ne_of_gt hx)).mono hsubset).intervalIntegrable
  have hp : ∀ x ∈ Icc M (2 * M),
      M * ((Real.cos (t * Real.log x + a) - c) ^ 2 / x) ≤
        (Real.cos (t * Real.log x + a) - c) ^ 2 := by
    intro x hx
    have hx0 : 0 < x := hM.trans_le hx.1
    calc
      M * ((Real.cos (t * Real.log x + a) - c) ^ 2 / x) ≤
          x * ((Real.cos (t * Real.log x + a) - c) ^ 2 / x) :=
        mul_le_mul_of_nonneg_right hx.1 (div_nonneg (sq_nonneg _) hx0.le)
      _ = (Real.cos (t * Real.log x + a) - c) ^ 2 := by field_simp
  have hmono := intervalIntegral.integral_mono_on (show M ≤ 2 * M by linarith)
    (hw.const_mul M) hi hp
  rw [intervalIntegral.integral_const_mul, weighted_annular_variance q t M c ht hM hres] at hmono
  have hnonneg : 0 ≤ M * Real.log 2 * c ^ 2 := by
    exact mul_nonneg (mul_nonneg hM.le (Real.log_nonneg (by norm_num))) (sq_nonneg c)
  dsimp [a] at hmono
  nlinarith

private theorem abs_variance_sub_le (t a c M x y : ℝ) (ht : 0 ≤ t) (hc : |c| ≤ 1)
    (hM : 0 < M) (hMy : M ≤ y) (hyx : y ≤ x) :
    |(Real.cos (t * Real.log x + a) - c) ^ 2 -
      (Real.cos (t * Real.log y + a) - c) ^ 2| ≤ (4 * t / M) * (x - y) := by
  have hy0 := hM.trans_le hMy
  have hx0 := hy0.trans_le hyx
  have hd0 : 0 ≤ Real.log x - Real.log y :=
    sub_nonneg.mpr (Real.log_le_log hy0 hyx)
  have hd : Real.log x - Real.log y ≤ (x - y) / y := by
    have h := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
    rw [Real.log_div hx0.ne' hy0.ne'] at h
    convert h using 1
    field_simp
  have hcos : |Real.cos (t * Real.log x + a) - Real.cos (t * Real.log y + a)| ≤
      t * ((x - y) / M) := by
    calc
      |Real.cos (t * Real.log x + a) - Real.cos (t * Real.log y + a)| ≤
          |(t * Real.log x + a) - (t * Real.log y + a)| := Real.abs_cos_sub_cos_le _ _
      _ = t * (Real.log x - Real.log y) := by
        rw [show (t * Real.log x + a) - (t * Real.log y + a) =
          t * (Real.log x - Real.log y) by ring, abs_of_nonneg (mul_nonneg ht hd0)]
      _ ≤ t * ((x - y) / y) := mul_le_mul_of_nonneg_left hd ht
      _ ≤ t * ((x - y) / M) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (sub_nonneg.mpr hyx) hM hMy) ht
  have hfour : |Real.cos (t * Real.log x + a) + Real.cos (t * Real.log y + a) - 2 * c| ≤ 4 := by
    obtain ⟨hc1, hc2⟩ := abs_le.mp hc
    obtain ⟨hx1, hx2⟩ := abs_le.mp (Real.abs_cos_le_one (t * Real.log x + a))
    obtain ⟨hy1, hy2⟩ := abs_le.mp (Real.abs_cos_le_one (t * Real.log y + a))
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    |(Real.cos (t * Real.log x + a) - c) ^ 2 -
      (Real.cos (t * Real.log y + a) - c) ^ 2| =
        |Real.cos (t * Real.log x + a) - Real.cos (t * Real.log y + a)| *
          |Real.cos (t * Real.log x + a) + Real.cos (t * Real.log y + a) - 2 * c| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ (t * ((x - y) / M)) * 4 := mul_le_mul hcos hfour (abs_nonneg _)
      (mul_nonneg ht (div_nonneg (sub_nonneg.mpr hyx) hM.le))
    _ = (4 * t / M) * (x - y) := by ring

/-- Integer sampling loses at most twice the logarithmic frequency. -/
theorem annular_quadrature_bound (M : ℕ) (hM : 0 < M) (t a c : ℝ)
    (ht : 0 ≤ t) (hc : |c| ≤ 1) :
    |(∑ k ∈ Finset.range M, (Real.cos (t * Real.log ((M : ℝ) + k) + a) - c) ^ 2) -
      ∫ x in (M : ℝ)..(2 * M), (Real.cos (t * Real.log x + a) - c) ^ 2| ≤ 2 * t := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hsubset := GaloisForLFunctions.HTGeometry.uIcc_subset_Ioi hM0
    (show (0 : ℝ) < 2 * M by positivity)
  have hi : IntervalIntegrable
      (fun x : ℝ => (((Real.cos (t * Real.log x + a) - c) ^ 2 : ℝ) : ℂ))
      volume M (2 * M) :=
    ((Complex.continuous_ofReal.comp_continuousOn (continuousOn_variance t a c)).mono hsubset).intervalIntegrable
  have hq := _root_.HTGeometry.norm_sum_smul_sub_integral_le
    (f := fun x : ℝ => (((Real.cos (t * Real.log x + a) - c) ^ 2 : ℝ) : ℂ))
    (K := 4 * t / M) (a := M) (h := 1) (N := M) (by norm_num)
    (by simpa only [mul_one, ← two_mul] using hi) (by
      intro k hk x hx
      have hb := abs_variance_sub_le t a c M x ((M : ℝ) + k * 1) ht hc hM0
        (by have := Nat.cast_nonneg (α := ℝ) k; linarith) hx.1
      simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hb)
  simp only [one_smul, mul_one, one_pow, ← Complex.ofReal_sum,
    intervalIntegral.integral_ofReal, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, ← two_mul] at hq
  have hr : (M : ℝ) * (4 * t / M) / 2 = 2 * t := by field_simp; ring
  rwa [hr] at hq

private theorem exists_bounded_center (c : ℝ) :
    ∃ d : ℝ, |d| ≤ 1 ∧ ∀ v : ℝ, |v| ≤ 1 → (v - d) ^ 2 ≤ (v - c) ^ 2 := by
  by_cases hl : c ≤ -1
  · refine ⟨-1, by norm_num, ?_⟩
    intro v hv
    have hv1 := (abs_le.mp hv).1
    apply (sq_le_sq₀ (by linarith) (by linarith)).mpr
    linarith
  · by_cases hh : 1 ≤ c
    · refine ⟨1, by norm_num, ?_⟩
      intro v hv
      have hv1 := (abs_le.mp hv).2
      have h := (sq_le_sq₀ (show 0 ≤ 1 - v by linarith)
        (show 0 ≤ c - v by linarith)).mpr (show 1 - v ≤ c - v by linarith)
      nlinarith
    · exact ⟨c, abs_le.mpr ⟨by linarith, by linarith⟩, fun _ _ => le_rfl⟩

/-- Actual integer-window variance, with every center and all boundary terms retained. -/
theorem integer_window_variance_lower_bound (M : ℕ) (hM : 0 < M)
    (q : ℕ) (t c : ℝ) (ht : 0 < t)
    (hres : t * Real.log 2 = (q : ℝ) * (2 * Real.pi)) :
    (M : ℝ) * Real.log 2 / 2 - 2 * t ≤
      ∑ n ∈ Finset.Icc 1 (2 * M),
        (Real.cos (t * Real.log n + -(t * Real.log (2 * M : ℕ))) - c) ^ 2 := by
  obtain ⟨d, hd, hproj⟩ := exists_bounded_center c
  let a := -(t * Real.log (2 * (M : ℝ)))
  have hcont := annular_variance_lower_bound q t M d ht.ne'
    (by exact_mod_cast hM) hres
  have hquad := annular_quadrature_bound M hM t a d ht.le hd
  have hquadlo := (abs_le.mp hquad).1
  have hsum : (M : ℝ) * Real.log 2 / 2 - 2 * t ≤
      ∑ k ∈ Finset.range M, (Real.cos (t * Real.log ((M : ℝ) + k) + a) - d) ^ 2 := by
    dsimp [a] at hquadlo ⊢
    linarith
  have he : (∑ k ∈ Finset.range M, (Real.cos (t * Real.log ((M : ℝ) + k) + a) - d) ^ 2) =
      ∑ n ∈ Finset.Ico M (2 * M), (Real.cos (t * Real.log n + a) - d) ^ 2 := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [show 2 * M - M = M by omega, Nat.cast_add]
  have hsub : Finset.Ico M (2 * M) ⊆ Finset.Icc 1 (2 * M) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ico.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hfull : (M : ℝ) * Real.log 2 / 2 - 2 * t ≤
      ∑ n ∈ Finset.Icc 1 (2 * M), (Real.cos (t * Real.log n + a) - c) ^ 2 := by
    calc
      (M : ℝ) * Real.log 2 / 2 - 2 * t ≤
          ∑ k ∈ Finset.range M, (Real.cos (t * Real.log ((M : ℝ) + k) + a) - d) ^ 2 := hsum
      _ = _ := he
      _ ≤ ∑ n ∈ Finset.Icc 1 (2 * M), (Real.cos (t * Real.log n + a) - d) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => sq_nonneg _)
      _ ≤ ∑ n ∈ Finset.Icc 1 (2 * M), (Real.cos (t * Real.log n + a) - c) ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        exact hproj _ (Real.abs_cos_le_one _)
  simpa only [a, Nat.cast_mul, Nat.cast_ofNat] using hfull

end
end GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
