import GaloisForLFunctions.RHTower.ChiCubicMovingProfileJets

/-!
# Full-band moving-profile cancellation with both boundaries retained

Two signed integrations give a summable inverse-square frequency term.
The actual window pays the remaining endpoint contribution by |ξ-1|.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Set Filter
open scoped Topology ContDiff
open GaloisForLFunctions.RHTower

private theorem fourier_twice_boundary (f f' f'' : ℝ → ℂ) {B τ : ℝ}
    (hτ : τ ≠ 0)
    (hf : ∀ x ∈ Icc (1 : ℝ) 2, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc (1 : ℝ) 2, HasDerivAt f' (f'' x) x)
    (hc : ContinuousOn f' (Icc (1 : ℝ) 2))
    (hc' : ContinuousOn f'' (Icc (1 : ℝ) 2))
    (hB : ∀ x ∈ Icc (1 : ℝ) 2, ‖f' x‖ ≤ B ∧ ‖f'' x‖ ≤ B) :
    ‖∫ x in (1 : ℝ)..2, f x * bourgainOscillation (τ * x)‖ ≤
      (‖f 1‖ + ‖f 2‖) / |τ| + 3 * B / τ ^ 2 := by
  let a : ℂ := (τ : ℂ) * Complex.I
  let e : ℝ → ℂ := fun x => bourgainOscillation (τ * x)
  have he (x : ℝ) : HasDerivAt e (a * e x) x := by
    have h := (((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (τ : ℂ)).mul_const Complex.I).cexp
    simpa only [e, a, bourgainOscillation, Complex.ofReal_mul, Complex.ofRealCLM_apply,
      Complex.ofReal_one, mul_one, mul_assoc, mul_comm, mul_left_comm] using h
  have hec : Continuous e := continuous_iff_continuousAt.mpr (fun x => (he x).continuousAt)
  have hei : IntervalIntegrable (fun x => a * e x) volume 1 2 :=
    (continuous_const.mul hec).intervalIntegrable _ _
  have hfi : IntervalIntegrable f' volume 1 2 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mpr hc.integrableOn_Icc
  have hid := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x hx => hf x (by simpa only [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using hx))
    (fun x _ => he x) hfi hei
  have factor : (∫ x in (1 : ℝ)..2, f x * (a * e x)) =
      a * (∫ x in (1 : ℝ)..2, f x * e x) := by
    calc
      _ = ∫ x in (1 : ℝ)..2, a * (f x * e x) :=
        intervalIntegral.integral_congr (fun _ _ => by ring)
      _ = _ := intervalIntegral.integral_const_mul _ _
  rw [factor] at hid
  have hfirst : ‖∫ x in (1 : ℝ)..2, f' x * e x‖ ≤ 3 * B / |τ| := by
    apply (primeProfile_fourier_once f' f'' hτ hf' hc' (fun x hx => (hB x hx).2)).trans
    apply div_le_div_of_nonneg_right _ (abs_nonneg τ)
    have h1 := (hB 1 (by constructor <;> norm_num)).1
    have h2 := (hB 2 (by constructor <;> norm_num)).1
    linarith
  have hn := congrArg norm hid
  rw [norm_mul, show ‖a‖ = |τ| by simp [a, Complex.norm_real, Real.norm_eq_abs]] at hn
  have hbound : |τ| * ‖∫ x in (1 : ℝ)..2, f x * e x‖ ≤
      ‖f 1‖ + ‖f 2‖ + 3 * B / |τ| := by
    rw [hn]
    calc
      _ ≤ ‖f 2 * e 2‖ + ‖f 1 * e 1‖ + ‖∫ x in (1 : ℝ)..2, f' x * e x‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ _ := by
        simp only [norm_mul, show ‖e 1‖ = 1 from norm_bourgainOscillation _,
          show ‖e 2‖ = 1 from norm_bourgainOscillation _, mul_one]
        linarith
  calc
    _ ≤ (‖f 1‖ + ‖f 2‖ + 3 * B / |τ|) / |τ| :=
      (le_div_iff₀ (abs_pos.2 hτ)).2 (by simpa [mul_comm] using hbound)
    _ = _ := by rw [add_div, div_div, ← pow_two, sq_abs]

private theorem profile_norm_le_window {ξ l x : ℝ} (hl : 0 ≤ l) (hx : 1 ≤ x) :
    ‖primeGaussianScaledLogProfile ξ l x‖ ≤ bagPhysicalHeightWindow (ξ * x) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hden : 1 ≤ 1 + l * Real.log x := by nlinarith [mul_nonneg hl (Real.log_nonneg hx)]
  have hi : ‖(1 + (l : ℂ) * (Real.log x : ℂ))⁻¹‖ ≤ 1 := by
    rw [show (1 + (l : ℂ) * (Real.log x : ℂ)) = ((1 + l * Real.log x : ℝ) : ℂ) by push_cast; rfl,
      norm_inv, Complex.norm_of_nonneg (by linarith : 0 ≤ 1 + l * Real.log x)]
    exact inv_le_one_of_one_le₀ hden
  simp only [primeGaussianScaledLogProfile, primeGaussianScaledProfile, norm_mul,
    Complex.norm_of_nonneg bagPhysicalHeightWindow.nonneg]
  have hV := norm_smoothAFECutoff_le_one hx0
  calc
    _ ≤ bagPhysicalHeightWindow (ξ * x) * 1 * 1 := by
      gcongr <;> simpa using bagPhysicalHeightWindow.nonneg (x := ξ * x)
    _ = _ := by ring

private theorem profile_boundary_bound :
    ∃ L : ℝ, 0 < L ∧ ∀ ξ ∈ Icc (1 / 2 : ℝ) 2, ∀ l ∈ Icc (0 : ℝ) 1,
      ‖primeGaussianScaledLogProfile ξ l 1‖ + ‖primeGaussianScaledLogProfile ξ l 2‖ ≤
        3 * L * |ξ - 1| := by
  have hc : Continuous (deriv (fun x : ℝ => bagPhysicalHeightWindow x)) :=
    (bagPhysicalHeightWindow.contDiff (n := 1)).continuous_deriv_one
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hc.continuousOn : ContinuousOn (deriv (fun x : ℝ => bagPhysicalHeightWindow x)) (Icc (0 : ℝ) 4))
  let L := |B| + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hLip (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 4) (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 4) :
      |bagPhysicalHeightWindow y - bagPhysicalHeightWindow x| ≤ L * |y - x| := by
    simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_deriv_le
      (fun t _ => (bagPhysicalHeightWindow.contDiff (n := 1)).differentiable (by norm_num) t)
      (fun t ht => (hB t ht).trans (by dsimp [L]; linarith [le_abs_self B]))
      (convex_Icc (0 : ℝ) 4) hx hy
  refine ⟨L, hL, ?_⟩
  intro ξ hξ l hl
  have hb (e : ℝ) (he : e = 1 ∨ e = 2) :
      ‖primeGaussianScaledLogProfile ξ l e‖ ≤ L * |ξ - 1| * e := by
    have he1 : 1 ≤ e := by rcases he with rfl | rfl <;> norm_num
    have he2 : e ≤ 2 := by rcases he with rfl | rfl <;> norm_num
    have he0 : 0 ≤ e := by linarith
    have hξ0 : 0 ≤ ξ := by linarith [hξ.1]
    have hξe : ξ * e ∈ Icc (0 : ℝ) 4 :=
      ⟨mul_nonneg hξ0 he0, (mul_le_mul hξ.2 he2 he0 (by norm_num)).trans_eq (by norm_num)⟩
    have hw : bagPhysicalHeightWindow e = 0 :=
      bagPhysicalHeightWindow.zero_of_le_dist (by
        change (1 / 2 : ℝ) ≤ dist e (3 / 2)
        rcases he with rfl | rfl <;> norm_num [Real.dist_eq])
    have hh := hLip e ⟨he0, by linarith⟩ (ξ * e) hξe
    rw [hw, sub_zero, abs_of_nonneg bagPhysicalHeightWindow.nonneg] at hh
    calc
      _ ≤ bagPhysicalHeightWindow (ξ * e) := profile_norm_le_window hl.1 he1
      _ ≤ L * |ξ * e - e| := hh
      _ = _ := by rw [show ξ * e - e = (ξ - 1) * e by ring, abs_mul, abs_of_nonneg he0]; ring
  have h1 := hb 1 (Or.inl rfl)
  have h2 := hb 2 (Or.inr rfl)
  linarith

/-- Complete signed moving-profile cancellation. The first boundary is paid
by the ACTUAL endpoint-window defect |ξ-1|; the remainder is inverse-square. -/
theorem exists_primeGaussianScaledLogProfile_fourier_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ ∈ Icc (1 / 2 : ℝ) 2, ∀ l ∈ Icc (0 : ℝ) 1,
      ∀ τ : ℝ, τ ≠ 0 →
        ‖∫ x in (1 : ℝ)..2, primeGaussianScaledLogProfile ξ l x * bourgainOscillation (τ * x)‖ ≤
          C * (|ξ - 1| / |τ| + 1 / τ ^ 2) := by
  obtain ⟨L, hL, hboundary⟩ := profile_boundary_bound
  obtain ⟨B₁, hB₁, hb₁⟩ := exists_primeGaussianScaledLogProfile_jet_bound 1
  obtain ⟨B₂, hB₂, hb₂⟩ := exists_primeGaussianScaledLogProfile_jet_bound 2
  let B := B₁ + B₂
  let C := 3 * L + 3 * B
  refine ⟨C, by dsimp [C, B]; positivity, ?_⟩
  intro ξ hξ l hl τ hτ
  have hs (k : ℕ) (x : ℝ) (hx : x ∈ Icc (1 : ℝ) 2) :=
    primeGaussianScaledLogProfile_jet_contDiffAt k ξ hl.1 hx.1
  have hj : ∀ x ∈ Icc (1 : ℝ) 2,
      ‖deriv (primeGaussianScaledLogProfile ξ l) x‖ ≤ B ∧
      ‖deriv (deriv (primeGaussianScaledLogProfile ξ l)) x‖ ≤ B := by
    intro x hx
    have h1 := hb₁ ξ hξ l hl x hx
    have h2 := hb₂ ξ hξ l hl x hx
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at h1 h2
    constructor <;> dsimp [B] <;> linarith
  have h := fourier_twice_boundary (primeGaussianScaledLogProfile ξ l)
    (deriv (primeGaussianScaledLogProfile ξ l))
    (deriv (deriv (primeGaussianScaledLogProfile ξ l))) hτ
    (fun x hx => by simpa only [iteratedDeriv_zero] using ((hs 0 x hx).differentiableAt (by simp)).hasDerivAt)
    (fun x hx => by simpa only [iteratedDeriv_one] using ((hs 1 x hx).differentiableAt (by simp)).hasDerivAt)
    (fun x hx => by simpa only [iteratedDeriv_one] using (hs 1 x hx).continuousAt.continuousWithinAt)
    (fun x hx => by simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      (hs 2 x hx).continuousAt.continuousWithinAt) hj
  calc
    _ ≤ (‖primeGaussianScaledLogProfile ξ l 1‖ + ‖primeGaussianScaledLogProfile ξ l 2‖) / |τ| +
        3 * B / τ ^ 2 := h
    _ ≤ 3 * L * |ξ - 1| / |τ| + 3 * B / τ ^ 2 := by
      gcongr
      exact hboundary ξ hξ l hl
    _ ≤ C * (|ξ - 1| / |τ| + 1 / τ ^ 2) := by
      calc
        _ = (3 * L) * (|ξ - 1| / |τ|) + (3 * B) * (1 / τ ^ 2) := by ring
        _ ≤ C * (|ξ - 1| / |τ|) + C * (1 / τ ^ 2) := by
          gcongr <;> dsimp [C, B] <;> linarith
        _ = _ := by ring

end RHTower
