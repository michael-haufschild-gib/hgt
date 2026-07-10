import GaloisForLFunctions.RHTower.CarrierZeroUnconditional

namespace RHTower

open Complex Real Metric Set

noncomputable section

theorem hasDerivAt_log_norm_complex {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) (h0 : f x ≠ 0) :
    HasDerivAt (fun y => Real.log ‖f y‖) (f' / f x).re x := by
  have hre : HasDerivAt (fun y => (f y).re) f'.re x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hf
  have him : HasDerivAt (fun y => (f y).im) f'.im x :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hf
  let B : ℝ := 2 * ((f x).re * f'.re + (f x).im * f'.im)
  have hnsq : HasDerivAt (fun y => Complex.normSq (f y)) B x := by
    have h := (hre.mul hre).add (him.mul him)
    have heq : (fun y => Complex.normSq (f y)) =
        fun y => (f y).re * (f y).re + (f y).im * (f y).im := by
      funext y
      rw [Complex.normSq_apply]
    rw [heq]
    convert h using 1
    dsimp [B]
    ring
  have hnsq0 : Complex.normSq (f x) ≠ 0 := fun h => h0 (Complex.normSq_eq_zero.mp h)
  have hlog := (Real.hasDerivAt_log hnsq0).comp x hnsq
  have hhalf := hlog.const_mul (1 / 2 : ℝ)
  simp only [Function.comp_apply] at hhalf
  have heq : (fun y => (1 / 2 : ℝ) * Real.log (Complex.normSq (f y))) =
      fun y => Real.log ‖f y‖ := by
    funext y
    rw [Complex.normSq_eq_norm_sq, Real.log_pow]
    ring
  rw [heq] at hhalf
  convert hhalf using 1
  rw [Complex.div_re]
  dsimp [B]
  field_simp [Complex.normSq_apply]

theorem hasDerivAt_stripPt_horizontal (τ σ : ℝ) :
    HasDerivAt (fun x : ℝ => stripPt x τ) 1 σ := by
  unfold stripPt
  simpa using (Complex.ofRealCLM.hasDerivAt (x := σ)).add_const ((τ : ℂ) * I)

theorem hasDerivAt_log_norm_archFactor_horizontal {σ τ : ℝ}
    (hσ : 0 < σ) (hτ : τ ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.log ‖archFactor (stripPt x τ)‖)
      (stripWindingRate σ τ) σ := by
  have hre : 0 < (stripPt σ τ).re := by rw [stripPt_re]; exact hσ
  have harch : HasDerivAt (fun x : ℝ => archFactor (stripPt x τ))
      (archFactorDeriv (stripPt σ τ)) σ := by
    simpa using (hasDerivAt_archFactor_of_re_pos hre).comp σ
      (hasDerivAt_stripPt_horizontal τ σ)
  have h := hasDerivAt_log_norm_complex harch (archFactor_stripPt_ne_zero hσ hτ)
  simpa [stripWindingRate, stripWinding] using h

theorem log_norm_archFactor_horizontal_strictMonoOn {τ : ℝ} (hτ : 12 ≤ τ) :
    StrictMonoOn (fun σ : ℝ => Real.log ‖archFactor (stripPt σ τ)‖) (Set.Ioo 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1)
  · intro σ hσ
    exact ((hasDerivAt_log_norm_archFactor_horizontal hσ.1 (by linarith)).continuousAt).continuousWithinAt
  · intro σ hσ
    rw [interior_Ioo] at hσ
    rw [(hasDerivAt_log_norm_archFactor_horizontal hσ.1 (by linarith)).deriv]
    exact lt_of_lt_of_le (stripFloor_pos hσ.1.le hτ)
      (stripWindingRate_ge hσ.1 hσ.2.le (by linarith))

theorem dirichletPoly_one (s : ℂ) : dirichletPoly 1 s = 1 := by
  simp [dirichletPoly]

theorem completedGN_one_eq_archFactor_add_reflect {s : ℂ} (h0 : 0 < s.re) :
    completedGN 1 s = archFactor s + archFactor (1 - s) := by
  rw [completedGN, gN]
  simp only [chiSymmetrize, dirichletPoly_one, mul_one]
  rw [mul_add, mul_one, archFactor_mul_zetaChi (Gammaℝ_ne_zero_of_re_pos h0)]

theorem norm_archFactor_reflect_eq_horizontal (s : ℂ) :
    ‖archFactor (1 - s)‖ = ‖archFactor (stripPt (1 - s.re) s.im)‖ := by
  have heq : 1 - s = (starRingEnd ℂ) (stripPt (1 - s.re) s.im) := by
    apply Complex.ext <;> simp [stripPt_re, stripPt_im]
  rw [heq, archFactor_conj, RCLike.norm_conj]

theorem completedGN_one_zero_re_eq_half_of_high {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (ht : 12 ≤ s.im)
    (hzero : completedGN 1 s = 0) :
    s.re = 1 / 2 := by
  have hsum := completedGN_one_eq_archFactor_add_reflect h0
  rw [hzero] at hsum
  have hnorm : ‖archFactor s‖ = ‖archFactor (1 - s)‖ := by
    have heq : archFactor s = -archFactor (1 - s) := eq_neg_of_add_eq_zero_left hsum.symm
    rw [heq, norm_neg]
  have hsrepr : s = stripPt s.re s.im := by
    apply Complex.ext <;> simp [stripPt_re, stripPt_im]
  have hlogeq : Real.log ‖archFactor (stripPt s.re s.im)‖ =
      Real.log ‖archFactor (stripPt (1 - s.re) s.im)‖ := by
    rw [← hsrepr, ← norm_archFactor_reflect_eq_horizontal s, hnorm]
  have hmono := log_norm_archFactor_horizontal_strictMonoOn ht
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmem : s.re ∈ Set.Ioo (0 : ℝ) 1 := ⟨h0, h1⟩
    have hrefmem : 1 - s.re ∈ Set.Ioo (0 : ℝ) 1 := by constructor <;> linarith
    exact (ne_of_lt (hmono hmem hrefmem (by linarith))) hlogeq
  · have hmem : s.re ∈ Set.Ioo (0 : ℝ) 1 := ⟨h0, h1⟩
    have hrefmem : 1 - s.re ∈ Set.Ioo (0 : ℝ) 1 := by constructor <;> linarith
    exact (ne_of_lt (hmono hrefmem hmem (by linarith))) hlogeq.symm

theorem completedGN_one_zero_re_eq_half_of_abs_im_ge {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (ht : 12 ≤ |s.im|)
    (hzero : completedGN 1 s = 0) :
    s.re = 1 / 2 := by
  rcases le_total 0 s.im with him | him
  · apply completedGN_one_zero_re_eq_half_of_high h0 h1 ?_ hzero
    rwa [abs_of_nonneg him] at ht
  · have him' : s.im ≤ 0 := him
    have ht' : 12 ≤ ((starRingEnd ℂ) s).im := by
      rw [abs_of_nonpos him'] at ht
      simpa using ht
    have hzero' : completedGN 1 ((starRingEnd ℂ) s) = 0 := by
      rw [completedGN_conj, hzero, map_zero]
    have hre := completedGN_one_zero_re_eq_half_of_high
      (s := (starRingEnd ℂ) s) (by simpa using h0) (by simpa using h1) ht' hzero'
    simpa using hre

end

end RHTower
