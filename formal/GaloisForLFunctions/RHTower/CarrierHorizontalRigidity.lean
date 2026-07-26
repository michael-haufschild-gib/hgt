import GaloisForLFunctions.RHTower.CarrierZeroUnconditional
import GaloisForLFunctions.U0.U0KummerBranch
import GaloisForLFunctions.RHTower.CoherentTower

namespace RHTower

open Complex Real Metric Set

noncomputable section

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
  have h := GaloisForLFunctions.HTGeometry.hasDerivAt_log_norm_complex harch (archFactor_stripPt_ne_zero hσ hτ)
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

theorem completedGN_one_zero_simple_of_high {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (ht : 12 ≤ s.im)
    (hzero : completedGN 1 s = 0) :
    deriv (completedGN 1) s ≠ 0 := by
  have hre := completedGN_one_zero_re_eq_half_of_high h0 h1 ht hzero
  have hs : s = linePt s.im := by
    apply Complex.ext
    · simpa [linePt_re] using hre
    · simp [linePt]
  have hfloor : (1 : ℝ) ≤ ‖dirichletPoly 1 (linePt s.im)‖ := by
    rw [dirichletPoly_one, norm_one]
  have hwind : 0 < windingRate s.im := by
    have hp : 0 < stripFloor (1 / 2) s.im := stripFloor_pos (by norm_num) ht
    have hr := stripWindingRate_ge (show (0 : ℝ) < 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) ≤ 1 by norm_num) (by linarith : 0 < s.im)
    have : 0 < stripWindingRate (1 / 2) s.im := lt_of_lt_of_le hp hr
    rw [← congrFun stripWindingRate_one_half s.im]
    exact this
  have hdom : dirichletLineDerivativeBudget 1 < (1 : ℝ) * windingRate s.im := by
    simpa [dirichletLineDerivativeBudget] using hwind
  rw [hs] at hzero ⊢
  exact deriv_completedGN_line_zero_ne_zero 1 s.im 1 (by norm_num) hfloor hdom hzero

theorem completedGN_one_zero_simple_of_abs_im_ge {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (ht : 12 ≤ |s.im|)
    (hzero : completedGN 1 s = 0) :
    deriv (completedGN 1) s ≠ 0 := by
  rcases le_total 0 s.im with him | him
  · apply completedGN_one_zero_simple_of_high h0 h1 ?_ hzero
    rwa [abs_of_nonneg him] at ht
  · have him' : s.im ≤ 0 := him
    have ht' : 12 ≤ ((starRingEnd ℂ) s).im := by
      rw [abs_of_nonpos him'] at ht
      simpa using ht
    have hzero' : completedGN 1 ((starRingEnd ℂ) s) = 0 := by
      rw [completedGN_conj, hzero, map_zero]
    have hsimple' := completedGN_one_zero_simple_of_high
      (s := (starRingEnd ℂ) s) (by simpa using h0) (by simpa using h1) ht' hzero'
    have hfun : (starRingEnd ℂ) ∘ completedGN 1 ∘ (starRingEnd ℂ) = completedGN 1 := by
      funext z
      simpa [Function.comp_apply] using (completedGN_conj 1 ((starRingEnd ℂ) z)).symm
    have hder : deriv (completedGN 1) =
        (starRingEnd ℂ) ∘ deriv (completedGN 1) ∘ (starRingEnd ℂ) := by
      calc
        deriv (completedGN 1) = deriv ((starRingEnd ℂ) ∘ completedGN 1 ∘ (starRingEnd ℂ)) :=
          congrArg deriv hfun.symm
        _ = (starRingEnd ℂ) ∘ deriv (completedGN 1) ∘ (starRingEnd ℂ) :=
          deriv_conj_conj
    have heq : deriv (completedGN 1) ((starRingEnd ℂ) s) =
        (starRingEnd ℂ) (deriv (completedGN 1) s) := by
      simpa [Function.comp_apply] using congrFun hder ((starRingEnd ℂ) s)
    intro hzeroDeriv
    rw [hzeroDeriv, map_zero] at heq
    exact hsimple' heq

/-- The depth-one completed carrier is zero-free in the high right half of the critical strip. -/
theorem completedGN_one_ne_zero_of_high_right {s : ℂ}
    (hhalf : 1 / 2 < s.re) (h1 : s.re < 1) (ht : 12 ≤ |s.im|) :
    completedGN 1 s ≠ 0 := by
  intro hzero
  have hre := completedGN_one_zero_re_eq_half_of_abs_im_ge (by linarith) h1 ht hzero
  linarith

/-- The high right half of the critical strip. -/
def carrierOneHighRight : Set ℂ :=
  {s | 1 / 2 < s.re ∧ s.re < 1 ∧ 12 < s.im}

theorem isOpen_carrierOneHighRight : IsOpen carrierOneHighRight := by
  simpa only [carrierOneHighRight, Set.setOf_and] using
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt continuous_const Complex.continuous_im))

theorem convex_carrierOneHighRight : Convex ℝ carrierOneHighRight :=
  by
    simpa only [carrierOneHighRight, Set.setOf_and] using
      (convex_halfSpace_re_gt (1 / 2)).inter
        ((convex_halfSpace_re_lt 1).inter (convex_halfSpace_im_gt 12))

theorem carrierOneHighRight_nonempty : carrierOneHighRight.Nonempty := by
  refine ⟨((3 / 4 : ℝ) : ℂ) + ((13 : ℝ) : ℂ) * I, ?_⟩
  constructor <;> norm_num

theorem completedGN_one_ne_zero_carrierOneHighRight :
    ∀ s ∈ carrierOneHighRight, completedGN 1 s ≠ 0 := by
  intro s hs hzero
  change 1 / 2 < s.re ∧ s.re < 1 ∧ 12 < s.im at hs
  have hre := completedGN_one_zero_re_eq_half_of_high (by linarith) hs.2.1 (by linarith) hzero
  linarith

/-- Every dyadic root of the depth-one carrier exists analytically on the high right strip. -/
theorem exists_completedGN_one_root_carrierOneHighRight (k : ℕ) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G carrierOneHighRight ∧
      (∀ z, G z ≠ 0) ∧ ∀ z ∈ carrierOneHighRight, G z ^ (2 ^ k) = completedGN 1 z := by
  exact U0KummerBranch.exists_analyticOnNhd_pow_eq isOpen_carrierOneHighRight
    (isSimplyConnected_of_convex convex_carrierOneHighRight carrierOneHighRight_nonempty)
    ((completedGN_analyticOnNhd_strip 1).mono (fun z hz => ⟨by linarith [hz.1], hz.2.1⟩))
    completedGN_one_ne_zero_carrierOneHighRight (pow_ne_zero k two_ne_zero)

/-- The independent depth-one dyadic roots assemble into an unconditional coherent Kummer tower
on the high right half-strip. -/
theorem completedGN_one_coherentTower_carrierOneHighRight :
    Nonempty (CoherentTower (completedGN 1) carrierOneHighRight) := by
  obtain ⟨z₀, hz₀⟩ := carrierOneHighRight_nonempty
  have hfan : AnalyticOnNhd ℂ (completedGN 1) carrierOneHighRight :=
    (completedGN_analyticOnNhd_strip 1).mono (fun z hz => ⟨by linarith [hz.1], hz.2.1⟩)
  exact (coherentTower_iff_nonvanishing isOpen_carrierOneHighRight
    (isSimplyConnected_of_convex convex_carrierOneHighRight carrierOneHighRight_nonempty)
    convex_carrierOneHighRight.isPreconnected hfan hz₀
    (completedGN_one_ne_zero_carrierOneHighRight z₀ hz₀)).2
    completedGN_one_ne_zero_carrierOneHighRight

end

end RHTower
