/-
# Horizontal phase-modulus rigidity at carrier depth two

The first nonconstant finite carrier is still rigid.  Its Dirichlet factor is
`1 + 2^{-s}`.  The unit-disc Cayley bound `Re(q/(1+q)) < 1/2` limits this factor's
horizontal counter-rate by `(log 2)/2`, while the archimedean horizontal rate grows
without bound.  Hence the direct completed summand has strictly increasing horizontal
log-modulus at large height.  Reflection then forces every high strip zero onto the
critical line; the same rate inequality makes it simple and supplies dyadic roots on
the zero-free right half-strip.
-/
import GaloisForLFunctions.RHTower.CarrierHorizontalRigidity

namespace RHTower

open Complex Real Metric Set

noncomputable section

theorem dirichletPoly_two (s : ℂ) :
    dirichletPoly 2 s = 1 + (2 : ℂ) ^ (-s) := by
  norm_num [dirichletPoly, Finset.sum_Icc_succ_top]

/-- The Cayley transform of the unit disc lies to the left of `Re z = 1/2`. -/
theorem cayley_re_lt_half {q : ℂ} (hq : ‖q‖ < 1) :
    (q / (1 + q)).re < 1 / 2 := by
  have hqne : 1 + q ≠ 0 := by
    intro h
    have : q = -1 := by linear_combination h
    rw [this, norm_neg, norm_one] at hq
    exact (lt_irrefl 1) hq
  have hden : 0 < Complex.normSq (1 + q) := Complex.normSq_pos.mpr hqne
  have hsq : Complex.normSq q < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg q]
  rw [Complex.normSq_apply] at hsq
  rw [Complex.div_re]
  simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
    zero_add, Complex.normSq_apply]
  rw [← add_div]
  have hden' : 0 < (1 + q.re) * (1 + q.re) + q.im * q.im := by
    simpa [Complex.normSq_apply] using hden
  apply (div_lt_iff₀ hden').2
  nlinarith

theorem norm_two_cpow_neg_strip_lt_one {σ τ : ℝ} (hσ : 0 < σ) :
    ‖(2 : ℂ) ^ (-stripPt σ τ)‖ < 1 := by
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2), Complex.neg_re,
    stripPt_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

/-- The depth-two Dirichlet factor is zero-free in the open right half-plane. -/
theorem dirichletPoly_two_ne_zero {s : ℂ} (h0 : 0 < s.re) :
    dirichletPoly 2 s ≠ 0 := by
  rw [dirichletPoly_two]
  intro h
  have hq : (2 : ℂ) ^ (-s) = -1 := by linear_combination h
  have hs : s = stripPt s.re s.im := by
    apply Complex.ext <;> simp [stripPt_re, stripPt_im]
  have hlt := norm_two_cpow_neg_strip_lt_one (τ := s.im) h0
  rw [← hs, hq, norm_neg, norm_one] at hlt
  exact (lt_irrefl 1) hlt

theorem hasDerivAt_dirichletPoly_two (s : ℂ) :
    HasDerivAt (dirichletPoly 2)
      ((2 : ℂ) ^ (-s) * Complex.log 2 * (-1)) s := by
  have hcpow : HasDerivAt (fun z : ℂ => (2 : ℂ) ^ (-z))
      ((2 : ℂ) ^ (-s) * Complex.log 2 * (-1)) s :=
    ((hasDerivAt_id s).neg).const_cpow (Or.inl (by norm_num))
  have h := (hasDerivAt_const s (1 : ℂ)).add hcpow
  rw [show dirichletPoly 2 = fun z => 1 + (2 : ℂ) ^ (-z) from
    funext dirichletPoly_two]
  simpa only [Pi.add_apply, zero_add] using h

theorem hasDerivAt_log_norm_dirichletPoly_two_horizontal {σ τ : ℝ} (hσ : 0 < σ) :
    HasDerivAt (fun x : ℝ => Real.log ‖dirichletPoly 2 (stripPt x τ)‖)
      (((2 : ℂ) ^ (-stripPt σ τ) * Complex.log 2 * (-1)) /
        dirichletPoly 2 (stripPt σ τ)).re σ := by
  apply hasDerivAt_log_norm_complex
  · simpa using (hasDerivAt_dirichletPoly_two (stripPt σ τ)).comp σ
      (hasDerivAt_stripPt_horizontal τ σ)
  · exact dirichletPoly_two_ne_zero (by simpa [stripPt_re] using hσ)

/-- The depth-two Dirichlet factor's horizontal log-rate is bounded below by
`-(log 2)/2`, uniformly in the height and abscissa. -/
theorem deriv_log_norm_dirichletPoly_two_horizontal_gt {σ τ : ℝ} (hσ : 0 < σ) :
    -(Real.log 2) / 2 <
      deriv (fun x : ℝ => Real.log ‖dirichletPoly 2 (stripPt x τ)‖) σ := by
  let q : ℂ := (2 : ℂ) ^ (-stripPt σ τ)
  have hq : ‖q‖ < 1 := norm_two_cpow_neg_strip_lt_one hσ
  have hcre := cayley_re_lt_half hq
  have hder := hasDerivAt_log_norm_dirichletPoly_two_horizontal (τ := τ) hσ
  rw [hder.deriv, dirichletPoly_two]
  have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℝ) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hlog]
  change -(Real.log 2) / 2 <
    (q * (Real.log 2 : ℂ) * (-1) / (1 + q)).re
  have heq : q * (Real.log 2 : ℂ) * (-1) / (1 + q) =
      (-(Real.log 2) : ℂ) * (q / (1 + q)) := by ring
  rw [heq, Complex.mul_re]
  simp only [Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, neg_zero,
    zero_mul, sub_zero]
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- At all sufficiently high positive heights, the direct depth-two completed summand has
strictly increasing horizontal log-modulus throughout the open critical strip. -/
theorem exists_height_two_direct_horizontal_strictMono :
    ∃ A > 0, ∀ τ, A ≤ τ →
      StrictMonoOn
        (fun σ : ℝ => Real.log ‖archFactor (stripPt σ τ)‖ +
          Real.log ‖dirichletPoly 2 (stripPt σ τ)‖)
        (Set.Ioo 0 1) := by
  obtain ⟨A, hA, hfloor⟩ := exists_height_net_rate_ge
    (P := (∅ : Finset ℕ)) (σ := 0) (B_D := Real.log 2 / 2) (ρ₀ := 1) (by norm_num)
  refine ⟨A, hA, fun τ hAτ => ?_⟩
  have hτ : 0 < τ := lt_of_lt_of_le hA hAτ
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1)
  · intro σ hσ
    exact (((hasDerivAt_log_norm_archFactor_horizontal hσ.1 (ne_of_gt hτ)).add
      (hasDerivAt_log_norm_dirichletPoly_two_horizontal hσ.1)).continuousAt).continuousWithinAt
  · intro σ hσ
    rw [interior_Ioo] at hσ
    have harch := hasDerivAt_log_norm_archFactor_horizontal hσ.1 (ne_of_gt hτ)
    have hdp := hasDerivAt_log_norm_dirichletPoly_two_horizontal (τ := τ) hσ.1
    have hsum := harch.add hdp
    have hsum' : HasDerivAt
        (fun x : ℝ => Real.log ‖archFactor (stripPt x τ)‖ +
          Real.log ‖dirichletPoly 2 (stripPt x τ)‖)
        (stripWindingRate σ τ +
          (((2 : ℂ) ^ (-stripPt σ τ) * Complex.log 2 * (-1)) /
            dirichletPoly 2 (stripPt σ τ)).re) σ := by
      simpa only [Pi.add_apply] using hsum
    rw [hsum'.deriv]
    have hdpgt := deriv_log_norm_dirichletPoly_two_horizontal_gt (τ := τ) hσ.1
    rw [hdp.deriv] at hdpgt
    have hbase : 1 ≤ stripFloor 0 τ - Real.log 2 / 2 := by
      simpa [eulerHeadBound] using hfloor τ hAτ
    have hmono : stripFloor 0 τ ≤ stripFloor σ τ :=
      stripFloor_mono_sigma hσ.1.le hτ
    have hwind : stripFloor σ τ ≤ stripWindingRate σ τ :=
      stripWindingRate_ge hσ.1 hσ.2.le hτ
    linarith

/-- Completed finite carriers are sums of a direct completed Dirichlet polynomial and its
functional-equation reflection. -/
theorem completedGN_eq_direct_add_reflect {N : ℕ} {s : ℂ} (h0 : 0 < s.re) :
    completedGN N s =
      archFactor s * dirichletPoly N s + archFactor (1 - s) * dirichletPoly N (1 - s) := by
  rw [completedGN, gN]
  simp only [chiSymmetrize, mul_add]
  rw [← mul_assoc, archFactor_mul_zetaChi (Gammaℝ_ne_zero_of_re_pos h0)]

theorem norm_direct_two_reflect_eq_horizontal (s : ℂ) :
    ‖archFactor (1 - s) * dirichletPoly 2 (1 - s)‖ =
      ‖archFactor (stripPt (1 - s.re) s.im) *
        dirichletPoly 2 (stripPt (1 - s.re) s.im)‖ := by
  have heq : 1 - s = (starRingEnd ℂ) (stripPt (1 - s.re) s.im) := by
    apply Complex.ext <;> simp [stripPt_re, stripPt_im]
  rw [heq, archFactor_conj, dirichletPoly_conj, ← map_mul, RCLike.norm_conj]

/-- Above one absolute height, every depth-two completed-carrier zero in the critical strip
lies on the critical line. -/
theorem exists_height_completedGN_two_zero_re_eq_half :
    ∃ A > 0, ∀ s : ℂ, 0 < s.re → s.re < 1 → A ≤ s.im →
      completedGN 2 s = 0 → s.re = 1 / 2 := by
  obtain ⟨A, hA, hmono⟩ := exists_height_two_direct_horizontal_strictMono
  refine ⟨A, hA, fun s h0 h1 hheight hzero => ?_⟩
  have hsum := completedGN_eq_direct_add_reflect (N := 2) h0
  rw [hzero] at hsum
  have hnorm : ‖archFactor s * dirichletPoly 2 s‖ =
      ‖archFactor (1 - s) * dirichletPoly 2 (1 - s)‖ := by
    have heq : archFactor s * dirichletPoly 2 s =
        -(archFactor (1 - s) * dirichletPoly 2 (1 - s)) :=
      eq_neg_of_add_eq_zero_left hsum.symm
    rw [heq, norm_neg]
  have hsrepr : s = stripPt s.re s.im := by
    apply Complex.ext <;> simp [stripPt_re, stripPt_im]
  have harch0 : ‖archFactor (stripPt s.re s.im)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (archFactor_stripPt_ne_zero h0 (by linarith [hA, hheight]))
  have hD0 : ‖dirichletPoly 2 (stripPt s.re s.im)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (dirichletPoly_two_ne_zero (by simpa [stripPt_re] using h0))
  have href0 : 0 < 1 - s.re := by linarith
  have harchR0 : ‖archFactor (stripPt (1 - s.re) s.im)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (archFactor_stripPt_ne_zero href0 (by linarith [hA, hheight]))
  have hDR0 : ‖dirichletPoly 2 (stripPt (1 - s.re) s.im)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (dirichletPoly_two_ne_zero (by simpa [stripPt_re] using href0))
  have hlogeq :
      Real.log ‖archFactor (stripPt s.re s.im)‖ +
          Real.log ‖dirichletPoly 2 (stripPt s.re s.im)‖ =
        Real.log ‖archFactor (stripPt (1 - s.re) s.im)‖ +
          Real.log ‖dirichletPoly 2 (stripPt (1 - s.re) s.im)‖ := by
    rw [← Real.log_mul harch0 hD0, ← norm_mul, ← hsrepr, hnorm,
      norm_direct_two_reflect_eq_horizontal, norm_mul, Real.log_mul harchR0 hDR0]
  have hstrict := hmono s.im hheight
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmem : s.re ∈ Set.Ioo (0 : ℝ) 1 := ⟨h0, h1⟩
    have hrefmem : 1 - s.re ∈ Set.Ioo (0 : ℝ) 1 := by constructor <;> linarith
    exact (ne_of_lt (hstrict hmem hrefmem (by linarith))) hlogeq
  · have hmem : s.re ∈ Set.Ioo (0 : ℝ) 1 := ⟨h0, h1⟩
    have hrefmem : 1 - s.re ∈ Set.Ioo (0 : ℝ) 1 := by constructor <;> linarith
    exact (ne_of_lt (hstrict hrefmem hmem (by linarith))) hlogeq.symm

theorem re_deriv_dirichletPoly_two_div_gt {s : ℂ} (h0 : 0 < s.re) :
    -(Real.log 2) / 2 <
      (deriv (dirichletPoly 2) s / dirichletPoly 2 s).re := by
  let q : ℂ := (2 : ℂ) ^ (-s)
  have hs : s = stripPt s.re s.im := by
    apply Complex.ext <;> simp [stripPt_re, stripPt_im]
  have hq : ‖q‖ < 1 := by
    dsimp [q]
    rw [hs]
    exact norm_two_cpow_neg_strip_lt_one h0
  have hcre := cayley_re_lt_half hq
  rw [(hasDerivAt_dirichletPoly_two s).deriv, dirichletPoly_two]
  have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℝ) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hlog]
  change -(Real.log 2) / 2 <
    (q * (Real.log 2 : ℂ) * (-1) / (1 + q)).re
  have heq : q * (Real.log 2 : ℂ) * (-1) / (1 + q) =
      (-(Real.log 2) : ℂ) * (q / (1 + q)) := by ring
  rw [heq, Complex.mul_re]
  simp only [Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, neg_zero,
    zero_mul, sub_zero]
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- Above one absolute positive height, every depth-two strip zero lies on the line and is
simple. -/
theorem exists_height_completedGN_two_zero_simple_of_high :
    ∃ A > 0, ∀ s : ℂ, 0 < s.re → s.re < 1 → A ≤ s.im →
      completedGN 2 s = 0 →
        s.re = 1 / 2 ∧ deriv (completedGN 2) s ≠ 0 := by
  obtain ⟨A₁, hA₁, halign⟩ := exists_height_completedGN_two_zero_re_eq_half
  obtain ⟨A₂, hA₂, hfloor⟩ := exists_height_net_rate_ge
    (P := (∅ : Finset ℕ)) (σ := 0) (B_D := Real.log 2 / 2) (ρ₀ := 1) (by norm_num)
  refine ⟨max A₁ A₂, lt_of_lt_of_le hA₁ (le_max_left _ _), fun s h0 h1 hheight hzero => ?_⟩
  have hA₁s : A₁ ≤ s.im := le_trans (le_max_left _ _) hheight
  have hA₂s : A₂ ≤ s.im := le_trans (le_max_right _ _) hheight
  have hre := halign s h0 h1 hA₁s hzero
  refine ⟨hre, ?_⟩
  have hs : s = linePt s.im := by
    apply Complex.ext
    · simpa [linePt_re] using hre
    · simp [linePt]
  have ht : 0 < s.im := lt_of_lt_of_le hA₂ hA₂s
  have hbase : 1 ≤ stripFloor 0 s.im - Real.log 2 / 2 := by
    simpa [eulerHeadBound] using hfloor s.im hA₂s
  have hfloorHalf : stripFloor 0 s.im ≤ stripFloor (1 / 2) s.im :=
    stripFloor_mono_sigma (by norm_num) ht
  have hwindStrip : stripFloor (1 / 2) s.im ≤ stripWindingRate (1 / 2) s.im :=
    stripWindingRate_ge (by norm_num) (by norm_num) ht
  have hwind : Real.log 2 / 2 < windingRate s.im := by
    rw [← congrFun stripWindingRate_one_half s.im]
    linarith
  have hDlog := re_deriv_dirichletPoly_two_div_gt (s := linePt s.im) (linePt_re_pos _)
  have hphase : 0 < windingRate s.im +
      (deriv (dirichletPoly 2) (linePt s.im) / dirichletPoly 2 (linePt s.im)).re := by
    linarith
  have hDne := dirichletPoly_two_ne_zero (s := linePt s.im) (linePt_re_pos _)
  have hexact := norm_deriv_completedGN_line_zero 2 s.im (hs ▸ hzero) hDne hphase.le
  rw [hs]
  apply norm_pos_iff.mp
  rw [hexact]
  have harch : 0 < ‖archFactor (linePt s.im)‖ :=
    norm_pos_iff.mpr (archFactor_linePt_ne_zero _)
  have hD : 0 < ‖dirichletPoly 2 (linePt s.im)‖ := norm_pos_iff.mpr hDne
  positivity

/-- The depth-two high-zero alignment and simplicity theorem at both signs of the height. -/
theorem exists_height_completedGN_two_zero_simple_of_abs_im_ge :
    ∃ A > 0, ∀ s : ℂ, 0 < s.re → s.re < 1 → A ≤ |s.im| →
      completedGN 2 s = 0 →
        s.re = 1 / 2 ∧ deriv (completedGN 2) s ≠ 0 := by
  obtain ⟨A, hA, hhigh⟩ := exists_height_completedGN_two_zero_simple_of_high
  refine ⟨A, hA, fun s h0 h1 hheight hzero => ?_⟩
  rcases le_total 0 s.im with him | him
  · exact hhigh s h0 h1 (by rwa [abs_of_nonneg him] at hheight) hzero
  · have him' : s.im ≤ 0 := him
    have hheight' : A ≤ ((starRingEnd ℂ) s).im := by
      rw [abs_of_nonpos him'] at hheight
      simpa using hheight
    have hzero' : completedGN 2 ((starRingEnd ℂ) s) = 0 := by
      rw [completedGN_conj, hzero, map_zero]
    obtain ⟨hre, hsimple'⟩ := hhigh ((starRingEnd ℂ) s)
      (by simpa using h0) (by simpa using h1) hheight' hzero'
    refine ⟨by simpa using hre, ?_⟩
    have hfun : (starRingEnd ℂ) ∘ completedGN 2 ∘ (starRingEnd ℂ) = completedGN 2 := by
      funext z
      simpa [Function.comp_apply] using (completedGN_conj 2 ((starRingEnd ℂ) z)).symm
    have hder : deriv (completedGN 2) =
        (starRingEnd ℂ) ∘ deriv (completedGN 2) ∘ (starRingEnd ℂ) := by
      calc
        deriv (completedGN 2) = deriv ((starRingEnd ℂ) ∘ completedGN 2 ∘ (starRingEnd ℂ)) :=
          congrArg deriv hfun.symm
        _ = (starRingEnd ℂ) ∘ deriv (completedGN 2) ∘ (starRingEnd ℂ) :=
          deriv_conj_conj
    have heq : deriv (completedGN 2) ((starRingEnd ℂ) s) =
        (starRingEnd ℂ) (deriv (completedGN 2) s) := by
      simpa [Function.comp_apply] using congrFun hder ((starRingEnd ℂ) s)
    intro hzeroDeriv
    rw [hzeroDeriv, map_zero] at heq
    exact hsimple' heq

/-- Above one absolute height, the depth-two carrier is zero-free on the right half-strip and
therefore has analytic dyadic roots of every level there. -/
theorem exists_height_completedGN_two_root_highRight :
    ∃ A > 0, ∀ k : ℕ,
      ∃ G : ℂ → ℂ,
        AnalyticOnNhd ℂ G {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ A < s.im} ∧
        (∀ z, G z ≠ 0) ∧
        ∀ z ∈ {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ A < s.im},
          G z ^ (2 ^ k) = completedGN 2 z := by
  obtain ⟨A, hA, hrigid⟩ := exists_height_completedGN_two_zero_simple_of_abs_im_ge
  refine ⟨A, hA, fun k => ?_⟩
  let U : Set ℂ := {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ A < s.im}
  have hopen : IsOpen U := by
    simpa only [U, Set.setOf_and] using
      (isOpen_lt continuous_const Complex.continuous_re).inter
        ((isOpen_lt Complex.continuous_re continuous_const).inter
          (isOpen_lt continuous_const Complex.continuous_im))
  have hconvex : Convex ℝ U := by
    simpa only [U, Set.setOf_and] using
      (convex_halfSpace_re_gt (1 / 2)).inter
        ((convex_halfSpace_re_lt 1).inter (convex_halfSpace_im_gt A))
  have hnonempty : U.Nonempty := by
    refine ⟨((3 / 4 : ℝ) : ℂ) + ((A + 1 : ℝ) : ℂ) * I, ?_⟩
    change 1 / 2 < _ ∧ _ < 1 ∧ A < _
    constructor
    · norm_num
    constructor
    · norm_num
    · simp
  have hzeroFree : ∀ z ∈ U, completedGN 2 z ≠ 0 := by
    intro z hz hzero
    change 1 / 2 < z.re ∧ z.re < 1 ∧ A < z.im at hz
    have habs : A ≤ |z.im| := by
      rw [abs_of_pos (lt_trans hA hz.2.2)]
      exact hz.2.2.le
    have hre := (hrigid z (by linarith) hz.2.1 habs hzero).1
    linarith
  have hroot := U0KummerBranch.exists_analyticOnNhd_pow_eq hopen
    (isSimplyConnected_of_convex hconvex hnonempty)
    ((completedGN_analyticOnNhd_strip 2).mono (fun z hz => ⟨by linarith [hz.1], hz.2.1⟩))
    hzeroFree (pow_ne_zero k two_ne_zero)
  simpa [U] using hroot

/-- At some absolute height the depth-two regional roots assemble into a coherent Kummer tower,
not merely unrelated roots at each dyadic level. -/
theorem exists_height_completedGN_two_coherentTower_highRight :
    ∃ A > 0,
      Nonempty (CoherentTower (completedGN 2)
        {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ A < s.im}) := by
  obtain ⟨A, hA, hroots⟩ := exists_height_completedGN_two_root_highRight
  refine ⟨A, hA, ?_⟩
  let U : Set ℂ := {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ A < s.im}
  have hopen : IsOpen U := by
    simpa only [U, Set.setOf_and] using
      (isOpen_lt continuous_const Complex.continuous_re).inter
        ((isOpen_lt Complex.continuous_re continuous_const).inter
          (isOpen_lt continuous_const Complex.continuous_im))
  have hconvex : Convex ℝ U := by
    simpa only [U, Set.setOf_and] using
      (convex_halfSpace_re_gt (1 / 2)).inter
        ((convex_halfSpace_re_lt 1).inter (convex_halfSpace_im_gt A))
  let z₀ : ℂ := ((3 / 4 : ℝ) : ℂ) + ((A + 1 : ℝ) : ℂ) * I
  have hz₀ : z₀ ∈ U := by
    change 1 / 2 < _ ∧ _ < 1 ∧ A < _
    constructor
    · norm_num [z₀]
    constructor
    · norm_num [z₀]
    · simp [z₀]
  have hfan : AnalyticOnNhd ℂ (completedGN 2) U :=
    (completedGN_analyticOnNhd_strip 2).mono (fun z hz => ⟨by linarith [hz.1], hz.2.1⟩)
  obtain ⟨G₀, hG₀an, hG₀ne, hG₀pow⟩ := hroots 0
  have hf0 : completedGN 2 z₀ ≠ 0 := by
    have hp := hG₀pow z₀ (by simpa [U] using hz₀)
    rw [pow_zero, pow_one] at hp
    rw [← hp]
    exact hG₀ne z₀
  have htower : Nonempty (CoherentTower (completedGN 2) U) := by
    apply coherentTower_of_exists_roots_all_two_powers hopen hconvex hz₀ hfan hf0
    intro k
    obtain ⟨G, hGan, -, hGpow⟩ := hroots k
    exact ⟨G, by simpa [U] using hGan, fun s hs => hGpow s (by simpa [U] using hs)⟩
  simpa [U] using htower

end

end RHTower
