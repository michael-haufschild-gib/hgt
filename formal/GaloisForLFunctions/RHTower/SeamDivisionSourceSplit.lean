import GaloisForLFunctions.HTGeometry.GammaLogDeriv
import GaloisForLFunctions.RHTower.VorosPowerSumClosedForm
import GaloisForLFunctions.RHTower.ZetaRealStrip

/-!
# Seam division: the source split needs the functional-equation cancellation
-/

namespace GaloisForLFunctions.SeamSplit

open Complex GaloisForLFunctions GaloisForLFunctions.VorosClosedForm

noncomputable section

/-! ## The digamma value at a quarter -/

theorem digamma_half : Complex.digamma (1 / 2 : ℂ)
    = -(Real.eulerMascheroniConstant : ℂ) - 2 * Complex.log 2 := by
  have hcond : ∀ n : ℕ, (2 : ℂ) * (1 / 2 : ℂ) ≠ -(n : ℂ) := by
    intro n h
    have hre := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    norm_num at hre
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hdup := HTGeometry.digamma_duplication (1 / 2 : ℂ) hcond
  rw [show (2 : ℂ) * (1 / 2 : ℂ) = 1 by ring,
    show (1 / 2 : ℂ) + 1 / 2 = 1 by ring, Complex.digamma_one] at hdup
  linear_combination -hdup

theorem digamma_three_quarters_sub_quarter :
    Complex.digamma (3 / 4 : ℂ) - Complex.digamma (1 / 4 : ℂ) = (Real.pi : ℂ) := by
  have hs : ∀ k : ℤ, (1 / 4 : ℂ) ≠ (k : ℂ) := by
    intro k h
    have hre := congrArg Complex.re h
    simp only [Complex.intCast_re] at hre
    norm_num at hre
    have hk : ((k : ℤ) : ℝ) = 1 / 4 := hre.symm
    have h4 : ((4 * k : ℤ) : ℝ) = 1 := by push_cast; linarith
    have : (4 * k : ℤ) = 1 := by exact_mod_cast h4
    omega
  have href := HTGeometry.digamma_reflection (1 / 4 : ℂ) hs
  rw [show (1 : ℂ) - 1 / 4 = 3 / 4 by ring] at href
  rw [href]
  have hval : Complex.cos ((Real.pi : ℂ) * (1 / 4 : ℂ))
      / Complex.sin ((Real.pi : ℂ) * (1 / 4 : ℂ)) = 1 := by
    have hcast : ((Real.pi : ℂ) * (1 / 4 : ℂ)) = ((Real.pi / 4 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
      Real.sin_pi_div_four, ← Complex.ofReal_div, div_self (by positivity)]
    norm_num
  rw [hval, mul_one]

/-- **The digamma value at a quarter**: `ψ(1/4) = −γ − 3 log 2 − π/2`. -/
theorem digamma_one_quarter : Complex.digamma (1 / 4 : ℂ)
    = -(Real.eulerMascheroniConstant : ℂ) - 3 * Complex.log 2 - (Real.pi : ℂ) / 2 := by
  have hcond : ∀ n : ℕ, (2 : ℂ) * (1 / 4 : ℂ) ≠ -(n : ℂ) := by
    intro n h
    have hre := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    norm_num at hre
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hdup := HTGeometry.digamma_duplication (1 / 4 : ℂ) hcond
  rw [show (2 : ℂ) * (1 / 4 : ℂ) = 1 / 2 by ring,
    show (1 / 4 : ℂ) + 1 / 2 = 3 / 4 by ring, digamma_half] at hdup
  have href := digamma_three_quarters_sub_quarter
  linear_combination -(hdup + href) / 2

end

end GaloisForLFunctions.SeamSplit

namespace GaloisForLFunctions.SeamSplit

open Complex GaloisForLFunctions GaloisForLFunctions.VorosClosedForm

noncomputable section

/-! ## The archimedean and prime summands -/

/-- The archimedean summand of the completed logarithmic derivative. -/
def archSummand (s : ℂ) : ℂ :=
  1 / s + 1 / (s - 1) + (-(Real.log Real.pi : ℂ) / 2 + Complex.digamma (s / 2) / 2)

/-- The prime summand of the completed logarithmic derivative. -/
def primeSummand (s : ℂ) : ℂ := logDeriv riemannZeta s

theorem logDeriv_xiFun_split {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hpoles : ∀ n : ℕ, s / 2 ≠ -(n : ℂ)) (hz : riemannZeta s ≠ 0) :
    logDeriv xiFun s = archSummand s + primeSummand s := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have helem : elemFactor s ≠ 0 := by
    rw [elemFactor]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hs0) hsub
  have hG : Complex.Gammaℝ s ≠ 0 := GammaR_ne_zero hpoles
  have hdE : DifferentiableAt ℂ elemFactor s := by
    have : DifferentiableAt ℂ (fun z : ℂ => (1 / 2 : ℂ) * z * (z - 1)) s :=
      (differentiableAt_id.const_mul _).mul (differentiableAt_id.sub_const 1)
    exact this
  have hdG : DifferentiableAt ℂ Complex.Gammaℝ s := differentiableAt_GammaR hpoles
  have hdZ : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hxi : xiFun = fun z : ℂ => elemFactor z * (Complex.Gammaℝ z * riemannZeta z) := rfl
  have hprodne : Complex.Gammaℝ s * riemannZeta s ≠ 0 := mul_ne_zero hG hz
  have step1 : logDeriv (fun z : ℂ => elemFactor z * (Complex.Gammaℝ z * riemannZeta z)) s
      = logDeriv elemFactor s
        + logDeriv (fun z : ℂ => Complex.Gammaℝ z * riemannZeta z) s :=
    logDeriv_mul s helem hprodne hdE (hdG.mul hdZ)
  have step2 : logDeriv (fun z : ℂ => Complex.Gammaℝ z * riemannZeta z) s
      = logDeriv Complex.Gammaℝ s + logDeriv riemannZeta s :=
    logDeriv_mul s hG hz hdG hdZ
  rw [hxi, step1, step2, logDeriv_elemFactor hs0 hs1,
    BohrGeneratorAxis.logDeriv_GammaR s hpoles, archSummand, primeSummand]
  ring

/-! ## The functional equation -/

theorem xiFun_eq_elem_mul_completed {s : ℂ} (hs0 : s ≠ 0) (hG : Complex.Gammaℝ s ≠ 0) :
    xiFun s = elemFactor s * completedRiemannZeta s := by
  rw [xiFun, riemannZeta_def_of_ne_zero hs0]
  field_simp

theorem GammaR_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : Complex.Gammaℝ s ≠ 0 := by
  have hhalf : 0 < (s / 2).re := by
    rw [show s / 2 = (2 : ℂ)⁻¹ * s by ring, Complex.mul_re]
    norm_num
    linarith
  exact GammaR_ne_zero (offPoles_of_re_pos hhalf)

/-- **The functional equation for `ξ`.** -/
theorem xiFun_one_sub {s : ℂ} (hs0 : 0 < s.re) (hs1 : 0 < (1 - s).re) :
    xiFun (1 - s) = xiFun s := by
  have hsne : s ≠ 0 := by
    intro h
    rw [h] at hs0
    simp at hs0
  have h1sne : (1 - s) ≠ 0 := by
    intro h
    rw [h] at hs1
    simp at hs1
  rw [xiFun_eq_elem_mul_completed h1sne (GammaR_ne_zero_of_re_pos hs1),
    xiFun_eq_elem_mul_completed hsne (GammaR_ne_zero_of_re_pos hs0),
    completedRiemannZeta_one_sub]
  congr 1
  rw [elemFactor, elemFactor]
  ring

end

end GaloisForLFunctions.SeamSplit

namespace GaloisForLFunctions.SeamSplit

open Complex Filter Topology GaloisForLFunctions GaloisForLFunctions.VorosClosedForm

noncomputable section

/-- The seam-centred completed function `Ξ(w) = ξ(1/2 + w)`. -/
def Xi (w : ℂ) : ℂ := xiFun (1 / 2 + w)

theorem seamDomain_isOpen : IsOpen {w : ℂ | |w.re| < 1 / 2} := by
  refine isOpen_lt ?_ continuous_const
  fun_prop

theorem re_pos_of_seam {w : ℂ} (hw : |w.re| < 1 / 2) : 0 < ((1 : ℂ) / 2 + w).re := by
  have h := (abs_lt.mp hw).1
  simp only [Complex.add_re, Complex.div_re]
  norm_num
  linarith

theorem re_pos_of_seam' {w : ℂ} (hw : |w.re| < 1 / 2) : 0 < ((1 : ℂ) - (1 / 2 + w)).re := by
  have h := (abs_lt.mp hw).2
  simp only [Complex.sub_re, Complex.add_re, Complex.div_re, Complex.one_re]
  norm_num
  linarith

/-- **`Ξ` is even.**  This is the functional equation in seam coordinates. -/
theorem Xi_even {w : ℂ} (hw : |w.re| < 1 / 2) : Xi (-w) = Xi w := by
  have hneg : |(-w).re| < 1 / 2 := by
    rw [Complex.neg_re, abs_neg]
    exact hw
  have hEq : (1 : ℂ) / 2 + -w = 1 - (1 / 2 + w) := by ring
  rw [Xi, Xi, hEq]
  exact xiFun_one_sub (re_pos_of_seam hw) (re_pos_of_seam' hw)

theorem analyticAt_xiFun {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) : AnalyticAt ℂ xiFun s := by
  have hhalf : 0 < (s / 2).re := by
    rw [show s / 2 = (2 : ℂ)⁻¹ * s by ring, Complex.mul_re]
    norm_num
    linarith
  have hpoles : ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := offPoles_of_re_pos hhalf
  have hE : AnalyticAt ℂ elemFactor s := by
    have : AnalyticAt ℂ (fun z : ℂ => (1 / 2 : ℂ) * z * (z - 1)) s :=
      ((analyticAt_const).mul analyticAt_id).mul (analyticAt_id.sub analyticAt_const)
    exact this
  have hG : AnalyticAt ℂ Complex.Gammaℝ s := by
    have hopenR : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hdiffR : DifferentiableOn ℂ Complex.Gammaℝ {z : ℂ | 0 < z.re} := by
      intro z hz
      have hzre : 0 < z.re := hz
      have hzh : 0 < (z / 2).re := by
        rw [show z / 2 = (2 : ℂ)⁻¹ * z by ring, Complex.mul_re]
        norm_num
        linarith
      exact (differentiableAt_GammaR (offPoles_of_re_pos hzh)).differentiableWithinAt
    exact hdiffR.analyticOnNhd hopenR s hs
  have hZ : AnalyticAt ℂ riemannZeta s := by
    have hopen : IsOpen {z : ℂ | z ≠ 1} := isOpen_ne
    have hdiff : DifferentiableOn ℂ riemannZeta {z : ℂ | z ≠ 1} := fun z hz =>
      (differentiableAt_riemannZeta hz).differentiableWithinAt
    exact hdiff.analyticOnNhd hopen s hs1
  exact hE.mul (hG.mul hZ)

theorem xiFun_half_ne_zero : xiFun (1 / 2 : ℂ) ≠ 0 := by
  have hz : riemannZeta ((1 : ℂ) / 2) ≠ 0 := by
    have h := RHTower.riemannZeta_real_strip_ne_zero (σ := 1 / 2) (by norm_num) (by norm_num)
    simpa using h
  have hre : (0 : ℝ) < ((1 : ℂ) / 2).re := by norm_num
  have hG : Complex.Gammaℝ ((1 : ℂ) / 2) ≠ 0 := GammaR_ne_zero_of_re_pos hre
  rw [xiFun]
  refine mul_ne_zero ?_ (mul_ne_zero hG hz)
  rw [elemFactor]
  norm_num

end

end GaloisForLFunctions.SeamSplit

namespace GaloisForLFunctions.SeamSplit

open Complex Filter Topology GaloisForLFunctions GaloisForLFunctions.VorosClosedForm

noncomputable section

theorem analyticAt_xiFun_half : AnalyticAt ℂ xiFun (1 / 2 : ℂ) := by
  refine analyticAt_xiFun (by norm_num) ?_
  intro h
  have := congrArg Complex.re h
  norm_num at this

theorem hasDerivAt_Xi_zero : HasDerivAt Xi (deriv xiFun (1 / 2 : ℂ)) 0 := by
  have haff : HasDerivAt (fun w : ℂ => (1 / 2 : ℂ) + w) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_add (1 / 2 : ℂ)
  have hx : HasDerivAt xiFun (deriv xiFun ((1 : ℂ) / 2)) ((fun w : ℂ => (1 / 2 : ℂ) + w) 0) := by
    rw [show ((fun w : ℂ => (1 / 2 : ℂ) + w) 0) = (1 / 2 : ℂ) by ring]
    exact analyticAt_xiFun_half.differentiableAt.hasDerivAt
  have h := HasDerivAt.comp (0 : ℂ) hx haff
  rw [mul_one] at h
  exact h

/-- **The seam value of the completed logarithmic derivative vanishes.**  `Ξ` is even, so its
logarithmic derivative is odd and vanishes at the seam. -/
theorem deriv_xiFun_half : deriv xiFun (1 / 2 : ℂ) = 0 := by
  have hXd : HasDerivAt Xi (deriv xiFun (1 / 2 : ℂ)) 0 := hasDerivAt_Xi_zero
  have hneg : HasDerivAt (fun w : ℂ => Xi (-w)) (-deriv xiFun (1 / 2 : ℂ)) 0 := by
    have hn : HasDerivAt (fun w : ℂ => -w) (-1 : ℂ) 0 := hasDerivAt_neg 0
    have hx : HasDerivAt Xi (deriv xiFun (1 / 2 : ℂ)) ((fun w : ℂ => -w) 0) := by
      simp only [neg_zero]
      exact hXd
    have h := HasDerivAt.comp (0 : ℂ) hx hn
    rw [mul_neg_one] at h
    exact h
  have hev : (fun w : ℂ => Xi (-w)) =ᶠ[nhds 0] Xi := by
    filter_upwards [seamDomain_isOpen.mem_nhds (by norm_num : |(0 : ℂ).re| < 1 / 2)] with w hw
    exact Xi_even hw
  have heq := hneg.congr_of_eventuallyEq hev.symm
  have hdd := hXd.unique heq
  linear_combination hdd / 2

theorem logDeriv_xiFun_half : logDeriv xiFun (1 / 2 : ℂ) = 0 := by
  rw [logDeriv_apply, deriv_xiFun_half, zero_div]

/-! ## The seam residues -/

theorem archSummand_half :
    archSummand (1 / 2 : ℂ)
      = (Complex.digamma (1 / 4 : ℂ) - (Real.log Real.pi : ℂ)) / 2 := by
  rw [archSummand, show ((1 : ℂ) / 2) / 2 = 1 / 4 by ring]
  norm_num
  ring

theorem complex_log_two : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
  have h := Complex.ofReal_log (x := (2 : ℝ)) (by norm_num)
  rw [show (((2 : ℝ) : ℂ)) = (2 : ℂ) by norm_num] at h
  exact h.symm

/-- **The seam residue of the archimedean summand**, in closed form. -/
theorem archSummand_half_real :
    archSummand (1 / 2 : ℂ)
      = ((-(Real.eulerMascheroniConstant + Real.pi / 2 + 3 * Real.log 2 + Real.log Real.pi) / 2
          : ℝ) : ℂ) := by
  rw [archSummand_half, digamma_one_quarter, complex_log_two]
  push_cast
  ring

theorem archSummand_half_ne_zero : archSummand (1 / 2 : ℂ) ≠ 0 := by
  rw [archSummand_half_real]
  rw [Complex.ofReal_ne_zero]
  have hγ : (1 : ℝ) / 2 < Real.eulerMascheroniConstant := Real.one_half_lt_eulerMascheroniConstant
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlπ : (0 : ℝ) < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  intro h
  have hpos : (0 : ℝ)
      < Real.eulerMascheroniConstant + Real.pi / 2 + 3 * Real.log 2 + Real.log Real.pi := by
    linarith
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · rw [neg_eq_zero] at h
    linarith
  · norm_num at h

/-- **The functional-equation cancellation.**  The prime summand's seam residue is the exact
negative of the archimedean one. -/
theorem primeSummand_half : primeSummand (1 / 2 : ℂ) = -archSummand (1 / 2 : ℂ) := by
  have hz : riemannZeta ((1 : ℂ) / 2) ≠ 0 := by
    have h := RHTower.riemannZeta_real_strip_ne_zero (σ := 1 / 2) (by norm_num) (by norm_num)
    simpa using h
  have hpoles : ∀ n : ℕ, ((1 : ℂ) / 2) / 2 ≠ -(n : ℂ) := by
    refine offPoles_of_re_pos ?_
    norm_num
  have hs1 : ((1 : ℂ) / 2) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hsplit := logDeriv_xiFun_split (s := (1 : ℂ) / 2) (by norm_num) hs1 hpoles hz
  rw [logDeriv_xiFun_half] at hsplit
  linear_combination -hsplit

theorem primeSummand_half_ne_zero : primeSummand (1 / 2 : ℂ) ≠ 0 := by
  rw [primeSummand_half, neg_ne_zero]
  exact archSummand_half_ne_zero

end

end GaloisForLFunctions.SeamSplit

namespace GaloisForLFunctions.SeamSplit

open Complex Filter Topology GaloisForLFunctions GaloisForLFunctions.VorosClosedForm

noncomputable section

theorem continuousAt_archSummand_half : ContinuousAt archSummand (1 / 2 : ℂ) := by
  have hs0 : ((1 : ℂ) / 2) ≠ 0 := by norm_num
  have hs1 : ((1 : ℂ) / 2) - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hdig : ContinuousAt (fun z : ℂ => Complex.digamma (z / 2) / 2) (1 / 2 : ℂ) := by
    have haff : ContinuousAt (fun z : ℂ => z / 2) (1 / 2 : ℂ) := (continuous_id.div_const 2).continuousAt
    have hval : ((fun z : ℂ => z / 2) (1 / 2 : ℂ)) = 1 / 4 := by norm_num
    have hd : ContinuousAt Complex.digamma ((fun z : ℂ => z / 2) (1 / 2 : ℂ)) := by
      rw [hval]
      exact (contDiffAt_digamma_top (offPoles_of_re_pos (by norm_num))).continuousAt
    exact (ContinuousAt.comp (g := Complex.digamma) (f := fun z : ℂ => z / 2) hd haff).div_const 2
  have h1 : ContinuousAt (fun z : ℂ => 1 / z) (1 / 2 : ℂ) := (continuousAt_const).div continuousAt_id hs0
  have h2 : ContinuousAt (fun z : ℂ => 1 / (z - 1)) (1 / 2 : ℂ) :=
    (continuousAt_const).div (continuousAt_id.sub continuousAt_const) hs1
  exact (h1.add h2).add ((continuousAt_const).add hdig)

theorem continuousAt_primeSummand_half : ContinuousAt primeSummand (1 / 2 : ℂ) := by
  have hz : riemannZeta ((1 : ℂ) / 2) ≠ 0 := by
    have h := RHTower.riemannZeta_real_strip_ne_zero (σ := 1 / 2) (by norm_num) (by norm_num)
    simpa using h
  have hs1 : ((1 : ℂ) / 2) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hZ : AnalyticAt ℂ riemannZeta (1 / 2 : ℂ) := by
    have hopen : IsOpen {z : ℂ | z ≠ 1} := isOpen_ne
    have hdiff : DifferentiableOn ℂ riemannZeta {z : ℂ | z ≠ 1} := fun z hz' =>
      (differentiableAt_riemannZeta hz').differentiableWithinAt
    exact hdiff.analyticOnNhd hopen _ hs1
  have hq : AnalyticAt ℂ (fun s : ℂ => deriv riemannZeta s / riemannZeta s) (1 / 2 : ℂ) :=
    hZ.deriv.div hZ hz
  exact hq.continuousAt

theorem residue_of_continuousAt {f : ℂ → ℂ} {c : ℂ} (hf : ContinuousAt f c) :
    Tendsto (fun w : ℂ => w * (f (c + w) / w)) (𝓝[≠] 0) (𝓝 (f c)) := by
  have hshift : Tendsto (fun w : ℂ => f (c + w)) (𝓝[≠] 0) (𝓝 (f c)) := by
    have hc : Tendsto (fun w : ℂ => c + w) (𝓝[≠] (0 : ℂ)) (𝓝 c) := by
      have hcont : ContinuousAt (fun w : ℂ => c + w) 0 :=
        (continuousAt_const).add continuousAt_id
      have htend : Tendsto (fun w : ℂ => c + w) (𝓝 (0 : ℂ)) (𝓝 (c + 0)) := hcont.tendsto
      rw [add_zero] at htend
      exact htend.mono_left nhdsWithin_le_nhds
    exact hf.tendsto.comp hc
  refine hshift.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  rw [mul_div_cancel₀ _ (by simpa using hw)]

/-- **The divided archimedean summand has a simple pole at the seam with residue `A(1/2)`.** -/
theorem residue_archSummand :
    Tendsto (fun w : ℂ => w * (archSummand (1 / 2 + w) / w)) (𝓝[≠] 0)
      (𝓝 (archSummand (1 / 2 : ℂ))) :=
  residue_of_continuousAt continuousAt_archSummand_half

/-- **The divided prime summand has a simple pole at the seam with the opposite residue.** -/
theorem residue_primeSummand :
    Tendsto (fun w : ℂ => w * (primeSummand (1 / 2 + w) / w)) (𝓝[≠] 0)
      (𝓝 (-archSummand (1 / 2 : ℂ))) := by
  rw [← primeSummand_half]
  exact residue_of_continuousAt continuousAt_primeSummand_half

/-- **The divided completed sum has no pole at the seam: the residues cancel.** -/
theorem residue_sum :
    Tendsto (fun w : ℂ => w * ((archSummand (1 / 2 + w) + primeSummand (1 / 2 + w)) / w))
      (𝓝[≠] 0) (𝓝 0) := by
  have h := residue_of_continuousAt (continuousAt_archSummand_half.add continuousAt_primeSummand_half)
  have hval : (archSummand + primeSummand) (1 / 2 : ℂ) = 0 := by
    show archSummand (1 / 2 : ℂ) + primeSummand (1 / 2 : ℂ) = 0
    rw [primeSummand_half]
    ring
  rw [hval] at h
  exact h

/-- **Seam division: the source split requires the functional-equation cancellation.**

The completed quotient is regular at the seam, but each source summand divided by the seam
coordinate has a *nonzero* simple pole there, and the two residues are exact negatives. -/
theorem seam_division_source_split :
    archSummand (1 / 2 : ℂ) ≠ 0 ∧
      primeSummand (1 / 2 : ℂ) ≠ 0 ∧
      primeSummand (1 / 2 : ℂ) = -archSummand (1 / 2 : ℂ) ∧
      archSummand (1 / 2 : ℂ) + primeSummand (1 / 2 : ℂ) = 0 ∧
      archSummand (1 / 2 : ℂ)
        = ((-(Real.eulerMascheroniConstant + Real.pi / 2 + 3 * Real.log 2 + Real.log Real.pi) / 2
            : ℝ) : ℂ) := by
  refine ⟨archSummand_half_ne_zero, primeSummand_half_ne_zero, primeSummand_half, ?_,
    archSummand_half_real⟩
  rw [primeSummand_half]
  ring

end

end GaloisForLFunctions.SeamSplit
