import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCompletedDensityTransversePick
import GaloisForLFunctions.RHTower.EulerTailWinding
import GaloisForLFunctions.HTGeometry.AffineSimpleZeroMotion

/-!
# Signed winding and critical-zero ejection for the completed-density affine pencil

A full signed phase turn, unlike an unsigned real-axis collision, forces a positive incidence
parameter and hence a zero of the source-to-Xi affine pencil. More decisively, the pencil cannot
be upper-half-plane zero-free throughout the homotopy: at every positive simple real Xi zero with
negative slope, the analytic implicit-function branch has exact velocity

g'(0) = -E(t) / (2 t^2 XiC'(t)).

It enters the open upper half-plane for positive pencil parameter. This is a local structural
obstruction; no estimate at infinity is involved. All results are unconditional implications
from their displayed hypotheses.
-/

namespace RHTower

open Complex Metric Filter Topology Set

noncomputable section

theorem exists_positive_real_of_two_pi_phase_advance
    {F : ℝ → ℂ} {R θ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hR : ∀ τ ∈ Set.Icc a b, 0 < R τ)
    (hpolar : ∀ τ ∈ Set.Icc a b,
      F τ = (R τ : ℂ) * Complex.exp ((θ τ : ℝ) * I))
    (hθc : ContinuousOn θ (Set.Icc a b))
    (hadv : θ a + 2 * Real.pi ≤ θ b) :
    ∃ τ ∈ Set.Icc a b, 0 < (F τ).re ∧ (F τ).im = 0 := by
  have h2π : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  obtain ⟨k, hk1, hk2⟩ :
      ∃ k : ℤ, θ a ≤ (k : ℝ) * (2 * Real.pi) ∧
        (k : ℝ) * (2 * Real.pi) ≤ θ b := by
    refine ⟨⌈θ a / (2 * Real.pi)⌉, ?_, ?_⟩
    · calc
        θ a = (θ a / (2 * Real.pi)) * (2 * Real.pi) := by field_simp
        _ ≤ (⌈θ a / (2 * Real.pi)⌉ : ℝ) * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_right (Int.le_ceil _) h2π.le
    · calc
        (⌈θ a / (2 * Real.pi)⌉ : ℝ) * (2 * Real.pi) ≤
            (θ a / (2 * Real.pi) + 1) * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_right (Int.ceil_lt_add_one _).le h2π.le
        _ = θ a + 2 * Real.pi := by field_simp
        _ ≤ θ b := hadv
  obtain ⟨σ, hσ, hθσ⟩ :=
    intermediate_value_Icc hab hθc (Set.mem_Icc.mpr ⟨hk1, hk2⟩)
  have hexp : Complex.exp ((θ σ : ℝ) * I) = 1 := by
    rw [hθσ]
    simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_ofNat_Int,
      Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_ofNat,
      mul_assoc] using Complex.exp_int_mul_two_pi_mul_I k
  refine ⟨σ, hσ, ?_, ?_⟩
  · rw [hpolar σ hσ, hexp, mul_one]
    simpa using hR σ hσ
  · rw [hpolar σ hσ, hexp, mul_one]
    simp

theorem exists_positive_incidence_of_two_pi_phase_advance
    {Λ₁ Λ₂ : ℂ → ℂ} {γ : ℝ → ℂ} {R θ : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hR : ∀ τ ∈ Set.Icc a b, 0 < R τ)
    (hpolar : ∀ τ ∈ Set.Icc a b,
      incidence Λ₁ Λ₂ (γ τ) = (R τ : ℂ) * Complex.exp ((θ τ : ℝ) * I))
    (hθc : ContinuousOn θ (Set.Icc a b))
    (hadv : θ a + 2 * Real.pi ≤ θ b) :
    ∃ τ ∈ Set.Icc a b,
      0 < (incidence Λ₁ Λ₂ (γ τ)).re ∧
      (incidence Λ₁ Λ₂ (γ τ)).im = 0 := by
  exact exists_positive_real_of_two_pi_phase_advance hab hR hpolar hθc hadv

theorem thetaCuspTailSecondDensityDeBrangesAffinePencil_eq_tau_E_add_center
    {tau : ℝ} {z : ℂ} (hz : |z.im| < 1) :
    thetaCuspTailSecondDensityDeBrangesAffinePencil tau z =
      (tau : ℂ) * thetaCuspTailSecondDensityDeBrangesE z +
        ((1 - tau : ℝ) : ℂ) * (2 * z ^ 2 * XiC z) := by
  rw [← thetaCuspTailSecondDensityDeBrangesAffinePencil_zero hz]
  unfold thetaCuspTailSecondDensityDeBrangesAffinePencil
  push_cast
  ring

theorem thetaCuspTailSecondDensityDeBrangesAffinePencil_zero_of_positive_incidence
    {z : ℂ} (hzstrip : |z.im| < 1)
    (hinc : 0 < (incidence thetaCuspTailSecondDensityDeBrangesE
      (fun w => 2 * w ^ 2 * XiC w) z).re)
    (him : (incidence thetaCuspTailSecondDensityDeBrangesE
      (fun w => 2 * w ^ 2 * XiC w) z).im = 0) :
    ∃ tau : ℝ, tau ∈ Set.Ioo 0 1 ∧
      thetaCuspTailSecondDensityDeBrangesAffinePencil tau z = 0 := by
  let c : ℝ := (incidence thetaCuspTailSecondDensityDeBrangesE
    (fun w => 2 * w ^ 2 * XiC w) z).re
  let tau : ℝ := c / (1 + c)
  have hc : 0 < c := hinc
  have honec : 0 < 1 + c := by linarith
  have htau0 : 0 < tau := div_pos hc honec
  have htau1 : tau < 1 := (div_lt_one honec).2 (by linarith)
  have hincReal : incidence thetaCuspTailSecondDensityDeBrangesE
      (fun w => 2 * w ^ 2 * XiC w) z = (c : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa [c] using him
  have hE : thetaCuspTailSecondDensityDeBrangesE z ≠ 0 := by
    intro hzero
    unfold incidence at hincReal
    rw [hzero, div_zero] at hincReal
    have := congrArg Complex.re hincReal
    simp [c] at this
    linarith
  have hrelation : (c : ℂ) * thetaCuspTailSecondDensityDeBrangesE z +
      2 * z ^ 2 * XiC z = 0 := by
    have hdiv : -(2 * z ^ 2 * XiC z) /
        thetaCuspTailSecondDensityDeBrangesE z = (c : ℂ) := by
      simpa [incidence] using hincReal
    rw [div_eq_iff hE] at hdiv
    linear_combination -hdiv
  refine ⟨tau, ⟨htau0, htau1⟩, ?_⟩
  rw [thetaCuspTailSecondDensityDeBrangesAffinePencil_eq_tau_E_add_center hzstrip]
  have htau : (tau : ℂ) = ((1 - tau : ℝ) : ℂ) * (c : ℂ) := by
    have htauR : tau = (1 - tau) * c := by
      dsimp [tau]
      field_simp
      ring
    exact_mod_cast htauR
  rw [htau]
  linear_combination ((1 - tau : ℝ) : ℂ) * hrelation

/-- A signed full turn of the actual incidence map forces a zero of the completed-density affine
pencil with parameter strictly between its Xi center and zero-free endpoint. -/
theorem exists_thetaCuspTailSecondDensityDeBrangesAffinePencil_zero_of_two_pi_incidence_advance
    {gamma : ℝ → ℂ} {R theta : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hstrip : ∀ u ∈ Set.Icc a b, |(gamma u).im| < 1)
    (hR : ∀ u ∈ Set.Icc a b, 0 < R u)
    (hpolar : ∀ u ∈ Set.Icc a b,
      incidence thetaCuspTailSecondDensityDeBrangesE
          (fun w => 2 * w ^ 2 * XiC w) (gamma u) =
        (R u : ℂ) * Complex.exp ((theta u : ℝ) * I))
    (htheta : ContinuousOn theta (Set.Icc a b))
    (hadvance : theta a + 2 * Real.pi ≤ theta b) :
    ∃ u ∈ Set.Icc a b, ∃ tau ∈ Set.Ioo (0 : ℝ) 1,
      thetaCuspTailSecondDensityDeBrangesAffinePencil tau (gamma u) = 0 := by
  obtain ⟨u, hu, hre, him⟩ :=
    exists_positive_incidence_of_two_pi_phase_advance hab hR hpolar htheta hadvance
  obtain ⟨tau, htau, hzero⟩ :=
    thetaCuspTailSecondDensityDeBrangesAffinePencil_zero_of_positive_incidence
      (hstrip u hu) hre him
  exact ⟨u, hu, tau, htau, hzero⟩

/-- The complex incidence parameter whose zero set is the affine source-to-Xi pencil after
the real reparametrization `tau = c / (1 + c)`. -/
def thetaCuspTailSecondDensityDeBrangesIncidencePencil (c z : ℂ) : ℂ :=
  c * thetaCuspTailSecondDensityDeBrangesE z + 2 * z ^ 2 * XiC z

theorem thetaCuspTailSecondDensityDeBrangesAffinePencil_zero_of_incidenceParameter
    {c : ℝ} {z : ℂ} (hc : 0 < c) (hzstrip : |z.im| < 1)
    (hzero : thetaCuspTailSecondDensityDeBrangesIncidencePencil (c : ℂ) z = 0) :
    c / (1 + c) ∈ Set.Ioo (0 : ℝ) 1 ∧
      thetaCuspTailSecondDensityDeBrangesAffinePencil (c / (1 + c)) z = 0 := by
  have hden : 0 < 1 + c := by linarith
  have htau0 : 0 < c / (1 + c) := div_pos hc hden
  have htau1 : c / (1 + c) < 1 := (div_lt_one hden).2 (by linarith)
  refine ⟨⟨htau0, htau1⟩, ?_⟩
  rw [thetaCuspTailSecondDensityDeBrangesAffinePencil_eq_tau_E_add_center hzstrip]
  have hone : (1 - c / (1 + c) : ℝ) = 1 / (1 + c) := by
    field_simp
    ring
  rw [hone]
  push_cast
  unfold thetaCuspTailSecondDensityDeBrangesIncidencePencil at hzero
  calc
    ↑c / (1 + ↑c) * thetaCuspTailSecondDensityDeBrangesE z +
          (1 / (1 + ↑c)) * (2 * z ^ 2 * XiC z) =
        (↑c * thetaCuspTailSecondDensityDeBrangesE z + 2 * z ^ 2 * XiC z) /
          (1 + ↑c) := by ring
    _ = 0 := by rw [hzero]; simp

theorem analyticAt_thetaCuspTailSecondDensityDeBrangesE_ofReal (t : ℝ) :
    AnalyticAt ℂ thetaCuspTailSecondDensityDeBrangesE (t : ℂ) := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have hnhds : {z : ℂ | -1 < z.im} ∈ 𝓝 (t : ℂ) := by
    exact isOpen_lt continuous_const Complex.continuous_im |>.mem_nhds (by simp)
  filter_upwards [hnhds] with z hz
  exact (hasDerivAt_thetaCuspTailSecondDensityDeBrangesE hz).differentiableAt

/-- A positive real Xi zero with negative simple slope launches a local analytic zero branch of
the incidence pencil into the open upper half-plane.  The displayed derivative is the exact
normal velocity. -/
theorem exists_affinePencil_zero_branch_ejected_upper_of_deriv_re_neg
    {t : ℝ} (ht : 0 < t) (hz : XiC (t : ℂ) = 0)
    (hXi' : (deriv XiC (t : ℂ)).re < 0) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g 0 ∧
      g 0 = (t : ℂ) ∧
      HasDerivAt g
        (-thetaCuspTailSecondDensityDeBrangesE (t : ℂ) /
          (2 * (t : ℂ) ^ 2 * deriv XiC (t : ℂ))) 0 ∧
      ∀ᶠ c : ℝ in 𝓝[>] 0,
        0 < (g (c : ℂ)).im ∧
        |(g (c : ℂ)).im| < 1 ∧
        c / (1 + c) ∈ Set.Ioo (0 : ℝ) 1 ∧
        thetaCuspTailSecondDensityDeBrangesAffinePencil
          (c / (1 + c)) (g (c : ℂ)) = 0 := by
  let E := thetaCuspTailSecondDensityDeBrangesE
  let X := deriv XiC (t : ℂ)
  let D : ℂ := 2 * (t : ℂ) ^ 2 * X
  let V : ℂ := -E (t : ℂ) / D
  let H : ℂ → ℂ := fun z => 2 * z ^ 2 * XiC z
  have hXine : X ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [X] at this
    linarith
  have hDne : D ≠ 0 := by
    dsimp [D]
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr ht.ne'))) hXine
  have hEan : AnalyticAt ℂ E (t : ℂ) :=
    analyticAt_thetaCuspTailSecondDensityDeBrangesE_ofReal t
  have hHan : AnalyticAt ℂ H (t : ℂ) := by
    have htwo : AnalyticAt ℂ (fun _ : ℂ => (2 : ℂ)) (t : ℂ) := analyticAt_const
    have hprod := htwo.mul
      ((analyticAt_id.pow 2).mul (XiC_analytic (t : ℂ) (Set.mem_univ _)))
    have hfun : H = fun z : ℂ => (2 : ℂ) * (z ^ 2 * XiC z) := by
      funext z
      show 2 * z ^ 2 * XiC z = 2 * (z ^ 2 * XiC z)
      ring
    rw [hfun]
    exact hprod
  have hHroot : H (t : ℂ) = 0 := by simp [H, hz]
  have hXiDer : HasDerivAt XiC X (t : ℂ) := by
    simpa [X] using (XiC_analytic (t : ℂ) (Set.mem_univ _)).differentiableAt.hasDerivAt
  have hHder : HasDerivAt H D (t : ℂ) := by
    have hprod := ((hasDerivAt_id (t : ℂ)).pow 2).mul hXiDer
    have hscaled := hprod.const_mul (2 : ℂ)
    have hfun : H = fun w : ℂ => (2 : ℂ) * (w ^ 2 * XiC w) := by
      funext w
      show 2 * w ^ 2 * XiC w = 2 * (w ^ 2 * XiC w)
      ring
    rw [hfun]
    exact hscaled.congr_deriv (by simp [D, hz]; ring)
  have hHderiv : deriv H (t : ℂ) = D := hHder.deriv
  have hHsimple : deriv H (t : ℂ) ≠ 0 := by rw [hHderiv]; exact hDne
  obtain ⟨g, hgan, hg0, hrelH, hgV0⟩ :=
    HTGeometry.exists_affineSimpleZero_branch hHan hEan hHroot hHsimple
  have hrel : ∀ᶠ c : ℂ in 𝓝 0,
      thetaCuspTailSecondDensityDeBrangesIncidencePencil c (g c) = 0 := by
    filter_upwards [hrelH] with c hc
    simpa [thetaCuspTailSecondDensityDeBrangesIncidencePencil, H, E, add_comm] using hc
  have hgV : HasDerivAt g V 0 := by
    rw [hHderiv] at hgV0
    simpa [V] using hgV0
  have hconj := deriv_XiC_conj (t : ℂ)
  simp only [conj_ofReal] at hconj
  have hXiim : X.im = 0 := by
    have him := congrArg Complex.im hconj
    simp only [conj_im] at him
    dsimp [X]
    linarith
  have hEre := thetaCuspTailSecondDensityDeBrangesE_re_ofReal_eq_zero hz
  have hEim := thetaCuspTailSecondDensityDeBrangesE_im_ofReal_pos ht
  have hVim : 0 < V.im := by
    have hXeq : X = (X.re : ℂ) := by
      apply Complex.ext <;> simp [hXiim]
    have hEeq : E (t : ℂ) = I * ((E (t : ℂ)).im : ℂ) := by
      apply Complex.ext <;> simp [E, hEre]
    have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
    have hdenneg : 2 * t ^ 2 * X.re < 0 :=
      mul_neg_of_pos_of_neg (mul_pos (by norm_num) ht2) hXi'
    have hdenne : 2 * t ^ 2 * X.re ≠ 0 := hdenneg.ne
    have hDeq : D = ((2 * t ^ 2 * X.re : ℝ) : ℂ) := by
      dsimp [D]
      rw [hXeq]
      norm_num
    have hVimEq : V.im = -(E (t : ℂ)).im / (2 * t ^ 2 * X.re) := by
      dsimp [V]
      rw [hDeq, Complex.div_ofReal_im]
      simp
    rw [hVimEq]
    exact div_pos_of_neg_of_neg (neg_neg_of_pos hEim)
      hdenneg
  have hgReal : HasDerivAt (fun c : ℝ => g (c : ℂ)) V 0 := hgV.comp_ofReal
  have himDer : HasDerivAt (fun c : ℝ => (g (c : ℂ)).im) V.im 0 :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hgReal
  have hposSlope : ∀ᶠ c : ℝ in 𝓝[>] 0,
      0 < c⁻¹ * ((g ((0 + c : ℝ) : ℂ)).im - (g (0 : ℂ)).im) := by
    have hlim := himDer.tendsto_slope_zero_right
    simpa only [smul_eq_mul, Complex.ofReal_zero] using
      hlim.eventually (Ioi_mem_nhds hVim)
  have hpos : ∀ᶠ c : ℝ in 𝓝[>] 0, 0 < (g (c : ℂ)).im := by
    filter_upwards [self_mem_nhdsWithin, hposSlope] with c hc hslope
    have hcpos : 0 < c := hc
    have hg0im : (g (0 : ℂ)).im = 0 := by rw [hg0]; simp
    rw [zero_add, hg0im, sub_zero] at hslope
    calc
      0 < c * (c⁻¹ * (g (c : ℂ)).im) := mul_pos hcpos hslope
      _ = (g (c : ℂ)).im := by field_simp [hcpos.ne']
  have hstripN : ∀ᶠ c : ℝ in 𝓝 0, |(g (c : ℂ)).im| < 1 := by
    have hcont := himDer.continuousAt
    have hzero : (g (0 : ℂ)).im = 0 := by rw [hg0]; simp
    have htend : Tendsto (fun c : ℝ => (g (c : ℂ)).im) (𝓝 0) (𝓝 0) := by
      change Tendsto (fun c : ℝ => (g (c : ℂ)).im) (𝓝 0)
        (𝓝 ((g ((0 : ℝ) : ℂ)).im)) at hcont
      simpa [hg0] using hcont
    have hball := htend.eventually
      (Metric.ball_mem_nhds (0 : ℝ) (ε := (1 : ℝ)) (by norm_num))
    simpa [Real.dist_eq] using hball
  have hstrip : ∀ᶠ c : ℝ in 𝓝[>] 0, |(g (c : ℂ)).im| < 1 :=
    hstripN.filter_mono inf_le_left
  have hrelRealN : ∀ᶠ c : ℝ in 𝓝 0,
      thetaCuspTailSecondDensityDeBrangesIncidencePencil (c : ℂ) (g (c : ℂ)) = 0 :=
    (Complex.ofRealCLM.continuous.continuousAt.tendsto.eventually hrel)
  have hrelReal : ∀ᶠ c : ℝ in 𝓝[>] 0,
      thetaCuspTailSecondDensityDeBrangesIncidencePencil (c : ℂ) (g (c : ℂ)) = 0 :=
    hrelRealN.filter_mono inf_le_left
  refine ⟨g, hgan, hg0, ?_, ?_⟩
  · simpa [V, D, E, X] using hgV
  filter_upwards [self_mem_nhdsWithin, hpos, hstrip, hrelReal] with c hc hgc hgs hrelc
  exact ⟨hgc, hgs,
    thetaCuspTailSecondDensityDeBrangesAffinePencil_zero_of_incidenceParameter
      hc hgs hrelc |>.1,
    thetaCuspTailSecondDensityDeBrangesAffinePencil_zero_of_incidenceParameter
      hc hgs hrelc |>.2⟩

/-- The proposed zero-free homotopy is locally impossible at a negative-slope positive simple Xi
zero: arbitrarily small positive parameters contain an upper-half-strip pencil zero. -/
theorem not_eventually_affinePencil_zeroFree_upper_of_deriv_re_neg
    {t : ℝ} (ht : 0 < t) (hz : XiC (t : ℂ) = 0)
    (hXi' : (deriv XiC (t : ℂ)).re < 0) :
    ¬ ∀ᶠ c : ℝ in 𝓝[>] 0, ∀ z : ℂ,
        0 < z.im → |z.im| < 1 →
          thetaCuspTailSecondDensityDeBrangesAffinePencil
            (c / (1 + c)) z ≠ 0 := by
  rintro hfree
  obtain ⟨g, _, _, _, hzero⟩ :=
    exists_affinePencil_zero_branch_ejected_upper_of_deriv_re_neg ht hz hXi'
  have hfalse : ∀ᶠ _c : ℝ in 𝓝[>] 0, False := by
    filter_upwards [hzero, hfree] with c hc hfreec
    exact (hfreec (g (c : ℂ)) hc.1 hc.2.1) hc.2.2.2
  rcases hfalse.exists with ⟨_, h⟩
  exact h

end

end RHTower
