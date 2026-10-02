import GaloisForLFunctions.RHTower.OneSignTailImpossible

/-!
# A negative real Laplace residue forbids an eventually nonnegative source

The source's compact head is retained. Landau pins the positive tail's
abscissa at the real endpoint; positivity then excludes a negative residue.
Only local analyticity along the real interval is needed. No meromorphic
continuation across its nonreal singularities is assumed.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open GaloisForLFunctions.RHTower (laplaceReal complexLaplace tailMeasure
  headLaplace complexLaplace_ofReal hasDerivAt_complexLaplace
  false_of_analyticAt_abscissa)
namespace RHTower

/-- An admitted source with a negative real residue cannot keep a nonnegative tail. -/
theorem not_eventually_nonneg_of_negative_real_laplace_residue
    {g : ℝ → ℝ} (hgc : Continuous g) {G : ℂ → ℂ}
    (hgi : ∀ σ : ℝ, 3 / 2 < σ →
      IntegrableOn (fun u : ℝ => g u * Real.exp (-σ * u)) (Ioi 0))
    (htrans : ∀ σ : ℝ, 3 / 2 < σ →
      ((∫ u in Ioi (0 : ℝ), g u * Real.exp (-σ * u) : ℝ) : ℂ) = G (σ : ℂ))
    (hGan : ∀ σ : ℝ, 1 / 4 < σ → AnalyticAt ℂ G (σ : ℂ))
    {κ : ℝ} (hκ : 0 < κ)
    (hres : Tendsto (fun σ : ℝ => (σ - 1 / 4) * (G (σ : ℂ)).re)
      (𝓝[>] (1 / 4 : ℝ)) (𝓝 (-κ))) :
    ¬ ∃ H : ℝ, ∀ u : ℝ, H < u → 0 ≤ g u := by
  rintro ⟨H₀, htail⟩
  let H : ℝ := max (max 0 H₀) (4 / κ)
  have hH : 0 ≤ H := (le_max_left 0 H₀).trans (le_max_left _ _)
  have hHH : H₀ ≤ H := (le_max_right 0 H₀).trans (le_max_left _ _)
  have hHk : 4 / κ ≤ H := le_max_right _ _
  have hlarge : 1 < κ * Real.exp (H / 4) := by
    have hdiv : 4 ≤ H * κ := (div_le_iff₀ hκ).mp hHk
    have hexp := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (H / 4)) hκ.le
    nlinarith
  have hpos : ∀ u : ℝ, 0 < u → 0 ≤ g (H + u) :=
    fun u hu => htail _ (by linarith)
  obtain ⟨c, hc, hc4, _⟩ := exists_isAbscissa_tail hgc hH hgi hpos
  let ν : Measure ℝ := tailMeasure g H
  have hΦan : ∀ σ : ℝ, 1 / 4 < σ →
      AnalyticAt ℂ (tailTransform g G H) (σ : ℂ) := by
    intro σ hσ
    apply analyticAt_tailTransform hgc hH _ (hGan σ hσ)
    intro he
    have hr := congrArg Complex.re he
    norm_num at hr
    linarith
  have hCLan : ∀ z : ℂ, c < z.re → AnalyticAt ℂ (complexLaplace ν) z := by
    intro z hz
    have hopen : IsOpen {w : ℂ | c < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hdiff : DifferentiableOn ℂ (complexLaplace ν) {w : ℂ | c < w.re} :=
      fun w hw => ((hasDerivAt_complexLaplace hc hw).differentiableAt).differentiableWithinAt
    exact hdiff.analyticAt (hopen.mem_nhds hz)
  have hray : ∀ σ : ℝ, c < σ →
      tailTransform g G H (σ : ℂ) = complexLaplace ν (σ : ℂ) := by
    have h1 : AnalyticOnNhd ℝ (fun t : ℝ => tailTransform g G H (t : ℂ)) (Ioi c) :=
      fun t ht => analyticAt_ofReal_comp (hΦan t (hc4.trans_lt ht))
    have h2 : AnalyticOnNhd ℝ (fun t : ℝ => complexLaplace ν (t : ℂ)) (Ioi c) :=
      fun t ht => analyticAt_ofReal_comp (hCLan _ (by simpa using ht))
    let z₀ : ℝ := max 2 c + 1
    have hz₀c : c < z₀ := by dsimp [z₀]; linarith [le_max_right 2 c]
    have hz₀big : 3 / 2 < z₀ := by dsimp [z₀]; linarith [le_max_left 2 c]
    have hev : (fun t : ℝ => tailTransform g G H (t : ℂ)) =ᶠ[𝓝 z₀]
        fun t : ℝ => complexLaplace ν (t : ℂ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz₀big] with t ht
      change 3 / 2 < t at ht
      rw [tailTransform_ofReal hgc hH (by linarith) (hgi t ht) hpos (htrans t ht),
        complexLaplace_ofReal]
    exact fun σ hσ => h1.eqOn_of_preconnected_of_eventuallyEq h2
      isPreconnected_Ioi hz₀c hev hσ
  have hceq : c = 1 / 4 := by
    by_contra hne
    have hcgt : 1 / 4 < c := lt_of_le_of_ne hc4 (Ne.symm hne)
    obtain ⟨δ, hδ, hball⟩ := (hΦan c hcgt).exists_ball_analyticOnNhd
    exact false_of_analyticAt_abscissa hc hδ hball
      (fun σ hσ _ => by rw [hray σ hσ, complexLaplace_ofReal])
  have hnonneg (σ : ℝ) (hσ : 1 / 4 < σ) :
      0 ≤ (σ - 1 / 4) * (tailTransform g G H (σ : ℂ)).re := by
    rw [hray σ (by rwa [hceq]), complexLaplace_ofReal, Complex.ofReal_re]
    exact mul_nonneg (by linarith) (integral_nonneg (fun _ => (Real.exp_pos _).le))
  have hreal (σ : ℝ) :
      (tailTransform g G H (σ : ℂ)).re =
        Real.exp (σ * H) * ((G (σ : ℂ)).re - (headLaplace g H (σ : ℂ)).re) +
          1 / (σ - 1 / 4) := by
    have he : Complex.exp ((σ : ℂ) * (H : ℂ)) = (Real.exp (σ * H) : ℂ) := by
      rw [Complex.ofReal_exp, Complex.ofReal_mul]
    have hd : (1 : ℂ) / ((σ : ℂ) - 1 / 4) = ((1 / (σ - 1 / 4) : ℝ) : ℂ) := by
      push_cast
      norm_num
    rw [tailTransform, he, hd]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, zero_mul, sub_zero]
  have hx : Tendsto (fun σ : ℝ => σ) (𝓝[>] (1 / 4 : ℝ)) (𝓝 (1 / 4 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hd : Tendsto (fun σ : ℝ => σ - 1 / 4) (𝓝[>] (1 / 4 : ℝ)) (𝓝 0) := by
    simpa using hx.sub_const (1 / 4 : ℝ)
  have hh : Tendsto (fun σ : ℝ => (headLaplace g H (σ : ℂ)).re)
      (𝓝[>] (1 / 4 : ℝ)) (𝓝 (headLaplace g H ((1 / 4 : ℝ) : ℂ)).re) :=
    (Complex.continuous_re.continuousAt.comp
      ((analyticAt_headLaplace hgc hH _).continuousAt.comp
        Complex.continuous_ofReal.continuousAt)).tendsto.mono_left nhdsWithin_le_nhds
  have he : Tendsto (fun σ : ℝ => Real.exp (σ * H)) (𝓝[>] (1 / 4 : ℝ))
      (𝓝 (Real.exp (H / 4))) := by
    simpa only [Function.comp_def, one_div, mul_comm (4⁻¹ : ℝ), ← div_eq_mul_inv] using
      (Real.continuous_exp.tendsto ((1 / 4 : ℝ) * H)).comp (hx.mul_const H)
  have hlim : Tendsto (fun σ : ℝ => (σ - 1 / 4) * (tailTransform g G H (σ : ℂ)).re)
      (𝓝[>] (1 / 4 : ℝ)) (𝓝 (1 - κ * Real.exp (H / 4))) := by
    have h := (he.mul (hres.sub (hd.mul hh))).add_const 1
    simp only [zero_mul, sub_zero] at h
    have hv : Real.exp (H / 4) * -κ + 1 = 1 - κ * Real.exp (H / 4) := by ring
    rw [hv] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    change 1 / 4 < σ at hσ
    rw [hreal]
    have hden : σ - 1 / 4 ≠ 0 := by linarith
    have hcancel : (σ - 1 / 4) * (1 / (σ - 1 / 4)) = 1 := by
      rw [mul_one_div, div_self hden]
    nlinarith only [hcancel]
  have hzero : 0 ≤ 1 - κ * Real.exp (H / 4) :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim (by
      filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact hnonneg σ hσ)
  linarith

end RHTower
