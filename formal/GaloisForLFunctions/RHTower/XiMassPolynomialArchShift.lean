import GaloisForLFunctions.RHTower.XiMassPolynomialArchLines

/-!
# The filtered archimedean contour shift and its uniform bound

The even polynomial weight is entire, so the exact shift of the archimedean bottom integral to the
centred real line survives it: the only crossed zero is the simple archimedean factor at `s = 1`,
and the residue picks up the filtered test at that point.  On the centred line the filtered modulus
does not depend on the vertical time, so the whole filtered archimedean channel is uniformly bounded
on every positive vertical line.
-/

open Complex Filter intervalIntegral MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-! ## Edge identifications -/

private theorem xiMassPolyArchRectangle_subset_domain
    {a c R : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hR : 0 < R) :
    (uIcc ((((-R : ℝ) : ℂ) - c * I)).re ((R : ℂ)).re ×ℂ
      uIcc ((((-R : ℝ) : ℂ) - c * I)).im ((R : ℂ)).im) ⊆
      xiMassArchShiftDomain a := by
  intro z hz
  have hre : -R ≤ z.re ∧ z.re ≤ R := by
    have := (Complex.mem_reProdIm.mp hz).1
    have hRR : -R ≤ R := by linarith
    rw [show ((((-R : ℝ) : ℂ) - c * I)).re = -R by simp [Complex.mul_re],
      show ((R : ℂ)).re = R by simp, uIcc_of_le hRR] at this
    exact this
  have him : -c ≤ z.im ∧ z.im ≤ 0 := by
    have := (Complex.mem_reProdIm.mp hz).2
    have hc0 : -c ≤ 0 := by linarith
    rw [show ((((-R : ℝ) : ℂ) - c * I)).im = -c by simp [Complex.mul_im],
      show ((R : ℂ)).im = 0 by simp, uIcc_of_le hc0] at this
    exact this
  change z ∈ xiMassStrip a ∧ z.im < 1 / 2
  refine ⟨?_, by linarith [him.2]⟩
  change |z.im| < a
  rw [abs_lt]
  constructor <;> linarith [hre.1, hre.2, him.1, him.2]

theorem xiMassPolyCenteredArchIntegrand_eq (P : Polynomial ℝ) (a : ℝ) (τ : ℂ) (x : ℝ) :
    xiMassPolyAnalyticTest P a τ (x : ℂ) *
        logDeriv archFactor (xiMassCenteredArchPoint (x : ℂ))
      = xiMassPolyCenteredArchIntegrand P a τ x := by
  rw [xiMassPolyCenteredArchIntegrand, xiMassCenteredArchIntegrand, xiMassPolyAnalyticTest]
  ring

theorem xiMassPolyArchVerticalIntegrand_def_eq (P : Polynomial ℝ) (a : ℝ) (τ : ℂ) (R y : ℝ) :
    xiMassPolyAnalyticTest P a τ ((R : ℂ) + y * I) *
        logDeriv archFactor (xiMassCenteredArchPoint ((R : ℂ) + y * I))
      = xiMassPolyArchVerticalIntegrand P a τ R y := rfl

theorem xiMassPolyArchVerticalIntegrand_neg_def_eq
    (P : Polynomial ℝ) (a : ℝ) (τ : ℂ) (R y : ℝ) :
    xiMassPolyAnalyticTest P a τ (-(R : ℂ) + y * I) *
        logDeriv archFactor (xiMassCenteredArchPoint (-(R : ℂ) + y * I))
      = xiMassPolyArchVerticalIntegrand P a τ (-R) y := by
  rw [xiMassPolyArchVerticalIntegrand, xiMassArchVerticalEulerPoint]
  norm_num

theorem xiMassPolyArchContourIntegrand_bottom_eq (P : Polynomial ℝ) (a c : ℝ) (τ : ℂ) (x : ℝ) :
    xiMassPolyAnalyticTest P a τ ((x : ℂ) - c * I) *
        logDeriv archFactor (xiMassCenteredArchPoint ((x : ℂ) - c * I))
      = xiMassPolyBottomArchIntegrand P a c τ x := by
  rw [xiMassPolyBottomArchIntegrand, xiMassBottomArchIntegrand, xiMassBottomTest,
    xiMassCenteredArchPoint_bottom_eq, xiMassPolyAnalyticTest]
  ring

theorem xiMassPolyArchContourIntegrand_bottom_add_neg_eq
    (P : Polynomial ℝ) (a c : ℝ) (τ : ℂ) (x : ℝ) :
    xiMassPolyAnalyticTest P a τ ((x : ℂ) + -(c * I)) *
        logDeriv archFactor (xiMassCenteredArchPoint ((x : ℂ) + -(c * I)))
      = xiMassPolyBottomArchIntegrand P a c τ x := by
  simpa [sub_eq_add_neg] using xiMassPolyArchContourIntegrand_bottom_eq P a c τ x

/-! ## The finite residue law -/

/-- Finite rectangle extracts exactly the crossed archimedean zero, filtered. -/
theorem rectIntegral_xiMassPoly_mul_logDeriv_centeredArchFactor (P : Polynomial ℝ)
    {a c R : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hR : 0 < R) (τ : ℂ) :
    rectIntegral
      (fun z => xiMassPolyAnalyticTest P a τ z *
        logDeriv (fun w => archFactor (xiMassCenteredArchPoint w)) z)
      (((-R : ℝ) : ℂ) - c * I) (R : ℂ) =
        2 * Real.pi * I * xiMassPolyAnalyticTest P a τ xiMassArchPole := by
  let z₁ : ℂ := (((-R : ℝ) : ℂ) - c * I)
  let z₂ : ℂ := (R : ℂ)
  let U : Set ℂ := xiMassArchShiftDomain a
  let ρ : Unit → ℂ := fun _ => xiMassArchPole
  let m : Unit → ℕ := fun _ => 1
  let h : ℂ → ℂ := xiMassCenteredArchCofactor
  have ha : 0 < a := lt_trans (lt_trans (by norm_num) hhalf) hca
  have hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U := by
    simpa only [z₁, z₂, U] using xiMassPolyArchRectangle_subset_domain hhalf hca hR
  have hin : ∀ i ∈ ({()} : Finset Unit),
      z₁.re < (ρ i).re ∧ (ρ i).re < z₂.re ∧
        z₁.im < (ρ i).im ∧ (ρ i).im < z₂.im := by
    intro i _
    have hi : i = () := Subsingleton.elim _ _
    subst i
    have hz₁re : z₁.re = -R := by simp [z₁, Complex.mul_re]
    have hz₂re : z₂.re = R := by simp [z₂]
    have hz₁im : z₁.im = -c := by simp [z₁, Complex.mul_im]
    have hz₂im : z₂.im = 0 := by simp [z₂]
    have hρre : (ρ ()).re = 0 := by simp [ρ, xiMassArchPole]
    have hρim : (ρ ()).im = -(1 / 2) := by
      norm_num [ρ, xiMassArchPole, Complex.div_im, Complex.normSq]
    rw [hz₁re, hz₂re, hz₁im, hz₂im, hρre, hρim]
    refine ⟨by linarith, hR, by linarith, by linarith⟩
  have hres := rectIntegral_mul_logDeriv_boxCount_of_analyticOnNhd
    ({()} : Finset Unit) ρ m
    (f := fun z => archFactor (xiMassCenteredArchPoint z))
    (g := xiMassPolyAnalyticTest P a τ) (h := h) (z₁ := z₁) (z₂ := z₂) (U := U)
    (isOpen_xiMassArchShiftDomain a)
    ((analyticOnNhd_xiMassPolyAnalyticTest P ha τ).mono (fun _ hz => hz.1))
    hin hsub analyticOnNhd_xiMassCenteredArchCofactor
    (fun z hz => xiMassCenteredArchCofactor_ne_zero hz)
    (fun z _ => by
      rw [archFactor_centered_factorization]
      simp only [Finset.prod_singleton, m, ρ, h, pow_one])
  simpa only [z₁, z₂, ρ, m, Finset.sum_singleton, Nat.cast_one, one_mul] using hres

/-- Same finite residue law in the Euler logarithmic-derivative normalization, filtered. -/
theorem rectIntegral_xiMassPoly_mul_archLogDeriv (P : Polynomial ℝ)
    {a c R : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hR : 0 < R) (τ : ℂ) :
    rectIntegral
      (fun z => xiMassPolyAnalyticTest P a τ z *
        logDeriv archFactor (xiMassCenteredArchPoint z))
      (((-R : ℝ) : ℂ) - c * I) (R : ℂ) =
        2 * Real.pi * xiMassPolyAnalyticTest P a τ xiMassArchPole := by
  have hres := rectIntegral_xiMassPoly_mul_logDeriv_centeredArchFactor P hhalf hca hR τ
  have hcongr : rectIntegral
      (fun z => xiMassPolyAnalyticTest P a τ z *
        logDeriv archFactor (xiMassCenteredArchPoint z))
      (((-R : ℝ) : ℂ) - c * I) (R : ℂ) =
      (-I) * rectIntegral
        (fun z => xiMassPolyAnalyticTest P a τ z *
          logDeriv (fun w => archFactor (xiMassCenteredArchPoint w)) z)
        (((-R : ℝ) : ℂ) - c * I) (R : ℂ) := by
    let z₁ : ℂ := (((-R : ℝ) : ℂ) - c * I)
    let z₂ : ℂ := (R : ℂ)
    let S : Set ℂ := uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im
    have hsub : S ⊆ xiMassArchShiftDomain a := by
      simpa only [S, z₁, z₂] using xiMassPolyArchRectangle_subset_domain hhalf hca hR
    have hedges : rectIntegral
        (fun z => xiMassPolyAnalyticTest P a τ z *
          logDeriv archFactor (xiMassCenteredArchPoint z)) z₁ z₂ =
        rectIntegral
          (fun z => (-I) * (xiMassPolyAnalyticTest P a τ z *
            logDeriv (fun w => archFactor (xiMassCenteredArchPoint w)) z)) z₁ z₂ := by
      apply rectIntegral_congr (S := S)
      · intro z hz
        rw [logDeriv_centeredArchFactor_eq_I_mul z
          (xiMassCenteredArchPoint_re_pos (hsub hz))]
        calc
          xiMassPolyAnalyticTest P a τ z *
              logDeriv archFactor (xiMassCenteredArchPoint z) =
              (-I * I) * (xiMassPolyAnalyticTest P a τ z *
                logDeriv archFactor (xiMassCenteredArchPoint z)) := by
            rw [neg_mul, Complex.I_mul_I]
            ring
          _ = -I * (xiMassPolyAnalyticTest P a τ z *
                (I * logDeriv archFactor (xiMassCenteredArchPoint z))) := by ring
      · intro x hx
        exact Complex.mem_reProdIm.mpr
          ⟨by simpa [Complex.mul_re] using hx, by simp [Complex.mul_im]⟩
      · intro x hx
        exact Complex.mem_reProdIm.mpr
          ⟨by simpa [Complex.mul_re] using hx, by simp [Complex.mul_im]⟩
      · intro y hy
        exact Complex.mem_reProdIm.mpr
          ⟨by simp [Complex.mul_re], by simpa [Complex.mul_im] using hy⟩
      · intro y hy
        exact Complex.mem_reProdIm.mpr
          ⟨by simp [Complex.mul_re], by simpa [Complex.mul_im] using hy⟩
    rw [show (((-R : ℝ) : ℂ) - c * I) = z₁ by rfl,
      show (R : ℂ) = z₂ by rfl, hedges, rectIntegral_const_mul]
  rw [hcongr, hres]
  calc
    -I * (2 * Real.pi * I * xiMassPolyAnalyticTest P a τ xiMassArchPole) =
        2 * Real.pi * (-I * I) * xiMassPolyAnalyticTest P a τ xiMassArchPole := by ring
    _ = 2 * Real.pi * xiMassPolyAnalyticTest P a τ xiMassArchPole := by
      rw [neg_mul, Complex.I_mul_I]
      ring

/-! ## The exact infinite shift -/

/-- Exact infinite contour shift for the filtered archimedean channel. -/
theorem integral_xiMassPolyBottomArch_eq_centered_add_residue (P : Polynomial ℝ)
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re) :
    (∫ x : ℝ, xiMassPolyBottomArchIntegrand P a c τ x) =
      (∫ x : ℝ, xiMassPolyCenteredArchIntegrand P a τ x) +
        2 * Real.pi * xiMassPolyAnalyticTest P a τ xiMassArchPole := by
  let F : ℂ → ℂ := fun z => xiMassPolyAnalyticTest P a τ z *
    logDeriv archFactor (xiMassCenteredArchPoint z)
  have ha : 0 < a := lt_trans (lt_trans (by norm_num) hhalf) hca
  have hbottom := tendsto_integral_xiMassPolyBottomArchIntegrand_atTop P hhalf hca hτ
  have hcentered : Tendsto (fun R : ℝ => ∫ x in -R..R,
      xiMassPolyCenteredArchIntegrand P a τ x) atTop
      (𝓝 (∫ x : ℝ, xiMassPolyCenteredArchIntegrand P a τ x)) := by
    have hτform : τ = (τ.re : ℂ) + τ.im * I := by
      apply Complex.ext <;> simp
    rw [hτform]
    exact tendsto_integral_xiMassPolyCenteredArchIntegrand_atTop P ha hτ
  have hright := tendsto_integral_xiMassPolyArchVerticalIntegrand_right_atTop P hhalf hca hτ
  have hleft := tendsto_integral_xiMassPolyArchVerticalIntegrand_left_atTop P hhalf hca hτ
  have hlim := ((hbottom.sub hcentered).add (hright.const_smul I)).sub
    (hleft.const_smul I)
  have hlim' : Tendsto (fun R : ℝ =>
      rectIntegral F (((-R : ℝ) : ℂ) - c * I) (R : ℂ)) atTop
      (𝓝 ((∫ x : ℝ, xiMassPolyBottomArchIntegrand P a c τ x) -
        (∫ x : ℝ, xiMassPolyCenteredArchIntegrand P a τ x))) := by
    simpa [rectIntegral, F, xiMassPolyCenteredArchIntegrand_eq,
      xiMassPolyArchVerticalIntegrand_def_eq, xiMassPolyArchVerticalIntegrand_neg_def_eq,
      xiMassArchVerticalEulerPoint,
      xiMassPolyArchContourIntegrand_bottom_add_neg_eq, smul_eq_mul,
      sub_eq_add_neg] using hlim
  have heventually : ∀ᶠ R : ℝ in atTop,
      rectIntegral F (((-R : ℝ) : ℂ) - c * I) (R : ℂ) =
        2 * Real.pi * xiMassPolyAnalyticTest P a τ xiMassArchPole := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact rectIntegral_xiMassPoly_mul_archLogDeriv P hhalf hca hR τ
  have hconst : Tendsto (fun _ : ℝ =>
      2 * Real.pi * xiMassPolyAnalyticTest P a τ xiMassArchPole) atTop
      (𝓝 (2 * Real.pi * xiMassPolyAnalyticTest P a τ xiMassArchPole)) :=
    tendsto_const_nhds
  have heventually' : ∀ᶠ R : ℝ in atTop,
      2 * Real.pi * xiMassPolyAnalyticTest P a τ xiMassArchPole =
        rectIntegral F (((-R : ℝ) : ℂ) - c * I) (R : ℂ) :=
    heventually.mono fun _ h => h.symm
  have htarget := tendsto_nhds_unique hlim' (hconst.congr' heventually')
  exact sub_eq_iff_eq_add'.mp htarget

end

end RHTower
