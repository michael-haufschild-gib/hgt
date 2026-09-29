import GaloisForLFunctions.RHTower.ThetaCutoffCommutatorMellin
import GaloisForLFunctions.RHTower.ThetaZeroDivisionRateTomography
import GaloisForLFunctions.RHTower.RiemannXiZerosInfinite
import GaloisForLFunctions.RHTower.XiRealAxisGrowth
import GaloisForLFunctions.RHTower.SuzukiTorqueContinuationPole
import GaloisForLFunctions.HTGeometry.RiemannZetaMeromorphic

/-!
# The cofinal boundary current changes sign arbitrarily deep in the cusp

The cusp-side Laplace transform of `C_∞`, `∫_0^∞ C_∞(−L) e^{−wL} dL`, equals
`−G(w)/ζ(1+w) − P(w)` for `Re w > 0`, where `P(w) = ∫_0^∞ e^{wy} C_∞(y) dy` is entire (Gaussian decay)
and `1/ζ(1+w) = (1+w) w Γ_ℝ(1+w)/(2 ξ(1+w))` is holomorphic on `Re w > −1` away from the zeros of
`ξ`, none of which is real.  At a zero `ρ` of `ξ` the continuation has a genuine pole.  A
generalization of Landau's singularity theorem to a closed countable singular set therefore
excludes every eventually one-signed tail: `C_∞(y)` takes both signs for arbitrarily negative `y`.
-/

open MeasureTheory Set Filter Topology ArithmeticFunction
open GaloisForLFunctions.RHTower (laplaceReal laplaceMass complexLaplace IsAbscissa tailCarrier
  tailMeasure headLaplace complexLaplace_ofReal hasDerivAt_complexLaplace
  false_of_analyticAt_abscissa)
open GaloisForLFunctions.HTGeometry (isPreconnected_diff_of_countable_of_convex_complex)

namespace RHTower

noncomputable section

/-- **Landau: no eventual sign, countable singular set.**  As in `not_eventually_nonneg_of_pole`,
but the continuation may have a closed countable set `S` of non-real singularities, the chosen
pole `p` being isolated in `S`. -/
theorem not_eventually_nonneg_of_pole_of_countable {g : ℝ → ℝ} (hgc : Continuous g) {Gc : ℂ → ℂ}
    {S : Set ℂ} (hSc : S.Countable) (hScl : IsClosed S) (hSre : ∀ z ∈ S, z.im ≠ 0)
    (hgi : ∀ σ : ℝ, 3 / 2 < σ → IntegrableOn (fun L : ℝ => g L * Real.exp (-σ * L)) (Ioi 0))
    (htrans : ∀ σ : ℝ, 3 / 2 < σ →
      ((∫ L in Ioi (0 : ℝ), g L * Real.exp (-σ * L) : ℝ) : ℂ) = Gc ((σ : ℂ)))
    (hGan : ∀ z : ℂ, 1 / 4 < z.re → z ∉ S → AnalyticAt ℂ Gc z)
    {p : ℂ} (hp : 1 / 4 < p.re) (hpole : ¬ 0 ≤ meromorphicOrderAt Gc p)
    (hpiso : ∀ᶠ s in 𝓝[≠] p, s ∉ S) :
    ¬ ∃ H : ℝ, 0 ≤ H ∧ ∀ L : ℝ, H < L → 0 ≤ g L := by
  rintro ⟨H, hH, hTpos⟩
  have hpos : ∀ u : ℝ, 0 < u → 0 ≤ g (H + u) := fun u hu => hTpos (H + u) (by linarith)
  obtain ⟨c, hc, hc4, hc32⟩ := exists_isAbscissa_tail hgc hH hgi hpos
  set ν : Measure ℝ := tailMeasure g H
  have hSreal : ∀ σ : ℝ, (σ : ℂ) ∉ S := fun σ hσ => hSre _ hσ (Complex.ofReal_im σ)
  have hΦan : ∀ σ : ℝ, 1 / 4 < σ → AnalyticAt ℂ (tailTransform g Gc H) ((σ : ℂ)) := by
    intro σ hσ
    refine analyticAt_tailTransform hgc hH ?_ (hGan _ (by simpa using hσ) (hSreal σ))
    intro hcon
    have hre : ((σ : ℂ)).re = ((1 : ℂ) / 4).re := by rw [hcon]
    simp only [Complex.ofReal_re] at hre
    norm_num at hre
    linarith
  have hCLan : ∀ z : ℂ, c < z.re → AnalyticAt ℂ (complexLaplace ν) z := by
    intro z hz
    have hopen : IsOpen {w : ℂ | c < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hdiff : DifferentiableOn ℂ (complexLaplace ν) {w : ℂ | c < w.re} := fun w hw =>
      ((hasDerivAt_complexLaplace hc hw).differentiableAt).differentiableWithinAt
    exact hdiff.analyticAt (hopen.mem_nhds hz)
  have hray : ∀ σ : ℝ, c < σ → tailTransform g Gc H ((σ : ℂ)) = complexLaplace ν ((σ : ℂ)) := by
    have h1 : AnalyticOnNhd ℝ (fun t : ℝ => tailTransform g Gc H ((t : ℂ))) (Ioi c) := fun t ht =>
      analyticAt_ofReal_comp (hΦan t (lt_of_le_of_lt hc4 ht))
    have h2 : AnalyticOnNhd ℝ (fun t : ℝ => complexLaplace ν ((t : ℂ))) (Ioi c) := fun t ht =>
      analyticAt_ofReal_comp (hCLan _ (by simpa using ht))
    set z₀ : ℝ := max 2 c + 1
    have hz₀c : c < z₀ := by have := le_max_right 2 c; simp only [z₀]; linarith
    have hz₀big : (3 : ℝ) / 2 < z₀ := by have := le_max_left 2 c; simp only [z₀]; linarith
    have hev : (fun t : ℝ => tailTransform g Gc H ((t : ℂ)))
        =ᶠ[𝓝 z₀] fun t : ℝ => complexLaplace ν ((t : ℂ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds (show z₀ ∈ Ioi ((3 : ℝ) / 2) from hz₀big)] with t ht
      have hgt : (3 : ℝ) / 2 < t := ht
      rw [tailTransform_ofReal hgc hH (by linarith) (hgi t hgt) hpos (htrans t hgt),
        complexLaplace_ofReal]
    exact fun σ hσ => h1.eqOn_of_preconnected_of_eventuallyEq h2 isPreconnected_Ioi hz₀c hev hσ
  -- Landau pins the abscissa at the reference pole
  have hceq : c = 1 / 4 := by
    by_contra hne
    have hcgt : 1 / 4 < c := lt_of_le_of_ne hc4 (Ne.symm hne)
    obtain ⟨δ₁, hδ₁, hsub⟩ := Metric.isOpen_iff.mp hScl.isOpen_compl _ (hSreal c)
    set δ : ℝ := min δ₁ (c - 1 / 4)
    have hδpos : 0 < δ := lt_min hδ₁ (by linarith)
    refine false_of_analyticAt_abscissa (Φ := tailTransform g Gc H) hc hδpos (fun z hz => ?_)
      (fun σ h1 _ => by rw [hray σ h1, complexLaplace_ofReal])
    have hdist : dist z ((c : ℂ)) < δ := Metric.mem_ball.mp hz
    have hre : |z.re - c| < δ := by
      have h1 : |z.re - ((c : ℂ)).re| ≤ ‖z - ((c : ℂ))‖ := by
        simpa using Complex.abs_re_le_norm (z - ((c : ℂ)))
      rw [← Complex.dist_eq] at h1
      simpa using lt_of_le_of_lt h1 hdist
    have hzre : 1 / 4 < z.re := by
      have := abs_lt.mp hre; have := min_le_right δ₁ (c - 1 / 4); linarith
    have hz4 : z ≠ 1 / 4 := fun hcon => by rw [hcon] at hzre; norm_num at hzre
    exact analyticAt_tailTransform hgc hH hz4 (hGan z hzre fun hzS =>
      hsub (Metric.mem_ball.mpr (lt_of_lt_of_le hdist (min_le_left _ _))) hzS)
  subst hceq
  -- the continuation is holomorphic across the whole half-plane
  set Psi : ℂ → ℂ := fun s : ℂ =>
    Complex.exp (-s * (H : ℂ)) * (complexLaplace ν s - 1 / (s - 1 / 4)) + headLaplace g H s
  have hPsian : ∀ z : ℂ, 1 / 4 < z.re → AnalyticAt ℂ Psi z := by
    intro z hz
    have hz4 : z ≠ 1 / 4 := fun hcon => by rw [hcon] at hz; norm_num at hz
    exact ((((analyticAt_id.neg).mul analyticAt_const).cexp).mul ((hCLan z hz).sub
      (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hz4)))).add
      (analyticAt_headLaplace hgc hH z)
  have hGPsi : ∀ σ : ℝ, 1 / 4 < σ → Gc ((σ : ℂ)) = Psi ((σ : ℂ)) := by
    intro σ hσ
    have h := hray σ hσ
    rw [tailTransform] at h
    have hEE : Complex.exp (-((σ : ℂ)) * (H : ℂ)) * Complex.exp (((σ : ℂ)) * (H : ℂ)) = 1 := by
      rw [← Complex.exp_add, show -((σ : ℂ)) * (H : ℂ) + ((σ : ℂ)) * (H : ℂ) = 0 by ring,
        Complex.exp_zero]
    simp only [Psi]
    rw [← h]
    linear_combination (headLaplace g H ((σ : ℂ)) - Gc ((σ : ℂ))) * hEE
  set W : Set ℂ := {s : ℂ | 1 / 4 < s.re} \ S
  have h2W : (2 : ℂ) ∈ W := ⟨by show (1 : ℝ) / 4 < (2 : ℂ).re; norm_num, by
    have := hSreal 2; simpa using this⟩
  have hWconn : IsPreconnected W :=
    isPreconnected_diff_of_countable_of_convex_complex (convex_halfSpace_re_gt _)
      (isOpen_lt continuous_const Complex.continuous_re) hSc h2W
  have hGW : AnalyticOnNhd ℂ Gc W := fun z hz => hGan z hz.1 hz.2
  have hPsiW : AnalyticOnNhd ℂ Psi W := fun z hz => hPsian z hz.1
  have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] ((2 : ℂ)), Gc z = Psi z := by
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] (2 : ℝ), Gc ((t : ℂ)) = Psi ((t : ℂ)) := by
      filter_upwards [nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds
        (show (2 : ℝ) ∈ Ioi ((1 : ℝ) / 4) by norm_num))] with t ht
      exact hGPsi t ht
    have hcast : ((2 : ℂ)) = (((2 : ℝ)) : ℂ) := by norm_num
    rw [hcast]
    exact (tendsto_ofReal_nhdsNE 2).frequently hev.frequently
  have hEqOn := hGW.eqOn_of_preconnected_of_frequently_eq hPsiW hWconn h2W hfreq
  have hnear : ∀ᶠ s : ℂ in 𝓝[≠] p, s ∈ W := by
    have hre : ∀ᶠ s : ℂ in 𝓝 p, 1 / 4 < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hp
    filter_upwards [hpiso, nhdsWithin_le_nhds hre] with s hs1 hs2
    exact ⟨hs2, hs1⟩
  have hEv : Gc =ᶠ[𝓝[≠] p] Psi := by
    filter_upwards [hnear] with s hs
    exact hEqOn hs
  exact hpole ((meromorphicOrderAt_congr hEv).symm ▸ (hPsian p hp).meromorphicOrderAt_nonneg)


/-! ## The reciprocal zeta factor as an analytic function -/

/-- `1/ζ(1+w)` written as `(1+w) w Γ_ℝ(1+w) / (2 ξ(1+w))`. -/
def zetaInvShift (w : ℂ) : ℂ := (1 + w) * w * Complex.Gammaℝ (1 + w) / (2 * xi (1 + w))

theorem zetaInvShift_eq {w : ℂ} (hw : 0 < w.re) : zetaInvShift w = (riemannZeta (1 + w))⁻¹ := by
  have hs0 : (1 + w) ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have hs1 : (1 + w) ≠ 1 := fun h => hw0 (by linear_combination h)
  have hG : Complex.Gammaℝ (1 + w) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hz : riemannZeta (1 + w) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  have hζ := riemannZeta_def_of_ne_zero hs0
  have hΛ : completedRiemannZeta (1 + w) ≠ 0 := fun h => hz (by rw [hζ, h, zero_div])
  rw [zetaInvShift, xi_eq_mul_completedRiemannZeta hs0 hs1, hζ]
  field_simp
  ring

theorem analyticAt_zetaInvShift {w : ℂ} (hw : -1 < w.re) (hxi : xi (1 + w) ≠ 0) :
    AnalyticAt ℂ zetaInvShift w := by
  set U : Set ℂ := {w : ℂ | -1 < w.re} ∩ {w | xi (1 + w) ≠ 0}
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_ne_fun (xi_differentiable.continuous.comp (continuous_const.add continuous_id))
      continuous_const)
  refine DifferentiableOn.analyticAt (fun v hv => ?_) (hU.mem_nhds ⟨hw, hxi⟩)
  have hv1 : -1 < v.re := hv.1
  have hv2 : xi (1 + v) ≠ 0 := hv.2
  have hG : DifferentiableAt ℂ Complex.Gamma ((1 + v) / 2) :=
    Complex.differentiableAt_Gamma _ fun m h => by
      have h1 := congrArg Complex.re h
      simp only [Complex.div_re, Complex.add_re, Complex.one_re, Complex.neg_re,
        Complex.natCast_re] at h1
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      norm_num at h1
      nlinarith
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_pos.ne'
  have hf : DifferentiableAt ℂ (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)) (1 + v) :=
    ((differentiableAt_id.neg.div_const 2).const_cpow (Or.inl hpi)).mul
      (hG.comp (1 + v) (differentiableAt_id.div_const 2))
  have hΓ : DifferentiableAt ℂ Complex.Gammaℝ (1 + v) :=
    hf.congr_of_eventuallyEq (Eventually.of_forall fun s => Complex.Gammaℝ_def s)
  have hshift : DifferentiableAt ℂ (fun w : ℂ => 1 + w) v :=
    (differentiableAt_const _).add differentiableAt_id
  have hnum : DifferentiableAt ℂ (fun w : ℂ => (1 + w) * w * Complex.Gammaℝ (1 + w)) v :=
    (hshift.mul differentiableAt_id).mul (hΓ.comp v hshift)
  have hden : DifferentiableAt ℂ (fun w : ℂ => 2 * xi (1 + w)) v :=
    (differentiableAt_const _).mul (xi_differentiable.differentiableAt.comp v hshift)
  exact (hnum.div hden (mul_ne_zero two_ne_zero hv2)).differentiableWithinAt

/-! ## The physical-side head transform is entire -/

/-- `P(w) = ∫_0^∞ e^{wy} C_∞(y) dy`. -/
def cofinalHeadTransform (w : ℂ) : ℂ :=
  ∫ y in Ioi (0 : ℝ), Complex.exp (w * y) * (cofinalBoundaryProfile y : ℂ)

theorem continuous_cofinalBoundaryProfile : Continuous cofinalBoundaryProfile := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  have hS : PrimeExhaustion fun N => (N + 1).primesBelow :=
    ⟨fun N p hp => Nat.prime_of_mem_primesBelow hp, fun p hp => by
      filter_upwards [eventually_ge_atTop p] with N hN
      exact Nat.mem_primesBelow.2 ⟨by omega, hp⟩⟩
  have h := hS.tendstoUniformlyOn_commutatorBoundaryProfile (|y| + 1)
  have hc : ContinuousOn cofinalBoundaryProfile (Icc (-(|y| + 1)) (|y| + 1)) :=
    h.continuousOn (Eventually.of_forall fun N => by
      refine Continuous.continuousOn ?_
      refine (continuous_iff_continuousAt.2 fun x => ?_)
      rw [show commutatorBoundaryProfile ((N + 1).primesBelow) = fun x => _ from
        funext (commutatorBoundaryProfile_eq_flux _ (hS.prime N))]
      exact ((continuous_finsetSum _ fun T _ => continuous_const.mul
        (continuous_thetaFluxTerm _)).neg.add (continuous_const.mul
          (continuous_thetaFluxTerm 1))).continuousAt).frequently
  exact hc.continuousAt (Icc_mem_nhds (by linarith [neg_abs_le y]) (by linarith [le_abs_self y]))

theorem differentiable_cofinalHeadTransform : Differentiable ℂ cofinalHeadTransform := by
  intro w₀
  set K : ℝ := 2 * Real.pi * ∑' d : ℕ, (d : ℝ) ^ 2 * Real.exp (-(Real.pi / 2) * (d : ℝ) ^ 2)
  set b : ℝ := max (w₀.re + 5) 1
  have hb : 0 < b := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hmaj : IntegrableOn (fun y : ℝ => K * (Real.exp (b * y) *
      Real.exp (-(Real.pi / 2 * Real.exp (2 * y))))) (Ioi 0) :=
    ((integrable_exp_mul_exp_neg_mul_exp_two_mul hb (by positivity)).const_mul K).integrableOn
  have hC : ∀ y : ℝ, 0 < y → ∀ w : ℂ, w.re ≤ w₀.re + 1 →
      (1 + y) * Real.exp (w.re * y) * |cofinalBoundaryProfile y| ≤
        K * (Real.exp (b * y) * Real.exp (-(Real.pi / 2 * Real.exp (2 * y)))) := fun y hy w hw => by
    have hg := abs_cofinalBoundaryProfile_le_gaussian hy.le
    have h1 : 1 + y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
    have h2 : Real.exp y * Real.exp (w.re * y) * Real.exp (3 * y) ≤ Real.exp (b * y) := by
      rw [← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith [le_max_left (w₀.re + 5) 1])
    have hK : 0 ≤ K := by
      have : (0 : ℝ) ≤ ∑' d : ℕ, (d : ℝ) ^ 2 * Real.exp (-(Real.pi / 2) * (d : ℝ) ^ 2) :=
        tsum_nonneg fun d => by positivity
      positivity
    calc (1 + y) * Real.exp (w.re * y) * |cofinalBoundaryProfile y|
        ≤ Real.exp y * Real.exp (w.re * y) * (K * (Real.exp (3 * y) *
            Real.exp (-(Real.pi / 2 * Real.exp (2 * y))))) := by gcongr
      _ = K * ((Real.exp y * Real.exp (w.re * y) * Real.exp (3 * y)) *
            Real.exp (-(Real.pi / 2 * Real.exp (2 * y)))) := by ring
      _ ≤ _ := by gcongr
  have hcont : ∀ w : ℂ, Continuous fun y : ℝ => Complex.exp (w * y) * (cofinalBoundaryProfile y : ℂ) :=
    fun w => (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
      (Complex.continuous_ofReal.comp continuous_cofinalBoundaryProfile)
  have hball : ∀ w ∈ Metric.ball w₀ 1, w.re ≤ w₀.re + 1 := fun w hw => by
    have := (Complex.abs_re_le_norm (w - w₀)).trans (le_of_lt (by rwa [← dist_eq_norm]))
    rw [Complex.sub_re] at this
    linarith [le_abs_self (w.re - w₀.re)]
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun w y => Complex.exp (w * y) * (cofinalBoundaryProfile y : ℂ))
    (F' := fun w y => (y : ℂ) * (Complex.exp (w * y) * (cofinalBoundaryProfile y : ℂ)))
    (bound := fun y => K * (Real.exp (b * y) * Real.exp (-(Real.pi / 2 * Real.exp (2 * y)))))
    (Metric.ball_mem_nhds w₀ one_pos) (Eventually.of_forall fun w => (hcont w).aestronglyMeasurable)
    (hmaj.mono' (hcont w₀).aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioi).2
      (ae_of_all _ fun y hy => by
        rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        have := hC y hy w₀ (by linarith)
        have hy0 : (0 : ℝ) < y := hy
        have hp := mul_nonneg (Real.exp_pos (w₀.re * y)).le (abs_nonneg (cofinalBoundaryProfile y))
        calc Real.exp (w₀.re * y) * |cofinalBoundaryProfile y|
            ≤ (1 + y) * (Real.exp (w₀.re * y) * |cofinalBoundaryProfile y|) :=
              le_mul_of_one_le_left hp (by linarith)
          _ ≤ _ := by rw [← mul_assoc]; exact this)))
    ((Complex.continuous_ofReal.mul (hcont w₀)).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun y hy w hw => by
      rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (show (0:ℝ) < y from hy)]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      have := hC y hy w (hball w hw)
      have hp := mul_nonneg (Real.exp_pos (w.re * y)).le (abs_nonneg (cofinalBoundaryProfile y))
      calc y * (Real.exp (w.re * y) * |cofinalBoundaryProfile y|)
          ≤ (1 + y) * (Real.exp (w.re * y) * |cofinalBoundaryProfile y|) :=
            mul_le_mul_of_nonneg_right (by linarith) hp
        _ ≤ _ := by rw [← mul_assoc]; exact this))
    hmaj (ae_of_all _ fun y w _ => by
      have := ((hasDerivAt_id w).mul_const (y : ℂ)).cexp.mul_const (cofinalBoundaryProfile y : ℂ)
      refine this.congr_deriv ?_
      simp only [id, one_mul]
      ring)
  exact h.2.differentiableAt

/-! ## The cusp-side transform and its continuation -/

/-- The continuation `Gc(s) = −G(s−1)/ζ(s) − P(s−1)` of the cusp-side Laplace transform. -/
def cuspTransformContinuation (s : ℂ) : ℂ :=
  -(commutatorGammaFactor (s - 1) * zetaInvShift (s - 1)) - cofinalHeadTransform (s - 1)

theorem cuspTransform_eq {σ : ℝ} (hσ : 3 / 2 < σ) :
    IntegrableOn (fun L : ℝ => cofinalBoundaryProfile (-L) * Real.exp L * Real.exp (-σ * L)) (Ioi 0) ∧
    ((∫ L in Ioi (0 : ℝ), cofinalBoundaryProfile (-L) * Real.exp L * Real.exp (-σ * L) : ℝ) : ℂ) =
      cuspTransformContinuation σ := by
  set w : ℝ := σ - 1
  have hw : 1 / 2 < w := by simp only [w]; linarith
  have hfun : ∀ L : ℝ, cofinalBoundaryProfile (-L) * Real.exp L * Real.exp (-σ * L) =
      cofinalBoundaryProfile (-L) * Real.exp (-w * L) := fun L => by
    rw [mul_assoc, ← Real.exp_add]; congr 2; simp only [w]; ring
  simp_rw [hfun]
  refine ⟨((exp_neg_integrableOn_Ioi 0 (by linarith : (0:ℝ) < w)).const_mul (1 / 2)).mono'
    ((continuous_cofinalBoundaryProfile.comp continuous_neg).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
    (ae_of_all _ fun L => ?_), ?_⟩
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), neg_mul]
    exact mul_le_mul_of_nonneg_right (abs_cofinalBoundaryProfile_le _) (Real.exp_pos _).le
  obtain ⟨hint, hval⟩ := integral_cexp_mul_cofinalBoundaryProfile (z := (w : ℂ)) (by simp; linarith)
  have hsplit := integral_add_compl (measurableSet_Ioi (a := (0 : ℝ))) hint
  rw [compl_Ioi, hval] at hsplit
  have hneg := integral_comp_neg_Iic (0 : ℝ)
    (fun x : ℝ => Complex.exp ((w : ℂ) * (-x : ℝ)) * (cofinalBoundaryProfile (-x) : ℂ))
  simp only [neg_neg, neg_zero] at hneg
  rw [← integral_complex_ofReal]
  have hcast : (fun L : ℝ => ((cofinalBoundaryProfile (-L) * Real.exp (-w * L) : ℝ) : ℂ)) =
      fun x : ℝ => Complex.exp ((w : ℂ) * (-x : ℝ)) * (cofinalBoundaryProfile (-x) : ℂ) := by
    funext x; push_cast; ring_nf
  rw [hcast, ← hneg, cuspTransformContinuation, show (σ : ℂ) - 1 = (w : ℂ) by simp [w],
    zetaInvShift_eq (by simp; linarith), cofinalHeadTransform]
  linear_combination hsplit

theorem analyticAt_cuspTransformContinuation {s : ℂ} (hs : 1 / 4 < s.re) (hxi : xi s ≠ 0) :
    AnalyticAt ℂ cuspTransformContinuation s := by
  set U : Set ℂ := {s : ℂ | 1 / 4 < s.re} ∩ {s | xi s ≠ 0}
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_ne_fun xi_differentiable.continuous continuous_const)
  refine DifferentiableOn.analyticAt (fun v hv => ?_) (hU.mem_nhds ⟨hs, hxi⟩)
  have hv1 : 1 / 4 < v.re := hv.1
  have hv2 : xi v ≠ 0 := hv.2
  have hsh : DifferentiableAt ℂ (fun s : ℂ => s - 1) v := differentiableAt_id.sub_const 1
  have hG : DifferentiableAt ℂ commutatorGammaFactor (v - 1) := by
    have hΓ : DifferentiableAt ℂ Complex.Gamma ((v - 1 + 3) / 2) :=
      Complex.differentiableAt_Gamma _ fun m h => by
        have h1 := congrArg Complex.re h
        simp only [Complex.div_re, Complex.add_re, Complex.sub_re, Complex.one_re, Complex.neg_re,
          Complex.natCast_re] at h1
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        norm_num at h1
        nlinarith
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_pos.ne'
    have h1 : DifferentiableAt ℂ (fun z : ℂ => -(z + 1) / 2) (v - 1) :=
      ((differentiableAt_id.add_const 1).neg.div_const 2)
    have h2 : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-(z + 1) / 2)) (v - 1) :=
      h1.const_cpow (Or.inl hpi)
    have h3 : DifferentiableAt ℂ (fun z : ℂ => (z + 3) / 2) (v - 1) :=
      (differentiableAt_id.add_const 3).div_const 2
    have h4 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma ((z + 3) / 2)) (v - 1) :=
      hΓ.comp (v - 1) h3
    exact h2.mul h4
  have hZ : DifferentiableAt ℂ zetaInvShift (v - 1) :=
    (analyticAt_zetaInvShift (by simp; linarith) (by rwa [add_sub_cancel])).differentiableAt
  exact ((((hG.comp v hsh).mul (hZ.comp v hsh)).neg).sub
    ((differentiable_cofinalHeadTransform (v - 1)).comp v hsh)).differentiableWithinAt

/-! ## A genuine pole at every zero of `ξ` -/

theorem eventually_xi_ne_zero (ρ : ℂ) : ∀ᶠ s in 𝓝[≠] ρ, xi s ≠ 0 := by
  rcases (xi_differentiable.analyticAt ρ).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have hxiA : AnalyticOnNhd ℂ xi univ := fun z _ => xi_differentiable.analyticAt z
    have hEq := hxiA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ ρ) (show xi =ᶠ[𝓝 ρ] 0 from h)
    exact xi_ne_zero_of_real 0 (by simpa using hEq (mem_univ ((0 : ℝ) : ℂ)))
  · exact h

theorem analyticAt_commutatorGammaFactor {z : ℂ} (hz : -3 < z.re) :
    AnalyticAt ℂ commutatorGammaFactor z := by
  have hU : IsOpen {z : ℂ | -3 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.analyticAt (fun v hv => ?_) (hU.mem_nhds hz)
  have hv1 : -3 < v.re := hv
  have hΓ : DifferentiableAt ℂ Complex.Gamma ((v + 3) / 2) :=
    Complex.differentiableAt_Gamma _ fun m h => by
      have h1 := congrArg Complex.re h
      simp only [Complex.div_re, Complex.add_re, Complex.neg_re, Complex.natCast_re] at h1
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      norm_num at h1
      nlinarith
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_pos.ne'
  have h2 : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-(z + 1) / 2)) v :=
    ((differentiableAt_id.add_const 1).neg.div_const 2).const_cpow (Or.inl hpi)
  have h4 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma ((z + 3) / 2)) v :=
    hΓ.comp v ((differentiableAt_id.add_const 3).div_const 2)
  exact (h2.mul h4).differentiableWithinAt

theorem commutatorGammaFactor_ne_zero {z : ℂ} (hz : -3 < z.re) : commutatorGammaFactor z ≠ 0 := by
  refine mul_ne_zero ?_ (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))
  rw [Ne, Complex.cpow_eq_zero_iff]
  exact fun h => (Complex.ofReal_ne_zero.2 Real.pi_pos.ne') h.1

theorem not_meromorphicOrderAt_nonneg_cuspTransform {ε : ℂ} (hε : ε ≠ 0) {ρ : ℂ} (hρ : xi ρ = 0)
    (hρre : 0 < ρ.re) : ¬ 0 ≤ meromorphicOrderAt (fun s => ε * cuspTransformContinuation s) ρ := by
  intro ho
  have hρ1 : ρ ≠ 1 := fun h => xi_ne_zero_of_real 1 (by rw [h] at hρ; simpa using hρ)
  have hρ0 : ρ ≠ 0 := fun h => xi_ne_zero_of_real 0 (by rw [h] at hρ; simpa using hρ)
  set N : ℂ → ℂ := fun s => (1 + (s - 1)) * (s - 1) * Complex.Gammaℝ (1 + (s - 1))
  have hNan : AnalyticAt ℂ N ρ := by
    have hsh : AnalyticAt ℂ (fun s : ℂ => 1 + (s - 1)) ρ := analyticAt_const.add (analyticAt_id.sub analyticAt_const)
    exact (hsh.mul (analyticAt_id.sub analyticAt_const)).mul
      ((GaloisForLFunctions.HTGeometry.analyticAt_Gammaℝ (by simpa using hρre)).comp hsh)
  have hN0 : N ρ ≠ 0 := by
    simp only [N, add_sub_cancel]
    exact mul_ne_zero (mul_ne_zero hρ0 (sub_ne_zero.2 hρ1)) (Complex.Gammaℝ_ne_zero_of_re_pos hρre)
  have hxian : AnalyticAt ℂ (fun s => 2 * xi (1 + (s - 1))) ρ :=
    analyticAt_const.mul ((xi_differentiable.analyticAt _).comp
      (analyticAt_const.add (analyticAt_id.sub analyticAt_const)))
  have hGan : AnalyticAt ℂ (fun s => commutatorGammaFactor (s - 1)) ρ :=
    (analyticAt_commutatorGammaFactor (by simp; linarith)).comp (analyticAt_id.sub analyticAt_const)
  have hGne : commutatorGammaFactor (ρ - 1) ≠ 0 := commutatorGammaFactor_ne_zero (by simp; linarith)
  have hPan : AnalyticAt ℂ (fun s => cofinalHeadTransform (s - 1)) ρ :=
    (differentiable_cofinalHeadTransform.analyticAt _).comp (analyticAt_id.sub analyticAt_const)
  have hZfun : (fun s => zetaInvShift (s - 1)) = fun s => N s / (2 * xi (1 + (s - 1))) := rfl
  have hmero : MeromorphicAt (fun s => ε * cuspTransformContinuation s) ρ := by
    have hZ : MeromorphicAt (fun s => zetaInvShift (s - 1)) ρ := by
      rw [hZfun]; exact hNan.meromorphicAt.div hxian.meromorphicAt
    exact analyticAt_const.meromorphicAt.mul ((hGan.meromorphicAt.mul hZ).neg.sub hPan.meromorphicAt)
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hmero ho
  have hGnear : ∀ᶠ s in 𝓝[≠] ρ, commutatorGammaFactor (s - 1) ≠ 0 :=
    nhdsWithin_le_nhds (hGan.continuousAt.eventually_ne hGne)
  have hZlim : Tendsto (fun s => zetaInvShift (s - 1)) (𝓝[≠] ρ)
      (𝓝 (-(ε⁻¹ * c + cofinalHeadTransform (ρ - 1)) / commutatorGammaFactor (ρ - 1))) := by
    have h1 := (((hc.const_mul ε⁻¹).add (hPan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)).neg).div
      (hGan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hGne
    refine h1.congr' ?_
    filter_upwards [hGnear] with s hs
    show -(ε⁻¹ * (ε * cuspTransformContinuation s) + cofinalHeadTransform (s - 1)) /
      commutatorGammaFactor (s - 1) = zetaInvShift (s - 1)
    rw [cuspTransformContinuation, inv_mul_cancel_left₀ hε, div_eq_iff hs]
    ring
  have hprod : ∀ᶠ s in 𝓝[≠] ρ, 2 * xi (1 + (s - 1)) * zetaInvShift (s - 1) = N s := by
    filter_upwards [eventually_xi_ne_zero ρ] with s hs
    have : 2 * xi (1 + (s - 1)) ≠ 0 := mul_ne_zero two_ne_zero (by rwa [add_sub_cancel])
    show 2 * xi (1 + (s - 1)) * (N s / (2 * xi (1 + (s - 1)))) = N s
    rw [mul_div_cancel₀ _ this]
  have hL := ((hxian.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul hZlim).congr' hprod
  have hN := hNan.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (a := ρ) (s := {ρ}ᶜ))
  have huniq := tendsto_nhds_unique hL hN
  simp only [add_sub_cancel, hρ, mul_zero, zero_mul] at huniq
  exact hN0 huniq.symm

theorem exists_xi_zero_re_ge_half : ∃ ρ : ℂ, xi ρ = 0 ∧ 1 / 2 ≤ ρ.re := by
  obtain ⟨ρ, h0, h1, hz⟩ := exists_riemannZeta_zero_mem_openStrip
  have hρ1 : ρ ≠ 1 := fun h => by rw [h] at h1; simp at h1
  have hxi : xi ρ = 0 := (xi_eq_zero_iff h0 hρ1).2 hz
  by_cases h : 1 / 2 ≤ ρ.re
  · exact ⟨ρ, hxi, h⟩
  · refine ⟨1 - ρ, by rw [xi_one_sub, hxi], ?_⟩
    simp only [Complex.sub_re, Complex.one_re]
    linarith

/-- **The cofinal current changes sign arbitrarily far into the negative cusp.**  For `ε = ±1`
there is no `T` with `ε C_∞(y) ≥ 0` for all `y ≤ −T`: an eventually one-signed tail would, by
Landau's theorem, have a real singularity at its abscissa, while the Mellin transform
`−G(z)/ζ(1+z)` is holomorphic at every real `z > −1` and has a genuine pole at `ρ − 1` for every
zero `ρ` of `ξ`. -/
theorem cofinalBoundaryProfile_not_eventually_signed {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ¬ ∃ T : ℝ, ∀ y ≤ -T, 0 ≤ ε * cofinalBoundaryProfile y := by
  rintro ⟨T, hT⟩
  have hε0 : (ε : ℂ) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  obtain ⟨ρ, hρ, hρre⟩ := exists_xi_zero_re_ge_half
  set g : ℝ → ℝ := fun L => ε * cofinalBoundaryProfile (-L) * Real.exp L
  have hgc : Continuous g := (continuous_const.mul (continuous_cofinalBoundaryProfile.comp
    continuous_neg)).mul Real.continuous_exp
  have hS : ({s : ℂ | xi s = 0}).Countable := xi_zeroSet_countable
  have hScl : IsClosed {s : ℂ | xi s = 0} := isClosed_eq xi_differentiable.continuous continuous_const
  have hSre : ∀ z ∈ {s : ℂ | xi s = 0}, z.im ≠ 0 := fun z hz him => by
    have : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    exact xi_ne_zero_of_real z.re (this ▸ hz)
  have hgi : ∀ σ : ℝ, 3 / 2 < σ → IntegrableOn (fun L : ℝ => g L * Real.exp (-σ * L)) (Ioi 0) :=
    fun σ hσ => IntegrableOn.congr_fun ((cuspTransform_eq hσ).1.const_mul ε)
      (fun L _ => by simp only [g]; ring) measurableSet_Ioi
  have htrans : ∀ σ : ℝ, 3 / 2 < σ →
      ((∫ L in Ioi (0 : ℝ), g L * Real.exp (-σ * L) : ℝ) : ℂ) =
        (fun s => (ε : ℂ) * cuspTransformContinuation s) (σ : ℂ) := fun σ hσ => by
    show _ = (ε : ℂ) * cuspTransformContinuation (σ : ℂ)
    rw [← (cuspTransform_eq hσ).2, ← Complex.ofReal_mul, ← integral_const_mul]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun L _ => ?_
    simp only [g]; ring
  have hGan : ∀ z : ℂ, 1 / 4 < z.re → z ∉ {s : ℂ | xi s = 0} →
      AnalyticAt ℂ (fun s => (ε : ℂ) * cuspTransformContinuation s) z := fun z hz hzS =>
    analyticAt_const.mul (analyticAt_cuspTransformContinuation hz hzS)
  refine not_eventually_nonneg_of_pole_of_countable hgc hS hScl hSre hgi htrans hGan
    (p := ρ) (by linarith) (not_meromorphicOrderAt_nonneg_cuspTransform hε0 hρ (by linarith))
    ((eventually_xi_ne_zero ρ).mono fun s hs => hs) ⟨max T 0, le_max_right _ _, fun L hL => ?_⟩
  have hy : -L ≤ -T := by linarith [le_max_left T 0]
  have := hT (-L) hy
  simp only [g]
  exact mul_nonneg this (Real.exp_pos _).le

/-- `C_∞` takes both signs for arbitrarily negative `y`. -/
theorem cofinalBoundaryProfile_takes_both_signs (T : ℝ) :
    (∃ y ≤ -T, cofinalBoundaryProfile y < 0) ∧ ∃ y ≤ -T, 0 < cofinalBoundaryProfile y := by
  constructor
  · by_contra h
    push Not at h
    exact cofinalBoundaryProfile_not_eventually_signed (Or.inl rfl) ⟨T, fun y hy => by
      simpa using h y hy⟩
  · by_contra h
    push Not at h
    exact cofinalBoundaryProfile_not_eventually_signed (Or.inr rfl) ⟨T, fun y hy => by
      simpa using h y hy⟩

end

end RHTower
