import GaloisForLFunctions.RHTower.GaussianBudgetShiftMixtureLaw
import GaloisForLFunctions.HTGeometry.LogDerivativeResidue

/-!
# Signed mixtures of Gaussian budgets: the smallest weighted shift decides

For distinct shifts `σ_j > 0` and arbitrary real weights `c_j` let

  `M(y) = Σ_j c_j (P_{σ_j} − C_{σ_j})(y)`,  `P_σ(y) = Σ Λ(n) n^{-σ} e^{-yn²}`,  `C_σ(y) = ∫₁^∞ u^{-σ} e^{-yu²} du`.

* **Signed mixture law** (`xi_ne_zero_of_gaussianSignedMixtureBudget`).  If `M ≤ B` on `(0, 1]` and
  the smallest shift `σ₀` carries a nonzero weight, then `ξ` has no zero with `Re z > σ₀`, whatever
  the signs of the weights.  Landau's theorem continues `Σ_j c_j ξ'/ξ(σ_j + 2w)` holomorphically to
  `Re w > 0`.  At a zero `z*` of maximal real part on its horizontal line, the point
  `w* = (z* − σ₀)/2` is a pole of the `σ₀`-term with residue `c₀ m(z*)/2`, while the other shifts see
  the points `z* + σ_j − σ₀`, which lie further right on the same line and are not zeros.  No
  cancellation is possible.
* **Differenced budgets** (`riemannHypothesis_iff_gaussianDifferenceBudget`).  For `½ < σ < 2`, RH holds
  iff `(P_½ − C_½) − (P_σ − C_σ)` is bounded above on `(0, 1]`.  This is the central budget of the
  Euler product `ζ(s)/ζ(s + σ − ½)`, whose von Mangoldt coefficients `Λ(n)(1 − n^{½−σ})` are nonnegative
  and tempered.  Differencing in the shift, or dividing by a shifted zeta factor, removes no part of
  the RH content of the budget.
-/

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.RHTower (laplaceMass complexLaplace IsAbscissa exists_isAbscissa
  differentiableOn_complexLaplace)

namespace RHTower

noncomputable section

open XiAtlasFinitePart

variable {ι : Type*}

/-- The signed Gaussian mixture gap `Σ_{j ∈ s} c_j (P_{σ_j} − C_{σ_j})(y)`. -/
def gaussianSignedMixtureGap (s : Finset ι) (c σ : ι → ℝ) (y : ℝ) : ℝ :=
  ∑ j ∈ s, c j * (gaussianWeightedPrimeMass (σ j) y - gaussianWeightedContinuumMass (σ j) y)

theorem continuous_gaussianSignedMixtureGap_exp {s : Finset ι} {c σ : ι → ℝ}
    (hσ : ∀ j ∈ s, 0 < σ j) :
    Continuous fun u : ℝ => gaussianSignedMixtureGap s c σ (Real.exp (-u)) := by
  unfold gaussianSignedMixtureGap
  refine continuous_finsetSum s fun j hj => ?_
  simp_rw [gaussianWeightedGap_exp_eq_neg_profile]
  exact continuous_const.mul (continuous_gaussianBudgetProfile (hσ j hj) 1 0 0).neg

/-- **Laplace transform of the signed mixture deficit** for `Re w > 3`. -/
theorem integral_gaussianSignedMixtureDeficit_mul_cexp {s : Finset ι} {c σ : ι → ℝ}
    (hσ : ∀ j ∈ s, 0 < σ j) (B : ℝ) {w : ℂ} (hw : 3 < w.re) :
    IntegrableOn (fun u : ℝ => ((B - gaussianSignedMixtureGap s c σ (Real.exp (-u)) : ℝ) : ℂ) *
        Complex.exp (-w * u)) (Ioi 0) ∧
    ∫ u in Ioi (0 : ℝ), ((B - gaussianSignedMixtureGap s c σ (Real.exp (-u)) : ℝ) : ℂ) *
        Complex.exp (-w * u) =
      B / w - ∑ j ∈ s, (c j : ℂ) * (Complex.Gamma w *
        (gaussianArchimedeanCurrent ((σ j : ℂ) + 2 * w) - logDeriv xi ((σ j : ℂ) + 2 * w)) -
          mellin ((Ioi (1 : ℝ)).indicator (gaussianPrimeContinuumGap (σ j : ℂ))) w) := by
  have hpt : ∀ u : ℝ, ((B - gaussianSignedMixtureGap s c σ (Real.exp (-u)) : ℝ) : ℂ) *
      Complex.exp (-w * u) = (B : ℂ) * Complex.exp (-w * u) +
        ∑ j ∈ s, (c j : ℂ) * ((gaussianBudgetProfile 1 (σ j) 0 0 u : ℂ) *
          Complex.exp (-w * u)) := by
    intro u
    simp only [gaussianSignedMixtureGap, gaussianWeightedGap_exp_eq_neg_profile, mul_neg,
      Finset.sum_neg_distrib, sub_neg_eq_add]
    push_cast
    rw [add_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hre : (-w).re < 0 := by simp; linarith
  have hiB : IntegrableOn (fun u : ℝ => (B : ℂ) * Complex.exp (-w * u)) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi hre 0).const_mul _
  have hij : ∀ j ∈ s, IntegrableOn (fun u : ℝ => (c j : ℂ) *
      ((gaussianBudgetProfile 1 (σ j) 0 0 u : ℂ) * Complex.exp (-w * u))) (Ioi 0) :=
    fun j hj => (integrableOn_gaussianBudgetProfile_mul_cexp (hσ j hj) (by norm_num) (by norm_num)
      0 hw).const_mul _
  have hisum : IntegrableOn (fun u : ℝ => ∑ j ∈ s, (c j : ℂ) *
      ((gaussianBudgetProfile 1 (σ j) 0 0 u : ℂ) * Complex.exp (-w * u))) (Ioi 0) :=
    integrable_finsetSum s hij
  refine ⟨(hiB.add hisum).congr_fun (fun u _ => (hpt u).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hpt u), integral_add hiB hisum,
    integral_finsetSum s hij, integral_const_mul, integral_exp_mul_complex_Ioi hre 0]
  have hterm : ∀ j ∈ s, ∫ u in Ioi (0 : ℝ), (c j : ℂ) *
      ((gaussianBudgetProfile 1 (σ j) 0 0 u : ℂ) * Complex.exp (-w * u)) =
      -((c j : ℂ) * (Complex.Gamma w * (gaussianArchimedeanCurrent ((σ j : ℂ) + 2 * w) -
        logDeriv xi ((σ j : ℂ) + 2 * w)) -
          mellin ((Ioi (1 : ℝ)).indicator (gaussianPrimeContinuumGap (σ j : ℂ))) w)) := by
    intro j hj
    rw [integral_const_mul, integral_gaussianBudgetProfile_mul_cexp (hσ j hj) 1 (a := 0)
      (by norm_num) 0 hw, mellin_gap_eq_gamma_mul (hσ j hj) hw]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
  push_cast
  simp only [mul_zero, Complex.exp_zero]
  ring

/-- The residue of `w ↦ ξ'/ξ(a + 2w)` at `w₀` is half the order of `ξ` at `a + 2w₀`. -/
theorem tendsto_sub_mul_logDeriv_xi_affine (a w₀ : ℂ) :
    Tendsto (fun w => (w - w₀) * logDeriv xi (a + 2 * w)) (𝓝[≠] w₀)
      (𝓝 (((analyticOrderAt xi (a + 2 * w₀)).toNat : ℂ) / 2)) := by
  set u₀ : ℂ := a + 2 * w₀ with hu₀
  have hres := GaloisForLFunctions.HTGeometry.tendsto_sub_mul_logDeriv_of_analyticOrderAt
    (xi_differentiable.analyticAt u₀) (ENat.coe_toNat (xi_order_ne_top u₀)).symm
  have hg : Tendsto (fun w : ℂ => a + 2 * w) (𝓝[≠] w₀) (𝓝[≠] u₀) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Continuous fun w : ℂ => a + 2 * w := by fun_prop
      exact (hc.tendsto w₀).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      intro h
      apply hw
      have h' : a + 2 * w = a + 2 * w₀ := h
      have : 2 * w = 2 * w₀ := add_left_cancel h'
      exact mul_left_cancel₀ two_ne_zero this
  have h2 := (hres.comp hg).div_const 2
  refine h2.congr fun w => ?_
  simp only [Function.comp, hu₀]
  ring

/-- Zeros of `w ↦ ξ(a + 2w)` are isolated. -/
theorem xi_affine_eventually_ne_zero (a w₀ : ℂ) :
    ∀ᶠ w in 𝓝[≠] w₀, xi (a + 2 * w) ≠ 0 := by
  have hA : AnalyticAt ℂ (fun w : ℂ => xi (a + 2 * w)) w₀ :=
    (xi_differentiable.analyticAt _).comp (by fun_prop)
  rcases hA.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have hc : Continuous fun u : ℂ => (u - a) / 2 := by fun_prop
    have hmap : Tendsto (fun u : ℂ => (u - a) / 2) (𝓝 (a + 2 * w₀)) (𝓝 w₀) := by
      have := hc.tendsto (a + 2 * w₀)
      rwa [show (a + 2 * w₀ - a) / 2 = w₀ by ring] at this
    have hev : xi =ᶠ[𝓝 (a + 2 * w₀)] 0 := by
      filter_upwards [hmap.eventually h] with u hu
      rwa [show a + 2 * ((u - a) / 2) = u by ring] at hu
    exact xi_order_ne_top (a + 2 * w₀) (analyticOrderAt_eq_top.mpr hev)
  · exact h

/-- **Signed mixture law.**  Let the shifts `σ_j > 0` be distinct, let `σ₀ = σ_{j₀}` be the smallest
one and let its weight be nonzero.  If `Σ_j c_j (P_{σ_j} − C_{σ_j})` is bounded above on `(0, 1]`,
then `ξ` has no zero with `Re z > σ₀`. -/
theorem xi_ne_zero_of_gaussianSignedMixtureBudget {s : Finset ι} {c σ : ι → ℝ}
    (hσ : ∀ j ∈ s, 0 < σ j) (hinj : Set.InjOn σ s) {j₀ : ι} (hj₀ : j₀ ∈ s) (hc₀ : c j₀ ≠ 0)
    (hmin : ∀ j ∈ s, σ j₀ ≤ σ j) {B : ℝ}
    (hB : ∀ y : ℝ, 0 < y → y ≤ 1 → gaussianSignedMixtureGap s c σ y ≤ B)
    {z : ℂ} (hz : σ j₀ < z.re) : xi z ≠ 0 := by
  classical
  set h : ℝ → ℝ := fun u => B - gaussianSignedMixtureGap s c σ (Real.exp (-u)) with hhdef
  have hc : Continuous h := continuous_const.sub (continuous_gaussianSignedMixtureGap_exp hσ)
  have hPc : Continuous fun u => max (h u) 0 := hc.max continuous_const
  have hP0 : ∀ u : ℝ, 0 < u → 0 ≤ max (h u) 0 := fun u _ => le_max_right _ _
  have hPeq : ∀ u : ℝ, 0 < u → max (h u) 0 = h u := by
    intro u hu
    refine max_eq_left ?_
    have := hB (Real.exp (-u)) (Real.exp_pos _) (Real.exp_le_one_iff.2 (by linarith))
    simp only [hhdef]
    linarith
  set ν : Measure ℝ := expThickenedCarrier fun u => max (h u) 0 with hν
  set T : ι → ℂ → ℂ := fun j =>
    mellin ((Ioi (1 : ℝ)).indicator (gaussianPrimeContinuumGap (σ j : ℂ))) with hT
  have hTd : ∀ j ∈ s, Differentiable ℂ (T j) := fun j hj =>
    differentiable_mellin_indicator_gap (by simpa using hσ j hj)
  have hfar : ∀ w : ℂ, 3 < w.re → complexLaplace ν w =
      B / w - ∑ j ∈ s, (c j : ℂ) * (Complex.Gamma w *
        (gaussianArchimedeanCurrent ((σ j : ℂ) + 2 * w) - logDeriv xi ((σ j : ℂ) + 2 * w)) -
          T j w) + 1 / (w + 1) := by
    intro w hw
    obtain ⟨hint, hval⟩ := integral_gaussianSignedMixtureDeficit_mul_cexp (c := c) hσ B hw
    have hint' : IntegrableOn (fun u : ℝ => ((max (h u) 0 : ℝ) : ℂ) * Complex.exp (-w * u))
        (Ioi 0) :=
      hint.congr_fun (fun u hu => by simp only [hhdef] at hPeq ⊢; rw [hPeq u hu]) measurableSet_Ioi
    rw [hν, complexLaplace_expThickenedCarrier hPc hP0 (by linarith) hint',
      setIntegral_congr_fun measurableSet_Ioi (fun u hu => by rw [hPeq u hu]), hval]
  -- the continuation candidate is analytic at every positive real point
  set Ψ : ℂ → ℂ := fun w => B / w - ∑ j ∈ s, (c j : ℂ) * (Complex.Gamma w *
      (gaussianArchimedeanCurrent ((σ j : ℂ) + 2 * w) - logDeriv xi ((σ j : ℂ) + 2 * w)) - T j w) +
      1 / (w + 1) with hΨ
  set V : Set ℂ := {w : ℂ | 0 < w.re} ∩ ⋂ j ∈ s, {w : ℂ | xi ((σ j : ℂ) + 2 * w) ≠ 0} with hV
  have hVo : IsOpen V := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_biInter_finset fun j _ =>
      isOpen_ne_fun (xi_differentiable.continuous.comp (by fun_prop)) continuous_const)
  have hΨd : DifferentiableOn ℂ Ψ V := by
    intro w hw
    have hw0 : 0 < w.re := hw.1
    have hxw : ∀ j ∈ s, xi ((σ j : ℂ) + 2 * w) ≠ 0 := fun j hj => by
      have := hw.2; simp only [mem_iInter] at this; exact this j hj
    have hwne : w ≠ 0 := by intro h; rw [h] at hw0; simp at hw0
    have hw1 : w + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hΓ : DifferentiableAt ℂ Complex.Gamma w := Complex.differentiableAt_Gamma w (fun m h => by
      have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    have hsum : DifferentiableAt ℂ (fun w => ∑ j ∈ s, (c j : ℂ) * (Complex.Gamma w *
        (gaussianArchimedeanCurrent ((σ j : ℂ) + 2 * w) - logDeriv xi ((σ j : ℂ) + 2 * w)) -
          T j w)) w := by
      refine DifferentiableAt.fun_sum fun j hj => ?_
      have hre : 0 < ((σ j : ℂ) + 2 * w).re := by simp; linarith [hσ j hj]
      have hA : DifferentiableAt ℂ (fun w : ℂ => gaussianArchimedeanCurrent ((σ j : ℂ) + 2 * w)) w :=
        (differentiableAt_gaussianArchimedeanCurrent hre).comp (f := fun w : ℂ => (σ j : ℂ) + 2 * w)
          w (by fun_prop)
      have hL : DifferentiableAt ℂ (fun w : ℂ => logDeriv xi ((σ j : ℂ) + 2 * w)) w := by
        have hd : DifferentiableAt ℂ (fun ζ => deriv xi ζ / xi ζ) ((σ j : ℂ) + 2 * w) :=
          ((xi_differentiable.analyticAt _).deriv.differentiableAt).div
            (xi_differentiable _) (hxw j hj)
        exact hd.comp (f := fun w : ℂ => (σ j : ℂ) + 2 * w) w (by fun_prop)
      exact (differentiableAt_const _).mul ((hΓ.mul (hA.sub hL)).sub (hTd j hj w))
    have hBw : DifferentiableAt ℂ (fun w : ℂ => (B : ℂ) / w) w :=
      (differentiableAt_const _).div differentiableAt_id hwne
    have hOw : DifferentiableAt ℂ (fun w : ℂ => 1 / (w + 1)) w :=
      (differentiableAt_const _).div (differentiableAt_id.add (differentiableAt_const _)) hw1
    exact ((hBw.sub hsum).add hOw).differentiableWithinAt
  have hΨan : ∀ t : ℝ, 0 < t → AnalyticAt ℂ Ψ (t : ℂ) := by
    intro t ht
    have hmem : (t : ℂ) ∈ V := by
      refine ⟨by simpa using ht, ?_⟩
      simp only [mem_iInter]
      intro j _
      have hcast : (σ j : ℂ) + 2 * (t : ℂ) = ((σ j + 2 * t : ℝ) : ℂ) := by push_cast; ring
      rw [Set.mem_setOf_eq, hcast]
      exact xi_ne_zero_of_real _
    exact hΨd.analyticAt (hVo.mem_nhds hmem)
  -- Landau: the abscissa of the carrier is at most `0`
  have hiP4 : IntegrableOn (fun u : ℝ => max (h u) 0 * Real.exp (-4 * u)) (Ioi 0) := by
    obtain ⟨hint, -⟩ := integral_gaussianSignedMixtureDeficit_mul_cexp (c := c) hσ B
      (w := (4 : ℝ)) (by simp; norm_num)
    refine integrableOn_real_mul_exp_of_cexp hPc ?_
    refine hint.congr_fun (fun u hu => ?_) measurableSet_Ioi
    simp only [hhdef] at hPeq ⊢
    rw [hPeq u hu]
  obtain ⟨c', hcP⟩ := exists_isAbscissa
    ⟨4, laplaceMass_expThickenedCarrier_ne_top hPc hP0 (by norm_num) hiP4⟩
    ⟨-2, laplaceMass_expThickenedCarrier_eq_top hPc hP0⟩
  have hab : ∃ c₀ : ℝ, IsAbscissa ν c₀ ∧ c₀ ≤ 0 := by
    by_cases hc0 : c' ≤ 0
    · exact ⟨c', hcP, hc0⟩
    · push Not at hc0
      refine ⟨0, RHTower.LiouvilleTriangularHeadOscillation.isAbscissa_eq_of_analyticAt_real hcP
        hc0.le (le_max_left c' 4) (fun t ht => hΨan t ht) (fun w hw => ?_), le_rfl⟩
      have hw3 : 3 < w.re := lt_of_le_of_lt (by have := le_max_right c' 4; linarith) hw
      exact hfar w hw3
  obtain ⟨c₀, hc₀', hc₀0⟩ := hab
  have hLd : DifferentiableOn ℂ (complexLaplace ν) {w : ℂ | 0 < w.re} :=
    (differentiableOn_complexLaplace hc₀').mono fun w hw => lt_of_le_of_lt hc₀0 hw
  -- the holomorphic continuation of `Σ_j c_j ξ'/ξ(σ_j + 2w)`
  set U : Set ℂ := {w : ℂ | 0 < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  set K : ℂ → ℂ := fun w => ∑ j ∈ s, (c j : ℂ) * gaussianArchimedeanCurrent ((σ j : ℂ) + 2 * w) -
      (B / w + 1 / (w + 1) - complexLaplace ν w + ∑ j ∈ s, (c j : ℂ) * T j w) *
        (Complex.Gamma w)⁻¹ with hK
  have hKd : DifferentiableOn ℂ K U := by
    intro w hw
    have hw0 : 0 < w.re := hw
    have hwne : w ≠ 0 := by intro h; rw [h] at hw0; simp at hw0
    have hw1 : w + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hA : DifferentiableAt ℂ
        (fun w => ∑ j ∈ s, (c j : ℂ) * gaussianArchimedeanCurrent ((σ j : ℂ) + 2 * w)) w := by
      refine DifferentiableAt.fun_sum fun j hj => ?_
      have hre : 0 < ((σ j : ℂ) + 2 * w).re := by simp; linarith [hσ j hj]
      exact (differentiableAt_const _).mul ((differentiableAt_gaussianArchimedeanCurrent hre).comp
        (f := fun w : ℂ => (σ j : ℂ) + 2 * w) w (by fun_prop))
    have hTs : DifferentiableAt ℂ (fun w => ∑ j ∈ s, (c j : ℂ) * T j w) w :=
      DifferentiableAt.fun_sum fun j hj => (differentiableAt_const _).mul (hTd j hj w)
    have hLw : DifferentiableAt ℂ (complexLaplace ν) w := hLd.differentiableAt (hUo.mem_nhds hw)
    have hBw : DifferentiableAt ℂ (fun w : ℂ => (B : ℂ) / w) w :=
      (differentiableAt_const _).div differentiableAt_id hwne
    have hOw : DifferentiableAt ℂ (fun w : ℂ => 1 / (w + 1)) w :=
      (differentiableAt_const _).div (differentiableAt_id.add (differentiableAt_const _)) hw1
    have hinner : DifferentiableAt ℂ (fun w => (B / w + 1 / (w + 1) - complexLaplace ν w +
        ∑ j ∈ s, (c j : ℂ) * T j w) * (Complex.Gamma w)⁻¹) w :=
      (((hBw.add hOw).sub hLw).add hTs).mul (Complex.differentiable_one_div_Gamma w)
    exact (hA.sub hinner).differentiableWithinAt
  have hKfar : ∀ w : ℂ, 3 < w.re →
      ∑ j ∈ s, (c j : ℂ) * logDeriv xi ((σ j : ℂ) + 2 * w) = K w := by
    intro w hw
    have hΓ : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have hcore : B / w + 1 / (w + 1) - complexLaplace ν w + ∑ j ∈ s, (c j : ℂ) * T j w =
        Complex.Gamma w * ∑ j ∈ s, (c j : ℂ) * (gaussianArchimedeanCurrent ((σ j : ℂ) + 2 * w) -
          logDeriv xi ((σ j : ℂ) + 2 * w)) := by
      rw [hfar w hw, Finset.mul_sum]
      have : ∑ j ∈ s, (c j : ℂ) * (Complex.Gamma w * (gaussianArchimedeanCurrent
          ((σ j : ℂ) + 2 * w) - logDeriv xi ((σ j : ℂ) + 2 * w)) - T j w) =
          ∑ j ∈ s, Complex.Gamma w * ((c j : ℂ) * (gaussianArchimedeanCurrent ((σ j : ℂ) + 2 * w) -
            logDeriv xi ((σ j : ℂ) + 2 * w))) - ∑ j ∈ s, (c j : ℂ) * T j w := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [this]
      ring
    simp only [hK]
    rw [hcore, mul_comm (Complex.Gamma w), mul_assoc, mul_inv_cancel₀ hΓ, mul_one,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  -- clear denominators: `R = K Q` on `Re w > 0`
  set Q : ℂ → ℂ := fun w => ∏ j ∈ s, xi ((σ j : ℂ) + 2 * w) with hQ
  set R : ℂ → ℂ := fun w => ∑ j ∈ s, (c j : ℂ) * deriv xi ((σ j : ℂ) + 2 * w) *
      ∏ i ∈ s.erase j, xi ((σ i : ℂ) + 2 * w) with hR
  have hQd : Differentiable ℂ Q := by
    have := Differentiable.finsetProd (u := s) (f := fun j w => xi ((σ j : ℂ) + 2 * w))
      (fun j _ => xi_differentiable.comp (by fun_prop))
    have hfun : (∏ j ∈ s, fun w : ℂ => xi ((σ j : ℂ) + 2 * w)) = Q := by
      funext w; rw [Finset.prod_apply]
    rwa [hfun] at this
  have hderiv : Differentiable ℂ (deriv xi) := fun u =>
    (xi_differentiable.analyticAt u).deriv.differentiableAt
  have hRd : Differentiable ℂ R := by
    intro w
    refine DifferentiableAt.fun_sum fun j _ => ?_
    have hp := Differentiable.finsetProd (u := s.erase j) (f := fun i w => xi ((σ i : ℂ) + 2 * w))
      (fun i _ => xi_differentiable.comp (by fun_prop))
    have hfun : (∏ i ∈ s.erase j, fun w : ℂ => xi ((σ i : ℂ) + 2 * w)) =
        fun w => ∏ i ∈ s.erase j, xi ((σ i : ℂ) + 2 * w) := by
      funext w; rw [Finset.prod_apply]
    rw [hfun] at hp
    exact ((differentiableAt_const _).mul ((hderiv.comp (by fun_prop :
      Differentiable ℂ fun w : ℂ => (σ j : ℂ) + 2 * w)) w)).mul (hp w)
  have hRQ : ∀ w : ℂ, Q w ≠ 0 →
      R w = (∑ j ∈ s, (c j : ℂ) * logDeriv xi ((σ j : ℂ) + 2 * w)) * Q w := by
    intro w hQw
    have hxw : ∀ j ∈ s, xi ((σ j : ℂ) + 2 * w) ≠ 0 := Finset.prod_ne_zero_iff.1 hQw
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hQ]
    simp only
    rw [← Finset.mul_prod_erase s (fun i => xi ((σ i : ℂ) + 2 * w)) hj, logDeriv_apply]
    field_simp [hxw j hj]
  have hrelfar : ∀ w : ℂ, 3 < w.re → R w = K w * Q w := by
    intro w hw
    have hQw : Q w ≠ 0 := Finset.prod_ne_zero_iff.2 fun j hj =>
      xi_ne_zero_of_one_lt_re (by simp; linarith [hσ j hj])
    rw [hRQ w hQw, hKfar w hw]
  have hanaL : AnalyticOnNhd ℂ R U := fun w _ => hRd.analyticAt w
  have hanaR : AnalyticOnNhd ℂ (fun w => K w * Q w) U :=
    (hKd.mul hQd.differentiableOn).analyticOnNhd hUo
  have hw₄ : ((4 : ℝ) : ℂ) ∈ U := by show (0 : ℝ) < ((4 : ℝ) : ℂ).re; simp
  have hev : R =ᶠ[𝓝 ((4 : ℝ) : ℂ)] fun w => K w * Q w := by
    have hopen : IsOpen {w : ℂ | 3 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have h43 : (3 : ℝ) < ((4 : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; norm_num
    filter_upwards [hopen.mem_nhds h43] with w hw
    exact hrelfar w hw
  have hid := hanaL.eqOn_of_preconnected_of_eventuallyEq hanaR
    (convex_halfSpace_re_gt 0).isPreconnected hw₄ hev
  -- a zero of maximal real part on the horizontal line through `z`
  intro hzero
  have hz1 : z.re ≤ 1 := by
    by_contra h1; push Not at h1; exact xi_ne_zero_of_one_le_re h1.le hzero
  set S : Set ℂ := {z' : ℂ | xi z' = 0} ∩ ({z' : ℂ | z'.im = z.im} ∩
    ({z' : ℂ | z.re ≤ z'.re} ∩ {z' : ℂ | z'.re ≤ 1})) with hS
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_eq xi_differentiable.continuous continuous_const).inter
        ((isClosed_eq Complex.continuous_im continuous_const).inter
          ((isClosed_le continuous_const Complex.continuous_re).inter
            (isClosed_le Complex.continuous_re continuous_const)))
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := |z.re| + 1 + |z.im|)).subset ?_
      rintro z' ⟨-, him, hre1, hre2⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      have him' : z'.im = z.im := him
      have hre1' : z.re ≤ z'.re := hre1
      have hre2' : z'.re ≤ 1 := hre2
      have habs : |z'.re| ≤ |z.re| + 1 := abs_le.2 ⟨by linarith [neg_abs_le z.re],
        by linarith [abs_nonneg z.re]⟩
      calc ‖z'‖ ≤ |z'.re| + |z'.im| := Complex.norm_le_abs_re_add_abs_im z'
        _ ≤ |z.re| + 1 + |z.im| := by rw [him']; linarith
  have hzS : z ∈ S := ⟨hzero, rfl, (le_refl z.re : z.re ≤ z.re), hz1⟩
  obtain ⟨zs, hzsS, hmax⟩ := hSc.exists_isMaxOn ⟨z, hzS⟩ Complex.continuous_re.continuousOn
  have hzs0 : xi zs = 0 := hzsS.1
  have hzsim : zs.im = z.im := hzsS.2.1
  have hzsre : z.re ≤ zs.re := hzsS.2.2.1
  set w₀ : ℂ := (zs - σ j₀) / 2 with hw₀
  have hw₀U : w₀ ∈ U := by show 0 < w₀.re; rw [hw₀]; simp; linarith
  have hpt₀ : (σ j₀ : ℂ) + 2 * w₀ = zs := by rw [hw₀]; ring
  -- the other shifts see non-zeros
  have hother : ∀ j ∈ s, j ≠ j₀ → xi ((σ j : ℂ) + 2 * w₀) ≠ 0 := by
    intro j hj hjj hzj
    have hlt : σ j₀ < σ j := lt_of_le_of_ne (hmin j hj) (fun heq => hjj (hinj hj hj₀ heq.symm))
    set u : ℂ := (σ j : ℂ) + 2 * w₀ with hu
    have hure : u.re = zs.re + (σ j - σ j₀) := by rw [hu, hw₀]; simp; ring
    have huim : u.im = zs.im := by rw [hu, hw₀]; simp; ring
    have hu1 : u.re ≤ 1 := by
      by_contra h1; push Not at h1; exact xi_ne_zero_of_one_le_re h1.le hzj
    have hu2 : u.im = z.im := by rw [huim, hzsim]
    have hu3 : z.re ≤ u.re := by rw [hure]; linarith
    have huS : u ∈ S := ⟨hzj, hu2, hu3, hu1⟩
    have hle : u.re ≤ zs.re := hmax huS
    linarith
  -- residues at `w₀`
  set m : ι → ℕ := fun j => (analyticOrderAt xi ((σ j : ℂ) + 2 * w₀)).toNat with hm
  have hm_other : ∀ j ∈ s, j ≠ j₀ → m j = 0 := by
    intro j hj hjj
    have h0 : analyticOrderAt xi ((σ j : ℂ) + 2 * w₀) = 0 :=
      analyticOrderAt_eq_zero.2 (Or.inr (hother j hj hjj))
    simp [hm, h0]
  have hm₀ : m j₀ ≠ 0 := by
    intro h0
    have hord : analyticOrderAt xi ((σ j₀ : ℂ) + 2 * w₀) = 0 := by
      have := ENat.coe_toNat (xi_order_ne_top ((σ j₀ : ℂ) + 2 * w₀))
      rw [← this]
      simp only [hm] at h0
      rw [h0]
      rfl
    rcases analyticOrderAt_eq_zero.1 hord with h | h
    · exact h (xi_differentiable.analyticAt _)
    · exact h (by rw [hpt₀]; exact hzs0)
  have hlimL : Tendsto (fun w => (w - w₀) * ∑ j ∈ s, (c j : ℂ) * logDeriv xi ((σ j : ℂ) + 2 * w))
      (𝓝[≠] w₀) (𝓝 (∑ j ∈ s, (c j : ℂ) * ((m j : ℂ) / 2))) := by
    have : Tendsto (fun w => ∑ j ∈ s, (c j : ℂ) * ((w - w₀) * logDeriv xi ((σ j : ℂ) + 2 * w)))
        (𝓝[≠] w₀) (𝓝 (∑ j ∈ s, (c j : ℂ) * ((m j : ℂ) / 2))) :=
      tendsto_finsetSum s fun j _ =>
        (tendsto_sub_mul_logDeriv_xi_affine (σ j : ℂ) w₀).const_mul _
    refine this.congr fun w => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hlimK : Tendsto (fun w => (w - w₀) * K w) (𝓝[≠] w₀) (𝓝 0) := by
    have hKc : ContinuousAt K w₀ := (hKd.differentiableAt (hUo.mem_nhds hw₀U)).continuousAt
    have h1 : Tendsto (fun w => (w - w₀) * K w) (𝓝 w₀) (𝓝 ((w₀ - w₀) * K w₀)) :=
      ((continuous_id.sub continuous_const).continuousAt.tendsto).mul hKc.tendsto
    rw [sub_self, zero_mul] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hQev : ∀ᶠ w in 𝓝[≠] w₀, Q w ≠ 0 := by
    have hall : ∀ j ∈ s, ∀ᶠ w in 𝓝[≠] w₀, xi ((σ j : ℂ) + 2 * w) ≠ 0 :=
      fun j _ => xi_affine_eventually_ne_zero _ _
    have hfin : ∀ᶠ w in 𝓝[≠] w₀, ∀ j ∈ s, xi ((σ j : ℂ) + 2 * w) ≠ 0 :=
      (Finset.eventually_all s).2 hall
    filter_upwards [hfin] with w hw
    exact Finset.prod_ne_zero_iff.2 hw
  have hUev : ∀ᶠ w in 𝓝[≠] w₀, w ∈ U := nhdsWithin_le_nhds (hUo.mem_nhds hw₀U)
  have hlimL' : Tendsto (fun w => (w - w₀) * K w) (𝓝[≠] w₀)
      (𝓝 (∑ j ∈ s, (c j : ℂ) * ((m j : ℂ) / 2))) := by
    refine hlimL.congr' ?_
    filter_upwards [hQev, hUev] with w hQw hwU
    have h1 := hRQ w hQw
    have h2 := hid hwU
    simp only at h2
    rw [h2] at h1
    have : K w = ∑ j ∈ s, (c j : ℂ) * logDeriv xi ((σ j : ℂ) + 2 * w) :=
      mul_right_cancel₀ hQw h1
    rw [this]
  have heq := tendsto_nhds_unique hlimL' hlimK
  rw [Finset.sum_eq_single_of_mem j₀ hj₀ (fun j hj hjj => by rw [hm_other j hj hjj]; simp)] at heq
  have hc₀' : (c j₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc₀
  have hm₀' : (m j₀ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm₀
  exact (mul_ne_zero hc₀' (div_ne_zero hm₀' two_ne_zero)) heq

/-- **Differenced budget.**  For `½ < σ < 2`, RH holds iff `(P_½ − C_½) − (P_σ − C_σ)` is bounded above
on `(0, 1]`.  This is the central Gaussian budget of `ζ(s)/ζ(s + σ − ½)`. -/
theorem riemannHypothesis_iff_gaussianDifferenceBudget {σ : ℝ} (hσ : 1 / 2 < σ) (hσ2 : σ < 2) :
    RiemannHypothesis ↔ ∃ B : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      (gaussianWeightedPrimeMass (1 / 2) y - gaussianWeightedContinuumMass (1 / 2) y) -
        (gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y) ≤ B := by
  constructor
  · intro hRH
    have hθ : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ 1 / 2 := fun ρ hρ => by
      by_contra h
      push Not at h
      exact (rh_iff_xi_ne_zero_right.mp hRH) ρ (mem_rightHalf.mpr h) hρ
    obtain ⟨K, hK⟩ := riemannHypothesis_iff_gaussianCentralPrimeBudget.1 hRH
    obtain ⟨B', hB'⟩ := exists_abs_gaussianWeightedGap_le_of_zero_bound hθ hσ (by linarith) hσ2
    refine ⟨K + B', fun y hy hy1 => ?_⟩
    have h1 := hK y hy hy1
    have h2 := neg_abs_le (gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y)
    have h3 := hB' y hy hy1
    linarith
  · rintro ⟨B, hB⟩
    rw [rh_iff_xi_ne_zero_right]
    intro z hz hzero
    have hre : 1 / 2 < z.re := mem_rightHalf.mp hz
    set σf : Bool → ℝ := fun b => if b then σ else 1 / 2 with hσf
    set cf : Bool → ℝ := fun b => if b then -1 else 1 with hcf
    have hpos : ∀ b ∈ (Finset.univ : Finset Bool), 0 < σf b := by
      intro b _; cases b <;> simp [hσf]; linarith
    have hinj : Set.InjOn σf (Finset.univ : Finset Bool) := by
      intro a _ b _ hab
      cases a <;> cases b <;> simp [hσf] at hab ⊢ <;> linarith
    have hminb : ∀ b ∈ (Finset.univ : Finset Bool), σf false ≤ σf b := by
      intro b _; cases b <;> simp [hσf]; linarith
    have hBm : ∀ y : ℝ, 0 < y → y ≤ 1 →
        gaussianSignedMixtureGap Finset.univ cf σf y ≤ B := by
      intro y hy hy1
      have := hB y hy hy1
      rw [gaussianSignedMixtureGap, Fintype.sum_bool]
      simp only [hσf, hcf, if_true, Bool.false_eq_true, if_false]
      linarith
    exact xi_ne_zero_of_gaussianSignedMixtureBudget hpos hinj (Finset.mem_univ false)
      (by simp [hcf]) hminb hBm (by simpa [hσf] using hre) hzero

end

end RHTower
