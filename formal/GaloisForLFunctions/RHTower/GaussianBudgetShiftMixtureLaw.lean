import GaloisForLFunctions.RHTower.GaussianPrimeGapExponentLaw
import GaloisForLFunctions.HTGeometry.LogDerivNoZero

/-!
# Positive mixtures of Gaussian budgets: the smallest shift decides

For a finite family of shifts `σ_j > 0` (repetitions allowed, so integer weights are included) let

  `M(y) = Σ_j (P_{σ_j} − C_{σ_j})(y)`,  `P_σ(y) = Σ Λ(n) n^{-σ} e^{-yn²}`,  `C_σ(y) = ∫₁^∞ u^{-σ} e^{-yu²} du`.

* **Mixture law** (`xi_ne_zero_of_gaussianMixtureBudget`).  If `M(y) ≤ B` on `(0, 1]`, then `ξ` has
  no zero with `Re z > σ_j` for any `j`: the smallest shift decides.  In the logarithmic variable the
  deficit `B − M(e^{-u})` is a nonnegative Laplace carrier with transform
  `B/w − Σ_j (Γ(w)(A − ξ'/ξ)(σ_j + 2w) − T_j(w)) + 1/(w+1)`; Landau's theorem continues it to
  `Re w > 0`, so `Σ_j ξ'/ξ(σ_j + 2w)` is holomorphic there.  This sum is half the logarithmic
  derivative of `H(w) = Π_j ξ(σ_j + 2w)`, so `H' = K H` with `K` holomorphic on `Re w > 0`, and `H`
  has no zero there.  A zero of one factor cannot be cancelled by the others because every zero of
  `ξ` contributes a positive multiplicity to `H`.
* **Abscissa form** (`xi_zero_re_le_of_gaussianMixtureBudget`, `exists_gaussianMixtureBudget_of_zero_bound`).
  The mixture budget holds if all zeros lie left of every shift and forces all zeros to lie left of
  the smallest shift.
* **Temperedness gate** (`not_exists_gaussianEisensteinBudget`).  The Euler product
  `ζ(s − a) ζ(s + a)` has a functional equation, nonnegative von Mangoldt coefficients
  `Λ(n)(n^a + n^{-a})`, and central Gaussian prime gap `(P_{½−a} − C_{½−a}) + (P_{½+a} − C_{½+a})`.
  For `0 < a < ½` this gap is unbounded above on `(0, 1]`, unconditionally: critical-line zeros lie
  right of the shift `½ − a`.  A producer of the central budget of `ζ` must therefore use the size of
  the coefficients, not only positivity, the Euler product and the functional equation.
* **RH as a mixture budget** (`riemannHypothesis_iff_gaussianMixtureBudget`).  For shifts in
  `[½, 2)` with smallest shift `½`, RH holds iff the mixture budget holds.
-/

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.RHTower (laplaceMass complexLaplace IsAbscissa exists_isAbscissa
  differentiableOn_complexLaplace)

namespace RHTower

noncomputable section

open XiAtlasFinitePart

variable {ι : Type*}

/-- The Gaussian mixture gap `Σ_{j ∈ s} (P_{σ_j} − C_{σ_j})(y)`. -/
def gaussianMixtureGap (s : Finset ι) (σ : ι → ℝ) (y : ℝ) : ℝ :=
  ∑ j ∈ s, (gaussianWeightedPrimeMass (σ j) y - gaussianWeightedContinuumMass (σ j) y)

theorem gaussianWeightedGap_exp_eq_neg_profile (σ u : ℝ) :
    gaussianWeightedPrimeMass σ (Real.exp (-u)) - gaussianWeightedContinuumMass σ (Real.exp (-u)) =
      -gaussianBudgetProfile 1 σ 0 0 u := by
  simp [gaussianBudgetProfile]

theorem continuous_gaussianMixtureGap_exp {s : Finset ι} {σ : ι → ℝ} (hσ : ∀ j ∈ s, 0 < σ j) :
    Continuous fun u : ℝ => gaussianMixtureGap s σ (Real.exp (-u)) := by
  unfold gaussianMixtureGap
  refine continuous_finsetSum s fun j hj => ?_
  simp_rw [gaussianWeightedGap_exp_eq_neg_profile]
  exact (continuous_gaussianBudgetProfile (hσ j hj) 1 0 0).neg

/-- **Laplace transform of the mixture deficit** for `Re w > 3`. -/
theorem integral_gaussianMixtureDeficit_mul_cexp {s : Finset ι} {σ : ι → ℝ}
    (hσ : ∀ j ∈ s, 0 < σ j) (B : ℝ) {w : ℂ} (hw : 3 < w.re) :
    IntegrableOn (fun u : ℝ => ((B - gaussianMixtureGap s σ (Real.exp (-u)) : ℝ) : ℂ) *
        Complex.exp (-w * u)) (Ioi 0) ∧
    ∫ u in Ioi (0 : ℝ), ((B - gaussianMixtureGap s σ (Real.exp (-u)) : ℝ) : ℂ) *
        Complex.exp (-w * u) =
      B / w - ∑ j ∈ s, (Complex.Gamma w * (gaussianArchimedeanCurrent ((σ j : ℂ) + 2 * w) -
        logDeriv xi ((σ j : ℂ) + 2 * w)) -
          mellin ((Ioi (1 : ℝ)).indicator (gaussianPrimeContinuumGap (σ j : ℂ))) w) := by
  have hpt : ∀ u : ℝ, ((B - gaussianMixtureGap s σ (Real.exp (-u)) : ℝ) : ℂ) *
      Complex.exp (-w * u) = (B : ℂ) * Complex.exp (-w * u) +
        ∑ j ∈ s, (gaussianBudgetProfile 1 (σ j) 0 0 u : ℂ) * Complex.exp (-w * u) := by
    intro u
    simp only [gaussianMixtureGap, gaussianWeightedGap_exp_eq_neg_profile, Finset.sum_neg_distrib,
      sub_neg_eq_add]
    push_cast
    rw [add_mul, Finset.sum_mul]
  have hre : (-w).re < 0 := by simp; linarith
  have hiB : IntegrableOn (fun u : ℝ => (B : ℂ) * Complex.exp (-w * u)) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi hre 0).const_mul _
  have hij : ∀ j ∈ s, IntegrableOn
      (fun u : ℝ => (gaussianBudgetProfile 1 (σ j) 0 0 u : ℂ) * Complex.exp (-w * u)) (Ioi 0) :=
    fun j hj => integrableOn_gaussianBudgetProfile_mul_cexp (hσ j hj) (by norm_num) (by norm_num)
      0 hw
  have hisum : IntegrableOn (fun u : ℝ =>
      ∑ j ∈ s, (gaussianBudgetProfile 1 (σ j) 0 0 u : ℂ) * Complex.exp (-w * u)) (Ioi 0) :=
    integrable_finsetSum s hij
  refine ⟨(hiB.add hisum).congr_fun (fun u _ => (hpt u).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hpt u), integral_add hiB hisum,
    integral_finsetSum s hij, integral_const_mul, integral_exp_mul_complex_Ioi hre 0]
  have hterm : ∀ j ∈ s, ∫ u in Ioi (0 : ℝ),
      (gaussianBudgetProfile 1 (σ j) 0 0 u : ℂ) * Complex.exp (-w * u) =
      -(Complex.Gamma w * (gaussianArchimedeanCurrent ((σ j : ℂ) + 2 * w) -
        logDeriv xi ((σ j : ℂ) + 2 * w)) -
          mellin ((Ioi (1 : ℝ)).indicator (gaussianPrimeContinuumGap (σ j : ℂ))) w) := by
    intro j hj
    rw [integral_gaussianBudgetProfile_mul_cexp (hσ j hj) 1 (a := 0) (by norm_num) 0 hw,
      mellin_gap_eq_gamma_mul (hσ j hj) hw]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
  push_cast
  simp only [mul_zero, Complex.exp_zero]
  ring

/-- **Mixture law.**  If the mixture gap `Σ_j (P_{σ_j} − C_{σ_j})` is bounded above on `(0, 1]`,
then `ξ` has no zero with `Re z > σ_j`, for every shift `σ_j` of the family. -/
theorem xi_ne_zero_of_gaussianMixtureBudget {s : Finset ι} {σ : ι → ℝ} (hσ : ∀ j ∈ s, 0 < σ j)
    {B : ℝ} (hB : ∀ y : ℝ, 0 < y → y ≤ 1 → gaussianMixtureGap s σ y ≤ B)
    {j₀ : ι} (hj₀ : j₀ ∈ s) {z : ℂ} (hz : σ j₀ < z.re) : xi z ≠ 0 := by
  set h : ℝ → ℝ := fun u => B - gaussianMixtureGap s σ (Real.exp (-u)) with hhdef
  have hc : Continuous h := continuous_const.sub (continuous_gaussianMixtureGap_exp hσ)
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
  -- the transform right of `3`
  have hfar : ∀ w : ℂ, 3 < w.re → complexLaplace ν w =
      B / w - ∑ j ∈ s, (Complex.Gamma w * (gaussianArchimedeanCurrent ((σ j : ℂ) + 2 * w) -
        logDeriv xi ((σ j : ℂ) + 2 * w)) - T j w) + 1 / (w + 1) := by
    intro w hw
    obtain ⟨hint, hval⟩ := integral_gaussianMixtureDeficit_mul_cexp hσ B hw
    have hint' : IntegrableOn (fun u : ℝ => ((max (h u) 0 : ℝ) : ℂ) * Complex.exp (-w * u))
        (Ioi 0) :=
      hint.congr_fun (fun u hu => by simp only [hhdef] at hPeq ⊢; rw [hPeq u hu]) measurableSet_Ioi
    rw [hν, complexLaplace_expThickenedCarrier hPc hP0 (by linarith) hint',
      setIntegral_congr_fun measurableSet_Ioi (fun u hu => by rw [hPeq u hu]), hval]
  -- the continuation candidate, analytic at every positive real point
  set Ψ : ℂ → ℂ := fun w => B / w - ∑ j ∈ s, (Complex.Gamma w *
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
    have hsum : DifferentiableAt ℂ (fun w => ∑ j ∈ s, (Complex.Gamma w *
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
      exact (hΓ.mul (hA.sub hL)).sub (hTd j hj w)
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (((differentiableAt_const _).div differentiableAt_id hwne).sub hsum).add
      ((differentiableAt_const _).div (by fun_prop) hw1)
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
    obtain ⟨hint, -⟩ := integral_gaussianMixtureDeficit_mul_cexp hσ B (w := (4 : ℝ))
      (by simp; norm_num)
    refine integrableOn_real_mul_exp_of_cexp hPc ?_
    refine hint.congr_fun (fun u hu => ?_) measurableSet_Ioi
    simp only [hhdef] at hPeq ⊢
    rw [hPeq u hu]
  obtain ⟨c, hcP⟩ := exists_isAbscissa
    ⟨4, laplaceMass_expThickenedCarrier_ne_top hPc hP0 (by norm_num) hiP4⟩
    ⟨-2, laplaceMass_expThickenedCarrier_eq_top hPc hP0⟩
  have hab : ∃ c₀ : ℝ, IsAbscissa ν c₀ ∧ c₀ ≤ 0 := by
    by_cases hc0 : c ≤ 0
    · exact ⟨c, hcP, hc0⟩
    · push Not at hc0
      refine ⟨0, RHTower.LiouvilleTriangularHeadOscillation.isAbscissa_eq_of_analyticAt_real hcP
        hc0.le (le_max_left c 4) (fun t ht => hΨan t ht) (fun w hw => ?_), le_rfl⟩
      have hw3 : 3 < w.re := lt_of_le_of_lt (by have := le_max_right c 4; linarith) hw
      exact hfar w hw3
  obtain ⟨c₀, hc₀, hc₀0⟩ := hab
  have hLd : DifferentiableOn ℂ (complexLaplace ν) {w : ℂ | 0 < w.re} :=
    (differentiableOn_complexLaplace hc₀).mono fun w hw => lt_of_le_of_lt hc₀0 hw
  -- the holomorphic logarithmic derivative of `H(w) = Π_j ξ(σ_j + 2w)`
  set U : Set ℂ := {w : ℂ | 0 < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  set K : ℂ → ℂ := fun w => 2 * (∑ j ∈ s, gaussianArchimedeanCurrent ((σ j : ℂ) + 2 * w) -
      (B / w + 1 / (w + 1) - complexLaplace ν w + ∑ j ∈ s, T j w) * (Complex.Gamma w)⁻¹) with hK
  have hKd : DifferentiableOn ℂ K U := by
    intro w hw
    have hw0 : 0 < w.re := hw
    have hwne : w ≠ 0 := by intro h; rw [h] at hw0; simp at hw0
    have hw1 : w + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hA : DifferentiableAt ℂ (fun w => ∑ j ∈ s, gaussianArchimedeanCurrent ((σ j : ℂ) + 2 * w))
        w := by
      refine DifferentiableAt.fun_sum fun j hj => ?_
      have hre : 0 < ((σ j : ℂ) + 2 * w).re := by simp; linarith [hσ j hj]
      exact (differentiableAt_gaussianArchimedeanCurrent hre).comp
        (f := fun w : ℂ => (σ j : ℂ) + 2 * w) w (by fun_prop)
    have hTs : DifferentiableAt ℂ (fun w => ∑ j ∈ s, T j w) w :=
      DifferentiableAt.fun_sum fun j hj => hTd j hj w
    have hLw : DifferentiableAt ℂ (complexLaplace ν) w := hLd.differentiableAt (hUo.mem_nhds hw)
    have hBw : DifferentiableAt ℂ (fun w : ℂ => (B : ℂ) / w) w :=
      (differentiableAt_const _).div differentiableAt_id hwne
    have hOw : DifferentiableAt ℂ (fun w : ℂ => 1 / (w + 1)) w :=
      (differentiableAt_const _).div (differentiableAt_id.add (differentiableAt_const _)) hw1
    have hinner : DifferentiableAt ℂ (fun w => (B / w + 1 / (w + 1) - complexLaplace ν w +
        ∑ j ∈ s, T j w) * (Complex.Gamma w)⁻¹) w :=
      (((hBw.add hOw).sub hLw).add hTs).mul (Complex.differentiable_one_div_Gamma w)
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (differentiableAt_const _).mul (hA.sub hinner)
  set H : ℂ → ℂ := fun w => ∏ j ∈ s, xi ((σ j : ℂ) + 2 * w) with hH
  have hHd : Differentiable ℂ H := by
    have := Differentiable.finsetProd (u := s) (f := fun j w => xi ((σ j : ℂ) + 2 * w))
      (fun j _ => xi_differentiable.comp (by fun_prop))
    have hfun : (∏ j ∈ s, fun w : ℂ => xi ((σ j : ℂ) + 2 * w)) = H := by
      funext w; rw [Finset.prod_apply]
    rwa [hfun] at this
  have hrelfar : ∀ w : ℂ, 3 < w.re → deriv H w = K w * H w := by
    intro w hw
    have hxw : ∀ j ∈ s, xi ((σ j : ℂ) + 2 * w) ≠ 0 := fun j hj =>
      xi_ne_zero_of_one_lt_re (by simp; linarith [hσ j hj])
    have hHw : H w ≠ 0 := Finset.prod_ne_zero_iff.2 hxw
    have hdj : ∀ j ∈ s, DifferentiableAt ℂ (fun w => xi ((σ j : ℂ) + 2 * w)) w :=
      fun j _ => (xi_differentiable.comp (by fun_prop : Differentiable ℂ
        fun w : ℂ => (σ j : ℂ) + 2 * w)) w
    have hlog : logDeriv H w = 2 * ∑ j ∈ s, logDeriv xi ((σ j : ℂ) + 2 * w) := by
      rw [hH, logDeriv_prod (f := fun j w => xi ((σ j : ℂ) + 2 * w)) (fun j hj => hxw j hj) hdj,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hc := logDeriv_comp (f := xi) (g := fun w : ℂ => (σ j : ℂ) + 2 * w) (x := w)
        (xi_differentiable _) (by fun_prop)
      rw [show (xi ∘ fun w : ℂ => (σ j : ℂ) + 2 * w) = fun w => xi ((σ j : ℂ) + 2 * w) from rfl]
        at hc
      rw [hc]
      have hd : deriv (fun w : ℂ => (σ j : ℂ) + 2 * w) w = 2 := by
        have := (((hasDerivAt_id w).const_mul (2 : ℂ)).const_add (σ j : ℂ)).deriv
        simp only [id, mul_one] at this
        exact this
      rw [hd]
      ring
    have hKw : K w = 2 * ∑ j ∈ s, logDeriv xi ((σ j : ℂ) + 2 * w) := by
      have hΓ : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
      have hcore : B / w + 1 / (w + 1) - complexLaplace ν w + ∑ j ∈ s, T j w =
          Complex.Gamma w * ∑ j ∈ s, (gaussianArchimedeanCurrent ((σ j : ℂ) + 2 * w) -
            logDeriv xi ((σ j : ℂ) + 2 * w)) := by
        rw [hfar w hw, Finset.mul_sum]
        have : ∑ j ∈ s, (Complex.Gamma w * (gaussianArchimedeanCurrent ((σ j : ℂ) + 2 * w) -
            logDeriv xi ((σ j : ℂ) + 2 * w)) - T j w) =
            ∑ j ∈ s, Complex.Gamma w * (gaussianArchimedeanCurrent ((σ j : ℂ) + 2 * w) -
              logDeriv xi ((σ j : ℂ) + 2 * w)) - ∑ j ∈ s, T j w := Finset.sum_sub_distrib _ _
        rw [this]
        ring
      simp only [hK]
      rw [hcore, mul_comm (Complex.Gamma w), mul_assoc, mul_inv_cancel₀ hΓ, mul_one,
        ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hKw, ← hlog, logDeriv_apply]
    field_simp
  -- extend the relation to `Re w > 0` and conclude
  have hanaL : AnalyticOnNhd ℂ (deriv H) U := fun w _ => (hHd.analyticAt w).deriv
  have hanaR : AnalyticOnNhd ℂ (fun w => K w * H w) U :=
    (hKd.mul hHd.differentiableOn).analyticOnNhd hUo
  have hw₄ : ((4 : ℝ) : ℂ) ∈ U := by show (0 : ℝ) < ((4 : ℝ) : ℂ).re; simp
  have hev : deriv H =ᶠ[𝓝 ((4 : ℝ) : ℂ)] fun w => K w * H w := by
    have hopen : IsOpen {w : ℂ | 3 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have h43 : (3 : ℝ) < ((4 : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; norm_num
    filter_upwards [hopen.mem_nhds h43] with w hw
    exact hrelfar w hw
  have hid := hanaL.eqOn_of_preconnected_of_eventuallyEq hanaR
    (convex_halfSpace_re_gt 0).isPreconnected hw₄ hev
  have hH4 : H ((4 : ℝ) : ℂ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j hj =>
    xi_ne_zero_of_one_lt_re (by simp; linarith [hσ j hj])
  have hnz := GaloisForLFunctions.HTGeometry.ne_zero_of_deriv_eq_mul hUo
    (convex_halfSpace_re_gt 0).isPreconnected (fun w _ => hHd.analyticAt w)
    (hKd.analyticOnNhd hUo) (fun w hw => hid hw) hw₄ hH4
  set w₀ : ℂ := (z - σ j₀) / 2 with hw₀
  have hw₀U : w₀ ∈ U := by show 0 < w₀.re; rw [hw₀]; simp; linarith
  have hfac := (Finset.prod_ne_zero_iff.1 (hnz w₀ hw₀U)) j₀ hj₀
  rwa [hw₀, show (σ j₀ : ℂ) + 2 * ((z - σ j₀) / 2) = z by ring] at hfac

/-- **Abscissa form of the mixture law.**  A mixture budget forces every zero of `ξ` to lie left of
every shift of the family. -/
theorem xi_zero_re_le_of_gaussianMixtureBudget {s : Finset ι} {σ : ι → ℝ} (hσ : ∀ j ∈ s, 0 < σ j)
    {B : ℝ} (hB : ∀ y : ℝ, 0 < y → y ≤ 1 → gaussianMixtureGap s σ y ≤ B)
    {ρ : ℂ} (hρ : xi ρ = 0) {j : ι} (hj : j ∈ s) : ρ.re ≤ σ j := by
  by_contra hlt
  push Not at hlt
  exact xi_ne_zero_of_gaussianMixtureBudget hσ hB hj hlt hρ

/-- **Converse.**  If all zeros satisfy `Re ρ ≤ θ` and every shift lies in `(max θ 0, 2)`, the
mixture budget holds. -/
theorem exists_gaussianMixtureBudget_of_zero_bound {θ : ℝ}
    (hθ : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ θ) {s : Finset ι} {σ : ι → ℝ}
    (hσ : ∀ j ∈ s, θ < σ j ∧ 0 < σ j ∧ σ j < 2) :
    ∃ B : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → gaussianMixtureGap s σ y ≤ B := by
  classical
  have hloc : ∀ j ∈ s, ∃ B : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      |gaussianWeightedPrimeMass (σ j) y - gaussianWeightedContinuumMass (σ j) y| ≤ B :=
    fun j hj => exists_abs_gaussianWeightedGap_le_of_zero_bound hθ (hσ j hj).1 (hσ j hj).2.1
      (hσ j hj).2.2
  choose! Bf hBf using hloc
  refine ⟨∑ j ∈ s, Bf j, fun y hy hy1 => ?_⟩
  unfold gaussianMixtureGap
  exact Finset.sum_le_sum fun j hj => (le_abs_self _).trans (hBf j hj y hy hy1)

/-- **RH as a mixture budget.**  For shifts in `[½, 2)` whose smallest member is `½`, RH holds iff
the mixture gap is bounded above on `(0, 1]`. -/
theorem riemannHypothesis_iff_gaussianMixtureBudget {s : Finset ι} {σ : ι → ℝ}
    (hσ : ∀ j ∈ s, 1 / 2 ≤ σ j ∧ σ j < 2) {j₀ : ι} (hj₀ : j₀ ∈ s) (hmin : σ j₀ = 1 / 2) :
    RiemannHypothesis ↔ ∃ B : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → gaussianMixtureGap s σ y ≤ B := by
  classical
  have hpos : ∀ j ∈ s, 0 < σ j := fun j hj => lt_of_lt_of_le (by norm_num) (hσ j hj).1
  constructor
  · intro hRH
    have hθ : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ 1 / 2 := fun ρ hρ => by
      by_contra h
      push Not at h
      exact (rh_iff_xi_ne_zero_right.mp hRH) ρ (mem_rightHalf.mpr h) hρ
    obtain ⟨K, hK⟩ := riemannHypothesis_iff_gaussianCentralPrimeBudget.1 hRH
    have hloc : ∀ j ∈ s, ∃ B : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
        gaussianWeightedPrimeMass (σ j) y - gaussianWeightedContinuumMass (σ j) y ≤ B := by
      intro j hj
      rcases (hσ j hj).1.lt_or_eq with hlt | heq
      · obtain ⟨B, hB⟩ := exists_abs_gaussianWeightedGap_le_of_zero_bound hθ hlt (hpos j hj)
          (hσ j hj).2
        exact ⟨B, fun y hy hy1 => (le_abs_self _).trans (hB y hy hy1)⟩
      · refine ⟨K, fun y hy hy1 => ?_⟩
        rw [← heq]
        linarith [hK y hy hy1]
    choose! Bf hBf using hloc
    exact ⟨∑ j ∈ s, Bf j, fun y hy hy1 => Finset.sum_le_sum fun j hj => hBf j hj y hy hy1⟩
  · rintro ⟨B, hB⟩
    rw [rh_iff_xi_ne_zero_right]
    intro z hz hzero
    have hre : 1 / 2 < z.re := mem_rightHalf.mp hz
    have := xi_zero_re_le_of_gaussianMixtureBudget hpos hB hzero hj₀
    rw [hmin] at this
    linarith

/-- The Eisenstein shift pair `½ ∓ a`, indexed by `Bool`. -/
def eisensteinShift (a : ℝ) (b : Bool) : ℝ := if b then 1 / 2 + a else 1 / 2 - a

/-- The central Gaussian gap of `ζ(s − a) ζ(s + a)`, whose von Mangoldt coefficients are
`Λ(n)(n^a + n^{-a})`: the sum of the gaps of `ζ` at `½ − a` and `½ + a`. -/
theorem gaussianMixtureGap_eisensteinShift (a y : ℝ) :
    gaussianMixtureGap Finset.univ (eisensteinShift a) y =
      (gaussianWeightedPrimeMass (1 / 2 - a) y - gaussianWeightedContinuumMass (1 / 2 - a) y) +
        (gaussianWeightedPrimeMass (1 / 2 + a) y - gaussianWeightedContinuumMass (1 / 2 + a) y) := by
  rw [gaussianMixtureGap, Fintype.sum_bool]
  simp only [eisensteinShift, if_true, Bool.false_eq_true, if_false]
  ring

/-- **Temperedness gate for the Gaussian budget.**  For `0 < a < ½` the central Gaussian prime gap
of the non-tempered Euler product `ζ(s − a) ζ(s + a)` is unbounded above on `(0, 1]`.  The product
has a functional equation and nonnegative von Mangoldt coefficients; its zeros `ρ ± a` include
points right of the line whenever `ζ` has a critical zero, which it does. -/
theorem not_exists_gaussianEisensteinBudget {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) :
    ¬ ∃ B : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      (gaussianWeightedPrimeMass (1 / 2 - a) y - gaussianWeightedContinuumMass (1 / 2 - a) y) +
        (gaussianWeightedPrimeMass (1 / 2 + a) y - gaussianWeightedContinuumMass (1 / 2 + a) y)
          ≤ B := by
  rintro ⟨B, hB⟩
  have hpos : ∀ b ∈ (Finset.univ : Finset Bool), 0 < eisensteinShift a b := by
    intro b _
    cases b <;> simp [eisensteinShift] <;> linarith
  have hB' : ∀ y : ℝ, 0 < y → y ≤ 1 → gaussianMixtureGap Finset.univ (eisensteinShift a) y ≤ B :=
    fun y hy hy1 => by rw [gaussianMixtureGap_eisensteinShift]; exact hB y hy hy1
  obtain ⟨ρ, hρ, hre⟩ := exists_xi_zero_re_eq_half
  have := xi_zero_re_le_of_gaussianMixtureBudget hpos hB' hρ (Finset.mem_univ false)
  simp only [eisensteinShift, Bool.false_eq_true, if_false] at this
  linarith

end

end RHTower
