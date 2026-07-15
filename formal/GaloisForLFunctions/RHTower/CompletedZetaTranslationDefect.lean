import GaloisForLFunctions.RHTower.EulerTranslationAnalyticFaithful
import GaloisForLFunctions.HTGeometry.GammaDifferentialFE

/-!
# The concrete completed-zeta translation defect

The archimedean curvature term in the differentiated completed-zeta logarithmic derivative has an
explicit rational two-step difference.  This file derives that fact from the already formalized
trigamma recurrence, removing the abstract `hRat` input from the original completion theorem.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The trigamma function in the normalization used by the completed zeta factor. -/
def trigamma (s : ℂ) : ℂ :=
  deriv (fun z => deriv Complex.Gamma z / Complex.Gamma z) s

/-- The archimedean curvature summand in `(Xi'/Xi)'`. -/
def completedZetaArchimedeanCurvature (s : ℂ) : ℂ :=
  -1 / s ^ 2 - 1 / (s - 1) ^ 2 + (1 / 4) * trigamma (s / 2)

/-- The explicit rational response of the archimedean curvature under `s ↦ s+2`. -/
def completedZetaArchimedeanShiftRational (s : ℂ) : ℂ :=
  -1 / (s + 2) ^ 2 - 1 / (s + 1) ^ 2 + 1 / (s - 1) ^ 2

/-- The trigamma recurrence makes the two-step archimedean translation difference literally
rational on the right half-plane. -/
theorem completedZetaArchimedeanCurvature_add_two_sub
    {s : ℂ} (hs : 2 < s.re) :
    completedZetaArchimedeanCurvature (s + 2) -
        completedZetaArchimedeanCurvature s =
      completedZetaArchimedeanShiftRational s := by
  have hoff : ∀ p : ℕ, s / 2 ≠ -(p : ℂ) := by
    intro p hp
    have hre := congrArg Complex.re hp
    norm_num [Complex.div_re] at hre
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    nlinarith
  have hrec := GaloisForLFunctions.trigamma_recurrence (s / 2) hoff
  have hshift : (s + 2) / 2 = s / 2 + 1 := by ring
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have hsm1 : s - 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hre
    linarith
  have hsp1 : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
    linarith
  have hsp2 : s + 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have htriDiff :
      (1 / 4) * trigamma ((s + 2) / 2) - (1 / 4) * trigamma (s / 2) =
        -1 / s ^ 2 := by
    rw [hshift, trigamma, trigamma, hrec]
    field_simp [hs0]
    ring
  rw [completedZetaArchimedeanCurvature, completedZetaArchimedeanCurvature,
    completedZetaArchimedeanShiftRational]
  calc
    (-1 / (s + 2) ^ 2 - 1 / (s + 2 - 1) ^ 2 + (1 / 4) * trigamma ((s + 2) / 2)) -
          (-1 / s ^ 2 - 1 / (s - 1) ^ 2 + (1 / 4) * trigamma (s / 2)) =
        (-1 / (s + 2) ^ 2 - 1 / (s + 1) ^ 2 + 1 / s ^ 2 + 1 / (s - 1) ^ 2) +
          ((1 / 4) * trigamma ((s + 2) / 2) - (1 / 4) * trigamma (s / 2)) := by ring
    _ = -1 / (s + 2) ^ 2 - 1 / (s + 1) ^ 2 + 1 / (s - 1) ^ 2 := by
      rw [htriDiff]
      ring

/-- The finite translation operator `T₂ - 1`. -/
def twoStepTranslationOperator : AddMonoidAlgebra ℂ ℂ :=
  AddMonoidAlgebra.single (2 : ℂ) 1 - 1

theorem twoStepTranslationOperator_ne_zero : twoStepTranslationOperator ≠ 0 := by
  rw [twoStepTranslationOperator, sub_ne_zero]
  intro h
  have hcoe : (AddMonoidAlgebra.single (2 : ℂ) (1 : ℂ)) (2 : ℂ) =
      (1 : AddMonoidAlgebra ℂ ℂ) (2 : ℂ) := congrArg (fun f => f (2 : ℂ)) h
  rw [AddMonoidAlgebra.single_apply, AddMonoidAlgebra.one_def,
    AddMonoidAlgebra.single_apply, if_pos rfl, if_neg (by norm_num : ¬ (0 : ℂ) = 2)] at hcoe
  exact one_ne_zero hcoe

private theorem finiteTranslationAction_twoStep_sub_one
    (f : ℂ → ℂ) (s : ℂ) :
    finiteTranslationAction twoStepTranslationOperator f s = f (s + 2) - f s := by
  rw [finiteTranslationAction]
  change twoStepTranslationOperator.sum (fun h c => c * f (s + h)) = _
  have hop : twoStepTranslationOperator =
      AddMonoidAlgebra.single (2 : ℂ) 1 + AddMonoidAlgebra.single 0 (-1) := by
    rw [twoStepTranslationOperator, AddMonoidAlgebra.one_def, sub_eq_add_neg]
    congr 1
    exact (Finsupp.single_neg (0 : ℂ) (1 : ℂ)).symm
  rw [hop]
  calc
    (AddMonoidAlgebra.single (2 : ℂ) (1 : ℂ) +
        AddMonoidAlgebra.single 0 (-1 : ℂ)).sum
          (fun h c => c * f (s + h)) =
        (AddMonoidAlgebra.single (2 : ℂ) (1 : ℂ)).sum (fun h c => c * f (s + h)) +
          (AddMonoidAlgebra.single (0 : ℂ) (-1 : ℂ)).sum
            (fun h c => c * f (s + h)) := by
      apply Finsupp.sum_add_index'
      · intro h
        simp
      · intro h b₁ b₂
        ring
    _ = f (s + 2) - f s := by
      rw [Finsupp.sum_single_index, Finsupp.sum_single_index]
      · ring
      · simp
      · simp

/-- The literal `T₂-1` action on the archimedean curvature equals its explicit rational response. -/
theorem finiteTranslationAction_completedZetaArchimedeanCurvature
    {s : ℂ} (hs : 2 < s.re) :
    finiteTranslationAction twoStepTranslationOperator
        completedZetaArchimedeanCurvature s =
      completedZetaArchimedeanShiftRational s := by
  rw [finiteTranslationAction_twoStep_sub_one]
  exact completedZetaArchimedeanCurvature_add_two_sub hs

private theorem ratFunc_eval_mk_of_eval_ne_zero
    (p q : Polynomial ℂ) (s : ℂ) (hqeval : q.eval s ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) s (RatFunc.mk p q) = p.eval s / q.eval s := by
  let R : RatFunc ℂ := RatFunc.mk p q
  have hq : q ≠ 0 := by
    intro h
    apply hqeval
    rw [h]
    simp
  have hdvd : R.denom ∣ q := by
    dsimp [R]
    rw [RatFunc.mk_eq_div]
    exact RatFunc.denom_div_dvd p q
  have hden : R.denom.eval s ≠ 0 := by
    intro h
    exact hqeval (Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdvd h)
  have hden₂ : Polynomial.eval₂ (RingHom.id ℂ) s R.denom ≠ 0 := by
    simpa only [Polynomial.eval₂_id] using hden
  have hqden : Polynomial.eval₂ (RingHom.id ℂ) s
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) q).denom ≠ 0 := by
    simp
  have hfield : R * algebraMap (Polynomial ℂ) (RatFunc ℂ) q =
      algebraMap (Polynomial ℂ) (RatFunc ℂ) p := by
    dsimp [R]
    rw [RatFunc.mk_eq_div]
    exact div_mul_cancel₀ _ (RatFunc.algebraMap_ne_zero hq)
  have hprod := RatFunc.eval_mul (RingHom.id ℂ) s hden₂ hqden
  rw [hfield] at hprod
  simp only [RatFunc.eval_algebraMap, Polynomial.eval₂_id] at hprod
  exact (eq_div_iff hqeval).mpr hprod.symm

/-- Common denominator for the rational archimedean two-step response. -/
def completedZetaArchimedeanShiftDenominator : Polynomial ℂ :=
  (Polynomial.X + 2) ^ 2 * (Polynomial.X + 1) ^ 2 * (Polynomial.X - 1) ^ 2

/-- Common numerator for the rational archimedean two-step response. -/
def completedZetaArchimedeanShiftNumerator : Polynomial ℂ :=
  -((Polynomial.X + 1) ^ 2 * (Polynomial.X - 1) ^ 2) -
    ((Polynomial.X + 2) ^ 2 * (Polynomial.X - 1) ^ 2) +
    ((Polynomial.X + 2) ^ 2 * (Polynomial.X + 1) ^ 2)

/-- The rational function represented by the archimedean two-step response. -/
def completedZetaArchimedeanShiftRatFunc : RatFunc ℂ :=
  RatFunc.mk completedZetaArchimedeanShiftNumerator
    completedZetaArchimedeanShiftDenominator

theorem completedZetaArchimedeanShiftRatFunc_eval
    {x : ℝ} (hx : 2 < x) :
    RatFunc.eval (RingHom.id ℂ) (x : ℂ) completedZetaArchimedeanShiftRatFunc =
      completedZetaArchimedeanShiftRational x := by
  have hxm1 : (x : ℂ) - 1 ≠ 0 := by exact_mod_cast (by linarith : x - 1 ≠ 0)
  have hxp1 : (x : ℂ) + 1 ≠ 0 := by exact_mod_cast (by linarith : x + 1 ≠ 0)
  have hxp2 : (x : ℂ) + 2 ≠ 0 := by exact_mod_cast (by linarith : x + 2 ≠ 0)
  have hqeval : completedZetaArchimedeanShiftDenominator.eval (x : ℂ) ≠ 0 := by
    simp only [completedZetaArchimedeanShiftDenominator, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_ofNat, Polynomial.eval_one]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hxp2) (pow_ne_zero _ hxp1))
      (pow_ne_zero _ hxm1)
  rw [completedZetaArchimedeanShiftRatFunc,
    ratFunc_eval_mk_of_eval_ne_zero _ _ _ hqeval]
  simp only [completedZetaArchimedeanShiftNumerator,
    completedZetaArchimedeanShiftDenominator, completedZetaArchimedeanShiftRational,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_neg, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
  field_simp [hxm1, hxp1, hxp2]

/-- The concrete archimedean constraint `(T₂-1)a∞ ∈ ℂ(s)`, with no abstract rationality
hypothesis. -/
theorem twoStepTranslation_archimedean_is_rational :
    ∀ x : ℝ, 2 < x →
      finiteTranslationAction twoStepTranslationOperator
          completedZetaArchimedeanCurvature x =
        RatFunc.eval (RingHom.id ℂ) (x : ℂ)
          completedZetaArchimedeanShiftRatFunc := by
  intro x hx
  rw [finiteTranslationAction_completedZetaArchimedeanCurvature hx,
    completedZetaArchimedeanShiftRatFunc_eval hx]

private theorem polynomial_eval_ofReal_eventually_ne_zero
    (q : Polynomial ℂ) (hq : q ≠ 0) :
    ∀ᶠ x : ℝ in atTop, q.eval (x : ℂ) ≠ 0 := by
  classical
  let B : ℝ := ∑ z ∈ q.roots.toFinset, ‖z‖
  filter_upwards [eventually_gt_atTop (max B 0)] with x hx
  have hx0 : 0 < x := (le_max_right B 0).trans_lt hx
  intro hzero
  have hroot : (x : ℂ) ∈ q.roots := (Polynomial.mem_roots hq).mpr hzero
  have hmem : (x : ℂ) ∈ q.roots.toFinset := Multiset.mem_toFinset.mpr hroot
  have hle : ‖(x : ℂ)‖ ≤ B := by
    exact Finset.single_le_sum (fun z hz => norm_nonneg z) hmem
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0] at hle
  exact (not_lt_of_ge hle) ((le_max_left B 0).trans_lt hx)

/-- The completed curvature model `Θ_Ξ = a∞ - E'` from the card. -/
def completedZetaCurvatureModel (s : ℂ) : ℂ :=
  completedZetaArchimedeanCurvature s - iteratedDeriv 1 eulerLogDerivative s

/-- The Euler derivative response is exactly the rational archimedean response minus the completed
response. -/
theorem twoStepTranslation_eulerDerivative_eq_archimedean_sub_completed
    {s : ℂ} (hs : 2 < s.re) :
    finiteTranslationAction twoStepTranslationOperator
        (iteratedDeriv 1 eulerLogDerivative) s =
      completedZetaArchimedeanShiftRational s -
        finiteTranslationAction twoStepTranslationOperator completedZetaCurvatureModel s := by
  rw [finiteTranslationAction_twoStep_sub_one,
    finiteTranslationAction_twoStep_sub_one]
  simp only [completedZetaCurvatureModel]
  have harch := completedZetaArchimedeanCurvature_add_two_sub hs
  rw [← harch]
  ring

/-- A common-fraction representative of the difference between the explicit archimedean rational
response and an arbitrary rational completed response. -/
def completedZetaEulerDefectRatFunc (R : RatFunc ℂ) : RatFunc ℂ :=
  RatFunc.mk
    (completedZetaArchimedeanShiftNumerator * R.denom -
      R.num * completedZetaArchimedeanShiftDenominator)
    (completedZetaArchimedeanShiftDenominator * R.denom)

private theorem completedZetaEulerDefectRatFunc_eval
    (R : RatFunc ℂ) {x : ℝ} (hx : 2 < x) (hRden : R.denom.eval (x : ℂ) ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) (x : ℂ) (completedZetaEulerDefectRatFunc R) =
      completedZetaArchimedeanShiftRational x -
        RatFunc.eval (RingHom.id ℂ) (x : ℂ) R := by
  have hxm1 : (x : ℂ) - 1 ≠ 0 := by exact_mod_cast (by linarith : x - 1 ≠ 0)
  have hxp1 : (x : ℂ) + 1 ≠ 0 := by exact_mod_cast (by linarith : x + 1 ≠ 0)
  have hxp2 : (x : ℂ) + 2 ≠ 0 := by exact_mod_cast (by linarith : x + 2 ≠ 0)
  have hqeval : completedZetaArchimedeanShiftDenominator.eval (x : ℂ) ≠ 0 := by
    simp only [completedZetaArchimedeanShiftDenominator, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_ofNat, Polynomial.eval_one]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hxp2) (pow_ne_zero _ hxp1))
      (pow_ne_zero _ hxm1)
  have hprod :
      (completedZetaArchimedeanShiftDenominator * R.denom).eval (x : ℂ) ≠ 0 := by
    rw [Polynomial.eval_mul]
    exact mul_ne_zero hqeval hRden
  rw [completedZetaEulerDefectRatFunc,
    ratFunc_eval_mk_of_eval_ne_zero _ _ _ hprod]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul]
  have harch :
      completedZetaArchimedeanShiftNumerator.eval (x : ℂ) /
          completedZetaArchimedeanShiftDenominator.eval (x : ℂ) =
        completedZetaArchimedeanShiftRational x := by
    rw [← completedZetaArchimedeanShiftRatFunc_eval hx,
      completedZetaArchimedeanShiftRatFunc,
      ratFunc_eval_mk_of_eval_ne_zero _ _ _ hqeval]
  rw [RatFunc.eval]
  simp only [Polynomial.eval₂_id]
  rw [← harch]
  field_simp [hqeval, hRden]

/-- **Concrete completed-zeta defect.**  The nonzero operator `T₂-1` does not rationalize
`Θ_Ξ = a∞ - E'` on any right real ray.  The proof subtracts the explicit trigamma rational response;
the result would rationalize `E'`, contradicting the literal Euler flat-tower theorem. -/
theorem twoStepTranslation_completedZetaCurvatureModel_not_eventually_rational :
    ¬ ∃ R : RatFunc ℂ,
      (fun x : ℝ => finiteTranslationAction twoStepTranslationOperator
        completedZetaCurvatureModel x) =ᶠ[atTop]
      (fun x : ℝ => RatFunc.eval (RingHom.id ℂ) (x : ℂ) R) := by
  rintro ⟨R, hcompleted⟩
  have hden := polynomial_eval_ofReal_eventually_ne_zero R.denom (RatFunc.denom_ne_zero R)
  have heuler :
      (fun x : ℝ => finiteTranslationAction twoStepTranslationOperator
        (iteratedDeriv 1 eulerLogDerivative) x) =ᶠ[atTop]
      (fun x : ℝ => RatFunc.eval (RingHom.id ℂ) (x : ℂ)
        (completedZetaEulerDefectRatFunc R)) := by
    filter_upwards [hcompleted, hden, eventually_gt_atTop (2 : ℝ)] with x hcomp hxden hx
    rw [twoStepTranslation_eulerDerivative_eq_archimedean_sub_completed hx, hcomp,
      completedZetaEulerDefectRatFunc_eval R hx hxden]
  obtain ⟨B, hB⟩ := (eventually_atTop.1 heuler)
  let sigma : ℝ := max B 2 + 1
  have hsigma : 1 < sigma := by dsimp [sigma]; linarith [le_max_right B 2]
  have htau (x : ℝ) (hx : finiteTranslationThreshold twoStepTranslationOperator sigma ≤ x) :
      B ≤ x := by
    have hsum : 0 ≤ ∑ h ∈ twoStepTranslationOperator.support, |h.re| :=
      Finset.sum_nonneg fun h hh => abs_nonneg h.re
    have hsigma_le : sigma ≤ finiteTranslationThreshold twoStepTranslationOperator sigma := by
      dsimp [finiteTranslationThreshold]
      linarith
    have hBsigma : B ≤ sigma := by
      dsimp [sigma]
      linarith [le_max_left B 2]
    exact hBsigma.trans (hsigma_le.trans hx)
  have hzero := (eulerLogDerivative_iterated_rationalizes_iff_eq_zero
    1 hsigma twoStepTranslationOperator).mp ⟨completedZetaEulerDefectRatFunc R, fun x hx =>
      hB x (htau x hx)⟩
  exact twoStepTranslationOperator_ne_zero hzero

/-- The actual Euler derivative response has zero complete inverse-power Poincare shadow. -/
theorem twoStepTranslation_eulerDerivative_hasZeroInversePowerPoincareShadow :
    HasZeroInversePowerPoincareShadow (fun x : ℝ =>
      finiteTranslationAction twoStepTranslationOperator
        (iteratedDeriv 1 eulerLogDerivative) x) := by
  have hflat := eulerDerivativeTranslation_hasZeroInversePowerPoincareShadow
    1 (sigma := 2) (by norm_num) twoStepTranslationOperator
  intro N
  apply Tendsto.congr' ?_ (hflat N)
  filter_upwards [eventually_ge_atTop
    (finiteTranslationThreshold twoStepTranslationOperator 2)] with x hx
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  congr 1
  have hre : (1 : ℝ) < ((x : ℂ) + h).re :=
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
      (finiteTranslationThreshold_le_re_add twoStepTranslationOperator 2 x hx hh)
  calc
    generalizedDirichletSeries eulerGeneralizedFrequency
        (eulerGeneralizedCoefficient 1) ((x : ℂ) + h) =
      iteratedDeriv 1
        (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) ((x : ℂ) + h) :=
      eulerGeneralizedDirichletSeries_eq_iteratedDeriv 1 hre
    _ = iteratedDeriv 1 eulerLogDerivative ((x : ℂ) + h) :=
      (iteratedDeriv_eulerLogDerivative_eq_vonMangoldtLSeries 1 hre).symm

/-- Formal constraint statement `(30)`: the completed `T₂-1` response differs from the explicit
rational response by a function flat beyond every inverse power. -/
theorem twoStepTranslation_completedZetaCurvatureModel_formally_rational :
    HasZeroInversePowerPoincareShadow (fun x : ℝ =>
      finiteTranslationAction twoStepTranslationOperator completedZetaCurvatureModel x -
        completedZetaArchimedeanShiftRational x) := by
  have hflat := twoStepTranslation_eulerDerivative_hasZeroInversePowerPoincareShadow
  intro N
  have hneg : Tendsto (fun x : ℝ =>
      -((x : ℂ) ^ N * finiteTranslationAction twoStepTranslationOperator
        (iteratedDeriv 1 eulerLogDerivative) x)) atTop (nhds 0) := by
    simpa using (hflat N).neg
  apply Tendsto.congr' ?_ hneg
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
  have hid := twoStepTranslation_eulerDerivative_eq_archimedean_sub_completed
    (s := (x : ℂ)) (by simpa using hx)
  change -((x : ℂ) ^ N * finiteTranslationAction twoStepTranslationOperator
      (iteratedDeriv 1 eulerLogDerivative) x) =
    (x : ℂ) ^ N *
      (finiteTranslationAction twoStepTranslationOperator completedZetaCurvatureModel x -
        completedZetaArchimedeanShiftRational x)
  rw [hid]
  ring

/-- Exact nonzero-class certificate for `(29)`–`(30)`: `T₂-1` is nonzero, is a formal rational
constraint of the completed curvature, and is not an analytic rational constraint. -/
theorem completedZeta_twoStep_nonzero_flatDefect_certificate :
    twoStepTranslationOperator ≠ 0 ∧
      HasZeroInversePowerPoincareShadow (fun x : ℝ =>
        finiteTranslationAction twoStepTranslationOperator completedZetaCurvatureModel x -
          completedZetaArchimedeanShiftRational x) ∧
      ¬ ∃ R : RatFunc ℂ,
        (fun x : ℝ => finiteTranslationAction twoStepTranslationOperator
          completedZetaCurvatureModel x) =ᶠ[atTop]
        (fun x : ℝ => RatFunc.eval (RingHom.id ℂ) (x : ℂ) R) :=
  ⟨twoStepTranslationOperator_ne_zero,
    twoStepTranslation_completedZetaCurvatureModel_formally_rational,
    twoStepTranslation_completedZetaCurvatureModel_not_eventually_rational⟩

end GaloisForLFunctions.RHTower
