import GaloisForLFunctions.SelbergClass.CompletedEulerQuotient
import GaloisForLFunctions.HTGeometry.FiniteOrderEntireQuotient
import GaloisForLFunctions.RHTower.ReciprocalGammaExactOrderOne

/-!
# Polynomial exponent of the completed Euler quotient

The completed quotient is a removable quotient of entire finite-order
functions: cross-multiply the pole regularizations and the reciprocal
Gamma factors. Finite order descends to this zero-free entire quotient,
so Hadamard factorization writes it as the exponential of a polynomial.
-/

noncomputable section
open Complex Filter Set Topology

namespace GaloisForLFunctions.SelbergClass

open HTGeometry RHTower

private theorem finiteOrderEnvelope_regularized (A : EntireFiniteOrder) :
    FiniteOrderEnvelope A := by
  obtain ⟨a, b, ρ, ha, hb, hρ, hbound⟩ := A.growth
  let d : ℕ := ⌈ρ⌉₊
  refine ⟨a + b, d, by positivity, fun z => ?_⟩
  have hp : ‖z‖ ^ ρ ≤ (1 + ‖z‖) ^ d := by
    calc ‖z‖ ^ ρ ≤ (1 + ‖z‖) ^ ρ :=
        Real.rpow_le_rpow (norm_nonneg _) (by linarith) hρ
      _ ≤ (1 + ‖z‖) ^ (d : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg z]) (Nat.le_ceil _)
      _ = _ := Real.rpow_natCast _ _
  have hpow : 1 ≤ (1 + ‖z‖) ^ d := one_le_pow₀ (by linarith [norm_nonneg z])
  calc ‖A z‖ ≤ a * Real.exp (b * ‖z‖ ^ ρ) := hbound z
    _ ≤ Real.exp a * Real.exp (b * ‖z‖ ^ ρ) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp a]) (Real.exp_nonneg _)
    _ = Real.exp (a + b * ‖z‖ ^ ρ) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((a + b) * (1 + ‖z‖) ^ d) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hp hb.le,
        mul_le_mul_of_nonneg_left hpow ha.le]

private theorem finiteOrderEnvelope_reciprocalGamma : FiniteOrderEnvelope reciprocalGammaEntire := by
  obtain ⟨C, hC, hbound⟩ := orderOneEnvelope_reciprocalGammaEntire
  refine ⟨C, 2, hC.le, fun z => (hbound z).trans (Real.exp_le_exp.mpr ?_)⟩
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 2 + ‖z‖ by positivity)
  dsimp only [orderOneWeight]
  nlinarith [mul_le_mul_of_nonneg_left hlog (show 0 ≤ C * (1 + ‖z‖) by positivity)]

private theorem finiteOrderEnvelope_prod {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ S, FiniteOrderEnvelope (f i)) :
    FiniteOrderEnvelope (fun z => ∏ i ∈ S, f i z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using FiniteOrderEnvelope.const (1 : ℂ)
  | @insert i S hi ih =>
      simp only [Finset.prod_insert hi]
      exact (hf i (Finset.mem_insert_self i S)).mul
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- The entire reciprocal of the selected completed Gamma factor. -/
def inverseGammaFactor (D : SelbergGammaData) (s : ℂ) : ℂ :=
  Complex.exp (-((Real.log D.Q : ℂ) * s)) *
    ∏ j, reciprocalGammaEntire ((D.lambda j : ℂ) * s + D.mu j)

theorem inverseGammaFactor_eq_inv (D : SelbergGammaData) (s : ℂ) :
    inverseGammaFactor D s = (D.gammaFactor s)⁻¹ := by
  rw [gammaFactor_eq_exp_mul_archGammaFactor]
  simp only [inverseGammaFactor, archGammaFactor, reciprocalGammaEntire,
    Complex.exp_neg, mul_inv, Finset.prod_inv_distrib]

theorem inverseGammaFactor_analyticOnNhd (D : SelbergGammaData) :
    AnalyticOnNhd ℂ (inverseGammaFactor D) univ := by
  have hGamma : AnalyticOnNhd ℂ reciprocalGammaEntire univ :=
    analyticOnNhd_univ_iff_differentiable.mpr Complex.differentiable_one_div_Gamma
  intro s _
  apply (show AnalyticAt ℂ (fun z : ℂ => Complex.exp (-((Real.log D.Q : ℂ) * z))) s
    by fun_prop).mul
  have hprod : AnalyticAt ℂ (∏ j, fun z : ℂ =>
      reciprocalGammaEntire ((D.lambda j : ℂ) * z + D.mu j)) s :=
    Finset.univ.analyticAt_prod fun j _ =>
      (hGamma ((D.lambda j : ℂ) * s + D.mu j) (mem_univ _)).comp
        (f := fun z : ℂ => (D.lambda j : ℂ) * z + D.mu j) (x := s)
        (show AnalyticAt ℂ (fun z : ℂ => (D.lambda j : ℂ) * z + D.mu j) s by fun_prop)
  have heq : (∏ j, fun z : ℂ => reciprocalGammaEntire ((D.lambda j : ℂ) * z + D.mu j)) =
      fun z : ℂ => ∏ j, reciprocalGammaEntire ((D.lambda j : ℂ) * z + D.mu j) := by
    ext z
    simp only [Finset.prod_apply]
  rw [heq] at hprod
  exact hprod

theorem inverseGammaFactor_finiteOrderEnvelope (D : SelbergGammaData) :
    FiniteOrderEnvelope (inverseGammaFactor D) := by
  have hExp : FiniteOrderEnvelope (fun z : ℂ => Complex.exp (-((Real.log D.Q : ℂ) * z))) := by
    convert
      finiteOrderEnvelope_exp_polynomial (Polynomial.C (-(Real.log D.Q : ℂ)) * Polynomial.X)
      using 1
    simp [neg_mul]
  exact hExp.mul (finiteOrderEnvelope_prod Finset.univ _ fun j _ =>
    finiteOrderEnvelope_reciprocalGamma.compAffine (D.lambda j) (D.mu j))

private def crossRegularization (F G : RHTower.SelbergClass) (s : ℂ) : ℂ :=
  F.continuation.regularized s * (s - 1) ^ G.continuation.poleOrder *
    inverseGammaFactor G.gammaData s

private theorem crossRegularization_analytic (F G : RHTower.SelbergClass) :
    AnalyticOnNhd ℂ (crossRegularization F G) univ := fun s _ =>
  ((F.continuation.regularized.analytic s (mem_univ s)).mul (by fun_prop)).mul
    (inverseGammaFactor_analyticOnNhd G.gammaData s (mem_univ s))

private theorem crossRegularization_finiteOrder (F G : RHTower.SelbergClass) :
    FiniteOrderEnvelope (crossRegularization F G) := by
  have hp : FiniteOrderEnvelope (fun s : ℂ => (s - 1) ^ G.continuation.poleOrder) := by
    convert finiteOrderEnvelope_polynomial ((Polynomial.X - 1) ^ G.continuation.poleOrder)
      using 1
    simp
  exact ((finiteOrderEnvelope_regularized F.continuation.regularized).mul hp).mul
    (inverseGammaFactor_finiteOrderEnvelope G.gammaData)

private theorem crossRegularization_ne_zero_two (F G : RHTower.SelbergClass) :
    crossRegularization F G 2 ≠ 0 := by
  have hF : F.continuation.regularized 2 ≠ 0 := by
    intro hzero
    have he := F.eulerProduct 2 (by norm_num)
    rw [SelbergAnalyticContinuation.value, hzero, zero_div] at he
    exact Complex.exp_ne_zero _ he
  apply mul_ne_zero (mul_ne_zero hF (pow_ne_zero _ (by norm_num)))
  rw [inverseGammaFactor_eq_inv]
  exact inv_ne_zero (gammaFactor_analytic_ne_zero G.gammaData (by norm_num)).2

/-- Clearing the common poles and multiplying by reciprocal Gamma factors
realizes the glued quotient as a quotient of entire finite-order functions. -/
private theorem crossRegularization_eq (F G : RHTower.SelbergClass)
    (hT : AnalyticOnNhd ℂ (completedEulerQuotient F G) univ) :
    ∀ s, crossRegularization F G s = completedEulerQuotient F G s * crossRegularization G F s := by
  have hA := crossRegularization_analytic F G
  have hB := hT.mul (crossRegularization_analytic G F)
  have hevent : crossRegularization F G =ᶠ[𝓝 (2 : ℂ)]
      (fun s => completedEulerQuotient F G s * crossRegularization G F s) := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with s hs
    have hs0 : 0 < s.re := by linarith
    have hs1 : s - 1 ≠ 0 := by
      intro heq
      have : s = 1 := sub_eq_zero.mp heq
      subst s
      norm_num at hs
    have hGF := (gammaFactor_analytic_ne_zero F.gammaData hs0).2
    have hGG := (gammaFactor_analytic_ne_zero G.gammaData hs0).2
    have hv := eulerQuotient_mul_value F G hs
    change eulerQuotient F G s *
      (G.continuation.regularized s / (s - 1) ^ G.continuation.poleOrder) =
        F.continuation.regularized s / (s - 1) ^ F.continuation.poleOrder at hv
    have hcross : F.continuation.regularized s * (s - 1) ^ G.continuation.poleOrder =
        eulerQuotient F G s * G.continuation.regularized s *
          (s - 1) ^ F.continuation.poleOrder := by
      rw [← mul_div_assoc] at hv
      exact ((div_eq_div_iff (pow_ne_zero _ hs1) (pow_ne_zero _ hs1)).mp hv).symm
    rw [completedEulerQuotient_eq_right F G (by linarith)]
    dsimp only [crossRegularization, rightCompletedEulerQuotient]
    rw [inverseGammaFactor_eq_inv, inverseGammaFactor_eq_inv, hcross]
    field_simp
  exact fun s => hA.eqOn_of_preconnected_of_eventuallyEq hB isPreconnected_univ
    (mem_univ (2 : ℂ)) hevent (mem_univ s)

/-- Entire continuation of the completed quotient automatically has finite order. -/
theorem completedEulerQuotient_finiteOrderEnvelope_of_analytic (F G : RHTower.SelbergClass)
    (hT : AnalyticOnNhd ℂ (completedEulerQuotient F G) univ) :
    FiniteOrderEnvelope (completedEulerQuotient F G) :=
  FiniteOrderEnvelope.of_entire_quotient (crossRegularization_analytic G F)
    (crossRegularization_analytic F G) hT
    ⟨2, crossRegularization_ne_zero_two G F⟩ ⟨2, crossRegularization_ne_zero_two F G⟩
    (completedEulerQuotient_ne_zero F G) (crossRegularization_eq F G hT)
    (crossRegularization_finiteOrder G F) (crossRegularization_finiteOrder F G)

theorem completedEulerQuotient_finiteOrderEnvelope (F G : RHTower.SelbergClass) {σ : ℝ}
    (hσ : σ < 1 / 2)
    (hb : LSeriesSummable (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) σ) :
    FiniteOrderEnvelope (completedEulerQuotient F G) :=
  completedEulerQuotient_finiteOrderEnvelope_of_analytic F G
    (completedEulerQuotient_analyticOnNhd F G hσ hb)

/-- An entire completed Euler quotient is a polynomial exponential. -/
theorem completedEulerQuotient_eq_exp_polynomial_of_analytic (F G : RHTower.SelbergClass)
    (hT : AnalyticOnNhd ℂ (completedEulerQuotient F G) univ) :
    ∃ P : Polynomial ℂ, ∀ s, completedEulerQuotient F G s = Complex.exp (P.eval s) :=
  exists_polynomial_exp_of_ne_zero (analyticOnNhd_univ_iff_differentiable.mp hT)
    (completedEulerQuotient_ne_zero F G)
    (completedEulerQuotient_finiteOrderEnvelope_of_analytic F G hT)

/-- With arbitrary Gamma presentations, a subcritical Euler discrepancy leaves
only a polynomial exponential in the quotient of the completed functions. -/
theorem completedEulerQuotient_eq_exp_polynomial (F G : RHTower.SelbergClass) {σ : ℝ}
    (hσ : σ < 1 / 2)
    (hb : LSeriesSummable (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) σ) :
    ∃ P : Polynomial ℂ, ∀ s, completedEulerQuotient F G s = Complex.exp (P.eval s) :=
  completedEulerQuotient_eq_exp_polynomial_of_analytic F G
    (completedEulerQuotient_analyticOnNhd F G hσ hb)

end GaloisForLFunctions.SelbergClass
