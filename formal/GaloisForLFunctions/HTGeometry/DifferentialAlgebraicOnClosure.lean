import GaloisForLFunctions.HTGeometry.AnalyticJetFieldBridge
import GaloisForLFunctions.HTGeometry.DifferentiallyAlgebraicInvariance
import GaloisForLFunctions.HTGeometry.ReciprocalSubstitutionInjective

/-!
# Closure properties of differential algebraicity on an open set

The meromorphic jet field bridge is stated for an arbitrary open, preconnected, nonempty, infinite
domain, so the ring closure properties of differential algebraicity hold there verbatim; together
with the reciprocal closure this makes the differentially algebraic analytic functions on such a
domain a field.  Translation of the argument moves the domain.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial
open GaloisForLFunctions Bottcher

noncomputable section

/-! ## Translation -/

/-- **Translation invariance on a domain.**  If `f` satisfies an algebraic differential equation on
`U`, then `z ↦ f (z + a)` satisfies one on the translated domain. -/
theorem DifferentiallyAlgebraicOn.comp_add_const {f : ℂ → ℂ} {U : Set ℂ}
    (hf : DifferentiallyAlgebraicOn f U) (a : ℂ) :
    DifferentiallyAlgebraicOn (fun z => f (z + a)) {z : ℂ | z + a ∈ U} := by
  obtain ⟨n, P, hP0, hPz⟩ := hf
  refine ⟨n, bind₁ (jetShiftSub n a) P, ?_, ?_⟩
  · intro h
    apply hP0
    have hback : bind₁ (jetShiftSub n (-a)) (bind₁ (jetShiftSub n a) P) = P := by
      rw [bind₁_bind₁]
      have hσ : (fun i => bind₁ (jetShiftSub n (-a)) (jetShiftSub n a i))
          = (X : Fin (n + 2) → MvPolynomial (Fin (n + 2)) ℂ) := by
        funext i
        induction i using Fin.cases with
        | zero =>
          simp only [jetShiftSub, Fin.cases_zero, map_add, bind₁_X_right, bind₁_C_right]
          rw [map_neg]
          ring
        | succ j => simp only [jetShiftSub, Fin.cases_succ, bind₁_X_right]
      rw [hσ, bind₁_X_left]
      rfl
    rw [← hback, h, map_zero]
  · intro z hz
    rw [eval_bind₁]
    have hvec : (fun i => eval
          (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) (fun w => f (w + a)) z)
          (jetShiftSub n a i))
        = Fin.cons (z + a) (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f (z + a)) := by
      funext i
      induction i using Fin.cases with
      | zero => simp [jetShiftSub]
      | succ j =>
        simp only [jetShiftSub, Fin.cases_succ, eval_X, Fin.cons_succ]
        exact congrFun (iteratedDeriv_comp_add_const (j : ℕ) f a) z
    rw [hvec]
    exact hPz (z + a) hz

/-! ## The ring structure -/

/-- **Products.**  Differential algebraicity on a domain is closed under multiplication. -/
theorem differentiallyAlgebraicOn_mul {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hfDA : DifferentiallyAlgebraicOn f U) (hgDA : DifferentiallyAlgebraicOn g U) :
    DifferentiallyAlgebraicOn (fun z => f z * g z) U := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  letI : Differential (RatFunc ℂ) := ratFuncCoordinateDifferential
  letI := meroFieldDifferential (U := U) hUo hUc hUne
  letI : DifferentialAlgebra (RatFunc ℂ) (meroField U) :=
    meroFieldRatFuncDifferentialAlgebra hUo hUc hUne hUinf
  letI : CharZero (meroField U) :=
    charZero_of_injective_algebraMap (algebraMap (RatFunc ℂ) (meroField U)).injective
  refine (differentialAlgebraicOver_analyticMeroElement_iff hUo hUc hUne hUinf
    (hf.mul hg)).mp ?_
  rw [analyticMeroElement_mul hf hg]
  exact differentialAlgebraicOver_mul
    ((differentialAlgebraicOver_analyticMeroElement_iff hUo hUc hUne hUinf hf).mpr hfDA)
    ((differentialAlgebraicOver_analyticMeroElement_iff hUo hUc hUne hUinf hg).mpr hgDA)

/-- **Quotients.**  Differential algebraicity on a domain is closed under division by a
nonvanishing analytic differentially algebraic function. -/
theorem differentiallyAlgebraicOn_div {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U) (hgne : ∀ z ∈ U, g z ≠ 0)
    (hfDA : DifferentiallyAlgebraicOn f U) (hgDA : DifferentiallyAlgebraicOn g U) :
    DifferentiallyAlgebraicOn (fun z => f z / g z) U := by
  have hinvDA : DifferentiallyAlgebraicOn (fun z => (g z)⁻¹) U :=
    differentiallyAlgebraicOn_inv hUo hg hgne hgDA
  have hinvan : AnalyticOnNhd ℂ (fun z => (g z)⁻¹) U := fun z hz => (hg z hz).inv (hgne z hz)
  have hmul := differentiallyAlgebraicOn_mul hUo hUc hUne hUinf hf hinvan hfDA hinvDA
  obtain ⟨n, P, hP0, hPv⟩ := hmul
  refine ⟨n, P, hP0, ?_⟩
  intro z hz
  have hfun : (fun z => f z / g z) = fun z => f z * (g z)⁻¹ := by
    funext w
    rw [div_eq_mul_inv]
  rw [hfun]
  exact hPv z hz

end

end GaloisForLFunctions.HTGeometry
