import GaloisForLFunctions.HTGeometry.GomesHermitePolynomialOrbit

/-!
# What a Hermite normal form forgets about the polynomial coordinate

Creation and coordinate multiplication together have only scalar linear symmetries.
Moreover, the Hermite normal-form conjugacies cannot preserve coordinate multiplication:
the first-order connection commutator is the identity, whereas creation has a negative
scalar commutator. This pinpoints the extra structure lost by the abstract normal form.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- A nonzero scalar normalization leaves an operator's commuting maps unchanged. -/
theorem gomesHermiteStep_commutes_connection_iff (E : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    E.comp gomesHermiteStepLinearMap = gomesHermiteStepLinearMap.comp E ↔
      E.comp (gomesPolynomialFirstOrderLinearMap gomesHermiteConnectionCoefficient.val) =
        (gomesPolynomialFirstOrderLinearMap gomesHermiteConnectionCoefficient.val).comp E := by
  constructor
  · intro h
    apply LinearMap.ext
    intro P
    have he := congrArg (fun f : ℝ[X] →ₗ[ℝ] ℝ[X] => f P) h
    apply (LinearEquiv.smulOfNeZero ℝ ℝ[X] gomesHermiteConnectionScale
      gomesHermiteConnectionScale_ne_zero).injective
    change gomesHermiteConnectionScale • E
        (gomesPolynomialFirstOrderLinearMap gomesHermiteConnectionCoefficient.val P) =
      gomesHermiteConnectionScale •
        gomesPolynomialFirstOrderLinearMap gomesHermiteConnectionCoefficient.val (E P)
    simpa only [LinearMap.comp_apply, gomesHermiteStepLinearMap, LinearMap.smul_apply,
      map_smul] using he
  · intro h
    apply LinearMap.ext
    intro P
    have he := congrArg (fun f : ℝ[X] →ₗ[ℝ] ℝ[X] => f P) h
    simp only [LinearMap.comp_apply, gomesHermiteStepLinearMap, LinearMap.smul_apply, map_smul]
    exact congrArg (fun Q : ℝ[X] => gomesHermiteConnectionScale • Q) he

/-- Preserving both the coordinate and Hermite creation allows exactly scalar linear maps. -/
theorem gomesHermiteStep_coordinate_joint_commutant (E : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    (E.comp (gomesPolynomialMultiplicationMap X) = (gomesPolynomialMultiplicationMap X).comp E ∧
      E.comp gomesHermiteStepLinearMap = gomesHermiteStepLinearMap.comp E) ↔
        ∃ c : ℝ, E = c • (LinearMap.id : ℝ[X] →ₗ[ℝ] ℝ[X]) := by
  rw [gomesHermiteStep_commutes_connection_iff,
    gomesPolynomialConnection_coordinate_compatible_maps_iff]
  constructor
  · rintro (hz | ⟨_, c, hc⟩)
    · exact ⟨0, by simpa only [zero_smul] using hz⟩
    · exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    exact Or.inr ⟨rfl, c, hc⟩

/-- Every coefficient connection has the same unit coordinate commutator. -/
theorem gomesPolynomialFirstOrder_coordinate_commutator (A P : ℝ[X]) :
    gomesPolynomialFirstOrderOperator A (X * P) -
      X * gomesPolynomialFirstOrderOperator A P = P := by
  simp only [gomesPolynomialFirstOrderOperator, derivative_mul, derivative_X, one_mul]
  ring

/-- Hermite creation instead has its negative normalization as coordinate commutator. -/
theorem gomesHermiteStep_coordinate_commutator (P : ℝ[X]) :
    gomesHermiteStepLinearMap (X * P) - X * gomesHermiteStepLinearMap P =
      gomesHermiteConnectionScale • P := by
  change gomesHermiteConnectionScale •
      gomesPolynomialFirstOrderOperator gomesHermiteConnectionCoefficient.val (X * P) -
    X * (gomesHermiteConnectionScale •
      gomesPolynomialFirstOrderOperator gomesHermiteConnectionCoefficient.val P) = _
  simp only [smul_eq_C_mul]
  calc
    _ = C gomesHermiteConnectionScale *
        (gomesPolynomialFirstOrderOperator gomesHermiteConnectionCoefficient.val (X * P) -
          X * gomesPolynomialFirstOrderOperator gomesHermiteConnectionCoefficient.val P) := by ring
    _ = _ := by rw [gomesPolynomialFirstOrder_coordinate_commutator]

/-- No connection-to-creation equivalence can retain multiplication by the original coordinate. -/
theorem gomesPolynomialConnection_no_coordinate_Hermite_intertwiner (A : ℝ[X]) :
    ¬ ∃ E : ℝ[X] ≃ₗ[ℝ] ℝ[X],
      E.toLinearMap.comp (gomesPolynomialMultiplicationMap X) =
          (gomesPolynomialMultiplicationMap X).comp E.toLinearMap ∧
        E.toLinearMap.comp (gomesPolynomialFirstOrderLinearMap A) =
          gomesHermiteStepLinearMap.comp E.toLinearMap := by
  rintro ⟨E, hx, ht⟩
  have hxP (P : ℝ[X]) : E (X * P) = X * E P :=
    gomesPolynomialXCompatibleMap_apply_X ⟨E.toLinearMap, hx⟩ P
  have htP (P : ℝ[X]) : E (gomesPolynomialFirstOrderOperator A P) =
      gomesHermiteStepLinearMap (E P) :=
    congrArg (fun f : ℝ[X] →ₗ[ℝ] ℝ[X] => f P) ht
  have he := congrArg E (gomesPolynomialFirstOrder_coordinate_commutator A 1)
  simp only [map_sub, htP, hxP] at he
  rw [gomesHermiteStep_coordinate_commutator] at he
  have hn : E (1 : ℝ[X]) ≠ 0 := by
    intro hz
    have h0 : E (1 : ℝ[X]) = E 0 := by simpa only [map_zero] using hz
    exact one_ne_zero (E.injective h0)
  have hp : (C gomesHermiteConnectionScale - 1) * E 1 = 0 := by
    rw [sub_mul, one_mul, ← smul_eq_C_mul, he, sub_self]
  have hc : C gomesHermiteConnectionScale = 1 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right hn)
  have hs : gomesHermiteConnectionScale = 1 := by
    have h := congrArg (Polynomial.eval (0 : ℝ)) hc
    simpa only [eval_C, eval_one] using h
  have hneg := gomesHermiteConnectionScale_negative
  rw [hs] at hneg
  exact (not_lt_of_ge zero_le_one) hneg

/-- The existing Hermite normal form is available precisely through maps that lose coordinate compatibility. -/
theorem gomesPolynomialConnection_Hermite_normal_form_loses_coordinate
    (A : {A : ℝ[X] // A.natDegree = 1}) :
    ∃ E : ℝ[X] ≃ₗ[ℝ] ℝ[X],
      E.toLinearMap.comp (gomesPolynomialFirstOrderLinearMap A.val) =
          gomesHermiteStepLinearMap.comp E.toLinearMap ∧
        E.toLinearMap.comp (gomesPolynomialMultiplicationMap X) ≠
          (gomesPolynomialMultiplicationMap X).comp E.toLinearMap := by
  obtain ⟨E, ht⟩ := gomesPolynomialConnection_Hermite_normal_form A
  refine ⟨E, ht, ?_⟩
  intro hx
  exact gomesPolynomialConnection_no_coordinate_Hermite_intertwiner A.val ⟨E, hx, ht⟩

end GaloisForLFunctions.HTGeometry
