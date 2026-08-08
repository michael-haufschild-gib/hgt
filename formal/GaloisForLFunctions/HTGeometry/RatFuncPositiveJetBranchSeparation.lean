import GaloisForLFunctions.HTGeometry.JetFieldAlgebraicBranchRigidity
import GaloisForLFunctions.HTGeometry.RatFuncTranslationFixedField
import GaloisForLFunctions.HTGeometry.TranscendentalMobius
import GaloisForLFunctions.HTGeometry.FiniteShadowCapacitySpectrum
import GaloisForLFunctions.HTGeometry.DifferenceDifferential

/-!
# Rational shadows and positive jets separate algebraic branches

For a free differential coordinate `x`, let `z` be algebraic over the free differential field.
If one nonconstant rational function has the same value at `z` and `x`, and one positive jet of
`z` equals the corresponding jet of `x`, then `z = x`.

The positive-jet equality makes `z - x` a base constant by
`JetFieldAlgebraicBranchRigidity`.  Naturality of rational evaluation turns equality of the
rational shadows into invariance under translation by that constant.  The no-additive-period
theorem for nonconstant rational functions then forces the constant to vanish.
-/

open scoped Differential
open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Translating a transcendental element by a base constant preserves transcendence. -/
theorem transcendental_add_algebraMap
    {C E : Type*} [Field C] [Field E] [Algebra C E]
    {y : E} (hy : Transcendental C y) (c : C) :
    Transcendental C (y + algebraMap C E c) := by
  intro halg
  apply hy
  have hc : IsAlgebraic C (algebraMap C E c) := isAlgebraic_algebraMap c
  have := halg.sub hc
  simpa using this

/-- An injective scalar extension preserves transcendence. -/
theorem transcendental_algebraMap
    {C A E : Type*} [Field C] [Field A] [Field E]
    [Algebra C A] [Algebra A E] [Algebra C E] [IsScalarTower C A E]
    {y : A} (hy : Transcendental C y) :
    Transcendental C (algebraMap A E y) := by
  intro halg
  exact hy ((isAlgebraic_algHom_iff (IsScalarTower.toAlgHom C A E)
    (algebraMap A E).injective).mp halg)

/-- Rational-function evaluation commutes with injective scalar extension. -/
theorem ratFuncEval_algebraMap
    {C A E : Type*} [Field C] [Field A] [Field E]
    [Algebra C A] [Algebra A E] [Algebra C E] [IsScalarTower C A E]
    {y : A} (hy : Transcendental C y) (r : RatFunc C) :
    ratFuncEval (algebraMap A E y) (transcendental_algebraMap hy) r =
      algebraMap A E (ratFuncEval y hy r) := by
  have hhom :
      (ratFuncEval (algebraMap A E y) (transcendental_algebraMap hy)).toRingHom =
        (algebraMap A E).comp (ratFuncEval y hy).toRingHom := by
    apply IsFractionRing.ringHom_ext (A := C[X])
    intro p
    induction p using Polynomial.induction_on with
    | C c =>
        change ratFuncEval (algebraMap A E y) _ (RatFunc.C c) =
          algebraMap A E (ratFuncEval y hy (RatFunc.C c))
        rw [ratFuncEval_C, ratFuncEval_C, IsScalarTower.algebraMap_apply C A E]
    | add p q hp hq =>
        simpa only [map_add, RingHom.comp_apply] using congrArg₂ (fun a b ↦ a + b) hp hq
    | monomial n c ih =>
        have hX :
            (ratFuncEval (algebraMap A E y) (transcendental_algebraMap hy)).toRingHom
                (algebraMap C[X] (RatFunc C) X) =
              ((algebraMap A E).comp (ratFuncEval y hy).toRingHom)
                (algebraMap C[X] (RatFunc C) X) := by
          rw [RatFunc.algebraMap_X]
          change ratFuncEval (algebraMap A E y) _ RatFunc.X =
            algebraMap A E (ratFuncEval y hy RatFunc.X)
          rw [ratFuncEval_X, ratFuncEval_X]
        have hmul := congrArg₂ (fun a b ↦ a * b) ih hX
        simpa only [pow_succ, ← mul_assoc, map_mul, RingHom.comp_apply] using hmul
  exact DFunLike.congr_fun hhom r

/-- Evaluating after translating the rational variable equals evaluating at the translated
transcendental point. -/
theorem ratFuncEval_translation
    {C E : Type*} [Field C] [Field E] [Algebra C E]
    {y : E} (hy : Transcendental C y) (c : C) (r : RatFunc C) :
    ratFuncEval y hy (ratFuncTranslationEquiv c r) =
      ratFuncEval (y + algebraMap C E c) (transcendental_add_algebraMap hy c) r := by
  have hhom :
      ((ratFuncEval y hy).comp (ratFuncTranslationEquiv c).toAlgHom).toRingHom =
        (ratFuncEval (y + algebraMap C E c)
          (transcendental_add_algebraMap hy c)).toRingHom := by
    apply IsFractionRing.ringHom_ext (A := C[X])
    intro p
    induction p using Polynomial.induction_on with
    | C a =>
        change ratFuncEval y hy (ratFuncTranslationEquiv c (RatFunc.C a)) =
          ratFuncEval (y + algebraMap C E c) _ (RatFunc.C a)
        rw [← RatFunc.algebraMap_eq_C]
        simp only [AlgEquiv.commutes, AlgHom.commutes]
    | add p q hp hq =>
        simpa only [map_add] using congrArg₂ (fun a b ↦ a + b) hp hq
    | monomial n a ih =>
        have hX :
            ((ratFuncEval y hy).comp (ratFuncTranslationEquiv c).toAlgHom).toRingHom
                (algebraMap C[X] (RatFunc C) X) =
              (ratFuncEval (y + algebraMap C E c)
                (transcendental_add_algebraMap hy c)).toRingHom
                (algebraMap C[X] (RatFunc C) X) := by
          rw [RatFunc.algebraMap_X]
          change ratFuncEval y hy (ratFuncTranslationEquiv c RatFunc.X) =
            ratFuncEval (y + algebraMap C E c) _ RatFunc.X
          rw [ratFuncTranslationEquiv_X, map_add, ratFuncEval_X, AlgHom.commutes,
            ratFuncEval_X]
        have hmul := congrArg₂ (fun a b ↦ a * b) ih hX
        simpa only [pow_succ, ← mul_assoc, map_mul] using hmul
  exact DFunLike.congr_fun hhom r

/-- **One nonconstant rational shadow and one positive jet separate every algebraic branch.**

This is the exact branch-separation mechanism from the nonlinear rational-observation theorem,
stated in the canonical free differential field. -/
theorem algebraic_branch_eq_of_ratFunc_and_positive_jet
    {C ι R : Type*} [Field C] [CharZero C] [IsAlgClosed C] [Fintype ι]
    [Field R] [Algebra (JetField C ι) R] [Algebra C R]
    [IsScalarTower C (JetField C ι) R] [Differential R]
    [DifferentialAlgebra (JetField C ι) R]
    (i : ι) {r : RatFunc C} (hr : ¬ ∃ a : C, r = RatFunc.C a)
    {z : R} (hzalg : IsAlgebraic (JetField C ι) z) (hztrans : Transcendental C z)
    {n : ℕ} (hn : 0 < n)
    (hrat : ratFuncEval z hztrans r =
      algebraMap (JetField C ι) R
        (ratFuncEval (JetField.jet (i, 0))
          (JetField.algebraicIndependent_jet_free.transcendental (i, 0)) r))
    (hjet : differentialJet n z =
      algebraMap (JetField C ι) R
        (differentialJet n (JetField.jet (i, 0)))) :
    z = algebraMap (JetField C ι) R (JetField.jet (i, 0)) := by
  let A := JetField C ι
  let x₀ : A := JetField.jet (i, 0)
  have hxtrans : Transcendental C x₀ :=
    JetField.algebraicIndependent_jet_free.transcendental (i, 0)
  let w : R := z - algebraMap A R x₀
  have hwalg : IsAlgebraic A w := hzalg.sub (isAlgebraic_algebraMap x₀)
  have hwjet : differentialJet n w = 0 := by
    change differentialJet n (z - algebraMap A R x₀) = 0
    rw [GaloisForLFunctions.differentialJet_sub,
      differentialJet_algebraMap_apply, hjet, sub_self]
  obtain ⟨_, c, hwc⟩ := differentialJet_eq_base_of_isAlgebraic hwalg hn (c := 0) (by
    simpa only [map_zero] using hwjet)
  have hzform : z = algebraMap A R (x₀ + algebraMap C A c) := by
    rw [map_add, ← IsScalarTower.algebraMap_apply C A R]
    dsimp only [w] at hwc
    linear_combination hwc
  have hxc : Transcendental C (x₀ + algebraMap C A c) :=
    transcendental_add_algebraMap hxtrans c
  have hevalR :
      algebraMap A R (ratFuncEval (x₀ + algebraMap C A c) hxc r) =
        algebraMap A R (ratFuncEval x₀ hxtrans r) := by
    rw [← ratFuncEval_algebraMap hxc r]
    simpa only [A, x₀, hzform] using hrat
  have hevalA : ratFuncEval (x₀ + algebraMap C A c) hxc r =
      ratFuncEval x₀ hxtrans r := (algebraMap A R).injective hevalR
  have hfixed : ratFuncTranslationEquiv c r = r := by
    apply ratFuncEval_injective x₀ hxtrans
    rw [ratFuncEval_translation hxtrans c r, hevalA]
  have hc : c = 0 := by
    by_contra hc
    exact hr (ratFuncTranslation_fixed_eq_constant c hc hfixed)
  subst c
  simpa only [map_zero, add_zero, A, x₀] using hzform

end

end GaloisForLFunctions.HTGeometry
