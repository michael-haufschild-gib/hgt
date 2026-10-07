import GaloisForLFunctions.RHTower.XiKummerUnitRoots
import GaloisForLFunctions.RHTower.XiLegendreHalvingFields
import GaloisForLFunctions.RHTower.XiCriticalStripMarkedComponent
import GaloisForLFunctions.HTGeometry.QuadraticRootConjugation

/-!
# Two distinct deck actions on the actual marked source units

Over the global marked field, the extra quadratic root involution negates the
explicit unit roots. Over the analytic strip field, the component involution
fixes the factor roots, flips all marked generators, and inverts those unit
roots. The two base fields and the original source embedding stay explicit.
-/

noncomputable section
namespace RHTower.XiGlobalKummer
open GaloisForLFunctions.HTGeometry
open scoped IntermediateField

def globalCommonXiRoot : commonHalvingField :=
  ⟨commonHalfRoot, IntermediateField.mem_adjoin_simple_self Marked commonHalfRoot⟩

theorem globalCommonXiRoot_sq : globalCommonXiRoot * globalCommonXiRoot =
    algebraMap Marked commonHalvingField xiMarked := by
  apply Subtype.ext
  exact commonHalfRoot_sq

/-- This deck transformation fixes the entire global marked field. -/
def globalCommonDeck : commonHalvingField ≃ₐ[Marked] commonHalvingField :=
  quadraticRootConjugation commonHalfRoot_sq xi_not_isSquare_markedExtension

theorem globalCommonDeck_root : globalCommonDeck globalCommonXiRoot = -globalCommonXiRoot :=
  quadraticRootConjugation_gen commonHalfRoot_sq xi_not_isSquare_markedExtension

theorem globalCommonDeck_involutive : Function.Involutive globalCommonDeck :=
  quadraticRootConjugation_involutive commonHalfRoot_sq xi_not_isSquare_markedExtension

theorem globalCommonDeck_factorRoot (n : ℕ) :
    globalCommonDeck (halfFactorFromRoot globalCommonXiRoot n) =
      -halfFactorFromRoot globalCommonXiRoot n := by
  rw [halfFactorFromRoot, map_div₀, AlgEquiv.commutes, globalCommonDeck_root, div_neg]

/-- The extra global root involution negates the square root of each marked unit. -/
theorem globalCommonDeck_halfUnit (n : ℕ) :
    globalCommonDeck (halfUnitFromRoot globalCommonXiRoot n) =
      -halfUnitFromRoot globalCommonXiRoot n := by
  letI : Module Marked commonHalvingField := Algebra.toModule
  rw [halfUnitFromRoot, map_add, map_mul, map_mul,
    globalCommonDeck_factorRoot, globalCommonDeck_root,
    globalCommonDeck.commutes markedI, globalCommonDeck.commutes (betaMarked n)]
  ring

def stripComponentXiRoot : stripQuadraticField :=
  ⟨stripXiRoot, IntermediateField.mem_adjoin_simple_self StripField stripXiRoot⟩

theorem stripComponentXiRoot_sq : stripComponentXiRoot * stripComponentXiRoot =
    algebraMap Marked stripQuadraticField xiMarked := by
  rw [xiMarked, ← IsScalarTower.algebraMap_apply K Marked stripQuadraticField,
    IsScalarTower.algebraMap_apply K StripField stripQuadraticField]
  apply Subtype.ext
  exact stripXiRoot_sq

/-- This deck transformation fixes the analytic strip field. -/
def stripComponentDeck : stripQuadraticField ≃ₐ[StripField] stripQuadraticField :=
  quadraticRootConjugation stripXiRoot_sq strip_xi_not_isSquare

theorem stripComponentDeck_root : stripComponentDeck stripComponentXiRoot = -stripComponentXiRoot :=
  quadraticRootConjugation_gen stripXiRoot_sq strip_xi_not_isSquare

theorem stripComponentDeck_involutive : Function.Involutive stripComponentDeck :=
  quadraticRootConjugation_involutive stripXiRoot_sq strip_xi_not_isSquare

theorem stripComponentDeck_base (a : K) :
    stripComponentDeck (algebraMap Marked stripQuadraticField (algebraMap K Marked a)) =
      algebraMap Marked stripQuadraticField (algebraMap K Marked a) := by
  rw [← IsScalarTower.algebraMap_apply K Marked stripQuadraticField,
    IsScalarTower.algebraMap_apply K StripField stripQuadraticField, AlgEquiv.commutes]

/-- The factor root determined by this exact marked embedding lies in the strip base. -/
theorem stripComponent_factorRoot_mem_base (n : ℕ) :
    halfFactorFromRoot stripComponentXiRoot n ∈
      (⊥ : IntermediateField StripField stripQuadraticField) := by
  have hw := halfFactorFromRoot_sq stripComponentXiRoot_sq n
  rw [factorMarked, ← IsScalarTower.algebraMap_apply K Marked stripQuadraticField,
    IsScalarTower.algebraMap_apply K StripField stripQuadraticField, pow_two] at hw
  apply (root_mem_iff_isSquare hw ⊥).mpr
  exact (strip_factor_isSquare (n := n + 2)
    (Nat.succ_le_succ (Nat.zero_le (n + 1)))).map
      (algebraMap StripField (⊥ : IntermediateField StripField stripQuadraticField))

theorem stripComponentDeck_factorRoot (n : ℕ) :
    stripComponentDeck (halfFactorFromRoot stripComponentXiRoot n) =
      halfFactorFromRoot stripComponentXiRoot n := by
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp (stripComponent_factorRoot_mem_base n)
  rw [← ha, AlgEquiv.commutes]

/-- It flips every marked generator, so it does not fix the global marked base. -/
theorem stripComponentDeck_markedRoot (n : ℕ) :
    stripComponentDeck (algebraMap Marked stripQuadraticField (markedRoot n)) =
      -algebraMap Marked stripQuadraticField (markedRoot n) := by
  rw [← halfFactorFromRoot_mul_root stripComponentXiRoot_sq n, map_mul,
    stripComponentDeck_factorRoot, stripComponentDeck_root, mul_neg]

/-- On the analytic component, the same source expression has norm one. -/
theorem stripComponentDeck_halfUnit (n : ℕ) :
    stripComponentDeck (halfUnitFromRoot stripComponentXiRoot n) =
      (halfUnitFromRoot stripComponentXiRoot n)⁻¹ := by
  have he : stripComponentDeck (halfUnitFromRoot stripComponentXiRoot n) =
      halfFactorFromRoot stripComponentXiRoot n -
        algebraMap Marked stripQuadraticField markedI *
          algebraMap Marked stripQuadraticField (betaMarked n) * stripComponentXiRoot := by
    simp only [halfUnitFromRoot, map_add, map_mul, stripComponentDeck_factorRoot,
      stripComponentDeck_root, markedI, betaMarked, stripComponentDeck_base]
    ring
  rw [he]
  exact eq_inv_of_mul_eq_one_right (halfUnitFromRoot_mul_opposite stripComponentXiRoot_sq n)

/-- Squaring gives reciprocal action on the actual marked unit itself. -/
theorem stripComponentDeck_unitRepresentative (n : ℕ) :
    stripComponentDeck (algebraMap Marked stripQuadraticField (unitRepresentative n)) =
      (algebraMap Marked stripQuadraticField (unitRepresentative n))⁻¹ := by
  rw [← halfUnitFromRoot_sq stripComponentXiRoot_sq n, map_pow,
    stripComponentDeck_halfUnit, inv_pow]

end RHTower.XiGlobalKummer
