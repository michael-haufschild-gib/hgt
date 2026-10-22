import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicCyclicRestrictionFormula
import Mathlib.LinearAlgebra.PiTensorProduct.Finsupp

/-!
# Linear extension of the higher CCM restriction

The convergent monomial formula is multilinear in every Bruhat--Schwartz coefficient.  Tensor
products distribute exactly over the finitely supported scaling coefficients of the crossed
product, so the formula extends canonically to a linear map on every full algebraic cyclic-chain
degree of the nonunital CCM source.
-/

noncomputable section

open scoped TensorProduct

namespace GaloisForLFunctions
namespace RHTower

private abbrev Core := CCMRationalAdelicBruhatSimpleTensor
private abbrev Scale := CCMRationalAdelicScaling
private abbrev Crossed := CCMRationalAdelicAlgebraicCrossedProduct

/-- Degree-`n` class-space functions before imposing strong-Schwartz regularity. -/
abbrev CCMRationalAdelicClassSpaceFunctions (n : ℕ) :=
  (Fin (n + 1) → CCMRationalAdelicMoritaBase) → ℂ

private def ccmRationalAdelicCyclicRestrictionFactor {n : ℕ}
    (k : Fin (n + 1) → Scale)
    (t : Fin (n + 1) → Core)
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase)
    (q : CCMRationalUnit) (j : Fin (n + 1)) : ℂ :=
  ccmRationalAdelicBruhatTensorOrbitCoefficient
    (t j) (base j).bInf (base j).bFin
    ((ccmRationalAdelicCyclicPrefix k j).val⁻¹ * q)

theorem ccmRationalAdelicCyclicRestrictionTerm_update_add {n : ℕ}
    (k : Fin (n + 1) → Scale)
    (t : Fin (n + 1) → Core)
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase)
    (q : CCMRationalUnit) (j : Fin (n + 1)) (a b : Core) :
    ccmRationalAdelicCyclicRestrictionTerm k (Function.update t j (a + b)) base q =
      ccmRationalAdelicCyclicRestrictionTerm k (Function.update t j a) base q +
        ccmRationalAdelicCyclicRestrictionTerm k (Function.update t j b) base q := by
  classical
  let f : Fin (n + 1) → ℂ :=
    ccmRationalAdelicCyclicRestrictionFactor k t base q
  let fa := ccmRationalAdelicBruhatTensorOrbitCoefficient
    a (base j).bInf (base j).bFin
      ((ccmRationalAdelicCyclicPrefix k j).val⁻¹ * q)
  let fb := ccmRationalAdelicBruhatTensorOrbitCoefficient
    b (base j).bInf (base j).bFin
      ((ccmRationalAdelicCyclicPrefix k j).val⁻¹ * q)
  have hadd : (fun i => ccmRationalAdelicCyclicRestrictionFactor k
      (Function.update t j (a + b)) base q i) = Function.update f j (fa + fb) := by
    funext i
    by_cases hij : i = j
    · subst i
      simp [ccmRationalAdelicCyclicRestrictionFactor, f, fa, fb]
      exact ccmRationalAdelicBruhatTensorOrbit_add a b
        (base j).bInf (base j).bFin _
    · simp [ccmRationalAdelicCyclicRestrictionFactor, f, fa, fb, hij]
  have ha : (fun i => ccmRationalAdelicCyclicRestrictionFactor k
      (Function.update t j a) base q i) = Function.update f j fa := by
    funext i
    by_cases hij : i = j <;>
      simp [ccmRationalAdelicCyclicRestrictionFactor, f, fa, hij]
  have hb : (fun i => ccmRationalAdelicCyclicRestrictionFactor k
      (Function.update t j b) base q i) = Function.update f j fb := by
    funext i
    by_cases hij : i = j <;>
      simp [ccmRationalAdelicCyclicRestrictionFactor, f, fb, hij]
  change (∏ i, ccmRationalAdelicCyclicRestrictionFactor k
      (Function.update t j (a + b)) base q i) =
    (∏ i, ccmRationalAdelicCyclicRestrictionFactor k
      (Function.update t j a) base q i) +
    ∏ i, ccmRationalAdelicCyclicRestrictionFactor k
      (Function.update t j b) base q i
  rw [hadd, ha, hb,
    Finset.prod_update_of_mem (Finset.mem_univ j),
    Finset.prod_update_of_mem (Finset.mem_univ j),
    Finset.prod_update_of_mem (Finset.mem_univ j)]
  ring

theorem ccmRationalAdelicCyclicRestrictionTerm_update_smul {n : ℕ}
    (k : Fin (n + 1) → Scale)
    (t : Fin (n + 1) → Core)
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase)
    (q : CCMRationalUnit) (j : Fin (n + 1)) (z : ℂ) (a : Core) :
    ccmRationalAdelicCyclicRestrictionTerm k (Function.update t j (z • a)) base q =
      z * ccmRationalAdelicCyclicRestrictionTerm k (Function.update t j a) base q := by
  classical
  let f : Fin (n + 1) → ℂ :=
    ccmRationalAdelicCyclicRestrictionFactor k t base q
  let fa := ccmRationalAdelicBruhatTensorOrbitCoefficient
    a (base j).bInf (base j).bFin
      ((ccmRationalAdelicCyclicPrefix k j).val⁻¹ * q)
  have hsmul : (fun i => ccmRationalAdelicCyclicRestrictionFactor k
      (Function.update t j (z • a)) base q i) = Function.update f j (z * fa) := by
    funext i
    by_cases hij : i = j
    · subst i
      simp [ccmRationalAdelicCyclicRestrictionFactor, f, fa]
      exact ccmRationalAdelicBruhatTensorOrbit_smul z a
        (base j).bInf (base j).bFin _
    · simp [ccmRationalAdelicCyclicRestrictionFactor, f, fa, hij]
  have ha : (fun i => ccmRationalAdelicCyclicRestrictionFactor k
      (Function.update t j a) base q i) = Function.update f j fa := by
    funext i
    by_cases hij : i = j <;>
      simp [ccmRationalAdelicCyclicRestrictionFactor, f, fa, hij]
  change (∏ i, ccmRationalAdelicCyclicRestrictionFactor k
      (Function.update t j (z • a)) base q i) =
    z * ∏ i, ccmRationalAdelicCyclicRestrictionFactor k
      (Function.update t j a) base q i
  rw [hsmul, ha,
    Finset.prod_update_of_mem (Finset.mem_univ j),
    Finset.prod_update_of_mem (Finset.mem_univ j)]
  ring

theorem ccmRationalAdelicCyclicRestrictionMonomial_update_add {n : ℕ}
    (k : Fin (n + 1) → Scale)
    (t : Fin (n + 1) → Core)
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase)
    (j : Fin (n + 1)) (a b : Core) :
    ccmRationalAdelicCyclicRestrictionMonomial k (Function.update t j (a + b)) base =
      ccmRationalAdelicCyclicRestrictionMonomial k (Function.update t j a) base +
        ccmRationalAdelicCyclicRestrictionMonomial k (Function.update t j b) base := by
  by_cases hscale : ccmRationalAdelicCyclicTotalScale k = 1
  · rw [ccmRationalAdelicCyclicRestrictionMonomial_eq_tsum_of_totalScale_eq_one
      _ _ _ hscale,
      ccmRationalAdelicCyclicRestrictionMonomial_eq_tsum_of_totalScale_eq_one
        _ _ _ hscale,
      ccmRationalAdelicCyclicRestrictionMonomial_eq_tsum_of_totalScale_eq_one
        _ _ _ hscale]
    rw [show (fun q => ccmRationalAdelicCyclicRestrictionTerm k
        (Function.update t j (a + b)) base q) =
      fun q => ccmRationalAdelicCyclicRestrictionTerm k
          (Function.update t j a) base q +
        ccmRationalAdelicCyclicRestrictionTerm k
          (Function.update t j b) base q by
      funext q
      exact ccmRationalAdelicCyclicRestrictionTerm_update_add k t base q j a b]
    exact (ccmRationalAdelicCyclicRestrictionTerm_summable k
      (Function.update t j a) base).tsum_add
        (ccmRationalAdelicCyclicRestrictionTerm_summable k
          (Function.update t j b) base)
  · simp [ccmRationalAdelicCyclicRestrictionMonomial, hscale]

theorem ccmRationalAdelicCyclicRestrictionMonomial_update_smul {n : ℕ}
    (k : Fin (n + 1) → Scale)
    (t : Fin (n + 1) → Core)
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase)
    (j : Fin (n + 1)) (z : ℂ) (a : Core) :
    ccmRationalAdelicCyclicRestrictionMonomial k (Function.update t j (z • a)) base =
      z * ccmRationalAdelicCyclicRestrictionMonomial k (Function.update t j a) base := by
  by_cases hscale : ccmRationalAdelicCyclicTotalScale k = 1
  · rw [ccmRationalAdelicCyclicRestrictionMonomial_eq_tsum_of_totalScale_eq_one
      _ _ _ hscale,
      ccmRationalAdelicCyclicRestrictionMonomial_eq_tsum_of_totalScale_eq_one
        _ _ _ hscale]
    rw [show (fun q => ccmRationalAdelicCyclicRestrictionTerm k
        (Function.update t j (z • a)) base q) =
      fun q => z * ccmRationalAdelicCyclicRestrictionTerm k
        (Function.update t j a) base q by
      funext q
      exact ccmRationalAdelicCyclicRestrictionTerm_update_smul k t base q j z a]
    exact tsum_mul_left
  · simp [ccmRationalAdelicCyclicRestrictionMonomial, hscale]

/-- Fixed scaling tuple: the higher restriction is multilinear in all core coefficients. -/
def ccmRationalAdelicCyclicRestrictionMonomialMultilinear {n : ℕ}
    (k : Fin (n + 1) → Scale) :
    MultilinearMap ℂ (fun _ : Fin (n + 1) => Core)
      (CCMRationalAdelicClassSpaceFunctions n) :=
  MultilinearMap.mk'
    (fun t base => ccmRationalAdelicCyclicRestrictionMonomial k t base)
    (by
      intro t j a b
      funext base
      exact ccmRationalAdelicCyclicRestrictionMonomial_update_add k t base j a b)
    (by
      intro t j z a
      funext base
      exact ccmRationalAdelicCyclicRestrictionMonomial_update_smul k t base j z a)

/-- Linear fixed-scaling restriction on the tensor power of the adelic core. -/
def ccmRationalAdelicCyclicRestrictionMonomialLinear {n : ℕ}
    (k : Fin (n + 1) → Scale) :
    PiTensorProduct ℂ (fun _ : Fin (n + 1) => Core) →ₗ[ℂ]
      CCMRationalAdelicClassSpaceFunctions n :=
  PiTensorProduct.lift (ccmRationalAdelicCyclicRestrictionMonomialMultilinear k)

/-- Linear higher restriction on the full nonunital crossed-product cyclic chain degree. -/
def ccmRationalAdelicCyclicRestrictionLinear (n : ℕ) :
    PiTensorProduct ℂ (fun _ : Fin (n + 1) => Crossed) →ₗ[ℂ]
      CCMRationalAdelicClassSpaceFunctions n := by
  classical
  exact ((Finsupp.lsum ℂ) fun k : Fin (n + 1) → Scale =>
        ccmRationalAdelicCyclicRestrictionMonomialLinear k).comp
      (PiTensorProduct.ofFinsuppEquiv
        (R := ℂ) (ι := Fin (n + 1))
        (κ := fun _ => Scale) (M := fun _ => Core)).toLinearMap

@[simp]
theorem ccmRationalAdelicCyclicRestrictionLinear_tprod_single {n : ℕ}
    (k : Fin (n + 1) → Scale) (t : Fin (n + 1) → Core) :
    ccmRationalAdelicCyclicRestrictionLinear n
        (PiTensorProduct.tprod ℂ
          (fun j => Finsupp.single (k j) (t j) : Fin (n + 1) → Crossed)) =
      fun base => ccmRationalAdelicCyclicRestrictionMonomial k t base := by
  classical
  simp [ccmRationalAdelicCyclicRestrictionLinear,
    ccmRationalAdelicCyclicRestrictionMonomialLinear,
    ccmRationalAdelicCyclicRestrictionMonomialMultilinear]

end RHTower
end GaloisForLFunctions
