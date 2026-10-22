import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicUnitizedCyclicSummability
import Mathlib.LinearAlgebra.PiTensorProduct.DFinsupp

/-!
# Linear extension of the normalized unitized CCM restriction

Every dependent scalar/crossed label sector is multilinear.  Absolute convergence of every
non-all-scalar sector permits passage of addition and scalar multiplication through the orbit sum.
The dependent multilinear family then extends canonically across `DFinsupp`, tensor product, and
the exact minimal-unitization equivalence.
-/

noncomputable section

open scoped TensorProduct

namespace GaloisForLFunctions
namespace RHTower

private abbrev Label := CCMRationalAdelicUnitizedLabel
private abbrev Fiber := CCMRationalAdelicUnitizedFiber
private abbrev Source := CCMRationalAdelicCyclicSourceAlgebra

theorem ccmRationalAdelicUnitizedFiberCoefficient_add
    (label : Label) (a b : Fiber label)
    (base : CCMRationalAdelicMoritaBase) (shift q : CCMRationalUnit) :
    ccmRationalAdelicUnitizedFiberCoefficient label (a + b) base shift q =
      ccmRationalAdelicUnitizedFiberCoefficient label a base shift q +
        ccmRationalAdelicUnitizedFiberCoefficient label b base shift q := by
  exact CCMRationalAdelicUnitizedLabel.rec
    (motive := fun label => ∀ a b : Fiber label,
      ccmRationalAdelicUnitizedFiberCoefficient label (a + b) base shift q =
        ccmRationalAdelicUnitizedFiberCoefficient label a base shift q +
          ccmRationalAdelicUnitizedFiberCoefficient label b base shift q)
    (fun _ _ => rfl)
    (fun _ a b =>
      ccmRationalAdelicBruhatTensorOrbit_add a b
        base.bInf base.bFin (shift * q))
    label a b

theorem ccmRationalAdelicUnitizedFiberCoefficient_smul
    (label : Label) (z : ℂ) (a : Fiber label)
    (base : CCMRationalAdelicMoritaBase) (shift q : CCMRationalUnit) :
    ccmRationalAdelicUnitizedFiberCoefficient label (z • a) base shift q =
      z * ccmRationalAdelicUnitizedFiberCoefficient label a base shift q := by
  exact CCMRationalAdelicUnitizedLabel.rec
    (motive := fun label => ∀ a : Fiber label,
      ccmRationalAdelicUnitizedFiberCoefficient label (z • a) base shift q =
        z * ccmRationalAdelicUnitizedFiberCoefficient label a base shift q)
    (fun _ => rfl)
    (fun _ a =>
      ccmRationalAdelicBruhatTensorOrbit_smul z a
        base.bInf base.bFin (shift * q))
    label a

theorem ccmRationalAdelicUnitizedCyclicTerm_update_add {n : ℕ}
    (label : Fin (n + 1) → Label)
    (coefficient : (i : Fin (n + 1)) → Fiber (label i))
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase)
    (q : CCMRationalUnit) (j : Fin (n + 1)) (a b : Fiber (label j)) :
    ccmRationalAdelicUnitizedCyclicTerm label
        (Function.update coefficient j (a + b)) base q =
      ccmRationalAdelicUnitizedCyclicTerm label
          (Function.update coefficient j a) base q +
        ccmRationalAdelicUnitizedCyclicTerm label
          (Function.update coefficient j b) base q := by
  classical
  let f : Fin (n + 1) → ℂ :=
    fun i => ccmRationalAdelicUnitizedCyclicFactor label coefficient base q i
  let fa := ccmRationalAdelicUnitizedCyclicFactor label
    (Function.update coefficient j a) base q j
  let fb := ccmRationalAdelicUnitizedCyclicFactor label
    (Function.update coefficient j b) base q j
  have hadd : (fun i => ccmRationalAdelicUnitizedCyclicFactor label
      (Function.update coefficient j (a + b)) base q i) =
      Function.update f j (fa + fb) := by
    funext i
    by_cases hij : i = j
    · subst i
      dsimp [fa, fb]
      simp only [Function.update_self]
      unfold ccmRationalAdelicUnitizedCyclicFactor
      simp only [Function.update_self]
      exact ccmRationalAdelicUnitizedFiberCoefficient_add
        (label j) a b (base j) _ q
    · rw [ccmRationalAdelicUnitizedCyclicFactor_eq_fiberCoefficient]
      simp only [Function.update_of_ne hij]
      rfl
  have ha : (fun i => ccmRationalAdelicUnitizedCyclicFactor label
      (Function.update coefficient j a) base q i) = Function.update f j fa := by
    funext i
    by_cases hij : i = j
    · subst i
      simp [f, fa]
    · rw [ccmRationalAdelicUnitizedCyclicFactor_eq_fiberCoefficient]
      simp only [Function.update_of_ne hij]
      rfl
  have hb : (fun i => ccmRationalAdelicUnitizedCyclicFactor label
      (Function.update coefficient j b) base q i) = Function.update f j fb := by
    funext i
    by_cases hij : i = j
    · subst i
      simp [f, fb]
    · rw [ccmRationalAdelicUnitizedCyclicFactor_eq_fiberCoefficient]
      simp only [Function.update_of_ne hij]
      rfl
  change (∏ i, ccmRationalAdelicUnitizedCyclicFactor label
      (Function.update coefficient j (a + b)) base q i) =
    (∏ i, ccmRationalAdelicUnitizedCyclicFactor label
      (Function.update coefficient j a) base q i) +
    ∏ i, ccmRationalAdelicUnitizedCyclicFactor label
      (Function.update coefficient j b) base q i
  rw [hadd, ha, hb,
    Finset.prod_update_of_mem (Finset.mem_univ j),
    Finset.prod_update_of_mem (Finset.mem_univ j),
    Finset.prod_update_of_mem (Finset.mem_univ j)]
  ring

theorem ccmRationalAdelicUnitizedCyclicTerm_update_smul {n : ℕ}
    (label : Fin (n + 1) → Label)
    (coefficient : (i : Fin (n + 1)) → Fiber (label i))
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase)
    (q : CCMRationalUnit) (j : Fin (n + 1)) (z : ℂ) (a : Fiber (label j)) :
    ccmRationalAdelicUnitizedCyclicTerm label
        (Function.update coefficient j (z • a)) base q =
      z * ccmRationalAdelicUnitizedCyclicTerm label
        (Function.update coefficient j a) base q := by
  classical
  let f : Fin (n + 1) → ℂ :=
    fun i => ccmRationalAdelicUnitizedCyclicFactor label coefficient base q i
  let fa := ccmRationalAdelicUnitizedCyclicFactor label
    (Function.update coefficient j a) base q j
  have hsmul : (fun i => ccmRationalAdelicUnitizedCyclicFactor label
      (Function.update coefficient j (z • a)) base q i) =
      Function.update f j (z * fa) := by
    funext i
    by_cases hij : i = j
    · subst i
      dsimp [fa]
      simp only [Function.update_self]
      unfold ccmRationalAdelicUnitizedCyclicFactor
      simp only [Function.update_self]
      exact ccmRationalAdelicUnitizedFiberCoefficient_smul
        (label j) z a (base j) _ q
    · rw [ccmRationalAdelicUnitizedCyclicFactor_eq_fiberCoefficient]
      simp only [Function.update_of_ne hij]
      rfl
  have ha : (fun i => ccmRationalAdelicUnitizedCyclicFactor label
      (Function.update coefficient j a) base q i) = Function.update f j fa := by
    funext i
    by_cases hij : i = j
    · subst i
      simp [f, fa]
    · rw [ccmRationalAdelicUnitizedCyclicFactor_eq_fiberCoefficient]
      simp only [Function.update_of_ne hij]
      rfl
  change (∏ i, ccmRationalAdelicUnitizedCyclicFactor label
      (Function.update coefficient j (z • a)) base q i) =
    z * ∏ i, ccmRationalAdelicUnitizedCyclicFactor label
      (Function.update coefficient j a) base q i
  rw [hsmul, ha,
    Finset.prod_update_of_mem (Finset.mem_univ j),
    Finset.prod_update_of_mem (Finset.mem_univ j)]
  ring

theorem ccmRationalAdelicUnitizedCyclicRestriction_update_add {n : ℕ}
    (label : Fin (n + 1) → Label)
    (coefficient : (i : Fin (n + 1)) → Fiber (label i))
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase)
    (j : Fin (n + 1)) (a b : Fiber (label j)) :
    ccmRationalAdelicUnitizedCyclicRestriction label
        (Function.update coefficient j (a + b)) base =
      ccmRationalAdelicUnitizedCyclicRestriction label
          (Function.update coefficient j a) base +
        ccmRationalAdelicUnitizedCyclicRestriction label
          (Function.update coefficient j b) base := by
  classical
  by_cases hscalar : ccmRationalAdelicUnitizedAllScalar label
  · rw [ccmRationalAdelicUnitizedCyclicRestriction_allScalar _ _ _ hscalar,
      ccmRationalAdelicUnitizedCyclicRestriction_allScalar _ _ _ hscalar,
      ccmRationalAdelicUnitizedCyclicRestriction_allScalar _ _ _ hscalar]
    exact ccmRationalAdelicUnitizedCyclicTerm_update_add
      label coefficient base 1 j a b
  · by_cases hscale : ccmRationalAdelicUnitizedCyclicTotalScale label = 1
    · simp only [ccmRationalAdelicUnitizedCyclicRestriction, hscalar, hscale,
        ↓reduceIte]
      rw [show (fun q => ccmRationalAdelicUnitizedCyclicTerm label
          (Function.update coefficient j (a + b)) base q) =
        fun q => ccmRationalAdelicUnitizedCyclicTerm label
            (Function.update coefficient j a) base q +
          ccmRationalAdelicUnitizedCyclicTerm label
            (Function.update coefficient j b) base q by
        funext q
        exact ccmRationalAdelicUnitizedCyclicTerm_update_add
          label coefficient base q j a b]
      exact (ccmRationalAdelicUnitizedCyclicTerm_summable_of_not_allScalar
        label (Function.update coefficient j a) base hscalar).tsum_add
          (ccmRationalAdelicUnitizedCyclicTerm_summable_of_not_allScalar
            label (Function.update coefficient j b) base hscalar)
    · simp [ccmRationalAdelicUnitizedCyclicRestriction, hscalar, hscale]

theorem ccmRationalAdelicUnitizedCyclicRestriction_update_smul {n : ℕ}
    (label : Fin (n + 1) → Label)
    (coefficient : (i : Fin (n + 1)) → Fiber (label i))
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase)
    (j : Fin (n + 1)) (z : ℂ) (a : Fiber (label j)) :
    ccmRationalAdelicUnitizedCyclicRestriction label
        (Function.update coefficient j (z • a)) base =
      z * ccmRationalAdelicUnitizedCyclicRestriction label
        (Function.update coefficient j a) base := by
  classical
  by_cases hscalar : ccmRationalAdelicUnitizedAllScalar label
  · rw [ccmRationalAdelicUnitizedCyclicRestriction_allScalar _ _ _ hscalar,
      ccmRationalAdelicUnitizedCyclicRestriction_allScalar _ _ _ hscalar]
    exact ccmRationalAdelicUnitizedCyclicTerm_update_smul
      label coefficient base 1 j z a
  · by_cases hscale : ccmRationalAdelicUnitizedCyclicTotalScale label = 1
    · simp only [ccmRationalAdelicUnitizedCyclicRestriction, hscalar, hscale,
        ↓reduceIte]
      rw [show (fun q => ccmRationalAdelicUnitizedCyclicTerm label
          (Function.update coefficient j (z • a)) base q) =
        fun q => z * ccmRationalAdelicUnitizedCyclicTerm label
          (Function.update coefficient j a) base q by
        funext q
        exact ccmRationalAdelicUnitizedCyclicTerm_update_smul
          label coefficient base q j z a]
      exact tsum_mul_left
    · simp [ccmRationalAdelicUnitizedCyclicRestriction, hscalar, hscale]

/-- Fixed dependent label tuple: normalized restriction is multilinear in every coefficient. -/
def ccmRationalAdelicUnitizedCyclicRestrictionLabelMultilinear {n : ℕ}
    (label : Fin (n + 1) → Label) :
    MultilinearMap ℂ (fun j => Fiber (label j))
      (CCMRationalAdelicClassSpaceFunctions n) :=
  MultilinearMap.mk'
    (fun coefficient base =>
      ccmRationalAdelicUnitizedCyclicRestriction label coefficient base)
    (by
      intro coefficient j a b
      funext base
      exact ccmRationalAdelicUnitizedCyclicRestriction_update_add
        label coefficient base j a b)
    (by
      intro coefficient j z a
      funext base
      exact ccmRationalAdelicUnitizedCyclicRestriction_update_smul
        label coefficient base j z a)

/-- Normalized multilinear restriction on dependent unitized coefficient families. -/
def ccmRationalAdelicUnitizedCyclicRestrictionDFinsuppMultilinear (n : ℕ) :
    MultilinearMap ℂ
      (fun _ : Fin (n + 1) => CCMRationalAdelicUnitizedDFinsupp)
      (CCMRationalAdelicClassSpaceFunctions n) := by
  classical
  exact MultilinearMap.fromDFinsuppEquiv
    (fun _ : Fin (n + 1) => Label) ℂ
    ccmRationalAdelicUnitizedCyclicRestrictionLabelMultilinear

/-- Linear normalized restriction on the exact unitized CCM cyclic source in degree `n`. -/
def ccmRationalAdelicUnitizedCyclicRestrictionLinear (n : ℕ) :
    PiTensorProduct ℂ (fun _ : Fin (n + 1) => Source) →ₗ[ℂ]
      CCMRationalAdelicClassSpaceFunctions n :=
  (PiTensorProduct.lift
      (ccmRationalAdelicUnitizedCyclicRestrictionDFinsuppMultilinear n)).comp
    (PiTensorProduct.congr
      (fun _ : Fin (n + 1) => ccmRationalAdelicSourceUnitizedDFinsuppEquiv)).toLinearMap

@[simp]
theorem ccmRationalAdelicUnitizedCyclicRestrictionLinear_tprod_single {n : ℕ}
    (label : Fin (n + 1) → Label)
    (coefficient : (j : Fin (n + 1)) → Fiber (label j)) :
    ccmRationalAdelicUnitizedCyclicRestrictionLinear n
        (PiTensorProduct.tprod ℂ (fun j =>
          ccmRationalAdelicUnitizedDFinsuppToSource
            (DFinsupp.single (label j) (coefficient j)))) =
      fun base =>
        ccmRationalAdelicUnitizedCyclicRestriction label coefficient base := by
  classical
  simp [ccmRationalAdelicUnitizedCyclicRestrictionLinear,
    ccmRationalAdelicUnitizedCyclicRestrictionDFinsuppMultilinear,
    ccmRationalAdelicSourceUnitizedDFinsuppEquiv]
  rfl

end RHTower
end GaloisForLFunctions
