import GaloisForLFunctions.RHTower.CyclicBarProjectiveContinuity
import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicClassSpaceProjectiveTopology

/-!
# Cyclic continuity on the rational adelic class space

Independent-base evaluation intertwines pointwise section faces, degeneracies, and cyclic
rotation with the corresponding operators on the natural `ℓ¹` trace-class Morita fiber.
Consequently every generator is continuous for the coefficientwise projective topology.
-/

noncomputable section
open scoped TensorProduct
open CategoryTheory

namespace GaloisForLFunctions.RHTower

private abbrev Base := CCMRationalAdelicMoritaBase
private abbrev Fiber := CCMRationalMoritaTraceClassL1Unitization
private abbrev Sections := CCMRationalAdelicMoritaClassSpaceAlgebra

def ccmRationalAdelicClassSpaceFaceBaseExpansion {n : ℕ} (i : Fin (n + 2))
    (base : Fin (n + 1) → Base) : Fin (n + 2) → Base :=
  Fin.lastCases
    ((Fin.last (n + 1)).insertNth (base 0) base)
    (fun j => j.succ.insertNth (base j) base) i

theorem ccmRationalAdelicClassSpaceFaceEvaluationTuple {n : ℕ} (i : Fin (n + 2))
    (base : Fin (n + 1) → Base) (f : Fin (n + 2) → Sections) :
    cyclicBarFaceTuple i
        (fun j => f j (ccmRationalAdelicClassSpaceFaceBaseExpansion i base j)) =
      fun k => cyclicBarFaceTuple i f k (base k) := by
  induction i using Fin.lastCases with
  | last =>
      funext k
      by_cases hk : k = 0
      · subst k
        simp [cyclicBarFaceTuple, cyclicBarFaceWrapTuple,
          ccmRationalAdelicClassSpaceFaceBaseExpansion]
      · simp only [cyclicBarFaceTuple, Fin.lastCases_last,
          cyclicBarFaceWrapTuple, Function.update_of_ne hk,
          Fin.removeNth_last]
        change f k.castSucc
          (ccmRationalAdelicClassSpaceFaceBaseExpansion (Fin.last (n + 1)) base k.castSucc) =
            f k.castSucc (base k)
        simp [ccmRationalAdelicClassSpaceFaceBaseExpansion, Fin.snoc,
          Nat.le_of_lt_succ k.isLt]
  | cast i =>
      funext k
      by_cases hk : k = i
      · subst k
        have hi : i.castSucc = i.succ.succAbove i :=
          (cyclicBar_succ_succAbove_self i).symm
        simp only [cyclicBarFaceTuple, Fin.lastCases_castSucc,
          cyclicBarFaceNonwrapTuple, Function.update_self]
        change f i.castSucc (ccmRationalAdelicClassSpaceFaceBaseExpansion i.castSucc base i.castSucc) *
            f i.succ (ccmRationalAdelicClassSpaceFaceBaseExpansion i.castSucc base i.succ) =
          f i.castSucc (base i) * f i.succ (base i)
        rw [show ccmRationalAdelicClassSpaceFaceBaseExpansion i.castSucc base =
          i.succ.insertNth (base i) base by
            simp [ccmRationalAdelicClassSpaceFaceBaseExpansion]]
        rw [hi, Fin.insertNth_apply_succAbove,
          Fin.insertNth_apply_same]
      · simp [cyclicBarFaceTuple, cyclicBarFaceNonwrapTuple,
          ccmRationalAdelicClassSpaceFaceBaseExpansion, hk, Fin.removeNth]

def ccmRationalAdelicClassSpaceDegeneracyBaseContraction {n : ℕ} (i : Fin (n + 1))
    (base : Fin (n + 2) → Base) : Fin (n + 1) → Base :=
  Fin.removeNth i.succ base

theorem ccmRationalAdelicClassSpaceDegeneracyEvaluationTuple {n : ℕ} (i : Fin (n + 1))
    (base : Fin (n + 2) → Base) (f : Fin (n + 1) → Sections) :
    cyclicBarDegeneracyTuple i
        (fun j => f j (ccmRationalAdelicClassSpaceDegeneracyBaseContraction i base j)) =
      fun k => cyclicBarDegeneracyTuple i f k (base k) := by
  funext k
  cases k using i.succ.succAboveCases with
  | x => simp [cyclicBarDegeneracyTuple, ccmRationalAdelicClassSpaceDegeneracyBaseContraction]
  | p k => simp [cyclicBarDegeneracyTuple, ccmRationalAdelicClassSpaceDegeneracyBaseContraction,
      Fin.removeNth]

def ccmRationalAdelicClassSpaceRotateBasePullback {n : ℕ} (base : Fin (n + 1) → Base) :
    Fin (n + 1) → Base :=
  fun k => base (finRotate (n + 1) k)

theorem ccmRationalAdelicClassSpaceRotateEvaluationTuple {n : ℕ}
    (base : Fin (n + 1) → Base) (f : Fin (n + 1) → Sections) :
    cyclicBarRotateTuple
        (fun j => f j (ccmRationalAdelicClassSpaceRotateBasePullback base j)) =
      fun k => cyclicBarRotateTuple f k (base k) := by
  funext k
  simp [cyclicBarRotateTuple, ccmRationalAdelicClassSpaceRotateBasePullback]

theorem ccmRationalAdelicClassSpaceFaceEvaluation {n : ℕ} (i : Fin (n + 2))
    (base : Fin (n + 1) → Base)
    (x : CyclicBarTensor ℂ Sections (n + 1)) :
    ccmRationalAdelicClassSpaceDegreeEvaluation base
        (cyclicBarFace (R := ℂ) (A := Sections) i x) =
      cyclicBarFace (R := ℂ) (A := Fiber) i
        (ccmRationalAdelicClassSpaceDegreeEvaluation
          (ccmRationalAdelicClassSpaceFaceBaseExpansion i base) x) := by
  refine PiTensorProduct.induction_on x ?_ ?_
  · intro r f
    simp [ccmRationalAdelicClassSpaceFaceEvaluationTuple]
  · intro x y hx hy
    simp only [map_add, hx, hy]

theorem ccmRationalAdelicClassSpaceDegeneracyEvaluation {n : ℕ} (i : Fin (n + 1))
    (base : Fin (n + 2) → Base)
    (x : CyclicBarTensor ℂ Sections n) :
    ccmRationalAdelicClassSpaceDegreeEvaluation base
        (cyclicBarDegeneracy (R := ℂ) (A := Sections) i x) =
      cyclicBarDegeneracy (R := ℂ) (A := Fiber) i
        (ccmRationalAdelicClassSpaceDegreeEvaluation
          (ccmRationalAdelicClassSpaceDegeneracyBaseContraction i base) x) := by
  refine PiTensorProduct.induction_on x ?_ ?_
  · intro r f
    simp [ccmRationalAdelicClassSpaceDegeneracyEvaluationTuple]
  · intro x y hx hy
    simp only [map_add, hx, hy]

theorem ccmRationalAdelicClassSpaceRotateEvaluation {n : ℕ}
    (base : Fin (n + 1) → Base)
    (x : CyclicBarTensor ℂ Sections n) :
    ccmRationalAdelicClassSpaceDegreeEvaluation base
        (cyclicBarRotate (R := ℂ) (A := Sections) n x) =
      cyclicBarRotate (R := ℂ) (A := Fiber) n
        (ccmRationalAdelicClassSpaceDegreeEvaluation
          (ccmRationalAdelicClassSpaceRotateBasePullback base) x) := by
  refine PiTensorProduct.induction_on x ?_ ?_
  · intro r f
    simp [ccmRationalAdelicClassSpaceRotateEvaluationTuple]
  · intro x y hx hy
    simp only [map_add, hx, hy]

theorem continuous_ccmRationalAdelicClassSpaceFace {n : ℕ} (i : Fin (n + 2)) :
    @Continuous
      (CyclicBarTensor ℂ Sections (n + 1))
      (CyclicBarTensor ℂ Sections n)
      (ccmRationalAdelicClassSpaceProjectiveTopology (n + 1))
      (ccmRationalAdelicClassSpaceProjectiveTopology n)
      (cyclicBarFace (R := ℂ) (A := Sections) i) := by
  letI : TopologicalSpace (CyclicBarTensor ℂ Sections (n + 1)) :=
    ccmRationalAdelicClassSpaceProjectiveTopology (n + 1)
  rw [continuous_induced_rng]
  apply continuous_pi
  intro base
  have hEval :
      @Continuous
        (CyclicBarTensor ℂ Sections (n + 1))
        (CyclicBarTensor ℂ Fiber (n + 1))
        (ccmRationalAdelicClassSpaceProjectiveTopology (n + 1))
        inferInstance
        (ccmRationalAdelicClassSpaceDegreeEvaluation
          (ccmRationalAdelicClassSpaceFaceBaseExpansion i base)) := by
    have hApply : Continuous (fun z :
        ((Fin (n + 2) → Base) → CyclicBarTensor ℂ Fiber (n + 1)) =>
          z (ccmRationalAdelicClassSpaceFaceBaseExpansion i base)) :=
      continuous_apply (ccmRationalAdelicClassSpaceFaceBaseExpansion i base)
    have hAll :
        @Continuous
          (CyclicBarTensor ℂ Sections (n + 1))
          ((Fin (n + 2) → Base) → CyclicBarTensor ℂ Fiber (n + 1))
          (ccmRationalAdelicClassSpaceProjectiveTopology (n + 1))
          inferInstance
          (ccmRationalAdelicClassSpaceAllDegreeEvaluations (n + 1)) :=
      continuous_induced_dom
    exact hApply.comp hAll
  have h := (continuous_cyclicBarFace (A := Fiber) i).comp hEval
  convert h using 1
  funext x
  exact ccmRationalAdelicClassSpaceFaceEvaluation i base x

theorem continuous_ccmRationalAdelicClassSpaceDegeneracy {n : ℕ} (i : Fin (n + 1)) :
    @Continuous
      (CyclicBarTensor ℂ Sections n)
      (CyclicBarTensor ℂ Sections (n + 1))
      (ccmRationalAdelicClassSpaceProjectiveTopology n)
      (ccmRationalAdelicClassSpaceProjectiveTopology (n + 1))
      (cyclicBarDegeneracy (R := ℂ) (A := Sections) i) := by
  letI : TopologicalSpace (CyclicBarTensor ℂ Sections n) :=
    ccmRationalAdelicClassSpaceProjectiveTopology n
  rw [continuous_induced_rng]
  apply continuous_pi
  intro base
  have hEval :
      @Continuous
        (CyclicBarTensor ℂ Sections n)
        (CyclicBarTensor ℂ Fiber n)
        (ccmRationalAdelicClassSpaceProjectiveTopology n)
        inferInstance
        (ccmRationalAdelicClassSpaceDegreeEvaluation
          (ccmRationalAdelicClassSpaceDegeneracyBaseContraction i base)) := by
    have hApply : Continuous (fun z :
        ((Fin (n + 1) → Base) → CyclicBarTensor ℂ Fiber n) =>
          z (ccmRationalAdelicClassSpaceDegeneracyBaseContraction i base)) :=
      continuous_apply (ccmRationalAdelicClassSpaceDegeneracyBaseContraction i base)
    have hAll :
        @Continuous
          (CyclicBarTensor ℂ Sections n)
          ((Fin (n + 1) → Base) → CyclicBarTensor ℂ Fiber n)
          (ccmRationalAdelicClassSpaceProjectiveTopology n)
          inferInstance
          (ccmRationalAdelicClassSpaceAllDegreeEvaluations n) :=
      continuous_induced_dom
    exact hApply.comp hAll
  have h := (continuous_cyclicBarDegeneracy (A := Fiber) i).comp hEval
  convert h using 1
  funext x
  exact ccmRationalAdelicClassSpaceDegeneracyEvaluation i base x

theorem continuous_ccmRationalAdelicClassSpaceRotate (n : ℕ) :
    @Continuous
      (CyclicBarTensor ℂ Sections n)
      (CyclicBarTensor ℂ Sections n)
      (ccmRationalAdelicClassSpaceProjectiveTopology n)
      (ccmRationalAdelicClassSpaceProjectiveTopology n)
      (cyclicBarRotate (R := ℂ) (A := Sections) n) := by
  letI : TopologicalSpace (CyclicBarTensor ℂ Sections n) :=
    ccmRationalAdelicClassSpaceProjectiveTopology n
  rw [continuous_induced_rng]
  apply continuous_pi
  intro base
  have hEval :
      @Continuous
        (CyclicBarTensor ℂ Sections n)
        (CyclicBarTensor ℂ Fiber n)
        (ccmRationalAdelicClassSpaceProjectiveTopology n)
        inferInstance
        (ccmRationalAdelicClassSpaceDegreeEvaluation
          (ccmRationalAdelicClassSpaceRotateBasePullback base)) := by
    have hApply : Continuous (fun z :
        ((Fin (n + 1) → Base) → CyclicBarTensor ℂ Fiber n) =>
          z (ccmRationalAdelicClassSpaceRotateBasePullback base)) :=
      continuous_apply (ccmRationalAdelicClassSpaceRotateBasePullback base)
    have hAll :
        @Continuous
          (CyclicBarTensor ℂ Sections n)
          ((Fin (n + 1) → Base) → CyclicBarTensor ℂ Fiber n)
          (ccmRationalAdelicClassSpaceProjectiveTopology n)
          inferInstance
          (ccmRationalAdelicClassSpaceAllDegreeEvaluations n) :=
      continuous_induced_dom
    exact hApply.comp hAll
  have h := (continuous_cyclicBarRotate (A := Fiber) n).comp hEval
  convert h using 1
  funext x
  exact ccmRationalAdelicClassSpaceRotateEvaluation base x

end GaloisForLFunctions.RHTower
