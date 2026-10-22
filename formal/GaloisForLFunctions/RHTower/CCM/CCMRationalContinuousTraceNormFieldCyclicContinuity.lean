import GaloisForLFunctions.RHTower.CyclicBarProjectiveContinuity
import GaloisForLFunctions.RHTower.CCM.CCMRationalContinuousTraceNormFieldProjectiveTopology

/-!
# Cyclic continuity for continuous trace-norm fields

Independent class-space evaluation intertwines pointwise field faces,
degeneracies, and rotation with the corresponding projective fibre operators.
Consequently all cyclic generators are continuous for the exact
continuous-field projective topology.
-/

noncomputable section

open scoped TensorProduct

namespace GaloisForLFunctions.RHTower

private abbrev Base := CCMRationalClassSpaceSection
private abbrev Fiber := CCMRationalMoritaTraceNormL1Unitization
private abbrev Field := CCMRationalContinuousTraceNormField

def ccmRationalContinuousFieldFaceBaseExpansion {n : ℕ}
    (i : Fin (n + 2)) (base : Fin (n + 1) → Base) : Fin (n + 2) → Base :=
  Fin.lastCases
    ((Fin.last (n + 1)).insertNth (base 0) base)
    (fun j => j.succ.insertNth (base j) base) i

theorem ccmRationalContinuousFieldFaceEvaluationTuple {n : ℕ}
    (i : Fin (n + 2)) (base : Fin (n + 1) → Base)
    (F : Fin (n + 2) → Field) :
    cyclicBarFaceTuple i
        (fun j => F j (ccmRationalContinuousFieldFaceBaseExpansion i base j)) =
      fun k => cyclicBarFaceTuple i F k (base k) := by
  induction i using Fin.lastCases with
  | last =>
      funext k
      by_cases hk : k = 0
      · subst k
        simp [cyclicBarFaceTuple, cyclicBarFaceWrapTuple,
          ccmRationalContinuousFieldFaceBaseExpansion]
      · simp only [cyclicBarFaceTuple, Fin.lastCases_last,
          cyclicBarFaceWrapTuple, Function.update_of_ne hk,
          Fin.removeNth_last]
        change F k.castSucc
          (ccmRationalContinuousFieldFaceBaseExpansion
            (Fin.last (n + 1)) base k.castSucc) = F k.castSucc (base k)
        simp [ccmRationalContinuousFieldFaceBaseExpansion, Fin.snoc,
          Nat.le_of_lt_succ k.isLt]
  | cast i =>
      funext k
      by_cases hk : k = i
      · subst k
        have hi : i.castSucc = i.succ.succAbove i :=
          (cyclicBar_succ_succAbove_self i).symm
        simp only [cyclicBarFaceTuple, Fin.lastCases_castSucc,
          cyclicBarFaceNonwrapTuple, Function.update_self]
        change F i.castSucc
            (ccmRationalContinuousFieldFaceBaseExpansion i.castSucc base i.castSucc) *
              F i.succ
                (ccmRationalContinuousFieldFaceBaseExpansion i.castSucc base i.succ) =
          F i.castSucc (base i) * F i.succ (base i)
        rw [show ccmRationalContinuousFieldFaceBaseExpansion i.castSucc base =
            i.succ.insertNth (base i) base by
          simp [ccmRationalContinuousFieldFaceBaseExpansion]]
        rw [hi, Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same]
      · simp [cyclicBarFaceTuple, cyclicBarFaceNonwrapTuple,
          ccmRationalContinuousFieldFaceBaseExpansion, hk, Fin.removeNth]

def ccmRationalContinuousFieldDegeneracyBaseContraction {n : ℕ}
    (i : Fin (n + 1)) (base : Fin (n + 2) → Base) : Fin (n + 1) → Base :=
  Fin.removeNth i.succ base

theorem ccmRationalContinuousFieldDegeneracyEvaluationTuple {n : ℕ}
    (i : Fin (n + 1)) (base : Fin (n + 2) → Base)
    (F : Fin (n + 1) → Field) :
    cyclicBarDegeneracyTuple i
        (fun j => F j
          (ccmRationalContinuousFieldDegeneracyBaseContraction i base j)) =
      fun k => cyclicBarDegeneracyTuple i F k (base k) := by
  funext k
  cases k using i.succ.succAboveCases with
  | x => simp [cyclicBarDegeneracyTuple,
      ccmRationalContinuousFieldDegeneracyBaseContraction]
  | p k => simp [cyclicBarDegeneracyTuple,
      ccmRationalContinuousFieldDegeneracyBaseContraction, Fin.removeNth]

def ccmRationalContinuousFieldRotateBasePullback {n : ℕ}
    (base : Fin (n + 1) → Base) : Fin (n + 1) → Base :=
  fun k => base (finRotate (n + 1) k)

theorem ccmRationalContinuousFieldRotateEvaluationTuple {n : ℕ}
    (base : Fin (n + 1) → Base) (F : Fin (n + 1) → Field) :
    cyclicBarRotateTuple
        (fun j => F j (ccmRationalContinuousFieldRotateBasePullback base j)) =
      fun k => cyclicBarRotateTuple F k (base k) := by
  funext k
  simp [cyclicBarRotateTuple, ccmRationalContinuousFieldRotateBasePullback]

theorem ccmRationalContinuousFieldFaceEvaluation {n : ℕ}
    (i : Fin (n + 2)) (base : Fin (n + 1) → Base)
    (x : CyclicBarTensor ℂ Field (n + 1)) :
    ccmRationalContinuousTraceNormFieldDegreeEvaluation base
        (cyclicBarFace (R := ℂ) (A := Field) i x) =
      cyclicBarFace (R := ℂ) (A := Fiber) i
        (ccmRationalContinuousTraceNormFieldDegreeEvaluation
          (ccmRationalContinuousFieldFaceBaseExpansion i base) x) := by
  refine PiTensorProduct.induction_on x ?_ ?_
  · intro r F
    simp [ccmRationalContinuousFieldFaceEvaluationTuple]
  · intro x y hx hy
    simp only [map_add, hx, hy]

theorem ccmRationalContinuousFieldDegeneracyEvaluation {n : ℕ}
    (i : Fin (n + 1)) (base : Fin (n + 2) → Base)
    (x : CyclicBarTensor ℂ Field n) :
    ccmRationalContinuousTraceNormFieldDegreeEvaluation base
        (cyclicBarDegeneracy (R := ℂ) (A := Field) i x) =
      cyclicBarDegeneracy (R := ℂ) (A := Fiber) i
        (ccmRationalContinuousTraceNormFieldDegreeEvaluation
          (ccmRationalContinuousFieldDegeneracyBaseContraction i base) x) := by
  refine PiTensorProduct.induction_on x ?_ ?_
  · intro r F
    simp [ccmRationalContinuousFieldDegeneracyEvaluationTuple]
  · intro x y hx hy
    simp only [map_add, hx, hy]

theorem ccmRationalContinuousFieldRotateEvaluation {n : ℕ}
    (base : Fin (n + 1) → Base) (x : CyclicBarTensor ℂ Field n) :
    ccmRationalContinuousTraceNormFieldDegreeEvaluation base
        (cyclicBarRotate (R := ℂ) (A := Field) n x) =
      cyclicBarRotate (R := ℂ) (A := Fiber) n
        (ccmRationalContinuousTraceNormFieldDegreeEvaluation
          (ccmRationalContinuousFieldRotateBasePullback base) x) := by
  refine PiTensorProduct.induction_on x ?_ ?_
  · intro r F
    simp [ccmRationalContinuousFieldRotateEvaluationTuple]
  · intro x y hx hy
    simp only [map_add, hx, hy]

theorem continuous_ccmRationalContinuousTraceNormFieldFace {n : ℕ}
    (i : Fin (n + 2)) :
    @Continuous (CyclicBarTensor ℂ Field (n + 1))
      (CyclicBarTensor ℂ Field n)
      (ccmRationalContinuousTraceNormFieldProjectiveTopology (n + 1))
      (ccmRationalContinuousTraceNormFieldProjectiveTopology n)
      (cyclicBarFace (R := ℂ) (A := Field) i) := by
  letI : TopologicalSpace (CyclicBarTensor ℂ Field (n + 1)) :=
    ccmRationalContinuousTraceNormFieldProjectiveTopology (n + 1)
  rw [continuous_induced_rng]
  apply continuous_pi
  intro base
  have hEval :
      @Continuous (CyclicBarTensor ℂ Field (n + 1))
        (CyclicBarTensor ℂ Fiber (n + 1))
        (ccmRationalContinuousTraceNormFieldProjectiveTopology (n + 1))
        inferInstance
        (ccmRationalContinuousTraceNormFieldDegreeEvaluation
          (ccmRationalContinuousFieldFaceBaseExpansion i base)) := by
    have hApply : Continuous (fun z :
        ((Fin (n + 2) → Base) → CyclicBarTensor ℂ Fiber (n + 1)) =>
          z (ccmRationalContinuousFieldFaceBaseExpansion i base)) :=
      continuous_apply (ccmRationalContinuousFieldFaceBaseExpansion i base)
    have hAll :
        @Continuous (CyclicBarTensor ℂ Field (n + 1))
          ((Fin (n + 2) → Base) → CyclicBarTensor ℂ Fiber (n + 1))
          (ccmRationalContinuousTraceNormFieldProjectiveTopology (n + 1))
          inferInstance
          (ccmRationalContinuousTraceNormFieldAllDegreeEvaluations (n + 1)) :=
      continuous_induced_dom
    exact hApply.comp hAll
  have h := (continuous_cyclicBarFace (A := Fiber) i).comp hEval
  convert h using 1
  funext x
  exact ccmRationalContinuousFieldFaceEvaluation i base x

theorem continuous_ccmRationalContinuousTraceNormFieldDegeneracy {n : ℕ}
    (i : Fin (n + 1)) :
    @Continuous (CyclicBarTensor ℂ Field n)
      (CyclicBarTensor ℂ Field (n + 1))
      (ccmRationalContinuousTraceNormFieldProjectiveTopology n)
      (ccmRationalContinuousTraceNormFieldProjectiveTopology (n + 1))
      (cyclicBarDegeneracy (R := ℂ) (A := Field) i) := by
  letI : TopologicalSpace (CyclicBarTensor ℂ Field n) :=
    ccmRationalContinuousTraceNormFieldProjectiveTopology n
  rw [continuous_induced_rng]
  apply continuous_pi
  intro base
  have hEval :
      @Continuous (CyclicBarTensor ℂ Field n)
        (CyclicBarTensor ℂ Fiber n)
        (ccmRationalContinuousTraceNormFieldProjectiveTopology n)
        inferInstance
        (ccmRationalContinuousTraceNormFieldDegreeEvaluation
          (ccmRationalContinuousFieldDegeneracyBaseContraction i base)) := by
    have hApply : Continuous (fun z :
        ((Fin (n + 1) → Base) → CyclicBarTensor ℂ Fiber n) =>
          z (ccmRationalContinuousFieldDegeneracyBaseContraction i base)) :=
      continuous_apply
        (ccmRationalContinuousFieldDegeneracyBaseContraction i base)
    have hAll :
        @Continuous (CyclicBarTensor ℂ Field n)
          ((Fin (n + 1) → Base) → CyclicBarTensor ℂ Fiber n)
          (ccmRationalContinuousTraceNormFieldProjectiveTopology n)
          inferInstance
          (ccmRationalContinuousTraceNormFieldAllDegreeEvaluations n) :=
      continuous_induced_dom
    exact hApply.comp hAll
  have h := (continuous_cyclicBarDegeneracy (A := Fiber) i).comp hEval
  convert h using 1
  funext x
  exact ccmRationalContinuousFieldDegeneracyEvaluation i base x

theorem continuous_ccmRationalContinuousTraceNormFieldRotate (n : ℕ) :
    @Continuous (CyclicBarTensor ℂ Field n)
      (CyclicBarTensor ℂ Field n)
      (ccmRationalContinuousTraceNormFieldProjectiveTopology n)
      (ccmRationalContinuousTraceNormFieldProjectiveTopology n)
      (cyclicBarRotate (R := ℂ) (A := Field) n) := by
  letI : TopologicalSpace (CyclicBarTensor ℂ Field n) :=
    ccmRationalContinuousTraceNormFieldProjectiveTopology n
  rw [continuous_induced_rng]
  apply continuous_pi
  intro base
  have hEval :
      @Continuous (CyclicBarTensor ℂ Field n)
        (CyclicBarTensor ℂ Fiber n)
        (ccmRationalContinuousTraceNormFieldProjectiveTopology n)
        inferInstance
        (ccmRationalContinuousTraceNormFieldDegreeEvaluation
          (ccmRationalContinuousFieldRotateBasePullback base)) := by
    have hApply : Continuous (fun z :
        ((Fin (n + 1) → Base) → CyclicBarTensor ℂ Fiber n) =>
          z (ccmRationalContinuousFieldRotateBasePullback base)) :=
      continuous_apply (ccmRationalContinuousFieldRotateBasePullback base)
    have hAll :
        @Continuous (CyclicBarTensor ℂ Field n)
          ((Fin (n + 1) → Base) → CyclicBarTensor ℂ Fiber n)
          (ccmRationalContinuousTraceNormFieldProjectiveTopology n)
          inferInstance
          (ccmRationalContinuousTraceNormFieldAllDegreeEvaluations n) :=
      continuous_induced_dom
    exact hApply.comp hAll
  have h := (continuous_cyclicBarRotate (A := Fiber) n).comp hEval
  convert h using 1
  funext x
  exact ccmRationalContinuousFieldRotateEvaluation base x

end GaloisForLFunctions.RHTower
