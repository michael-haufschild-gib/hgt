/-
# Schatten-1 factorization and bounded cyclicity of ordinary operator trace

The project defines Schatten classes through approximation numbers and trace class through a
Hilbert--Schmidt factorization.  This file proves the missing converse at exponent one.  For a
Schatten-1 operator `T`, the positive fourth root `R = sqrt |T|` is Hilbert--Schmidt because its
squared basis energy is the absolutely summable diagonal of `|T|`.  Polar decomposition then gives

`T = (U R) R`.

Two applications of Hilbert--Schmidt trace cyclicity yield `Tr(A T) = Tr(T A)` for every bounded
`A`.  This is standard operator theory; its role here is to make the exact Sonin relative ideal an
honest cyclic trace ideal.
-/

import GaloisForLFunctions.RHTower.TraceClassOperatorTrace

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Positive square root of the absolute value, used in the canonical trace-class factorization. -/
def traceClassRoot (T : H →L[ℂ] H) : H →L[ℂ] H :=
  CFC.sqrt (absOp T)

theorem traceClassRoot_nonneg (T : H →L[ℂ] H) :
    (0 : H →L[ℂ] H) ≤ traceClassRoot T :=
  CFC.sqrt_nonneg _

theorem isSelfAdjoint_traceClassRoot (T : H →L[ℂ] H) :
    IsSelfAdjoint (traceClassRoot T) :=
  .of_nonneg (traceClassRoot_nonneg T)

theorem traceClassRoot_mul_self (T : H →L[ℂ] H) :
    traceClassRoot T * traceClassRoot T = absOp T :=
  CFC.sqrt_mul_sqrt_self _ (absOp_nonneg T)

theorem traceClassRoot_comp_self (T : H →L[ℂ] H) :
    traceClassRoot T ∘L traceClassRoot T = absOp T :=
  traceClassRoot_mul_self T

/-- Taking the absolute value preserves Schatten-1 membership. -/
theorem memSchattenClass_one_absOp {T : H →L[ℂ] H}
    (hT : MemSchattenClass 1 T) :
    MemSchattenClass 1 (absOp T) := by
  have hcpt : IsCompactOperator T := hT.isCompactOperator one_pos
  have habscpt : IsCompactOperator (absOp T) := by
    rw [← adjoint_polarMap_comp_eq_absOp hcpt]
    exact hcpt.clm_comp (ContinuousLinearMap.adjoint (polarMap T hcpt))
  refine hT.congr fun n => ?_
  rw [approxNumber_eq_singVal habscpt, approxNumber_eq_singVal hcpt,
    singVal_absOp]

/-- The square root of `|T|` is Hilbert--Schmidt whenever `T` is Schatten-1. -/
theorem traceClassRoot_isHilbertSchmidt {T : H →L[ℂ] H}
    (hT : MemSchattenClass 1 T) :
    (traceClassRoot T).IsHilbertSchmidt := by
  have habs := (memSchattenClass_one_absOp hT).one_summable_inner_diag
  refine isHilbertSchmidt_of_summable (hsBasis ℂ H) ?_
  rw [← RCLike.summable_ofReal (𝕜 := ℂ)]
  refine habs.congr fun i => ?_
  have hsym := isSelfAdjoint_iff_isSymmetric.mp (isSelfAdjoint_traceClassRoot T)
  let e := hsBasis ℂ H i
  change inner ℂ e (absOp T e) = ((‖traceClassRoot T e‖ ^ (2 : ℕ) : ℝ) : ℂ)
  calc
    inner ℂ e (absOp T e) =
        inner ℂ e ((traceClassRoot T ∘L traceClassRoot T) e) := by
      rw [traceClassRoot_comp_self]
    _ = inner ℂ (traceClassRoot T e) (traceClassRoot T e) := by
      rw [comp_apply]
      exact (hsym e (traceClassRoot T e)).symm
    _ = ((‖traceClassRoot T e‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      push_cast
      rfl

/-- Every approximation-number Schatten-1 operator has a Hilbert--Schmidt factorization. -/
theorem MemSchattenClass.one_isTraceClass {T : H →L[ℂ] H}
    (hT : MemSchattenClass 1 T) :
    IsTraceClass T := by
  have hcpt : IsCompactOperator T := hT.isCompactOperator one_pos
  let R := traceClassRoot T
  let S := polarMap T hcpt ∘L R
  have hR : R.IsHilbertSchmidt := traceClassRoot_isHilbertSchmidt hT
  have hS : S.IsHilbertSchmidt := hR.comp_left (polarMap T hcpt)
  refine ⟨S, R, hS, hR, ?_⟩
  calc
    T = polarMap T hcpt ∘L absOp T := (polarMap_comp_absOp hcpt).symm
    _ = polarMap T hcpt ∘L (R ∘L R) := by rw [traceClassRoot_comp_self]
    _ = S ∘L R := by simp only [S, ContinuousLinearMap.comp_assoc]

/-- **Bounded cyclicity of the Schatten-1 trace.**  A bounded factor can pass through ordinary
operator trace whenever the other factor is Schatten-1. -/
theorem MemSchattenClass.one_opTrace_comp_comm {T : H →L[ℂ] H}
    (hT : MemSchattenClass 1 T) (A : H →L[ℂ] H) :
    opTrace (A ∘L T) = opTrace (T ∘L A) := by
  obtain ⟨S, U, hS, hU, hfac⟩ := hT.one_isTraceClass
  rw [hfac]
  calc
    opTrace (A ∘L (S ∘L U)) = opTrace ((A ∘L S) ∘L U) := by
      rw [ContinuousLinearMap.comp_assoc]
    _ = opTrace (U ∘L (A ∘L S)) :=
      ContinuousLinearMap.opTrace_comp_comm (hS.comp_left A) hU
    _ = opTrace ((U ∘L A) ∘L S) := by
      rw [ContinuousLinearMap.comp_assoc]
    _ = opTrace (S ∘L (U ∘L A)) :=
      ContinuousLinearMap.opTrace_comp_comm (hU.comp_right A) hS
    _ = opTrace ((S ∘L U) ∘L A) := by
      rw [ContinuousLinearMap.comp_assoc]

end RHTower
