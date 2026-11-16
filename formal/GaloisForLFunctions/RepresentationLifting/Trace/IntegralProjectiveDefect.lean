import GaloisForLFunctions.RepresentationLifting.Trace.ProjectiveTraceDuality
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Data.ZMod.Basic

/-!
# The integral defect of trace-zero representatives

The inclusion of integral trace-zero matrices into matrices modulo scalars is
injective. Its cokernel is canonically `ℤ/nℤ`, detected by trace modulo the
matrix size. Thus adding off-diagonal coordinates preserves the cyclic defect
of the root-to-weight lattice inclusion. This is the integral exact sequence
of Mohajer, *Semistable 1-Motives*, Proposition 9.3, over `ℤ`.
-/

namespace GaloisForLFunctions.RepresentationLifting

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Integral projective matrices are matrices modulo the scalar identity line. -/
abbrev IntegralProjectiveMatrix (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  Matrix ι ι ℤ ⧸ scalarMatrices ℤ ι

/-- The natural map from integral trace-zero matrices to projective matrices. -/
def traceZeroToProjective : traceZeroMatrices ℤ ι →ₗ[ℤ] IntegralProjectiveMatrix ι :=
  (scalarMatrices ℤ ι).mkQ.comp (traceZeroMatrices ℤ ι).subtype

private def matrixTraceResidue : Matrix ι ι ℤ →ₗ[ℤ] ZMod (Fintype.card ι) where
  toFun A := (A.trace : ℤ)
  map_add' A B := by simp [Matrix.trace_add]
  map_smul' c A := by
    change (((c • A).trace : ℤ) : ZMod (Fintype.card ι)) = c • _
    rw [Matrix.trace_smul]
    simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_id]

/-- Trace modulo the dimension descends through all integral scalar shifts. -/
def projectiveTraceResidue : IntegralProjectiveMatrix ι →ₗ[ℤ] ZMod (Fintype.card ι) :=
  (scalarMatrices ℤ ι).liftQ matrixTraceResidue (by
    intro A hA
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hA
    change (((c • (1 : Matrix ι ι ℤ)).trace : ℤ) : ZMod (Fintype.card ι)) = 0
    rw [Matrix.trace_smul, Matrix.trace_one]
    simp)

/-- The residue of a projective class is the residue of any representative's trace. -/
theorem projectiveTraceResidue_mk (A : Matrix ι ι ℤ) :
    projectiveTraceResidue ((scalarMatrices ℤ ι).mkQ A) =
      (A.trace : ZMod (Fintype.card ι)) := rfl

/-- The trace-zero inclusion has no integral scalar kernel. -/
theorem traceZeroToProjective_injective (p : ι) :
    Function.Injective (traceZeroToProjective (ι := ι)) := by
  letI : Nonempty ι := ⟨p⟩
  intro A B h
  have hm : A.val - B.val ∈ scalarMatrices ℤ ι :=
    (Submodule.Quotient.eq _).mp h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
  have ht := congrArg Matrix.trace hc
  have hzA : A.val.trace = 0 := A.property
  have hzB : B.val.trace = 0 := B.property
  rw [Matrix.trace_smul, Matrix.trace_one, Matrix.trace_sub, hzA, hzB, sub_self] at ht
  change c * (Fintype.card ι : ℤ) = 0 at ht
  have hn : (Fintype.card ι : ℤ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc0 : c = 0 := (mul_eq_zero.mp ht).resolve_right hn
  apply Subtype.ext
  exact sub_eq_zero.mp (by simpa only [hc0, zero_smul] using hc.symm)

/-- Zero trace residue is exactly the image of integral trace-zero matrices. -/
theorem projectiveTraceResidue_ker :
    (projectiveTraceResidue (ι := ι)).ker = LinearMap.range traceZeroToProjective := by
  ext q
  induction q using Submodule.Quotient.induction_on (scalarMatrices ℤ ι) with
  | H A =>
    constructor
    · intro h
      have ht : (Fintype.card ι : ℤ) ∣ A.trace :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
      obtain ⟨c, hc⟩ := (traceZero_representative_iff A).mpr ht
      refine ⟨⟨A - c • 1, hc⟩, ?_⟩
      apply (Submodule.Quotient.eq _).mpr
      apply Submodule.mem_span_singleton.mpr
      refine ⟨-c, ?_⟩
      change -c • (1 : Matrix ι ι ℤ) = (A - c • 1) - A
      rw [neg_smul]
      abel
    · rintro ⟨B, hB⟩
      rw [← hB]
      change ((B.val.trace : ℤ) : ZMod (Fintype.card ι)) = 0
      rw [show B.val.trace = 0 from B.property, Int.cast_zero]

/-- A single diagonal entry realizes every trace residue. -/
theorem projectiveTraceResidue_surjective (p : ι) :
    Function.Surjective (projectiveTraceResidue (ι := ι)) := by
  intro a
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective a
  refine ⟨(scalarMatrices ℤ ι).mkQ (Matrix.single p p z), ?_⟩
  rw [projectiveTraceResidue_mk]
  simp [Matrix.trace, Matrix.diag, Matrix.single_apply]

/-- The entire obstruction to an integral trace-zero representative is `ℤ/nℤ`. -/
noncomputable def integralProjectiveTraceCokernelEquiv (p : ι) :
    (IntegralProjectiveMatrix ι ⧸ LinearMap.range traceZeroToProjective) ≃ₗ[ℤ]
      ZMod (Fintype.card ι) :=
  (Submodule.quotEquivOfEq _ _ projectiveTraceResidue_ker.symm).trans
    (projectiveTraceResidue.quotKerEquivOfSurjective (projectiveTraceResidue_surjective p))

/-- The index of trace-zero matrices in integral projective matrices is the matrix size. -/
theorem integralProjectiveTrace_index (p : ι) :
    Nat.card (IntegralProjectiveMatrix ι ⧸ LinearMap.range traceZeroToProjective) =
      Fintype.card ι := by
  letI : Nonempty ι := ⟨p⟩
  letI : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  rw [Nat.card_congr (integralProjectiveTraceCokernelEquiv p).toEquiv,
    Nat.card_eq_fintype_card, ZMod.card]

#print axioms traceZeroToProjective_injective
#print axioms projectiveTraceResidue_ker
#print axioms integralProjectiveTraceCokernelEquiv
#print axioms integralProjectiveTrace_index

end GaloisForLFunctions.RepresentationLifting
