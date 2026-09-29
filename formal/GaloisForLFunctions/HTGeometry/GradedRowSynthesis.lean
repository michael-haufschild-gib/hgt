import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace
import GaloisForLFunctions.RHTower.TraceNormBound
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Graded row synthesis

For bounded operators `S : E → H` and `T : F → H` the row synthesis on the `L²` direct sum is
`[S T] (e, f) = S e + T f`.  Its adjoint is the column `y ↦ (S* y, T* y)`, so for a grading
`diag(σ, τ)` one has the graded covariance identity

`[S T] diag(σ, τ) [S T]* = σ SS* + τ TT*`.

If `S` and `T` are Hilbert–Schmidt so is `[S T]`, with `‖[S T]‖²_HS = ‖S‖²_HS + ‖T‖²_HS`, every
range covariance `SS*` is Schatten-one with trace `‖S‖²_HS`, and the graded covariance is
Schatten-one with trace `σ ‖S‖²_HS + τ ‖T‖²_HS`.
-/

open ContinuousLinearMap
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {E F H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The row synthesis `[S T] (e, f) = S e + T f` on the `L²` direct sum. -/
def rowSynthesis (S : E →L[ℂ] H) (T : F →L[ℂ] H) : WithLp 2 (E × F) →L[ℂ] H :=
  S ∘L WithLp.fstL 2 ℂ E F + T ∘L WithLp.sndL 2 ℂ E F

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace H] in
theorem rowSynthesis_apply (S : E →L[ℂ] H) (T : F →L[ℂ] H) (x : WithLp 2 (E × F)) :
    rowSynthesis S T x = S x.fst + T x.snd := rfl

/-- The column `y ↦ (S* y, T* y)`. -/
def columnAnalysis (S : E →L[ℂ] H) (T : F →L[ℂ] H) : H →L[ℂ] WithLp 2 (E × F) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℂ E F).symm : E × F →L[ℂ] WithLp 2 (E × F)) ∘L
    (adjoint S).prod (adjoint T)

theorem columnAnalysis_apply (S : E →L[ℂ] H) (T : F →L[ℂ] H) (y : H) :
    columnAnalysis S T y = WithLp.toLp 2 (adjoint S y, adjoint T y) := rfl

/-- The adjoint of the row synthesis is the column analysis. -/
theorem adjoint_rowSynthesis (S : E →L[ℂ] H) (T : F →L[ℂ] H) :
    adjoint (rowSynthesis S T) = columnAnalysis S T := by
  refine ((eq_adjoint_iff (columnAnalysis S T) (rowSynthesis S T)).mpr fun y x => ?_).symm
  rw [columnAnalysis_apply, WithLp.prod_inner_apply, rowSynthesis_apply, inner_add_right,
    adjoint_inner_left, adjoint_inner_left]
  rfl

/-- The block-diagonal operator `diag(P, Q)`. -/
def blockDiag (P : E →L[ℂ] E) (Q : F →L[ℂ] F) : WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℂ E F).symm : E × F →L[ℂ] WithLp 2 (E × F)) ∘L
    (P.prodMap Q) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℂ E F : WithLp 2 (E × F) →L[ℂ] E × F)

/-- `[S T] diag(P, Q) [S T]* = S P S* + T Q T*`. -/
theorem rowSynthesis_blockDiag_adjoint (S : E →L[ℂ] H) (T : F →L[ℂ] H) (P : E →L[ℂ] E)
    (Q : F →L[ℂ] F) :
    rowSynthesis S T ∘L blockDiag P Q ∘L adjoint (rowSynthesis S T)
      = S ∘L P ∘L adjoint S + T ∘L Q ∘L adjoint T := by
  rw [adjoint_rowSynthesis]
  ext y
  simp [rowSynthesis_apply, blockDiag, columnAnalysis_apply]

/-- The grading `diag(σ, τ)`. -/
def gradingOp (σ τ : ℂ) : WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F) :=
  blockDiag (σ • ContinuousLinearMap.id ℂ E) (τ • ContinuousLinearMap.id ℂ F)

/-- **The graded covariance identity** `[S T] diag(σ, τ) [S T]* = σ SS* + τ TT*`. -/
theorem rowSynthesis_grading_adjoint (S : E →L[ℂ] H) (T : F →L[ℂ] H) (σ τ : ℂ) :
    rowSynthesis S T ∘L gradingOp σ τ ∘L adjoint (rowSynthesis S T)
      = σ • (S ∘L adjoint S) + τ • (T ∘L adjoint T) := by
  rw [gradingOp, rowSynthesis_blockDiag_adjoint]
  ext y
  simp

theorem norm_columnAnalysis_sq (S : E →L[ℂ] H) (T : F →L[ℂ] H) (y : H) :
    ‖columnAnalysis S T y‖ ^ 2 = ‖adjoint S y‖ ^ 2 + ‖adjoint T y‖ ^ 2 := by
  rw [columnAnalysis_apply, WithLp.prod_norm_sq_eq_of_L2]
  rfl

theorem isHilbertSchmidt_columnAnalysis {S : E →L[ℂ] H} {T : F →L[ℂ] H}
    (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (columnAnalysis S T) := by
  show Summable fun i => ‖columnAnalysis S T (hsBasis ℂ H i)‖ ^ 2
  simp_rw [norm_columnAnalysis_sq]
  exact (hS.adjoint.summable _).add (hT.adjoint.summable _)

/-- The row synthesis of Hilbert–Schmidt operators is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_rowSynthesis {S : E →L[ℂ] H} {T : F →L[ℂ] H}
    (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (rowSynthesis S T) := by
  have h := (isHilbertSchmidt_columnAnalysis hS hT).adjoint
  rwa [← adjoint_rowSynthesis, adjoint_adjoint] at h

/-- `‖[S T]‖²_HS = ‖S‖²_HS + ‖T‖²_HS`. -/
theorem hsNormSq_rowSynthesis {S : E →L[ℂ] H} {T : F →L[ℂ] H}
    (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T) :
    hsNormSq (rowSynthesis S T) = hsNormSq S + hsNormSq T := by
  rw [← (isHilbertSchmidt_rowSynthesis hS hT).hsNormSq_adjoint, adjoint_rowSynthesis,
    ← hS.hsNormSq_adjoint, ← hT.hsNormSq_adjoint, hsNormSq, hsNormSq, hsNormSq]
  simp_rw [norm_columnAnalysis_sq]
  exact (hS.adjoint.summable _).tsum_add (hT.adjoint.summable _)

/-- A range covariance `SS*` of a Hilbert–Schmidt `S` is Schatten-one. -/
theorem memSchattenClass_one_comp_adjoint {S : E →L[ℂ] H} (hS : IsHilbertSchmidt S) :
    RHTower.MemSchattenClass 1 (S ∘L adjoint S) :=
  RHTower.memSchattenClass_one_comp hS hS.adjoint

omit [CompleteSpace H] in
theorem hsInner_self_eq_ofReal_hsNormSq' (T : E →L[ℂ] H) :
    hsInner T T = (hsNormSq T : ℂ) := by
  rw [hsInner, hsNormSq, Complex.ofReal_tsum]
  exact tsum_congr fun i => by rw [inner_self_eq_norm_sq_to_K]; norm_cast

/-- `tr(SS*) = ‖S‖²_HS`. -/
theorem opTrace_comp_adjoint {S : E →L[ℂ] H} (hS : IsHilbertSchmidt S) :
    opTrace (S ∘L adjoint S) = (hsNormSq S : ℂ) := by
  rw [opTrace_comp_comm hS hS.adjoint, opTrace_adjoint_comp_self, hsInner_self_eq_ofReal_hsNormSq']

/-- The graded covariance is Schatten-one with trace `σ ‖S‖²_HS + τ ‖T‖²_HS`. -/
theorem gradedCovariance_traceClass {S : E →L[ℂ] H} {T : F →L[ℂ] H}
    (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T) (σ τ : ℂ) :
    RHTower.MemSchattenClass 1 (σ • (S ∘L adjoint S) + τ • (T ∘L adjoint T)) ∧
      opTrace (σ • (S ∘L adjoint S) + τ • (T ∘L adjoint T))
        = σ * hsNormSq S + τ * hsNormSq T := by
  have h1 := RHTower.memSchattenClass_one_smul (memSchattenClass_one_comp_adjoint hS) σ
  have h2 := RHTower.memSchattenClass_one_smul (memSchattenClass_one_comp_adjoint hT) τ
  refine ⟨RHTower.memSchattenClass_one_add (h1.isCompactOperator one_pos)
    (h2.isCompactOperator one_pos) h1 h2, ?_⟩
  rw [RHTower.opTrace_add_of_memSchattenClass_one h1 h2, RHTower.opTrace_smul,
    RHTower.opTrace_smul, opTrace_comp_adjoint hS, opTrace_comp_adjoint hT]

end GaloisForLFunctions.HTGeometry
