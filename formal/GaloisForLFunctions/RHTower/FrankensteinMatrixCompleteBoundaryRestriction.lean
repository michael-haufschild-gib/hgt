import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolWindowGramSquare

/-!
# Frankenstein matrix-complete boundary restriction

Scalar Poisson/passivity formulations collapse a family of completed-Xi conormal columns to one
coherent sum.  That collapse cannot support Route P's trace contradiction: even a positive
semidefinite Gram matrix can have positive trace while its coherent sum vanishes.  This module
formalizes that obstruction by an explicit two-column cancellation packet.

The positive survivor is matrix-complete boundary restriction.  We use the genuine Loewner order
`A <=_L B` defined by positivity of `B-A`, prove its finite trace monotonicity, and state the exact
coefficient-faithful restriction law comparing every finite actual-Xi conormal Gram with one
injectively labelled P-G186 primitive Burnol-window source Gram.  The law is proved equivalent to
RH.  Thus it is a precisely typed terminal receiver: an RH proof still has to construct the
Loewner domination unconditionally from the completed pole--Gamma--von-Mangoldt boundary value at
the P-G185 wall.  No scalar passivity or target-fed trace hypothesis is hidden here.
-/

open Complex Matrix
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

/-! ## Coherent scalarization loses diagonal trace -/

/-- Two nonzero columns with complete coherent cancellation. -/
def frankensteinCancellationPair : Fin 2 → ℂ := ![1, -1]

/-- Positive Gram of the cancellation pair. -/
def frankensteinCancellationGram : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.gram ℂ frankensteinCancellationPair

theorem frankensteinCancellationGram_posSemidef :
    frankensteinCancellationGram.PosSemidef := by
  exact Matrix.posSemidef_gram ℂ _

theorem frankensteinCancellationPair_sum :
    ∑ i : Fin 2, frankensteinCancellationPair i = 0 := by
  simp [frankensteinCancellationPair, Fin.sum_univ_two]

/-- The diagonal trace remains two although the coherent sum is zero. -/
theorem re_trace_frankensteinCancellationGram :
    frankensteinCancellationGram.trace.re = 2 := by
  norm_num [frankensteinCancellationGram, Matrix.trace, Matrix.gram_apply,
    frankensteinCancellationPair, Fin.sum_univ_two]

/-- There is no universal passage from Gram trace to the squared norm of the coherent sum, even
for a two-column positive Gram.  This is the exact no-go behind scalar Boundary Passivity. -/
theorem no_universal_gramTrace_le_coherentNormSq :
    ¬ ∀ v : Fin 2 → ℂ,
      (Matrix.gram ℂ v).trace.re ≤ ‖∑ i : Fin 2, v i‖ ^ 2 := by
  intro h
  have hbad := h frankensteinCancellationPair
  rw [show Matrix.gram ℂ frankensteinCancellationPair =
      frankensteinCancellationGram by rfl,
    re_trace_frankensteinCancellationGram,
    frankensteinCancellationPair_sum] at hbad
  norm_num at hbad

/-! ## Matrix-complete positive survivor -/

/-- Finite Hermitian Loewner comparison, expressed without a pointwise matrix order. -/
def frankensteinMatrixLoewnerLE {N : ℕ}
    (A B : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  (B - A).PosSemidef

/-- Loewner domination controls real trace and therefore cannot suffer coherent cancellation. -/
theorem matrix_re_trace_mono_of_frankensteinLoewnerLE {N : ℕ}
    {A B : Matrix (Fin N) (Fin N) ℂ}
    (hAB : frankensteinMatrixLoewnerLE A B) :
    A.trace.re ≤ B.trace.re := by
  have htrace : 0 ≤ (B - A).trace := hAB.trace_nonneg
  have hre : 0 ≤ (B - A).trace.re := (RCLike.nonneg_iff.mp htrace).1
  rw [Matrix.trace_sub, Complex.sub_re] at hre
  linarith

/-- Exact W-H184 terminal receiver.  Every finite actual-Xi conormal Gram must be Loewner-dominated
by an injectively labelled finite P-G186 source-window Gram.  The source packet remains explicit;
the law does not replace it by a naked scalar capacity bound. -/
def RoutePMatrixCompleteBoundaryRestrictionLaw : Prop :=
  ∀ {N : ℕ} (q : Fin N → XiRightZeroCopy),
    ∃ (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ),
      Function.Injective pe ∧
      frankensteinMatrixLoewnerLE
        (routePStrictRightZeroBaseCauchyCubicKernelMatrix q)
        (routePPrimitiveBurnolWindowGramMatrix pe kappa)

theorem routePPrimitiveBaseCauchyTraceCapacityLaw_of_matrixCompleteBoundaryRestriction
    (htransport : RoutePMatrixCompleteBoundaryRestrictionLaw) :
    RoutePPrimitiveBaseCauchyTraceCapacityLaw := by
  intro N q
  obtain ⟨pe, kappa, hpe, hdom⟩ := htransport q
  exact (matrix_re_trace_mono_of_frankensteinLoewnerLE hdom).trans
    (re_trace_routePPrimitiveBurnolWindowGramMatrix_le_budget pe hpe kappa)

theorem riemannHypothesis_of_matrixCompleteBoundaryRestriction
    (htransport : RoutePMatrixCompleteBoundaryRestrictionLaw) :
    RiemannHypothesis :=
  routePPrimitiveBaseCauchyTraceCapacityLaw_iff_riemannHypothesis.mp
    (routePPrimitiveBaseCauchyTraceCapacityLaw_of_matrixCompleteBoundaryRestriction htransport)

theorem matrixCompleteBoundaryRestriction_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    RoutePMatrixCompleteBoundaryRestrictionLaw := by
  intro N q
  letI : IsEmpty XiRightZeroCopy := by
    constructor
    intro x
    obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH x.1
    have hpos := x.2
    rw [ht] at hpos
    simp at hpos
  letI : IsEmpty (Fin N) := ⟨fun i => isEmptyElim (q i)⟩
  refine ⟨fun i => isEmptyElim i, fun i => isEmptyElim i, ?_, ?_⟩
  · intro i
    exact isEmptyElim i
  · unfold frankensteinMatrixLoewnerLE
    have heq : routePPrimitiveBurnolWindowGramMatrix
        (fun i : Fin N => isEmptyElim i)
        (fun i : Fin N => isEmptyElim i) =
      routePStrictRightZeroBaseCauchyCubicKernelMatrix q :=
      Subsingleton.elim _ _
    rw [heq, sub_self]
    exact Matrix.PosSemidef.zero

/-- The matrix-complete restriction law is exactly the terminal RH gate.  Future progress must
construct its witnesses from source boundary data rather than postulate this proposition. -/
theorem routePMatrixCompleteBoundaryRestrictionLaw_iff_riemannHypothesis :
    RoutePMatrixCompleteBoundaryRestrictionLaw ↔ RiemannHypothesis := by
  exact ⟨riemannHypothesis_of_matrixCompleteBoundaryRestriction,
    matrixCompleteBoundaryRestriction_of_riemannHypothesis⟩

end

end RHTower
