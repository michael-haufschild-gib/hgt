import GaloisForLFunctions.RHTower.RestrictedUnitaryCubicContinuity
import GaloisForLFunctions.RHTower.RestrictedUnitaryCubicIndex
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace

/-!
# Homotopy invariance of the cubic restricted-unitary trace

Along a family of unitaries `U_s`, continuous in operator norm and with Hardy commutator `[P, U_s]`
continuous in Hilbert–Schmidt norm, the cubic defect `T(U_s) = (U_s† P U_s - P)³` moves
continuously in trace norm.  Its trace is the integer relative index, and a trace-norm continuous
integer-valued function on a preconnected parameter space is constant.  This is the homotopy
clause RUCRI-A(6): `Tr T(U_s)` does not depend on `s`.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The cubic trace of a restricted unitary is its integer relative index. -/
theorem opTrace_restrictedUnitaryCubicDefect_eq_relativeIndex
    {P U : H →L[ℂ] H} (hPidem : IsIdempotentElem P)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hUadj : ContinuousLinearMap.adjoint U * U = 1)
    (hUunit : U * ContinuousLinearMap.adjoint U = 1)
    (hcomm : (restrictedUnitaryCommutator P U).IsHilbertSchmidt) :
    opTrace (restrictedProjectionCubicDefect (restrictedUnitaryConjugateProjection P U) P) =
      (restrictedProjectionRelativeIndex (restrictedUnitaryConjugateProjection P U) P : ℂ) :=
  opTrace_restrictedProjectionCubicDefect_eq_relativeIndex _ P
    (restrictedUnitaryConjugateProjection_idempotent P U hPidem hUunit) hPidem
    (restrictedUnitaryConjugateProjection_adjoint P U hPadj) hPadj
    (restrictedUnitaryDisplacement_isHilbertSchmidt P U hUadj hcomm)

/-- **RUCRI-A(6).**  For a unitary family that is operator-norm continuous with Hilbert–Schmidt
continuous Hardy commutator on a preconnected parameter space, the cubic trace is constant. -/
theorem opTrace_restrictedUnitaryCubicDefect_eq_of_preconnected
    {I : Type*} [TopologicalSpace I] [PreconnectedSpace I]
    {P : H →L[ℂ] H} {U : I → H →L[ℂ] H}
    (hPidem : IsIdempotentElem P)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hUadj : ∀ i, ContinuousLinearMap.adjoint (U i) * U i = 1)
    (hUunit : ∀ i, U i * ContinuousLinearMap.adjoint (U i) = 1)
    (hcomm : ∀ i, (restrictedUnitaryCommutator P (U i)).IsHilbertSchmidt)
    (hU : ∀ i, Tendsto (fun j => ‖U j - U i‖) (𝓝 i) (𝓝 0))
    (hC : ∀ i, Tendsto (fun j =>
      (restrictedUnitaryCommutator P (U j) - restrictedUnitaryCommutator P (U i)).hsNorm)
      (𝓝 i) (𝓝 0))
    (i j : I) :
    opTrace (restrictedProjectionCubicDefect (restrictedUnitaryConjugateProjection P (U i)) P) =
      opTrace (restrictedProjectionCubicDefect
        (restrictedUnitaryConjugateProjection P (U j)) P) := by
  let n : I → ℤ := fun i =>
    restrictedProjectionRelativeIndex (restrictedUnitaryConjugateProjection P (U i)) P
  have hn : ∀ i, opTrace (restrictedProjectionCubicDefect
      (restrictedUnitaryConjugateProjection P (U i)) P) = (n i : ℂ) := fun i =>
    opTrace_restrictedUnitaryCubicDefect_eq_relativeIndex hPidem hPadj (hUadj i) (hUunit i)
      (hcomm i)
  have hS1 : ∀ i, MemSchattenClass 1 (restrictedProjectionCubicDefect
      (restrictedUnitaryConjugateProjection P (U i)) P) := fun i =>
    restrictedProjectionCubicDefect_memSchattenClass_one _ P
      (restrictedUnitaryDisplacement_isHilbertSchmidt P (U i) (hUadj i) (hcomm i))
  have hloc : IsLocallyConstant n := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro i
    have ht := traceNorm_restrictedUnitaryCubicDefect_tendsto (l := 𝓝 i) hPidem hPadj hUadj
      hUunit (hUadj i) (hUunit i) hcomm (hcomm i) (hU i) (hC i)
    filter_upwards [(tendsto_order.1 ht).2 1 one_pos] with j hj
    have hdiff : ‖((n j : ℂ) - (n i : ℂ))‖ < 1 := by
      rw [← hn j, ← hn i, ← opTrace_sub_of_memSchattenClass_one (hS1 j) (hS1 i)]
      exact (norm_opTrace_le_traceNorm ((hS1 j).one_sub (hS1 i))).trans_lt hj
    have hint : |((n j - n i : ℤ) : ℝ)| < 1 := by
      have : ‖((n j - n i : ℤ) : ℂ)‖ < 1 := by push_cast; exact hdiff
      rwa [Complex.norm_intCast] at this
    have hint' : |n j - n i| < 1 := by exact_mod_cast hint
    have hz : n j - n i = 0 := Int.abs_lt_one_iff.1 hint'
    omega
  rw [hn i, hn j, hloc.apply_eq_of_preconnectedSpace i j]

end RHTower
