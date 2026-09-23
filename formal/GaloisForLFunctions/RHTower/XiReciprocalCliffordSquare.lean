import GaloisForLFunctions.RHTower.XiReciprocalSquareSourceCore

/-!
# A Clifford-polarized square route for the reciprocal Xi operator

An operator need not be self-adjoint for its square to be self-adjoint.  A source architecture
that splits an operator as `A + B`, with `A` self-adjoint, `B` skew-adjoint, and `A`, `B`
anticommuting, forces this weaker square symmetry: the mixed terms cancel and
`(A + B)^(2 : ℕ) = A^(2 : ℕ) + B^(2 : ℕ)`.

Applied to the compact reciprocal Xi divisor operator, such a splitting forces RH through the
existing reciprocal-square criterion.  The splitting predicate is also RH-equivalent, since under
RH the trivial splitting `A = R_Xi`, `B = 0` exists.  Consequently this module is a terminal bridge
and a circularity audit, not a source construction of the required Clifford polarization.
-/

open Complex

namespace RHTower

noncomputable section

/-- A self-adjoint and a skew-adjoint anticommuting pair has self-adjoint square after addition.
This is the abstract Clifford cancellation behind the reciprocal-square detour. -/
theorem square_isSelfAdjoint_of_self_skew_anticomm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : H →L[ℂ] H)
    (hA : IsSelfAdjoint A)
    (hB : ContinuousLinearMap.adjoint B = -B)
    (hanti : A * B = -(B * A)) :
    IsSelfAdjoint ((A + B) * (A + B)) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  change ContinuousLinearMap.adjoint ((A + B) ∘L (A + B)) =
    (A + B) ∘L (A + B)
  rw [ContinuousLinearMap.adjoint_comp, map_add, hA.adjoint_eq, hB]
  rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def]
  calc
    (A + -B) * (A + -B) = A * A - A * B - B * A + B * B := by
      noncomm_ring
    _ = A * A + B * B := by rw [hanti]; abel
    _ = A * A + A * B + B * A + B * B := by rw [hanti]; abel
    _ = (A + B) * (A + B) := by noncomm_ring

/-- A Clifford polarization of the reciprocal Xi operator: its Hermitian and skew-Hermitian
source pieces anticommute, so their mixed square vanishes. -/
def XiReciprocalCliffordPolarization : Prop :=
  ∃ A B : lp (fun _ : XiZeroCopy => ℂ) 2 →L[ℂ]
      lp (fun _ : XiZeroCopy => ℂ) 2,
    xiReciprocalOperator = A + B ∧
    IsSelfAdjoint A ∧
    ContinuousLinearMap.adjoint B = -B ∧
    A * B = -(B * A)

/-- A Clifford polarization makes the reciprocal square self-adjoint. -/
theorem xiReciprocalSquareOperator_isSelfAdjoint_of_cliffordPolarization
    (h : XiReciprocalCliffordPolarization) :
    IsSelfAdjoint xiReciprocalSquareOperator := by
  obtain ⟨A, B, hR, hA, hB, hanti⟩ := h
  rw [xiReciprocalSquareOperator, hR]
  exact square_isSelfAdjoint_of_self_skew_anticomm A B hA hB hanti

/-- A source-derived Clifford polarization of the reciprocal Xi operator forces RH. -/
theorem riemannHypothesis_of_xiReciprocalCliffordPolarization
    (h : XiReciprocalCliffordPolarization) : RiemannHypothesis :=
  riemannHypothesis_of_xiReciprocalSquareOperator_isSelfAdjoint
    (xiReciprocalSquareOperator_isSelfAdjoint_of_cliffordPolarization h)

/-- RH supplies the trivial Clifford splitting.  This proves that the bare splitting predicate is
an RH-equivalent consumer interface; a valid proof must construct it from the prime--Gamma source. -/
theorem xiReciprocalCliffordPolarization_of_riemannHypothesis
    (hRH : RiemannHypothesis) : XiReciprocalCliffordPolarization := by
  refine ⟨xiReciprocalOperator, 0, ?_,
    xiReciprocalOperator_isSelfAdjoint_of_rh hRH, ?_, ?_⟩
  · simp
  · simp
  · simp

/-- Exact circularity audit for the bare Clifford-polarization predicate. -/
theorem xiReciprocalCliffordPolarization_iff_riemannHypothesis :
    XiReciprocalCliffordPolarization ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_xiReciprocalCliffordPolarization,
    xiReciprocalCliffordPolarization_of_riemannHypothesis⟩

end

end RHTower
