import GaloisForLFunctions.RHTower.FormationAnchoredCubicHomotopyDefect

/-!
# The three-projection cubic as an aggregate spectral current

The cubic associator is half a single commutator `[P+Q+R, [P,Q]+[Q,R]+[R,P]]`.
Its matrix coefficient between aggregate eigenvectors contains their eigenvalue gap. Hence an
aggregate Hilbert eigenbasis forces its trace to vanish whenever the *combined* cubic is nuclear.
No separate cubic, adjacent product, or displacement is assumed to lie in a Schatten ideal.

This is not a general trace-cancellation theorem: a trace-class commutator of bounded operators
can have nonzero trace, and an arbitrary self-adjoint aggregate need not have an eigenbasis.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Sum of the three polarizations, without any commutation assumption. -/
def cubicAggregate (P Q R : H →L[ℂ] H) : H →L[ℂ] H := P + Q + R

/-- Cyclic oriented commutator current of the three polarizations. -/
def cubicCyclicCurrent (P Q R : H →L[ℂ] H) : H →L[ℂ] H :=
  (P * Q - Q * P) + (Q * R - R * Q) + (R * P - P * R)

omit [CompleteSpace H] in
/-- Exact aggregate-current identity. All terms containing three distinct projections cancel. -/
theorem cubicAggregate_commutator
    (P Q R : H →L[ℂ] H)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) (hR : IsIdempotentElem R) :
    cubicAggregate P Q R * cubicCyclicCurrent P Q R -
      cubicCyclicCurrent P Q R * cubicAggregate P Q R =
        formationAnchoredCubicAssociator R Q P + formationAnchoredCubicAssociator R Q P := by
  have hPP : P * P = P := hP
  have hQQ : Q * Q = Q := hQ
  have hRR : R * R = R := hR
  have hPPQ : P * (P * Q) = P * Q := by rw [← mul_assoc, hPP]
  have hPPR : P * (P * R) = P * R := by rw [← mul_assoc, hPP]
  have hQQP : Q * (Q * P) = Q * P := by rw [← mul_assoc, hQQ]
  have hQQR : Q * (Q * R) = Q * R := by rw [← mul_assoc, hQQ]
  have hRRP : R * (R * P) = R * P := by rw [← mul_assoc, hRR]
  have hRRQ : R * (R * Q) = R * Q := by rw [← mul_assoc, hRR]
  simp only [cubicAggregate, cubicCyclicCurrent, formationAnchoredCubicAssociator,
    formationAnchoredCubicDefect, restrictedProjectionCubicDefect,
    restrictedProjectionDisplacement]
  noncomm_ring [hPP, hQQ, hRR, hPPQ, hPPR, hQQP, hQQR, hRRP, hRRQ]

/-- Orthogonal polarizations have a self-adjoint aggregate. -/
theorem cubicAggregate_adjoint
    (P Q R : H →L[ℂ] H)
    (hP : adjoint P = P) (hQ : adjoint Q = Q) (hR : adjoint R = R) :
    adjoint (cubicAggregate P Q R) = cubicAggregate P Q R := by
  simp only [cubicAggregate, map_add, hP, hQ, hR]

/-- Exact eigenvalue-gap factor in each matrix coefficient of the combined cubic. -/
theorem cubicAggregate_eigenvector_current
    (P Q R : H →L[ℂ] H)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) (hR : IsIdempotentElem R)
    (hS : adjoint (cubicAggregate P Q R) = cubicAggregate P Q R)
    (x y : H) (ell em : ℝ)
    (hx : cubicAggregate P Q R x = (ell : ℂ) • x)
    (hy : cubicAggregate P Q R y = (em : ℂ) • y) :
    (2 : ℂ) * inner ℂ x (formationAnchoredCubicAssociator R Q P y) =
      ((ell : ℂ) - (em : ℂ)) * inner ℂ x (cubicCyclicCurrent P Q R y) := by
  have h := congrArg (fun T : H →L[ℂ] H => inner ℂ x (T y))
    (cubicAggregate_commutator P Q R hP hQ hR)
  simp only [sub_apply, mul_apply_eq_comp, add_apply, inner_sub_right, inner_add_right] at h
  have hleft : inner ℂ x (cubicAggregate P Q R (cubicCyclicCurrent P Q R y)) =
      (ell : ℂ) * inner ℂ x (cubicCyclicCurrent P Q R y) := by
    rw [← hS, adjoint_inner_right, hx, inner_smul_left]
    simp
  rw [hleft, hy, map_smul, inner_smul_right] at h
  linear_combination -h

/-- The cubic has zero compression between vectors with the same aggregate eigenvalue. -/
theorem cubicAggregate_same_eigenvalue_vanishes
    (P Q R : H →L[ℂ] H)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) (hR : IsIdempotentElem R)
    (hS : adjoint (cubicAggregate P Q R) = cubicAggregate P Q R)
    (x y : H) (ell : ℝ)
    (hx : cubicAggregate P Q R x = (ell : ℂ) • x)
    (hy : cubicAggregate P Q R y = (ell : ℂ) • y) :
    inner ℂ x (formationAnchoredCubicAssociator R Q P y) = 0 := by
  have h := cubicAggregate_eigenvector_current P Q R hP hQ hR hS x y ell ell hx hy
  simp only [sub_self, zero_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

/-- A complete aggregate eigenbasis rules out ordinary cubic trace charge. Only the combined
cubic is required to be nuclear; all individual transport channels may fail nuclearity. -/
theorem opTrace_cubicAssociator_eq_zero_of_aggregate_eigenbasis
    (P Q R : H →L[ℂ] H)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) (hR : IsIdempotentElem R)
    (hS : adjoint (cubicAggregate P Q R) = cubicAggregate P Q R)
    (hC : MemSchattenClass 1 (formationAnchoredCubicAssociator R Q P))
    {ι : Type*} (b : HilbertBasis ι ℂ H) (ell : ι → ℝ)
    (hb : ∀ i, cubicAggregate P Q R (b i) = (ell i : ℂ) • b i) :
    opTrace (formationAnchoredCubicAssociator R Q P) = 0 := by
  have hdiag (i : ι) : inner ℂ (b i) (formationAnchoredCubicAssociator R Q P (b i)) = 0 :=
    cubicAggregate_same_eigenvalue_vanishes P Q R hP hQ hR hS
      (b i) (b i) (ell i) (hb i) (hb i)
  obtain ⟨A, B, hA, hB, hfac⟩ := hC.one_isTraceClass
  have htrace := opTrace_comp_eq_tsum_basis hA hB b
  rw [← hfac] at htrace
  rw [htrace]
  simp only [hdiag, tsum_zero]

end RHTower
