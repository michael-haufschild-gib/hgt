import GaloisForLFunctions.HTGeometry.PointedFisherCutoffWardTrace

/-!
# The change in a second moment after removing one direction

The diagonal of the squared perturbation is summable. The two cross terms
are rank-one readings and the remaining correction is their squared mass.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def diagonalReading (A : H →L[ℂ] H) := fun i => inner ℂ (hsBasis ℂ H i) (A (hsBasis ℂ H i))

private theorem rank_reading (x y : H) : HasSum (diagonalReading (rankOne ℂ x y)) (inner ℂ y x) := by
  rw [← HTGeometry.opTrace_rankOne]
  exact (HTGeometry.summable_inner_diag_rankOne x y).hasSum

/-- Rank-one perturbation formula for the trace of the square of a self-adjoint observable. -/
theorem rank_one_trace_square (A : {T : H →L[ℂ] H // IsSelfAdjoint T ∧ T.IsHilbertSchmidt})
    (v : H) (c : ℂ) :
    opTrace ((A.val-c • rankOne ℂ v v)^2) =
      opTrace (A.val^2)-2*c*inner ℂ v (A.val v)+c^2*(inner ℂ v v)^2 := by
  let R := rankOne ℂ v v
  have hl : A.val*R = rankOne ℂ (A.val v) v := by
    ext x
    change A.val ((inner ℂ v x) • v) = (inner ℂ v x) • A.val v
    rw [map_smul]
  have hr : R*A.val = rankOne ℂ v (A.val v) := by
    ext x
    change (inner ℂ v (A.val x)) • v = (inner ℂ (A.val v) x) • v
    have hi := adjoint_inner_left A.val x v
    rw [show adjoint A.val = A.val from A.property.1.star_eq] at hi
    rw [hi]
  have hrr : R*R = inner ℂ v v • R := by
    ext x
    change (inner ℂ v ((inner ℂ v x) • v)) • v = (inner ℂ v v) • ((inner ℂ v x) • v)
    rw [inner_smul_right,smul_smul,mul_comm]
  have hcross : inner ℂ (A.val v) v = inner ℂ v (A.val v) := by
    have hi := adjoint_inner_left A.val v v
    rwa [show adjoint A.val = A.val from A.property.1.star_eq] at hi
  have he : (A.val-c • R)^2 =
      A.val^2-c • rankOne ℂ (A.val v) v-c • rankOne ℂ v (A.val v)+
        (c*c*inner ℂ v v) • R := by
    calc
      _ = A.val*A.val - A.val*(c • R) - (c • R)*A.val + (c • R)*(c • R) := by noncomm_ring
      _ = _ := by simp only [pow_two,smul_mul_assoc,mul_smul_comm,smul_smul,hl,hr,hrr,mul_assoc]
  have ha : HasSum (diagonalReading (A.val^2)) (opTrace (A.val^2)) :=
    (summable_inner_diag_comp A.property.2 A.property.2 (hsBasis ℂ H)).hasSum
  have hh := ((ha.sub ((rank_reading (A.val v) v).mul_left c)).sub
    ((rank_reading v (A.val v)).mul_left c)).add
      ((rank_reading v v).mul_left (c*c*inner ℂ v v))
  rw [hcross] at hh
  rw [he,opTrace]
  have Hsum := hh.tsum_eq
  calc
    _ = ∑' i, ((diagonalReading (A.val^2) i-c*diagonalReading (rankOne ℂ (A.val v) v) i)-
      c*diagonalReading (rankOne ℂ v (A.val v)) i)+(c*c*inner ℂ v v)*diagonalReading R i := by
        apply tsum_congr
        intro i
        simp only [diagonalReading,add_apply,sub_apply,smul_apply,inner_add_right,inner_sub_right,inner_smul_right]
    _ = _ := Hsum.trans (by ring)

#print axioms rank_one_trace_square

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
