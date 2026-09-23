import GaloisForLFunctions.HTGeometry.GramPairingCauchySchwarz

/-!
# The scaled atomic part of the Pick Gram matrix

An inserted atom contributes a rank-one term to the Pick kernel.  Evaluated at the node directly
above that atom and scaled by the height squared, the contribution is exactly the atom's
coefficient, with no error term at all: the two Cauchy factors are `∓ i y`, whose product is `y²`.

That exact cancellation is why the scaled Gram matrix has the coefficients themselves on the
diagonal in the limit, and hence why the negative index counts the negative coefficients.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

@[simp]
theorem conj_upperNode (a y : ℝ) :
    (starRingEnd ℂ) (upperNode a y) = (a : ℂ) - (y : ℂ) * Complex.I := by
  simp [upperNode, Complex.ext_iff]

/-- The Cauchy factor at the node directly above an atom. -/
theorem sub_upperNode_self (a y : ℝ) :
    (a : ℂ) - upperNode a y = -((y : ℂ) * Complex.I) := by
  simp [upperNode]

/-- The conjugate Cauchy factor at the node directly above an atom. -/
theorem sub_conj_upperNode_self (a y : ℝ) :
    (a : ℂ) - (starRingEnd ℂ) (upperNode a y) = (y : ℂ) * Complex.I := by
  rw [conj_upperNode]
  ring

/-- **The two Cauchy factors multiply to the height squared.**  This is the exact cancellation
behind the scaled atomic diagonal. -/
theorem sub_mul_sub_conj_upperNode (a y : ℝ) :
    ((a : ℂ) - upperNode a y) * ((a : ℂ) - (starRingEnd ℂ) (upperNode a y))
      = (y : ℂ) ^ (2 : ℕ) := by
  rw [sub_upperNode_self, sub_conj_upperNode_self]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **The scaled atomic diagonal is exactly the coefficient.**  Scaling by the height squared, an
atom's own rank-one contribution at the node above it equals its coefficient, with no limit
required. -/
theorem scaled_atomic_diagonal (a y : ℝ) (hy : y ≠ 0) (c : ℂ) :
    (y : ℂ) ^ (2 : ℕ) * (c / (((a : ℂ) - upperNode a y) *
        ((a : ℂ) - (starRingEnd ℂ) (upperNode a y)))) = c := by
  rw [sub_mul_sub_conj_upperNode]
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy
  field_simp

end

end GaloisForLFunctions.HTGeometry
