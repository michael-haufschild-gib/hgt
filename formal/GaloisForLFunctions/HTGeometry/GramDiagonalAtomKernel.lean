import GaloisForLFunctions.HTGeometry.PerturbedNegativeDefinite

/-!
# The scaled Gram diagonal is the atom kernel

At a node just above the real axis the squared distance to a real point is exactly the denominator of
the scaled Poisson kernel.  So the diagonal entry of the height-scaled Pick Gram matrix is precisely
the atom kernel integral, and its limit is the mass of the node.

That identification is what connects the atom limit to the Krein index computation: the diagonal
entries are controlled by the atom limit, and the off-diagonal ones are then controlled by
Cauchy-Schwarz against them.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The node just above a real point at a given height. -/
def upperNode (a y : ℝ) : ℂ := (a : ℂ) + (y : ℂ) * Complex.I

@[simp]
theorem upperNode_re (a y : ℝ) : (upperNode a y).re = a := by
  simp [upperNode]

@[simp]
theorem upperNode_im (a y : ℝ) : (upperNode a y).im = y := by
  simp [upperNode]

/-- **The squared distance to an upper node is the kernel denominator.** -/
theorem normSq_sub_upperNode (a y t : ℝ) :
    Complex.normSq ((t : ℂ) - upperNode a y) = (t - a) ^ 2 + y ^ 2 := by
  simp [Complex.normSq_apply, upperNode]
  ring

/-- **The scaled Gram diagonal is the atom kernel.**  The height-squared scaling of the Pick kernel
at a single upper node is exactly the scaled Poisson kernel. -/
theorem atomKernel_eq_sq_div_normSq (a y t : ℝ) :
    atomKernel a y t = y ^ 2 / Complex.normSq ((t : ℂ) - upperNode a y) := by
  rw [normSq_sub_upperNode, atomKernel]

/-- The Cauchy kernel at an upper node has squared modulus the kernel denominator. -/
theorem normSq_inv_sub_upperNode (a y t : ℝ) :
    Complex.normSq (((t : ℂ) - upperNode a y)⁻¹) = ((t - a) ^ 2 + y ^ 2)⁻¹ := by
  rw [Complex.normSq_inv, normSq_sub_upperNode]

/-- **The diagonal Pick entry scaled by the height is the atom kernel.**  This is the pointwise
identity integrated to give the diagonal of the scaled Gram matrix. -/
theorem sq_mul_normSq_inv_eq_atomKernel (a y t : ℝ) :
    y ^ 2 * Complex.normSq (((t : ℂ) - upperNode a y)⁻¹) = atomKernel a y t := by
  rw [normSq_inv_sub_upperNode, atomKernel, div_eq_mul_inv]

end

end GaloisForLFunctions.HTGeometry
