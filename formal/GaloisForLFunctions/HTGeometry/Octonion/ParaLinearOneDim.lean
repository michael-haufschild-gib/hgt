import GaloisForLFunctions.HTGeometry.Octonion.ResolventIdentity

namespace GaloisForLFunctions.HTGeometry.Octonion.RealOctonion

noncomputable section

/-- The second right associator of a map on the one-dimensional octonion module. -/
def secondRightAssociator (F : RealOctonion → RealOctonion)
    (p x : RealOctonion) : RealOctonion :=
  F x * p - F (x * p)

/-- The paper's right regular scalar multiplication of a map, specialized to `𝕆`. -/
def rightRegularScalar (F : RealOctonion → RealOctonion)
    (p : RealOctonion) : RealOctonion → RealOctonion := fun x =>
  F (p * x) - secondRightAssociator F p x

/-- Paper equation (8.3): the right regular scalar multiplication of a left
multiplication map is left multiplication by the product. -/
theorem leftAction_rightRegularScalar (q p : RealOctonion) :
    rightRegularScalar (leftAction q) p = leftAction (q * p) := by
  funext x
  unfold rightRegularScalar secondRightAssociator leftAction
  have h := IsAlternative.associator_swap_last q p x
  unfold IsAlternative.associator at h
  linear_combination (norm := abel) -h

end
end GaloisForLFunctions.HTGeometry.Octonion.RealOctonion
