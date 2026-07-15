import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaProduct

/-!
# Homogeneous multiple elliptic gamma carrier

The standard additive multiple elliptic gamma product is normalized by an implicit base period
`1`.  Restoring a variable base period `ω₀` turns its displayed argument and parameters into the
ratios `z / ω₀` and `ωᵢ / ω₀`.  Simultaneously scaling the argument and every period by the
same nonzero scalar is then an exact symmetry.

This is the value-level homogeneous carrier required before the affine dilation law can be
identified with a genuine Ward symmetry.  The normalization is standard; the mathematical point
here is to prevent the false claim that scaling only the already normalized parameters is a
symmetry.
-/

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type} [Fintype ι]

/-- Restore the missing base period in the normalized additive multiple elliptic gamma product. -/
def homogeneousMultipleEllipticGammaProduct
    (ω₀ : ℂ) (ω : ι → ℂ) (z : ℂ) : ℂ :=
  multipleEllipticGammaProduct (fun i => ω i / ω₀) (z / ω₀)

/-- Choosing base period `1` recovers the normalized product exactly. -/
@[simp]
theorem homogeneousMultipleEllipticGammaProduct_one
    (ω : ι → ℂ) (z : ℂ) :
    homogeneousMultipleEllipticGammaProduct 1 ω z =
      multipleEllipticGammaProduct ω z := by
  simp [homogeneousMultipleEllipticGammaProduct]

/-- Simultaneous nonzero scaling of the argument and every period is an exact symmetry. -/
theorem homogeneousMultipleEllipticGammaProduct_scale
    (c : ℂ) (hc : c ≠ 0) (ω₀ : ℂ) (ω : ι → ℂ) (z : ℂ) :
    homogeneousMultipleEllipticGammaProduct (c * ω₀) (fun i => c * ω i) (c * z) =
      homogeneousMultipleEllipticGammaProduct ω₀ ω z := by
  unfold homogeneousMultipleEllipticGammaProduct
  congr 1
  · funext i
    exact mul_div_mul_left (ω i) ω₀ hc
  · exact mul_div_mul_left z ω₀ hc

end

end GaloisForLFunctions
