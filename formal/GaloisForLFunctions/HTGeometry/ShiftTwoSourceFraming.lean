import GaloisForLFunctions.HTGeometry.CanonicalDigammaSourceSelection

/-!
# A boundary framing reconstructs a shift-two source primitive

Passing from an additive source cocycle to its cohomology class forgets the primitive.  For the
completed Xi/Gamma step `2`, a one-sided asymptotic framing restores uniqueness: two
right-half-plane primitives with the same exact cocycle and difference tending to zero along each
positive shift-two ray are equal.

This is the source-framed positive counterpart to rational-gauge blindness of unframed shift
cohomology.  It is obtained from the unit-shift theorem by rescaling the source coordinate.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Two right-half-plane primitives of one exact shift-two cocycle agree when their difference
tends to zero along every positive shift-two ray. -/
theorem eqOn_rightHalfPlane_of_same_shiftTwoCocycle_and_tendsto_sub_zero
    (f g cocycle : ℂ → ℂ)
    (hf : ∀ z : ℂ, 0 < z.re → f (z + 2) = f z + cocycle z)
    (hg : ∀ z : ℂ, 0 < z.re → g (z + 2) = g z + cocycle z)
    (hlim : ∀ z : ℂ, 0 < z.re →
      Tendsto (fun n : ℕ => f (z + 2 * n) - g (z + 2 * n)) atTop (nhds 0)) :
    Set.EqOn f g {z : ℂ | 0 < z.re} := by
  have hscaled := eqOn_rightHalfPlane_of_same_unitCocycle_and_tendsto_sub_zero
    (fun z => f (2 * z)) (fun z => g (2 * z)) (fun z => cocycle (2 * z))
    (fun z hz => by
      have h2z : 0 < (2 * z).re := by
        norm_num [Complex.mul_re]
        linarith
      simpa [mul_add] using hf (2 * z) h2z)
    (fun z hz => by
      have h2z : 0 < (2 * z).re := by
        norm_num [Complex.mul_re]
        linarith
      simpa [mul_add] using hg (2 * z) h2z)
    (fun z hz => by
      have h2z : 0 < (2 * z).re := by
        norm_num [Complex.mul_re]
        linarith
      simpa [mul_add, mul_assoc] using hlim (2 * z) h2z)
  intro z hz
  change 0 < z.re at hz
  have hz2 : 0 < (z / 2).re := by
    norm_num [Complex.div_re]
    linarith
  have h := hscaled hz2
  have harg : (2 : ℂ) * (z / 2) = z := by ring
  simpa [harg] using h

end

end GaloisForLFunctions.HTGeometry
