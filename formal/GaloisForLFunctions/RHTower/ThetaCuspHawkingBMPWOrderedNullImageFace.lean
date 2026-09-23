import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularCircleReconstruction

/-!
# PW-B ordered null image face of the literal full-circle kernel

In the direct two-event null chart, the reflected image cone does not start
at the direct vertex. Its first null coordinate is shifted by `2*y`, where
`y<0` is the original second-source radius. The exact direct-minus-image
kernel therefore carries a moving image face `u=-2*y`. This is the geometry
that a later nonseparable source transposition must retain.
-/

open Set

namespace RHTower.D4BMPWOrderedNullImageFace

open D4BMFullAngularCircle D4BMFullAngularReconstruction D4BMModularCore

noncomputable section
set_option autoImplicit false

/-- Direct causal support in the source-based null coordinates. -/
theorem direct_gate (u v : ℝ) :
    |(u - v) / 2| ≤ (u + v) / 2 ↔ 0 ≤ u ∧ 0 ≤ v := by
  rw [abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- The image gate is a translated quadrant, not the direct quadrant. -/
theorem image_gate (y u v : ℝ) :
    |2 * y + (u - v) / 2| ≤ (u + v) / 2 ↔
      0 ≤ u + 2 * y ∧ 0 ≤ v - 2 * y := by
  rw [abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- On the physical radial half-line, the sole extra image gate is the
moving lower `u` face. -/
theorem image_gate_on_physical_direct_quadrant
    (y u v : ℝ) (hy : y < 0) (_hu : 0 ≤ u) (hv : 0 ≤ v) :
    |2 * y + (u - v) / 2| ≤ (u + v) / 2 ↔ -2 * y ≤ u := by
  rw [image_gate]
  constructor
  · intro h
    linarith [h.1]
  · intro h
    constructor <;> linarith

/-- The original negative-radius condition cuts the image cone to a strict
ordered wedge. -/
theorem image_physical_wedge
    (y u v : ℝ) (hy : y < 0) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hx : y + (u - v) / 2 < 0)
    (hi : |2 * y + (u - v) / 2| ≤ (u + v) / 2) :
    -2 * y ≤ u ∧ u + 2 * y < v := by
  constructor
  · exact (image_gate_on_physical_direct_quadrant y u v hy hu hv).mp hi
  · linarith

/-- For two original negative-radius source events, the reflected image
causal cone lies inside the direct causal cone. Thus the full-circle kernel
has no hidden image support outside the direct null quadrant. -/
theorem image_implies_direct_on_physical_radial_domain
    (y u v : ℝ) (hy : y < 0)
    (hx : y + (u - v) / 2 < 0)
    (hi : |2 * y + (u - v) / 2| ≤ (u + v) / 2) :
    0 ≤ u ∧ 0 ≤ v := by
  have himage := (image_gate y u v).mp hi
  constructor
  · linarith [himage.1]
  · linarith [himage.1]

/-- Exact direct-minus-image theta-circle kernel in one source-based null
chart. The two causal gates are visibly different. -/
theorem kernel_shifted_image_face (q : XiZeroCopy) (branch : Bool)
    (y u v X k : ℝ) :
    angularDirichletKernel q branch ((u + v) / 2)
      (y + (u - v) / 2) y X k =
      ((if 0 ≤ u ∧ 0 ≤ v then
          angularMean q branch (Real.arcosh
            (D4BMCausalKernel.invariant ((u + v) / 2) (y + (u - v) / 2) y)) X k
          else 0) -
        (if 0 ≤ u + 2 * y ∧ 0 ≤ v - 2 * y then
          angularMean q branch (Real.arcosh
            (D4BMCausalKernel.invariant ((u + v) / 2) (y + (u - v) / 2) (-y))) X k
          else 0)) / 2 := by
  simp only [angularDirichletKernel, add_sub_cancel_left]
  rw [show y + (u - v) / 2 + y = 2 * y + (u - v) / 2 by ring]
  simp only [direct_gate, image_gate]

end
end RHTower.D4BMPWOrderedNullImageFace
