import GaloisForLFunctions.HTGeometry.GomesTruncatedJetNilpotentPart

/-!
# The full nilpotent vector space of joint clock symmetries

The scalar augmentation kernel is exactly the set of joint matrices annihilated
by the jet-horizon power. This is the natural additive coordinate space for the
unipotent gauge factor, at every phase and horizon.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The scalar-augmentation kernel in the actual joint matrix algebra. -/
def gomesTruncatedJetNilpotentSpace (n : ℕ) (z : ℂ) :
    Submodule ℂ (gomesTruncatedJetJointAlgebra n z) :=
  LinearMap.ker (gomesTruncatedJetAugmentation n z).toLinearMap

/-- Membership in the nilpotent coordinate space is exactly vanishing of the actual scalar observation. -/
theorem gomesTruncatedJetNilpotentSpace_mem_iff (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetJointAlgebra n z) :
    E ∈ gomesTruncatedJetNilpotentSpace n z ↔ gomesTruncatedJetAugmentation n z E = 0 := Iff.rfl

/-- The coordinate space is precisely the full set of horizon-nilpotent joint matrices. -/
theorem gomesTruncatedJetNilpotentSpace_mem_iff_pow (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetJointAlgebra n z) :
    E ∈ gomesTruncatedJetNilpotentSpace n z ↔ E.val ^ (n + 1) = 0 := by
  rw [gomesTruncatedJetNilpotentSpace_mem_iff]
  constructor
  · intro h
    simpa only [h, map_zero, sub_zero] using gomesTruncatedJetJointAlgebra_sub_scalar_pow n z E
  · intro h
    have hE : E ^ (n + 1) = 0 := Subtype.ext h
    have ha := congrArg (gomesTruncatedJetAugmentation n z) hE
    simp only [map_pow, map_zero] at ha
    exact (pow_eq_zero_iff (Nat.succ_ne_zero n)).mp ha

/-- Every actual coordinate has zero scalar augmentation. -/
theorem gomesTruncatedJetNilpotentSpace_augmentation (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetNilpotentSpace n z) :
    gomesTruncatedJetAugmentation n z E.val = 0 := E.property

/-- Every actual coordinate matrix is annihilated by the finite horizon power. -/
theorem gomesTruncatedJetNilpotentSpace_pow (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetNilpotentSpace n z) : E.val.val ^ (n + 1) = 0 :=
  (gomesTruncatedJetNilpotentSpace_mem_iff_pow n z E.val).mp E.property

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
