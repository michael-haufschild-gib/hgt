import Mathlib

/-!
# The primitive flux identity of a coordinate cutoff

A coordinatewise cutoff does not commute with a translation-invariant remainder, so inserting it in
a differentiated normal equation produces a defect.  The defect is exactly the `L`-derivative of the
commutator profile plus two zero-order terms — no second derivative and no new boundary condition
appear.  Keeping the derivative on the commutator is what puts the defect in its primitive source
class.
-/

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The commutator profile `[C, M] F`. -/
def fluxCommutatorProfile (C : X →L[ℝ] X) (M : ℝ → (X →L[ℝ] X)) (F : ℝ → X) : ℝ → X :=
  fun L => C (M L (F L)) - M L (C (F L))

/-- The differentiated transport operator `(2L I + C) ∂_L` applied to a profile with a known
derivative. -/
def transportApply (C : X →L[ℝ] X) (L : ℝ) (D : X) : X := (2 * L : ℝ) • D + C D

theorem hasDerivAt_fluxCommutatorProfile {C : X →L[ℝ] X} {M : ℝ → (X →L[ℝ] X)}
    {Md : X →L[ℝ] X} {F : ℝ → X} {Fd : X} {L : ℝ}
    (hM : HasDerivAt M Md L) (hF : HasDerivAt F Fd L) :
    HasDerivAt (fluxCommutatorProfile C M F)
      (C (Md (F L) + M L Fd) - (Md (C (F L)) + M L (C Fd))) L := by
  have hCF : HasDerivAt (fun L => C (F L)) (C Fd) L := C.hasFDerivAt.comp_hasDerivAt L hF
  have h1 : HasDerivAt (fun L => M L (F L)) (Md (F L) + M L Fd) L := hM.clm_apply hF
  have h2 : HasDerivAt (fun L => M L (C (F L))) (Md (C (F L)) + M L (C Fd)) L :=
    hM.clm_apply hCF
  have h3 : HasDerivAt (fun L => C (M L (F L))) (C (Md (F L) + M L Fd)) L :=
    C.hasFDerivAt.comp_hasDerivAt L h1
  exact h3.sub h2

/-- **The primitive flux identity `(2)`.**  Commuting a coordinate cutoff past the differentiated
transport operator produces exactly the derivative of the commutator profile plus the zero-order
term `M' (2L I + C) F`. -/
theorem primitive_flux_identity (C : X →L[ℝ] X) (M : ℝ → (X →L[ℝ] X)) (Md : X →L[ℝ] X)
    (F : ℝ → X) (Fd : X) (L : ℝ) :
    transportApply C L (Md (F L) + M L Fd) - M L (transportApply C L Fd)
      = (C (Md (F L) + M L Fd) - (Md (C (F L)) + M L (C Fd)))
        + Md (transportApply C L (F L)) := by
  simp only [transportApply, map_add, map_smul]
  module

/-- **The full normal-system version `(3)`.**  Adding a zero-order operator `Z` adds exactly its
commutator with the cutoff. -/
theorem primitive_flux_identity_with_zeroOrder (C Z : X →L[ℝ] X) (M : ℝ → (X →L[ℝ] X))
    (Md : X →L[ℝ] X) (F : ℝ → X) (Fd : X) (L : ℝ) :
    (transportApply C L (Md (F L) + M L Fd) + Z (M L (F L)))
        - M L (transportApply C L Fd + Z (F L))
      = (C (Md (F L) + M L Fd) - (Md (C (F L)) + M L (C Fd)))
        + Md (transportApply C L (F L))
        + (Z (M L (F L)) - M L (Z (F L))) := by
  simp only [transportApply, map_add, map_smul]
  module

/-- The defect is carried by the commutator of the *difference* `C = R − B`, so a term acting only
in orbit coordinates cancels out of the primitive source. -/
theorem fluxCommutatorProfile_sub (R B : X →L[ℝ] X) (M : ℝ → (X →L[ℝ] X)) (F : ℝ → X) (L : ℝ) :
    fluxCommutatorProfile (R - B) M F L
      = fluxCommutatorProfile R M F L - fluxCommutatorProfile B M F L := by
  simp only [fluxCommutatorProfile, sub_apply, map_sub]
  abel

/-- A cutoff that commutes with the remainder has no primitive source at all. -/
theorem fluxCommutatorProfile_eq_zero_of_commute {C : X →L[ℝ] X} {M : ℝ → (X →L[ℝ] X)}
    (hcomm : ∀ (L : ℝ) (x : X), C (M L x) = M L (C x)) (F : ℝ → X) (L : ℝ) :
    fluxCommutatorProfile C M F L = 0 := by
  simp only [fluxCommutatorProfile, hcomm, sub_self]

/-- A scalar cutoff commutes with every operator, so the scalar case of the predecessor card is the
degenerate case of the identity. -/
theorem fluxCommutatorProfile_scalar (C : X →L[ℝ] X) (χ : ℝ → ℝ) (F : ℝ → X) (L : ℝ) :
    fluxCommutatorProfile C (fun L => (χ L) • ContinuousLinearMap.id ℝ X) F L = 0 := by
  refine fluxCommutatorProfile_eq_zero_of_commute (fun L x => ?_) F L
  simp

end GaloisForLFunctions.HTGeometry
