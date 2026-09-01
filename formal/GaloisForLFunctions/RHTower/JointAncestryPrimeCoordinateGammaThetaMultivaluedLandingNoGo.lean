import GaloisForLFunctions.RHTower.JointAncestryPrimeCoordinateGammaThetaNilpotentLandingNoGo

/-!
# JAS multivalued Gamma--theta landing no-go

The actual Gamma--theta creator is square-zero, whereas positive and negative prime-coordinate
source actions are inverse. This module proves that covariance through an arbitrary linear
relation forces every target output into the relation's vertical fibre. Hence the induced map to
the quotient by its multivalued part is zero.

This removes the multivalued-relation escape from the JAS chain

`prime-coordinate source -> Gamma--theta support sewing -> Xi landing -> RH`.

No single-valuedness, closedness, density, boundedness, target inverse law, or target
representation law is used. A surviving JAS correspondence must break inverse source covariance
or replace literal Gamma--theta creation before quotient landing.
-/

open Complex Real MeasureTheory Set
open scoped ENNReal LinearPMap

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

section RelationRigidity

variable {H₁ H₂ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

/-- Inverse source covariance and a square-zero positive target force every relation output into
the vertical fibre. Equivalently, the induced relation on the target quotient is zero. -/
theorem hilbertRelation_output_mem_multivalued_of_inverse_source_squareZero_target
    (R : Submodule ℂ (HilbertSum H₁ H₂))
    (Aplus Aminus : H₁ →L[ℂ] H₁)
    (C D : H₂ →ₗ.[ℂ] H₂)
    (hleft : ∀ u, Aminus (Aplus u) = u)
    (hright : ∀ u, Aplus (Aminus u) = u)
    (hplus : PartialTargetRelationInvariant R Aplus C)
    (hminus : PartialTargetRelationInvariant R Aminus D)
    (hsq : LinearPMapSquareZero C)
    (z : HilbertSum H₁ H₂) (hz : z ∈ R) :
    hilbertSumInr (hilbertSumSnd z) ∈ R := by
  have vertical_of_mem_of_fst_zero : ∀ w : HilbertSum H₁ H₂, w ∈ R →
      hilbertSumFst w = 0 → hilbertSumInr (hilbertSumSnd w) ∈ R := by
    intro w hw hfst
    have hdecomp := hilbertSum_inl_add_inr w
    rw [hfst, map_zero, zero_add] at hdecomp
    rw [hdecomp]
    exact hw
  obtain ⟨hyC, hzC⟩ := hplus z hz
  have hyC' : hilbertSumSnd z ∈ C.domain := hyC
  obtain ⟨hCyD, hzDC⟩ := hminus _ hzC
  have hCyD' : C ⟨hilbertSumSnd z, hyC'⟩ ∈ D.domain := by
    rw [partialTargetRelationAction_snd] at hCyD
    exact hCyD
  have hmDCraw := vertical_of_mem_of_fst_zero
    (partialTargetRelationAction Aminus D
      (partialTargetRelationAction Aplus C z hyC) hCyD - z)
    (R.sub_mem hzDC hz) (by
      rw [map_sub, partialTargetRelationAction_fst,
        partialTargetRelationAction_fst, hleft, sub_self])
  have hmDC : hilbertSumInr
      (D ⟨C ⟨hilbertSumSnd z, hyC'⟩, hCyD'⟩ - hilbertSumSnd z) ∈ R := by
    simpa only [map_sub, partialTargetRelationAction_snd] using hmDCraw
  obtain ⟨hyD, hzD⟩ := hminus z hz
  have hyD' : hilbertSumSnd z ∈ D.domain := hyD
  obtain ⟨hDyC, hzCD⟩ := hplus _ hzD
  have hDyC' : D ⟨hilbertSumSnd z, hyD'⟩ ∈ C.domain := by
    rw [partialTargetRelationAction_snd] at hDyC
    exact hDyC
  have hmCDraw := vertical_of_mem_of_fst_zero
    (partialTargetRelationAction Aplus C
      (partialTargetRelationAction Aminus D z hyD) hDyC - z)
    (R.sub_mem hzCD hz) (by
      rw [map_sub, partialTargetRelationAction_fst,
        partialTargetRelationAction_fst, hright, sub_self])
  have hmCD : hilbertSumInr
      (C ⟨D ⟨hilbertSumSnd z, hyD'⟩, hDyC'⟩ - hilbertSumSnd z) ∈ R := by
    simpa only [map_sub, partialTargetRelationAction_snd] using hmCDraw
  obtain ⟨hCDyC, hCCDy⟩ := hsq (D ⟨hilbertSumSnd z, hyD'⟩) hDyC'
  have hmCDdom :
      C ⟨D ⟨hilbertSumSnd z, hyD'⟩, hDyC'⟩ - hilbertSumSnd z ∈ C.domain :=
    C.domain.sub_mem hCDyC hyC'
  obtain ⟨hCmCD, hmCDplus⟩ := hplus _ hmCD
  have hCmCDvertical : hilbertSumInr
      (C ⟨C ⟨D ⟨hilbertSumSnd z, hyD'⟩, hDyC'⟩ - hilbertSumSnd z,
        hmCDdom⟩) ∈ R := by
    have hv := vertical_of_mem_of_fst_zero _ hmCDplus (by
      rw [partialTargetRelationAction_fst, hilbertSumFst_inr, map_zero])
    simpa only [partialTargetRelationAction_snd, hilbertSumSnd_inr] using hv
  have hCarg :
      (⟨C ⟨D ⟨hilbertSumSnd z, hyD'⟩, hDyC'⟩ - hilbertSumSnd z,
        hmCDdom⟩ : C.domain) =
      ⟨C ⟨D ⟨hilbertSumSnd z, hyD'⟩, hDyC'⟩, hCDyC⟩ -
        ⟨hilbertSumSnd z, hyC'⟩ := by
    rfl
  have hCyneg : hilbertSumInr (-C ⟨hilbertSumSnd z, hyC'⟩) ∈ R := by
    rw [hCarg] at hCmCDvertical
    have hCmap :
        C (⟨C ⟨D ⟨hilbertSumSnd z, hyD'⟩, hDyC'⟩, hCDyC⟩ -
            ⟨hilbertSumSnd z, hyC'⟩) =
          C ⟨C ⟨D ⟨hilbertSumSnd z, hyD'⟩, hDyC'⟩, hCDyC⟩ -
            C ⟨hilbertSumSnd z, hyC'⟩ :=
      C.toFun.map_sub _ _
    rw [hCmap, hCCDy, zero_sub] at hCmCDvertical
    exact hCmCDvertical
  have hCyMult : hilbertSumInr (C ⟨hilbertSumSnd z, hyC'⟩) ∈ R := by
    have hneg := R.neg_mem hCyneg
    simpa using hneg
  obtain ⟨hDCy, hDCyMultRaw⟩ := hminus _ hCyMult
  have hDCyMult : hilbertSumInr
      (D ⟨C ⟨hilbertSumSnd z, hyC'⟩, hCyD'⟩) ∈ R := by
    have hv := vertical_of_mem_of_fst_zero _ hDCyMultRaw (by
      rw [partialTargetRelationAction_fst, hilbertSumFst_inr, map_zero])
    simpa only [partialTargetRelationAction_snd, hilbertSumSnd_inr] using hv
  have hfinal := R.sub_mem hDCyMult hmDC
  simpa [map_sub] using hfinal

end RelationRigidity

/-- Multivalued JAS landing with a target class surviving quotient by the vertical fibre. -/
def JASPrimeCoordinateGammaThetaMultivaluedLanding : Prop :=
  ∃ (sigma t : ℝ) (hsigma : 0 < sigma) (x : ℝ) (p : Nat.Primes)
      (R : Submodule ℂ
        (HilbertSum (PrimePoissonL2 sigma t hsigma) JASGammaThetaL2))
      (D : JASGammaThetaL2 →ₗ.[ℂ] JASGammaThetaL2),
    PartialTargetRelationInvariant R
      (jasPrimeCoordinateMul sigma t hsigma p 1)
      (jasGammaThetaCreation x p) ∧
    PartialTargetRelationInvariant R
      (jasPrimeCoordinateMul sigma t hsigma p (-1)) D ∧
    ∃ z ∈ R, hilbertSumInr (hilbertSumSnd z) ∉ R

/-- Route-class kill: a multivalued prime-coordinate/Gamma--theta relation has zero quotient
output, regardless of its vertical indeterminacy. -/
theorem not_JASPrimeCoordinateGammaThetaMultivaluedLanding :
    ¬ JASPrimeCoordinateGammaThetaMultivaluedLanding := by
  rintro ⟨sigma, t, hsigma, x, p, R, D,
    hplus, hminus, z, hz, hout⟩
  apply hout
  apply hilbertRelation_output_mem_multivalued_of_inverse_source_squareZero_target R
    (jasPrimeCoordinateMul sigma t hsigma p 1)
    (jasPrimeCoordinateMul sigma t hsigma p (-1))
    (jasGammaThetaCreation x p) D
  · exact jasPrimeCoordinateMul_neg_pos sigma t hsigma p
  · exact jasPrimeCoordinateMul_pos_neg sigma t hsigma p
  · exact hplus
  · exact hminus
  · intro y hy
    let f : (jasGammaThetaCreation x p).domain := ⟨y, hy⟩
    refine ⟨jasGammaThetaCreation_apply_mem_domain x p f, ?_⟩
    simpa [f, jasGammaThetaCreationSecondDomain] using
      jasGammaThetaCreation_sq_apply x p f
  · exact hz

end

end RHTower
