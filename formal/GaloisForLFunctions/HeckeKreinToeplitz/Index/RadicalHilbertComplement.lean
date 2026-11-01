import GaloisForLFunctions.HeckeKreinToeplitz.Index.SignedOrthogonalComplements
import GaloisForLFunctions.HeckeKreinToeplitz.Index.ClosedFiniteNegativeSignature

/-!
# Hilbert complements of finite radicals

Positive Hilbert projection splits the radical from a closed subspace.
Removing that radical preserves its indefinite form and gives a closed
nondegenerate representative of the quotient.
-/

noncomputable section
set_option autoImplicit false
open Complex
open scoped InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Coordinates between the Hilbert product norm and the ordinary product norm. -/
abbrev hilbertProductCoordinates : WithLp 2 (H × E) ≃L[ℂ] H × E :=
  WithLp.prodContinuousLinearEquiv 2 ℂ H E

/-- A subspace in positive Hilbert product coordinates. -/
def hilbertLift (U : Submodule ℂ (H × E)) : Submodule ℂ (WithLp 2 (H × E)) :=
  U.comap hilbertProductCoordinates.toLinearMap

/-- Orthogonality for the positive Hilbert product, rather than the signed form. -/
def positiveOrthogonal (U : Submodule ℂ (H × E)) : Submodule ℂ (H × E) :=
  (hilbertLift U)ᗮ.comap hilbertProductCoordinates.symm.toLinearMap

theorem isClosed_hilbertLift (U : Submodule ℂ (H × E))
    (hU : IsClosed (U : Set (H × E))) :
    IsClosed (hilbertLift U : Set (WithLp 2 (H × E))) :=
  hU.preimage hilbertProductCoordinates.continuous

/-- Positive Hilbert projection, transported to ordinary product coordinates. -/
def positiveProjection (U : Submodule ℂ (H × E))
    (hU : IsClosed (U : Set (H × E))) [CompleteSpace H] [CompleteSpace E] :
    (H × E) →L[ℂ] (H × E) := by
  letI : CompleteSpace (hilbertLift U) := (isClosed_hilbertLift U hU).completeSpace_coe
  exact hilbertProductCoordinates.toContinuousLinearMap.comp
    ((hilbertLift U).starProjection.comp hilbertProductCoordinates.symm.toContinuousLinearMap)

variable [CompleteSpace H] [CompleteSpace E]

theorem positiveProjection_mem (U : Submodule ℂ (H × E))
    (hU : IsClosed (U : Set (H × E))) (v : H × E) : positiveProjection U hU v ∈ U := by
  letI : CompleteSpace (hilbertLift U) := (isClosed_hilbertLift U hU).completeSpace_coe
  exact (hilbertLift U).starProjection_apply_mem (hilbertProductCoordinates.symm v)

theorem sub_positiveProjection_mem (U : Submodule ℂ (H × E))
    (hU : IsClosed (U : Set (H × E))) (v : H × E) :
    v - positiveProjection U hU v ∈ positiveOrthogonal U := by
  letI : CompleteSpace (hilbertLift U) := (isClosed_hilbertLift U hU).completeSpace_coe
  change hilbertProductCoordinates.symm
    (v - hilbertProductCoordinates ((hilbertLift U).starProjection
      (hilbertProductCoordinates.symm v))) ∈ (hilbertLift U)ᗮ
  rw [map_sub, ContinuousLinearEquiv.symm_apply_apply]
  exact (hilbertLift U).sub_starProjection_mem_orthogonal _

theorem positiveProjection_eq_self (U : Submodule ℂ (H × E))
    (hU : IsClosed (U : Set (H × E))) {v : H × E} (hv : v ∈ U) :
    positiveProjection U hU v = v := by
  letI : CompleteSpace (hilbertLift U) := (isClosed_hilbertLift U hU).completeSpace_coe
  have hm : hilbertProductCoordinates.symm v ∈ hilbertLift U := by
    change hilbertProductCoordinates (hilbertProductCoordinates.symm v) ∈ U
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hv
  change hilbertProductCoordinates ((hilbertLift U).starProjection
    (hilbertProductCoordinates.symm v)) = v
  rw [(Submodule.starProjection_eq_self_iff).mpr hm,
    ContinuousLinearEquiv.apply_symm_apply]

/-- A positive vector orthogonal to its own subspace is zero. -/
theorem eq_zero_of_mem_positiveOrthogonal (U : Submodule ℂ (H × E))
    {v : H × E} (hv : v ∈ U) (ho : v ∈ positiveOrthogonal U) : v = 0 := by
  have hm : hilbertProductCoordinates.symm v ∈ hilbertLift U := by
    change hilbertProductCoordinates (hilbertProductCoordinates.symm v) ∈ U
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hv
  have h := (Submodule.mem_orthogonal (hilbertLift U) _).mp ho _ hm
  have hz := inner_self_eq_zero.mp h
  exact hilbertProductCoordinates.symm.injective (hz.trans (map_zero _).symm)

theorem isClosed_positiveOrthogonal (U : Submodule ℂ (H × E)) :
    IsClosed (positiveOrthogonal U : Set (H × E)) :=
  (hilbertLift U).isClosed_orthogonal.preimage hilbertProductCoordinates.symm.continuous

theorem positiveProjection_eq_zero (U : Submodule ℂ (H × E))
    (hU : IsClosed (U : Set (H × E))) {v : H × E} (hv : v ∈ positiveOrthogonal U) :
    positiveProjection U hU v = 0 := by
  letI : CompleteSpace (hilbertLift U) := (isClosed_hilbertLift U hU).completeSpace_coe
  have hz : (hilbertLift U).orthogonalProjectionOnto (hilbertProductCoordinates.symm v) = 0 :=
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr hv
  have hp : (hilbertLift U).starProjection (hilbertProductCoordinates.symm v) = 0 :=
    congrArg Subtype.val hz
  change hilbertProductCoordinates ((hilbertLift U).starProjection
    (hilbertProductCoordinates.symm v)) = 0
  rw [hp, map_zero]

/-- The closed representative of a subspace modulo its radical. -/
def radicalComplement (W : Submodule ℂ (H × E)) : Submodule ℂ (H × E) :=
  W ⊓ positiveOrthogonal (restrictedRadical W)

theorem isClosed_radicalComplement (W : Submodule ℂ (H × E))
    (hW : IsClosed (W : Set (H × E))) :
    IsClosed (radicalComplement W : Set (H × E)) :=
  hW.inter (isClosed_positiveOrthogonal _)

variable [FiniteDimensional ℂ E]

/-- Remove the radical component by positive Hilbert projection. -/
def radicalRetraction (W : Submodule ℂ (H × E)) : (H × E) →L[ℂ] (H × E) :=
  ContinuousLinearMap.id ℂ (H × E) -
    positiveProjection (restrictedRadical W) (restrictedRadical W).closed_of_finiteDimensional

theorem radicalRetraction_mem (W : Submodule ℂ (H × E)) {v : H × E} (hv : v ∈ W) :
    radicalRetraction W v ∈ radicalComplement W := by
  refine ⟨W.sub_mem hv ?_, sub_positiveProjection_mem _ _ v⟩
  exact ((mem_restrictedRadical W _).mp (positiveProjection_mem _ _ v)).1

theorem sub_radicalRetraction_mem (W : Submodule ℂ (H × E)) (v : H × E) :
    v - radicalRetraction W v ∈ restrictedRadical W := by
  change v - (v - positiveProjection _ _ v) ∈ _
  rw [sub_sub_cancel]
  exact positiveProjection_mem _ _ v

theorem radicalRetraction_eq_self (W : Submodule ℂ (H × E))
    {v : H × E} (hv : v ∈ radicalComplement W) : radicalRetraction W v = v := by
  change v - positiveProjection _ _ v = v
  rw [positiveProjection_eq_zero _ _ hv.2, sub_zero]

theorem radicalRetraction_eq_zero (W : Submodule ℂ (H × E))
    {v : H × E} (hv : v ∈ restrictedRadical W) : radicalRetraction W v = 0 := by
  change v - positiveProjection _ _ v = 0
  rw [positiveProjection_eq_self _ _ hv, sub_self]

/-- Removing radical components leaves all pairings inside the subspace unchanged. -/
theorem pairing_radicalRetraction (W : Submodule ℂ (H × E))
    {u v : H × E} (hu : u ∈ W) (hv : v ∈ W) :
    pairing (radicalRetraction W u) (radicalRetraction W v) = pairing u v := by
  have hru := sub_radicalRetraction_mem W u
  have hrv := sub_radicalRetraction_mem W v
  have hqu := (radicalRetraction_mem W hu).1
  have hqv := (radicalRetraction_mem W hv).1
  have hright : pairing u (v - radicalRetraction W v) = 0 :=
    ((mem_restrictedRadical W _).mp hrv).2 u hu
  have hleft : pairing (u - radicalRetraction W u) (radicalRetraction W v) = 0 := by
    rw [← pairing_conj_symm,
      ((mem_restrictedRadical W _).mp hru).2 _ hqv, map_zero]
  have h1 := pairing_add_right u (v - radicalRetraction W v) (radicalRetraction W v)
  have h2 := pairing_add_left (u - radicalRetraction W u) (radicalRetraction W u)
    (radicalRetraction W v)
  rw [sub_add_cancel, hright, zero_add] at h1
  rw [sub_add_cancel, hleft, zero_add] at h2
  exact h2.symm.trans h1.symm

/-- The radical complement has nondegenerate restricted form. -/
theorem restrictedRadical_radicalComplement (W : Submodule ℂ (H × E)) :
    restrictedRadical (radicalComplement W) = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  obtain ⟨hvS, ho⟩ := (mem_restrictedRadical _ v).mp hv
  have hvR : v ∈ restrictedRadical W := by
    apply (mem_restrictedRadical W v).mpr
    refine ⟨hvS.1, ?_⟩
    intro w hw
    have h := pairing_radicalRetraction W hw hvS.1
    rw [radicalRetraction_eq_self W hvS] at h
    rw [← h]
    exact ho _ (radicalRetraction_mem W hw)
  exact (Submodule.mem_bot ℂ).mpr
    (eq_zero_of_mem_positiveOrthogonal (restrictedRadical W) hvR hvS.2)

#print axioms positiveProjection_mem
#print axioms sub_positiveProjection_mem
#print axioms pairing_radicalRetraction
#print axioms restrictedRadical_radicalComplement

end GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative
