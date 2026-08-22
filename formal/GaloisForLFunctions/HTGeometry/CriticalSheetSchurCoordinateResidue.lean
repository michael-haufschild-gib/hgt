import GaloisForLFunctions.HTGeometry.CriticalSheetResidueCongruence
import GaloisForLFunctions.HTGeometry.RingSchurCoordinates

/-!
# The Schur coordinates of a sheet are determined, after reduction, by its label

The Schur coordinates are built from the raw coordinates by dividing by the scale and then applying
a division-free polynomial construction (a truncated reciprocal followed by a square).  The scale is
a unit at the upper Schur place for every sheet, and the construction is natural in every ring
homomorphism, so the residues of the Schur coordinates are determined by the residues of the raw
coordinates — which the reduced label already fixes.

```text
criticalSourceNormalizedPositive_mul_scale     np * scale = raw
criticalSheetNormalizedPositive_residue_congr  equal labels ⟹ equal residues on the normalised jets
criticalSheetSchurCoordinate_succ_lift         a positive Schur coordinate inside the pullback ring
criticalSheetSchurCoordinates_residue_congr
      ** equal labels ⟹ equal residues on every Schur coordinate **
```
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsLocalRing

set_option synthInstance.maxHeartbeats 3000000
set_option maxHeartbeats 8000000
set_option maxSynthPendingDepth 3

variable (K : Type*) [Field K] [CharZero K] {m n : ℕ}

omit [CharZero K] in
/-- The normalised positive coordinate times the scale is the corresponding raw coordinate. -/
theorem criticalSourceNormalizedPositive_mul_scale (hm : 0 < m) (hn : 0 < n)
    (j : Fin (m + n - 1)) :
    criticalSourceNormalizedPositive K hm hn j * criticalSourceScale K hm hn
      = criticalSourceRaw K m n (Fin.cast (by omega) j.succ) := by
  show normalizedFiniteJet (criticalSourceRawReindexed K hm hn) j.succ * _ = _
  rw [normalizedFiniteJet, if_neg (by simp)]
  exact div_mul_cancel₀ _ (criticalSourceScale_ne_zero K hm hn)

/-- Sheets with the same reduced Schur label have the same residue on every normalised positive
coordinate. -/
theorem criticalSheetNormalizedPositive_residue_congr (hm : 1 < m) (hn : 1 < n)
    {σ τ : criticalGeometricSheet K m n}
    (h : criticalGeometricSheetToSchurReducedFibre K hm hn σ
      = criticalGeometricSheetToSchurReducedFibre K hm hn τ) (j : Fin (m + n - 1)) :
    criticalSheetResidue K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) σ
        ⟨criticalSourceNormalizedPositive K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) j,
          criticalSourceNormalizedPositive_mem_pullback K hm hn σ j⟩
      = criticalSheetResidue K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) τ
        ⟨criticalSourceNormalizedPositive K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) j,
          criticalSourceNormalizedPositive_mem_pullback K hm hn τ j⟩ := by
  have key : ∀ ρ : criticalGeometricSheet K m n,
      criticalSheetResidue K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) ρ
          ⟨criticalSourceNormalizedPositive K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) j,
            criticalSourceNormalizedPositive_mem_pullback K hm hn ρ j⟩
        * residue (criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
            (Nat.zero_lt_of_lt hn))
          ⟨ρ (criticalSourceScale K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)),
            criticalSheetScale_mem K hm hn ρ⟩
        = residue (criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
            (Nat.zero_lt_of_lt hn))
          ⟨ρ (criticalSourceRaw K m n (Fin.cast (by omega) j.succ)),
            criticalSheetRaw_mem K hm hn ρ _⟩ := by
    intro ρ
    have hmul : (⟨criticalSourceNormalizedPositive K (Nat.zero_lt_of_lt hm)
            (Nat.zero_lt_of_lt hn) j,
          criticalSourceNormalizedPositive_mem_pullback K hm hn ρ j⟩ :
            criticalSheetPullbackSubring K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) ρ)
          * ⟨criticalSourceScale K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn),
            criticalSheetScale_mem K hm hn ρ⟩
        = ⟨criticalSourceRaw K m n (Fin.cast (by omega) j.succ),
            criticalSheetRaw_mem K hm hn ρ _⟩ :=
      Subtype.ext (criticalSourceNormalizedPositive_mul_scale K (Nat.zero_lt_of_lt hm)
        (Nat.zero_lt_of_lt hn) j)
    exact (map_mul (criticalSheetResidue K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn) ρ) _ _).symm.trans
      (congrArg (criticalSheetResidue K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) ρ) hmul)
  have hunit : residue (criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
        (Nat.zero_lt_of_lt hn))
      ⟨σ (criticalSourceScale K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)),
        criticalSheetScale_mem K hm hn σ⟩ ≠ 0 :=
    ((isUnit_criticalSheetScale K hm hn σ).map
      (residue (criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
        (Nat.zero_lt_of_lt hn)))).ne_zero
  refine mul_right_cancel₀ hunit ?_
  refine (key σ).trans ?_
  refine (criticalSheetRaw_residue_congr K hm hn h _).trans ?_
  refine (key τ).symm.trans ?_
  exact congrArg _ (criticalSheetScale_residue_congr K hm hn h).symm

/-- A positive Schur coordinate of a sheet, computed inside the pullback subring. -/
theorem criticalSheetSchurCoordinate_succ_lift (hm : 1 < m) (hn : 1 < n)
    (ρ : criticalGeometricSheet K m n) (j : Fin (m + n - 1)) :
    (⟨criticalSourceSchurCoordinates K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) j.succ,
        criticalSourceSchurCoordinates_mem_pullback K hm hn ρ j.succ⟩ :
      criticalSheetPullbackSubring K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) ρ)
      = ringReciprocalSquarePositive
          (fun k : Fin (m + n - 1) =>
            (⟨criticalSourceNormalizedPositive K (Nat.zero_lt_of_lt hm)
                (Nat.zero_lt_of_lt hn) k,
              criticalSourceNormalizedPositive_mem_pullback K hm hn ρ k⟩ :
                criticalSheetPullbackSubring K (Nat.zero_lt_of_lt hm)
                  (Nat.zero_lt_of_lt hn) ρ))
          j.rev := by
  refine Subtype.ext ?_
  have hcoord : criticalSourceSchurCoordinates K (Nat.zero_lt_of_lt hm)
        (Nat.zero_lt_of_lt hn) j.succ
      = finiteReciprocalSquarePositive
          (criticalSourceNormalizedPositive K (Nat.zero_lt_of_lt hm)
            (Nat.zero_lt_of_lt hn)) j.rev := rfl
  have hmapv := ringReciprocalSquarePositive_map
      (criticalSheetPullbackSubring K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) ρ).subtype
      (fun k : Fin (m + n - 1) =>
        (⟨criticalSourceNormalizedPositive K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) k,
          criticalSourceNormalizedPositive_mem_pullback K hm hn ρ k⟩ :
            criticalSheetPullbackSubring K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) ρ))
      j.rev
  exact hcoord.trans ((congrFun (ringReciprocalSquarePositive_eq
    (criticalSourceNormalizedPositive K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn))).symm j.rev).trans hmapv.symm)

/-- **Sheets with the same reduced Schur label have the same residue on every Schur
coordinate.** -/
theorem criticalSheetSchurCoordinates_residue_congr (hm : 1 < m) (hn : 1 < n)
    {σ τ : criticalGeometricSheet K m n}
    (h : criticalGeometricSheetToSchurReducedFibre K hm hn σ
      = criticalGeometricSheetToSchurReducedFibre K hm hn τ) (i : Fin (m + n - 1 + 1)) :
    criticalSheetResidue K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) σ
        ⟨criticalSourceSchurCoordinates K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) i,
          criticalSourceSchurCoordinates_mem_pullback K hm hn σ i⟩
      = criticalSheetResidue K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) τ
        ⟨criticalSourceSchurCoordinates K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) i,
          criticalSourceSchurCoordinates_mem_pullback K hm hn τ i⟩ := by
  refine Fin.cases ?_ (fun j => ?_) i
  · have hz : ∀ ρ : criticalGeometricSheet K m n,
        (⟨criticalSourceSchurCoordinates K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) 0,
          criticalSourceSchurCoordinates_mem_pullback K hm hn ρ 0⟩ :
            criticalSheetPullbackSubring K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) ρ)
          = ⟨criticalSourceScale K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn),
            criticalSheetScale_mem K hm hn ρ⟩ := fun ρ =>
      Subtype.ext (criticalSourceScale_eq_schurCoordinate_zero K
        (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)).symm
    refine (congrArg (criticalSheetResidue K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn) σ) (hz σ)).trans ?_
    refine (criticalSheetScale_residue_congr K hm hn h).trans ?_
    exact (congrArg (criticalSheetResidue K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn) τ) (hz τ)).symm
  · refine (congrArg (criticalSheetResidue K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) σ)
      (criticalSheetSchurCoordinate_succ_lift K hm hn σ j)).trans ?_
    refine Eq.trans ?_ (congrArg (criticalSheetResidue K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn) τ) (criticalSheetSchurCoordinate_succ_lift K hm hn τ j)).symm
    refine (ringReciprocalSquarePositive_map (criticalSheetResidue K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn) σ) _ j.rev).trans ?_
    refine Eq.trans ?_ (ringReciprocalSquarePositive_map (criticalSheetResidue K
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) τ) _ j.rev).symm
    exact congrArg (fun u => ringReciprocalSquarePositive u j.rev)
      (funext fun k => criticalSheetNormalizedPositive_residue_congr K hm hn h k)

end

end GaloisForLFunctions.HTGeometry
