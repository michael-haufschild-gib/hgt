import GaloisForLFunctions.HTGeometry.CriticalSheetSchurCoordinateIntegrality
import GaloisForLFunctions.HTGeometry.CriticalSchurReducedSheetInvariance

/-!
# Sheets with the same reduced Schur label have the same residues

The reduced Schur label of a sheet is by definition the residue of its fibre point at the upper
Schur place.  Two sheets carrying the same label therefore agree, after reduction, on every
coefficient of the fibre point — hence on every *raw source coordinate*, since a raw coordinate
below the depth is such a coefficient and a raw coordinate above the depth is an observation
coordinate, which every sheet fixes outright.

```text
coe_criticalSheetJetCoeff        the j-th jet coefficient is the sheet's value on the j-th raw coordinate
criticalSheetToUpper             a sheet as a ring map into the upper Schur valuation ring
criticalSheetResidue             ** the residue of a sheet at the upper Schur place **
criticalSheetRaw_residue_congr   ** equal labels ⟹ equal residues on every raw coordinate **
criticalSheetScale_residue_congr the same for the normalising scale
```

The residue map is packaged as a ring homomorphism out of the pullback subring so that it can be
transported through the (division-free) Schur coordinate construction.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsLocalRing

set_option synthInstance.maxHeartbeats 3000000
set_option maxHeartbeats 8000000
set_option maxSynthPendingDepth 3

variable (K : Type*) [Field K] [CharZero K] {m n : ℕ}

/-- The `j`-th coefficient of a sheet's jet is the sheet's value on the `j`-th raw coordinate. -/
theorem coe_criticalSheetJetCoeff (hm : 1 < m) (hn : 1 < n)
    (σ : criticalGeometricSheet K m n) {j : ℕ} (hj : j < m) :
    (((criticalGeometricSheetToSchurFibre K hm hn σ).1.1.coeff j :
        criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
          (Nat.zero_lt_of_lt hn)) :
      criticalNormalClosure K m n)
      = σ (criticalSourceRaw K m n ⟨j, by omega⟩) := by
  have hmap := criticalFibreMap_criticalGeometricSheetToSchurFibre K hm hn σ
  have h1 : ((criticalGeometricSheetToSchurFibre K hm hn σ).1.1.map
        (criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
          (Nat.zero_lt_of_lt hn)).subtype).coeff j
      = (criticalGeometricSheetToSchurFieldFibre K (Nat.zero_lt_of_lt hm)
          (Nat.zero_lt_of_lt hn) σ).1.1.coeff j :=
    congrArg (fun p => p.1.1.coeff j) hmap
  rw [Polynomial.coeff_map] at h1
  refine h1.trans ?_
  show ((criticalSourceRawLow K m n).map σ.toRingHom).coeff j = _
  rw [Polynomial.coeff_map, criticalSourceRawLow, lowPolynomial_coeff, dif_pos hj]
  rfl

/-- A sheet, on the subring where it is integral at the upper Schur place, as a ring map into that
valuation ring. -/
def criticalSheetToUpper (hm : 0 < m) (hn : 0 < n) (σ : criticalGeometricSheet K m n) :
    criticalSheetPullbackSubring K hm hn σ →+*
      criticalNormalClosureSchurValuationSubring K hm hn where
  toFun x := ⟨σ (x : criticalSourceField K m n), x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- Residue of a sheet at the upper Schur place, on the subring where the sheet is integral. -/
def criticalSheetResidue (hm : 0 < m) (hn : 0 < n) (σ : criticalGeometricSheet K m n) :
    criticalSheetPullbackSubring K hm hn σ →+*
      ResidueField (criticalNormalClosureSchurValuationSubring K hm hn) :=
  (residue (criticalNormalClosureSchurValuationSubring K hm hn)).comp
    (criticalSheetToUpper K hm hn σ)

theorem criticalSheetResidue_apply (hm : 0 < m) (hn : 0 < n)
    (σ : criticalGeometricSheet K m n) (x : criticalSheetPullbackSubring K hm hn σ) :
    criticalSheetResidue K hm hn σ x
      = residue _ ⟨σ (x : criticalSourceField K m n), x.2⟩ := rfl

/-- **Sheets with the same reduced Schur label have the same residue on every raw coordinate.** -/
theorem criticalSheetRaw_residue_congr (hm : 1 < m) (hn : 1 < n)
    {σ τ : criticalGeometricSheet K m n}
    (h : criticalGeometricSheetToSchurReducedFibre K hm hn σ
      = criticalGeometricSheetToSchurReducedFibre K hm hn τ) (j : Fin (m + n)) :
    residue (criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
        (Nat.zero_lt_of_lt hn))
        ⟨σ (criticalSourceRaw K m n j), criticalSheetRaw_mem K hm hn σ j⟩
      = residue (criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
          (Nat.zero_lt_of_lt hn))
        ⟨τ (criticalSourceRaw K m n j), criticalSheetRaw_mem K hm hn τ j⟩ := by
  by_cases hj : (j : ℕ) < m
  · have hsub : ∀ ρ : criticalGeometricSheet K m n,
        (⟨ρ (criticalSourceRaw K m n j), criticalSheetRaw_mem K hm hn ρ j⟩ :
          criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
            (Nat.zero_lt_of_lt hn))
          = (criticalGeometricSheetToSchurFibre K hm hn ρ).1.1.coeff (j : ℕ) := by
      intro ρ
      refine Subtype.ext ?_
      refine ((coe_criticalSheetJetCoeff K hm hn ρ hj).trans ?_).symm
      exact congrArg (fun k : Fin (m + n) => ρ (criticalSourceRaw K m n k)) (Fin.ext rfl)
    have hp : (criticalGeometricSheetToSchurFibre K hm hn σ).1.1.map
          (residue (criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
            (Nat.zero_lt_of_lt hn)))
        = (criticalGeometricSheetToSchurFibre K hm hn τ).1.1.map
          (residue (criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
            (Nat.zero_lt_of_lt hn))) :=
      congrArg (fun p => p.1.1) h
    have hc := congrArg (fun p => Polynomial.coeff p (j : ℕ)) hp
    rw [Polynomial.coeff_map, Polynomial.coeff_map] at hc
    exact ((congrArg (residue _) (hsub σ)).trans hc).trans (congrArg (residue _) (hsub τ)).symm
  · have hle : m ≤ (j : ℕ) := Nat.le_of_not_gt hj
    have key : σ (criticalSourceRaw K m n j) = τ (criticalSourceRaw K m n j) := by
      rw [criticalSourceRaw_of_le K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) hle,
        σ.commutes, τ.commutes]
    exact congrArg (residue _) (Subtype.ext key)

/-- Sheets with the same reduced Schur label have the same residue on the source scale. -/
theorem criticalSheetScale_residue_congr (hm : 1 < m) (hn : 1 < n)
    {σ τ : criticalGeometricSheet K m n}
    (h : criticalGeometricSheetToSchurReducedFibre K hm hn σ
      = criticalGeometricSheetToSchurReducedFibre K hm hn τ) :
    residue (criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
        (Nat.zero_lt_of_lt hn))
        ⟨σ (criticalSourceScale K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)),
          criticalSheetScale_mem K hm hn σ⟩
      = residue (criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
          (Nat.zero_lt_of_lt hn))
        ⟨τ (criticalSourceScale K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)),
          criticalSheetScale_mem K hm hn τ⟩ :=
  criticalSheetRaw_residue_congr K hm hn h ⟨0, by omega⟩

end

end GaloisForLFunctions.HTGeometry
