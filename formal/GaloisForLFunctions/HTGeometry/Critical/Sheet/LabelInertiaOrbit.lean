import GaloisForLFunctions.HTGeometry.Critical.Sheet.OrbitRamification
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower
import GaloisForLFunctions.HTGeometry.ValuationInertiaSheetInertiaOrbit
import GaloisForLFunctions.HTGeometry.Critical.Sheet.SchurPlacePullback
import GaloisForLFunctions.HTGeometry.Critical.Sheet.CoordRingResidue

/-!
# The canonical label fibre of the critical horizon is one inertia orbit

Two sheets with the canonical reduced Schur label cut out the same place and have the same residue
map, so the general lift theorem produces an element of the Schur inertia group carrying one to the
other.  The label fibre therefore lies in a single inertia orbit — a count of at most `|I|`, with no
residue-degree computation anywhere.

```text
criticalSheet_residue_eq_of_canonical_label
    ** equal canonical labels ⟹ equal residues at every element of the source Schur place **
criticalSchur_exists_inertiaSubgroup_comp_eq
criticalSchur_exists_inertia_comp_eq
    ** the label fibre is inside one inertia orbit **
```

The residue statement is upgraded from the Schur coordinates to the whole place by writing an
element of the source Schur valuation ring as a ratio of coordinate polynomials with denominator off
the Schur prime: the labels fix the residues of numerator and denominator, and the denominator's
residue is a unit.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsLocalRing

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 3000000
set_option maxHeartbeats 8000000
set_option maxSynthPendingDepth 3

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}



/-- Every element of the source Schur place is a ratio of coordinate polynomials whose denominator
lies off the Schur prime. -/
private theorem exists_criticalSchurSource_ratio (hm : 1 < m) (hn : 1 < n)
    {x : criticalSourceField K m n}
    (hx : x ∈ criticalSchurSourceValuationSubring K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn)) :
    ∃ a b : criticalSchurSourceRing K m n, b ∉ criticalSchurRamificationIdeal K m n ∧
      x * MvPolynomial.aeval (criticalSourceSchurCoordinates K (Nat.zero_lt_of_lt hm)
          (Nat.zero_lt_of_lt hn)) b
        = MvPolynomial.aeval (criticalSourceSchurCoordinates K (Nat.zero_lt_of_lt hm)
          (Nat.zero_lt_of_lt hn)) a := by
  obtain ⟨y, hab⟩ := IsLocalization.surj
    (M := (criticalSchurPrimeDivisor K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn)).1.primeCompl)
    (⟨x, hx⟩ : criticalSchurSourceValuationSubring K
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
  refine ⟨y.1, (y.2 : criticalSchurSourceRing K m n), y.2.2, ?_⟩
  have h : x * ((algebraMap (criticalSchurSourceRing K m n)
        (criticalSchurSourceValuationSubring K (Nat.zero_lt_of_lt hm)
          (Nat.zero_lt_of_lt hn)) (y.2 : criticalSchurSourceRing K m n) :
        criticalSchurSourceValuationSubring K (Nat.zero_lt_of_lt hm)
          (Nat.zero_lt_of_lt hn)) : criticalSourceField K m n)
      = ((algebraMap (criticalSchurSourceRing K m n)
        (criticalSchurSourceValuationSubring K (Nat.zero_lt_of_lt hm)
          (Nat.zero_lt_of_lt hn)) y.1 :
        criticalSchurSourceValuationSubring K (Nat.zero_lt_of_lt hm)
          (Nat.zero_lt_of_lt hn)) : criticalSourceField K m n) :=
    congrArg Subtype.val hab
  rw [coe_algebraMap_criticalSchurSourceValuationSubring K (Nat.zero_lt_of_lt hm)
    (Nat.zero_lt_of_lt hn) (y.2 : criticalSchurSourceRing K m n),
    coe_algebraMap_criticalSchurSourceValuationSubring K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn) y.1] at h
  exact h

/-- Along a sheet, the residue of a ratio times the residue of its denominator is the residue of
its numerator. -/
private theorem criticalSheet_residue_mul_coordResidue (hm : 1 < m) (hn : 1 < n)
    {x : criticalSourceField K m n} {a b : criticalSchurSourceRing K m n}
    (hcoe : x * MvPolynomial.aeval (criticalSourceSchurCoordinates K (Nat.zero_lt_of_lt hm)
          (Nat.zero_lt_of_lt hn)) b
      = MvPolynomial.aeval (criticalSourceSchurCoordinates K (Nat.zero_lt_of_lt hm)
          (Nat.zero_lt_of_lt hn)) a)
    (ρ : criticalGeometricSheet K m n)
    (hρx : ρ x ∈ criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn)) :
    residue (criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
        (Nat.zero_lt_of_lt hn)) ⟨ρ x, hρx⟩
      * criticalSheetCoordResidue K hm hn ρ b
    = criticalSheetCoordResidue K hm hn ρ a :=
  have hmul : (⟨ρ x, hρx⟩ : criticalNormalClosureSchurValuationSubring K
        (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
      * criticalSheetToUpper K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) ρ
        (criticalSheetAevalHom K hm hn ρ b)
      = criticalSheetToUpper K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) ρ
        (criticalSheetAevalHom K hm hn ρ a) :=
    Subtype.ext ((map_mul ρ x (MvPolynomial.aeval (criticalSourceSchurCoordinates K
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)) b)).symm.trans (congrArg ρ hcoe))
  (map_mul (residue (criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
    (Nat.zero_lt_of_lt hn))) _ _).symm.trans
      (congrArg (residue (criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
        (Nat.zero_lt_of_lt hn))) hmul)

/-- **Sheets with the canonical reduced label have the same residue at every element of the source
Schur place.**  Every such element is a ratio of coordinate polynomials with denominator off the
Schur prime; the labels fix the residues of both, and the denominator's residue is nonzero. -/
theorem criticalSheet_residue_eq_of_canonical_label (hm : 1 < m) (hn : 1 < n)
    {σ τ : criticalGeometricSheet K m n}
    (hσ : criticalGeometricSheetToSchurReducedFibre K hm hn σ
      = criticalGeometricSheetToSchurReducedFibre K hm hn
        (criticalSourceNormalClosureEmbedding K m n))
    (hτ : criticalGeometricSheetToSchurReducedFibre K hm hn τ
      = criticalGeometricSheetToSchurReducedFibre K hm hn
        (criticalSourceNormalClosureEmbedding K m n))
    (x : criticalSourceField K m n)
    (hσx : σ x ∈ criticalNormalClosureSchurValuationSubring K
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
    (hτx : τ x ∈ criticalNormalClosureSchurValuationSubring K
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)) :
    residue (criticalNormalClosureSchurValuationSubring K
        (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)) ⟨σ x, hσx⟩
      = residue (criticalNormalClosureSchurValuationSubring K
        (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)) ⟨τ x, hτx⟩ := by
  have hx : x ∈ criticalSchurSourceValuationSubring K
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) :=
    criticalSheetPullbackValuation_eq K hm hn hσ ▸ hσx
  obtain ⟨a, b, hbP, hcoe⟩ := exists_criticalSchurSource_ratio K hm hn hx
  have hbne : criticalSheetCoordResidue K hm hn σ b ≠ 0 :=
    (isUnit_iff_residue_ne_zero K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) _).mp
      (isUnit_criticalSheetAeval K hm hn hσ hbP)
  have hστ : criticalSheetCoordResidue K hm hn σ = criticalSheetCoordResidue K hm hn τ :=
    (criticalSheetCoordResidue_congr K hm hn hσ).trans
      (criticalSheetCoordResidue_congr K hm hn hτ).symm
  exact mul_right_cancel₀ hbne
    ((criticalSheet_residue_mul_coordResidue K hm hn hcoe σ hσx).trans
      (((hστ ▸ criticalSheet_residue_mul_coordResidue K hm hn hcoe τ hτx)).symm))


/-- **A sheet with the canonical label is an inertia translate of the canonical sheet**, in
valuation-subgroup form. -/
theorem criticalSchur_exists_inertiaSubgroup_comp_eq (hm : 1 < m) (hn : 1 < n)
    {σ τ : criticalGeometricSheet K m n}
    (hσ : criticalGeometricSheetToSchurReducedFibre K hm hn σ
      = criticalGeometricSheetToSchurReducedFibre K hm hn
        (criticalSourceNormalClosureEmbedding K m n))
    (hτ : criticalGeometricSheetToSchurReducedFibre K hm hn τ
      = criticalGeometricSheetToSchurReducedFibre K hm hn
        (criticalSourceNormalClosureEmbedding K m n)) :
    ∃ i : (criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
        (Nat.zero_lt_of_lt hn)).decompositionSubgroup (criticalObservationField K m n),
      i ∈ (criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
        (Nat.zero_lt_of_lt hn)).inertiaSubgroup (criticalObservationField K m n) ∧
      ∀ x : criticalSourceField K m n,
        τ x = ((i : criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
          criticalNormalClosure K m n)) (σ x) := by
  haveI := criticalNormalClosure_finiteDimensional K (Nat.zero_lt_of_lt hm)
    (Nat.zero_lt_of_lt hn)
  haveI := criticalNormalClosure_isGalois K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)
  haveI := criticalSourceField_finiteDimensional_criticalObservationField K
    (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)
  have hplace : (criticalNormalClosureSchurValuationSubring K
        (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)).comap
        σ.toRingHom
      = (criticalNormalClosureSchurValuationSubring K
        (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)).comap
        τ.toRingHom :=
    (criticalSheetPullbackValuation_eq K hm hn hσ).trans
      (criticalSheetPullbackValuation_eq K hm hn hτ).symm
  have hres0 := criticalSheet_residue_eq_of_canonical_label K hm hn hσ hτ
  exact ValuationInertia.exists_mem_inertiaSubgroup_comp_eq
    (A := CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
    σ τ
    (criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
    (criticalSchurNormalBase_algebraMap_mem K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
    (ValuationSubring.ne_top_of_isDiscreteValuationRing _)
    (IsLocalRing.maximalIdeal
      (CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)))
    (IsDiscreteValuationRing.not_a_field _)
    (criticalSchurNormalBase_centre K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
    hplace hres0

end

end GaloisForLFunctions.HTGeometry
