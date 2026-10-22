import GaloisForLFunctions.HTGeometry.Critical.Sheet.SchurCoordinateResidue
import GaloisForLFunctions.HTGeometry.Critical.Schur.SourceCotangent
import GaloisForLFunctions.HTGeometry.Critical.Schur.NormalFibreReduction

/-!
# The residue a sheet induces on the whole Schur coordinate ring

The Schur coordinate ring is a polynomial ring over the ground field, so a ring homomorphism out of
it is determined by its values on the ground scalars and on the coordinates.  Two sheets agree on
the ground scalars outright and, when they carry the same reduced label, on the coordinates; so the
residues they induce on the entire coordinate ring coincide.

```text
coe_algebraMap_criticalSchurSourceValuationSubring   the structure map is evaluation at the coordinates
criticalSchur_ground_mem_sourceValuationSubring
criticalSchur_ground_mem_observationValuationSubring
criticalSheetGround_mem_pullback
criticalSheetAeval_mem_pullback      every coordinate polynomial is integral along every sheet
criticalSheetAevalHom                evaluation as a ring map into the pullback subring
criticalSheetCoordResidue            ** the residue a sheet induces on the coordinate ring **
criticalSheetCoordResidue_congr      ** equal labels ⟹ equal residue maps **
```

The ground scalars need the detour through the observation field: a sheet fixes the observation
field, and the ground field sits inside it, so a scalar is integral at the upper place exactly
because it is integral at the observation Schur place.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsLocalRing

set_option synthInstance.maxHeartbeats 3000000
set_option maxSynthPendingDepth 3

variable (K : Type*) [Field K] [CharZero K] {m n : ℕ}

/-- The Schur coordinate ring maps into the source Schur valuation ring by evaluation. -/
theorem coe_algebraMap_criticalSchurSourceValuationSubring (hm : 0 < m) (hn : 0 < n)
    (p : criticalSchurSourceRing K m n) :
    ((algebraMap (criticalSchurSourceRing K m n) (criticalSchurSourceValuationSubring K hm hn) p :
        criticalSchurSourceValuationSubring K hm hn) : criticalSourceField K m n)
      = MvPolynomial.aeval (criticalSourceSchurCoordinates K hm hn) p := by
  refine Eq.trans ?_ (criticalSourceSchurFieldEquiv_algebraMap_apply K hm hn p)
  rw [IsScalarTower.algebraMap_apply (criticalSchurSourceRing K m n)
    (Localization.AtPrime (criticalSchurPrimeDivisor K hm hn).1)
    (FractionRing (criticalSchurSourceRing K m n)) p]
  rfl

/-- Ground scalars are integral at the source Schur place. -/
theorem criticalSchur_ground_mem_sourceValuationSubring (hm : 0 < m) (hn : 0 < n) (k : K) :
    algebraMap K (criticalSourceField K m n) k
      ∈ criticalSchurSourceValuationSubring K hm hn := by
  have h2 : algebraMap K (criticalSourceField K m n) k
      = ((algebraMap (criticalSchurSourceRing K m n)
          (criticalSchurSourceValuationSubring K hm hn) (MvPolynomial.C k) :
            criticalSchurSourceValuationSubring K hm hn) : criticalSourceField K m n) := by
    rw [coe_algebraMap_criticalSchurSourceValuationSubring K hm hn, MvPolynomial.aeval_C]
  rw [h2]
  exact (algebraMap (criticalSchurSourceRing K m n)
    (criticalSchurSourceValuationSubring K hm hn) (MvPolynomial.C k)).2

/-- Ground scalars are integral at the observation Schur place. -/
theorem criticalSchur_ground_mem_observationValuationSubring (hm : 0 < m) (hn : 0 < n) (k : K) :
    algebraMap K (criticalObservationField K m n) k
      ∈ criticalSchurObservationValuationSubring K hm hn := by
  rw [mem_criticalSchurObservationValuationSubring_iff]
  rw [← IsScalarTower.algebraMap_apply K (criticalObservationField K m n)
    (criticalSourceField K m n) k]
  exact criticalSchur_ground_mem_sourceValuationSubring K hm hn k

/-- Every sheet sends a ground scalar into the upper Schur valuation ring. -/
theorem criticalSheetGround_mem_pullback (hm : 0 < m) (hn : 0 < n)
    (σ : criticalGeometricSheet K m n) (k : K) :
    algebraMap K (criticalSourceField K m n) k ∈ criticalSheetPullbackSubring K hm hn σ := by
  rw [mem_criticalSheetPullbackSubring,
    IsScalarTower.algebraMap_apply K (criticalObservationField K m n)
      (criticalSourceField K m n) k, σ.commutes]
  exact criticalNormalClosureSchurValuationSubring_observation_mem K hm hn
    ⟨algebraMap K (criticalObservationField K m n) k,
      criticalSchur_ground_mem_observationValuationSubring K hm hn k⟩

/-- Every polynomial in the Schur coordinates is integral along every sheet. -/
theorem criticalSheetAeval_mem_pullback (hm : 1 < m) (hn : 1 < n)
    (σ : criticalGeometricSheet K m n) (p : criticalSchurSourceRing K m n) :
    MvPolynomial.aeval (criticalSourceSchurCoordinates K (Nat.zero_lt_of_lt hm)
        (Nat.zero_lt_of_lt hn)) p
      ∈ criticalSheetPullbackSubring K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) σ := by
  refine MvPolynomial.induction_on
    (motive := fun q => MvPolynomial.aeval (criticalSourceSchurCoordinates K
        (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)) q
      ∈ criticalSheetPullbackSubring K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) σ)
    p (fun a => ?_) (fun p q hp hq => ?_) (fun p i hp => ?_)
  · rw [MvPolynomial.aeval_C]
    exact criticalSheetGround_mem_pullback K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn) σ a
  · rw [map_add]
    exact Subring.add_mem _ hp hq
  · rw [map_mul, MvPolynomial.aeval_X]
    exact Subring.mul_mem _ hp
      (criticalSourceSchurCoordinates_mem_pullback K hm hn σ i)

/-- Evaluation of the Schur coordinate ring along a sheet, into the pullback subring. -/
def criticalSheetAevalHom (hm : 1 < m) (hn : 1 < n) (σ : criticalGeometricSheet K m n) :
    criticalSchurSourceRing K m n →+*
      criticalSheetPullbackSubring K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) σ where
  toFun p := ⟨MvPolynomial.aeval (criticalSourceSchurCoordinates K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn)) p, criticalSheetAeval_mem_pullback K hm hn σ p⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- Residue of the Schur coordinate ring along a sheet. -/
def criticalSheetCoordResidue (hm : 1 < m) (hn : 1 < n) (σ : criticalGeometricSheet K m n) :
    criticalSchurSourceRing K m n →+*
      ResidueField (criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
        (Nat.zero_lt_of_lt hn)) :=
  (criticalSheetResidue K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) σ).comp
    (criticalSheetAevalHom K hm hn σ)

/-- **Sheets with the same reduced Schur label induce the same residue on the Schur coordinate
ring.** -/
theorem criticalSheetCoordResidue_congr (hm : 1 < m) (hn : 1 < n)
    {σ τ : criticalGeometricSheet K m n}
    (h : criticalGeometricSheetToSchurReducedFibre K hm hn σ
      = criticalGeometricSheetToSchurReducedFibre K hm hn τ) :
    criticalSheetCoordResidue K hm hn σ = criticalSheetCoordResidue K hm hn τ := by
  refine MvPolynomial.ringHom_ext (fun k => ?_) (fun i => ?_)
  · show criticalSheetResidue K _ _ σ ⟨_, _⟩ = criticalSheetResidue K _ _ τ ⟨_, _⟩
    have key : σ (MvPolynomial.aeval (criticalSourceSchurCoordinates K (Nat.zero_lt_of_lt hm)
          (Nat.zero_lt_of_lt hn)) (MvPolynomial.C k))
        = τ (MvPolynomial.aeval (criticalSourceSchurCoordinates K (Nat.zero_lt_of_lt hm)
          (Nat.zero_lt_of_lt hn)) (MvPolynomial.C k)) := by
      rw [MvPolynomial.aeval_C, IsScalarTower.algebraMap_apply K
        (criticalObservationField K m n) (criticalSourceField K m n) k, σ.commutes, τ.commutes]
    exact congrArg (residue _) (Subtype.ext key)
  · show criticalSheetResidue K _ _ σ ⟨_, _⟩ = criticalSheetResidue K _ _ τ ⟨_, _⟩
    have hx : ∀ ρ : criticalGeometricSheet K m n,
        (⟨MvPolynomial.aeval (criticalSourceSchurCoordinates K (Nat.zero_lt_of_lt hm)
              (Nat.zero_lt_of_lt hn)) (MvPolynomial.X i),
            criticalSheetAeval_mem_pullback K hm hn ρ (MvPolynomial.X i)⟩ :
              criticalSheetPullbackSubring K (Nat.zero_lt_of_lt hm)
                (Nat.zero_lt_of_lt hn) ρ)
          = ⟨criticalSourceSchurCoordinates K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) i,
            criticalSourceSchurCoordinates_mem_pullback K hm hn ρ i⟩ :=
      fun ρ => Subtype.ext (MvPolynomial.aeval_X _ _)
    refine (congrArg (criticalSheetResidue K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn) σ) (hx σ)).trans ?_
    refine (criticalSheetSchurCoordinates_residue_congr K hm hn h i).trans ?_
    exact (congrArg (criticalSheetResidue K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn) τ) (hx τ)).symm

end

end GaloisForLFunctions.HTGeometry
