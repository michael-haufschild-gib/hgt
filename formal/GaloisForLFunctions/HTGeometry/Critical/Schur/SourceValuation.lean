import GaloisForLFunctions.HTGeometry.Critical.Schur.GenericCorank
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.RamificationGroup

/-!
# The Schur divisorial valuation on the actual critical source field

The height-one Schur prime gives a DVR in the rational coordinate presentation.  Its fraction-field
valuation is transported through the actual Schur-coordinate equivalence to the concrete critical
source field, then restricted to the actual observation field.  These are the valuation rings used
to define decomposition and inertia groups in the normal closure.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsDiscreteValuationRing


/-- The Schur-coordinate field equivalence sends an embedded coordinate polynomial to its actual
evaluation in the critical source field. -/
theorem criticalSourceSchurFieldEquiv_algebraMap_apply
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (p : criticalSchurSourceRing K m n) :
    criticalSourceSchurFieldEquiv K hm hn
        (algebraMap (criticalSchurSourceRing K m n)
          (FractionRing (criticalSchurSourceRing K m n)) p) =
      MvPolynomial.aeval (criticalSourceSchurCoordinates K hm hn) p := by
  let hAI := algebraicIndependent_criticalSourceSchurCoordinates K hm hn
  have h := hAI.aevalEquivField_algebraMap_apply_coe p
  rw [criticalSourceSchurFieldEquiv, AlgEquiv.trans_apply]
  change (((algebraicIndependent_criticalSourceSchurCoordinates K hm hn).aevalEquivField
      (algebraMap _ (FractionRing (criticalSchurSourceRing K m n)) p) :
        IntermediateField.adjoin K
          (Set.range (criticalSourceSchurCoordinates K hm hn))) :
      criticalSourceField K m n) = _
  exact h

/-- Valuation ring of the Schur height-one prime inside its coordinate fraction field. -/
noncomputable def criticalSchurCoordinateValuationSubring
    (K : Type*) [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ValuationSubring (FractionRing (criticalSchurSourceRing K m n)) := by
  let R := criticalSchurSourceRing K m n
  let P := criticalSchurPrimeDivisor K hm hn
  let A := Localization.AtPrime P.1
  exact ((IsDiscreteValuationRing.maximalIdeal A).valuation
    (FractionRing R)).valuationSubring

/-- Actual Schur divisorial valuation ring in the concrete critical source field. -/
noncomputable def criticalSchurSourceValuationSubring
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ValuationSubring (criticalSourceField K m n) :=
  (criticalSchurCoordinateValuationSubring K hm hn).comap
    (criticalSourceSchurFieldEquiv K hm hn).symm.toRingHom

/-- Restriction of the actual Schur divisorial valuation to the observation field. -/
noncomputable def criticalSchurObservationValuationSubring
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ValuationSubring (criticalObservationField K m n) :=
  (criticalSchurSourceValuationSubring K hm hn).comap
    (algebraMap (criticalObservationField K m n) (criticalSourceField K m n))

@[simp] theorem mem_criticalSchurSourceValuationSubring_iff
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (x : criticalSourceField K m n) :
    x ∈ criticalSchurSourceValuationSubring K hm hn ↔
      (criticalSourceSchurFieldEquiv K hm hn).symm x ∈
        criticalSchurCoordinateValuationSubring K hm hn :=
  ValuationSubring.mem_comap

@[simp] theorem mem_criticalSchurObservationValuationSubring_iff
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (x : criticalObservationField K m n) :
    x ∈ criticalSchurObservationValuationSubring K hm hn ↔
      algebraMap (criticalObservationField K m n) (criticalSourceField K m n) x ∈
        criticalSchurSourceValuationSubring K hm hn :=
  ValuationSubring.mem_comap

end

end GaloisForLFunctions.HTGeometry
