import GaloisForLFunctions.HTGeometry.HiggsSpinorNullCone
import GaloisForLFunctions.RHTower.ThetaCuspCenterMixedFourPointParityWall
import GaloisForLFunctions.RHTower.XiSquaredEulerRayTwoPointPositivity

/-!
# Lorentz--Krein geometry of squared-Euler orbit masking

The first confluent reversed-Löwner jet of one squared Xi orbit is a real symmetric `2 × 2`
matrix.  Its three entries are exactly planar Lorentz coordinates: determinant is Lorentz mass
squared, determinant polarization is the Lorentz pairing, and transverse orbit charge is negative
mass squared.  Thus an off-critical orbit is spacelike at every nonnegative collision center.

For a finite packet, cross-orbit masking has one precise geometric meaning: the sum of spacelike
orbit vectors enters the positive-semidefinite Lorentz cone.  The final theorem identifies this
event with the exact interference-versus-charge inequality from the finite-packet decomposition.
No RH assumption occurs.
-/

open Matrix
open scoped Matrix

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- First reversed-Löwner jet matrix of one squared orbit. -/
def squaredEulerOrbitReversedLoewnerJetMatrix
    (t c X : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  symmetricTwoByTwo
    (squaredEulerOrbitReversedLoewnerMoment0 t c X)
    (squaredEulerOrbitReversedLoewnerMoment1 t c X)
    (squaredEulerOrbitReversedLoewnerMoment2 t c X)

/-- Lorentz time coordinate of one orbit jet. -/
def squaredEulerOrbitLorentzTime (t c X : ℝ) : ℝ :=
  (squaredEulerOrbitReversedLoewnerMoment0 t c X +
    squaredEulerOrbitReversedLoewnerMoment2 t c X) / 2

/-- Lorentz transverse coordinate of one orbit jet. -/
def squaredEulerOrbitLorentzSpace (t c X : ℝ) : ℝ :=
  squaredEulerOrbitReversedLoewnerMoment1 t c X

/-- Lorentz axial coordinate of one orbit jet. -/
def squaredEulerOrbitLorentzAxis (t c X : ℝ) : ℝ :=
  (squaredEulerOrbitReversedLoewnerMoment0 t c X -
    squaredEulerOrbitReversedLoewnerMoment2 t c X) / 2

/-- Minkowski pairing of two squared-orbit jet vectors in their common planar Lorentz slice. -/
def squaredEulerOrbitLorentzPair
    (t c t' c' X : ℝ) : ℝ :=
  squaredEulerOrbitLorentzTime t c X * squaredEulerOrbitLorentzTime t' c' X -
    squaredEulerOrbitLorentzSpace t c X * squaredEulerOrbitLorentzSpace t' c' X -
    squaredEulerOrbitLorentzAxis t c X * squaredEulerOrbitLorentzAxis t' c' X

/-- The real orbit jet matrix is exactly the planar slice of the corpus Lorentz--Hermitian
coordinate map. -/
theorem squaredEulerOrbitReversedLoewnerJetMatrix_complexification_eq_lorentzHermitianMatrix
    (t c X : ℝ) :
    (squaredEulerOrbitReversedLoewnerJetMatrix t c X).map Complex.ofReal =
      lorentzHermitianMatrix
        (squaredEulerOrbitLorentzTime t c X)
        (squaredEulerOrbitLorentzSpace t c X) 0
        (squaredEulerOrbitLorentzAxis t c X) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [squaredEulerOrbitReversedLoewnerJetMatrix, symmetricTwoByTwo,
      lorentzHermitianMatrix, squaredEulerOrbitLorentzTime,
      squaredEulerOrbitLorentzSpace, squaredEulerOrbitLorentzAxis]
  all_goals ring

/-- **Orbit mass-shell law.**  Lorentz mass squared is exactly negative transverse charge. -/
theorem squaredEulerOrbit_lorentzMassSq_eq_neg_charge
    {t c X : ℝ} (hch : SquaredEulerOrbitChamber t c) (hX : 0 ≤ X) :
    squaredEulerOrbitLorentzTime t c X ^ 2 -
        squaredEulerOrbitLorentzSpace t c X ^ 2 -
        squaredEulerOrbitLorentzAxis t c X ^ 2 =
      -c / (((t + X) ^ 2 + c) ^ 4) := by
  calc
    squaredEulerOrbitLorentzTime t c X ^ 2 -
          squaredEulerOrbitLorentzSpace t c X ^ 2 -
          squaredEulerOrbitLorentzAxis t c X ^ 2 =
        squaredEulerOrbitReversedLoewnerMoment0 t c X *
            squaredEulerOrbitReversedLoewnerMoment2 t c X -
          squaredEulerOrbitReversedLoewnerMoment1 t c X ^ 2 := by
            unfold squaredEulerOrbitLorentzTime squaredEulerOrbitLorentzSpace
              squaredEulerOrbitLorentzAxis
            ring
    _ = -c / (((t + X) ^ 2 + c) ^ 4) :=
      squaredEulerOrbit_reversedLoewnerJet_det_eq hch hX

/-- Every genuinely transverse orbit jet is spacelike in the Lorentz determinant geometry. -/
theorem squaredEulerOrbit_lorentzMassSq_neg
    {t c X : ℝ} (hch : SquaredEulerOrbitChamber t c) (hc : 0 < c) (hX : 0 ≤ X) :
    squaredEulerOrbitLorentzTime t c X ^ 2 -
        squaredEulerOrbitLorentzSpace t c X ^ 2 -
        squaredEulerOrbitLorentzAxis t c X ^ 2 < 0 := by
  rw [squaredEulerOrbit_lorentzMassSq_eq_neg_charge hch hX]
  have hden : 0 < (t + X) ^ 2 + c := by
    have htx : 0 < t + X := by linarith [hch.1]
    nlinarith [sq_pos_of_pos htx, hch.2.1]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hc) (pow_pos hden 4)

/-- Determinant cross-interaction is twice the Minkowski pairing. -/
theorem squaredEulerOrbitReversedLoewnerCross_eq_two_mul_lorentzPair
    (t c t' c' X : ℝ) :
    squaredEulerOrbitReversedLoewnerCross t c t' c' X =
      2 * squaredEulerOrbitLorentzPair t c t' c' X := by
  unfold squaredEulerOrbitReversedLoewnerCross squaredEulerOrbitLorentzPair
    squaredEulerOrbitLorentzTime squaredEulerOrbitLorentzSpace
    squaredEulerOrbitLorentzAxis
  ring

/-- Lorentz time coordinate of a finite squared-orbit packet. -/
def squaredEulerPacketLorentzTime
    {ι : Type*} (S : Finset ι) (t c : ι → ℝ) (X : ℝ) : ℝ :=
  ∑ i ∈ S, squaredEulerOrbitLorentzTime (t i) (c i) X

/-- Lorentz transverse coordinate of a finite squared-orbit packet. -/
def squaredEulerPacketLorentzSpace
    {ι : Type*} (S : Finset ι) (t c : ι → ℝ) (X : ℝ) : ℝ :=
  ∑ i ∈ S, squaredEulerOrbitLorentzSpace (t i) (c i) X

/-- Lorentz axial coordinate of a finite squared-orbit packet. -/
def squaredEulerPacketLorentzAxis
    {ι : Type*} (S : Finset ι) (t c : ι → ℝ) (X : ℝ) : ℝ :=
  ∑ i ∈ S, squaredEulerOrbitLorentzAxis (t i) (c i) X

/-- Reversed-Löwner jet matrix of a finite squared-orbit packet. -/
def squaredEulerPacketReversedLoewnerJetMatrix
    {ι : Type*} (S : Finset ι) (t c : ι → ℝ) (X : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  symmetricTwoByTwo
    (∑ i ∈ S, squaredEulerOrbitReversedLoewnerMoment0 (t i) (c i) X)
    (∑ i ∈ S, squaredEulerOrbitReversedLoewnerMoment1 (t i) (c i) X)
    (∑ i ∈ S, squaredEulerOrbitReversedLoewnerMoment2 (t i) (c i) X)

/-- Packet determinant is the Lorentz mass squared of the summed orbit vector. -/
theorem squaredEulerPacketReversedLoewnerJetDet_eq_lorentzMassSq
    {ι : Type*} (S : Finset ι) (t c : ι → ℝ) (X : ℝ) :
    squaredEulerPacketReversedLoewnerJetDet S t c X =
      squaredEulerPacketLorentzTime S t c X ^ 2 -
        squaredEulerPacketLorentzSpace S t c X ^ 2 -
        squaredEulerPacketLorentzAxis S t c X ^ 2 := by
  unfold squaredEulerPacketReversedLoewnerJetDet squaredEulerPacketLorentzTime
    squaredEulerPacketLorentzSpace squaredEulerPacketLorentzAxis
    squaredEulerOrbitLorentzTime squaredEulerOrbitLorentzSpace
    squaredEulerOrbitLorentzAxis
  rw [← Finset.sum_div, Finset.sum_add_distrib,
    ← Finset.sum_div, Finset.sum_sub_distrib]
  ring

/-- The leading orbit jet moment is positive throughout the squared-Euler chamber. -/
theorem squaredEulerOrbitReversedLoewnerMoment0_pos
    {t c X : ℝ} (hch : SquaredEulerOrbitChamber t c) (hX : 0 ≤ X) :
    0 < squaredEulerOrbitReversedLoewnerMoment0 t c X := by
  have htx : 0 < t + X := by linarith [hch.1]
  have hnum : 0 < (t + X) ^ 2 - c := by
    have htxsq : t ^ 2 ≤ (t + X) ^ 2 := by
      nlinarith [mul_nonneg hch.1.le hX, sq_nonneg X]
    linarith [hch.2.2]
  have hden : 0 < (t + X) ^ 2 + c := by
    nlinarith [sq_pos_of_pos htx, hch.2.1]
  exact div_pos hnum (sq_pos_of_pos hden)

/-- Every nonempty chamber packet has positive leading jet moment. -/
theorem squaredEulerPacketReversedLoewnerMoment0_sum_pos
    {ι : Type*} {S : Finset ι} (hS : S.Nonempty) (t c : ι → ℝ) {X : ℝ}
    (hch : ∀ i ∈ S, SquaredEulerOrbitChamber (t i) (c i))
    (hX : 0 ≤ X) :
    0 < ∑ i ∈ S, squaredEulerOrbitReversedLoewnerMoment0 (t i) (c i) X := by
  exact Finset.sum_pos
    (fun i hi => squaredEulerOrbitReversedLoewnerMoment0_pos (hch i hi) hX) hS

/-- The packet jet matrix is positive semidefinite exactly when its summed Lorentz vector has
nonnegative mass squared. -/
theorem squaredEulerPacketReversedLoewnerJetMatrix_posSemidef_iff_lorentzMassSq_nonneg
    {ι : Type*} {S : Finset ι} (hS : S.Nonempty) (t c : ι → ℝ) {X : ℝ}
    (hch : ∀ i ∈ S, SquaredEulerOrbitChamber (t i) (c i))
    (hX : 0 ≤ X) :
    (squaredEulerPacketReversedLoewnerJetMatrix S t c X).PosSemidef ↔
      0 ≤ squaredEulerPacketLorentzTime S t c X ^ 2 -
        squaredEulerPacketLorentzSpace S t c X ^ 2 -
        squaredEulerPacketLorentzAxis S t c X ^ 2 := by
  rw [squaredEulerPacketReversedLoewnerJetMatrix,
    symmetricTwoByTwo_posSemidef_iff_det_nonneg_of_pos_left
      (squaredEulerPacketReversedLoewnerMoment0_sum_pos hS t c hch hX),
    ← squaredEulerPacketReversedLoewnerJetDet_eq_lorentzMassSq]
  rfl

/-- **Lorentz-cone masking classification.**  A nonempty chamber packet enters the PSD cone
exactly when cross-orbit Lorentz interference pays its complete transverse mass debt. -/
theorem squaredEulerPacketReversedLoewnerJetMatrix_posSemidef_iff_interference_ge_charge
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} (hS : S.Nonempty) (t c : ι → ℝ) {X : ℝ}
    (hch : ∀ i ∈ S, SquaredEulerOrbitChamber (t i) (c i))
    (hX : 0 ≤ X) :
    (squaredEulerPacketReversedLoewnerJetMatrix S t c X).PosSemidef ↔
      2 * squaredEulerPacketReversedLoewnerCharge S t c X ≤
        squaredEulerPacketReversedLoewnerInterference S t c X := by
  rw [squaredEulerPacketReversedLoewnerJetMatrix,
    symmetricTwoByTwo_posSemidef_iff_det_nonneg_of_pos_left
      (squaredEulerPacketReversedLoewnerMoment0_sum_pos hS t c hch hX)]
  exact squaredEulerPacketReversedLoewnerJetDet_nonneg_iff_interference_ge_charge
    S t c hch hX

/-- Actual finite Xi specialization of the Lorentz-cone masking classification. -/
theorem xiSquaredEulerPacketReversedLoewnerJetMatrix_posSemidef_iff_interference_ge_charge
    {S : Finset XiZeroCopy} (hS : S.Nonempty) {X : ℝ} (hX : 0 ≤ X) :
    (squaredEulerPacketReversedLoewnerJetMatrix S
        xiSquaredEulerOrbitT xiSquaredEulerOrbitCharge X).PosSemidef ↔
      2 * squaredEulerPacketReversedLoewnerCharge S
          xiSquaredEulerOrbitT xiSquaredEulerOrbitCharge X ≤
        squaredEulerPacketReversedLoewnerInterference S
          xiSquaredEulerOrbitT xiSquaredEulerOrbitCharge X := by
  exact squaredEulerPacketReversedLoewnerJetMatrix_posSemidef_iff_interference_ge_charge
    hS xiSquaredEulerOrbitT xiSquaredEulerOrbitCharge
    (fun q _hq => xiSquaredEulerOrbit_mem_chamber q) hX

end

end RHTower
