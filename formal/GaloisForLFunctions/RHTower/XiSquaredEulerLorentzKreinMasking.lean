import GaloisForLFunctions.HTGeometry.HiggsSpinorNullCone
import GaloisForLFunctions.HTGeometry.RectangularKreinInertia
import GaloisForLFunctions.RHTower.ThetaCuspCenterMixedFourPointParityWall
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryPadeContactParity
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
    squaredEulerOrbitLorentzTime t c X ^ (2 : ℕ) -
        squaredEulerOrbitLorentzSpace t c X ^ (2 : ℕ) -
        squaredEulerOrbitLorentzAxis t c X ^ (2 : ℕ) =
      -c / (((t + X) ^ (2 : ℕ) + c) ^ (4 : ℕ)) := by
  calc
    squaredEulerOrbitLorentzTime t c X ^ (2 : ℕ) -
          squaredEulerOrbitLorentzSpace t c X ^ (2 : ℕ) -
          squaredEulerOrbitLorentzAxis t c X ^ (2 : ℕ) =
        squaredEulerOrbitReversedLoewnerMoment0 t c X *
            squaredEulerOrbitReversedLoewnerMoment2 t c X -
          squaredEulerOrbitReversedLoewnerMoment1 t c X ^ (2 : ℕ) := by
            unfold squaredEulerOrbitLorentzTime squaredEulerOrbitLorentzSpace
              squaredEulerOrbitLorentzAxis
            ring
    _ = -c / (((t + X) ^ (2 : ℕ) + c) ^ (4 : ℕ)) :=
      squaredEulerOrbit_reversedLoewnerJet_det_eq hch hX

/-- Every genuinely transverse orbit jet is spacelike in the Lorentz determinant geometry. -/
theorem squaredEulerOrbit_lorentzMassSq_neg
    {t c X : ℝ} (hch : SquaredEulerOrbitChamber t c) (hc : 0 < c) (hX : 0 ≤ X) :
    squaredEulerOrbitLorentzTime t c X ^ (2 : ℕ) -
        squaredEulerOrbitLorentzSpace t c X ^ (2 : ℕ) -
        squaredEulerOrbitLorentzAxis t c X ^ (2 : ℕ) < 0 := by
  rw [squaredEulerOrbit_lorentzMassSq_eq_neg_charge hch hX]
  have hden : 0 < (t + X) ^ (2 : ℕ) + c := by
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
      squaredEulerPacketLorentzTime S t c X ^ (2 : ℕ) -
        squaredEulerPacketLorentzSpace S t c X ^ (2 : ℕ) -
        squaredEulerPacketLorentzAxis S t c X ^ (2 : ℕ) := by
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
  have hnum : 0 < (t + X) ^ (2 : ℕ) - c := by
    have htxsq : t ^ (2 : ℕ) ≤ (t + X) ^ (2 : ℕ) := by
      nlinarith [mul_nonneg hch.1.le hX, sq_nonneg X]
    linarith [hch.2.2]
  have hden : 0 < (t + X) ^ (2 : ℕ) + c := by
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
      0 ≤ squaredEulerPacketLorentzTime S t c X ^ (2 : ℕ) -
        squaredEulerPacketLorentzSpace S t c X ^ (2 : ℕ) -
        squaredEulerPacketLorentzAxis S t c X ^ (2 : ℕ) := by
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

/-! ## All-order signed Vandermonde factorization -/

/-- Reciprocal complex atom whose real power jets generate one squared-orbit packet.  The signed
transverse coordinate `b` satisfies `c = b²`. -/
def squaredEulerReciprocalAtom (t b X : ℝ) : ℂ :=
  (((t + X : ℝ) : ℂ) + (b : ℂ) * Complex.I)⁻¹

/-- All-order reversed-Löwner moment generated by one reciprocal complex atom. -/
def squaredEulerReciprocalPowerMoment (t b X : ℝ) (n : ℕ) : ℝ :=
  (squaredEulerReciprocalAtom t b X ^ (n + 2)).re

/-- All-order finite-packet Hankel jet matrix of reciprocal squared-orbit atoms. -/
def squaredEulerReciprocalPacketJetMatrix
    {k N : ℕ} (t b : Fin k → ℝ) (X : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun p q => ∑ i,
    squaredEulerReciprocalPowerMoment (t i) (b i) X ((p : ℕ) + (q : ℕ))

/-- Positive real-power feature of one reciprocal atom. -/
def squaredEulerReciprocalPositiveFeature
    {k N : ℕ} (t b : Fin k → ℝ) (X : ℝ) (i : Fin k) : Fin N → ℂ :=
  fun p => ((squaredEulerReciprocalAtom (t i) (b i) X ^ ((p : ℕ) + 1)).re : ℂ)

/-- Negative imaginary-power feature of one reciprocal atom. -/
def squaredEulerReciprocalNegativeFeature
    {k N : ℕ} (t b : Fin k → ℝ) (X : ℝ) (i : Fin k) : Fin N → ℂ :=
  fun p => ((squaredEulerReciprocalAtom (t i) (b i) X ^ ((p : ℕ) + 1)).im : ℂ)

/-- Reciprocal atoms and their conjugates, reindexed as one square Vandermonde node family. -/
def squaredEulerReciprocalConjugateNodes
    {k : ℕ} (t b : Fin k → ℝ) (X : ℝ) : Fin (k + k) → ℂ :=
  fun j => Sum.elim
    (fun i => squaredEulerReciprocalAtom (t i) (b i) X)
    (fun i => star (squaredEulerReciprocalAtom (t i) (b i) X))
    (finSumFinEquiv.symm j)

private theorem half_conj_add_eq_ofReal_re (z : ℂ) :
    (1 / 2 : ℂ) * (star z + z) = (z.re : ℂ) := by
  apply Complex.ext
  · simp [Complex.mul_re]
    ring
  · simp [Complex.mul_im]

private theorem I_half_mul_conj_sub_eq_ofReal_im (z : ℂ) :
    (Complex.I / 2) * (star z - z) = (z.im : ℂ) := by
  apply Complex.ext
  · simp [Complex.mul_re]
    ring
  · simp [Complex.mul_im]

/-- Distinct nonzero reciprocal atoms and conjugates make the combined real/imaginary power
features linearly independent at order `2k`.  This is the signed-Vandermonde interpolation core. -/
theorem squaredEulerReciprocalFeatures_linearIndependent
    {k : ℕ} (t b : Fin k → ℝ) (X : ℝ)
    (hnode : Function.Injective (squaredEulerReciprocalConjugateNodes t b X))
    (hne : ∀ j, squaredEulerReciprocalConjugateNodes t b X j ≠ 0) :
    LinearIndependent ℂ
      (Sum.elim
        (squaredEulerReciprocalPositiveFeature (N := k + k) t b X)
        (squaredEulerReciprocalNegativeFeature (N := k + k) t b X)) := by
  classical
  let σ : Fin k ⊕ Fin k ≃ Fin (k + k) := finSumFinEquiv
  let P : Fin (k + k) → ℂ := squaredEulerReciprocalConjugateNodes t b X
  have Pinl (i : Fin k) :
      P (σ (Sum.inl i)) = squaredEulerReciprocalAtom (t i) (b i) X := by
    change Sum.elim
        (fun j => squaredEulerReciprocalAtom (t j) (b j) X)
        (fun j => star (squaredEulerReciprocalAtom (t j) (b j) X))
        (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  have Pinr (i : Fin k) :
      P (σ (Sum.inr i)) = star (squaredEulerReciprocalAtom (t i) (b i) X) := by
    change Sum.elim
        (fun j => squaredEulerReciprocalAtom (t j) (b j) X)
        (fun j => star (squaredEulerReciprocalAtom (t j) (b j) X))
        (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  have hV0 : LinearIndependent ℂ (fun j => (Matrix.vandermonde P) j) :=
    Matrix.linearIndependent_rows_of_det_ne_zero
      ((Matrix.det_vandermonde_ne_zero_iff).2 hnode)
  have hV1 : LinearIndependent ℂ
      (fun j => P j • (Matrix.vandermonde P) j) :=
    linearIndependent_smul_nonzero
      (fun j => (Matrix.vandermonde P) j) P hV0 hne
  let C : (Fin k ⊕ Fin k) → (Fin (k + k) → ℂ) :=
    Sum.elim
      (fun i p => squaredEulerReciprocalAtom (t i) (b i) X ^ ((p : ℕ) + 1))
      (fun i p => star (squaredEulerReciprocalAtom (t i) (b i) X) ^
        ((p : ℕ) + 1))
  have hC : LinearIndependent ℂ C := by
    have hcomp := hV1.comp σ σ.injective
    have hfamily : C = (fun j => P j • (Matrix.vandermonde P) j) ∘ σ := by
      funext s p
      cases s with
      | inl i =>
          change squaredEulerReciprocalAtom (t i) (b i) X ^ ((p : ℕ) + 1) =
            P (σ (Sum.inl i)) * P (σ (Sum.inl i)) ^ (p : ℕ)
          rw [Pinl, pow_succ']
      | inr i =>
          change star (squaredEulerReciprocalAtom (t i) (b i) X) ^
              ((p : ℕ) + 1) =
            P (σ (Sum.inr i)) * P (σ (Sum.inr i)) ^ (p : ℕ)
          rw [Pinr, pow_succ']
    rw [hfamily]
    exact hcomp
  let paired : (Fin k ⊕ Fin k) → (Fin (k + k) → ℂ) := fun s =>
    match s with
    | Sum.inl i => C (Sum.inr i) + C (Sum.inl i)
    | Sum.inr i => C (Sum.inr i) - C (Sum.inl i)
  have hpaired : LinearIndependent ℂ paired := by
    exact GaloisForLFunctions.linearIndependent_pm_of C hC
  let scale : Fin k ⊕ Fin k → ℂ :=
    Sum.elim (fun _ => 1 / 2) (fun _ => Complex.I / 2)
  have hscale : ∀ s, scale s ≠ 0 := by
    intro s
    cases s <;> simp [scale]
  have hscaled : LinearIndependent ℂ (fun s => scale s • paired s) :=
    linearIndependent_smul_nonzero paired scale hpaired hscale
  have hfamily :
      Sum.elim
          (squaredEulerReciprocalPositiveFeature (N := k + k) t b X)
          (squaredEulerReciprocalNegativeFeature (N := k + k) t b X) =
        fun s => scale s • paired s := by
    funext s p
    cases s with
    | inl i =>
        simpa [squaredEulerReciprocalPositiveFeature, scale, paired, C,
          Pi.smul_apply, smul_eq_mul, map_pow] using
          (half_conj_add_eq_ofReal_re
            (squaredEulerReciprocalAtom (t i) (b i) X ^ ((p : ℕ) + 1))).symm
    | inr i =>
        simpa [squaredEulerReciprocalNegativeFeature, scale, paired, C,
          Pi.smul_apply, smul_eq_mul, map_pow] using
          (I_half_mul_conj_sub_eq_ofReal_im
            (squaredEulerReciprocalAtom (t i) (b i) X ^ ((p : ℕ) + 1))).symm
  rw [hfamily]
  exact hscaled

/-- **All-order signed Vandermonde law.**  Entrywise complexification of the reciprocal-orbit jet
tower is exactly the positive real-feature Gram minus the negative imaginary-feature Gram. -/
theorem squaredEulerReciprocalPacketJetMatrix_complexification_eq_rectangularKreinForm
    {k N : ℕ} (t b : Fin k → ℝ) (X : ℝ) :
    (squaredEulerReciprocalPacketJetMatrix (N := N) t b X).map Complex.ofReal =
      rectangularKreinForm
        (squaredEulerReciprocalPositiveFeature (N := N) t b X)
        (squaredEulerReciprocalNegativeFeature (N := N) t b X) := by
  ext p q
  simp only [squaredEulerReciprocalPacketJetMatrix, Matrix.map_apply,
    rectangularKreinForm, Matrix.sub_apply, Matrix.sum_apply, Matrix.of_apply,
    squaredEulerReciprocalPowerMoment, squaredEulerReciprocalPositiveFeature,
    squaredEulerReciprocalNegativeFeature]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hpow :
      squaredEulerReciprocalAtom (t i) (b i) X ^
          ((p : ℕ) + (q : ℕ) + 2) =
        squaredEulerReciprocalAtom (t i) (b i) X ^ ((p : ℕ) + 1) *
          squaredEulerReciprocalAtom (t i) (b i) X ^ ((q : ℕ) + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow, Complex.mul_re]
  norm_num

/-- Concrete frontier condition for exact finite-packet negative inertia: the real and imaginary
reciprocal-power feature families jointly interpolate arbitrary data. -/
def SquaredEulerReciprocalFeaturesSurjective
    {k N : ℕ} (t b : Fin k → ℝ) (X : ℝ) : Prop :=
  Function.Surjective
    ((rectangularFeatureEval
        (squaredEulerReciprocalPositiveFeature (N := N) t b X)).prod
      (rectangularFeatureEval
        (squaredEulerReciprocalNegativeFeature (N := N) t b X)))

/-- Distinct nonzero atom/conjugate nodes discharge the interpolation condition at the sharp
square order `N = 2k`. -/
theorem squaredEulerReciprocalFeaturesSurjective_of_conjugateNodes_injective
    {k : ℕ} (t b : Fin k → ℝ) (X : ℝ)
    (hnode : Function.Injective (squaredEulerReciprocalConjugateNodes t b X))
    (hne : ∀ j, squaredEulerReciprocalConjugateNodes t b X j ≠ 0) :
    SquaredEulerReciprocalFeaturesSurjective (N := k + k) t b X := by
  exact rectangular_eval_surjective_of_linearIndependent
    (squaredEulerReciprocalPositiveFeature (N := k + k) t b X)
    (squaredEulerReciprocalNegativeFeature (N := k + k) t b X)
    (squaredEulerReciprocalFeatures_linearIndependent t b X hnode hne)

/-- Joint feature interpolation exposes a negative-definite subspace with one dimension per
reciprocal orbit. -/
theorem squaredEulerReciprocalPacketJetMatrix_exists_negativeSubspace
    {k N : ℕ} (t b : Fin k → ℝ) (X : ℝ)
    (hT : SquaredEulerReciprocalFeaturesSurjective (N := N) t b X) :
    ∃ W : Submodule ℂ (Fin N → ℂ), Module.finrank ℂ W = k ∧
      ∀ y ∈ W, y ≠ 0 →
        (star y ⬝ᵥ
          ((squaredEulerReciprocalPacketJetMatrix (N := N) t b X).map
            Complex.ofReal).mulVec y).re < 0 := by
  rw [squaredEulerReciprocalPacketJetMatrix_complexification_eq_rectangularKreinForm]
  exact exists_rectangular_neg_def_subspace
    (squaredEulerReciprocalPositiveFeature (N := N) t b X)
    (squaredEulerReciprocalNegativeFeature (N := N) t b X) hT

/-- Under joint interpolation, reciprocal packet jets have exact negative inertia equal to orbit
count—not merely one detectable negative minor. -/
theorem squaredEulerReciprocalPacketJetMatrix_exact_negativeInertia
    {k N : ℕ} (t b : Fin k → ℝ) (X : ℝ)
    (hT : SquaredEulerReciprocalFeaturesSurjective (N := N) t b X) :
    (∀ W : Submodule ℂ (Fin N → ℂ),
        (∀ y ∈ W, y ≠ 0 →
          (star y ⬝ᵥ
            ((squaredEulerReciprocalPacketJetMatrix (N := N) t b X).map
              Complex.ofReal).mulVec y).re < 0) →
        Module.finrank ℂ W ≤ k) ∧
      (∃ W : Submodule ℂ (Fin N → ℂ), Module.finrank ℂ W = k ∧
        ∀ y ∈ W, y ≠ 0 →
          (star y ⬝ᵥ
            ((squaredEulerReciprocalPacketJetMatrix (N := N) t b X).map
              Complex.ofReal).mulVec y).re < 0) := by
  rw [squaredEulerReciprocalPacketJetMatrix_complexification_eq_rectangularKreinForm]
  exact rectangular_exact_neg_inertia
    (squaredEulerReciprocalPositiveFeature (N := N) t b X)
    (squaredEulerReciprocalNegativeFeature (N := N) t b X) hT

/-! ## Exact inertia of actual finite shifted-Xi packets -/

/-- The reciprocal atom built from the real and imaginary coordinates of a squared Xi node is
the actual shifted reciprocal-square atom. -/
theorem squaredEulerReciprocalAtom_xiSquaredNode_eq_shifted
    {y : ℝ} (hy : 0 ≤ y) (q : XiZeroCopy) :
    squaredEulerReciprocalAtom (xiSquaredNode q).re (xiSquaredNode q).im y =
      xiShiftedReciprocalSquare y q := by
  rw [squaredEulerReciprocalAtom, xiShiftedReciprocalSquare_eq_inv hy]
  congr 1
  apply Complex.ext <;> simp [add_comm]

/-- A fold-distinct family of nonreal nodes remains distinct after adjoining every conjugate. -/
theorem conjugateFoldPair_injective
    {k : ℕ} (z : Fin k → ℂ)
    (hfold : Function.Injective (fun i => complexConjugationFold (z i)))
    (him : ∀ i, (z i).im ≠ 0) :
    Function.Injective
      (Sum.elim z (fun i => star (z i)) : Fin k ⊕ Fin k → ℂ) := by
  rw [Sum.elim_injective]
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    apply hfold
    change complexConjugationFold (z i) = complexConjugationFold (z j)
    rw [hij]
  · exact star_injective.comp (by
      intro i j hij
      apply hfold
      change complexConjugationFold (z i) = complexConjugationFold (z j)
      rw [hij])
  · intro i j hij
    have hfj : complexConjugationFold (z i) = complexConjugationFold (z j) := by
      rw [hij]
      exact complexConjugationFold_conj (z j)
    have hij' : i = j := hfold hfj
    subst j
    have hi := congrArg Complex.im hij
    apply him i
    simp only [Complex.star_def, Complex.conj_im] at hi
    linarith

/-- Distinct folded off-critical Xi orbits give a collision-free atom/conjugate family. -/
theorem xiShiftedReciprocalConjugateNodes_injective
    {k : ℕ} (q : Fin k → XiZeroCopy) {y : ℝ} (hy : 0 ≤ y)
    (hoff : ∀ i, ((q i).1 : ℂ).re ≠ 1 / 2)
    (hfold : Function.Injective (fun i =>
      complexConjugationFold (xiShiftedReciprocalSquare y (q i)))) :
    Function.Injective
      (squaredEulerReciprocalConjugateNodes
        (fun i => (xiSquaredNode (q i)).re)
        (fun i => (xiSquaredNode (q i)).im) y) := by
  let z : Fin k → ℂ := fun i => xiShiftedReciprocalSquare y (q i)
  have hzim : ∀ i, (z i).im ≠ 0 := by
    intro i hzero
    have hcentral : (xiZeroCopyReciprocalSquare (q i)).im = 0 :=
      (xiShiftedReciprocalSquare_im_eq_zero_iff hy (q i)).mp hzero
    have hline : ((q i).1 : ℂ).re = 1 / 2 :=
      (xiCentralReciprocalSquare_im_eq_zero_iff (q i).1).mp (by
        simpa only [xiZeroCopyReciprocalSquare_eq] using hcentral)
    exact hoff i hline
  have hpair : Function.Injective
      (Sum.elim z (fun i => star (z i)) : Fin k ⊕ Fin k → ℂ) :=
    conjugateFoldPair_injective z hfold hzim
  have hcomp := hpair.comp finSumFinEquiv.symm.injective
  intro a b hab
  apply hcomp
  change Sum.elim z (fun i => star (z i)) (finSumFinEquiv.symm a) =
    Sum.elim z (fun i => star (z i)) (finSumFinEquiv.symm b)
  simpa only [squaredEulerReciprocalConjugateNodes, z,
    squaredEulerReciprocalAtom_xiSquaredNode_eq_shifted hy] using hab

/-- Finite shifted-Xi reciprocal-power jet matrix. -/
def xiShiftedReciprocalFinitePacketJetMatrix
    {k N : ℕ} (q : Fin k → XiZeroCopy) (y : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun p r => ∑ i,
    (xiShiftedReciprocalSquare y (q i) ^ ((p : ℕ) + (r : ℕ) + 2)).re

/-- The actual finite shifted-Xi jet is the squared-Euler reciprocal packet jet. -/
theorem xiShiftedReciprocalFinitePacketJetMatrix_eq_squaredEuler
    {k N : ℕ} (q : Fin k → XiZeroCopy) {y : ℝ} (hy : 0 ≤ y) :
    xiShiftedReciprocalFinitePacketJetMatrix (N := N) q y =
      squaredEulerReciprocalPacketJetMatrix
        (N := N) (fun i => (xiSquaredNode (q i)).re)
          (fun i => (xiSquaredNode (q i)).im) y := by
  ext p r
  simp only [xiShiftedReciprocalFinitePacketJetMatrix,
    squaredEulerReciprocalPacketJetMatrix, squaredEulerReciprocalPowerMoment]
  apply Finset.sum_congr rfl
  intro i _
  rw [squaredEulerReciprocalAtom_xiSquaredNode_eq_shifted hy]

/-- Fold-distinct off-critical shifted-Xi atoms jointly interpolate all real and imaginary power
features at the sharp order `2k`. -/
theorem xiShiftedReciprocalFeaturesSurjective_of_fold_injective
    {k : ℕ} (q : Fin k → XiZeroCopy) {y : ℝ} (hy : 0 ≤ y)
    (hoff : ∀ i, ((q i).1 : ℂ).re ≠ 1 / 2)
    (hfold : Function.Injective (fun i =>
      complexConjugationFold (xiShiftedReciprocalSquare y (q i)))) :
    SquaredEulerReciprocalFeaturesSurjective (N := k + k)
      (fun i => (xiSquaredNode (q i)).re)
      (fun i => (xiSquaredNode (q i)).im) y := by
  apply squaredEulerReciprocalFeaturesSurjective_of_conjugateNodes_injective
  · exact xiShiftedReciprocalConjugateNodes_injective q hy hoff hfold
  · intro j
    unfold squaredEulerReciprocalConjugateNodes
    generalize hs : finSumFinEquiv.symm j = s
    cases s with
    | inl i =>
        simp only [Sum.elim_inl]
        rw [squaredEulerReciprocalAtom_xiSquaredNode_eq_shifted hy]
        exact xiShiftedReciprocalSquare_ne_zero hy (q i)
    | inr i =>
        simp only [Sum.elim_inr]
        apply star_ne_zero.mpr
        rw [squaredEulerReciprocalAtom_xiSquaredNode_eq_shifted hy]
        exact xiShiftedReciprocalSquare_ne_zero hy (q i)

/-- **Exact finite shifted-Xi inertia.**  A packet of `k` distinct folded off-critical Xi orbits
has exactly `k` negative directions at reciprocal-jet order `2k`.  Cross-orbit masking can hide
low-order minors, but cannot remove any orbit's negative charge at full interpolation depth. -/
theorem xiShiftedReciprocalFinitePacketJetMatrix_exact_negativeInertia
    {k : ℕ} (q : Fin k → XiZeroCopy) {y : ℝ} (hy : 0 ≤ y)
    (hoff : ∀ i, ((q i).1 : ℂ).re ≠ 1 / 2)
    (hfold : Function.Injective (fun i =>
      complexConjugationFold (xiShiftedReciprocalSquare y (q i)))) :
    (∀ W : Submodule ℂ (Fin (k + k) → ℂ),
        (∀ x ∈ W, x ≠ 0 →
          (star x ⬝ᵥ
            ((xiShiftedReciprocalFinitePacketJetMatrix (N := k + k) q y).map
              Complex.ofReal).mulVec x).re < 0) →
        Module.finrank ℂ W ≤ k) ∧
      (∃ W : Submodule ℂ (Fin (k + k) → ℂ),
        Module.finrank ℂ W = k ∧
          ∀ x ∈ W, x ≠ 0 →
            (star x ⬝ᵥ
              ((xiShiftedReciprocalFinitePacketJetMatrix (N := k + k) q y).map
                Complex.ofReal).mulVec x).re < 0) := by
  rw [xiShiftedReciprocalFinitePacketJetMatrix_eq_squaredEuler q hy]
  exact squaredEulerReciprocalPacketJetMatrix_exact_negativeInertia
    (fun i => (xiSquaredNode (q i)).re)
    (fun i => (xiSquaredNode (q i)).im) y
    (xiShiftedReciprocalFeaturesSurjective_of_fold_injective q hy hoff hfold)

/-- Fold injectivity of a finite Xi family is invariant under every nonnegative reciprocal mass
shift.  Therefore the exact negative charge above is a conserved orbit count along the shift. -/
theorem xiShiftedReciprocal_conjugationFold_injective_iff_shift
    {k : ℕ} (q : Fin k → XiZeroCopy) {y v : ℝ} (hy : 0 ≤ y) (hv : 0 ≤ v) :
    Function.Injective (fun i =>
        complexConjugationFold (xiShiftedReciprocalSquare y (q i))) ↔
      Function.Injective (fun i =>
        complexConjugationFold (xiShiftedReciprocalSquare v (q i))) := by
  constructor
  · intro h i j hij
    apply h
    exact (conjugationFold_xiShiftedReciprocalSquare_eq_iff_shift
      hy hv (q i) (q j)).mpr hij
  · intro h i j hij
    apply h
    exact (conjugationFold_xiShiftedReciprocalSquare_eq_iff_shift
      hy hv (q i) (q j)).mp hij

end

end RHTower
