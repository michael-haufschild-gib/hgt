import GaloisForLFunctions.HTGeometry.FiniteGridCoherenceMoment
import Mathlib.Data.ZMod.Basic

/-!
# Axial-weight aliasing thresholds for Stokes response

Moreau's retained jet at order `k` has largest axial weight `k-1`; its symmetric response space has
largest weight `2k-2`. A cyclic axial sample of order greater than `2k-2` therefore cannot alias a
nonzero response weight to zero.

Here `k = n + 3`, so the largest symmetric weight is `2n+4`. Sample order is constructed with an
arbitrary nonnegative surplus, making the result unconditional. A second theorem reuses the corpus's
finite-grid replica-band lemma: order greater than twice a full bandwidth makes every signed weight
residue distinct, not merely distinct from zero.
-/

namespace GaloisForLFunctions.HTGeometry.StokesResistance

/-- Largest axial Fourier weight in the symmetric response space at paper order `k = n + 3`. -/
def symmetricJetMaxWeight (n : ℕ) : ℕ := 2 * n + 4

/-- Cyclic sample order strictly above the largest symmetric-response weight. -/
def axialSampleOrder (n surplus : ℕ) : ℕ :=
  symmetricJetMaxWeight n + surplus + 1

/-- Constructed axial sample order is always beyond the paper's collapse threshold. -/
theorem symmetricJetMaxWeight_lt_axialSampleOrder (n surplus : ℕ) :
    symmetricJetMaxWeight n < axialSampleOrder n surplus := by
  simp [axialSampleOrder]

/-- No positive nonzero symmetric-response weight aliases to weight zero. -/
theorem positive_symmetricJetWeight_ne_zero_mod_axialSampleOrder
    (n surplus : ℕ) (m : Fin (symmetricJetMaxWeight n)) :
    ((m.val + 1 : ℕ) : ZMod (axialSampleOrder n surplus)) ≠ 0 := by
  intro h
  have hdvd : axialSampleOrder n surplus ∣ m.val + 1 :=
    (ZMod.natCast_eq_zero_iff _ _).mp h
  have hle : axialSampleOrder n surplus ≤ m.val + 1 :=
    Nat.le_of_dvd (by omega) hdvd
  have hm := m.isLt
  change m.val < 2 * n + 4 at hm
  change 2 * n + 4 + surplus + 1 ≤ m.val + 1 at hle
  omega

/-- No negative nonzero symmetric-response weight aliases to weight zero. -/
theorem negative_symmetricJetWeight_ne_zero_mod_axialSampleOrder
    (n surplus : ℕ) (m : Fin (symmetricJetMaxWeight n)) :
    -(((m.val + 1 : ℕ) : ZMod (axialSampleOrder n surplus))) ≠ 0 := by
  exact neg_ne_zero.mpr
    (positive_symmetricJetWeight_ne_zero_mod_axialSampleOrder n surplus m)

/-- Sample order strictly above twice a general signed bandwidth. -/
def fullBandSampleOrder (L surplus : ℕ) : ℕ := 2 * L + surplus + 1

/-- Residue of a signed weight in `[-L,L]`, indexed from left to right. -/
def centeredWeightResidue (L surplus : ℕ) :
    Fin (2 * L + 1) → ZMod (fullBandSampleOrder L surplus) :=
  fun i => ((i.val : ℤ) - L : ℤ)

/-- Above twice bandwidth, all signed weights have pairwise distinct residues. -/
theorem centeredWeightResidue_injective (L surplus : ℕ) :
    Function.Injective (centeredWeightResidue L surplus) := by
  intro a b hab
  have ha : |(a.val : ℤ) - L| ≤ (L : ℤ) := by
    rw [abs_le]
    constructor <;> omega
  have hb : |(b.val : ℤ) - L| ≤ (L : ℤ) := by
    rw [abs_le]
    constructor <;> omega
  have heq : (a.val : ℤ) - L = (b.val : ℤ) - L :=
    GaloisForLFunctions.HTGeometry.zmod_cast_injective_on_replica_band_of_two_mul_lt
      L (fullBandSampleOrder L surplus) (by simp [fullBandSampleOrder]) ha hb hab
  apply Fin.ext
  omega

end GaloisForLFunctions.HTGeometry.StokesResistance
