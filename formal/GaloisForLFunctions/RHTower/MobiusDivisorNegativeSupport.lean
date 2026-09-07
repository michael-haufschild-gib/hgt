import GaloisForLFunctions.RHTower.MobiusDivisorParityDefectTransport
/-!
# Prime support of negative retained coordinates

An active prime belongs to the negative support exactly when its merger
strictly increases some surviving oriented coordinate. Outside that support,
every surviving coordinate decreases: complete good energy cannot increase,
and complete defect energy cannot decrease. These statements hold for mixed
fields and do not assert preservation of a geometric energy certificate.
-/

noncomputable section
open Finset
namespace RHTower

/-- Active primes occurring in a negative nonempty oriented coordinate. -/
def mobiusDivisorNegativeSupport (M : ℕ) (P : Finset ℕ) : Finset ℕ :=
  (mobiusDivisorSelectionPrimes M).filter fun q =>
    ∃ R ∈ (mobiusDivisorSelectionPrimes M).powerset,
      q ∈ R ∧ mobiusDivisorOrientedFibre M P R < 0

private lemma partner_nonneg {M q : ℕ} {P R : Finset ℕ}
    (hq : q ∈ mobiusDivisorSelectionPrimes M)
    (hn : q ∉ mobiusDivisorNegativeSupport M P)
    (hR : R ∈ (mobiusDivisorSelectionPrimes M).powerset) :
    0 ≤ mobiusDivisorOrientedFibre M P (insert q R) := by
  by_contra h
  apply hn
  exact mem_filter.mpr ⟨hq, insert q R,
    mem_powerset.mpr (insert_subset hq (mem_powerset.mp hR)),
    mem_insert_self _ _, lt_of_not_ge h⟩

private lemma positive_square_mono {x y : ℝ} (h : x ≤ y) :
    (max x 0)^2 ≤ (max y 0)^2 := by
  have hm : max x 0 ≤ max y 0 := max_le_max_right 0 h
  have hx : 0 ≤ max x 0 := le_max_right _ _
  have hy : 0 ≤ max y 0 := le_max_right _ _
  nlinarith [mul_nonneg (sub_nonneg.mpr hm) (add_nonneg hx hy)]

/-- A negative prime partner exists exactly when a surviving coordinate strictly increases. -/
theorem mobiusDivisorNegativeSupport_iff_coordinate_increase
    (M : ℕ) (P : Finset ℕ) {q : ℕ} (hq : q ∈ mobiusDivisorSelectionPrimes M) :
    q ∈ mobiusDivisorNegativeSupport M P ↔
      ∃ R ∈ (mobiusDivisorSelectionPrimes M).powerset, q ∉ R ∧
        mobiusDivisorOrientedFibre M P R <
          mobiusDivisorOrientedFibre M (insert q P) R := by
  constructor
  · intro h
    obtain ⟨S, hS, hqS, hneg⟩ := (mem_filter.mp h).2
    refine ⟨S.erase q, mem_powerset.mpr ((erase_subset q S).trans (mem_powerset.mp hS)),
      notMem_erase q S, ?_⟩
    rw [mobiusDivisorOrientedFibre_insert M P (S.erase q) q (notMem_erase q S),
      insert_erase hqS]
    linarith
  · rintro ⟨R, hR, hqR, hinc⟩
    rw [mobiusDivisorOrientedFibre_insert M P R q hqR] at hinc
    exact mem_filter.mpr ⟨hq, insert q R,
      mem_powerset.mpr (insert_subset hq (mem_powerset.mp hR)),
      mem_insert_self _ _, by linarith⟩

/-- A prime outside the negative support decreases good energy and increases defect energy,
with no restriction on the signs of the current retained field. -/
theorem mobiusDivisorParityEnergy_insert_outside_negativeSupport
    (M : ℕ) (P : Finset ℕ) {q : ℕ} (hq : q ∈ mobiusDivisorSelectionPrimes M)
    (hn : q ∉ mobiusDivisorNegativeSupport M P) :
    mobiusDivisorParityGoodEnergy M (insert q P) ≤ mobiusDivisorParityGoodEnergy M P ∧
      mobiusDivisorParityDefectEnergy M P ≤ mobiusDivisorParityDefectEnergy M (insert q P) := by
  have hpair (R : Finset ℕ) (hR : R ∈ (mobiusDivisorSelectionPrimes M).powerset) :
      (max (mobiusDivisorOrientedFibre M (insert q P) R) 0)^2 ≤
        (max (mobiusDivisorOrientedFibre M P R) 0)^2 ∧
      (max (-mobiusDivisorOrientedFibre M P R) 0)^2 ≤
        (max (-mobiusDivisorOrientedFibre M (insert q P) R) 0)^2 := by
    by_cases hqR : q ∈ R
    · have hpos : 0 ≤ mobiusDivisorOrientedFibre M P R := by
        have h := partner_nonneg hq hn hR
        simpa only [insert_eq_of_mem hqR] using h
      have hz : mobiusDivisorOrientedFibre M (insert q P) R = 0 := by
        simp [mobiusDivisorOrientedFibre, mobiusDivisorSelectionFibre_insert, hqR]
      rw [hz]
      constructor
      · simp only [max_self, zero_pow (by omega : (2:ℕ)≠0)]
        exact sq_nonneg _
      · simp [max_eq_right (neg_nonpos.mpr hpos)]
    · have hle : mobiusDivisorOrientedFibre M (insert q P) R ≤
          mobiusDivisorOrientedFibre M P R := by
        rw [mobiusDivisorOrientedFibre_insert M P R q hqR]
        linarith only [partner_nonneg hq hn hR]
      exact ⟨positive_square_mono hle, positive_square_mono (neg_le_neg hle)⟩
  constructor
  · exact sum_le_sum fun R hR => (hpair R hR).1
  · exact sum_le_sum fun R hR => (hpair R hR).2

/-- Every strict decrease of total parity-defect energy selects a prime in the negative support. -/
theorem mobiusDivisor_mem_negativeSupport_of_defect_drop
    (M : ℕ) (P : Finset ℕ) {q : ℕ} (hq : q ∈ mobiusDivisorSelectionPrimes M)
    (hdrop : mobiusDivisorParityDefectEnergy M (insert q P) < mobiusDivisorParityDefectEnergy M P) :
    q ∈ mobiusDivisorNegativeSupport M P := by
  by_contra h
  exact (not_lt_of_ge (mobiusDivisorParityEnergy_insert_outside_negativeSupport M P hq h).2) hdrop
end RHTower
