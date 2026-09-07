import GaloisForLFunctions.RHTower.RetainedPrimeStateTransport

/-!
# Exact source support and retained-field witness thresholds

Every retained label vanishes before its prime product. The full actual
energy is exactly the sum over born remaining labels, whose cardinality is
at most the positive source-prefix length. Complete directional witnesses
must reach past every retained subset product, including the full field.
This is a witness-cutoff cost and exact support restriction, not an energy
lower bound or an exhaustive-order construction.
-/

noncomputable section
open Finset
namespace RHTower

private lemma prod_le_of_subset_primeFactors {R : Finset ℕ} {d : ℕ}
    (hd : 0 < d) (hR : R ⊆ d.primeFactors) : (∏ p ∈ R, p) ≤ d := by
  exact Nat.le_of_dvd hd ((prod_dvd_prod_of_subset R d.primeFactors id hR).trans
    (Nat.prod_primeFactors_dvd d))

/-- A retained label cannot occur before its squarefree product, in any actual processed state. -/
theorem mobiusDivisorSelectionFibre_eq_zero_of_le_product
    (M : ℕ) (P R : Finset ℕ) (hM : M ≤ ∏ p ∈ R, p) :
    mobiusDivisorSelectionFibre M P R = 0 := by
  unfold mobiusDivisorSelectionFibre subsetLabelFibre
  apply sum_eq_zero
  intro d hd
  have hd' := mem_Icc.mp (mem_filter.mp hd).1
  have he : d.primeFactors \ P ≠ R := by
    intro he
    have hsub : R ⊆ d.primeFactors := he ▸ sdiff_subset
    have hprod := prod_le_of_subset_primeFactors (by omega : 0<d) hsub
    omega
  simp [he]

/-- The complete intersection profile has the same exact product birth threshold. -/
theorem retainedPrimeFieldProfile_eq_zero_of_le_product (Q : Finset Nat.Primes)
    (M : ℕ) (R : retainedPrimeFieldIndex Q) (hM : M ≤ ∏ p ∈ R.1, p) :
    retainedPrimeFieldProfile Q M R = 0 := by
  unfold retainedPrimeFieldProfile
  apply sum_eq_zero
  intro d hd
  by_cases he : d = M
  · subst d
    have hM0 := (mem_Icc.mp hd).1
    have hz : mobiusDivisorDilationChannel M M = 0 := by
      simp [mobiusDivisorDilationChannel, Icc_eq_empty_of_lt (show M-1<M by omega)]
    simp [hz]
  · have hlabel : (⟨d.primeFactors ∩ Q.image (fun p : Nat.Primes => (p : ℕ)),
        mem_powerset.mpr inter_subset_right⟩ : retainedPrimeFieldIndex Q) ≠ R := by
      intro h
      have hval := congrArg Subtype.val h
      have hsub : R.1 ⊆ d.primeFactors := hval ▸ inter_subset_left
      have hprod := prod_le_of_subset_primeFactors (by have := mem_Icc.mp hd; omega : 0<d) hsub
      have := mem_Icc.mp hd
      omega
    simp [hlabel]

/-- The actual remaining coordinate family, restricted to products that have been born. -/
def mobiusDivisorActiveLabels (M : ℕ) (P : Finset ℕ) : Finset (Finset ℕ) :=
  ((mobiusDivisorSelectionPrimes M \ P).powerset).filter (fun R => (∏ p ∈ R, p) < M)

private lemma actual_label_subset {M d : ℕ} (hd : d ∈ mobiusDivisorSelectionIndices M)
    (P : Finset ℕ) : d.primeFactors \ P ⊆ mobiusDivisorSelectionPrimes M \ P := by
  intro p hp
  obtain ⟨hp, hpP⟩ := mem_sdiff.mp hp
  have hdp := Nat.le_of_mem_primeFactors hp
  have hd' := mem_Icc.mp (mem_filter.mp hd).1
  exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by omega),
    (Nat.mem_primeFactors.mp hp).1⟩, hpP⟩

/-- Every coordinate omitted from the active family is exactly zero. -/
theorem mobiusDivisorSelectionFibre_eq_zero_of_not_active (M : ℕ) (P R : Finset ℕ)
    (hR : R ∉ mobiusDivisorActiveLabels M P) : mobiusDivisorSelectionFibre M P R = 0 := by
  by_cases hprod : (∏ p ∈ R, p) < M
  · have hsub : ¬R ⊆ mobiusDivisorSelectionPrimes M \ P := by
      intro h
      exact hR (mem_filter.mpr ⟨mem_powerset.mpr h, hprod⟩)
    unfold mobiusDivisorSelectionFibre subsetLabelFibre
    apply sum_eq_zero
    intro d hd
    have he : d.primeFactors \ P ≠ R := fun he => hsub (he ▸ actual_label_subset hd P)
    simp [he]
  · exact mobiusDivisorSelectionFibre_eq_zero_of_le_product M P R (by omega)

/-- The full actual energy is carried by the born remaining coordinates, with no remainder. -/
theorem mobiusDivisorSelectionEnergy_eq_sum_active (M : ℕ) (P : Finset ℕ) :
    mobiusDivisorSelectionEnergy M P =
      ∑ R ∈ mobiusDivisorActiveLabels M P, (mobiusDivisorSelectionFibre M P R)^2 := by
  change (∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset,
    (mobiusDivisorSelectionFibre M P R)^2) = _
  symm
  apply sum_subset
  · intro R hR
    exact mem_powerset.mpr ((mem_powerset.mp (mem_filter.mp hR).1).trans sdiff_subset)
  · intro R hR hn
    rw [mobiusDivisorSelectionFibre_eq_zero_of_not_active M P R hn]
    ring

/-- The number of possible actual retained coordinates is at most the positive source prefix length. -/
theorem card_mobiusDivisorActiveLabels_le (M : ℕ) (P : Finset ℕ) :
    (mobiusDivisorActiveLabels M P).card ≤ M-1 := by
  have hprime (R : Finset ℕ) (hR : R ∈ mobiusDivisorActiveLabels M P) : ∀ p ∈ R, p.Prime := by
    intro p hp
    have hpU := (mem_sdiff.mp ((mem_powerset.mp (mem_filter.mp hR).1) hp)).1
    exact (mem_filter.mp hpU).2
  have hmap : Set.MapsTo (fun R : Finset ℕ => ∏ p ∈ R, p)
      (↑(mobiusDivisorActiveLabels M P)) (↑(Icc 1 (M-1))) := by
    intro R hR
    have hpos : 0 < ∏ p ∈ R, p := prod_pos (fun p hp => (hprime R hR p hp).pos)
    have hlt := (mem_filter.mp hR).2
    change (∏ p ∈ R, p) ∈ Icc 1 (M-1)
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hinj : Set.InjOn (fun R : Finset ℕ => ∏ p ∈ R, p) (↑(mobiusDivisorActiveLabels M P)) := by
    intro R hR T hT he
    have h := congrArg Nat.primeFactors he
    simpa only [Nat.primeFactors_prod (hprime R hR), Nat.primeFactors_prod (hprime T hT)] using h
  have hc := card_le_card_of_injOn _ hmap hinj
  simpa using hc

/-- A coordinate's delta functional reads exactly its complete actual source profile. -/
lemma retainedPrimeFieldPairing_single (Q : Finset Nat.Primes)
    (R : retainedPrimeFieldIndex Q) (M : ℕ) :
    retainedPrimeFieldPairing Q (Pi.single R 1) M = retainedPrimeFieldProfile Q M R := by
  rw [retainedPrimeFieldPairing_eq_sum_profile]
  simp [Pi.single_apply]

/-- Every family detecting all nonzero directions must reach past every retained subset product. -/
theorem retainedPrimeField_witness_reaches_product (Q : Finset Nat.Primes) (K : Finset ℕ)
    (hK : ∀ z : retainedPrimeFieldCoordinates Q, z ≠ 0 →
      ∃ M ∈ K, 0 < retainedPrimeFieldPairing Q z M)
    (R : retainedPrimeFieldIndex Q) : ∃ M ∈ K, (∏ p ∈ R.1, p) < M := by
  have hz : (Pi.single R 1 : retainedPrimeFieldCoordinates Q) ≠ 0 := by
    intro he
    have h := congrFun he R
    simp at h
  obtain ⟨M, hMK, hM⟩ := hK (Pi.single R 1) hz
  rw [retainedPrimeFieldPairing_single] at hM
  refine ⟨M, hMK, ?_⟩
  by_contra hn
  rw [retainedPrimeFieldProfile_eq_zero_of_le_product Q M R (by omega)] at hM
  linarith

/-- Complete retained-field directional witnesses necessarily exceed the product of the full field. -/
theorem retainedPrimeField_product_lt_witness_sup (Q : Finset Nat.Primes) (K : Finset ℕ)
    (hK : ∀ z : retainedPrimeFieldCoordinates Q, z ≠ 0 →
      ∃ M ∈ K, 0 < retainedPrimeFieldPairing Q z M) :
    (∏ p ∈ Q.image (fun p : Nat.Primes => (p : ℕ)), p) < K.sup id := by
  obtain ⟨M, hM, hprod⟩ := retainedPrimeField_witness_reaches_product Q K hK
    ⟨Q.image (fun p : Nat.Primes => (p : ℕ)), mem_powerset.mpr Subset.rfl⟩
  exact hprod.trans_le (le_sup (f := id) hM)

end RHTower
