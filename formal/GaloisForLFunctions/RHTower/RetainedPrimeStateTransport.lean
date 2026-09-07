import GaloisForLFunctions.RHTower.RetainedPrimeFiniteSourceMargin
import GaloisForLFunctions.RHTower.MobiusDivisorPrimeFibreInterpolation

/-!
# Exact retained-field transport into prime-merger energy

Processing the complementary active primes identifies every surviving child
fibre with the complete retained-intersection profile. Coordinates outside
the retained field vanish. The full all-cutoff prime energy change is thus
the signed pairing of the actual parent field with the clipped child source.
-/

noncomputable section
open Finset
namespace RHTower

private lemma active_label_subset {M d : ℕ} (hd : d < M) :
    d.primeFactors ⊆ mobiusDivisorSelectionPrimes M := by
  intro p hp
  exact mem_filter.mpr ⟨mem_range.mpr ((Nat.le_of_mem_primeFactors hp).trans_lt hd),
    (Nat.mem_primeFactors.mp hp).1⟩

private lemma complementary_label {A S P D : Finset ℕ}
    (hD : D ⊆ A) (hcore : A \ S ⊆ P) (hdis : Disjoint P S) :
    D \ P = D ∩ S := by
  ext p
  simp only [mem_sdiff, mem_inter]
  constructor
  · rintro ⟨hp, hpP⟩
    refine ⟨hp, ?_⟩
    by_contra hpS
    exact hpP (hcore (mem_sdiff.mpr ⟨hD hp, hpS⟩))
  · rintro ⟨hp, hpS⟩
    exact ⟨hp, fun hpP => disjoint_left.mp hdis hpP hpS⟩

/-- Complementary active-prime processing gives the complete retained source profile. -/
theorem mobiusDivisorSelectionFibre_eq_retainedProfile
    (Q : Finset Nat.Primes) (M : ℕ) (P : Finset ℕ)
    (hcore : mobiusDivisorSelectionPrimes M \ Q.image (fun p : Nat.Primes => (p : ℕ)) ⊆ P)
    (hdis : Disjoint P (Q.image (fun p : Nat.Primes => (p : ℕ))))
    (R : retainedPrimeFieldIndex Q) :
    mobiusDivisorSelectionFibre M P R.1 = retainedPrimeFieldProfile Q M R := by
  rw [mobiusDivisorSelectionFibre_eq_sum_Icc]
  unfold retainedPrimeFieldProfile
  apply sum_congr rfl
  intro d hd
  by_cases he : d = M
  · subst d
    have hM : 0 < M := (mem_Icc.mp hd).1
    have hz : mobiusDivisorDilationChannel M M = 0 := by
      simp [mobiusDivisorDilationChannel, Icc_eq_empty_of_lt (show M-1<M by omega)]
    simp [hz]
  · have hlabel := complementary_label (active_label_subset (by have := mem_Icc.mp hd; omega : d<M)) hcore hdis
    rw [hlabel]
    congr 1
    apply propext
    constructor
    · intro heq
      exact Subtype.ext heq
    · intro heq
      exact congrArg Subtype.val heq

/-- No retained coordinate outside the prescribed field survives a complementary active core. -/
theorem mobiusDivisorSelectionFibre_eq_zero_of_not_subset_retained
    (M : ℕ) (P S R : Finset ℕ) (hcore : mobiusDivisorSelectionPrimes M \ S ⊆ P)
    (hR : ¬ R ⊆ S) : mobiusDivisorSelectionFibre M P R = 0 := by
  unfold mobiusDivisorSelectionFibre subsetLabelFibre
  apply sum_eq_zero
  intro d hd
  have hD : d.primeFactors ⊆ mobiusDivisorSelectionPrimes M :=
    active_label_subset (by have := mem_Icc.mp (mem_filter.mp hd).1; omega)
  have hsub : d.primeFactors \ P ⊆ S := by
    intro p hp
    obtain ⟨hp, hpP⟩ := mem_sdiff.mp hp
    by_contra hpS
    exact hpP (hcore (mem_sdiff.mpr ⟨hD hp, hpS⟩))
  have hne : d.primeFactors \ P ≠ R := fun he => hR (he ▸ hsub)
  simp [hne]

/-- The complete actual parent field restricted to the retained subset coordinates. -/
def retainedPrimeParentField (Q : Finset Nat.Primes) (M : ℕ) (P : Finset ℕ) :
    retainedPrimeFieldCoordinates Q := fun R => mobiusDivisorSelectionFibre M P R.1

/-- The literal adjacent-cutoff profile at the physical clipping coefficient. -/
def retainedPrimeClippedProfile (Q : Finset Nat.Primes) (K : ℕ) (w : ℝ) :
    retainedPrimeFieldCoordinates Q :=
  (1-w) • retainedPrimeFieldProfile Q K + w • retainedPrimeFieldProfile Q (K+1)

private lemma selectionPrimes_mono {N M : ℕ} (h : N ≤ M) :
    mobiusDivisorSelectionPrimes N ⊆ mobiusDivisorSelectionPrimes M := by
  intro p hp
  obtain ⟨hp, hprime⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp hp).trans_le h), hprime⟩

/-- Exact transport of both adjacent child fibres, using the same prepared state. -/
theorem mobiusDivisorInterpolatedFibre_eq_retainedProfile
    (Q : Finset Nat.Primes) (M p : ℕ) (P : Finset ℕ)
    (hcore : mobiusDivisorSelectionPrimes (M/p+1) \ Q.image (fun q : Nat.Primes => (q : ℕ)) ⊆ P)
    (hdis : Disjoint P (Q.image (fun q : Nat.Primes => (q : ℕ))))
    (R : retainedPrimeFieldIndex Q) :
    mobiusDivisorInterpolatedFibre M p P R.1 =
      retainedPrimeClippedProfile Q (M/p) (divisorPrimeClipWeight M p) R := by
  have hsmall : mobiusDivisorSelectionPrimes (M/p) \ Q.image (fun q : Nat.Primes => (q : ℕ)) ⊆ P := by
    intro q hq
    obtain ⟨hq, hqS⟩ := mem_sdiff.mp hq
    exact hcore (mem_sdiff.mpr ⟨selectionPrimes_mono (Nat.le_succ _) hq, hqS⟩)
  unfold mobiusDivisorInterpolatedFibre retainedPrimeClippedProfile
  rw [mobiusDivisorSelectionFibre_eq_retainedProfile Q (M/p) P hsmall hdis R,
    mobiusDivisorSelectionFibre_eq_retainedProfile Q (M/p+1) P hcore hdis R]
  rfl

/-- Clipped coordinate pairing is the same clipping of the two literal source pairings. -/
lemma retainedPrimeClippedProfile_pairing (Q : Finset Nat.Primes)
    (z : retainedPrimeFieldCoordinates Q) (K : ℕ) (w : ℝ) :
    (∑ R : retainedPrimeFieldIndex Q, z R * retainedPrimeClippedProfile Q K w R) =
      (1-w) * retainedPrimeFieldPairing Q z K + w * retainedPrimeFieldPairing Q z (K+1) := by
  rw [retainedPrimeFieldPairing_eq_sum_profile, retainedPrimeFieldPairing_eq_sum_profile]
  simp only [retainedPrimeClippedProfile, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro R hR <;> ring

/-- Complete prime-merger energy is exactly the retained parent/child pairing.
All other coordinates have zero child source and make no contribution. -/
theorem mobiusDivisorSelectionEnergy_insert_retainedProfile
    (Q : Finset Nat.Primes) (M : ℕ) (P : Finset ℕ) {p : ℕ}
    (hp : p.Prime) (hpM : p < M) (hpP : p ∉ P)
    (hpQ : p ∉ Q.image (fun q : Nat.Primes => (q : ℕ)))
    (hQM : Q.image (fun q : Nat.Primes => (q : ℕ)) ⊆ mobiusDivisorSelectionPrimes M)
    (hcore : mobiusDivisorSelectionPrimes (M/p+1) \ Q.image (fun q : Nat.Primes => (q : ℕ)) ⊆ P)
    (hdis : Disjoint P (Q.image (fun q : Nat.Primes => (q : ℕ)))) :
    mobiusDivisorSelectionEnergy M (insert p P) - mobiusDivisorSelectionEnergy M P =
      (-2 * Real.sqrt p) * ∑ R : retainedPrimeFieldIndex Q,
        retainedPrimeParentField Q M P R *
          retainedPrimeClippedProfile Q (M/p) (divisorPrimeClipWeight M p) R := by
  rw [mobiusDivisorSelectionEnergy_insert_interpolation hp M P hpM hpP]
  congr 1
  let S := Q.image (fun q : Nat.Primes => (q : ℕ))
  have hsub : S.powerset ⊆ ((mobiusDivisorSelectionPrimes M).erase p).powerset := by
    intro R hR
    apply mem_powerset.mpr
    intro q hq
    have hqS := (mem_powerset.mp hR) hq
    exact mem_erase.mpr ⟨by intro he; subst q; exact hpQ hqS, hQM hqS⟩
  have hsmall : mobiusDivisorSelectionPrimes (M/p) \ S ⊆ P := by
    intro q hq
    obtain ⟨hq, hqS⟩ := mem_sdiff.mp hq
    exact hcore (mem_sdiff.mpr ⟨selectionPrimes_mono (Nat.le_succ _) hq, hqS⟩)
  have he := sum_subset hsub (f := fun R => mobiusDivisorSelectionFibre M P R *
      mobiusDivisorInterpolatedFibre M p P R) (by
    intro R hR hn
    have hnot : ¬ R ⊆ S := fun h => hn (mem_powerset.mpr h)
    unfold mobiusDivisorInterpolatedFibre
    rw [mobiusDivisorSelectionFibre_eq_zero_of_not_subset_retained (M/p) P S R hsmall hnot,
      mobiusDivisorSelectionFibre_eq_zero_of_not_subset_retained (M/p+1) P S R hcore hnot]
    ring)
  rw [← he, ← sum_coe_sort S.powerset]
  apply sum_congr rfl
  intro R hR
  rw [mobiusDivisorInterpolatedFibre_eq_retainedProfile Q M p P hcore hdis R]
  rfl

end RHTower
