import GaloisForLFunctions.RHTower.RetainedPrimeTopHomothety

/-!
# One coprime source head generates every retained coordinate

Every subset coordinate is a signed square-root-scaled sample of the same
coprime-to-full-field head at its own product scale. The complete prepared
energy is exactly the corresponding product-weighted sum of squares. Shared
prime masks and all clipped endpoints are retained. The head depends on the
retained field; no uniform estimate through field changes is asserted.
-/

noncomputable section
open Finset
namespace RHTower

private lemma profile_label_sum (Q : Finset Nat.Primes) (M : ℕ)
    (R : retainedPrimeFieldIndex Q) :
    retainedPrimeFieldProfile Q M R = ∑ d ∈ Icc 1 M,
      if d.primeFactors ∩ Q.image (fun p : Nat.Primes => (p : ℕ)) = R.1
      then mobiusDivisorDilationChannel M d else 0 := by
  unfold retainedPrimeFieldProfile
  apply sum_congr rfl
  intro d hd
  congr 1
  apply propext
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

/-- Every retained subset coordinate is a signed product-scale sample of the
same coprime-to-full-field source head, with its literal clipped endpoint. -/
theorem retainedPrimeFieldProfile_coordinate_interpolation
    (Q : Finset Nat.Primes) (M : ℕ) (R : retainedPrimeFieldIndex Q) :
    let r := ∏ p ∈ R.1, p
    let s := ∏ p ∈ Q.image (fun p : Nat.Primes => (p : ℕ)), p
    retainedPrimeFieldProfile Q M R =
      Real.sqrt r * ((ArithmeticFunction.moebius r : ℤ) : ℝ) *
        ((1-divisorPrimeClipWeight M r)*mobiusDivisorCoprimeHead s (M/r) +
          divisorPrimeClipWeight M r*mobiusDivisorCoprimeHead s (M/r+1)) := by
  intro r s
  let S := Q.image (fun p : Nat.Primes => (p : ℕ))
  have hS : ∀ p ∈ S, p.Prime := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    exact q.property
  have hR : R.1 ⊆ S := mem_powerset.mp R.2
  have hr : 0 < r := prod_pos (fun p hp => (hS p (hR hp)).pos)
  have hs : 0 < s := prod_pos (fun p hp => (hS p hp).pos)
  have hrfac : r.primeFactors = R.1 := Nat.primeFactors_prod (fun p hp => hS p (hR hp))
  have hsfac : s.primeFactors = S := Nat.primeFactors_prod hS
  have hrs : r ∣ s := prod_dvd_prod_of_subset R.1 S id hR
  rw [profile_label_sum]
  have hrestrict : (∑ d ∈ Icc 1 M,
      if d.primeFactors ∩ S = R.1 then mobiusDivisorDilationChannel M d else 0) =
      ∑ d ∈ (Icc 1 M).filter (fun d => r ∣ d),
        if d.primeFactors ∩ S = R.1 then mobiusDivisorDilationChannel M d else 0 := by
    rw [sum_filter]
    apply sum_congr rfl
    intro d hd
    by_cases hrd : r ∣ d
    · simp [hrd]
    · have hne : d.primeFactors ∩ S ≠ R.1 := by
        intro he
        have hsub : R.1 ⊆ d.primeFactors := he ▸ inter_subset_left
        exact hrd ((prod_dvd_prod_of_subset _ _ id hsub).trans (Nat.prod_primeFactors_dvd d))
      simp [hrd, hne]
  rw [hrestrict, sum_Icc_filter_dvd_reindex r M hr,
    mobiusDivisorCoprimeHead_succ_eq_sum]
  unfold mobiusDivisorCoprimeHead
  simp only [mul_add, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := by have := mem_Icc.mp hd; omega
  by_cases hc : r.Coprime d
  · have hdisR : Disjoint R.1 d.primeFactors := by
      simpa only [hrfac] using hc.disjoint_primeFactors
    have heq : (r*d).primeFactors ∩ S = R.1 ↔ s.Coprime d := by
      rw [Nat.primeFactors_mul hr.ne' hd0, hrfac]
      constructor
      · intro he
        apply (Nat.disjoint_primeFactors hs.ne' hd0).mp
        rw [hsfac]
        apply disjoint_left.mpr
        intro p hpS hpD
        have hpR : p ∈ R.1 := by
          rw [← he]
          exact mem_inter.mpr ⟨mem_union_right _ hpD, hpS⟩
        exact disjoint_left.mp hdisR hpR hpD
      · intro hcS
        have hdisS : Disjoint S d.primeFactors := by
          simpa only [hsfac] using hcS.disjoint_primeFactors
        apply subset_antisymm
        · intro p hp
          obtain ⟨hp, hpS⟩ := mem_inter.mp hp
          rcases mem_union.mp hp with hpR | hpD
          · exact hpR
          · exact False.elim (disjoint_left.mp hdisS hpS hpD)
        · intro p hpR
          exact mem_inter.mpr ⟨mem_union_left _ hpR, hR hpR⟩
    by_cases hcS : s.Coprime d
    · rw [if_pos (heq.mpr hcS), if_pos hcS, if_pos hcS,
        mobiusDivisorDilationChannel_interpolation_masked r M d hr, if_pos hc]
      ring
    · rw [if_neg (fun h => hcS (heq.mp h)), if_neg hcS, if_neg hcS]
      ring
  · have hcS : ¬s.Coprime d := fun h => hc (Nat.Coprime.of_dvd_left hrs h)
    have hm : ArithmeticFunction.moebius (r*d) = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree
        (fun h => hc (Nat.coprime_of_squarefree_mul h))
    have hz : mobiusDivisorDilationChannel M (r*d) = 0 := by
      simp [mobiusDivisorDilationChannel_eq_moebius_unsigned, hm]
    simp [hz, hcS]

/-- The complete prepared-state energy is a positive sum of product-weighted
samples of one common coprime head. The different subset scales remain exact. -/
theorem mobiusDivisorSelectionEnergy_eq_coprimeHead_scales
    (Q : Finset Nat.Primes) (M : ℕ) (P : Finset ℕ)
    (hQM : Q.image (fun p : Nat.Primes => (p : ℕ)) ⊆ mobiusDivisorSelectionPrimes M)
    (hcore : mobiusDivisorSelectionPrimes M \ Q.image (fun p : Nat.Primes => (p : ℕ)) ⊆ P)
    (hdis : Disjoint P (Q.image (fun p : Nat.Primes => (p : ℕ)))) :
    let s := ∏ p ∈ Q.image (fun p : Nat.Primes => (p : ℕ)), p
    mobiusDivisorSelectionEnergy M P = ∑ R : retainedPrimeFieldIndex Q,
      let r := ∏ p ∈ R.1, p
      (r:ℝ) * ((1-divisorPrimeClipWeight M r)*mobiusDivisorCoprimeHead s (M/r) +
        divisorPrimeClipWeight M r*mobiusDivisorCoprimeHead s (M/r+1))^2 := by
  intro s
  let S := Q.image (fun p : Nat.Primes => (p : ℕ))
  have hS : ∀ p ∈ S, p.Prime := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    exact q.property
  have hsub : S.powerset ⊆ (mobiusDivisorSelectionPrimes M).powerset := by
    intro R hR
    exact mem_powerset.mpr ((mem_powerset.mp hR).trans hQM)
  have he := sum_subset hsub (f := fun R => (mobiusDivisorSelectionFibre M P R)^2) (by
    intro R hR hn
    rw [mobiusDivisorSelectionFibre_eq_zero_of_not_subset_retained M P S R hcore
      (fun h => hn (mem_powerset.mpr h))]
    ring)
  change (∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset,
    (mobiusDivisorSelectionFibre M P R)^2) = _
  rw [← he, ← sum_coe_sort S.powerset]
  apply sum_congr rfl
  intro R hR
  rw [mobiusDivisorSelectionFibre_eq_retainedProfile Q M P hcore hdis R,
    retainedPrimeFieldProfile_coordinate_interpolation Q M R]
  dsimp only
  have hsq := GibbsGas.squarefree_prod_primes
    (fun p hp => hS p ((mem_powerset.mp R.2) hp))
  have hmu : (((ArithmeticFunction.moebius (∏ p ∈ R.1, p) : ℤ) : ℝ))^2 = 1 := by
    exact_mod_cast (ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq)
  rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), hmu, mul_one]

end RHTower
