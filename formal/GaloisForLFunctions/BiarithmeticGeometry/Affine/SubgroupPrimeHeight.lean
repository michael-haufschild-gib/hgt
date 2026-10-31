import GaloisForLFunctions.HTGeometry.RationalDenominatorLadder

/-!
# Prime heights of rational subgroups containing one

Reciprocals of coprime denominators generate their product reciprocal. Prime-power
factorization therefore detects every proper additive subgroup of the rationals.
For a subgroup containing one, a first missing prime-power reciprocal bounds the
prime exponent in every member's reduced denominator.
-/

open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Integer multiplication passes from a denominator reciprocal to every positive divisor. -/
theorem reciprocal_mem_of_dvd (H : AddSubgroup ℚ) {d e : ℕ}
    (hd : 0 < d) (he : 0 < e) (hde : d ∣ e) (hmem : (1 : ℚ) / (e : ℚ) ∈ H) :
    (1 : ℚ) / (d : ℚ) ∈ H := by
  obtain ⟨m, rfl⟩ := hde
  have hm : m ≠ 0 := by
    intro hm
    rw [hm, mul_zero] at he
    exact (Nat.lt_irrefl 0) he
  have hdQ : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hmQ : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hmul : (m : ℚ) * (1 / ((d * m : ℕ) : ℚ)) = 1 / (d : ℚ) := by
    rw [Nat.cast_mul]
    field_simp [hdQ, hmQ]
  simpa only [nsmul_eq_mul, hmul] using H.nsmul_mem hmem m

/-- All prime-power reciprocals generate the full additive group of rational numbers. -/
theorem rational_subgroup_eq_top_iff_prime_power_reciprocals (H : AddSubgroup ℚ) :
    H = ⊤ ↔ ∀ p : ℕ, p.Prime → ∀ n : ℕ, (1 : ℚ) / ((p ^ n : ℕ) : ℚ) ∈ H := by
  constructor
  · rintro rfl p hp n
    exact AddSubgroup.mem_top _
  · intro hprime
    have hall : ∀ n : ℕ, (1 : ℚ) / (n : ℚ) ∈ H := by
      apply Nat.recOnPrimeCoprime
        (motive := fun n => (1 : ℚ) / (n : ℚ) ∈ H)
      · simpa only [Nat.cast_zero, div_zero] using H.zero_mem
      · intro p n hp
        exact hprime p hp n
      · intro a b ha hb hab hA hB
        have hlcm : Nat.lcm a b = a * b := by
          have h := Nat.gcd_mul_lcm a b
          rwa [hab.gcd_eq_one, one_mul] at h
        simpa only [hlcm] using
          one_div_lcm_mem H (Nat.zero_lt_of_lt ha) (Nat.zero_lt_of_lt hb) hA hB
    apply top_unique
    intro q _
    have h : (q.num : ℚ) * (1 / (q.den : ℚ)) ∈ H := by
      simpa only [zsmul_eq_mul] using H.zsmul_mem (hall q.den) q.num
    rwa [mul_one_div, Rat.num_div_den] at h

/-- A proper subgroup containing one has a finite prime height, bounding all member denominators. -/
theorem exists_finite_prime_height (H : AddSubgroup ℚ) (h1 : (1 : ℚ) ∈ H)
    (hproper : H ≠ ⊤) :
    ∃ p h : ℕ, p.Prime ∧ (1 : ℚ) / ((p ^ h : ℕ) : ℚ) ∈ H ∧
      (1 : ℚ) / ((p ^ (h + 1) : ℕ) : ℚ) ∉ H ∧
      ∀ q : ℚ, q ∈ H → ¬p ^ (h + 1) ∣ q.den := by
  classical
  have hmiss : ∃ p : ℕ, p.Prime ∧ ∃ n : ℕ, (1 : ℚ) / ((p ^ n : ℕ) : ℚ) ∉ H := by
    by_contra h
    push Not at h
    exact hproper ((rational_subgroup_eq_top_iff_prime_power_reciprocals H).mpr h)
  obtain ⟨p, hp, hex⟩ := hmiss
  let e := Nat.find hex
  have heMissing : (1 : ℚ) / ((p ^ e : ℕ) : ℚ) ∉ H := Nat.find_spec hex
  have hepos : 0 < e := by
    by_contra h
    have hezero : e = 0 := Nat.eq_zero_of_not_pos h
    rw [hezero, pow_zero, Nat.cast_one, div_one] at heMissing
    exact heMissing h1
  have hprior : (1 : ℚ) / ((p ^ (e - 1) : ℕ) : ℚ) ∈ H := by
    by_contra h
    exact Nat.find_min hex (show e - 1 < e by omega) h
  have heq : e - 1 + 1 = e := by omega
  refine ⟨p, e - 1, hp, hprior, ?_, ?_⟩
  · simpa only [heq] using heMissing
  · intro q hq hdiv
    apply heMissing
    exact reciprocal_mem_of_dvd H (pow_pos hp.pos e) q.den_pos
      (by simpa only [heq] using hdiv) (one_div_den_mem H h1 hq)

#print axioms rational_subgroup_eq_top_iff_prime_power_reciprocals
#print axioms exists_finite_prime_height
end GaloisForLFunctions.BiarithmeticGeometry
