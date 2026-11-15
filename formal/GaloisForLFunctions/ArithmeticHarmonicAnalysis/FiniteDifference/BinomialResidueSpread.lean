import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteDifference.PolynomialResidueSpread

/-!
# Binomial phases in short residue intervals

Integer-valued polynomial sequences are naturally expressed in the
binomial basis. Finite differences recover their integer coefficients,
so a constant residue sequence is equivalent to divisibility of every
positive-degree coefficient. Short interval rigidity therefore gives
an explicit coefficient criterion for confinement.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Function Finset

/-- The integer-valued polynomial with prescribed binomial coefficients. -/
def binomialSequence (d : ℕ) (a : ℕ → ℤ) (j : ℕ) : ℤ :=
  ∑ i ∈ range (d + 1), a i * (j.choose i : ℤ)

private theorem binomialSequence_eq_sum (d : ℕ) (a : ℕ → ℤ) :
    binomialSequence d a = ∑ i ∈ range (d + 1), a i • (fun j : ℕ => (j.choose i : ℤ)) := by
  funext j
  simp only [binomialSequence, sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Every finite difference of the binomial expansion is the same expansion of differences. -/
theorem binomialSequence_iterated_difference (d n j : ℕ) (a : ℕ → ℤ) :
    (fwdDiff 1)^[n] (binomialSequence d a) j =
      ∑ i ∈ range (d + 1), a i * (fwdDiff 1)^[n] (fun x : ℕ => (x.choose i : ℤ)) j := by
  rw [binomialSequence_eq_sum, fwdDiff_iter_finsetSum]
  simp only [fwdDiff_iter_const_smul, sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The difference of a binomial coefficient vanishes above its index. -/
theorem iterated_difference_choose_eq_zero (i n : ℕ) (hin : i < n) :
    (fwdDiff 1)^[n] (fun j : ℕ => (j.choose i : ℤ)) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hin
  rw [show i + m + 1 = (m + 1) + i by omega, iterate_add_apply]
  have he := fwdDiff_iter_choose 0 i
  simp only [Nat.add_zero, Nat.choose_zero_right, Nat.cast_one] at he
  rw [he, iterate_succ_apply, fwdDiff_const]
  clear hin
  induction m with
  | zero => rfl
  | succ m ih => rw [iterate_succ_apply', ih]; rfl

/-- A binomial expansion of degree at most `d` has zero difference of order `d+1`. -/
theorem binomialSequence_difference_zero (d : ℕ) (a : ℕ → ℤ) :
    (fwdDiff 1)^[d + 1] (binomialSequence d a) = 0 := by
  funext j
  rw [binomialSequence_iterated_difference]
  apply sum_eq_zero
  intro i hi
  rw [iterated_difference_choose_eq_zero i (d + 1) (mem_range.mp hi)]
  exact mul_zero _

/-- The difference at zero recovers the corresponding binomial coefficient. -/
theorem binomialSequence_difference_at_zero (d n : ℕ) (a : ℕ → ℤ) :
    (fwdDiff 1)^[n] (binomialSequence d a) 0 = if n ≤ d then a n else 0 := by
  rw [binomialSequence_iterated_difference]
  simp only [fwdDiff_iter_choose_zero, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq]
  simp only [mem_range, Nat.lt_succ_iff]

/-- Evaluation at zero is the constant binomial coefficient. -/
theorem binomialSequence_zero (d : ℕ) (a : ℕ → ℤ) : binomialSequence d a 0 = a 0 := by
  have he := binomialSequence_difference_at_zero d 0 a
  simpa only [iterate_zero, id_eq, Nat.zero_le, if_true] using he

/-- Constant residues are equivalent to divisibility of every positive binomial coefficient. -/
theorem binomialSequence_constant_mod_iff (d : ℕ) (a : ℕ → ℤ) (k : ℤ) :
    (∀ j, binomialSequence d a j ≡ a 0 [ZMOD k]) ↔
      ∀ i, 1 ≤ i → i ≤ d → k ∣ a i := by
  constructor
  · intro hc i hi hid
    have he := iterated_difference_modEq (binomialSequence d a) (fun _ => a 0) k hc i 0
    rw [binomialSequence_difference_at_zero, if_pos hid] at he
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    have hz : (fwdDiff (1 : ℕ))^[m + 1] (fun _ => a 0) = 0 := by
      rw [iterate_succ_apply, fwdDiff_const]
      clear he hi hid
      induction m with
      | zero => rfl
      | succ m ih => rw [iterate_succ_apply', ih]; rfl
    rw [hz] at he
    simpa only [Pi.zero_apply, sub_zero] using Int.modEq_iff_dvd.mp he.symm
  · intro hd j
    rw [binomialSequence, sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.cast_one, mul_one]
    have hs : k ∣ ∑ i ∈ range d, a (i + 1) * (j.choose (i + 1) : ℤ) := by
      apply Finset.dvd_sum
      intro i hi
      exact dvd_mul_of_dvd_left (hd (i + 1) (by omega) (by have := mem_range.mp hi; omega)) _
    apply Int.modEq_iff_dvd.mpr
    rw [show a 0 - ((∑ i ∈ range d, a (i + 1) * (j.choose (i + 1) : ℤ)) + a 0) =
      -(∑ i ∈ range d, a (i + 1) * (j.choose (i + 1) : ℤ)) by ring]
    exact dvd_neg.mpr hs

/-- Confinement to a short interval detects exactly the divisible positive coefficients. -/
theorem binomialSequence_short_residues_iff (d : ℕ) (a : ℕ → ℤ) (D k : ℤ)
    (hk : 0 < k) (hsize : 2 ^ d * D < k) :
    (∀ j, binomialSequence d a j % k ≤ D) ↔
      a 0 % k ≤ D ∧ ∀ i, 1 ≤ i → i ≤ d → k ∣ a i := by
  constructor
  · intro hb
    have hc := short_residue_sequence_constant (binomialSequence d a) d D k hk hsize
      (binomialSequence_difference_zero d a) hb
    rw [binomialSequence_zero] at hc
    refine ⟨by simpa only [binomialSequence_zero] using hb 0, ?_⟩
    exact (binomialSequence_constant_mod_iff d a k).mp hc
  · rintro ⟨h0, hd⟩ j
    have hc := (binomialSequence_constant_mod_iff d a k).mpr hd j
    rw [hc.eq]
    exact h0

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.binomialSequence_iterated_difference
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.iterated_difference_choose_eq_zero
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.binomialSequence_difference_zero
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.binomialSequence_difference_at_zero
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.binomialSequence_zero
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.binomialSequence_constant_mod_iff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.binomialSequence_short_residues_iff
