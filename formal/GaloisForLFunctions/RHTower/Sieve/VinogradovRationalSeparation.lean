import GaloisForLFunctions.RHTower.Sieve.LargeSieveExplicit
import GaloisForLFunctions.RHTower.Sieve.FareySeparation
import GaloisForLFunctions.RHTower.Sieve.VinogradovRectangularKernel

namespace RHTower.Sieve

noncomputable section

/-- Reverse triangle inequality for distance to the nearest integer, with an
ordinary real perturbation on the right. -/
theorem toIntDist_le_toIntDist_add_add_abs (x y : ℝ) :
    toIntDist x ≤ toIntDist (x + y) + |y| := by
  unfold toIntDist
  calc
    |x - (round x : ℝ)| ≤ |x - (round (x + y) : ℝ)| :=
      round_le x (round (x + y))
    _ = |(x + y - (round (x + y) : ℝ)) - y| := by congr 1; ring
    _ ≤ |x + y - (round (x + y) : ℝ)| + |y| := by
      simpa using abs_sub_le (x + y - (round (x + y) : ℝ)) 0 y

theorem coprime_mul_int_sub_not_dvd
    {a q n m : ℕ} (hcop : Nat.Coprime a q)
    (hnm : n ≠ m) (hdiff : |(n : ℤ) - (m : ℤ)| < (q : ℤ)) :
    ¬ ((q : ℤ) ∣ (a : ℤ) * ((n : ℤ) - (m : ℤ))) := by
  intro hdvd
  have hcq : IsCoprime (q : ℤ) (a : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr hcop.symm
  have hqd : (q : ℤ) ∣ ((n : ℤ) - (m : ℤ)) :=
    hcq.dvd_of_dvd_mul_left hdvd
  have hzero : (n : ℤ) - (m : ℤ) = 0 :=
    Int.eq_zero_of_abs_lt_dvd hqd hdiff
  have heq : n = m := by exact_mod_cast (sub_eq_zero.mp hzero)
  exact hnm heq

/-- A reduced rational approximation separates every half-denominator block.
This is the arithmetic input needed by the existing separated large sieve. -/
theorem rationalApprox_halfBlock_separated
    {α : ℝ} {a q n m : ℕ} (hq : 0 < q) (hcop : Nat.Coprime a q)
    (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ (2 : ℕ))
    (hnm : n ≠ m)
    (hdiff : |(n : ℝ) - (m : ℝ)| ≤ (q : ℝ) / 2) :
    1 / (2 * (q : ℝ)) ≤ toIntDist (α * (n : ℝ) - α * (m : ℝ)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hdiffInt : |(n : ℤ) - (m : ℤ)| < (q : ℤ) := by
    have hhalf : (q : ℝ) / 2 < q := by linarith
    have hreal : |(n : ℝ) - (m : ℝ)| < (q : ℝ) := hdiff.trans_lt hhalf
    exact_mod_cast hreal
  have hnot := coprime_mul_int_sub_not_dvd hcop hnm hdiffInt
  have hrat0 := one_div_le_toIntDist_of_not_dvd hq hnot
  have hrat :
      1 / (q : ℝ) ≤
        toIntDist (((a : ℝ) / (q : ℝ)) * ((n : ℝ) - (m : ℝ))) := by
    convert hrat0 using 1
    push_cast
    field_simp
  let ε : ℝ := α - (a : ℝ) / (q : ℝ)
  let d : ℝ := (n : ℝ) - (m : ℝ)
  have herr : |ε * d| ≤ 1 / (2 * (q : ℝ)) := by
    rw [abs_mul]
    calc
      |ε| * |d| ≤ (1 / (q : ℝ) ^ (2 : ℕ)) * ((q : ℝ) / 2) := by
        exact mul_le_mul happrox hdiff (abs_nonneg _) (by positivity)
      _ = 1 / (2 * (q : ℝ)) := by field_simp
  have htriangle := toIntDist_le_toIntDist_add_add_abs
    (((a : ℝ) / (q : ℝ)) * d) (ε * d)
  have hsum : ((a : ℝ) / (q : ℝ)) * d + ε * d =
      α * (n : ℝ) - α * (m : ℝ) := by
    simp only [ε, d]
    ring
  rw [hsum] at htriangle
  have hone : 1 / (q : ℝ) = 2 * (1 / (2 * (q : ℝ))) := by field_simp
  linarith

end

end RHTower.Sieve
