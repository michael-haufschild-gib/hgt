import GaloisForLFunctions.SelbergClass.PositiveFiniteEulerProduct

/-!
# A finite logarithmic sign obstruction to reciprocal quadratic factors

Every real reciprocal quadratic modification of zeta has a negative Euler
logarithmic coefficient at one of the first four even powers of its prime.
Newton identities reduce the obstruction to two real polynomial inequalities.
-/

noncomputable section
open Complex

namespace GaloisForLFunctions.SelbergClass.PositiveFiniteEuler

/-- The first four even power sums of a reciprocal pair cannot all be at most one. -/
private theorem reciprocal_even_power_test {q x : ℝ} (hq : 4 ≤ q) :
    1 < x ∨ 1 < x ^ 2 - 2 * q ∨ 1 < x ^ 3 - 3 * q * x ∨
      1 < (x ^ 2 - 2 * q) ^ 2 - 2 * q ^ 2 := by
  by_cases h1 : 1 < x
  · exact Or.inl h1
  have hx : x ≤ 1 := le_of_not_gt h1
  by_cases h2 : 1 < x ^ 2 - 2 * q
  · exact Or.inr (Or.inl h2)
  have hx2 : x ^ 2 ≤ 2 * q + 1 := by linarith only [le_of_not_gt h2]
  by_cases hn : x ≤ -1
  · have hy : 1 ≤ -x := by linarith only [hn]
    have hf : q - 1 ≤ 3 * q - x ^ 2 := by linarith only [hx2]
    have hfp : 0 ≤ 3 * q - x ^ 2 := by linarith only [hf, hq]
    have hm : q - 1 ≤ (-x) * (3 * q - x ^ 2) :=
      hf.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hy hfp)
    exact Or.inr (Or.inr (Or.inl (by nlinarith only [hm, hq])))
  · have hxlo : -1 < x := lt_of_not_ge hn
    have hsq : x ^ 2 ≤ 1 := by
      nlinarith only [mul_nonneg
        (show 0 ≤ x + 1 by linarith only [hxlo])
        (show 0 ≤ 1 - x by linarith only [hx])]
    have hbase : 0 ≤ 2 * q - 1 := by linarith only [hq]
    have hbig : 2 * q - 1 ≤ 2 * q - x ^ 2 := by linarith only [hsq]
    have hpows := pow_le_pow_left₀ hbase hbig 2
    have hqq : 0 < q * (q - 2) := mul_pos
      (by linarith only [hq]) (by linarith only [hq])
    exact Or.inr (Or.inr (Or.inr (by nlinarith only [hpows, hqq])))

/-- Four even prime powers detect a negative logarithmic count for every real
reciprocal quadratic, including those whose roots lie on the critical circle. -/
theorem exists_negative_even_eulerLogCoeff {p : ℕ} (hp : p.Prime) {A : ℝ} {α β : ℂ}
    (hadd : α + β = -(A : ℂ)) (hmul : α * β = p) :
    ∃ k ∈ ({2, 4, 6, 8} : Finset ℕ), (eulerLogCoeff p α β (p ^ k)).re < 0 := by
  let q : ℝ := (p : ℝ) ^ 2
  let x : ℝ := A ^ 2 - 2 * p
  have hq : 4 ≤ q := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    dsimp only [q]
    nlinarith only [hp2]
  have h2 : α ^ 2 + β ^ 2 = (x : ℂ) := by
    calc α ^ 2 + β ^ 2 = (α + β) ^ 2 - 2 * (α * β) := by ring
      _ = (x : ℂ) := by rw [hadd, hmul]; dsimp only [x]; push_cast; ring
  have h4 : α ^ 4 + β ^ 4 = ((x ^ 2 - 2 * q : ℝ) : ℂ) := by
    calc α ^ 4 + β ^ 4 = (α ^ 2 + β ^ 2) ^ 2 - 2 * (α * β) ^ 2 := by ring
      _ = _ := by rw [h2, hmul]; dsimp only [q]; push_cast; ring
  have h6 : α ^ 6 + β ^ 6 = ((x ^ 3 - 3 * q * x : ℝ) : ℂ) := by
    calc α ^ 6 + β ^ 6 =
        (α ^ 2 + β ^ 2) ^ 3 - 3 * (α * β) ^ 2 * (α ^ 2 + β ^ 2) := by ring
      _ = _ := by rw [h2, hmul]; dsimp only [q]; push_cast; ring
  have h8 : α ^ 8 + β ^ 8 = (((x ^ 2 - 2 * q) ^ 2 - 2 * q ^ 2 : ℝ) : ℂ) := by
    calc α ^ 8 + β ^ 8 = (α ^ 4 + β ^ 4) ^ 2 - 2 * (α * β) ^ 4 := by ring
      _ = _ := by rw [h4, hmul]; dsimp only [q]; push_cast; ring
  have hcoeff (k : ℕ) (hk : k ≠ 0) (S : ℝ)
      (hS : α ^ k + β ^ k = (S : ℂ)) (hlarge : 1 < S) :
      (eulerLogCoeff p α β (p ^ k)).re < 0 := by
    rw [eulerLogCoeff_prime_pow hp α β hk]
    have he : (1 - α ^ k - β ^ k) / (k : ℂ) = (((1 - S) / k : ℝ) : ℂ) := by
      calc _ = (1 - (α ^ k + β ^ k)) / (k : ℂ) := by ring
        _ = _ := by rw [hS]; push_cast; ring
    rw [he, Complex.ofReal_re]
    exact div_neg_of_neg_of_pos (sub_neg.mpr hlarge)
      (by exact_mod_cast Nat.pos_of_ne_zero hk)
  rcases reciprocal_even_power_test (x := x) hq with h | h | h | h
  · exact ⟨2, by simp, hcoeff 2 (by norm_num) x h2 h⟩
  · exact ⟨4, by simp, hcoeff 4 (by norm_num) _ h4 h⟩
  · exact ⟨6, by simp, hcoeff 6 (by norm_num) _ h6 h⟩
  · exact ⟨8, by simp, hcoeff 8 (by norm_num) _ h8 h⟩

end GaloisForLFunctions.SelbergClass.PositiveFiniteEuler
