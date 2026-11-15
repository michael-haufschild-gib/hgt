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

end GaloisForLFunctions.SelbergClass.PositiveFiniteEuler
