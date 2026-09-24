import GaloisForLFunctions.RHTower.EstermannGeneralProgression

/-!
# The right edge of the Estermann strip is uniform in the modulus

On `Re s ≥ 2` the Estermann function is given by its absolutely convergent Dirichlet series, so

`‖D(s, a/q)‖ ≤ ∑_N d(N)/N²`,

a bound with **no dependence on the modulus `q` or the twist `a`**, because the twist is a
unimodular additive character.  This is the `q`-independent edge of the convexity argument; the
left edge `Re s = −1` is where the functional equation introduces powers of `q`, and Phragmén–
Lindelöf interpolates between them.  Isolating the right edge explicitly is the first step towards
an error term uniform in the modulus, which is what the shifted divisor correlation needs.
-/

open Complex

namespace RHTower

noncomputable section

/-- The `q`-free constant of the right edge: the second moment of the divisor function. -/
def divisorSquareMass : ℝ := ∑' N : ℕ, (N.divisors.card : ℝ) / (N : ℝ) ^ (2 : ℕ)

theorem summable_divisorSquareMass :
    Summable (fun N : ℕ => (N.divisors.card : ℝ) / (N : ℝ) ^ (2 : ℕ)) := by
  have h := summable_divisorCount_rpow (c := 2) (by norm_num)
  refine h.congr (fun N => ?_)
  rw [Real.rpow_neg (Nat.cast_nonneg N), div_eq_mul_inv]
  congr 1
  rw [← Real.rpow_natCast (N : ℝ) 2]
  norm_num

theorem divisorSquareMass_nonneg : 0 ≤ divisorSquareMass :=
  tsum_nonneg (fun N => by positivity)

/-- **The right edge is uniform in the modulus.**  For `Re s ≥ 2` the Estermann function is bounded
by the `q`-free constant `∑_N d(N)/N²`. -/
theorem norm_estermannZeta_le_divisorSquareMass (q : ℕ) [NeZero q] (a : ZMod q) {s : ℂ}
    (hs : 2 ≤ s.re) :
    ‖estermannZeta q a s‖ ≤ divisorSquareMass := by
  have hs1 : 1 < s.re := by linarith
  rw [← LSeries_estermannCoeff a hs1]
  have hterm : ∀ N : ℕ, ‖LSeries.term (estermannCoeff q a) s N‖
      ≤ (N.divisors.card : ℝ) / (N : ℝ) ^ (2 : ℕ) := by
    intro N
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero (by omega), norm_div, norm_estermannCoeff]
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have hnorm : ‖(N : ℂ) ^ s‖ = (N : ℝ) ^ s.re := by
        rw [Complex.norm_natCast_cpow_of_pos hN]
      rw [hnorm]
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      rw [← Real.rpow_natCast (N : ℝ) 2]
      rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (by omega) : 1 ≤ N) with h1 | h1
      · rw [← h1]
        norm_num
      · have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast h1
        exact Real.rpow_le_rpow_of_exponent_le hN1.le (by exact_mod_cast hs)
  have hsum : Summable (fun N : ℕ => ‖LSeries.term (estermannCoeff q a) s N‖) :=
    Summable.of_nonneg_of_le (fun N => norm_nonneg _) hterm summable_divisorSquareMass
  refine (norm_tsum_le_tsum_norm hsum).trans ?_
  exact Summable.tsum_le_tsum hterm hsum summable_divisorSquareMass

end

end RHTower
