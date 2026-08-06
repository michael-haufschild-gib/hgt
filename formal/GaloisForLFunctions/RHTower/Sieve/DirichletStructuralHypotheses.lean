import GaloisForLFunctions.RHTower.Sieve.DirichletTargetEps

/-!
# Discharging the structural hypotheses

Two of the three structural hypotheses of the assembled bound are consequences of `t` being large:
the split exponent is at least one as soon as `t` exceeds `2π·2^K`, and it stays below the top of
the range as soon as `t` exceeds `16π`.

The second is the only place where the two exponent choices have to be compared.  The split point is
largest at `K = 2`, where it is `3(log(t/2π) - 2 log 2)/(2 log 2)`, while the top of the range is
`3 log(t/8π)/log 2` up to one; the comparison reduces to `t ≥ 2π·2^(8/3)`, for which `16π`
suffices.
-/

namespace RHTower.Sieve

open Finset

/-- The split exponent is positive once `t` exceeds `2π · 2^K`. -/
theorem one_le_splitExponent {t : ℝ} {K : ℕ} (hK : 2 ≤ K)
    (hbig : 2 * Real.pi * (2 : ℝ) ^ (K : ℕ) < t) :
    1 ≤ splitExponent t K := by
  have hπ := Real.pi_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hden : (0 : ℝ) < ((K : ℝ) - 4 / 3) * Real.log 2 := by
    have : (0 : ℝ) < (K : ℝ) - 4 / 3 := by linarith
    positivity
  have hquot : (2 : ℝ) ^ (K : ℕ) < t / (2 * Real.pi) := by
    rw [lt_div_iff₀ h2π]
    linarith
  have hnum : 0 < Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2 := by
    have hlt : Real.log ((2 : ℝ) ^ (K : ℕ)) < Real.log (t / (2 * Real.pi)) :=
      Real.log_lt_log (by positivity) hquot
    rw [Real.log_pow] at hlt
    linarith
  rw [splitExponent, Nat.one_le_ceil_iff]
  positivity

/-- The split point stays strictly below the top of the range once `t ≥ 16π`. -/
theorem splitExponent_sub_one_lt_topExponent {t : ℝ} {K : ℕ} (hK : 2 ≤ K)
    (ht16 : 16 * Real.pi ≤ t) (hbig : 2 * Real.pi * (2 : ℝ) ^ (K : ℕ) ≤ t)
    (hσ1 : 1 ≤ splitExponent t K) :
    splitExponent t K - 1 < topExponent t := by
  have hπ := Real.pi_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have ht : 0 < t := lt_of_lt_of_le (by positivity) ht16
  set L : ℝ := Real.log (t / (2 * Real.pi)) with hLdef
  -- `log (t / 8π) = L - 2 log 2`
  have hsplit : Real.log (t / (8 * Real.pi)) = L - 2 * Real.log 2 := by
    have hval : t / (8 * Real.pi) = (t / (2 * Real.pi)) / 4 := by
      field_simp
      ring
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast
      ring
    rw [hval, Real.log_div (by positivity) (by norm_num), hlog4, hLdef]
  -- `L ≥ 3 log 2`
  have hL3 : 3 * Real.log 2 ≤ L := by
    have h8 : (8 : ℝ) ≤ t / (2 * Real.pi) := by
      rw [le_div_iff₀ h2π]
      linarith
    have hlog8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
      push_cast
      ring
    have := Real.log_le_log (by norm_num) h8
    rwa [hlog8] at this
  have hLpos : 0 < L := by linarith
  -- the balance point, bounded using `K ≥ 2`
  have hden : (0 : ℝ) < ((K : ℝ) - 4 / 3) * Real.log 2 := by
    have : (0 : ℝ) < (K : ℝ) - 4 / 3 := by linarith
    positivity
  have hnum : 0 ≤ L - (K : ℝ) * Real.log 2 := by
    have hquot : (2 : ℝ) ^ (K : ℕ) ≤ t / (2 * Real.pi) := by
      rw [le_div_iff₀ h2π]
      linarith
    have hle : Real.log ((2 : ℝ) ^ (K : ℕ)) ≤ L :=
      Real.log_le_log (by positivity) hquot
    rw [Real.log_pow] at hle
    linarith
  have hxle : (L - (K : ℝ) * Real.log 2) / (((K : ℝ) - 4 / 3) * Real.log 2)
      ≤ (L - 2 * Real.log 2) / ((2 / 3 : ℝ) * Real.log 2) := by
    rw [div_le_div_iff₀ hden (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ (K : ℝ) - 2)
      (by linarith : (0 : ℝ) ≤ L - 4 / 3 * Real.log 2)) hlog2.le, hlog2]
  have hσ : ((splitExponent t K : ℕ) : ℝ)
      ≤ (L - (K : ℝ) * Real.log 2) / (((K : ℝ) - 4 / 3) * Real.log 2) + 1 :=
    splitExponent_le (by positivity)
  have hfloor : 3 * Real.log (t / (8 * Real.pi)) / Real.log 2 - 1
      < ((topExponent t : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one (3 * Real.log (t / (8 * Real.pi)) / Real.log 2)
    rw [← topExponent] at this
    linarith
  have hkey : (L - 2 * Real.log 2) / ((2 / 3 : ℝ) * Real.log 2) + 1
      ≤ 3 * Real.log (t / (8 * Real.pi)) / Real.log 2 := by
    rw [hsplit, div_add' _ _ _ (by positivity), div_le_div_iff₀ (by positivity) hlog2]
    nlinarith [hlog2, hL3]
  have hcast : ((splitExponent t K - 1 : ℕ) : ℝ) = ((splitExponent t K : ℕ) : ℝ) - 1 := by
    push_cast [Nat.cast_sub hσ1]
    ring
  have hfinal : ((splitExponent t K - 1 : ℕ) : ℝ) < ((topExponent t : ℕ) : ℝ) := by
    rw [hcast]
    linarith [hσ, hxle, hkey, hfloor]
  exact_mod_cast hfinal

end RHTower.Sieve
