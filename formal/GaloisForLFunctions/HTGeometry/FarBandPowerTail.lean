import GaloisForLFunctions.HTGeometry.IntegerPowerSeriesBounds
import GaloisForLFunctions.HTGeometry.NearDiagonalHarmonicTail

/-!
# The far-band ratio weight at a general power

On the frequency lattice the weight

`c · I / ((1 + |j|)^s · |I + j|)`,

restricted to the far band `I < 2|j|`, tends to zero as `I → ∞`, for every real `s > 1`.  The two
regimes are separated by comparing `|j|` with `2|I + j|`:

* if `|j| ≤ 2|I + j|` the weight is `O(1/(1 + |j|)^s)` on a band escaping to infinity;
* otherwise `|I + j| < I` and `1 + |j| > I/2`, so the weight is `O(1/(I^(s-1)·|I + j|))`, a
  near-diagonal harmonic band at height `I^(1-s)`.

Both regimes vanish, by `tendsto_tsum_far_of_ne_top` and `tendsto_tsum_nearDiagonalWeighted_zero`.
The quadratic case `s = 2` is the one the unweighted moving-translation estimate uses; exponents
below `2` are what the same estimate needs once the amplitudes have been convolved.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions

/-- `(1 + log I)/I^t → 0` for every positive power. -/
theorem tendsto_one_add_log_div_rpow_atTop_zero {t : ℝ} (ht : 0 < t) :
    Tendsto (fun I : ℕ => (1 + Real.log (I : ℝ)) / (I : ℝ) ^ t) atTop (nhds 0) := by
  have hpow : Tendsto (fun I : ℕ => (I : ℝ) ^ t) atTop atTop :=
    (tendsto_rpow_atTop ht).comp tendsto_natCast_atTop_atTop
  have hone : Tendsto (fun I : ℕ => 1 / (I : ℝ) ^ t) atTop (nhds 0) := by
    simpa [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hpow
  have hlog : Tendsto (fun x : ℝ => Real.log x / x ^ t) atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop ht).tendsto_div_nhds_zero
  have hnat : Tendsto (fun I : ℕ => Real.log (I : ℝ) / (I : ℝ) ^ t) atTop (nhds 0) := by
    simpa [Function.comp_def] using hlog.comp tendsto_natCast_atTop_atTop
  have hsum := hone.add hnat
  rw [add_zero] at hsum
  refine hsum.congr fun I => ?_
  rw [add_div]

/-- **The far-band ratio weight vanishes at every power above one.** -/
theorem tendsto_tsum_farBandPower_zero {c s : ℝ} (hc : 0 ≤ c) (hs : 1 < s) :
    Tendsto (fun I : ℕ => ∑' j : ℤ,
      (if I < 2 * j.natAbs ∧ ((I : ℤ) + j).natAbs ≠ 0 then
        ENNReal.ofReal (c * (I : ℝ) /
          ((1 + (j.natAbs : ℝ)) ^ s * (((I : ℤ) + j).natAbs : ℝ))) else 0))
      atTop (nhds 0) := by
  have hs0 : (0 : ℝ) < s := by linarith
  have hdom : ∀ I : ℕ, ∀ j : ℤ,
      (if I < 2 * j.natAbs ∧ ((I : ℤ) + j).natAbs ≠ 0 then
        ENNReal.ofReal (c * (I : ℝ) /
          ((1 + (j.natAbs : ℝ)) ^ s * (((I : ℤ) + j).natAbs : ℝ))) else 0)
      ≤ (if ((I / 2 : ℕ) : ℤ) < |j| then ENNReal.ofReal (8 * c) * intPowWeight s j else 0) +
        (if ((I : ℤ) + j).natAbs < I then
          ENNReal.ofReal (2 ^ s * c / ((I : ℝ) ^ (s - 1) * (((I : ℤ) + j).natAbs : ℝ)))
          else 0) := by
    intro I j
    by_cases hsupp : I < 2 * j.natAbs ∧ ((I : ℤ) + j).natAbs ≠ 0
    swap
    · rw [if_neg hsupp]
      exact zero_le
    rw [if_pos hsupp]
    obtain ⟨hIa, hn0⟩ := hsupp
    have habsR : |(j : ℝ)| = (j.natAbs : ℝ) := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    have habsZ : |j| = (j.natAbs : ℤ) := (Int.natCast_natAbs j).symm
    have ha1 : 1 ≤ j.natAbs := by omega
    have hn1 : 1 ≤ ((I : ℤ) + j).natAbs := by omega
    have haR : (1 : ℝ) ≤ (j.natAbs : ℝ) := by exact_mod_cast ha1
    have hnR : (1 : ℝ) ≤ (((I : ℤ) + j).natAbs : ℝ) := by exact_mod_cast hn1
    have hIR : (0 : ℝ) ≤ (I : ℝ) := Nat.cast_nonneg _
    have hIaR : (I : ℝ) < 2 * (j.natAbs : ℝ) := by exact_mod_cast hIa
    have hXpos : (0 : ℝ) < (1 + (j.natAbs : ℝ)) ^ s :=
      Real.rpow_pos_of_pos (by linarith) s
    have hden : (0 : ℝ) < (1 + (j.natAbs : ℝ)) ^ s * (((I : ℤ) + j).natAbs : ℝ) := by
      have : (0 : ℝ) < (((I : ℤ) + j).natAbs : ℝ) := by linarith
      exact mul_pos hXpos this
    by_cases hcase : j.natAbs ≤ 2 * ((I : ℤ) + j).natAbs
    · -- escaping band
      refine le_trans ?_ (le_add_right le_rfl)
      have hband : ((I / 2 : ℕ) : ℤ) < |j| := by
        rw [habsZ]
        omega
      rw [if_pos hband]
      have hpow : intPowWeight s j = ENNReal.ofReal (1 / (1 + (j.natAbs : ℝ)) ^ s) := by
        rw [intPowWeight, habsR]
      rw [hpow, ← ENNReal.ofReal_mul (by linarith)]
      apply ENNReal.ofReal_le_ofReal
      have hcaseR : (j.natAbs : ℝ) ≤ 2 * (((I : ℤ) + j).natAbs : ℝ) := by exact_mod_cast hcase
      rw [div_le_iff₀ hden]
      have hsimp : 8 * c * (1 / (1 + (j.natAbs : ℝ)) ^ s) *
          ((1 + (j.natAbs : ℝ)) ^ s * (((I : ℤ) + j).natAbs : ℝ))
          = 8 * c * (((I : ℤ) + j).natAbs : ℝ) := by
        field_simp
      rw [hsimp]
      nlinarith
    · -- near-diagonal band
      rw [not_le] at hcase
      have hnI : ((I : ℤ) + j).natAbs < I := by omega
      refine le_trans ?_ (le_add_left le_rfl)
      rw [if_pos hnI]
      apply ENNReal.ofReal_le_ofReal
      have hIpos : (0 : ℝ) < (I : ℝ) := by
        have : 0 < I := by omega
        exact_mod_cast this
      have hhalf : (I : ℝ) / 2 ≤ 1 + (j.natAbs : ℝ) := by linarith
      have hlow : ((I : ℝ) / 2) ^ s ≤ (1 + (j.natAbs : ℝ)) ^ s :=
        Real.rpow_le_rpow (by positivity) hhalf hs0.le
      have hsplit : ((I : ℝ) / 2) ^ s = (I : ℝ) ^ s / 2 ^ s :=
        Real.div_rpow hIR (by norm_num) s
      have hIs : (I : ℝ) ^ (s - 1) * (I : ℝ) = (I : ℝ) ^ s := by
        rw [Real.rpow_sub hIpos, Real.rpow_one]
        field_simp
      have hIspos : (0 : ℝ) < (I : ℝ) ^ (s - 1) := Real.rpow_pos_of_pos hIpos _
      have hnpos : (0 : ℝ) < (((I : ℤ) + j).natAbs : ℝ) := by linarith
      have hdenR : (0 : ℝ) < (I : ℝ) ^ (s - 1) * (((I : ℤ) + j).natAbs : ℝ) :=
        mul_pos hIspos hnpos
      rw [div_le_div_iff₀ hden hdenR]
      have hlow' : (I : ℝ) ^ s / 2 ^ s ≤ (1 + (j.natAbs : ℝ)) ^ s := by
        rw [← hsplit]; exact hlow
      have h2s : (0 : ℝ) < 2 ^ s := Real.rpow_pos_of_pos (by norm_num) s
      have hkey : c * (I : ℝ) * ((I : ℝ) ^ (s - 1) * (((I : ℤ) + j).natAbs : ℝ))
          ≤ 2 ^ s * c * ((1 + (j.natAbs : ℝ)) ^ s * (((I : ℤ) + j).natAbs : ℝ)) := by
        have hstep : c * (I : ℝ) * (I : ℝ) ^ (s - 1)
            ≤ 2 ^ s * c * (1 + (j.natAbs : ℝ)) ^ s := by
          have hIs' : (I : ℝ) * (I : ℝ) ^ (s - 1) = (I : ℝ) ^ s := by
            rw [mul_comm]; exact hIs
          have hmul : c * ((I : ℝ) ^ s / 2 ^ s) ≤ c * (1 + (j.natAbs : ℝ)) ^ s :=
            mul_le_mul_of_nonneg_left hlow' hc
          have hexp : 2 ^ s * (c * ((I : ℝ) ^ s / 2 ^ s)) = c * (I : ℝ) ^ s := by
            field_simp
          nlinarith [hmul, h2s.le, hexp]
        nlinarith [hstep, hnpos.le]
      linarith [hkey]
  have hfar : Tendsto (fun I : ℕ => ∑' j : ℤ,
      (if ((I / 2 : ℕ) : ℤ) < |j| then ENNReal.ofReal (8 * c) * intPowWeight s j else 0))
      atTop (nhds 0) := by
    have hb : Tendsto (fun I : ℕ => I / 2) atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro b
      exact ⟨2 * b, fun I hI => by omega⟩
    exact tendsto_tsum_far_of_ne_top
      (tsum_const_mul_intPowWeight_ne_top hs ENNReal.ofReal_ne_top) hb
  have hnear : Tendsto (fun I : ℕ => ∑' j : ℤ,
      (if ((I : ℤ) + j).natAbs < I then
        ENNReal.ofReal (2 ^ s * c / ((I : ℝ) ^ (s - 1) * (((I : ℤ) + j).natAbs : ℝ)))
        else 0)) atTop (nhds 0) := by
    have hbase := tendsto_tsum_nearDiagonalWeighted_zero (c := 2 ^ s * c)
      (by positivity) (w := fun I : ℕ => (I : ℝ) ^ (s - 1))
      (fun I => (Real.rpow_nonneg (Nat.cast_nonneg I) _))
      (tendsto_one_add_log_div_rpow_atTop_zero (by linarith))
    refine hbase.congr ?_
    intro I
    exact (Equiv.tsum_eq (Equiv.addLeft (I : ℤ))
      (fun n : ℤ => if n.natAbs < I then
        ENNReal.ofReal (2 ^ s * c / ((I : ℝ) ^ (s - 1) * (n.natAbs : ℝ))) else 0)).symm
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hhalf : (0 : ℝ≥0∞) < ε / 2 := ENNReal.half_pos hε.ne'
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hfar (ε / 2) hhalf,
    ENNReal.tendsto_nhds_zero.mp hnear (ε / 2) hhalf] with I h1 h2
  calc ∑' j : ℤ, (if I < 2 * j.natAbs ∧ ((I : ℤ) + j).natAbs ≠ 0 then
        ENNReal.ofReal (c * (I : ℝ) /
          ((1 + (j.natAbs : ℝ)) ^ s * (((I : ℤ) + j).natAbs : ℝ))) else 0)
      ≤ ∑' j : ℤ,
          ((if ((I / 2 : ℕ) : ℤ) < |j| then ENNReal.ofReal (8 * c) * intPowWeight s j else 0) +
            (if ((I : ℤ) + j).natAbs < I then
              ENNReal.ofReal (2 ^ s * c /
                ((I : ℝ) ^ (s - 1) * (((I : ℤ) + j).natAbs : ℝ))) else 0)) :=
        ENNReal.tsum_le_tsum (hdom I)
    _ = (∑' j : ℤ,
          (if ((I / 2 : ℕ) : ℤ) < |j| then ENNReal.ofReal (8 * c) * intPowWeight s j else 0)) +
        ∑' j : ℤ, (if ((I : ℤ) + j).natAbs < I then
          ENNReal.ofReal (2 ^ s * c /
            ((I : ℝ) ^ (s - 1) * (((I : ℤ) + j).natAbs : ℝ))) else 0) :=
        ENNReal.tsum_add
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
    _ = ε := ENNReal.add_halves ε

end GaloisForLFunctions
