import GaloisForLFunctions.RHTower.Sieve.GenericMarkerAnalytic
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound
import GaloisForLFunctions.RHTower.BourgainPartialSummation
import GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeDisplacement

/-!
# Complete small-gap prime-pair prefixes

The averaged pair sieve applies uniformly to every gap cutoff in the literal
prime band. Its entire divisor remainder is retained and absorbed. Finite
Abel summation gives the harmonic gap bound used by the continuous cubic kernel.
-/

noncomputable section

namespace RHTower

open Finset Filter Topology

/-- The actual prime pairs with positive gap `d`, both in the original band. -/
def chiCubicPrimeGapCount (N : ℝ) (d : ℕ) : ℝ :=
  ((primeProfileBand N).filter (fun r => r + d ∈ primeProfileBand N)).card

private theorem primeProfileBand_eq_bigPrimeSet (N : ℝ) :
    primeProfileBand N = Sieve.bigPrimeSet ⌊N⌋₊ ⌊2 * N⌋₊ := by
  rw [primeProfileBand, Sieve.bigPrimeSet, Finset.Icc_add_one_left_eq_Ioc]

/-- Every gap prefix of the actual prime band has the full two-prime logarithmic
saving. The constant and threshold are independent of the cutoff. -/
theorem exists_chiCubicPrimeGapCount_prefix_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℝ in atTop, ∀ D : ℕ,
      (∑ d ∈ Finset.Icc 1 D, chiCubicPrimeGapCount N d) ≤
        C * D * N / Real.log N ^ 2 := by
  have hC := Sieve.pairMainConst_pos
  refine ⟨8 * Sieve.pairMainConst + 1, by positivity, ?_⟩
  have hsmall : Tendsto (fun N : ℝ => 2 * (Real.log N ^ 2 / N ^ ((1 : ℝ) / 4)))
      atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ) / 4) (2 : ℕ)
      (by norm_num)).tendsto_div_nhds_zero
    have h' := h.const_mul 2
    simpa only [Real.rpow_natCast, mul_zero] using h'
  filter_upwards [eventually_ge_atTop (4 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 * Real.log 2 + 1),
    Real.tendsto_log_atTop.eventually_ge_atTop (Sieve.markerLogBase + Real.log 2),
    (tendsto_order.1 hsmall).2 1 (by norm_num)] with N hN hlog hbig hsmallN
  have hN0 : 0 < N := by linarith
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogN : 0 < Real.log N := by linarith
  have hfloor2 : 2 ≤ ⌊N⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hfloor0 : (0 : ℝ) < (⌊N⌋₊ : ℝ) := by exact_mod_cast (by omega : 0 < ⌊N⌋₊)
  have hfloor : (⌊N⌋₊ : ℝ) ≤ N := Nat.floor_le hN0.le
  have hhalf : N ≤ 2 * (⌊N⌋₊ : ℝ) := by
    have h := Nat.lt_floor_add_one N
    have htwo : (2 : ℝ) ≤ (⌊N⌋₊ : ℝ) := by exact_mod_cast hfloor2
    linarith
  have hlogfloor : Real.log N ≤ Real.log 2 + Real.log (⌊N⌋₊ : ℝ) := by
    have h := Real.log_le_log hN0 hhalf
    rwa [Real.log_mul (by norm_num) hfloor0.ne'] at h
  have hloghalf : Real.log N / 2 ≤ Real.log (⌊N⌋₊ : ℝ) := by linarith
  have hmarker : Sieve.markerLogBase ≤ Real.log (⌊N⌋₊ : ℝ) := by linarith
  have htop : (⌊2 * N⌋₊ : ℝ) ≤ 2 * N := Nat.floor_le (by positivity)
  have hrem : 2 * N ^ ((3 : ℝ) / 4) ≤ N / Real.log N ^ 2 := by
    have hquarter : 0 < N ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hN0 _
    have hsplit : N ^ ((1 : ℝ) / 4) * N ^ ((3 : ℝ) / 4) = N := by
      rw [← Real.rpow_add hN0, show (1 : ℝ) / 4 + 3 / 4 = 1 by norm_num,
        Real.rpow_one]
    have hbudget : 2 * Real.log N ^ 2 ≤ N ^ ((1 : ℝ) / 4) := by
      have h := (div_lt_one hquarter).1 (show
        2 * Real.log N ^ 2 / N ^ ((1 : ℝ) / 4) < 1 by simpa [mul_div_assoc] using hsmallN)
      exact h.le
    apply (le_div_iff₀ (sq_pos_of_pos hlogN)).2
    have h := mul_le_mul_of_nonneg_right hbudget
      (Real.rpow_nonneg hN0.le ((3 : ℝ) / 4))
    rw [hsplit] at h
    nlinarith
  intro D
  have hbase := Sieve.generic_pair_le' (b := ⌊2 * N⌋₊) (K := D) hfloor2 hmarker
  have hmain : Sieve.pairMainConst * (D : ℝ) * (⌊2 * N⌋₊ : ℝ) /
        Real.log (⌊N⌋₊ : ℝ) ^ 2 ≤
      8 * Sieve.pairMainConst * D * N / Real.log N ^ 2 := by
    calc
      _ ≤ Sieve.pairMainConst * (D : ℝ) * (2 * N) /
          Real.log (⌊N⌋₊ : ℝ) ^ 2 := by gcongr
      _ ≤ Sieve.pairMainConst * (D : ℝ) * (2 * N) / (Real.log N / 2) ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact pow_le_pow_left₀ (by positivity) hloghalf 2
      _ = _ := by field_simp; ring
  have hremfloor : 2 * (⌊N⌋₊ : ℝ) ^ ((3 : ℝ) / 4) ≤ N / Real.log N ^ 2 := by
    calc
      _ ≤ 2 * N ^ ((3 : ℝ) / 4) := by
        gcongr
      _ ≤ _ := hrem
  simp only [chiCubicPrimeGapCount, primeProfileBand_eq_bigPrimeSet] at ⊢
  refine hbase.trans ?_
  calc
    _ ≤ 8 * Sieve.pairMainConst * D * N / Real.log N ^ 2 +
        (D : ℝ) * (N / Real.log N ^ 2) :=
      add_le_add hmain (mul_le_mul_of_nonneg_left hremfloor (Nat.cast_nonneg D))
    _ = _ := by ring

private theorem sum_Icc_reciprocal_mul_eq (f : ℕ → ℝ) (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, f d / (d : ℝ)) =
      (1 / ((D : ℝ) + 1)) * (∑ d ∈ Finset.Icc 1 D, f d) +
        ∑ d ∈ Finset.Icc 1 D, (1 / (d : ℝ) - 1 / ((d : ℝ) + 1)) *
          (∑ k ∈ Finset.Icc 1 d, f k) := by
  have h := sum_Ioc_weight_mul_eq (fun d => (f d : ℂ))
    (fun d => ((1 / (d : ℝ) : ℝ) : ℂ)) (a := 0) (b := D) (Nat.zero_le D)
  have hsets : ∀ n : ℕ, Finset.Ioc 0 n = Finset.Icc 1 n := by
    intro n
    simpa using (Finset.Icc_add_one_left_eq_Ioc (0 : ℕ) n).symm
  simp only [hsets, Nat.cast_add, Nat.cast_one] at h
  apply Complex.ofReal_inj.1
  push_cast at h ⊢
  simpa [div_eq_mul_inv, mul_comm] using h

private theorem sum_Icc_div_le_of_linear_prefix (f : ℕ → ℝ) (A : ℝ)
    (hprefix : ∀ D : ℕ, (∑ d ∈ Finset.Icc 1 D, f d) ≤ A * D) (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, f d / (d : ℝ)) ≤
      A * (∑ d ∈ Finset.Icc 1 D, 1 / (d : ℝ)) := by
  have hconst : ∀ n : ℕ, (∑ _k ∈ Finset.Icc 1 n, A) = A * n := by
    intro n
    simp [Finset.sum_const, Nat.card_Icc, mul_comm]
  calc
    _ = _ := sum_Icc_reciprocal_mul_eq f D
    _ ≤ (1 / ((D : ℝ) + 1)) * (∑ _d ∈ Finset.Icc 1 D, A) +
        ∑ d ∈ Finset.Icc 1 D, (1 / (d : ℝ) - 1 / ((d : ℝ) + 1)) *
          (∑ _k ∈ Finset.Icc 1 d, A) := by
      apply add_le_add
      · rw [hconst]
        exact mul_le_mul_of_nonneg_left (hprefix D) (by positivity)
      · apply Finset.sum_le_sum
        intro d hd
        rw [hconst]
        have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (Finset.mem_Icc.1 hd).1
        exact mul_le_mul_of_nonneg_left (hprefix d)
          (sub_nonneg.2 (one_div_le_one_div_of_le hd0 (by linarith)))
    _ = ∑ d ∈ Finset.Icc 1 D, A / (d : ℝ) := (sum_Icc_reciprocal_mul_eq (fun _ => A) D).symm
    _ = _ := by rw [Finset.mul_sum]; simp only [div_eq_mul_inv, one_mul]

/-- Complete harmonic-weighted gap prefixes of the actual prime band, with one
constant and threshold valid for every cutoff. -/
theorem exists_chiCubicPrimeGapCount_harmonic_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℝ in atTop, ∀ D : ℕ,
      (∑ d ∈ Finset.Icc 1 D, chiCubicPrimeGapCount N d / (d : ℝ)) ≤
        C * N / Real.log N ^ 2 * (1 + Real.log D) := by
  obtain ⟨C, hC, hprefix⟩ := exists_chiCubicPrimeGapCount_prefix_bound
  refine ⟨C, hC, ?_⟩
  filter_upwards [hprefix, eventually_ge_atTop (1 : ℝ)] with N hN hN1
  intro D
  have hpre : ∀ d : ℕ, (∑ k ∈ Finset.Icc 1 d, chiCubicPrimeGapCount N k) ≤
      (C * N / Real.log N ^ 2) * d := by
    intro d
    convert hN d using 1; ring
  exact (sum_Icc_div_le_of_linear_prefix _ _ hpre D).trans
    (mul_le_mul_of_nonneg_left (Sieve.sum_Icc_one_div_le_one_add_log D) (by positivity))

end RHTower
