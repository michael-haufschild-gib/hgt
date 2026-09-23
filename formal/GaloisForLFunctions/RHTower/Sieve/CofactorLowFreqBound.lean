import GaloisForLFunctions.RHTower.Sieve.MoebiusTwistSharpRate
import GaloisForLFunctions.RHTower.Sieve.PrimeBlockTwistBound
import GaloisForLFunctions.RHTower.Sieve.TwoSidedCofactorBlock

/-!
# The cofactor polynomial at low frequency

Near zero frequency the prime polynomial of a ladder step carries no cancellation, so the saving has
to come from the cofactor.  The cofactor polynomial of a step is a Möbius sum over an interval, and
the twisted contour bound gives it a saving better than any power of the logarithm, uniformly over a
frequency range that is itself larger than any power of the logarithm.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The explicit majorant for a sharp twisted Möbius sum. -/
def moebiusSharpBound (N : ℝ) : ℝ :=
  3 * N * Real.exp (-(zeroFreeConst / 8192 * ((Real.log N) ^ ((1 : ℝ) / 20)) ^ (2 : ℕ) / 2)) / Real.pi
    + (smoothWidth N + 1)

/-- The Möbius coefficient against the Gallagher phase is the twisted Möbius coefficient. -/
theorem moebiusCoeff_mul_unitLogPhase_eq (n : ℕ) (w : ℝ) :
    moebiusCoeff n * unitLogPhase w n = moebiusTwist (-(2 * Real.pi * w)) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [moebiusTwist_zero, moebiusCoeff]
    simp
  · rw [moebiusTwist, moebiusCoeff, unitLogPhase_eq_cpow hn w]
    congr 2
    push_cast
    ring

/-- **The cofactor polynomial is a twisted Möbius sum.** -/
theorem logPoly_moebiusCoeff_eq_sum_moebiusTwist (s : Finset ℕ) (w : ℝ) :
    logPoly moebiusCoeff s w = ∑ n ∈ s, moebiusTwist (-(2 * Real.pi * w)) n := by
  rw [logPoly]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← moebiusCoeff_mul_unitLogPhase_eq n w, unitLogPhase]

/-- A twisted Möbius sum over an interval is a difference of initial sums. -/
theorem sum_moebiusTwist_Icc_eq (τ : ℝ) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b + 1) :
    ∑ n ∈ Finset.Icc a b, moebiusTwist τ n
      = (∑ n ∈ Finset.range (b + 1), moebiusTwist τ n)
        - ∑ n ∈ Finset.range ((a - 1) + 1), moebiusTwist τ n := by
  classical
  have hsub : Finset.range ((a - 1) + 1) ⊆ Finset.range (b + 1) := by
    intro n hn
    rw [Finset.mem_range] at hn ⊢
    omega
  rw [eq_comm, sub_eq_iff_eq_add, ← Finset.sum_sdiff hsub]
  have hsd : Finset.range (b + 1) \ Finset.range ((a - 1) + 1) = Finset.Icc a b := by
    ext n
    rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range, Finset.mem_Icc]
    omega
  rw [hsd, add_comm]

/-- The majorant is nonnegative above `3`. -/
theorem moebiusSharpBound_nonneg {N : ℝ} (hN : 3 ≤ N) : 0 ≤ moebiusSharpBound N := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog : (1 : ℝ) ≤ Real.log N := by
    have h3 : Real.exp 1 ≤ N := le_trans (le_of_lt (Real.exp_one_lt_d9.trans (by norm_num))) hN
    have := Real.log_le_log (Real.exp_pos 1) h3
    rwa [Real.log_exp] at this
  have hW := one_le_smoothWidth hN0 hlog
  rw [moebiusSharpBound]
  have h1 : (0 : ℝ)
      ≤ 3 * N * Real.exp (-(zeroFreeConst / 8192 * ((Real.log N) ^ ((1 : ℝ) / 20)) ^ (2 : ℕ) / 2))
        / Real.pi := by positivity
  linarith

/-- **The cofactor polynomial at low frequency.**  The saving is better than any power of the
logarithm, uniformly over a frequency range larger than any power of the logarithm. -/
theorem exists_norm_logPoly_moebiusCoeff_Icc_le :
    ∃ (K₀ : ℕ) (N₁ : ℝ), ∀ (a b : ℕ) (w : ℝ), 1 ≤ a →
      N₁ ≤ ((a - 1 : ℕ) : ℝ) → N₁ ≤ (b : ℝ) →
      K₀ ≤ contourParam (((a - 1 : ℕ) : ℝ) + smoothWidth ((a - 1 : ℕ) : ℝ)) →
      K₀ ≤ contourParam ((b : ℝ) + smoothWidth (b : ℝ)) →
      5 + 4 * |(-(2 * Real.pi * w))|
        ≤ ((contourParam (((a - 1 : ℕ) : ℝ) + smoothWidth ((a - 1 : ℕ) : ℝ)) : ℕ) : ℝ) →
      5 + 4 * |(-(2 * Real.pi * w))| ≤ ((contourParam ((b : ℝ) + smoothWidth (b : ℝ)) : ℕ) : ℝ) →
      ‖logPoly moebiusCoeff (Finset.Icc a b) w‖
        ≤ moebiusSharpBound ((a - 1 : ℕ) : ℝ) + moebiusSharpBound (b : ℝ) := by
  obtain ⟨K₀, hev⟩ := exists_norm_sum_moebiusTwist_rate
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 hev
  refine ⟨K₀, max N₁ 3, ?_⟩
  intro a b w ha hlo' hhi' hKlo hKhi hτlo hτhi
  have hlo : N₁ ≤ ((a - 1 : ℕ) : ℝ) := le_trans (le_max_left _ _) hlo'
  have hhi : N₁ ≤ (b : ℝ) := le_trans (le_max_left _ _) hhi'
  have hlo3 : (3 : ℝ) ≤ ((a - 1 : ℕ) : ℝ) := le_trans (le_max_right _ _) hlo'
  have hhi3 : (3 : ℝ) ≤ (b : ℝ) := le_trans (le_max_right _ _) hhi'
  set τ : ℝ := -(2 * Real.pi * w) with hτ
  have hbound : ∀ N : ℝ, N₁ ≤ N →
      K₀ ≤ contourParam (N + smoothWidth N) →
      5 + 4 * |τ| ≤ ((contourParam (N + smoothWidth N) : ℕ) : ℝ) →
      ‖∑ n ∈ Finset.range (⌊N⌋₊ + 1), moebiusTwist τ n‖ ≤ moebiusSharpBound N := by
    intro N hN hK hτle
    exact hN₁ N hN τ hK hτle
  have hlofl : ⌊((a - 1 : ℕ) : ℝ)⌋₊ = a - 1 := Nat.floor_natCast _
  have hhifl : ⌊((b : ℕ) : ℝ)⌋₊ = b := Nat.floor_natCast _
  have hA := hbound ((a - 1 : ℕ) : ℝ) hlo hKlo hτlo
  have hB := hbound ((b : ℕ) : ℝ) hhi hKhi hτhi
  rw [hlofl] at hA
  rw [hhifl] at hB
  by_cases hab : a ≤ b + 1
  · rw [logPoly_moebiusCoeff_eq_sum_moebiusTwist, ← hτ, sum_moebiusTwist_Icc_eq τ ha hab]
    refine (norm_sub_le _ _).trans ?_
    linarith [hA, hB]
  · have hempty : Finset.Icc a b = ∅ := Finset.Icc_eq_empty (by omega)
    rw [logPoly, hempty, Finset.sum_empty, norm_zero]
    linarith [moebiusSharpBound_nonneg hlo3, moebiusSharpBound_nonneg hhi3]

/-- **The cofactor polynomial of an initial block at low frequency.** -/
theorem exists_norm_logPoly_moebiusCoeff_Icc_one_le :
    ∃ (K₀ : ℕ) (N₁ : ℝ), ∀ (b : ℕ) (w : ℝ), N₁ ≤ (b : ℝ) →
      K₀ ≤ contourParam ((b : ℝ) + smoothWidth (b : ℝ)) →
      5 + 4 * |(-(2 * Real.pi * w))|
        ≤ ((contourParam ((b : ℝ) + smoothWidth (b : ℝ)) : ℕ) : ℝ) →
      ‖logPoly moebiusCoeff (Finset.Icc 1 b) w‖ ≤ moebiusSharpBound (b : ℝ) := by
  obtain ⟨K₀, hev⟩ := exists_norm_sum_moebiusTwist_rate
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 hev
  refine ⟨K₀, N₁, ?_⟩
  intro b w hb hK hτ
  have hfl : ⌊((b : ℕ) : ℝ)⌋₊ = b := Nat.floor_natCast _
  have hbase := hN₁ ((b : ℕ) : ℝ) hb (-(2 * Real.pi * w)) hK hτ
  rw [hfl] at hbase
  rw [logPoly_moebiusCoeff_eq_sum_moebiusTwist,
    ← sum_range_succ_eq_sum_Icc (moebiusTwist_zero (-(2 * Real.pi * w))) b]
  exact hbase

/-- The cofactor block of a ladder step over an initial index range is an initial interval. -/
theorem geomCofactorBlockAt_one_eq {B₀ : ℕ} {Q η : ℝ} (hQ : 1 ≤ Q) (hη : 0 ≤ η) (j : ℕ) :
    geomCofactorBlockAt 1 B₀ Q η j = Finset.Icc 1 ⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ := by
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  have hpow : (1 : ℝ) ≤ (1 + η) ^ j := one_le_pow₀ hr1
  have hQ0 : (0 : ℝ) < Q := by linarith
  have h1 : (1 : ℝ) ≤ Q * (1 + η) ^ j := by nlinarith [hQ, hpow]
  have hden : (1 : ℝ) ≤ Q * (1 + η) ^ j * (1 + η) := by nlinarith [h1, hr1]
  have hden0 : (0 : ℝ) < Q * (1 + η) ^ j * (1 + η) := by linarith
  have hceil : ⌈((1 : ℕ) : ℝ) / (Q * (1 + η) ^ j * (1 + η))⌉₊ = 1 := by
    refine le_antisymm (Nat.ceil_le.2 ?_) (Nat.one_le_ceil_iff.2 ?_)
    · push_cast
      rw [div_le_one hden0]
      linarith
    · push_cast
      positivity
  rw [geomCofactorBlockAt, hceil]

/-- **The cofactor polynomial of a ladder step at low frequency.** -/
theorem exists_norm_logPoly_geomCofactorBlockAt_le :
    ∃ (K₀ : ℕ) (N₁ : ℝ), ∀ (B₀ j : ℕ) (Q η w : ℝ), 1 ≤ Q → 0 ≤ η →
      N₁ ≤ ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ) →
      K₀ ≤ contourParam (((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)
        + smoothWidth ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)) →
      5 + 4 * |(-(2 * Real.pi * w))|
        ≤ ((contourParam (((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)
            + smoothWidth ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)) : ℕ) : ℝ) →
      ‖logPoly moebiusCoeff (geomCofactorBlockAt 1 B₀ Q η j) w‖
        ≤ moebiusSharpBound ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ) := by
  obtain ⟨K₀, N₁, hbound⟩ := exists_norm_logPoly_moebiusCoeff_Icc_one_le
  refine ⟨K₀, N₁, ?_⟩
  intro B₀ j Q η w hQ hη hN hK hτ
  rw [geomCofactorBlockAt_one_eq hQ hη j]
  exact hbound ⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ w hN hK hτ

end

end RHTower.Sieve
