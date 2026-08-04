import GaloisForLFunctions.RHTower.Sieve.BlockCount
import GaloisForLFunctions.RHTower.Sieve.MoebiusMeanSquareRealForm

/-!
# The mean square, fully explicit

Substituting the block count `J ≤ log(1+K/Y)(1+ε)/ε` and the logarithm-free block cost leaves the
mean square bounded by an expression in the parameters alone:

    ∑_{t ∈ [Y, Y+K)} ( ∑_{t<n≤t+L} μ(n) )²
      ≤ (Y+K) · log(1+K/Y)(1+ε)/ε · ( 2(B(N)N)²·(L/Y) + 4(⌊N⌋+1)²/(π²W) + 2(εL+1)²·ε ) .

The three terms are the cancellation, the frequency tail and the excess; no logarithm and no implicit
constant remains.
-/

namespace RHTower.Sieve

open Filter Topology Finset GaloisForLFunctions.HTGeometry

/-- **The mean square, fully explicit in the parameters.** -/
theorem exists_sum_sq_real_moebius_explicit :
    ∃ B : ℝ → ℝ, Tendsto B atTop (𝓝 0) ∧
      ∀ᶠ N : ℝ in atTop, ∀ (L Y K J : ℕ) (ε W : ℝ),
        Y + K + L < ⌊N⌋₊ + 1 → 0 < (L : ℝ) → 0 < (Y : ℝ) → 0 < ε → 0 < W →
        8 * Real.pi * W + 5 ≤ ((contourParam (N + smoothWidth N) : ℕ) : ℝ) →
        (Y : ℝ) + K = (Y : ℝ) * (1 + ε) ^ J →
        (∑ t ∈ Finset.Ico Y (Y + K),
            (∑ n ∈ Finset.Ioc t (t + L), ((ArithmeticFunction.moebius n : ℤ) : ℝ)) ^ 2)
          ≤ ((Y : ℝ) + K) * (Real.log (1 + (K : ℝ) / (Y : ℝ)) * (1 + ε) / ε)
              * (2 * (B N * N) ^ 2 * ((L : ℝ) / (Y : ℝ))
                  + 4 * ((((⌊N⌋₊ + 1 : ℕ) : ℝ)) ^ 2) / (Real.pi ^ 2 * W)
                  + 2 * (ε * (L : ℝ) + 1) ^ 2 * ε) := by
  obtain ⟨B, hB, hev⟩ := exists_sum_sq_real_moebius_Ico_le
  refine ⟨B, hB, ?_⟩
  filter_upwards [hev] with N hN
  intro L Y K J ε W hM hL hY hε hW hWC hJ
  have hbase := hN L Y K J ε W hM hL hY hε.le hW hWC hJ
  set M₁ : ℝ := (B N * N) ^ 2 with hM₁def
  set M₂ : ℝ := (((⌊N⌋₊ + 1 : ℕ) : ℝ)) ^ 2 with hM₂def
  have hM₁ : 0 ≤ M₁ := by rw [hM₁def]; positivity
  have hM₂ : 0 ≤ M₂ := by rw [hM₂def]; positivity
  have hbc0 : 0 ≤ blockCost (L : ℝ) (Y : ℝ) ε M₁ M₂ W :=
    blockCost_nonneg hL hY hε.le hW hM₁ hM₂
  have hbcle := blockCost_le (L := (L : ℝ)) (Y := (Y : ℝ)) (ε := ε) (M₁ := M₁) (M₂ := M₂)
    (W := W) hL.le hY hε.le hW hM₁
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hJle := blocks_le (Y := (Y : ℝ)) (K := (K : ℝ)) (ε := ε) (J := J) hY hK0 hε hJ
  have hJb0 : (0 : ℝ) ≤ Real.log (1 + (K : ℝ) / (Y : ℝ)) * (1 + ε) / ε := by
    have hlog : 0 ≤ Real.log (1 + (K : ℝ) / (Y : ℝ)) := by
      refine Real.log_nonneg ?_
      have : (0 : ℝ) ≤ (K : ℝ) / (Y : ℝ) := by positivity
      linarith
    positivity
  have hZ : (0 : ℝ) ≤ (Y : ℝ) + K := by linarith
  have hstep1 : (J : ℝ) * blockCost (L : ℝ) (Y : ℝ) ε M₁ M₂ W
      ≤ (Real.log (1 + (K : ℝ) / (Y : ℝ)) * (1 + ε) / ε)
        * blockCost (L : ℝ) (Y : ℝ) ε M₁ M₂ W :=
    mul_le_mul_of_nonneg_right hJle hbc0
  have hstep2 : (Real.log (1 + (K : ℝ) / (Y : ℝ)) * (1 + ε) / ε)
        * blockCost (L : ℝ) (Y : ℝ) ε M₁ M₂ W
      ≤ (Real.log (1 + (K : ℝ) / (Y : ℝ)) * (1 + ε) / ε)
        * (2 * M₁ * ((L : ℝ) / (Y : ℝ)) + 4 * M₂ / (Real.pi ^ 2 * W)
            + 2 * (ε * (L : ℝ) + 1) ^ 2 * ε) :=
    mul_le_mul_of_nonneg_left hbcle hJb0
  have hfinal := mul_le_mul_of_nonneg_left (le_trans hstep1 hstep2) hZ
  rw [← hJ] at hbase
  calc (∑ t ∈ Finset.Ico Y (Y + K),
        (∑ n ∈ Finset.Ioc t (t + L), ((ArithmeticFunction.moebius n : ℤ) : ℝ)) ^ 2)
      ≤ ((Y : ℝ) + K) * ((J : ℝ) * blockCost (L : ℝ) (Y : ℝ) ε M₁ M₂ W) := hbase
    _ ≤ ((Y : ℝ) + K) * ((Real.log (1 + (K : ℝ) / (Y : ℝ)) * (1 + ε) / ε)
          * (2 * M₁ * ((L : ℝ) / (Y : ℝ)) + 4 * M₂ / (Real.pi ^ 2 * W)
              + 2 * (ε * (L : ℝ) + 1) ^ 2 * ε)) := hfinal
    _ = ((Y : ℝ) + K) * (Real.log (1 + (K : ℝ) / (Y : ℝ)) * (1 + ε) / ε)
          * (2 * M₁ * ((L : ℝ) / (Y : ℝ)) + 4 * M₂ / (Real.pi ^ 2 * W)
              + 2 * (ε * (L : ℝ) + 1) ^ 2 * ε) := by ring

end RHTower.Sieve
