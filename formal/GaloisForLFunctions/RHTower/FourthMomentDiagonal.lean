/-
The fourth-moment diagonal is bounded on every line right of the critical line.

Combining the divisor bound `d(n) ≪_ε n^ε` (`DivisorBound`) with `p`-series convergence, the
fourth-moment diagonal coefficient sum is uniformly bounded for `σ > 1/2`:

  ∑_{n≤N} d(n)² n^{-2σ} ≤ C(σ)      for all N,

with `C(σ) = C₀² · ζ((2σ+1)/2)` finite.  Taking `ε = (2σ−1)/4`, the divisor bound gives
`d(n)² n^{-2σ} ≤ C₀² n^{2ε−2σ} = C₀² n^{−(2σ+1)/2}`, and `(2σ+1)/2 > 1` exactly when `σ > 1/2`, so the
majorant is a convergent `p`-series.

This is the estimate Carlson's density theorem needs: fed to `FourthMoment.fourthMoment_dpoly_le`, it
makes the fourth moment `∫_T^{T+U} ‖∑_{n≤N} d(n) n^{-σ-it}‖² dt` bounded by `C·U + (off-diagonal)` — a
*bounded* mean value on every vertical line with `σ > 1/2`, uniformly in the length `N` of the
Dirichlet polynomial.  It is the sharp-range companion of `FourthMoment.fourthMoment_diagonal_crude_le`
(which reaches only `σ > 3/2` via the crude `d(n) ≤ n`).
-/
import GaloisForLFunctions.RHTower.FourthMoment
import GaloisForLFunctions.RHTower.DivisorBound

open Real Finset

namespace RHTower

/-- **The fourth-moment diagonal is uniformly bounded for `σ > 1/2`.**  There is a finite constant
`C` with `∑_{n≤N} d(n)² n^{-2σ} ≤ C` for every `N`, via the divisor bound and `p`-series convergence. -/
theorem fourthMoment_diagonal_bounded {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-2 * σ) ≤ C := by
  set ε : ℝ := (2 * σ - 1) / 4 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  obtain ⟨C₀, hC₀pos, hC₀⟩ := card_divisors_le_const_mul_rpow hε
  set s : ℝ := (2 * σ + 1) / 2 with hs_def
  have hs1 : 1 < s := by rw [hs_def]; linarith
  -- The majorant `g n = C₀² · n^{-s}` is summable and nonnegative.
  have hns : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) := by
    refine ((Real.summable_one_div_nat_rpow (p := s)).mpr hs1).congr (fun n => ?_)
    rw [one_div, ← Real.rpow_neg (Nat.cast_nonneg n)]
  set g : ℕ → ℝ := fun n => C₀ ^ 2 * (n : ℝ) ^ (-s) with hg_def
  have hgsum : Summable g := hns.mul_left (C₀ ^ 2)
  have hgnn : ∀ n : ℕ, 0 ≤ g n := fun n => by rw [hg_def]; positivity
  refine ⟨∑' n : ℕ, g n, ?_, ?_⟩
  · -- positivity of the constant: the `n = 1` term is `C₀² > 0`.
    refine Summable.tsum_pos hgsum hgnn 1 ?_
    rw [hg_def]; simp only [Nat.cast_one, Real.one_rpow, mul_one]; positivity
  · intro N
    -- termwise majorant on `[1, N]`
    have hfg : ∀ n ∈ Finset.Icc 1 N,
        (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-2 * σ) ≤ g n := by
      intro n hn
      obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have hd : (n.divisors.card : ℝ) ≤ C₀ * (n : ℝ) ^ ε := hC₀ n hn1
      have hdsq : (n.divisors.card : ℝ) ^ 2 ≤ (C₀ * (n : ℝ) ^ ε) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hd 2
      calc (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-2 * σ)
          ≤ (C₀ * (n : ℝ) ^ ε) ^ 2 * (n : ℝ) ^ (-2 * σ) :=
            mul_le_mul_of_nonneg_right hdsq (Real.rpow_nonneg hnpos.le _)
        _ = g n := by
            rw [hg_def, mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ ε) 2, ← Real.rpow_mul hnpos.le,
              mul_assoc, ← Real.rpow_add hnpos]
            congr 2
            rw [hs_def, hε_def]; push_cast; ring
    calc ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-2 * σ)
        ≤ ∑ n ∈ Finset.Icc 1 N, g n := Finset.sum_le_sum hfg
      _ ≤ ∑' n : ℕ, g n := hgsum.sum_le_tsum _ (fun n _ => hgnn n)

/-- **Carlson's bounded fourth moment.**  For `σ > 1/2` there is a finite `C` such that, for every
Dirichlet-polynomial length `N` and every window `[T, T+U]` with `U ≥ 0`,

  ∫_T^{T+U} ‖∑_{n≤N} d(n) n^{-σ-it}‖² dt ≤ C · U + (off-diagonal remainder),

with the diagonal main term bounded *uniformly in `N`* by `C · U`.  This is the fourth moment of ζ
(the second moment of `ζ²`) as a bounded mean value on every vertical line right of the critical line
— the analytic input Carlson's density theorem feeds through Littlewood's lemma to reach `o(T)`. -/
theorem fourthMoment_bounded {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (T U : ℝ), 0 ≤ U →
      (∫ t in T..(T + U), ‖dpoly (divisorCoeff σ) (Finset.Icc 1 N) t‖ ^ 2)
        ≤ C * U
          + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
              2 * |divisorCoeff σ m * divisorCoeff σ n| / |Real.log n - Real.log m| := by
  obtain ⟨C, hCpos, hC⟩ := fourthMoment_diagonal_bounded hσ
  refine ⟨C, hCpos, fun N T U hU => ?_⟩
  have hdiag_eq : ∑ m ∈ Finset.Icc 1 N, (divisorCoeff σ m) ^ 2
      = ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-2 * σ) :=
    Finset.sum_congr rfl (fun n hn => divisorCoeff_sq σ (Finset.mem_Icc.mp hn).1)
  have hdiag_le : U * (∑ m ∈ Finset.Icc 1 N, (divisorCoeff σ m) ^ 2) ≤ C * U := by
    rw [hdiag_eq, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC N) hU
  calc (∫ t in T..(T + U), ‖dpoly (divisorCoeff σ) (Finset.Icc 1 N) t‖ ^ 2)
      ≤ U * (∑ m ∈ Finset.Icc 1 N, (divisorCoeff σ m) ^ 2)
        + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            2 * |divisorCoeff σ m * divisorCoeff σ n| / |Real.log n - Real.log m| :=
        fourthMoment_dpoly_le N σ T U
    _ ≤ C * U
        + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            2 * |divisorCoeff σ m * divisorCoeff σ n| / |Real.log n - Real.log m| := by
        linarith [hdiag_le]

end RHTower
