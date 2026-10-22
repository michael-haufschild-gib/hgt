import GaloisForLFunctions.SmoothBernoulliPoleCalibration.HigherOrderKernelStatisticAndDualNorm
import GaloisForLFunctions.BezoutValuationIncidence.MoebiusBlockBeatsTheTypeTwoBarrier
import GaloisForLFunctions.BezoutValuationIncidence.CentredPrimeRowPassesTheCoherentBlockObstruction
import GaloisForLFunctions.BezoutValuationIncidence.SharpCutoffTypeIStopsAtFourThirds

/-!
# Smooth-Tapered Cross-Scale Dispersion and Smooth-Plus-Oscillatory Row Bridge

In `SharpCutoffTypeIStopsAtFourThirds`, a flat row on `[A + 1, A + L]` with sharp endpoints
suffers a boundary jump in `centredKernelPrimitive`, forcing
`∑ p ∈ S', |kernelStatistic N (flatRow A L) p| / p ≥ (∑ p ∈ S', p^2) / (14400 * A)` and
stopping sharp-cutoff Type-I dispersion at `θ = 4/3`.

This file proves the smooth-tapered elimination of the polynomial Bernoulli tower and couples it
with the short-window arithmetic rows (`moebiusWindowRow` and `centredPrimeRow`):
1. Defines `crossScaleFunctional N c c'` and proves its exact linearity in the large-scale row `c'`
   (`crossScaleFunctional_add_right`).
2. Defines `IsSmoothTaperedAtScale N L Q C₀ c'` (`smoothnessNorm N L c' ≤ C₀ * M₂(c') / Q^L`) and
   proves that across any prime modulus support `d ≤ 2P`, the order-`L` polynomial factor `d^{L+1}`
   collapses to `2^L C₀ d (P / Q)^L M₂(c')` (`sum_abs_higherOrderKernelStatistic_le_of_isSmoothTaperedAtScale`,
   `abs_crossScaleFunctional_le_of_isSmoothTaperedAtScale`).
3. Proves the **Smooth-Plus-Oscillatory Row Decomposition Bridge**
   (`abs_crossScaleFunctional_add_le_of_isSmoothTaperedAtScale`) and instantiates it on both
   `centredPrimeRow A H K` (`exists_abs_crossScaleFunctional_smooth_add_centredPrimeRow_le`) and
   `moebiusWindowRow Q` (`eventually_abs_crossScaleFunctional_smooth_add_moebiusWindowRow_le`).
-/

noncomputable section

open Finset Filter Topology BigOperators Real RHTower GaloisForLFunctions.BiScaleUncertainty

namespace GaloisForLFunctions.SmoothBernoulliPoleCalibration

open GaloisForLFunctions.BezoutValuationIncidence

/-- The shifted cross-scale functional `B(c, c') + m(c) R(c') + β(c) H(c')`. -/
def crossScaleFunctional (N : ℕ) (c c' : ℕ → ℝ) : ℝ :=
  rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
    rowBeta N c * finiteHarmonicSum N c'

/-- Exact linearity of `crossScaleFunctional` in the large-scale row `c'`, proved via the exact
residue tail identity `rowBilinear_add_mean_add_beta_eq_tail`. -/
theorem crossScaleFunctional_add_right (N : ℕ) (c c'₁ c'₂ : ℕ → ℝ) :
    crossScaleFunctional N c (fun n => c'₁ n + c'₂ n) =
      crossScaleFunctional N c c'₁ + crossScaleFunctional N c c'₂ := by
  unfold crossScaleFunctional
  rw [rowBilinear_add_mean_add_beta_eq_tail N c (fun n => c'₁ n + c'₂ n),
    rowBilinear_add_mean_add_beta_eq_tail N c c'₁,
    rowBilinear_add_mean_add_beta_eq_tail N c c'₂, ← neg_add, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun n _ => ?_
  rw [← sum_add_distrib]
  exact sum_congr rfl fun d _ => by ring

/-- A large-scale row `c'` is `L`-smooth-tapered at scale `Q` with constant `C₀` if it is
supported in `[L + 1, N]` and its order-`L` backward-difference smoothness norm satisfies
`smoothnessNorm N L c' ≤ C₀ * M₂(c') / Q^L`. -/
def IsSmoothTaperedAtScale (N L Q : ℕ) (C₀ : ℝ) (c' : ℕ → ℝ) : Prop :=
  (∀ n, c' n ≠ 0 → L + 1 ≤ n ∧ n ≤ N) ∧
    smoothnessNorm N L c' ≤
      C₀ * (∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2) / (Q : ℝ) ^ L

/-- For an `L`-smooth-tapered row at scale `Q`, the order-`L` dual norm over primes `p ∈ S`
with `p ≤ 2P` has its polynomial Bernoulli growth `p^{L+1}` compressed to `p * (2P / Q)^L`. -/
theorem sum_abs_higherOrderKernelStatistic_le_of_isSmoothTaperedAtScale
    (N L P Q : ℕ) (C₀ : ℝ)
    (S : Finset ℕ) (hp : ∀ p ∈ S, p.Prime ∧ p ≤ 2 * P)
    (c' : ℕ → ℝ) (hsmooth : IsSmoothTaperedAtScale N L Q C₀ c') :
    ∑ p ∈ S, |higherOrderKernelStatistic N L c' p| / (p : ℝ) ≤
      (2 * (L : ℝ) * (8 : ℝ) ^ L * (L + 1).factorial * C₀ *
        (∑ p ∈ S, (p : ℝ)) * ((P : ℝ) / (Q : ℝ)) ^ L +
      (L : ℝ) * (2 : ℝ) ^ L * L.factorial * (∑ p ∈ S, (1 : ℝ) / (p : ℝ))) *
        (∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2) := by
  have h_base := sum_abs_higherOrderKernelStatistic_le_smoothnessNorm N L S
    (fun p hpS => (hp p hpS).1) c' hsmooth.1
  set M₂ := ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2
  have hM₂ : 0 ≤ M₂ := sum_nonneg fun n _ => by positivity
  have h_p_sum : ∑ p ∈ S, (p : ℝ) ^ (L + 1) ≤
      (2 : ℝ) ^ L * (P : ℝ) ^ L * ∑ p ∈ S, (p : ℝ) := by
    rw [mul_sum]
    refine sum_le_sum fun p hpS => ?_
    have hp_le : (p : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast (hp p hpS).2
    have hp_pow : (p : ℝ) ^ L ≤ (2 * (P : ℝ)) ^ L :=
      pow_le_pow_left₀ (Nat.cast_nonneg p) hp_le L
    calc (p : ℝ) ^ (L + 1) = (p : ℝ) ^ L * (p : ℝ) := pow_succ (p : ℝ) L
      _ ≤ (2 * (P : ℝ)) ^ L * (p : ℝ) := mul_le_mul_of_nonneg_right hp_pow (Nat.cast_nonneg p)
      _ = (2 : ℝ) ^ L * (P : ℝ) ^ L * (p : ℝ) := by rw [mul_pow]
  have h_prod : (∑ p ∈ S, (p : ℝ) ^ (L + 1)) * smoothnessNorm N L c' ≤
      (2 : ℝ) ^ L * C₀ * (∑ p ∈ S, (p : ℝ)) * ((P : ℝ) / (Q : ℝ)) ^ L * M₂ := by
    have hSn : 0 ≤ smoothnessNorm N L c' :=
      sum_nonneg fun t _ => sum_nonneg fun n _ => by positivity
    calc (∑ p ∈ S, (p : ℝ) ^ (L + 1)) * smoothnessNorm N L c'
      _ ≤ ((2 : ℝ) ^ L * (P : ℝ) ^ L * ∑ p ∈ S, (p : ℝ)) * (C₀ * M₂ / (Q : ℝ) ^ L) :=
          mul_le_mul h_p_sum hsmooth.2 hSn (by positivity)
      _ = (2 : ℝ) ^ L * C₀ * (∑ p ∈ S, (p : ℝ)) * ((P : ℝ) / (Q : ℝ)) ^ L * M₂ := by
          rw [div_pow]; ring
  have h8 : (4 : ℝ) ^ L * (2 : ℝ) ^ L = (8 : ℝ) ^ L := by
    rw [← mul_pow]; norm_num
  calc ∑ p ∈ S, |higherOrderKernelStatistic N L c' p| / (p : ℝ)
    _ ≤ 2 * (L : ℝ) * (4 : ℝ) ^ L * (L + 1).factorial *
          ((∑ p ∈ S, (p : ℝ) ^ (L + 1)) * smoothnessNorm N L c') +
        (L : ℝ) * (2 : ℝ) ^ L * L.factorial *
          (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) * M₂ := by
        linarith [h_base]
    _ ≤ 2 * (L : ℝ) * (4 : ℝ) ^ L * (L + 1).factorial *
          ((2 : ℝ) ^ L * C₀ * (∑ p ∈ S, (p : ℝ)) * ((P : ℝ) / (Q : ℝ)) ^ L * M₂) +
        (L : ℝ) * (2 : ℝ) ^ L * L.factorial *
          (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) * M₂ := by
        gcongr
    _ = (2 * (L : ℝ) * ((4 : ℝ) ^ L * (2 : ℝ) ^ L) * (L + 1).factorial * C₀ *
          (∑ p ∈ S, (p : ℝ)) * ((P : ℝ) / (Q : ℝ)) ^ L +
        (L : ℝ) * (2 : ℝ) ^ L * L.factorial * (∑ p ∈ S, (1 : ℝ) / (p : ℝ))) * M₂ := by ring
    _ = _ := by rw [h8]

/-- Smooth-tapered cross-scale dispersion bound: for any `L`-smooth-tapered row `c'` at scale `Q`
and any prime weight `c` supported on `[1, 2P]`, `|crossScaleFunctional N c c'|` is bounded by
`O_L((∑ |c d| d) (P / Q)^L + ∑ |c d| / d) * M₂(c')`, eliminating the polynomial Bernoulli
barrier in every regime `P ≪ Q^{1 - 1/(L+1)}`. -/
theorem abs_crossScaleFunctional_le_of_isSmoothTaperedAtScale
    (N L P Q : ℕ) (C₀ : ℝ)
    {c c' : ℕ → ℝ} (hc : ∀ d, c d ≠ 0 → d.Prime ∧ d ≤ 2 * P)
    (hsmooth : IsSmoothTaperedAtScale N L Q C₀ c') :
    |crossScaleFunctional N c c'| ≤
      2 * ((L : ℝ) + 1) * (4 : ℝ) ^ L * (L + 1).factorial *
        ((2 : ℝ) ^ L * C₀ * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ)) * ((P : ℝ) / (Q : ℝ)) ^ L +
          ∑ d ∈ Icc 1 N, |c d| / (d : ℝ)) *
        (∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2) := by
  unfold crossScaleFunctional
  have h_law := abs_rowBilinear_add_mean_add_beta_le_smoothnessNorm N L
    (fun d hd => (hc d hd).1) hsmooth.1
  set M₂ := ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2
  have hM₂ : 0 ≤ M₂ := sum_nonneg fun n _ => by positivity
  have h_sum : ∑ d ∈ Icc 1 N, |c d| * ((d : ℝ) ^ (L + 1) * smoothnessNorm N L c' + M₂ / (d : ℝ)) ≤
      ((2 : ℝ) ^ L * C₀ * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ)) * ((P : ℝ) / (Q : ℝ)) ^ L +
        ∑ d ∈ Icc 1 N, |c d| / (d : ℝ)) * M₂ := by
    have h_each : ∀ d ∈ Icc 1 N,
        |c d| * ((d : ℝ) ^ (L + 1) * smoothnessNorm N L c' + M₂ / (d : ℝ)) ≤
        |c d| * (d : ℝ) * ((2 : ℝ) ^ L * C₀ * ((P : ℝ) / (Q : ℝ)) ^ L * M₂) +
          (|c d| / (d : ℝ)) * M₂ := by
      intro d _
      by_cases hcd : c d = 0
      · simp [hcd]
      · have hdP : (d : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast (hc d hcd).2
        have hd_pow : (d : ℝ) ^ L ≤ (2 * (P : ℝ)) ^ L :=
          pow_le_pow_left₀ (Nat.cast_nonneg d) hdP L
        have hSn : 0 ≤ smoothnessNorm N L c' :=
          sum_nonneg fun t _ => sum_nonneg fun n _ => by positivity
        have h_dL : (d : ℝ) ^ (L + 1) * smoothnessNorm N L c' ≤
            (d : ℝ) * ((2 : ℝ) ^ L * C₀ * ((P : ℝ) / (Q : ℝ)) ^ L * M₂) := by
          calc (d : ℝ) ^ (L + 1) * smoothnessNorm N L c'
            _ = (d : ℝ) * ((d : ℝ) ^ L * smoothnessNorm N L c') := by
                rw [pow_succ' (d : ℝ) L, mul_assoc]
            _ ≤ (d : ℝ) * ((2 * (P : ℝ)) ^ L * (C₀ * M₂ / (Q : ℝ) ^ L)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul hd_pow hsmooth.2 hSn (by positivity))
                  (Nat.cast_nonneg d)
            _ = (d : ℝ) * ((2 : ℝ) ^ L * C₀ * ((P : ℝ) / (Q : ℝ)) ^ L * M₂) := by
                rw [mul_pow, div_pow]; ring
        calc |c d| * ((d : ℝ) ^ (L + 1) * smoothnessNorm N L c' + M₂ / (d : ℝ))
          _ ≤ |c d| * ((d : ℝ) * ((2 : ℝ) ^ L * C₀ * ((P : ℝ) / (Q : ℝ)) ^ L * M₂) +
                M₂ / (d : ℝ)) :=
              mul_le_mul_of_nonneg_left (add_le_add_left h_dL _) (abs_nonneg _)
          _ = |c d| * (d : ℝ) * ((2 : ℝ) ^ L * C₀ * ((P : ℝ) / (Q : ℝ)) ^ L * M₂) +
                (|c d| / (d : ℝ)) * M₂ := by ring
    calc ∑ d ∈ Icc 1 N, |c d| * ((d : ℝ) ^ (L + 1) * smoothnessNorm N L c' + M₂ / (d : ℝ))
      _ ≤ ∑ d ∈ Icc 1 N, (|c d| * (d : ℝ) * ((2 : ℝ) ^ L * C₀ * ((P : ℝ) / (Q : ℝ)) ^ L * M₂) +
            (|c d| / (d : ℝ)) * M₂) := sum_le_sum h_each
      _ = ((2 : ℝ) ^ L * C₀ * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ)) * ((P : ℝ) / (Q : ℝ)) ^ L +
            ∑ d ∈ Icc 1 N, |c d| / (d : ℝ)) * M₂ := by
          rw [sum_add_distrib, ← sum_mul, ← sum_mul]; ring
  calc |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
          rowBeta N c * finiteHarmonicSum N c'|
    _ ≤ 2 * ((L : ℝ) + 1) * (4 : ℝ) ^ L * (L + 1).factorial *
          ∑ d ∈ Icc 1 N, |c d| * ((d : ℝ) ^ (L + 1) * smoothnessNorm N L c' + M₂ / (d : ℝ)) := h_law
    _ ≤ 2 * ((L : ℝ) + 1) * (4 : ℝ) ^ L * (L + 1).factorial *
          (((2 : ℝ) ^ L * C₀ * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ)) * ((P : ℝ) / (Q : ℝ)) ^ L +
            ∑ d ∈ Icc 1 N, |c d| / (d : ℝ)) * M₂) :=
        mul_le_mul_of_nonneg_left h_sum (by positivity)
    _ = _ := by ring

/-- **Smooth-Plus-Oscillatory Row Decomposition Bridge.**
For any decomposition `c' = c'_smooth + c'_osc` into an `L`-smooth-tapered baseline at scale `Q`
and an oscillatory residual `c'_osc`, the cross-scale functional is bounded by the order-`L`
smooth dispersion of `c'_smooth` plus `|crossScaleFunctional N c c'_osc|`. -/
theorem abs_crossScaleFunctional_add_le_of_isSmoothTaperedAtScale
    (N L P Q : ℕ) (C₀ : ℝ)
    {c c'_smooth c'_osc : ℕ → ℝ} (hc : ∀ d, c d ≠ 0 → d.Prime ∧ d ≤ 2 * P)
    (hsmooth : IsSmoothTaperedAtScale N L Q C₀ c'_smooth) :
    |crossScaleFunctional N c (fun n => c'_smooth n + c'_osc n)| ≤
      2 * ((L : ℝ) + 1) * (4 : ℝ) ^ L * (L + 1).factorial *
        ((2 : ℝ) ^ L * C₀ * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ)) * ((P : ℝ) / (Q : ℝ)) ^ L +
          ∑ d ∈ Icc 1 N, |c d| / (d : ℝ)) *
        (∑ n ∈ Icc 1 N, |c'_smooth n| / (n : ℝ) ^ 2) +
      |crossScaleFunctional N c c'_osc| := by
  rw [crossScaleFunctional_add_right]
  refine (abs_add_le _ _).trans ?_
  exact add_le_add_left
    (abs_crossScaleFunctional_le_of_isSmoothTaperedAtScale N L P Q C₀ hc hsmooth) _

/-- Coupling the order-`L` smooth-tapered dispersion law with `centredPrimeRow`:
any superposition `c'_smooth + centredPrimeRow A H K` simultaneously eliminates the polynomial
Bernoulli tower on `c'_smooth` and passes the coherent-block obstruction on `centredPrimeRow`. -/
theorem exists_abs_crossScaleFunctional_smooth_add_centredPrimeRow_le
    {α : ℝ} (hα : 7 / 12 < α) (hα1 : α < 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ Q₀ : ℕ, ∀ {N L A H K P Q : ℕ} {C₀ : ℝ} {c c'_smooth : ℕ → ℝ},
      Q₀ ≤ Q → Q ≤ A → A + K * H ≤ 2 * Q → 2 * Q ≤ N → 1 ≤ P →
      (2 * (Q : ℝ)) ^ α ≤ H → (H : ℝ) ≤ 4 * (Q : ℝ) ^ α →
      (∀ d, c d ≠ 0 → d.Prime ∧ P < d ∧ d ≤ 2 * P) →
      IsSmoothTaperedAtScale N L Q C₀ c'_smooth →
      (H : ℝ) * (∑ k ∈ Icc 1 N, 1 / (k : ℝ)) ^ 2 / 2 + 1 / 8 ≤ ε * P →
      3 * (P : ℝ) ≤ 2 * ε * Q →
      |crossScaleFunctional N c (fun n => c'_smooth n + centredPrimeRow A H K n)| ≤
        2 * ((L : ℝ) + 1) * (4 : ℝ) ^ L * (L + 1).factorial *
          ((2 : ℝ) ^ L * C₀ * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ)) * ((P : ℝ) / (Q : ℝ)) ^ L +
            ∑ d ∈ Icc 1 N, |c d| / (d : ℝ)) *
          (∑ n ∈ Icc 1 N, |c'_smooth n| / (n : ℝ) ^ 2) +
        16 * ε * rowInverseSquareMass N (centredPrimeRow A H K) * rowLinearWeight N c := by
  obtain ⟨Q₀, hQ₀⟩ := exists_abs_rowBilinear_centredPrimeRow_le hα hα1 hε hε1
  refine ⟨Q₀, ?_⟩
  intro N L A H K P Q C₀ c c'_smooth hQ hA hAK hN hP hH1 hH2 hc hsmooth hterm2 hterm3
  have h_bridge := abs_crossScaleFunctional_add_le_of_isSmoothTaperedAtScale
    N L P Q C₀ (c'_osc := centredPrimeRow A H K)
    (fun d hd => ⟨(hc d hd).1, (hc d hd).2.2⟩) hsmooth
  have h_osc : |crossScaleFunctional N c (centredPrimeRow A H K)| ≤
      16 * ε * rowInverseSquareMass N (centredPrimeRow A H K) * rowLinearWeight N c :=
    hQ₀ hQ hA hAK hN hP hH1 hH2 (fun d hd => (hc d hd).2) hterm2 hterm3
  exact h_bridge.trans (add_le_add_right h_osc _)

end GaloisForLFunctions.SmoothBernoulliPoleCalibration
