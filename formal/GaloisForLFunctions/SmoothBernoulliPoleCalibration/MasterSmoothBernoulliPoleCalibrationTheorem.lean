import GaloisForLFunctions.SmoothBernoulliPoleCalibration.HigherOrderKernelStatisticAndDualNorm
import GaloisForLFunctions.SmoothBernoulliPoleCalibration.SmoothTaperedCrossScaleDispersion
import GaloisForLFunctions.SmoothBernoulliPoleCalibration.EvenPoleCalibrationAndLogMomentPinning

/-!
# Master Theorem: Smooth-Tapered Higher-Order Bernoulli Elimination and Even-Pole Calibration

This file assembles the four legs of §1.3 Mechanism 2 of Project Argon into a single
unconditional theorem (`smooth_bernoulli_pole_calibration_master_theorem`) and proves the
balanced-scale boundary contrast (`subbalanced_vs_balanced_bernoulli_scaling`) between the
sub-balanced regime `P ≪_L Q` and the balanced horizon `Q ≤ 2P`:

1. **Leg 1 (All-Order Cross-Scale Dual-Norm & Smooth Compression):**
   The order-`L` kernel statistic `higherOrderKernelStatistic N L c' d` controls the shifted
   cross-scale functional up to the order-`(L + 2)` tail (`abs_rowBilinear_sub_higherOrderKernelStatistic_le`),
   is attained by an adversarial sign pattern on any modulus set `S ⊆ Icc 1 N`
   (`exists_rowBilinear_ge_higherOrderDualNorm`), and for any `L`-smooth-tapered row at scale `Q`
   compresses the polynomial Bernoulli growth `p^{L+1}` across `p ≤ 2P` to `p * (P / Q)^L`
   (`sum_abs_higherOrderKernelStatistic_le_of_isSmoothTaperedAtScale`).
2. **Leg 2 (Smooth-Plus-Oscillatory Row Bridge & Coherent-Block Passage):**
   Splitting a large-scale row into an `L`-smooth-tapered baseline `c'_smooth` and an oscillatory
   arithmetic residual (`centredPrimeRow A H K`) simultaneously eliminates the polynomial
   Bernoulli tower on `c'_smooth` and passes the coherent-block obstruction on `centredPrimeRow`
   (`abs_crossScaleFunctional_add_le_of_isSmoothTaperedAtScale`,
   `exists_abs_crossScaleFunctional_smooth_add_centredPrimeRow_le`).
3. **Leg 3 (Simultaneous Odd–Even Pole Calibration Law):**
   For `0 < ε ≤ 1/2` and a kernel `k` on `[1, J]` vanishing on multiples of `4`, both
   `c = k ⋆ o` and its even flip `c^♭ = k^♭ ⋆ o` are `ReceiverBounded` if and only if both
   `poleValue (oddPartKernel k) J ε = 0` and `poleValue (evenPartWeight k) J ε = 0`
   (`both_evenFlip_pair_receiverBounded_iff_odd_and_even_pole`).
4. **Leg 4 (Logarithmic Moment Pinning & Fermi Horizon Separation):**
   On the generalized Fermi locus (`poleValue k J ε = 0`, `poleValue (evenPartWeight k) J ε ≠ 0`),
   `c` and `c^♭` share identical Ramanujan amplitudes at every modulus `e`, yet some logarithmic
   pronic moment `M(· log^m)` strictly separates them (`exists_logMoment_ne_of_fermi_evenFlip`),
   whereas equality of all logarithmic moments forces `c d = c^♭ d` for all `d ≥ 2`
   (`evenFlip_eq_of_logMoments_eq`).
-/

noncomputable section

open Finset Filter Topology BigOperators Real RHTower GaloisForLFunctions.BiScaleUncertainty

namespace GaloisForLFunctions.SmoothBernoulliPoleCalibration

open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.TransHorizonIncidenceMechanics

/-- **Sub-Balanced vs. Balanced Bernoulli Scaling Contrast.**
1. In the sub-balanced regime where `((L + 1).factorial : ℝ) * (P : ℝ)^L ≤ ε * (Q : ℝ)^L` (`1 ≤ Q`),
   the order-`L` smooth-tapered Bernoulli factor `((L + 1).factorial : ℝ) * (P / Q)^L` is at most `ε`.
2. In the balanced regime `Q ≤ P` (`1 ≤ Q`), for every order `L : ℕ`, the ratio `(P / Q)^L ≥ 1`
   ceases to damp the factorial growth `((L + 1).factorial : ℝ)`. -/
theorem subbalanced_vs_balanced_bernoulli_scaling (L P Q : ℕ) (ε : ℝ) (hQ : 1 ≤ Q) :
    (((L + 1).factorial : ℝ) * (P : ℝ) ^ L ≤ ε * (Q : ℝ) ^ L →
      ((L + 1).factorial : ℝ) * ((P : ℝ) / (Q : ℝ)) ^ L ≤ ε) ∧
    (Q ≤ P →
      ((L + 1).factorial : ℝ) ≤ ((L + 1).factorial : ℝ) * ((P : ℝ) / (Q : ℝ)) ^ L) := by
  have hQ_pos : (0 : ℝ) < (Q : ℝ) := by positivity
  have hQL_pos : (0 : ℝ) < (Q : ℝ) ^ L := pow_pos hQ_pos L
  constructor
  · intro h_sub
    rw [div_pow, mul_div_assoc', div_le_iff₀ hQL_pos]
    exact h_sub
  · intro h_bal
    have hPQ : (1 : ℝ) ≤ (P : ℝ) / (Q : ℝ) := by
      rw [ one_le_div hQ_pos]
      exact_mod_cast h_bal
    have hPQL : (1 : ℝ) ≤ ((P : ℝ) / (Q : ℝ)) ^ L := one_le_pow₀ hPQ
    exact le_mul_of_one_le_right (by positivity) hPQL

/-- **Four-Part Master Theorem of Smooth-Tapered Higher-Order Bernoulli Elimination and Even-Pole Calibration.** -/
theorem smooth_bernoulli_pole_calibration_master_theorem :
    -- Leg 1: All-order cross-scale dual-norm attainment & smooth-tapered compression
    (∀ (N L P Q : ℕ) (C₀ : ℝ) (S : Finset ℕ),
      S ⊆ Icc 1 N → (∀ p ∈ S, p.Prime ∧ p ≤ 2 * P) →
      ∀ (c' : ℕ → ℝ), IsSmoothTaperedAtScale N L Q C₀ c' →
        (∃ c : ℕ → ℝ,
          (∀ d, d ∉ S → c d = 0) ∧
          (∀ d ∈ S, |c d| = 1) ∧
          ∑ d ∈ S, |higherOrderKernelStatistic N L c' d| / (d : ℝ) -
            (2 : ℝ) ^ L * (L + 1).factorial *
              (∑ d ∈ S, (d : ℝ) ^ (L + 1)) * (∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ (L + 2)) ≤
            crossScaleFunctional N c c') ∧
        ∑ p ∈ S, |higherOrderKernelStatistic N L c' p| / (p : ℝ) ≤
          (2 * (L : ℝ) * (8 : ℝ) ^ L * (L + 1).factorial * C₀ *
            (∑ p ∈ S, (p : ℝ)) * ((P : ℝ) / (Q : ℝ)) ^ L +
          (L : ℝ) * (2 : ℝ) ^ L * L.factorial * (∑ p ∈ S, (1 : ℝ) / (p : ℝ))) *
            (∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2)) ∧
    -- Leg 2: Smooth-plus-oscillatory row bridge & coherent-block passage on `centredPrimeRow`
    (∀ {α : ℝ}, 7 / 12 < α → α < 1 → ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
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
          16 * ε * rowInverseSquareMass N (centredPrimeRow A H K) * rowLinearWeight N c) ∧
    -- Leg 3: Simultaneous odd-even pole calibration law for even-flip pairs over `oddSqfWeight`
    (∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 2 → ∀ {k : ℕ → ℝ}, (∀ m, 4 ∣ m → k m = 0) →
      ∀ {J : ℕ}, (∀ j, J < j → k j = 0) →
        ((ReceiverBounded (RHTower.dirichletConv k (oddSqfWeight ε)) ∧
          ReceiverBounded (RHTower.dirichletConv (flipKernelOf k) (oddSqfWeight ε))) ↔
          (poleValue (oddPartKernel k) J ε = 0 ∧ poleValue (evenPartWeight k) J ε = 0))) ∧
    -- Leg 4: Logarithmic moment separation on the generalized Fermi horizon
    (∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 2 → ∀ {k : ℕ → ℝ}, (∀ m, 4 ∣ m → k m = 0) →
      ∀ {J : ℕ}, (∀ j, J < j → k j = 0) →
        poleValue k J ε = 0 → poleValue (evenPartWeight k) J ε ≠ 0 →
        (∀ e, |weightRamanujanCoeff (RHTower.dirichletConv (flipKernelOf k) (oddSqfWeight ε)) e| =
          |weightRamanujanCoeff (RHTower.dirichletConv k (oddSqfWeight ε)) e|) ∧
        ReceiverBounded (RHTower.dirichletConv k (oddSqfWeight ε)) ∧
        ¬ ReceiverBounded (RHTower.dirichletConv (flipKernelOf k) (oddSqfWeight ε)) ∧
        ∃ m : ℕ,
          firstPronicMoment (logPowWeight (RHTower.dirichletConv k (oddSqfWeight ε)) m) ≠
            firstPronicMoment (logPowWeight (RHTower.dirichletConv (flipKernelOf k) (oddSqfWeight ε)) m)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro N L P Q C₀ S hS hp c' hsmooth
    exact ⟨exists_rowBilinear_ge_higherOrderDualNorm N L S hS c',
      sum_abs_higherOrderKernelStatistic_le_of_isSmoothTaperedAtScale N L P Q C₀ S hp c' hsmooth⟩
  · intro α hα hα1 ε hε hε1
    exact exists_abs_crossScaleFunctional_smooth_add_centredPrimeRow_le hα hα1 hε hε1
  · intro ε hε hε2 k hk4 J hkJ
    exact both_evenFlip_pair_receiverBounded_iff_odd_and_even_pole hε hε2 hk4 hkJ
  · intro ε hε hε2 k hk4 J hkJ hk0 he_ne
    exact exists_logMoment_ne_of_fermi_evenFlip hε hε2 hk4 hkJ hk0 he_ne

end GaloisForLFunctions.SmoothBernoulliPoleCalibration
