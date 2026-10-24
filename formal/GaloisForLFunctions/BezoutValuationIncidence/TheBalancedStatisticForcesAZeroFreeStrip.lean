import GaloisForLFunctions.BezoutValuationIncidence.TheMoebiusTailStatisticAtLargeModuli
import GaloisForLFunctions.BezoutValuationIncidence.TheDualNormAtCompositeModuli
import GaloisForLFunctions.BezoutValuationIncidence.ShortWindowMoebiusSavingIsTheQuasiRiemannHypothesis
import GaloisForLFunctions.RHTower.MobiusHilbertLogarithmicMertensBound

/-!
# A power saving for the balanced statistic forces a zero-free strip

Suppose the statistics of the Möbius windows have a power saving on a neighbourhood of the
diagonal, `|Λ_d(μ𝟙_{(Q,2Q]})| ≤ C (d²/Q) Q^{-η}` for `Q^{1-ε} ≤ d ≤ Q^{1+ε}`
(`BalancedStatisticPowerSaving`). Take a modulus `d ≈ X^{1+ε}`. The windows beyond `X` split into
band windows (the hypothesis) and windows beyond `d^{1+ε}` (the minor-arc law,
`abs_kernelStatisticAll_moebiusWindowRow_le_cutoff`); their sum is the tail of the Möbius row, which
by the inversion law and the near-origin kernel bound is `(π²/24) d² Σ_{n > X} μ(n)/n²` up to
`O(d log² d)`. Hence `Σ_{n ≤ X} μ(n)/n² = 6/π² + O(X^{-1-κ})`; Abel summation gives
`M(X) ≪ X^{1-κ}`, and the absolute-moment law gives `Θ ≤ 1 - κ`
(`zetaZeroAbscissa_lt_one_of_balancedStatisticPowerSaving`).
-/

open Finset Filter Topology ArithmeticFunction RHTower
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- A power saving for the statistic of the Möbius windows on a neighbourhood
`Q^{1-ε} ≤ d ≤ Q^{1+ε}` of the diagonal. -/
def BalancedStatisticPowerSaving : Prop :=
  ∃ ε η C : ℝ, 0 < ε ∧ 0 < η ∧ ∀ Q d : ℕ, 2 ≤ Q → (Q : ℝ) ^ (1 - ε) ≤ d →
    (d : ℝ) ≤ (Q : ℝ) ^ (1 + ε) →
      |kernelStatisticAll (2 * Q) (moebiusWindowRow Q) d| ≤ C * ((d : ℝ) ^ 2 / Q) * (Q : ℝ) ^ (-η)

/-- The partial sums `S₂(X) = Σ_{n ≤ X} μ(n)/n²`. -/
def moebiusSqSum (X : ℕ) : ℝ := ∑ n ∈ Ioc 0 X, (μ n : ℝ) / (n : ℝ) ^ 2

/-! ## §1. Elementary bounds -/

/-- `Σ_{i<k} (2^i X)^{-a} ≤ 4 X^{-a}` for `a ≥ 1/2`. -/
theorem sum_range_two_pow_mul_rpow_neg_le {a : ℝ} (ha : 1 / 2 ≤ a) {X : ℕ} (hX : 1 ≤ X) (k : ℕ) :
    ∑ i ∈ range k, ((2 ^ i * X : ℕ) : ℝ) ^ (-a) ≤ 4 * (X : ℝ) ^ (-a) := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  set r : ℝ := (2 : ℝ) ^ (-a) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr34 : r ≤ 3 / 4 := by
    have h1 : (2 : ℝ) ^ (-a) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 4 := by
      rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      rw [show ((3 : ℝ) / 4)⁻¹ = Real.sqrt ((4 / 3) ^ 2) by
        rw [Real.sqrt_sq (by norm_num)]; norm_num]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  have e : ∀ i : ℕ, ((2 ^ i * X : ℕ) : ℝ) ^ (-a) = r ^ i * (X : ℝ) ^ (-a) := fun i => by
    push_cast
    rw [Real.mul_rpow (by positivity) hX0.le, hr, ← Real.rpow_natCast ((2 : ℝ) ^ (-a)),
      ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast (2 : ℝ), ← Real.rpow_mul (by norm_num)]
    ring_nf
  rw [sum_congr rfl fun i _ => e i, ← sum_mul]
  have hg : ∑ i ∈ range k, r ^ i ≤ 4 := by
    have h := geom_sum_Ico_le_of_lt_one hr0 (by linarith : r < 1) (m := 0) (n := k)
    rw [← range_eq_Ico, pow_zero] at h
    refine h.trans ?_
    rw [div_le_iff₀ (by linarith)]
    linarith
  exact mul_le_mul_of_nonneg_right hg (Real.rpow_nonneg hX0.le _)

/-- `1 + log x ≤ (1 + 1/θ) x^θ` for `x ≥ 1`, `θ > 0`. -/
theorem one_add_log_le_rpow {x θ : ℝ} (hx : 1 ≤ x) (hθ : 0 < θ) :
    1 + Real.log x ≤ (1 + 1 / θ) * x ^ θ := by
  have h1 := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ x) hθ
  have h2 : 1 ≤ x ^ θ := Real.one_le_rpow hx hθ.le
  have e : x ^ θ / θ = 1 / θ * x ^ θ := by ring
  nlinarith

/-- `m_d ≤ d`. -/
theorem kernelMean_le_self {d : ℕ} (hd : 0 < d) : kernelMean d ≤ d := by
  have h1 := kernelMean_le hd
  have h2 : ((d.divisors.card : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.card_divisors_le_self d
  have hpi : Real.pi ^ 2 / 72 ≤ 1 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have h0 : 0 ≤ ((d.divisors.card : ℕ) : ℝ) - 1 := by
    have : 1 ≤ d.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hd.ne'⟩
    have : (1 : ℝ) ≤ ((d.divisors.card : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  calc kernelMean d ≤ Real.pi ^ 2 / 72 * (((d.divisors.card : ℕ) : ℝ) - 1) := h1
    _ ≤ 1 * (d : ℝ) := mul_le_mul hpi (by linarith) h0 (by norm_num)
    _ = d := one_mul _

/-! ## §2. The tail of `μ(n)/n²` from the statistic of the tail -/

/-- **The tail relation.** If the full-row value and the head differ by at most `B`, then
`|S₂(X) - 6/π²| ≤ (8/3)(B + 5d(1 + log d)(1 + log X) + 2d)/d²`. -/
theorem abs_moebiusSqSum_sub_le {d X : ℕ} (hd : 0 < d) (hX : 1 ≤ X) {B : ℝ}
    (hB : |2 * cubicPotential d 1 - 6 / Real.pi ^ 2 * kernelMean d -
      ∑ n ∈ Ioc 0 X, (μ n : ℝ) * kernelTerm d n| ≤ B) :
    |moebiusSqSum X - 6 / Real.pi ^ 2| ≤
      8 / 3 * ((B + 5 * (d : ℝ) * (1 + Real.log d) * (1 + Real.log X) + 2 * (d : ℝ)) /
        (d : ℝ) ^ 2) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hhead := abs_sum_moebius_mul_kernelTerm_sub_le hd hX
  set E := 2 * cubicPotential d 1 - 6 / Real.pi ^ 2 * kernelMean d with hEdef
  set H := ∑ n ∈ Ioc 0 X, (μ n : ℝ) * kernelTerm d n
  set S := ∑ n ∈ Ioc 0 X, (μ n : ℝ) / (n : ℝ) ^ 2
  have hE : |E - (d : ℝ) ^ 2 / 4| ≤ 2 * (d : ℝ) := by
    rw [hEdef, two_mul_cubicPotential_one hd]
    have hm0 := kernelMean_nonneg hd
    have hm := kernelMean_le_self hd
    have hpi : 6 / Real.pi ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
    have hpi0 : 0 ≤ 6 / Real.pi ^ 2 := by positivity
    have t : 6 / Real.pi ^ 2 * kernelMean d ≤ d := (mul_le_of_le_one_left hm0 hpi).trans hm
    have t0 : 0 ≤ 6 / Real.pi ^ 2 * kernelMean d := mul_nonneg hpi0 hm0
    have e : ((d : ℝ) - 1) * ((d : ℝ) - 3) / 4 - (d : ℝ) ^ 2 / 4 = (3 - 4 * (d : ℝ)) / 4 := by ring
    rw [abs_le]; constructor <;> linarith
  have h3 : |Real.pi ^ 2 / 24 * (d : ℝ) ^ 2 * S - (d : ℝ) ^ 2 / 4| ≤
      |Real.pi ^ 2 / 24 * (d : ℝ) ^ 2 * S - H| + |H - E| + |E - (d : ℝ) ^ 2 / 4| := by
    have := abs_add_three (Real.pi ^ 2 / 24 * (d : ℝ) ^ 2 * S - H) (H - E) (E - (d : ℝ) ^ 2 / 4)
    rwa [show Real.pi ^ 2 / 24 * (d : ℝ) ^ 2 * S - H + (H - E) + (E - (d : ℝ) ^ 2 / 4) =
      Real.pi ^ 2 / 24 * (d : ℝ) ^ 2 * S - (d : ℝ) ^ 2 / 4 by ring] at this
  rw [abs_sub_comm] at hhead hB
  have hd2 : 0 < Real.pi ^ 2 / 24 * (d : ℝ) ^ 2 := by positivity
  have key : Real.pi ^ 2 / 24 * (d : ℝ) ^ 2 * |S - 6 / Real.pi ^ 2| ≤
      B + 5 * (d : ℝ) * (1 + Real.log d) * (1 + Real.log X) + 2 * (d : ℝ) := by
    have e : Real.pi ^ 2 / 24 * (d : ℝ) ^ 2 * (S - 6 / Real.pi ^ 2) =
        Real.pi ^ 2 / 24 * (d : ℝ) ^ 2 * S - (d : ℝ) ^ 2 / 4 := by
      field_simp; ring
    rw [← abs_of_pos hd2, ← abs_mul, e]
    linarith
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hB
  have hnum : 0 ≤ B + 5 * (d : ℝ) * (1 + Real.log d) * (1 + Real.log X) + 2 * (d : ℝ) := by
    have := Real.log_nonneg hdR
    have := Real.log_nonneg (by exact_mod_cast hX : (1 : ℝ) ≤ X)
    positivity
  have hpi2 : 3 / 8 ≤ Real.pi ^ 2 / 24 := by nlinarith [Real.pi_gt_three]
  show |S - 6 / Real.pi ^ 2| ≤ _
  calc |S - 6 / Real.pi ^ 2| = Real.pi ^ 2 / 24 * (d : ℝ) ^ 2 * |S - 6 / Real.pi ^ 2| /
        (Real.pi ^ 2 / 24 * (d : ℝ) ^ 2) := by field_simp
    _ ≤ (B + 5 * (d : ℝ) * (1 + Real.log d) * (1 + Real.log X) + 2 * (d : ℝ)) /
        (Real.pi ^ 2 / 24 * (d : ℝ) ^ 2) := div_le_div_of_nonneg_right key hd2.le
    _ ≤ (B + 5 * (d : ℝ) * (1 + Real.log d) * (1 + Real.log X) + 2 * (d : ℝ)) /
        (3 / 8 * (d : ℝ) ^ 2) :=
        div_le_div_of_nonneg_left hnum (by positivity) (by nlinarith)
    _ = _ := by field_simp

/-! ## §3. Abel summation -/

/-- `M(X) = X² D(X) - Σ_{n<X} (2n + 1) D(n)` with `D(n) = S₂(n) - 6/π²`. -/
theorem mertensM_eq_abel (X : ℕ) :
    RHTower.Sieve.mertensM X = (X : ℝ) ^ 2 * (moebiusSqSum X - 6 / Real.pi ^ 2) -
      ∑ n ∈ range X, (2 * (n : ℝ) + 1) * (moebiusSqSum n - 6 / Real.pi ^ 2) := by
  induction X with
  | zero => simp [RHTower.Sieve.mertensM]
  | succ X ih =>
    have hS : moebiusSqSum (X + 1) = moebiusSqSum X + (μ (X + 1) : ℝ) / ((X : ℝ) + 1) ^ 2 := by
      unfold moebiusSqSum
      rw [sum_Ioc_succ_top (Nat.zero_le X)]
      push_cast
      ring
    have hM : RHTower.Sieve.mertensM (X + 1) =
        RHTower.Sieve.mertensM X + (μ (X + 1) : ℝ) := by
      unfold RHTower.Sieve.mertensM
      rw [Finset.sum_range_succ _ (X + 1)]
    rw [hM, ih, hS, Finset.sum_range_succ]
    have hX1 : ((X : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- **Abel summation.** If `|S₂(n) - 6/π²| ≤ C n^{-1-κ}` for `n ≥ 1`, `0 < κ < 1`, then
`|M(X)| ≤ (C + 1 + 3C/(1 - κ)) (X + 1)^{1-κ}`. -/
theorem abs_mertensM_le_of_moebiusSqSum {C κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (hC : 0 ≤ C)
    (hD : ∀ n : ℕ, 1 ≤ n → |moebiusSqSum n - 6 / Real.pi ^ 2| ≤ C * (n : ℝ) ^ (-1 - κ))
    (X : ℕ) :
    |RHTower.Sieve.mertensM X| ≤ (C + 1 + 3 * C / (1 - κ)) * ((X : ℝ) + 1) ^ (1 - κ) := by
  have h1κ : 0 < 1 - κ := by linarith
  have hX1 : (1 : ℝ) ≤ (X : ℝ) + 1 := by linarith [(Nat.cast_nonneg X : (0 : ℝ) ≤ X)]
  have hpow1 : 1 ≤ ((X : ℝ) + 1) ^ (1 - κ) := Real.one_le_rpow hX1 h1κ.le
  rw [mertensM_eq_abel]
  rcases Nat.eq_zero_or_pos X with rfl | hXpos
  · simp; positivity
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hXpos
  -- the boundary term
  have hT1 : |(X : ℝ) ^ 2 * (moebiusSqSum X - 6 / Real.pi ^ 2)| ≤ C * ((X : ℝ) + 1) ^ (1 - κ) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc (X : ℝ) ^ 2 * |moebiusSqSum X - 6 / Real.pi ^ 2| ≤ (X : ℝ) ^ 2 * (C * (X : ℝ) ^ (-1 - κ)) :=
          mul_le_mul_of_nonneg_left (hD X hXpos) (by positivity)
      _ = C * (X : ℝ) ^ (1 - κ) := by
          rw [mul_left_comm, ← Real.rpow_natCast (X : ℝ) 2, ← Real.rpow_add (by linarith)]
          congr 2; push_cast; ring
      _ ≤ C * ((X : ℝ) + 1) ^ (1 - κ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) (by linarith) h1κ.le) hC
  -- the interior terms
  have hT2 : |∑ n ∈ range X, (2 * (n : ℝ) + 1) * (moebiusSqSum n - 6 / Real.pi ^ 2)| ≤
      1 + 3 * C / (1 - κ) * ((X : ℝ) + 1) ^ (1 - κ) := by
    rw [range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hXpos]
    have h0 : |(2 * ((0 : ℕ) : ℝ) + 1) * (moebiusSqSum 0 - 6 / Real.pi ^ 2)| ≤ 1 := by
      simp only [moebiusSqSum, Ioc_self, sum_empty, Nat.cast_zero, mul_zero, zero_add, one_mul,
        zero_sub, abs_neg]
      rw [abs_of_pos (by positivity), div_le_one (by positivity)]
      nlinarith [Real.pi_gt_three]
    have hterm : ∀ n ∈ Ico (0 + 1) X, |(2 * (n : ℝ) + 1) * (moebiusSqSum n - 6 / Real.pi ^ 2)| ≤
        3 * C * (((n - 1 : ℕ) : ℝ) + 1) ^ (-κ) := by
      intro n hn
      have hn1 : 1 ≤ n := (mem_Ico.mp hn).1
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hcast : (((n - 1 : ℕ) : ℝ) + 1) = n := by
        rw [Nat.cast_sub hn1]; push_cast; ring
      rw [hcast, abs_mul, abs_of_pos (by positivity)]
      calc (2 * (n : ℝ) + 1) * |moebiusSqSum n - 6 / Real.pi ^ 2|
          ≤ (3 * (n : ℝ)) * (C * (n : ℝ) ^ (-1 - κ)) :=
            mul_le_mul (by linarith) (hD n hn1) (abs_nonneg _) (by positivity)
        _ = 3 * C * (n : ℝ) ^ (-κ) := by
            rw [show (-1 - κ : ℝ) = -1 + -κ by ring, Real.rpow_add (by linarith),
              Real.rpow_neg_one]
            field_simp
    have hsum : ∑ n ∈ Ico (0 + 1) X, 3 * C * (((n - 1 : ℕ) : ℝ) + 1) ^ (-κ) ≤
        3 * C / (1 - κ) * ((X : ℝ) + 1) ^ (1 - κ) := by
      rw [← mul_sum, Finset.sum_Ico_eq_sum_range]
      simp only [zero_add, Nat.add_sub_cancel_left]
      have h := RHTower.sum_range_rpow_neg_le κ hκ0 hκ1 (X - 1)
      calc 3 * C * ∑ k ∈ range (X - 1), ((k : ℝ) + 1) ^ (-κ)
          ≤ 3 * C * (((X - 1 : ℕ) : ℝ) ^ (1 - κ) / (1 - κ)) := mul_le_mul_of_nonneg_left h (by positivity)
        _ ≤ 3 * C * (((X : ℝ) + 1) ^ (1 - κ) / (1 - κ)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine div_le_div_of_nonneg_right ?_ h1κ.le
            refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ h1κ.le
            have : ((X - 1 : ℕ) : ℝ) ≤ X := by exact_mod_cast Nat.sub_le X 1
            linarith
        _ = 3 * C / (1 - κ) * ((X : ℝ) + 1) ^ (1 - κ) := by ring
    calc |(2 * ((0 : ℕ) : ℝ) + 1) * (moebiusSqSum 0 - 6 / Real.pi ^ 2) +
          ∑ n ∈ Ico (0 + 1) X, (2 * (n : ℝ) + 1) * (moebiusSqSum n - 6 / Real.pi ^ 2)|
        ≤ 1 + ∑ n ∈ Ico (0 + 1) X, 3 * C * (((n - 1 : ℕ) : ℝ) + 1) ^ (-κ) :=
          (abs_add_le _ _).trans (add_le_add h0 ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)))
      _ ≤ _ := by linarith
  calc |(X : ℝ) ^ 2 * (moebiusSqSum X - 6 / Real.pi ^ 2) -
        ∑ n ∈ range X, (2 * (n : ℝ) + 1) * (moebiusSqSum n - 6 / Real.pi ^ 2)|
      ≤ C * ((X : ℝ) + 1) ^ (1 - κ) + (1 + 3 * C / (1 - κ) * ((X : ℝ) + 1) ^ (1 - κ)) :=
        (abs_sub _ _).trans (add_le_add hT1 hT2)
    _ ≤ (C + 1 + 3 * C / (1 - κ)) * ((X : ℝ) + 1) ^ (1 - κ) := by nlinarith

/-- **A power saving of `S₂` past `X^{-1}` is a zero-free strip.** -/
theorem zetaZeroAbscissa_le_of_moebiusSqSum {C κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (hC : 0 ≤ C)
    (hD : ∀ n : ℕ, 1 ≤ n → |moebiusSqSum n - 6 / Real.pi ^ 2| ≤ C * (n : ℝ) ^ (-1 - κ)) :
    zetaZeroAbscissa ≤ 1 - κ := by
  set K := C + 1 + 3 * C / (1 - κ)
  have hK : 0 ≤ K := by have : 0 < 1 - κ := by linarith
                        positivity
  have hM := abs_mertensM_le_of_moebiusSqSum hκ0 hκ1 hC hD
  have hsum : ∀ X : ℕ, ∑ k ∈ range (X + 1), ‖mobiusMertensPartialSum k‖ ≤
      K * ((X : ℝ) + 1) ^ (2 - κ) := by
    intro X
    calc ∑ k ∈ range (X + 1), ‖mobiusMertensPartialSum k‖
        ≤ ∑ _k ∈ range (X + 1), K * ((X : ℝ) + 1) ^ (1 - κ) := by
          refine sum_le_sum fun k hk => ?_
          rw [norm_mobiusMertensPartialSum_eq]
          refine (hM k).trans (mul_le_mul_of_nonneg_left ?_ hK)
          have : (k : ℝ) ≤ X := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hk)
          exact Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      _ = K * ((X : ℝ) + 1) ^ (2 - κ) := by
          rw [sum_const, card_range, nsmul_eq_mul,
            show (2 - κ : ℝ) = 1 + (1 - κ) by ring, Real.rpow_add (by positivity), Real.rpow_one]
          push_cast; ring
  have := zetaZeroAbscissa_le_of_sum_norm_mertens_le (by linarith : (1 : ℝ) ≤ 2 - κ) hsum
  linarith

end

end GaloisForLFunctions.BezoutValuationIncidence
