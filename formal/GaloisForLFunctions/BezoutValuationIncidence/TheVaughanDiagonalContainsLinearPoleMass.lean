import GaloisForLFunctions.BezoutValuationIncidence.CompletePronicVaughanCalibration
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Linear pole mass in the Vaughan Gram

The density component forces linear diagonal energy for every choice of Vaughan
cutoffs. The interior energy is sublinear by the absolutely convergent divisor mean
theorem. Consequently the mixed part cancels an asymptotic fraction one of the
diagonal, even when both cutoffs vary with the horizon. Relative cancellation alone
does not bound the residual energy.
-/

open Finset Filter RHTower
open GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators Topology

noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence

set_option autoImplicit false

/-- The diagonal budget of the five-component Vaughan decomposition. -/
def pmPronicVaughanDiagonal (ε : ℝ) (U V T : ℕ) : ℝ :=
  ∑ i : Fin 5, pmPronicVaughanGram ε U V T i i

/-- The pole component is independent of the Vaughan cutoffs. -/
theorem pmPronicVaughanPiece_pole (ε : ℝ) (U V n : ℕ) :
    pmPronicVaughanPiece ε U V n 4 =
      -(pmPowerDampedDivisorDensity ε).re * n -
        addDiff (pmActiveSawtoothComponent ε) n := by
  simp only [pmPronicVaughanPiece, Matrix.cons_val_succ, Matrix.cons_val_zero]

theorem pmPronicVaughanGram_diag_nonneg (ε : ℝ) (U V T : ℕ) (i : Fin 5) :
    0 ≤ pmPronicVaughanGram ε U V T i i := by
  unfold pmPronicVaughanGram
  exact sum_nonneg fun n _ => div_nonneg (mul_self_nonneg _) (Nat.cast_nonneg _)

theorem pmPronicVaughanGram_pole_le_diagonal (ε : ℝ) (U V T : ℕ) :
    pmPronicVaughanGram ε U V T 4 4 ≤ pmPronicVaughanDiagonal ε U V T :=
  single_le_sum (fun i _ => pmPronicVaughanGram_diag_nonneg ε U V T i) (mem_univ 4)

/-- A linear lower bound from the pole component, uniform in both cutoffs. -/
theorem pmPronicVaughanGram_pole_linear_lower {ε : ℝ} (hε : 0 ≤ ε) (U V T : ℕ) :
    (pmPowerDampedDivisorDensity ε).re ^ 2 / 4 * T - 1 / 4 ≤
      pmPronicVaughanGram ε U V T 4 4 := by
  let ρ := (pmPowerDampedDivisorDensity ε).re
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 T) :
      ρ ^ 2 / 4 - (1 / 4 : ℝ) / (pronicSeq n : ℝ) ≤
        pmPronicVaughanPiece ε U V n 4 * pmPronicVaughanPiece ε U V n 4 /
          (pronicSeq n : ℝ) := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    have hden : (0 : ℝ) < pronicSeq n := by
      simp only [pronicSeq, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      positivity
    have ha := (addDiff_pmActiveSawtoothComponent_sq_le_quarter hε n).2
    have hs := sq_nonneg (ρ * n + 2 * addDiff (pmActiveSawtoothComponent ε) n)
    have hn' : (pronicSeq n : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by
      simp only [pronicSeq, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      nlinarith only [hn1]
    have hm := mul_le_mul_of_nonneg_left hn' (sq_nonneg ρ)
    simp only [pmPronicVaughanPiece_pole]
    apply (le_div_iff₀ hden).mpr
    rw [sub_mul, div_mul_cancel₀ _ hden.ne']
    change (ρ ^ 2 / 4) * (pronicSeq n : ℝ) - 1 / 4 ≤
      (-ρ * n - addDiff (pmActiveSawtoothComponent ε) n) *
        (-ρ * n - addDiff (pmActiveSawtoothComponent ε) n)
    nlinarith only [hs, ha, hm]
  have hsum := sum_le_sum hpoint
  have hrecip := sum_one_div_pronicSeq_le_one T
  simp only [sum_sub_distrib, sum_const, Nat.card_Icc, Nat.add_sub_cancel,
    nsmul_eq_mul, div_eq_mul_inv, ← mul_sum] at hsum hrecip
  change ρ ^ 2 / 4 * T - 1 / 4 ≤ _
  unfold pmPronicVaughanGram
  nlinarith only [hsum, hrecip]

/-- The full diagonal retains the pole's linear lower bound. -/
theorem pmPronicVaughanDiagonal_linear_lower {ε : ℝ} (hε : 0 ≤ ε) (U V T : ℕ) :
    (pmPowerDampedDivisorDensity ε).re ^ 2 / 4 * T - 1 / 4 ≤
      pmPronicVaughanDiagonal ε U V T :=
  (pmPronicVaughanGram_pole_linear_lower hε U V T).trans
    (pmPronicVaughanGram_pole_le_diagonal ε U V T)

private theorem tendsto_activePair_div_nat {ε : ℝ} (hε : 0 ≤ ε) :
    Tendsto (fun n : ℕ => addDiff (pmActiveSawtoothComponent ε) n / n)
      atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero, Real.norm_eq_abs, abs_div, abs_of_nonneg (Nat.cast_nonneg _)]
  exact squeeze_zero
    (fun n => div_nonneg (abs_nonneg _) (Nat.cast_nonneg n))
    (fun n => div_le_div_of_nonneg_right
      (abs_addDiff_pmActiveSawtoothComponent_le_half hε n) (Nat.cast_nonneg n))
    (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)

/-- Absolute convergence of the divisor density makes the interior prefix sublinear. -/
theorem tendsto_pmBezoutInteriorPrefix_div_nat {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => pmBezoutInteriorPrefix ε n / n) atTop (𝓝 0) := by
  have hm := (tendsto_pmPowerDampedDivisorSum_div_real hε).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hc : Tendsto (fun n : ℕ => pmPowerDampedCenteredDivisorPrefix ε n / n)
      atTop (𝓝 0) := by
    have h := hm.sub (tendsto_const_nhds (x := (pmPowerDampedDivisorDensity ε).re))
    simp only [sub_self] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    simp only [Function.comp_def, pmPowerDampedDivisorSum, Nat.floor_natCast,
      pmPowerDampedCenteredDivisorPrefix_eq, sub_div, mul_div_cancel_right₀ _ hn0]
  have h := hc.sub (tendsto_activePair_div_nat hε.le)
  simp only [sub_zero] at h
  convert h using 1
  ext n
  rw [pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior]
  ring

private theorem tendsto_pronic_pair_mean {f g : ℕ → ℝ} {a b : ℝ}
    (hf : Tendsto (fun n : ℕ => f n / n) atTop (𝓝 a))
    (hg : Tendsto (fun n : ℕ => g n / n) atTop (𝓝 b)) :
    Tendsto (fun T : ℕ => (∑ n ∈ Icc 1 T, f n * g n / (pronicSeq n : ℝ)) / T)
      atTop (𝓝 (a * b)) := by
  have hr : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1) :=
    tendsto_natCast_div_add_atTop 1
  have hp : Tendsto (fun n : ℕ => f n * g n / (pronicSeq n : ℝ))
      atTop (𝓝 (a * b)) := by
    have h := (hf.mul hg).mul hr
    simp only [mul_one] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    simp only [pronicSeq, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp [hn0]
    <;> ring
  have h := (hp.comp (tendsto_add_atTop_nat 1)).cesaro
  convert h using 1
  ext T
  rw [Finset.range_eq_Ico, Finset.sum_Ico_add' _ 0 T (c := 1)]
  simp only [zero_add, Finset.Ico_add_one_right_eq_Icc, div_eq_mul_inv, mul_comm]

/-- The interior energy is sublinear for every positive damping, without a zero-free input. -/
theorem tendsto_pmBezoutInteriorPronicEnergy_div_nat {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun T : ℕ => pmBezoutInteriorPronicEnergy ε T / T) atTop (𝓝 0) := by
  simpa only [pmBezoutInteriorPronicEnergy, ← sq, mul_zero] using
    tendsto_pronic_pair_mean (tendsto_pmBezoutInteriorPrefix_div_nat hε)
      (tendsto_pmBezoutInteriorPrefix_div_nat hε)

/-- The fifth component has the same linear asymptotic at every pair of cutoffs. -/
theorem tendsto_pmPronicVaughanPiece_pole_div_nat {ε : ℝ} (hε : 0 ≤ ε)
    (U V : ℕ) :
    Tendsto (fun n : ℕ => pmPronicVaughanPiece ε U V n 4 / n)
      atTop (𝓝 (-(pmPowerDampedDivisorDensity ε).re)) := by
  have h := (tendsto_const_nhds (x := -(pmPowerDampedDivisorDensity ε).re)).sub
    (tendsto_activePair_div_nat hε)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [pmPronicVaughanPiece_pole, sub_div, mul_div_cancel_right₀ _ hn0]

/-- The pole diagonal has exact positive linear density, even along moving cutoffs. -/
theorem tendsto_pmPronicVaughanGram_pole_div_nat {ε : ℝ} (hε : 0 ≤ ε)
    (U V : ℕ → ℕ) :
    Tendsto (fun T : ℕ => pmPronicVaughanGram ε (U T) (V T) T 4 4 / T)
      atTop (𝓝 ((pmPowerDampedDivisorDensity ε).re ^ 2)) := by
  have h := tendsto_pronic_pair_mean
    (tendsto_pmPronicVaughanPiece_pole_div_nat hε 0 0)
    (tendsto_pmPronicVaughanPiece_pole_div_nat hε 0 0)
  simpa only [pmPronicVaughanGram, pmPronicVaughanPiece_pole, neg_mul_neg, ← sq] using h

/-- The off-diagonal portion of the pole row, with one orientation retained. -/
def pmPronicVaughanPoleMixed (ε : ℝ) (U V T : ℕ) : ℝ :=
  (∑ j : Fin 5, pmPronicVaughanGram ε U V T 4 j) -
    pmPronicVaughanGram ε U V T 4 4

theorem sum_pmPronicVaughanGram_pole_row (ε : ℝ) (U V T : ℕ) :
    (∑ j : Fin 5, pmPronicVaughanGram ε U V T 4 j) =
      ∑ n ∈ Icc 1 T, pmPronicVaughanPiece ε 0 0 n 4 * pmBezoutInteriorPrefix ε n /
        (pronicSeq n : ℝ) := by
  unfold pmPronicVaughanGram
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  rw [← sum_div, ← mul_sum, sum_pmPronicVaughanPiece]
  rw [pmPronicVaughanPiece_pole, pmPronicVaughanPiece_pole]

/-- The complete mixed pole row is independent of both cutoffs. -/
theorem pmPronicVaughanPoleMixed_eq_zero_cutoffs (ε : ℝ) (U V T : ℕ) :
    pmPronicVaughanPoleMixed ε U V T = pmPronicVaughanPoleMixed ε 0 0 T := by
  simp only [pmPronicVaughanPoleMixed, sum_pmPronicVaughanGram_pole_row,
    pmPronicVaughanGram, pmPronicVaughanPiece_pole]

/-- Exactly four off-diagonal entries comprise the pole row. -/
theorem pmPronicVaughanPoleMixed_eq_four (ε : ℝ) (U V T : ℕ) :
    pmPronicVaughanPoleMixed ε U V T =
      pmPronicVaughanGram ε U V T 4 0 + pmPronicVaughanGram ε U V T 4 1 +
      pmPronicVaughanGram ε U V T 4 2 + pmPronicVaughanGram ε U V T 4 3 := by
  simp only [pmPronicVaughanPoleMixed, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  ring

/-- The mixed pole row has exact negative linear density. -/
theorem tendsto_pmPronicVaughanPoleMixed_div_nat {ε : ℝ} (hε : 0 < ε)
    (U V : ℕ → ℕ) :
    Tendsto (fun T : ℕ => pmPronicVaughanPoleMixed ε (U T) (V T) T / T)
      atTop (𝓝 (-(pmPowerDampedDivisorDensity ε).re ^ 2)) := by
  have hrow := tendsto_pronic_pair_mean
    (tendsto_pmPronicVaughanPiece_pole_div_nat hε.le 0 0)
    (tendsto_pmBezoutInteriorPrefix_div_nat hε)
  have hpole := tendsto_pmPronicVaughanGram_pole_div_nat hε.le U V
  have h := hrow.sub hpole
  simpa only [pmPronicVaughanPoleMixed, sum_pmPronicVaughanGram_pole_row,
    sub_div, mul_zero, zero_sub] using h

/-- No choice of cutoffs makes all uncentered pole cross entries sublinear. -/
theorem not_all_pmPronicVaughan_pole_cross_entries_sublinear {ε : ℝ} (hε : 0 < ε)
    (U V : ℕ → ℕ) :
    ¬ (∀ j : Fin 5, j ≠ 4 →
      Tendsto (fun T : ℕ => pmPronicVaughanGram ε (U T) (V T) T 4 j / T)
        atTop (𝓝 0)) := by
  intro h
  have hzero := (((h 0 (by omega)).add (h 1 (by omega))).add
    (h 2 (by omega))).add (h 3 (by omega))
  have hzero' : Tendsto
      (fun T : ℕ => pmPronicVaughanPoleMixed ε (U T) (V T) T / T) atTop (𝓝 0) := by
    simpa only [pmPronicVaughanPoleMixed_eq_four, add_div, add_zero] using hzero
  have heq := tendsto_nhds_unique (tendsto_pmPronicVaughanPoleMixed_div_nat hε U V) hzero'
  have hρ := pmPowerDampedDivisorDensity_re_pos hε
  nlinarith only [heq, sq_pos_of_pos hρ]

/-- Relative mixed cancellation approaches one uniformly over all Vaughan cutoffs. -/
theorem eventually_pmPronicVaughan_relative_cancellation {ε : ℝ} (hε : 0 < ε)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℕ in atTop, ∀ U V : ℕ,
      0 < pmPronicVaughanDiagonal ε U V T ∧
        |pmPronicVaughanMixedRemainder ε U V T / pmPronicVaughanDiagonal ε U V T + 1| ≤ η := by
  let ρ := (pmPowerDampedDivisorDensity ε).re
  have hρ : 0 < ρ := pmPowerDampedDivisorDensity_re_pos hε
  have hc : 0 < ρ ^ 2 / 8 := by positivity
  have he := (tendsto_pmBezoutInteriorPronicEnergy_div_nat hε).eventually
    (eventually_le_nhds (mul_pos hη hc))
  have ht : ∀ᶠ T : ℕ in atTop, 2 / ρ ^ 2 ≤ (T : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [he, ht, eventually_ge_atTop 1] with T hE hT hT1
  intro U V
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT1
  have hlarge : 2 ≤ ρ ^ 2 * T := by
    have := (div_le_iff₀ (sq_pos_of_pos hρ)).mp hT
    nlinarith only [this]
  have hdiag : ρ ^ 2 / 8 * T ≤ pmPronicVaughanDiagonal ε U V T := by
    have h := pmPronicVaughanDiagonal_linear_lower hε.le U V T
    change ρ ^ 2 / 4 * T - 1 / 4 ≤ _ at h
    linarith
  have hD : 0 < pmPronicVaughanDiagonal ε U V T :=
    (mul_pos hc hTpos).trans_le hdiag
  refine ⟨hD, ?_⟩
  have hid := pmInteriorPronicEnergy_eq_diagonal_add_mixed ε U V T
  change pmBezoutInteriorPronicEnergy ε T =
    pmPronicVaughanDiagonal ε U V T + pmPronicVaughanMixedRemainder ε U V T at hid
  have hratio : pmPronicVaughanMixedRemainder ε U V T / pmPronicVaughanDiagonal ε U V T + 1 =
      pmBezoutInteriorPronicEnergy ε T / pmPronicVaughanDiagonal ε U V T := by
    rw [hid, add_div, div_self hD.ne']
    ring
  rw [hratio, abs_of_nonneg (div_nonneg (pmBezoutInteriorPronicEnergy_nonneg ε T) hD.le)]
  apply (div_le_iff₀ hD).mpr
  have hE' := (div_le_iff₀ hTpos).mp hE
  have hD' := mul_le_mul_of_nonneg_left hdiag hη.le
  nlinarith only [hE', hD']

/-- Moving the cutoffs cannot change the limiting relative cancellation. -/
theorem tendsto_pmPronicVaughan_mixed_div_diagonal {ε : ℝ} (hε : 0 < ε)
    (U V : ℕ → ℕ) :
    Tendsto (fun T => pmPronicVaughanMixedRemainder ε (U T) (V T) T /
      pmPronicVaughanDiagonal ε (U T) (V T) T) atTop (𝓝 (-1)) := by
  apply Metric.tendsto_atTop.mpr
  intro η hη
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_pmPronicVaughan_relative_cancellation hε (half_pos hη))
  refine ⟨N, fun T hT => ?_⟩
  have h := (hN T hT (U T) (V T)).2
  rw [Real.dist_eq]
  simpa only [sub_neg_eq_add] using h.trans_lt (half_lt_self hη)

/-- The unnormalized error in relative cancellation is exactly the interior energy. -/
theorem pmPronicVaughan_cancellation_error (ε : ℝ) (U V T : ℕ) :
    pmPronicVaughanDiagonal ε U V T + pmPronicVaughanMixedRemainder ε U V T =
      pmBezoutInteriorPronicEnergy ε T :=
  (pmInteriorPronicEnergy_eq_diagonal_add_mixed ε U V T).symm

end GaloisForLFunctions.BezoutValuationIncidence
