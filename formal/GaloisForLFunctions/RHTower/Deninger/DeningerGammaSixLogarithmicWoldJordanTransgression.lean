import GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixSingularGreenStokesCoface

/-!
# Gamma-six logarithmic Wold--Jordan transgression

Differentiating the literal Gamma-six shell exponent before divisor specialization produces a
logarithmic generalized Wold eigenoperator. Its coface is the nonzero weak-trace principal source
class, while the logarithmic jet itself lies strictly above weak Schatten one and every positive
power regularization is trace class.

The construction is lifted to the actual corrected Möbius tensor source. Exponential convergence
of its tensor remainder survives the logarithmic shell factor, so the complete logarithmic coface
equals the full corrected principal source modulo rectangular trace class and is itself not trace
class. All statements are unconditional and pre-Xi; no target landing or RH claim is made.
-/

open Filter Topology

namespace RHTower

noncomputable section

def deningerGammaSixShellLogWeight (m : ℕ) : ℝ :=
  (m : ℝ) * Real.log 6 * (1 / 6 : ℝ) ^ m

theorem deningerGammaSixShellLogWeight_nonneg (m : ℕ) : 0 ≤ deningerGammaSixShellLogWeight m := by
  unfold deningerGammaSixShellLogWeight
  positivity

theorem deningerGammaSixShellLogWeight_succ_le (m : ℕ) (hm : 3 ≤ m) :
    deningerGammaSixShellLogWeight (m + 1) ≤ deningerGammaSixShellLogWeight m := by
  unfold deningerGammaSixShellLogWeight
  rw [pow_succ]
  have hlog : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hp : 0 ≤ (1 / 6 : ℝ) ^ m := by positivity
  have hmR : (m : ℝ) + 1 ≤ 6 * m := by
    exact_mod_cast (show m + 1 ≤ 6 * m by omega)
  have hfrac : ((m : ℝ) + 1) / 6 ≤ m := by linarith
  push_cast
  calc
    (↑m + 1) * Real.log 6 * ((1 / 6) ^ m * (1 / 6)) =
        (((m : ℝ) + 1) / 6) * (Real.log 6 * (1 / 6) ^ m) := by ring
    _ ≤ (m : ℝ) * (Real.log 6 * (1 / 6) ^ m) :=
      mul_le_mul_of_nonneg_right hfrac (mul_nonneg hlog.le hp)
    _ = (m : ℝ) * Real.log 6 * (1 / 6) ^ m := by ring

theorem deningerGammaSixShellLogWeight_antitoneOn :
    AntitoneOn deningerGammaSixShellLogWeight (Set.Ici 3) := by
  exact antitoneOn_nat_Ici_of_succ_le deningerGammaSixShellLogWeight_succ_le

def deningerGammaSixLogWeight (n : ℕ) : ℝ :=
  deningerGammaSixShellLogWeight (deningerGammaSixShellDepth n)

theorem deningerGammaSixLogWeight_antitone : Antitone deningerGammaSixLogWeight := by
  intro i j hij
  exact deningerGammaSixShellLogWeight_antitoneOn
    (three_le_deningerGammaSixShellDepth i)
    (three_le_deningerGammaSixShellDepth j)
    (deningerGammaSixShellDepth_mono hij)

def deningerGammaSixLogOperator : EllTwo →L[ℂ] EllTwo :=
  antitoneDiagonalOperator deningerGammaSixLogWeight
    (fun n => deningerGammaSixShellLogWeight_nonneg (deningerGammaSixShellDepth n))
    (fun {_ _} h => deningerGammaSixLogWeight_antitone h)

theorem deningerGammaSixLogWeight_wold (n : ℕ) :
    deningerGammaSixLogWeight (deningerGammaSixWoldCoordinate n) -
        (1 / 6 : ℝ) * deningerGammaSixLogWeight n =
      (Real.log 6 / 6) * deningerGammaSixShellEigenvalue n := by
  rw [deningerGammaSixLogWeight, deningerGammaSixLogWeight, deningerGammaSixShellDepth_wold]
  unfold deningerGammaSixShellLogWeight deningerGammaSixShellEigenvalue
  rw [pow_succ]
  push_cast
  ring

theorem approxNumber_deningerGammaSixLogOperator (n : ℕ) :
    approxNumber deningerGammaSixLogOperator n = deningerGammaSixLogWeight n := by
  exact approxNumber_antitoneDiagonalOperator_eq _
    (fun n => deningerGammaSixShellLogWeight_nonneg (deningerGammaSixShellDepth n))
    (fun {_ _} h => deningerGammaSixLogWeight_antitone h) n

theorem deningerGammaSixShellDepth_pow (m : ℕ) (hm : 3 ≤ m) :
    deningerGammaSixShellDepth (6 ^ m) = m := by
  apply deningerGammaSixShellDepth_eq_of_shell
  · omega
  · rw [pow_succ]
    have h216 := deningerGammaSix_pow_three_le hm
    omega

theorem deningerGammaSixLogOperator_not_weak : ¬ MemWeakSchattenClass 1 deningerGammaSixLogOperator := by
  rintro ⟨C, hC, hbound⟩
  have hlog : 0 < Real.log 6 := Real.log_pos (by norm_num)
  obtain ⟨m, hm⟩ := exists_nat_gt (C / Real.log 6)
  let M := m + 3
  have hM : 3 ≤ M := by omega
  have hMC : C < (M : ℝ) * Real.log 6 := by
    have hmR : C / Real.log 6 < (m : ℝ) := hm
    have hdiv : C < (m : ℝ) * Real.log 6 :=
      (div_lt_iff₀ hlog).mp hmR
    dsimp [M]
    push_cast
    nlinarith
  have hb := hbound (6 ^ M)
  rw [Real.rpow_one, approxNumber_deningerGammaSixLogOperator, deningerGammaSixLogWeight,
    deningerGammaSixShellDepth_pow M hM, deningerGammaSixShellLogWeight] at hb
  have hden : 0 < (((6 ^ M : ℕ) : ℝ) + 1) := by positivity
  have hupper :
      ((M : ℝ) * Real.log 6 * (1 / 6 : ℝ) ^ M) *
          (((6 ^ M : ℕ) : ℝ) + 1) ≤ C :=
    (le_div_iff₀ hden).mp hb
  have hcancel :
      ((6 ^ M : ℕ) : ℝ) * (1 / 6 : ℝ) ^ M = 1 := by
    push_cast
    rw [← mul_pow]
    norm_num
  have hfactor :
      1 ≤ (((6 ^ M : ℕ) : ℝ) + 1) * (1 / 6 : ℝ) ^ M := by
    rw [add_mul, hcancel]
    exact le_add_of_nonneg_right (by positivity)
  have hlower :
      (M : ℝ) * Real.log 6 ≤
        ((M : ℝ) * Real.log 6 * (1 / 6 : ℝ) ^ M) *
          (((6 ^ M : ℕ) : ℝ) + 1) := by
    calc
      (M : ℝ) * Real.log 6 = (M : ℝ) * Real.log 6 * 1 := by ring
      _ ≤ (M : ℝ) * Real.log 6 *
          ((((6 ^ M : ℕ) : ℝ) + 1) * (1 / 6 : ℝ) ^ M) :=
        mul_le_mul_of_nonneg_left hfactor (mul_nonneg (by positivity) hlog.le)
      _ = ((M : ℝ) * Real.log 6 * (1 / 6 : ℝ) ^ M) *
          (((6 ^ M : ℕ) : ℝ) + 1) := by ring
  linarith

def deningerGammaSixRegularizedShellLogWeight (epsilon : ℝ) (m : ℕ) : ℝ :=
  (m : ℝ) * Real.log 6 * (((1 / 6 : ℝ) ^ (1 + epsilon)) ^ m)

def deningerGammaSixRegularizedLogWeight (epsilon : ℝ) (n : ℕ) : ℝ :=
  deningerGammaSixRegularizedShellLogWeight epsilon (deningerGammaSixShellDepth n)

theorem deningerGammaSixRegularizedLogWeight_nonneg (epsilon : ℝ) (n : ℕ) :
    0 ≤ deningerGammaSixRegularizedLogWeight epsilon n := by
  unfold deningerGammaSixRegularizedLogWeight deningerGammaSixRegularizedShellLogWeight
  positivity

theorem deningerGammaSixDepthFiber_tsum_regularizedLogWeight
    (epsilon : ℝ) {m : ℕ} (hm : 3 ≤ m) :
    (∑' n : deningerGammaSixDepthFiber m,
        deningerGammaSixRegularizedLogWeight epsilon n) =
      5 * (6 : ℝ) ^ m * deningerGammaSixRegularizedShellLogWeight epsilon m := by
  rw [deningerGammaSixDepthFiber_eq_shellCoordinates hm]
  letI : Fintype ((deningerGammaSixShellCoordinates m : Set ℕ)) :=
    (Finset.finite_toSet (deningerGammaSixShellCoordinates m)).fintype
  rw [tsum_fintype]
  calc
    ∑ n : (deningerGammaSixShellCoordinates m : Set ℕ),
        deningerGammaSixRegularizedLogWeight epsilon n =
      ∑ _n : (deningerGammaSixShellCoordinates m : Set ℕ),
        deningerGammaSixRegularizedShellLogWeight epsilon m := by
      apply Finset.sum_congr rfl
      intro n _hn
      unfold deningerGammaSixRegularizedLogWeight
      congr 1
      change (n : ℕ) ∈ deningerGammaSixDepthFiber m
      rw [deningerGammaSixDepthFiber_eq_shellCoordinates hm]
      exact n.property
    _ = (Fintype.card ((deningerGammaSixShellCoordinates m : Set ℕ)) : ℝ) *
        deningerGammaSixRegularizedShellLogWeight epsilon m := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ = ((deningerGammaSixShellCoordinates m).card : ℝ) *
        deningerGammaSixRegularizedShellLogWeight epsilon m := by
      have hcard :
        Fintype.card ((deningerGammaSixShellCoordinates m : Set ℕ)) =
            Nat.card ((deningerGammaSixShellCoordinates m : Set ℕ)) :=
          Nat.card_eq_fintype_card.symm
      have hcard' : Nat.card ((deningerGammaSixShellCoordinates m : Set ℕ)) =
          (deningerGammaSixShellCoordinates m : Set ℕ).ncard :=
          Nat.card_coe_set_eq _
      have hcard'' : (deningerGammaSixShellCoordinates m : Set ℕ).ncard =
          (deningerGammaSixShellCoordinates m).card :=
          Set.ncard_coe_finset _
      rw [hcard, hcard', hcard'']
    _ = 5 * (6 : ℝ) ^ m * deningerGammaSixRegularizedShellLogWeight epsilon m := by
      rw [deningerGammaSixShellCoordinates_card hm]
      push_cast
      ring

theorem summable_deningerGammaSixRegularizedLogWeight (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    Summable (deningerGammaSixRegularizedLogWeight epsilon) := by
  let r : ℝ := 6 * (1 / 6 : ℝ) ^ (1 + epsilon)
  have hbase : (1 / 6 : ℝ) ^ (1 + epsilon) < 1 / 6 := by
    simpa only [Real.rpow_one] using
      Real.rpow_lt_rpow_of_exponent_gt (by norm_num : (0 : ℝ) < 1 / 6)
        (by norm_num : (1 : ℝ) / 6 < 1) (by linarith : 1 < 1 + epsilon)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; nlinarith
  have hrnorm : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  rw [summable_partition (deningerGammaSixRegularizedLogWeight_nonneg epsilon)
    existsUnique_mem_deningerGammaSixDepthFiber]
  constructor
  · intro m
    by_cases hm : 3 ≤ m
    · rw [deningerGammaSixDepthFiber_eq_shellCoordinates hm]
      exact (hasSum_fintype (fun n :
        (deningerGammaSixShellCoordinates m : Set ℕ) =>
          deningerGammaSixRegularizedLogWeight epsilon n)).summable
    · rw [deningerGammaSixDepthFiber_eq_empty (by omega)]
      exact summable_empty
  · apply (summable_nat_add_iff 3).1
    have hs1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hrnorm
    have hs0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 hrnorm
    have hs := (hs1.add (hs0.mul_left 3)).mul_left
      (5 * Real.log 6 * r ^ 3)
    exact hs.congr fun j => by
      rw [deningerGammaSixDepthFiber_tsum_regularizedLogWeight epsilon (by omega : 3 ≤ j + 3)]
      unfold deningerGammaSixRegularizedShellLogWeight
      dsimp [r]
      push_cast
      ring

theorem deningerGammaSixRegularizedShellLogWeight_succ_le
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (m : ℕ) (hm : 3 ≤ m) :
    deningerGammaSixRegularizedShellLogWeight epsilon (m + 1) ≤
      deningerGammaSixRegularizedShellLogWeight epsilon m := by
  let b : ℝ := (1 / 6 : ℝ) ^ (1 + epsilon)
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hb6 : b ≤ 1 / 6 := by
    dsimp [b]
    simpa only [Real.rpow_one] using
      (Real.rpow_lt_rpow_of_exponent_gt (by norm_num : (0 : ℝ) < 1 / 6)
        (by norm_num : (1 : ℝ) / 6 < 1) (by linarith : 1 < 1 + epsilon)).le
  have hlog : 0 ≤ Real.log 6 := (Real.log_pos (by norm_num)).le
  have hmR : ((m : ℝ) + 1) / 6 ≤ m := by
    have : (m : ℝ) + 1 ≤ 6 * m := by
      exact_mod_cast (show m + 1 ≤ 6 * m by omega)
    linarith
  unfold deningerGammaSixRegularizedShellLogWeight
  change ((m + 1 : ℕ) : ℝ) * Real.log 6 * b ^ (m + 1) ≤
    (m : ℝ) * Real.log 6 * b ^ m
  rw [pow_succ]
  push_cast
  calc
    ((m : ℝ) + 1) * Real.log 6 * (b ^ m * b) ≤
        ((m : ℝ) + 1) * Real.log 6 * (b ^ m * (1 / 6)) := by
      gcongr
    _ = (((m : ℝ) + 1) / 6) * (Real.log 6 * b ^ m) := by ring
    _ ≤ (m : ℝ) * (Real.log 6 * b ^ m) :=
      mul_le_mul_of_nonneg_right hmR (mul_nonneg hlog (by positivity))
    _ = (m : ℝ) * Real.log 6 * b ^ m := by ring

theorem deningerGammaSixRegularizedLogWeight_antitone
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    Antitone (deningerGammaSixRegularizedLogWeight epsilon) := by
  intro i j hij
  exact (antitoneOn_nat_Ici_of_succ_le
      (deningerGammaSixRegularizedShellLogWeight_succ_le epsilon hepsilon))
    (three_le_deningerGammaSixShellDepth i)
    (three_le_deningerGammaSixShellDepth j)
    (deningerGammaSixShellDepth_mono hij)

def deningerGammaSixRegularizedLogOperator (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    EllTwo →L[ℂ] EllTwo :=
  antitoneDiagonalOperator (deningerGammaSixRegularizedLogWeight epsilon)
    (deningerGammaSixRegularizedLogWeight_nonneg epsilon)
    (fun {_ _} h => deningerGammaSixRegularizedLogWeight_antitone epsilon hepsilon h)

theorem approxNumber_deningerGammaSixRegularizedLogOperator
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (n : ℕ) :
    approxNumber (deningerGammaSixRegularizedLogOperator epsilon hepsilon) n =
      deningerGammaSixRegularizedLogWeight epsilon n := by
  exact approxNumber_antitoneDiagonalOperator_eq _
    (deningerGammaSixRegularizedLogWeight_nonneg epsilon)
    (fun {_ _} h => deningerGammaSixRegularizedLogWeight_antitone epsilon hepsilon h) n

theorem deningerGammaSixRegularizedLogOperator_traceClass
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    MemSchattenClass 1 (deningerGammaSixRegularizedLogOperator epsilon hepsilon) := by
  unfold MemSchattenClass
  simpa only [approxNumber_deningerGammaSixRegularizedLogOperator, Real.rpow_one] using
    summable_deningerGammaSixRegularizedLogWeight epsilon hepsilon

theorem deningerGammaSixRegularizedLogWeight_eq
    (epsilon : ℝ) (n : ℕ) :
    deningerGammaSixRegularizedLogWeight epsilon n =
      deningerGammaSixLogWeight n * deningerGammaSixShellEigenvalue n ^ epsilon := by
  let m := deningerGammaSixShellDepth n
  change (m : ℝ) * Real.log 6 * (((1 / 6 : ℝ) ^ (1 + epsilon)) ^ m) =
    ((m : ℝ) * Real.log 6 * (1 / 6 : ℝ) ^ m) *
      (((1 / 6 : ℝ) ^ m) ^ epsilon)
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 6), Real.rpow_one, mul_pow]
  rw [show (((1 / 6 : ℝ) ^ epsilon) ^ m) =
      (((1 / 6 : ℝ) ^ m) ^ epsilon) by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 6)]
        rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 6),
          Real.rpow_natCast]]
  ring

def deningerGammaSixLogRemainderColumn (n : ℕ) : DeningerGammaSixTensorSourceL2 :=
  ((((deningerGammaSixShellDepth n : ℕ) : ℝ) * Real.log 6 : ℝ) : ℂ) •
    deningerGammaSixSourceTensorRemainderColumn n

theorem deningerGammaSixDepthFiber_tsum_logRemainderColumn {m : ℕ} (hm : 3 ≤ m) :
    (∑' n : deningerGammaSixDepthFiber m,
        ‖deningerGammaSixLogRemainderColumn n‖) =
      (m : ℝ) * Real.log 6 *
        (5 * (6 : ℝ) ^ m *
          ‖deningerGammaSixSourceTensorRemainder ⟨m, hm⟩‖) := by
  calc
    (∑' n : deningerGammaSixDepthFiber m,
        ‖deningerGammaSixLogRemainderColumn n‖) =
      ∑' n : deningerGammaSixDepthFiber m,
        ((m : ℝ) * Real.log 6) *
          ‖deningerGammaSixSourceTensorRemainderColumn n‖ := by
      apply tsum_congr
      intro n
      rw [deningerGammaSixLogRemainderColumn, norm_smul]
      have hdepth : deningerGammaSixShellDepth (n : ℕ) = m := n.property
      rw [hdepth, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_pos (by norm_num)).le)]
    _ = (m : ℝ) * Real.log 6 *
        (∑' n : deningerGammaSixDepthFiber m,
          ‖deningerGammaSixSourceTensorRemainderColumn n‖) := by
      rw [tsum_mul_left]
    _ = (m : ℝ) * Real.log 6 *
        (5 * (6 : ℝ) ^ m *
          ‖deningerGammaSixSourceTensorRemainder ⟨m, hm⟩‖) := by
      rw [deningerGammaSixDepthFiber_tsum_remainderColumn hm]

theorem summable_deningerGammaSix_logShellWeightedRemainder :
    Summable (fun j : ℕ =>
      ((j + 3 : ℕ) : ℝ) * Real.log 6 *
        (5 * (6 : ℝ) ^ (j + 3) *
          ‖deningerGammaSixSourceTensorRemainder
            (deningerGammaSixHonestDepth j)‖)) := by
  let q : ℝ := ((6 : ℝ) / 7) ^ (1 / 2 : ℝ)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)
  have hqnorm : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1
  have hq2norm : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    nlinarith [norm_nonneg q]
  have hs1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hqnorm
  have hs0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 hqnorm
  have hshift := hs1.add (hs0.mul_left 3)
  have hs1sq := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hq2norm
  have hs0sq := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 hq2norm
  have hshiftsq := hs1sq.add (hs0sq.mul_left 3)
  let A : ℝ := 2 * ‖xiThetaSourceL2‖ * deningerGammaSixTailConstant
  let B : ℝ := deningerGammaSixTailConstant ^ 2
  have hmajor : Summable (fun j : ℕ =>
      5 * Real.log 6 *
        (A * (((j : ℝ) + 3) * q ^ j) +
          B * (((j : ℝ) + 3) * (q ^ 2) ^ j))) := by
    apply (((hshift.mul_left A).add (hshiftsq.mul_left B)).mul_left
      (5 * Real.log 6)).congr
    intro j
    simp only [pow_one, pow_zero, one_mul]
    ring
  apply hmajor.of_nonneg_of_le
  · intro j
    positivity
  · intro j
    have hsource := deningerGammaSix_shellWeightedRemainder_le j
    have hscale : 0 ≤ 5 * (((j : ℝ) + 3) * Real.log 6) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hsource hscale
    dsimp [A, B, q]
    rw [← deningerGammaSixTailRate_honestDepth] at hmul
    rw [deningerGammaSixTailRate_honestDepth] at hmul
    push_cast
    calc
      ((j : ℝ) + 3) * Real.log 6 *
          (5 * 6 ^ (j + 3) *
            ‖deningerGammaSixSourceTensorRemainder
              (deningerGammaSixHonestDepth j)‖) =
        (5 * (((j : ℝ) + 3) * Real.log 6)) *
          (6 ^ (j + 3) *
            ‖deningerGammaSixSourceTensorRemainder
              (deningerGammaSixHonestDepth j)‖) := by ring
      _ ≤ (5 * (((j : ℝ) + 3) * Real.log 6)) *
          (2 * ‖xiThetaSourceL2‖ * deningerGammaSixTailConstant *
              (((6 : ℝ) / 7) ^ ((j : ℝ) / 2)) +
            deningerGammaSixTailConstant ^ 2 *
              (((6 : ℝ) / 7) ^ ((j : ℝ) / 2)) ^ 2) := hmul
      _ = 5 * Real.log 6 *
          ((2 * ‖xiThetaSourceL2‖ * deningerGammaSixTailConstant) *
              (((j : ℝ) + 3) *
                (((6 : ℝ) / 7) ^ (1 / 2 : ℝ)) ^ j) +
            deningerGammaSixTailConstant ^ 2 *
              (((j : ℝ) + 3) *
                ((((6 : ℝ) / 7) ^ (1 / 2 : ℝ)) ^ 2) ^ j)) := by
        have hqj : ((6 : ℝ) / 7) ^ ((j : ℝ) / 2) =
            (((6 : ℝ) / 7) ^ (1 / 2 : ℝ)) ^ j := by
          rw [← Real.rpow_natCast,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (6 : ℝ) / 7)]
          congr 1
          ring
        have hsq : ((((6 : ℝ) / 7) ^ (1 / 2 : ℝ)) ^ j) ^ 2 =
            ((((6 : ℝ) / 7) ^ (1 / 2 : ℝ)) ^ 2) ^ j := by
          rw [← pow_mul, ← pow_mul]
          congr 1
          omega
        rw [hqj, hsq]
        ring

theorem summable_norm_deningerGammaSixLogRemainderColumn :
    Summable (fun n : ℕ => ‖deningerGammaSixLogRemainderColumn n‖) := by
  rw [summable_partition (fun n => norm_nonneg (deningerGammaSixLogRemainderColumn n))
    existsUnique_mem_deningerGammaSixDepthFiber]
  constructor
  · intro m
    by_cases hm : 3 ≤ m
    · rw [deningerGammaSixDepthFiber_eq_shellCoordinates hm]
      exact (hasSum_fintype (fun n :
        (deningerGammaSixShellCoordinates m : Set ℕ) =>
          ‖deningerGammaSixLogRemainderColumn n‖)).summable
    · rw [deningerGammaSixDepthFiber_eq_empty (by omega)]
      exact summable_empty
  · apply (summable_nat_add_iff 3).1
    exact summable_deningerGammaSix_logShellWeightedRemainder.congr fun j => by
      rw [deningerGammaSixDepthFiber_tsum_logRemainderColumn (by omega : 3 ≤ j + 3)]
      simp only [deningerGammaSixHonestDepth]

def deningerGammaSixLogRemainderTraceBound : ℝ :=
  ∑' n : ℕ, ‖deningerGammaSixLogRemainderColumn n‖

theorem deningerGammaSixLogRemainderTraceBound_nonneg : 0 ≤ deningerGammaSixLogRemainderTraceBound :=
  tsum_nonneg fun _ => norm_nonneg _

theorem norm_deningerGammaSixLogRemainderColumn_le_traceBound (n : ℕ) :
    ‖deningerGammaSixLogRemainderColumn n‖ ≤ deningerGammaSixLogRemainderTraceBound :=
  summable_norm_deningerGammaSixLogRemainderColumn.le_tsum n (fun _k _ => norm_nonneg _)

def deningerGammaSixLogRemainderOperator :
    EllTwo →L[ℂ] lp (fun _ : ℕ => DeningerGammaSixTensorSourceL2) 2 :=
  vectorDiagonalOperator deningerGammaSixLogRemainderColumn
    deningerGammaSixLogRemainderTraceBound_nonneg
    norm_deningerGammaSixLogRemainderColumn_le_traceBound

theorem deningerGammaSixLogRemainderOperator_traceClass :
    MemRectSchattenClass 1 deningerGammaSixLogRemainderOperator :=
  vectorDiagonalOperator_memRectSchattenClass_one_of_summable_norm
    deningerGammaSixLogRemainderColumn deningerGammaSixLogRemainderTraceBound_nonneg
    norm_deningerGammaSixLogRemainderColumn_le_traceBound
    summable_norm_deningerGammaSixLogRemainderColumn

@[simp] theorem deningerGammaSixLogOperator_apply (x : EllTwo) (n : ℕ) :
    deningerGammaSixLogOperator x n = ((deningerGammaSixLogWeight n : ℝ) : ℂ) * x n := by
  rfl

def deningerGammaSixPrincipalLogSourceOperator :
    EllTwo →L[ℂ] lp (fun _ : ℕ => DeningerGammaSixTensorSourceL2) 2 :=
  deningerGammaSixLeadingTensorEmbedding ∘L deningerGammaSixLogOperator

@[simp] theorem deningerGammaSixPrincipalLogSourceOperator_apply (x : EllTwo) (n : ℕ) :
    deningerGammaSixPrincipalLogSourceOperator x n =
      x n • ((deningerGammaSixLogWeight n : ℝ) : ℂ) • deningerGammaSixLeadingTensorVector := by
  rw [deningerGammaSixPrincipalLogSourceOperator, ContinuousLinearMap.comp_apply,
    deningerGammaSixLeadingTensorEmbedding, vectorDiagonalOperator_apply,
    deningerGammaSixLogOperator_apply]
  rw [smul_smul]
  congr 1
  ring

theorem deningerGammaSixWoldCompression_principalLog :
    deningerGammaSixWoldCompression deningerGammaSixPrincipalLogSourceOperator =
      (1 / 6 : ℂ) • deningerGammaSixPrincipalLogSourceOperator +
        ((Real.log 6 / 6 : ℝ) : ℂ) •
          deningerGammaSixSourceTensorPrincipalOperator := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  rw [deningerGammaSixWoldCompression_apply,
    deningerGammaSixPrincipalLogSourceOperator_apply,
    deningerGammaSixWoldShift_coordinate]
  change x n • ((deningerGammaSixLogWeight (deningerGammaSixWoldCoordinate n) : ℝ) : ℂ) •
      deningerGammaSixLeadingTensorVector =
    (1 / 6 : ℂ) • deningerGammaSixPrincipalLogSourceOperator x n +
      ((Real.log 6 / 6 : ℝ) : ℂ) •
        deningerGammaSixSourceTensorPrincipalOperator x n
  rw [deningerGammaSixPrincipalLogSourceOperator_apply,
    deningerGammaSixSourceTensorPrincipalOperator_apply,
    deningerGammaSixSourceTensorPrincipal_eq]
  have hw := deningerGammaSixLogWeight_wold n
  change x n • ((deningerGammaSixLogWeight (deningerGammaSixWoldCoordinate n) : ℝ) : ℂ) •
      deningerGammaSixLeadingTensorVector =
    (1 / 6 : ℂ) •
        (x n • ((deningerGammaSixLogWeight n : ℝ) : ℂ) • deningerGammaSixLeadingTensorVector) +
      ((Real.log 6 / 6 : ℝ) : ℂ) •
        (x n • (((1 / 6 : ℝ) ^ deningerGammaSixShellDepth n : ℝ) : ℂ) •
          deningerGammaSixLeadingTensorVector)
  rw [show deningerGammaSixLogWeight (deningerGammaSixWoldCoordinate n) =
      (1 / 6 : ℝ) * deningerGammaSixLogWeight n +
        (Real.log 6 / 6) * deningerGammaSixShellEigenvalue n by linarith]
  unfold deningerGammaSixShellEigenvalue
  module

def deningerGammaSixFullLogSourceOperator :
    EllTwo →L[ℂ] lp (fun _ : ℕ => DeningerGammaSixTensorSourceL2) 2 :=
  deningerGammaSixPrincipalLogSourceOperator + deningerGammaSixLogRemainderOperator

def deningerGammaSixFullLogCoface :
    EllTwo →L[ℂ] lp (fun _ : ℕ => DeningerGammaSixTensorSourceL2) 2 :=
  deningerGammaSixWoldCompression deningerGammaSixFullLogSourceOperator -
    (1 / 6 : ℂ) • deningerGammaSixFullLogSourceOperator

def deningerGammaSixFullLogCofaceError :
    EllTwo →L[ℂ] lp (fun _ : ℕ => DeningerGammaSixTensorSourceL2) 2 :=
  deningerGammaSixFullLogCoface -
    ((Real.log 6 / 6 : ℝ) : ℂ) • deningerGammaSixFullSourceTensorOperator

theorem deningerGammaSixFullLogCofaceError_eq :
    deningerGammaSixFullLogCofaceError =
      deningerGammaSixWoldCompression deningerGammaSixLogRemainderOperator -
        (1 / 6 : ℂ) • deningerGammaSixLogRemainderOperator -
          ((Real.log 6 / 6 : ℝ) : ℂ) •
            deningerGammaSixSourceTensorRemainderOperator := by
  have hfull : deningerGammaSixFullSourceTensorOperator =
      deningerGammaSixSourceTensorPrincipalOperator +
        deningerGammaSixSourceTensorRemainderOperator := by
    rw [← deningerGammaSixFullSourceTensorOperator_sub_principal]
    module
  rw [deningerGammaSixFullLogCofaceError, deningerGammaSixFullLogCoface, deningerGammaSixFullLogSourceOperator,
    deningerGammaSixWoldCompression_add, smul_add, hfull, smul_add,
    deningerGammaSixWoldCompression_principalLog]
  abel

theorem memRectSchattenClass_one_smul
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {T : E →L[ℂ] F} (hT : MemRectSchattenClass 1 T) (c : ℂ) :
    MemRectSchattenClass 1 (c • T) := by
  let A : F →L[ℂ] F := c • ContinuousLinearMap.id ℂ F
  have h := hT.one_comp_left A
  convert h using 1
  apply ContinuousLinearMap.ext
  intro x
  simp [A]

theorem deningerGammaSixFullLogCofaceError_traceClass :
    MemRectSchattenClass 1 deningerGammaSixFullLogCofaceError := by
  rw [deningerGammaSixFullLogCofaceError_eq]
  have hcomp : MemRectSchattenClass 1
      (deningerGammaSixWoldCompression deningerGammaSixLogRemainderOperator) :=
    (deningerGammaSixLogRemainderOperator_traceClass.one_comp_right
      deningerGammaSixWoldShift.toContinuousLinearMap).one_comp_left
        deningerGammaSixTensorWoldPullback
  exact (hcomp.one_sub
      (memRectSchattenClass_one_smul deningerGammaSixLogRemainderOperator_traceClass (1 / 6))) |>.one_sub
    (memRectSchattenClass_one_smul
      deningerGammaSixSourceTensorRemainderOperator_traceClass
      ((Real.log 6 / 6 : ℝ) : ℂ))

theorem deningerGammaSixFullLogCoface_not_traceClass :
    ¬ MemRectSchattenClass 1 deningerGammaSixFullLogCoface := by
  intro hcoface
  have hcfull : MemRectSchattenClass 1
      (((Real.log 6 / 6 : ℝ) : ℂ) • deningerGammaSixFullSourceTensorOperator) := by
    rw [show (((Real.log 6 / 6 : ℝ) : ℂ) •
          deningerGammaSixFullSourceTensorOperator) =
        deningerGammaSixFullLogCoface - deningerGammaSixFullLogCofaceError by
      rw [deningerGammaSixFullLogCofaceError]
      abel]
    exact hcoface.one_sub deningerGammaSixFullLogCofaceError_traceClass
  have hc : ((Real.log 6 / 6 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast div_ne_zero (ne_of_gt (Real.log_pos (by norm_num))) (by norm_num : (6 : ℝ) ≠ 0)
  have hfull := memRectSchattenClass_one_smul hcfull
    (((Real.log 6 / 6 : ℝ) : ℂ)⁻¹)
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at hfull
  exact deningerGammaSixFullSourceTensorOperator_not_traceClass hfull

def deningerGammaSixForwardShellFamily (n : ℕ) (delta : ℝ) : ℝ :=
  deningerGammaSixShellEigenvalue n ^ (1 - delta)

def deningerGammaSixReflectedShellFamily (n : ℕ) (delta : ℝ) : ℝ :=
  deningerGammaSixShellEigenvalue n ^ (1 + delta)

theorem log_deningerGammaSixShellEigenvalue (n : ℕ) :
    Real.log (deningerGammaSixShellEigenvalue n) =
      -(deningerGammaSixShellDepth n : ℝ) * Real.log 6 := by
  rw [deningerGammaSixShellEigenvalue, Real.log_pow]
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (6 : ℝ) ≠ 0),
    Real.log_one]
  ring

theorem hasDerivAt_deningerGammaSixForwardShellFamily_zero (n : ℕ) :
    HasDerivAt (deningerGammaSixForwardShellFamily n) (deningerGammaSixLogWeight n) 0 := by
  have hp : 0 < deningerGammaSixShellEigenvalue n := by
    unfold deningerGammaSixShellEigenvalue
    positivity
  have h := ((hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).sub
    (hasDerivAt_id (𝕜 := ℝ) 0)).const_rpow hp
  convert h using 1
  · rfl
  · rw [deningerGammaSixLogWeight, deningerGammaSixShellLogWeight, log_deningerGammaSixShellEigenvalue]
    simp only [Pi.sub_apply, id_eq, sub_zero, zero_sub, Real.rpow_one]
    rw [deningerGammaSixShellEigenvalue]
    ring

theorem hasDerivAt_deningerGammaSixReflectedShellFamily_zero (n : ℕ) :
    HasDerivAt (deningerGammaSixReflectedShellFamily n) (-deningerGammaSixLogWeight n) 0 := by
  have hp : 0 < deningerGammaSixShellEigenvalue n := by
    unfold deningerGammaSixShellEigenvalue
    positivity
  have h := ((hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).add
    (hasDerivAt_id (𝕜 := ℝ) 0)).const_rpow hp
  convert h using 1
  · rfl
  · rw [deningerGammaSixLogWeight, deningerGammaSixShellLogWeight, log_deningerGammaSixShellEigenvalue]
    simp only [Pi.add_apply, id_eq, add_zero, zero_add, Real.rpow_one]
    rw [deningerGammaSixShellEigenvalue]
    ring

def deningerGammaSixAffineShellJetWeight (a b : ℝ) (n : ℕ) : ℝ :=
  (a * (deningerGammaSixShellDepth n : ℝ) + b) *
    deningerGammaSixShellEigenvalue n

theorem deningerGammaSixAffineShellJetWeight_woldCoface (a b : ℝ) (n : ℕ) :
    deningerGammaSixAffineShellJetWeight a b (deningerGammaSixWoldCoordinate n) -
        (1 / 6 : ℝ) * deningerGammaSixAffineShellJetWeight a b n =
      (a / 6) * deningerGammaSixShellEigenvalue n := by
  rw [deningerGammaSixAffineShellJetWeight, deningerGammaSixAffineShellJetWeight,
    deningerGammaSixShellDepth_wold, deningerGammaSixShellEigenvalue_wold]
  push_cast
  ring

theorem deningerGammaSixAffineShellJetWeight_coface_eq_iff (a b c : ℝ) :
    (∀ n : ℕ,
      deningerGammaSixAffineShellJetWeight a b (deningerGammaSixWoldCoordinate n) -
          (1 / 6 : ℝ) * deningerGammaSixAffineShellJetWeight a b n =
        (c / 6) * deningerGammaSixShellEigenvalue n) ↔ a = c := by
  constructor
  · intro h
    have h0 := h 0
    rw [deningerGammaSixAffineShellJetWeight_woldCoface] at h0
    have hg : 0 < deningerGammaSixShellEigenvalue 0 := by
      unfold deningerGammaSixShellEigenvalue
      positivity
    nlinarith
  · rintro rfl n
    exact deningerGammaSixAffineShellJetWeight_woldCoface a b n

theorem deningerGammaSixAffineShellJetWeight_eq_log_add_eigen (b : ℝ) (n : ℕ) :
    deningerGammaSixAffineShellJetWeight (Real.log 6) b n =
      deningerGammaSixLogWeight n + b * deningerGammaSixShellEigenvalue n := by
  unfold deningerGammaSixAffineShellJetWeight deningerGammaSixLogWeight deningerGammaSixShellLogWeight
  rw [deningerGammaSixShellEigenvalue]
  ring

end
end RHTower
