import GaloisForLFunctions.RHTower.Sieve.MoebiusRangeLadderCosts

/-!
# The Möbius window over the ladder of prime ranges

With the ranges of `Sieve/MoebiusRangeLadderSchedule`, every range costs at most
`1500·M²/(2^j·log ν)`, so all ranges together cost at most `3000·M²/log ν`, whatever their number.
What remains of the window is the low-frequency disc and the exceptional set where some block of
every range is large.
-/

namespace RHTower.Sieve

open Finset MeasureTheory
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- `(8ℓ+8)^ℓ ≤ exp((3t⁶+1)(4+6 log t))` for `ℓ = ⌈3t⁶⌉`. -/
theorem amplification_pow_le_exp {t : ℝ} (ht : 1 ≤ t) :
    (8 * ⌈3 * t ^ 6⌉₊ + 8 : ℝ) ^ ⌈3 * t ^ 6⌉₊
      ≤ Real.exp ((3 * t ^ 6 + 1) * (4 + 6 * Real.log t)) := by
  have ht0 : 0 < t := by linarith
  set ℓ := ⌈3 * t ^ 6⌉₊ with hℓdef
  have hℓ : (ℓ : ℝ) ≤ 3 * t ^ 6 + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
  have hbase0 : (0 : ℝ) < 8 * ℓ + 8 := by positivity
  have ht6 : 1 ≤ t ^ 6 := one_le_pow₀ ht
  have he4 : (40 : ℝ) ≤ Real.exp 4 := by
    have he : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    have h : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h]
    calc (40 : ℝ) ≤ 2.7 ^ 4 := by norm_num
      _ ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) he 4
  have hbase : 8 * (ℓ : ℝ) + 8 ≤ Real.exp 4 * t ^ 6 := by nlinarith
  have hlog : Real.log (8 * (ℓ : ℝ) + 8) ≤ 4 + 6 * Real.log t := by
    have := Real.log_le_log hbase0 hbase
    rwa [Real.log_mul (Real.exp_pos 4).ne' (by positivity), Real.log_exp, Real.log_pow] at this
  have hlog0 : 0 ≤ Real.log (8 * (ℓ : ℝ) + 8) := Real.log_nonneg (by linarith)
  rw [pow_eq_exp_nat_mul_log hbase0]
  refine Real.exp_le_exp.mpr ?_
  exact mul_le_mul hℓ hlog hlog0 (by positivity)

/-- **The cofactor term of the first range.** -/
theorem rangeLadder_zero_cofactor_le {ν : ℝ} (hν : 3000 ≤ ν) (M : ℕ) :
    4 * (rangeLadderSteps ν 0 : ℝ) * ∑ v ∈ Finset.range (rangeLadderSteps ν 0),
        rangeCofactorCost (rangeLadderR ν) (rangeLadderEta ν) (rangeLadderSteps ν) rangeLadderAlpha M 0 v
      ≤ (M : ℝ) ^ 2 / Real.log ν := by
  have hν0 : 0 < ν := by linarith
  have hlogν : 0 < Real.log ν := by have := log_ge_four_of_ge hν; linarith
  have hsum := rangeLadder_zero_cost_le hν0 M
  have hL := rangeLadderSteps_le_exp (by linarith : (1 : ℝ) ≤ ν) 0
  rw [rangeLadderNu, pow_zero, pow_one, pow_zero, mul_one] at hL
  have hL0 : (0 : ℝ) ≤ rangeLadderSteps ν 0 := Nat.cast_nonneg _
  have hcore := rangeLadder_zero_numeric_core hν
  have hE0 : 0 ≤ Real.exp (-(ν ^ 4) / 4) := (Real.exp_pos _).le
  have hM0 : (0 : ℝ) ≤ (M : ℝ) ^ 2 := by positivity
  rw [le_div_iff₀ hlogν]
  calc 4 * (rangeLadderSteps ν 0 : ℝ) * (∑ v ∈ Finset.range (rangeLadderSteps ν 0),
        rangeCofactorCost (rangeLadderR ν) (rangeLadderEta ν) (rangeLadderSteps ν) rangeLadderAlpha
          M 0 v) * Real.log ν
      ≤ 4 * (rangeLadderSteps ν 0 : ℝ)
          * (rangeLadderSteps ν 0 * (15 * (M : ℝ) ^ 2 * Real.exp (-(ν ^ 4) / 4))) * Real.log ν := by
        gcongr
    _ = 60 * (rangeLadderSteps ν 0 : ℝ) ^ 2 * Real.exp (-(ν ^ 4) / 4) * Real.log ν * (M : ℝ) ^ 2 := by
        ring
    _ ≤ 60 * (3 * ν ^ 5 * Real.exp ν) ^ 2 * Real.exp (-(ν ^ 4) / 4) * Real.log ν * (M : ℝ) ^ 2 := by
        gcongr
    _ = (540 * ν ^ 10 * (Real.exp ν) ^ 2 * Real.exp (-(ν ^ 4) / 4) * Real.log ν) * (M : ℝ) ^ 2 := by
        ring
    _ = (540 * ν ^ 10 * Real.exp (2 * ν) * Real.exp (-(ν ^ 4) / 4) * Real.log ν) * (M : ℝ) ^ 2 := by
        rw [← Real.exp_nat_mul]; norm_num
    _ ≤ 1 * (M : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hcore hM0
    _ = (M : ℝ) ^ 2 := one_mul _

/-- **The cofactor term of a later range.** -/
theorem rangeLadder_succ_cofactor_le {ν : ℝ} (hν : 3000 ≤ ν) (M : ℕ) (j : ℕ) :
    4 * (rangeLadderSteps ν (j + 1) : ℝ) * ∑ v ∈ Finset.range (rangeLadderSteps ν (j + 1)),
        rangeCofactorCost (rangeLadderR ν) (rangeLadderEta ν) (rangeLadderSteps ν) rangeLadderAlpha M
          (j + 1) v
      ≤ (M : ℝ) ^ 2 / (2 ^ (j + 1) * Real.log ν) := by
  have hν0 : 0 < ν := by linarith
  have hlogν4 := log_ge_four_of_ge hν
  have hlogν : 0 < Real.log ν := by linarith
  set t := rangeLadderNu ν j with htdef
  have hνt : ν ≤ t := le_rangeLadderNu (by linarith) j
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  set g : ℝ := 2 ^ j with hgdef
  have hg1 : 1 ≤ g := one_le_pow₀ (by norm_num)
  have hgu : g * Real.log ν = Real.log t := by rw [htdef, log_rangeLadderNu]
  have hsum := rangeLadder_succ_cost_le (by linarith : (2 : ℝ) ≤ ν) M j
  rw [← htdef] at hsum
  have hL' := rangeLadderSteps_le_exp (by linarith : (1 : ℝ) ≤ ν) (j + 1)
  rw [rangeLadderNu_succ, ← htdef] at hL'
  have hL := rangeLadderSteps_le_exp (by linarith : (1 : ℝ) ≤ ν) j
  rw [← htdef] at hL
  have hamp := amplification_pow_le_exp ht1
  have hQ : rangeLadderTopReal ν j ≤ Real.exp (3 * t ^ 5) := by
    have h := log_rangeLadderTopReal_le (by linarith : (2 : ℝ) ≤ ν) j
    rw [← htdef] at h
    calc rangeLadderTopReal ν j = Real.exp (Real.log (rangeLadderTopReal ν j)) :=
          (Real.exp_log (rangeLadderTopReal_pos hν0 j)).symm
      _ ≤ Real.exp (3 * t ^ 5) := Real.exp_le_exp.mpr h
  have hcore := rangeLadder_succ_numeric_core (by linarith : (2880 : ℝ) ≤ t) hg1 hgu
    (by linarith) hνt
  have hL0 : (0 : ℝ) ≤ rangeLadderSteps ν j := Nat.cast_nonneg _
  have hL0' : (0 : ℝ) ≤ rangeLadderSteps ν (j + 1) := Nat.cast_nonneg _
  have hQ0 := (rangeLadderTopReal_pos hν0 j).le
  have hM0 : (0 : ℝ) ≤ (M : ℝ) ^ 2 := by positivity
  have hE0 : 0 ≤ Real.exp (-(t ^ 8 / (8 * 2 ^ j))) := (Real.exp_pos _).le
  have hamp0 : (0 : ℝ) ≤ (8 * ⌈3 * t ^ 6⌉₊ + 8 : ℝ) ^ ⌈3 * t ^ 6⌉₊ := by positivity
  have hden : 0 < 2 ^ (j + 1) * Real.log ν := by positivity
  rw [le_div_iff₀ hden]
  calc 4 * (rangeLadderSteps ν (j + 1) : ℝ) * (∑ v ∈ Finset.range (rangeLadderSteps ν (j + 1)),
        rangeCofactorCost (rangeLadderR ν) (rangeLadderEta ν) (rangeLadderSteps ν) rangeLadderAlpha
          M (j + 1) v) * (2 ^ (j + 1) * Real.log ν)
      ≤ 4 * (rangeLadderSteps ν (j + 1) : ℝ) * (rangeLadderSteps ν (j + 1) * (rangeLadderSteps ν j
          * (15 * (8 * ⌈3 * t ^ 6⌉₊ + 8 : ℝ) ^ ⌈3 * t ^ 6⌉₊
            * rangeLadderTopReal ν j * (M : ℝ) ^ 2
            * Real.exp (-(t ^ 8 / (8 * 2 ^ j)))))) * (2 ^ (j + 1) * Real.log ν) := by
        gcongr
    _ = 60 * (rangeLadderSteps ν (j + 1) : ℝ) ^ 2 * rangeLadderSteps ν j
          * (8 * ⌈3 * t ^ 6⌉₊ + 8 : ℝ) ^ ⌈3 * t ^ 6⌉₊ * rangeLadderTopReal ν j
          * Real.exp (-(t ^ 8 / (8 * g))) * (2 * g * Real.log ν) * (M : ℝ) ^ 2 := by
        rw [hgdef, pow_succ]; ring
    _ ≤ 60 * (3 * (t ^ 2) ^ 5 * (2 * g) * Real.exp ν) ^ 2 * (3 * t ^ 5 * g * Real.exp ν)
          * Real.exp ((3 * t ^ 6 + 1) * (4 + 6 * Real.log t)) * Real.exp (3 * t ^ 5)
          * Real.exp (-(t ^ 8 / (8 * g))) * (2 * g * Real.log ν) * (M : ℝ) ^ 2 := by
        have hL'' : (rangeLadderSteps ν (j + 1) : ℝ) ≤ 3 * (t ^ 2) ^ 5 * (2 * g) * Real.exp ν := by
          rw [hgdef, ← pow_succ']; exact hL'
        gcongr
    _ = (12960 * t ^ 25 * g ^ 4 * Real.log ν * ((Real.exp ν) ^ 3)
          * Real.exp ((3 * t ^ 6 + 1) * (4 + 6 * Real.log t)) * Real.exp (3 * t ^ 5)
          * Real.exp (-(t ^ 8 / (8 * g)))) * (M : ℝ) ^ 2 := by ring
    _ = (12960 * t ^ 25 * g ^ 4 * Real.log ν * Real.exp (3 * ν)
          * Real.exp ((3 * t ^ 6 + 1) * (4 + 6 * Real.log t)) * Real.exp (3 * t ^ 5)
          * Real.exp (-(t ^ 8 / (8 * g)))) * (M : ℝ) ^ 2 := by
        rw [← Real.exp_nat_mul]; norm_num
    _ ≤ 1 * (M : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hcore hM0
    _ = (M : ℝ) ^ 2 := one_mul _

/-- The cofactor term of every range. -/
theorem rangeLadder_cofactor_le {ν : ℝ} (hν : 3000 ≤ ν) (M : ℕ) (j : ℕ) :
    4 * (rangeLadderSteps ν j : ℝ) * ∑ v ∈ Finset.range (rangeLadderSteps ν j),
        rangeCofactorCost (rangeLadderR ν) (rangeLadderEta ν) (rangeLadderSteps ν) rangeLadderAlpha M j v
      ≤ (M : ℝ) ^ 2 / (2 ^ j * Real.log ν) := by
  cases j with
  | zero => simpa using rangeLadder_zero_cofactor_le hν M
  | succ j => exact rangeLadder_succ_cofactor_le hν M j

/-- **One range of the ladder costs at most `1500·M²/(2^j log ν)`.** -/
theorem rangeLadder_term_le {ν : ℝ} (hν : 3000 ≤ ν) (hc : 4 * mertensFirstConst + 1 ≤ ν)
    (M : ℕ) {W : ℝ} (hW : 1 ≤ W) (hWM : W ≤ M) (j : ℕ)
    (htop : (rangeLadderTop ν j : ℝ) ≤ M) :
    2 * (2 * (rangeLadderSteps ν j : ℝ) * ∑ v ∈ Finset.range (rangeLadderSteps ν j),
          rangeCofactorCost (rangeLadderR ν) (rangeLadderEta ν) (rangeLadderSteps ν) rangeLadderAlpha
            M j v
        + 2 * ∫ w in Set.Icc (-W) W,
            ‖ramareLadderError (rangeLadderP ν j) M (rangeLadderR ν j) (rangeLadderEta ν j)
              (rangeLadderSteps ν j) w‖ ^ 2)
      + 2 * (∫ w in Set.Icc (-W) W,
          ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (supportMeanSquareRoughSet (rangeLadderP ν j) M) w‖ ^ 2)
      ≤ 1500 * (M : ℝ) ^ 2 / (2 ^ j * Real.log ν) := by
  have hν0 : 0 < ν := by linarith
  have hlogν4 := log_ge_four_of_ge hν
  have hlogν : 0 < Real.log ν := by linarith
  have hcof := rangeLadder_cofactor_le hν M j
  have herr := rangeLadder_error_le hν0 j M hW hWM
  have hrough := rangeLadder_rough_le hν hc j M hW hWM htop
  have hlogt : Real.log (rangeLadderNu ν j) = 2 ^ j * Real.log ν := log_rangeLadderNu ν j
  rw [hlogt] at hrough
  have hden : 0 < 2 ^ j * Real.log ν := by positivity
  -- the step ratio
  have hη : rangeLadderEta ν j ≤ 1 / (2 ^ j * Real.log ν) := by
    rw [rangeLadderEta, div_le_div_iff₀ (by positivity) hden, one_mul, mul_comm (2 ^ j : ℝ),
      ← mul_assoc]
    have h1 : Real.log ν ≤ Real.exp ν := by
      have := Real.log_le_sub_one_of_pos hν0
      have := Real.add_one_le_exp ν
      linarith
    have h2 : Real.exp (-ν) * Real.exp ν = 1 := by rw [← Real.exp_add]; simp
    have h3 : Real.exp (-ν) * Real.log ν ≤ 1 := by
      calc Real.exp (-ν) * Real.log ν ≤ Real.exp (-ν) * Real.exp ν :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = 1 := h2
    nlinarith [show (0 : ℝ) < 2 ^ j by positivity]
  -- the base
  have hR : 6 / rangeLadderR ν j ≤ 6 / (2 ^ j * Real.log ν) := by
    refine div_le_div_of_nonneg_left (by norm_num) hden ?_
    rw [← hlogt]
    set t := rangeLadderNu ν j
    have ht1 : 1 ≤ t := by linarith [le_rangeLadderNu (by linarith : (1 : ℝ) ≤ ν) j]
    have h1 : Real.log t ≤ t := by have := Real.log_le_sub_one_of_pos (by linarith : 0 < t); linarith
    have h2 : t ≤ t ^ 4 := by
      calc t = t ^ 1 := (pow_one t).symm
        _ ≤ t ^ 4 := pow_le_pow_right₀ ht1 (by norm_num)
    have h3 : t ^ 4 ≤ Real.exp (t ^ 4) := by have := Real.add_one_le_exp (t ^ 4); linarith
    linarith [exp_le_rangeLadderR ν j]
  have hM0 : (0 : ℝ) ≤ (M : ℝ) ^ 2 := by positivity
  have herr' : 2 * (2 * ∫ w in Set.Icc (-W) W,
            ‖ramareLadderError (rangeLadderP ν j) M (rangeLadderR ν j) (rangeLadderEta ν j)
              (rangeLadderSteps ν j) w‖ ^ 2)
      ≤ 1232 * (M : ℝ) ^ 2 / (2 ^ j * Real.log ν) := by
    have h7 : rangeLadderEta ν j + 6 / rangeLadderR ν j ≤ 7 / (2 ^ j * Real.log ν) := by
      have : 1 / (2 ^ j * Real.log ν) + 6 / (2 ^ j * Real.log ν) = 7 / (2 ^ j * Real.log ν) := by
        rw [← add_div]; norm_num
      linarith
    have := mul_le_mul_of_nonneg_left h7 (show (0 : ℝ) ≤ 44 * (M : ℝ) ^ 2 by positivity)
    have hid : 44 * (M : ℝ) ^ 2 * (7 / (2 ^ j * Real.log ν)) = 308 * (M : ℝ) ^ 2 / (2 ^ j * Real.log ν) := by
      ring
    have hfin : 4 * (308 * (M : ℝ) ^ 2 / (2 ^ j * Real.log ν))
        = 1232 * (M : ℝ) ^ 2 / (2 ^ j * Real.log ν) := by ring
    linarith
  have hsplit : 1500 * (M : ℝ) ^ 2 / (2 ^ j * Real.log ν)
      = (M : ℝ) ^ 2 / (2 ^ j * Real.log ν) + 1232 * (M : ℝ) ^ 2 / (2 ^ j * Real.log ν)
        + 2 * (90 * (M : ℝ) ^ 2 / (2 ^ j * Real.log ν))
        + 87 * (M : ℝ) ^ 2 / (2 ^ j * Real.log ν) := by ring
  have h87 : 0 ≤ 87 * (M : ℝ) ^ 2 / (2 ^ j * Real.log ν) := by positivity
  rw [hsplit]
  nlinarith [hcof, herr', hrough]

/-- **All ranges of the ladder together cost at most `3000·M²/log ν`.** -/
theorem rangeLadder_sum_le {ν : ℝ} (hν : 3000 ≤ ν) (hc : 4 * mertensFirstConst + 1 ≤ ν)
    (M J : ℕ) {W : ℝ} (hW : 1 ≤ W) (hWM : W ≤ M)
    (htop : ∀ j ∈ Finset.range J, (rangeLadderTop ν j : ℝ) ≤ M) :
    ∑ j ∈ Finset.range J,
        (2 * (2 * (rangeLadderSteps ν j : ℝ) * ∑ v ∈ Finset.range (rangeLadderSteps ν j),
              rangeCofactorCost (rangeLadderR ν) (rangeLadderEta ν) (rangeLadderSteps ν)
                rangeLadderAlpha M j v
            + 2 * ∫ w in Set.Icc (-W) W,
                ‖ramareLadderError (rangeLadderP ν j) M (rangeLadderR ν j) (rangeLadderEta ν j)
                  (rangeLadderSteps ν j) w‖ ^ 2)
          + 2 * (∫ w in Set.Icc (-W) W,
              ‖logPoly (fun n => ((μ n : ℤ) : ℂ))
                (supportMeanSquareRoughSet (rangeLadderP ν j) M) w‖ ^ 2))
      ≤ 3000 * (M : ℝ) ^ 2 / Real.log ν := by
  have hlogν : 0 < Real.log ν := by have := log_ge_four_of_ge hν; linarith
  refine (Finset.sum_le_sum fun j hj =>
    rangeLadder_term_le hν hc M hW hWM j (htop j hj)).trans ?_
  have hgeo : ∑ j ∈ Finset.range J, ((1 : ℝ) / 2) ^ j ≤ 2 := sum_geometric_two_le J
  have hid : ∀ j : ℕ, 1500 * (M : ℝ) ^ 2 / (2 ^ j * Real.log ν)
      = (1500 * (M : ℝ) ^ 2 / Real.log ν) * ((1 : ℝ) / 2) ^ j := by
    intro j
    rw [div_pow, one_pow]
    field_simp
  rw [Finset.sum_congr rfl fun j _ => hid j, ← Finset.mul_sum]
  have h0 : 0 ≤ 1500 * (M : ℝ) ^ 2 / Real.log ν := by positivity
  calc 1500 * (M : ℝ) ^ 2 / Real.log ν * ∑ j ∈ Finset.range J, ((1 : ℝ) / 2) ^ j
      ≤ 1500 * (M : ℝ) ^ 2 / Real.log ν * 2 := mul_le_mul_of_nonneg_left hgeo h0
    _ = 3000 * (M : ℝ) ^ 2 / Real.log ν := by ring

end

end RHTower.Sieve
