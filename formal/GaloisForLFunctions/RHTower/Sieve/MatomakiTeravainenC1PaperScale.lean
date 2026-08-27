import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenC1Schedule

/-!
# Matomäki--Teräväinen `c₁,n` estimate at paper scale

The rounded source schedule gives a Gaussian saving in `log log X`.  This file absorbs every fixed
divisor-weight and Euler-product loss, then applies the result to the literal bounded-coefficient
Legendre truncation error.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

set_option maxHeartbeats 400000 in
/-- A quadratic `log log X` Rankin exponent absorbs the complete fixed-polylogarithmic loss. -/
theorem eventually_mtC1_polylog_absorption (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (z D Y : ℕ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → 2 ≤ z → 0 < D →
      (Real.log (Real.log X)) ^ 2 / 4 ≤ Real.log (D : ℝ) / Real.log (z : ℝ) →
      logLog z ≤ Real.log (Real.log X) + 1 →
      (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) *
          ((D : ℝ) ^ (-(1 / Real.log z)) *
            Real.exp ((((2 : ℝ) ^ 3) * Real.exp 1) *
              (logLog z + mertensSecondUpperConst))) ≤
        (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
  let lam : ℝ := ((2 : ℝ) ^ 3) * Real.exp 1
  let cTot : ℝ := 8 + lam + (3 * A : ℕ) +
    |lam * (1 + mertensSecondUpperConst)|
  have htend : Tendsto (fun X : ℝ => Real.log (Real.log X)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hlarge := htend.eventually_ge_atTop
    (max ((5 : ℝ) ^ 7) (max 1 (4 * cTot)))
  filter_upwards [hlarge, Filter.eventually_gt_atTop (Real.exp (Real.exp 1))]
    with X ht hX
  intro z D Y hY hYX hz hD hratio hlogLog
  let t : ℝ := Real.log (Real.log X)
  have htFive : (5 : ℝ) ^ 7 ≤ t :=
    (le_max_left _ _).trans ht
  have htOne : (1 : ℝ) ≤ t :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have htC : 4 * cTot ≤ t :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  have hL : 0 < Real.log X := by
    apply Real.log_pos
    have : (1 : ℝ) < Real.exp (Real.exp 1) := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (Real.exp_pos 1)
    linarith
  have htPos : 0 < t := lt_of_lt_of_le zero_lt_one htOne
  have hlogz : 0 < Real.log (z : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hz))
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  have hDfactor :
      (D : ℝ) ^ (-(1 / Real.log z)) ≤ Real.exp (-(t ^ 2 / 4)) := by
    rw [Real.rpow_def_of_pos hDR, Real.exp_le_exp]
    dsimp [t]
    have heq : Real.log (D : ℝ) * (-(1 / Real.log (z : ℝ))) =
        -(Real.log (D : ℝ) / Real.log (z : ℝ)) := by ring
    rw [heq]
    exact neg_le_neg hratio
  have hEuler :
      Real.exp (lam * (logLog z + mertensSecondUpperConst)) ≤
        Real.exp (lam * (t + 1 + mertensSecondUpperConst)) := by
    rw [Real.exp_le_exp]
    apply mul_le_mul_of_nonneg_left _ (by dsimp [lam]; positivity)
    linarith
  have hlogXone : 1 ≤ Real.log X := by
    rw [← Real.exp_zero, ← Real.exp_log hL]
    exact Real.exp_le_exp.mpr (le_trans (by norm_num) htOne)
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hY)
  have hlogY : Real.log (Y : ℝ) ≤ Real.log (4 * X) :=
    Real.log_le_log hYpos hYX
  have hlog4X : Real.log (4 * X) = Real.log 4 + Real.log X := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
      (ne_of_gt (lt_trans (Real.exp_pos _) hX))]
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hYscale : 1 + Real.log (Y : ℝ) ≤ 5 * Real.log X := by
    rw [hlog4X] at hlogY
    linarith
  have hYbase : 0 ≤ 1 + Real.log (Y : ℝ) := by
    have : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast hY)
    linarith
  have hpoly :
      (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) ≤ (5 * Real.log X) ^ 7 := by
    norm_num
    exact pow_le_pow_left₀ hYbase hYscale 7
  have hfiveLog : Real.log ((5 : ℝ) ^ 7) ≤ t := by
    have hlogBound := Real.log_le_sub_one_of_pos
      (by positivity : (0 : ℝ) < (5 : ℝ) ^ 7)
    linarith
  have hfive : (5 : ℝ) ^ 7 ≤ Real.exp t := by
    calc
      (5 : ℝ) ^ 7 = Real.exp (Real.log ((5 : ℝ) ^ 7)) :=
        (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp t := Real.exp_le_exp.mpr hfiveLog
  have hexpT : Real.exp t = Real.log X := by
    dsimp [t]
    exact Real.exp_log hL
  have hcTot0 : 0 ≤ cTot := by
    dsimp [cTot, lam]
    positivity
  have hquad : cTot * t ≤ t ^ 2 / 4 := by
    nlinarith [mul_nonneg hcTot0 htPos.le]
  have habs : lam * (1 + mertensSecondUpperConst) ≤
      |lam * (1 + mertensSecondUpperConst)| := le_abs_self _
  have habs0 : 0 ≤ |lam * (1 + mertensSecondUpperConst)| := abs_nonneg _
  have hconst : |lam * (1 + mertensSecondUpperConst)| ≤
      |lam * (1 + mertensSecondUpperConst)| * t := by
    nlinarith
  have hlinear :
      (8 + lam + (3 * A : ℕ)) * t + lam * (1 + mertensSecondUpperConst) ≤
        cTot * t := by
    dsimp [cTot]
    nlinarith
  have hexponent :
      t + (7 * t + (-(t ^ 2 / 4) + lam * (t + 1 + mertensSecondUpperConst))) ≤
        -((3 * A : ℕ) : ℝ) * t := by
    push_cast at hlinear ⊢
    nlinarith [hlinear, hquad]
  have htarget : Real.exp (-((3 * A : ℕ) : ℝ) * t) =
      (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
    rw [Real.rpow_def_of_pos hL]
    dsimp [t]
    congr 1
    ring
  calc
    (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) *
        ((D : ℝ) ^ (-(1 / Real.log z)) *
          Real.exp ((((2 : ℝ) ^ 3) * Real.exp 1) *
            (logLog z + mertensSecondUpperConst))) ≤
      (5 * Real.log X) ^ 7 *
        (Real.exp (-(t ^ 2 / 4)) *
          Real.exp (lam * (t + 1 + mertensSecondUpperConst))) := by
      dsimp [lam]
      gcongr
    _ = (5 : ℝ) ^ 7 * (Real.log X) ^ 7 *
        Real.exp (-(t ^ 2 / 4) + lam * (t + 1 + mertensSecondUpperConst)) := by
      rw [mul_pow, ← Real.exp_add]
    _ ≤ Real.exp t * Real.exp (7 * t) *
        Real.exp (-(t ^ 2 / 4) + lam * (t + 1 + mertensSecondUpperConst)) := by
      have hlogPow : (Real.log X) ^ 7 = Real.exp (7 * t) := by
        rw [← hexpT, ← Real.exp_nat_mul]
        norm_num
      rw [hlogPow]
      gcongr
    _ = Real.exp (t + (7 * t + (-(t ^ 2 / 4) +
        lam * (t + 1 + mertensSecondUpperConst)))) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-((3 * A : ℕ) : ℝ) * t) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hexponent]
    _ = (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := htarget

/-- Exact source-scale `d₃(n)|c₁,n|` capstone with final `(log X)^(-3A)` saving. -/
theorem eventually_sum_ternaryWeighted_norm_mtC1_le_log_rpow (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (α : ℕ → ℂ) (Y : ℕ) (B : ℝ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → 0 ≤ B → (∀ m, ‖α m‖ ≤ B) →
      ∑ n ∈ Finset.Icc 1 Y,
          (ternaryDivisorCount n : ℝ) *
            ‖mtC1Coefficient α (mtLowerCutoffNat X) (mtTruncationNat X) n‖ ≤
        B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
  filter_upwards [eventually_mtC1_integer_schedule,
    eventually_mtC1_polylog_absorption A] with X hschedule habsorb
  intro α Y B hY hYX hB hα
  obtain ⟨hz, hD, hratio, hlogLog⟩ := hschedule
  have hmean := sum_ternaryDivisorCount_mul_norm_mtC1Coefficient_le
    α hz hD hY hB hα
  have hscalar := habsorb (mtLowerCutoffNat X) (mtTruncationNat X) Y
    hY hYX hz hD hratio hlogLog
  calc
    ∑ n ∈ Finset.Icc 1 Y,
        (ternaryDivisorCount n : ℝ) *
          ‖mtC1Coefficient α (mtLowerCutoffNat X) (mtTruncationNat X) n‖ ≤
      B * ((Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) *
        ((mtTruncationNat X : ℝ) ^
            (-(1 / Real.log (mtLowerCutoffNat X))) *
          Real.exp ((((2 : ℝ) ^ 3) * Real.exp 1) *
            (logLog (mtLowerCutoffNat X) + mertensSecondUpperConst)))) := hmean
    _ = B * (Y : ℝ) *
        ((1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) *
          ((mtTruncationNat X : ℝ) ^
              (-(1 / Real.log (mtLowerCutoffNat X))) *
            Real.exp ((((2 : ℝ) ^ 3) * Real.exp 1) *
              (logLog (mtLowerCutoffNat X) + mertensSecondUpperConst)))) := by ring
    _ ≤ B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hscalar (mul_nonneg hB (Nat.cast_nonneg _))

end

end RHTower.Sieve
