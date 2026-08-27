import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenDivisorBoundedError

/-!
# Matomäki--Teräväinen Lemma 2.3(i) for divisor-bounded coefficients

The repaired finite iteration produces coefficients bounded by `B * d(m)`, not by a depth-
dependent constant.  This file absorbs the resulting fixed fifth divisor moment at the literal
paper scales.  The exponent stays independent of iteration depth.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

set_option maxHeartbeats 500000 in
/-- The quadratic Rankin exponent absorbs the fixed fifth divisor moment. -/
theorem eventually_mtC1_fifthMoment_polylog_absorption (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (z D Y : ℕ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → 2 ≤ z → 0 < D →
      (Real.log (Real.log X)) ^ 2 / 4 ≤ Real.log (D : ℝ) / Real.log (z : ℝ) →
      logLog z ≤ Real.log (Real.log X) + 1 →
      (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) *
          ((D : ℝ) ^ (-(1 / Real.log z)) *
            Real.exp ((((2 : ℝ) ^ 5) * Real.exp 1) *
              (logLog z + mertensSecondUpperConst))) ≤
        (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
  let lam : ℝ := ((2 : ℝ) ^ 5) * Real.exp 1
  let cTot : ℝ := 32 + lam + (3 * A : ℕ) +
    |lam * (1 + mertensSecondUpperConst)|
  have htend : Tendsto (fun X : ℝ => Real.log (Real.log X)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hlarge := htend.eventually_ge_atTop
    (max ((5 : ℝ) ^ 31) (max 1 (4 * cTot)))
  filter_upwards [hlarge, Filter.eventually_gt_atTop (Real.exp (Real.exp 1))]
    with X ht hX
  intro z D Y hY hYX hz hD hratio hlogLog
  let t : ℝ := Real.log (Real.log X)
  have htFive : (5 : ℝ) ^ 31 ≤ t :=
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
      (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) ≤ (5 * Real.log X) ^ 31 := by
    norm_num
    exact pow_le_pow_left₀ hYbase hYscale 31
  have hfiveLog : Real.log ((5 : ℝ) ^ 31) ≤ t := by
    have hlogBound := Real.log_le_sub_one_of_pos
      (by positivity : (0 : ℝ) < (5 : ℝ) ^ 31)
    linarith
  have hfive : (5 : ℝ) ^ 31 ≤ Real.exp t := by
    calc
      (5 : ℝ) ^ 31 = Real.exp (Real.log ((5 : ℝ) ^ 31)) :=
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
      (32 + lam + (3 * A : ℕ)) * t + lam * (1 + mertensSecondUpperConst) ≤
        cTot * t := by
    dsimp [cTot]
    nlinarith
  have hexponent :
      t + (31 * t + (-(t ^ 2 / 4) + lam * (t + 1 + mertensSecondUpperConst))) ≤
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
    (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) *
        ((D : ℝ) ^ (-(1 / Real.log z)) *
          Real.exp ((((2 : ℝ) ^ 5) * Real.exp 1) *
            (logLog z + mertensSecondUpperConst))) ≤
      (5 * Real.log X) ^ 31 *
        (Real.exp (-(t ^ 2 / 4)) *
          Real.exp (lam * (t + 1 + mertensSecondUpperConst))) := by
      dsimp [lam]
      gcongr
    _ = (5 : ℝ) ^ 31 * (Real.log X) ^ 31 *
        Real.exp (-(t ^ 2 / 4) + lam * (t + 1 + mertensSecondUpperConst)) := by
      rw [mul_pow, ← Real.exp_add]
    _ ≤ Real.exp t * Real.exp (31 * t) *
        Real.exp (-(t ^ 2 / 4) + lam * (t + 1 + mertensSecondUpperConst)) := by
      have hlogPow : (Real.log X) ^ 31 = Real.exp (31 * t) := by
        rw [← hexpT, ← Real.exp_nat_mul]
        norm_num
      rw [hlogPow]
      gcongr
    _ = Real.exp (t + (31 * t + (-(t ^ 2 / 4) +
        lam * (t + 1 + mertensSecondUpperConst)))) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-((3 * A : ℕ) : ℝ) * t) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hexponent]
    _ = (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := htarget

/-- Paper width absorbs fifth-moment polylogarithm and one outer harmonic factor. -/
theorem eventually_mt_fifthMoment_width_absorption (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop, ∀ (Y N : ℕ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → 1 ≤ N → (N : ℝ) ≤ X →
      (4 : ℝ) ^ 5 * (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) *
          (2 * mtPaperWidth A X) * (1 + Real.log (N : ℝ)) ≤
        (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
  have hαβ : (32 : ℝ) - ((10 * A : ℕ) : ℝ) < -((3 * A : ℕ) : ℝ) := by
    have hAR : (5 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
    push_cast
    linarith
  have hkey := eventually_const_mul_rpow_polylog_le_rpow
    (C := (4 : ℝ) ^ 6 * (5 : ℝ) ^ 31)
      (α := (32 : ℝ) - ((10 * A : ℕ) : ℝ))
      (β := -((3 * A : ℕ) : ℝ)) 0 hαβ
  have hkeyX := Real.tendsto_log_atTop.eventually hkey
  filter_upwards [hkeyX, Filter.eventually_ge_atTop (Real.exp 1)] with X hkeyX hX
  intro Y N hY hYX hN hNX
  have hL1 : 1 ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos 1) hX
    simpa only [Real.log_exp] using hmono
  have hL : 0 < Real.log X := lt_of_lt_of_le zero_lt_one hL1
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hY)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
  have hlogY : Real.log (Y : ℝ) ≤ Real.log 4 + Real.log X := by
    have hmono := Real.log_le_log hYpos hYX
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hXpos.ne'] at hmono
    exact hmono
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hYscale : 1 + Real.log (Y : ℝ) ≤ 5 * Real.log X := by linarith
  have hYbase0 : 0 ≤ 1 + Real.log (Y : ℝ) := by
    have : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast hY)
    linarith
  have hNlog : Real.log (N : ℝ) ≤ Real.log X := Real.log_le_log hNpos hNX
  have hNscale : 1 + Real.log (N : ℝ) ≤ 2 * Real.log X := by linarith
  have hδ0 : 0 ≤ mtPaperWidth A X := by
    rw [mtPaperWidth]
    exact Real.rpow_nonneg hL.le _
  have hrough :
      (4 : ℝ) ^ 5 * (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) *
          (2 * mtPaperWidth A X) * (1 + Real.log (N : ℝ)) ≤
        (4 : ℝ) ^ 5 * (5 * Real.log X) ^ 31 *
          (2 * mtPaperWidth A X) * (2 * Real.log X) := by
    norm_num
    gcongr
  calc
    (4 : ℝ) ^ 5 * (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) *
        (2 * mtPaperWidth A X) * (1 + Real.log (N : ℝ)) ≤
      (4 : ℝ) ^ 5 * (5 * Real.log X) ^ 31 *
        (2 * mtPaperWidth A X) * (2 * Real.log X) := hrough
    _ = ((4 : ℝ) ^ 6 * (5 : ℝ) ^ 31) *
        (Real.log X) ^ ((32 : ℝ) - ((10 * A : ℕ) : ℝ)) := by
      rw [mtPaperWidth]
      rw [show (5 * Real.log X) ^ 31 =
        (5 : ℝ) ^ 31 * (Real.log X) ^ 31 by ring]
      have hpow : (Real.log X) ^ 31 *
          (Real.log X) ^ (-((10 * A : ℕ) : ℝ)) * Real.log X =
          (Real.log X) ^ ((32 : ℝ) - ((10 * A : ℕ) : ℝ)) := by
        have hfirst : (Real.log X) ^ 31 *
            (Real.log X) ^ (-((10 * A : ℕ) : ℝ)) =
            (Real.log X) ^ ((31 : ℝ) + (-((10 * A : ℕ) : ℝ))) := by
          simpa using (Real.rpow_add hL (31 : ℝ)
            (-((10 * A : ℕ) : ℝ))).symm
        have hsecond :
            (Real.log X) ^ ((31 : ℝ) + (-((10 * A : ℕ) : ℝ))) *
              Real.log X =
            (Real.log X) ^ (((31 : ℝ) + (-((10 * A : ℕ) : ℝ))) + 1) := by
          simpa using (Real.rpow_add hL
            ((31 : ℝ) + (-((10 * A : ℕ) : ℝ))) (1 : ℝ)).symm
        calc
          (Real.log X) ^ 31 * (Real.log X) ^ (-((10 * A : ℕ) : ℝ)) *
              Real.log X =
            (Real.log X) ^ ((31 : ℝ) + (-((10 * A : ℕ) : ℝ))) *
              Real.log X := congrArg (fun x => x * Real.log X) hfirst
          _ = (Real.log X) ^
              (((31 : ℝ) + (-((10 * A : ℕ) : ℝ))) + 1) := hsecond
          _ = (Real.log X) ^ ((32 : ℝ) - ((10 * A : ℕ) : ℝ)) := by
            congr 1
            push_cast
            ring
      rw [← hpow]
      ring
    _ ≤ (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
      simpa using hkeyX

/-- Truncation error with a divisor-bounded coefficient has the source saving. -/
theorem eventually_sum_divisor_ternary_norm_mtC1_le_log_rpow (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (α : ℕ → ℂ) (Y : ℕ) (B : ℝ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → 0 ≤ B → MTDivisorBounded α B →
      ∑ n ∈ Finset.Icc 1 Y,
          (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
            ‖mtC1Coefficient α (mtLowerCutoffNat X) (mtTruncationNat X) n‖ ≤
        B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
  filter_upwards [eventually_mtC1_integer_schedule,
    eventually_mtC1_fifthMoment_polylog_absorption A] with X hschedule habsorb
  intro α Y B hY hYX hB hα
  obtain ⟨hz, hD, hratio, hlogLog⟩ := hschedule
  have hpoint :
      ∑ n ∈ Finset.Icc 1 Y,
          (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
            ‖mtC1Coefficient α (mtLowerCutoffNat X) (mtTruncationNat X) n‖ ≤
        B * ∑ n ∈ Finset.Icc 1 Y,
          weightedSiftTailDivisorCount 5 (mtLowerCutoffNat X) (mtTruncationNat X) n := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hnPos : 0 < n := by
      rw [Finset.mem_Icc] at hn
      omega
    exact divisor_mul_ternary_mul_norm_mtC1Coefficient_le
      α (z := mtLowerCutoffNat X) (D := mtTruncationNat X) hnPos hB hα
  have hweighted := sum_weightedSiftTailDivisorCount_le
    5 (mtLowerCutoffNat X) (mtTruncationNat X) Y hY
  have heuler := sum_largeSiftDivisors_card_pow_div_le
    5 hz hD
  have hlogY : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast hY)
  have hmean :
      ∑ n ∈ Finset.Icc 1 Y,
          weightedSiftTailDivisorCount 5 (mtLowerCutoffNat X) (mtTruncationNat X) n ≤
        (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) *
          ((mtTruncationNat X : ℝ) ^
              (-(1 / Real.log (mtLowerCutoffNat X))) *
            Real.exp ((((2 : ℝ) ^ 5) * Real.exp 1) *
              (logLog (mtLowerCutoffNat X) + mertensSecondUpperConst))) := by
    exact hweighted.trans (mul_le_mul_of_nonneg_left heuler (by positivity))
  have hscalar := habsorb (mtLowerCutoffNat X) (mtTruncationNat X) Y
    hY hYX hz hD hratio hlogLog
  calc
    ∑ n ∈ Finset.Icc 1 Y,
        (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
          ‖mtC1Coefficient α (mtLowerCutoffNat X) (mtTruncationNat X) n‖ ≤
      B * ∑ n ∈ Finset.Icc 1 Y,
        weightedSiftTailDivisorCount 5 (mtLowerCutoffNat X) (mtTruncationNat X) n := hpoint
    _ ≤ B * ((Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) *
        ((mtTruncationNat X : ℝ) ^
            (-(1 / Real.log (mtLowerCutoffNat X))) *
          Real.exp ((((2 : ℝ) ^ 5) * Real.exp 1) *
            (logLog (mtLowerCutoffNat X) + mertensSecondUpperConst)))) :=
      mul_le_mul_of_nonneg_left hmean hB
    _ = B * (Y : ℝ) *
        ((1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) *
          ((mtTruncationNat X : ℝ) ^
              (-(1 / Real.log (mtLowerCutoffNat X))) *
            Real.exp ((((2 : ℝ) ^ 5) * Real.exp 1) *
              (logLog (mtLowerCutoffNat X) + mertensSecondUpperConst)))) := by ring
    _ ≤ B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hscalar (mul_nonneg hB (Nat.cast_nonneg _))

/-- Endpoint error with a divisor-bounded coefficient has the source saving. -/
theorem eventually_sum_divisor_ternary_norm_mtC2_le_log_rpow
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (α : ℕ → ℂ) (level : ℕ → ℕ)
        (aLower bLower aUpper bUpper Y : ℕ) (B : ℝ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X →
      mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((aLower - 1 : ℕ) : ℝ) →
      aLower ≤ bLower →
      ((bLower - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((aLower - 1 : ℕ) : ℝ) →
      mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((aUpper - 1 : ℕ) : ℝ) →
      aUpper ≤ bUpper →
      ((bUpper - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((aUpper - 1 : ℕ) : ℝ) →
      0 ≤ B → MTDivisorBounded α B →
      ∑ n ∈ Finset.Icc 1 Y,
          (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
            ‖mtC2Coefficient α (primesIco aLower bLower)
              (primesIco aUpper bUpper) level n‖ ≤
        B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
  filter_upwards [eventually_sum_inv_primesIco_relaxedPaperCutoff A,
    eventually_mt_fifthMoment_width_absorption A hA,
    Filter.eventually_ge_atTop 1] with X hmassX habsorbX hX
  intro α level aLower bLower aUpper bUpper Y B hY hYX
    hLowerCut hLowerOrder hLowerBand hUpperCut hUpperOrder hUpperBand hB hα
  have hLowerMass := hmassX hLowerCut hLowerOrder hLowerBand
  have hUpperMass := hmassX hUpperCut hUpperOrder hUpperBand
  have hprimeLower : ∀ q ∈ primesIco aLower bLower, q.Prime := by
    intro q hq
    exact (mem_primesIco.mp hq).2.2
  have hprimeUpper : ∀ q ∈ primesIco aUpper bUpper, q.Prime := by
    intro q hq
    exact (mem_primesIco.mp hq).2.2
  have hpoint :
      ∑ n ∈ Finset.Icc 1 Y,
          (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
            ‖mtC2Coefficient α (primesIco aLower bLower)
              (primesIco aUpper bUpper) level n‖ ≤
        B * ∑ n ∈ Finset.Icc 1 Y,
          (weightedPrimeDivisorCount 5 (primesIco aLower bLower) n +
            weightedPrimeDivisorCount 5 (primesIco aUpper bUpper) n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hnPos : 0 < n := by
      rw [Finset.mem_Icc] at hn
      omega
    exact divisor_mul_ternary_mul_norm_mtC2Coefficient_le
      α (primesIco aLower bLower) (primesIco aUpper bUpper) level hnPos hB hα
  let C : ℝ := (2 : ℝ) ^ 5 * (Y : ℝ) *
    (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1)
  have hmeanLower := sum_weightedPrimeDivisorCount_le
    5 Y hY (primesIco aLower bLower) hprimeLower
  have hmeanUpper := sum_weightedPrimeDivisorCount_le
    5 Y hY (primesIco aUpper bUpper) hprimeUpper
  have hweighted :
      ∑ n ∈ Finset.Icc 1 Y,
          (weightedPrimeDivisorCount 5 (primesIco aLower bLower) n +
            weightedPrimeDivisorCount 5 (primesIco aUpper bUpper) n) ≤
        C * (4 * mtPaperWidth A X) := by
    rw [Finset.sum_add_distrib]
    calc
      (∑ n ∈ Finset.Icc 1 Y,
          weightedPrimeDivisorCount 5 (primesIco aLower bLower) n) +
          ∑ n ∈ Finset.Icc 1 Y,
            weightedPrimeDivisorCount 5 (primesIco aUpper bUpper) n ≤
        C * (∑ q ∈ primesIco aLower bLower, 1 / (q : ℝ)) +
          C * ∑ q ∈ primesIco aUpper bUpper, 1 / (q : ℝ) :=
        add_le_add hmeanLower hmeanUpper
      _ = C * ((∑ q ∈ primesIco aLower bLower, 1 / (q : ℝ)) +
          ∑ q ∈ primesIco aUpper bUpper, 1 / (q : ℝ)) := by ring
      _ ≤ C * (4 * mtPaperWidth A X) := by
        have hC : 0 ≤ C := by
          dsimp [C]
          have hlog : 0 ≤ Real.log (Y : ℝ) :=
            Real.log_nonneg (by exact_mod_cast hY)
          positivity
        exact mul_le_mul_of_nonneg_left (by linarith) hC
  have hscalar := habsorbX Y 1 hY hYX (by omega : 1 ≤ (1 : ℕ))
    (by exact_mod_cast hX)
  have hlogY : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast hY)
  have hwidth : 0 ≤ mtPaperWidth A X := by
    rw [mtPaperWidth]
    exact Real.rpow_nonneg (Real.log_nonneg hX) _
  have hcompare :
      (2 : ℝ) ^ 5 * (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) *
          (4 * mtPaperWidth A X) ≤
        (4 : ℝ) ^ 5 * (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) *
          (2 * mtPaperWidth A X) * (1 + Real.log (1 : ℝ)) := by
    norm_num [Real.log_one]
    have hbase : 0 ≤ 1 + Real.log (Y : ℝ) := by linarith
    have hpoly : 0 ≤ (1 + Real.log (Y : ℝ)) ^ 31 := pow_nonneg hbase _
    nlinarith [mul_nonneg hpoly hwidth]
  calc
    ∑ n ∈ Finset.Icc 1 Y,
        (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
          ‖mtC2Coefficient α (primesIco aLower bLower)
            (primesIco aUpper bUpper) level n‖ ≤
      B * ∑ n ∈ Finset.Icc 1 Y,
        (weightedPrimeDivisorCount 5 (primesIco aLower bLower) n +
          weightedPrimeDivisorCount 5 (primesIco aUpper bUpper) n) := hpoint
    _ ≤ B * (C * (4 * mtPaperWidth A X)) :=
      mul_le_mul_of_nonneg_left hweighted hB
    _ = B * (Y : ℝ) *
        ((2 : ℝ) ^ 5 * (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) *
          (4 * mtPaperWidth A X)) := by
      dsimp [C]
      ring
    _ ≤ B * (Y : ℝ) *
        ((4 : ℝ) ^ 5 * (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) *
          (2 * mtPaperWidth A X) * (1 + Real.log (1 : ℝ))) := by
      have hBY : 0 ≤ B * (Y : ℝ) := mul_nonneg hB (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left hcompare hBY
    _ ≤ B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB (Nat.cast_nonneg _))
      simpa only [Nat.cast_one] using hscalar

/-- Buchstab replacement error with a divisor-bounded coefficient has the source saving. -/
theorem eventually_sum_divisor_ternary_norm_mtC3_le_log_rpow
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (α : ℕ → ℂ) (S : Finset ℕ) (lower : ℕ → ℕ)
        (Y N : ℕ) (B : ℝ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → 1 ≤ N → (N : ℝ) ≤ X →
      (∀ q ∈ S, q.Prime) → (∀ q ∈ S, q ≤ N) →
      (∀ q ∈ S,
        mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((lower q - 1 : ℕ) : ℝ)) →
      (∀ q ∈ S, lower q ≤ q) →
      (∀ q ∈ S, ((q - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((lower q - 1 : ℕ) : ℝ)) →
      0 ≤ B → MTDivisorBounded α B →
      ∑ n ∈ Finset.Icc 1 Y,
          (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
            ‖mtC3Coefficient α S lower n‖ ≤
        B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
  filter_upwards [eventually_lowerC3FibreMass_paperWidth A,
    eventually_mt_fifthMoment_width_absorption A hA] with X hmassX habsorbX
  intro α S lower Y N B hY hYX hN hNX hprime hupper
    hlowerCut hlower hband hB hα
  have hpairPrime : ∀ q ∈ S, ∀ p ∈ primesIco (lower q) q, p.Prime := by
    intro q hq p hp
    exact (mem_primesIco.mp hp).2.2
  have hfibre := hmassX S lower hlowerCut hlower hband
  have hpoint :
      ∑ n ∈ Finset.Icc 1 Y,
          (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
            ‖mtC3Coefficient α S lower n‖ ≤
        B * ∑ n ∈ Finset.Icc 1 Y,
          weightedPrimePairDivisorCount 5 S (fun q => primesIco (lower q) q) n := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hnPos : 0 < n := by
      rw [Finset.mem_Icc] at hn
      omega
    exact divisor_mul_ternary_mul_norm_mtC3Coefficient_le
      α S lower hnPos hprime hlower hB hα
  have hweighted := sum_weightedPrimePairDivisorCount_le_of_fibreMass
    5 Y hY S (fun q => primesIco (lower q) q) hprime hpairPrime hfibre
  have houter : ∑ q ∈ S, 1 / (q : ℝ) ≤ 1 + Real.log N :=
    sum_inv_finset_le_one_add_log S N (fun q hq => (hprime q hq).pos) hupper
  have hlogY : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast hY)
  have hwidth : 0 ≤ mtPaperWidth A X := by
    rw [mtPaperWidth]
    have hX1 : (1 : ℝ) ≤ X := (by exact_mod_cast hN : (1 : ℝ) ≤ (N : ℝ)).trans hNX
    exact Real.rpow_nonneg (Real.log_nonneg hX1) _
  have hfactor0 : 0 ≤ (4 : ℝ) ^ 5 * (Y : ℝ) *
      (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) * (2 * mtPaperWidth A X) := by
    positivity
  have hscalar := habsorbX Y N hY hYX hN hNX
  calc
    ∑ n ∈ Finset.Icc 1 Y,
        (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
          ‖mtC3Coefficient α S lower n‖ ≤
      B * ∑ n ∈ Finset.Icc 1 Y,
        weightedPrimePairDivisorCount 5 S (fun q => primesIco (lower q) q) n := hpoint
    _ ≤ B * ((4 : ℝ) ^ 5 * (Y : ℝ) *
        (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) *
          (2 * mtPaperWidth A X) * ∑ q ∈ S, 1 / (q : ℝ)) :=
      mul_le_mul_of_nonneg_left hweighted hB
    _ ≤ B * ((4 : ℝ) ^ 5 * (Y : ℝ) *
        (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) *
          (2 * mtPaperWidth A X) * (1 + Real.log N)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left houter hfactor0) hB
    _ = B * (Y : ℝ) *
        ((4 : ℝ) ^ 5 * (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) *
          (2 * mtPaperWidth A X) * (1 + Real.log N)) := by ring
    _ ≤ B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hscalar (mul_nonneg hB (Nat.cast_nonneg _))

/-- Combined divisor-weighted first moment at literal paper scales. -/
theorem eventually_sum_divisor_ternary_norm_mtLemma23Error_le_log_rpow
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (α : ℕ → ℂ) (lower : ℕ → ℕ)
        (z₁ aLower bLower aUpper bUpper Y : ℕ) (B : ℝ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → 1 ≤ z₁ → (z₁ : ℝ) ≤ X →
      mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((aLower - 1 : ℕ) : ℝ) →
      aLower ≤ bLower →
      ((bLower - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((aLower - 1 : ℕ) : ℝ) →
      mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((aUpper - 1 : ℕ) : ℝ) →
      aUpper ≤ bUpper →
      ((bUpper - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((aUpper - 1 : ℕ) : ℝ) →
      (∀ q ∈ primesIco (mtLowerCutoffNat X) z₁,
        mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((lower q - 1 : ℕ) : ℝ)) →
      (∀ q ∈ primesIco (mtLowerCutoffNat X) z₁, lower q ≤ q) →
      (∀ q ∈ primesIco (mtLowerCutoffNat X) z₁, ((q - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((lower q - 1 : ℕ) : ℝ)) →
      0 ≤ B → MTDivisorBounded α B →
      ∑ n ∈ Finset.Icc 1 Y,
          (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
            ‖mtLemma23Error α (mtLowerCutoffNat X) (mtTruncationNat X)
              (primesIco aLower bLower) (primesIco aUpper bUpper)
              (primesIco (mtLowerCutoffNat X) z₁) lower n‖ ≤
        3 * B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
  filter_upwards [eventually_sum_divisor_ternary_norm_mtC1_le_log_rpow A,
    eventually_sum_divisor_ternary_norm_mtC2_le_log_rpow A hA,
    eventually_sum_divisor_ternary_norm_mtC3_le_log_rpow A hA]
    with X hc1X hc2X hc3X
  intro α lower z₁ aLower bLower aUpper bUpper Y B hY hYX hz₁ hZ₁X
    hLowerCut hLowerOrder hLowerBand hUpperCut hUpperOrder hUpperBand
    hlowerCut hlower hband hB hα
  have hc1 := hc1X α Y B hY hYX hB hα
  have hc2 := hc2X α lower aLower bLower aUpper bUpper Y B hY hYX
    hLowerCut hLowerOrder hLowerBand hUpperCut hUpperOrder hUpperBand hB hα
  have hprime : ∀ q ∈ primesIco (mtLowerCutoffNat X) z₁, q.Prime := by
    intro q hq
    exact (mem_primesIco.mp hq).2.2
  have hupper : ∀ q ∈ primesIco (mtLowerCutoffNat X) z₁, q ≤ z₁ := by
    intro q hq
    exact (mem_primesIco.mp hq).2.1.le
  have hc3 := hc3X α (primesIco (mtLowerCutoffNat X) z₁) lower Y z₁ B
    hY hYX hz₁ hZ₁X hprime hupper hlowerCut hlower hband hB hα
  have hpoint : ∀ n ∈ Finset.Icc 1 Y,
      (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
          ‖mtLemma23Error α (mtLowerCutoffNat X) (mtTruncationNat X)
            (primesIco aLower bLower) (primesIco aUpper bUpper)
            (primesIco (mtLowerCutoffNat X) z₁) lower n‖ ≤
        (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
            ‖mtC1Coefficient α (mtLowerCutoffNat X) (mtTruncationNat X) n‖ +
          (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
            ‖mtC2Coefficient α (primesIco aLower bLower)
              (primesIco aUpper bUpper) lower n‖ +
          (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
            ‖mtC3Coefficient α (primesIco (mtLowerCutoffNat X) z₁) lower n‖ := by
    intro n hn
    unfold mtLemma23Error
    have hnorm := (norm_add_le
      (mtC1Coefficient α (mtLowerCutoffNat X) (mtTruncationNat X) n +
        mtC2Coefficient α (primesIco aLower bLower)
          (primesIco aUpper bUpper) lower n)
      (mtC3Coefficient α (primesIco (mtLowerCutoffNat X) z₁) lower n)).trans
        (add_le_add (norm_add_le _ _) le_rfl)
    calc
      (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
          ‖mtC1Coefficient α (mtLowerCutoffNat X) (mtTruncationNat X) n +
              mtC2Coefficient α (primesIco aLower bLower)
                (primesIco aUpper bUpper) lower n +
            mtC3Coefficient α (primesIco (mtLowerCutoffNat X) z₁) lower n‖ ≤
        (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
          (‖mtC1Coefficient α (mtLowerCutoffNat X) (mtTruncationNat X) n‖ +
            ‖mtC2Coefficient α (primesIco aLower bLower)
              (primesIco aUpper bUpper) lower n‖ +
            ‖mtC3Coefficient α (primesIco (mtLowerCutoffNat X) z₁) lower n‖) := by
        gcongr
      _ = _ := by ring
  calc
    ∑ n ∈ Finset.Icc 1 Y,
        (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
          ‖mtLemma23Error α (mtLowerCutoffNat X) (mtTruncationNat X)
            (primesIco aLower bLower) (primesIco aUpper bUpper)
            (primesIco (mtLowerCutoffNat X) z₁) lower n‖ ≤
      ∑ n ∈ Finset.Icc 1 Y,
        ((n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
            ‖mtC1Coefficient α (mtLowerCutoffNat X) (mtTruncationNat X) n‖ +
          (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
            ‖mtC2Coefficient α (primesIco aLower bLower)
              (primesIco aUpper bUpper) lower n‖ +
          (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
            ‖mtC3Coefficient α (primesIco (mtLowerCutoffNat X) z₁) lower n‖) :=
        Finset.sum_le_sum hpoint
    _ = (∑ n ∈ Finset.Icc 1 Y,
          (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
            ‖mtC1Coefficient α (mtLowerCutoffNat X) (mtTruncationNat X) n‖) +
        (∑ n ∈ Finset.Icc 1 Y,
          (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
            ‖mtC2Coefficient α (primesIco aLower bLower)
              (primesIco aUpper bUpper) lower n‖) +
        (∑ n ∈ Finset.Icc 1 Y,
          (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
            ‖mtC3Coefficient α (primesIco (mtLowerCutoffNat X) z₁) lower n‖) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) +
        B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) +
        B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) :=
      add_le_add (add_le_add hc1 hc2) hc3
    _ = 3 * B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by ring

/-- Divisor-bounded Lemma 2.3(i): one step retains depth-independent mean-square saving. -/
theorem eventually_sum_norm_sq_mtLemma23Error_le_log_rpow_of_divisorBounded
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (α : ℕ → ℂ) (lower : ℕ → ℕ)
        (z₁ aLower bLower aUpper bUpper Y : ℕ) (B : ℝ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → 1 ≤ z₁ → (z₁ : ℝ) ≤ X →
      mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((aLower - 1 : ℕ) : ℝ) →
      aLower ≤ bLower →
      ((bLower - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((aLower - 1 : ℕ) : ℝ) →
      mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((aUpper - 1 : ℕ) : ℝ) →
      aUpper ≤ bUpper →
      ((bUpper - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((aUpper - 1 : ℕ) : ℝ) →
      (∀ q ∈ primesIco (mtLowerCutoffNat X) z₁,
        mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((lower q - 1 : ℕ) : ℝ)) →
      (∀ q ∈ primesIco (mtLowerCutoffNat X) z₁, lower q ≤ q) →
      (∀ q ∈ primesIco (mtLowerCutoffNat X) z₁, ((q - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((lower q - 1 : ℕ) : ℝ)) →
      0 ≤ B → MTDivisorBounded α B →
      ∑ n ∈ Finset.Icc 1 Y,
          ‖mtLemma23Error α (mtLowerCutoffNat X) (mtTruncationNat X)
            (primesIco aLower bLower) (primesIco aUpper bUpper)
            (primesIco (mtLowerCutoffNat X) z₁) lower n‖ ^ 2 ≤
        15 * B ^ 2 * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
  filter_upwards [eventually_sum_divisor_ternary_norm_mtLemma23Error_le_log_rpow A hA]
    with X hweightedX
  intro α lower z₁ aLower bLower aUpper bUpper Y B hY hYX hz₁ hZ₁X
    hLowerCut hLowerOrder hLowerBand hUpperCut hUpperOrder hUpperBand
    hlowerCut hlower hband hB hα
  have hweighted := hweightedX α lower z₁ aLower bLower aUpper bUpper Y B
    hY hYX hz₁ hZ₁X hLowerCut hLowerOrder hLowerBand hUpperCut hUpperOrder hUpperBand
    hlowerCut hlower hband hB hα
  have hsq := sum_norm_sq_mtLemma23Error_le_five_mul_divisor_weighted
    α (mtLowerCutoffNat X) (mtTruncationNat X)
    (primesIco aLower bLower) (primesIco aUpper bUpper)
    (primesIco (mtLowerCutoffNat X) z₁) lower Y hB hα
  calc
    ∑ n ∈ Finset.Icc 1 Y,
        ‖mtLemma23Error α (mtLowerCutoffNat X) (mtTruncationNat X)
          (primesIco aLower bLower) (primesIco aUpper bUpper)
          (primesIco (mtLowerCutoffNat X) z₁) lower n‖ ^ 2 ≤
      5 * B * ∑ n ∈ Finset.Icc 1 Y,
        (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
          ‖mtLemma23Error α (mtLowerCutoffNat X) (mtTruncationNat X)
            (primesIco aLower bLower) (primesIco aUpper bUpper)
            (primesIco (mtLowerCutoffNat X) z₁) lower n‖ := hsq
    _ ≤ 5 * B *
        (3 * B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hweighted (mul_nonneg (by norm_num) hB)
    _ = 15 * B ^ 2 * (Y : ℝ) *
        (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by ring

end

end RHTower.Sieve
