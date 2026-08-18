import GaloisForLFunctions.RHTower.BakerGeneralProof.BakerGeneralParameters

/-!
# Stage smallness for the general Baker long extrapolation

At every stage the Schwarz node ratio is at most `2/3` and the whole positive budget — the
denominator-clearing power, the boundary majorant of the component jet, and the conjugate majorant
raised to the field degree — is an exponential on the scale `q^{2n+k+3}`.  The number of prescribed
zeros is `q^{2n+k+4}/2^{k+1}`, one power of the parameter larger, so the product is eventually below
one uniformly over the stage sample window and the stage component box.
-/

open scoped Classical
open BigOperators NumberField
open Filter Topology

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

namespace GeneralParameters

theorem stageOrder_le (n q k : ℕ) : stageOrder n q k ≤ q ^ (2 * n + 2) :=
  Nat.div_le_self _ _

theorem sum_nu_le (R : SolvedRelation) {q k : ℕ} {nu : R.Direction → ℕ}
    (hnu : ∀ dir, nu dir ≤ stageOrder R.n q (k + 1)) :
    (∑ dir, nu dir) ≤ R.n * q ^ (2 * R.n + 2) := by
  calc
    (∑ dir : R.Direction, nu dir) ≤ ∑ _dir : R.Direction, q ^ (2 * R.n + 2) :=
      Finset.sum_le_sum fun dir _ => le_trans (hnu dir) (stageOrder_le _ _ _)
    _ = R.n * q ^ (2 * R.n + 2) := by
      simp [Finset.sum_const, R.card_direction, mul_comm]

/-- Boundary majorant of a stage jet, on the exponential scale of the parameter. -/
theorem eventually_jetScalarBound_le_exp
    (R : SolvedRelation) (c : ℤ) (k : ℕ) (CH : ℝ) (hCH : 0 ≤ CH) :
    ∀ᶠ q : ℕ in atTop,
      ∀ (nu : R.Direction → ℕ) (Heta : ℝ),
        (∀ dir, nu dir ≤ stageOrder R.n q (k + 1)) → 0 ≤ Heta →
        Heta ≤ Real.exp (CH * (q : ℝ) ^ (2 * R.n + 3)) →
        R.jetScalarBound c (additiveWidth R.n q) (exponentWidth R.n q) nu Heta
            ((stageRadius q k : ℕ) : ℝ) ≤
          Real.exp ((2 + CH + R.n + 2 + 4 * R.lambdaNormSum) *
            (q : ℝ) ^ (2 * R.n + k + 3)) := by
  have hL0 : 0 ≤ R.lambdaNormSum := R.lambdaNormSum_nonneg
  have hn0 : (0 : ℝ) ≤ (R.n : ℝ) := Nat.cast_nonneg _
  have hcols := eventually_const_pow_le_exp (2 : ℝ) (2 * R.n * R.n + 2 * R.n + 2)
  have hord := eventually_const_pow_le_exp (2 : ℝ) (2 * R.n + 2)
  have hrad := eventually_const_pow_le_exp (4 : ℝ) (k + 3)
  have hGrow := eventually_const_pow_le_exp
    (5 * (1 + |(c : ℝ)|) * (1 + R.eigenCoordinateHouseSum c)) (4 * R.n + 2)
  filter_upwards [hcols, hord, hrad, hGrow, eventually_ge_atTop 1] with
    q hcolsq hordq hradq hGrowq hq1
  intro nu Heta hnu hHeta0 hHeta
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hqpow : ∀ j : ℕ, (1 : ℝ) ≤ (q : ℝ) ^ j := fun j => one_le_pow₀ hq1R
  have hq0R : (0 : ℝ) ≤ (q : ℝ) := by linarith
  have hUV : ((additiveWidth R.n q * exponentWidth R.n q ^ R.n : ℕ) : ℝ) ≤ Real.exp q := by
    rw [columnCount_cast]; exact hcolsq
  have hnu1 : ((nu none + 1 : ℕ) : ℝ) ≤ Real.exp q := by
    refine le_trans ?_ hordq
    have h1 : nu none + 1 ≤ q ^ (2 * R.n + 2) + 1 :=
      Nat.add_le_add_right (le_trans (hnu none) (stageOrder_le _ _ _)) 1
    have h1R : ((nu none + 1 : ℕ) : ℝ) ≤ ((q ^ (2 * R.n + 2) + 1 : ℕ) : ℝ) := by
      exact_mod_cast h1
    refine h1R.trans ?_
    push_cast
    nlinarith [hqpow (2 * R.n + 2)]
  have hradle : ((stageRadius q k : ℕ) : ℝ) ≤ Real.exp q := by
    rw [stageRadius_cast]; exact hradq
  have hrad0 : (0 : ℝ) ≤ ((stageRadius q k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hG0 : (0 : ℝ) ≤ R.jetGrowthBase c (additiveWidth R.n q) (exponentWidth R.n q) :=
    le_trans zero_le_one (R.one_le_jetGrowthBase _ _ _)
  have hGle : R.jetGrowthBase c (additiveWidth R.n q) (exponentWidth R.n q) ≤ Real.exp q :=
    le_trans (jetGrowthBase_stage_le R c hq1) hGrowq
  have hpowG : R.jetGrowthBase c (additiveWidth R.n q) (exponentWidth R.n q) ^ (∑ dir, nu dir) ≤
      Real.exp ((q : ℝ) * ((∑ dir, nu dir : ℕ) : ℝ)) := pow_le_exp_mul hG0 hGle _
  have hpowR : ((stageRadius q k : ℕ) : ℝ) ^ (additiveWidth R.n q) ≤
      Real.exp ((q : ℝ) * ((additiveWidth R.n q : ℕ) : ℝ)) := pow_le_exp_mul hrad0 hradle _
  have hfreq : ((exponentWidth R.n q : ℕ) : ℝ) * R.lambdaNormSum *
      ((stageRadius q k : ℕ) : ℝ) =
      4 * R.lambdaNormSum * (q : ℝ) ^ (2 * R.n + k + 3) := by
    rw [exponentWidth_cast, stageRadius_cast]
    ring
  unfold _root_.GaloisForLFunctions.RHTower.BakerGeneralProof.SolvedRelation.jetScalarBound
  rw [hfreq]
  calc
    ((additiveWidth R.n q * exponentWidth R.n q ^ R.n : ℕ) : ℝ) * Heta *
        ((nu none + 1 : ℕ) : ℝ) *
        R.jetGrowthBase c (additiveWidth R.n q) (exponentWidth R.n q) ^ (∑ dir, nu dir) *
        ((stageRadius q k : ℕ) : ℝ) ^ (additiveWidth R.n q) *
        Real.exp (4 * R.lambdaNormSum * (q : ℝ) ^ (2 * R.n + k + 3)) ≤
        Real.exp q * Real.exp (CH * (q : ℝ) ^ (2 * R.n + 3)) * Real.exp q *
          Real.exp ((q : ℝ) * ((∑ dir, nu dir : ℕ) : ℝ)) *
          Real.exp ((q : ℝ) * ((additiveWidth R.n q : ℕ) : ℝ)) *
          Real.exp (4 * R.lambdaNormSum * (q : ℝ) ^ (2 * R.n + k + 3)) := by
      gcongr
    _ = Real.exp ((q : ℝ) + CH * (q : ℝ) ^ (2 * R.n + 3) + (q : ℝ) +
          (q : ℝ) * ((∑ dir, nu dir : ℕ) : ℝ) +
          (q : ℝ) * ((additiveWidth R.n q : ℕ) : ℝ) +
          4 * R.lambdaNormSum * (q : ℝ) ^ (2 * R.n + k + 3)) := by
      simp only [← Real.exp_add]
    _ ≤ Real.exp ((2 + CH + R.n + 2 + 4 * R.lambdaNormSum) *
          (q : ℝ) ^ (2 * R.n + k + 3)) := by
      refine Real.exp_le_exp.mpr ?_
      have hA : (q : ℝ) ≤ (q : ℝ) ^ (2 * R.n + k + 3) := by
        simpa using pow_le_pow_right₀ hq1R (show 1 ≤ 2 * R.n + k + 3 by omega)
      have hB : (q : ℝ) ^ (2 * R.n + 3) ≤ (q : ℝ) ^ (2 * R.n + k + 3) :=
        pow_le_pow_right₀ hq1R (by omega)
      have hsucc : (q : ℝ) * (q : ℝ) ^ (2 * R.n + 2) = (q : ℝ) ^ (2 * R.n + 3) := by
        rw [← pow_succ']
      have hsum : ((∑ dir, nu dir : ℕ) : ℝ) ≤ (R.n : ℝ) * (q : ℝ) ^ (2 * R.n + 2) := by
        have := sum_nu_le R hnu
        exact_mod_cast this
      have hC : (q : ℝ) * ((∑ dir, nu dir : ℕ) : ℝ) ≤
          (R.n : ℝ) * (q : ℝ) ^ (2 * R.n + k + 3) := by
        calc
          (q : ℝ) * ((∑ dir, nu dir : ℕ) : ℝ) ≤
              (q : ℝ) * ((R.n : ℝ) * (q : ℝ) ^ (2 * R.n + 2)) :=
            mul_le_mul_of_nonneg_left hsum hq0R
          _ = (R.n : ℝ) * (q : ℝ) ^ (2 * R.n + 3) := by rw [← hsucc]; ring
          _ ≤ (R.n : ℝ) * (q : ℝ) ^ (2 * R.n + k + 3) :=
            mul_le_mul_of_nonneg_left hB hn0
      have hD : (q : ℝ) * ((additiveWidth R.n q : ℕ) : ℝ) =
          2 * (q : ℝ) ^ (2 * R.n + 3) := by
        rw [additiveWidth_cast, ← hsucc]
        ring
      have hCH0 : 0 ≤ CH := hCH
      nlinarith [hA, hB, hC, hD, hqpow (2 * R.n + k + 3)]

theorem sample_exponent_le (n q k s : ℕ) (hs : s ≤ stageSampleCount q (k + 1)) :
    s * (n * exponentWidth n q) ≤ n * q ^ (2 * n + k + 3) := by
  calc
    s * (n * exponentWidth n q) ≤ stageSampleCount q (k + 1) * (n * exponentWidth n q) :=
      Nat.mul_le_mul_right _ hs
    _ = n * q ^ (2 * n + k + 3) := by
      unfold stageSampleCount exponentWidth
      rw [← mul_assoc, mul_comm (q ^ (k + 1 + 2)) n, mul_assoc, ← pow_add]
      congr 2
      omega

theorem sample_exponent_le' (n q k s : ℕ) (hs : s ≤ stageSampleCount q (k + 1)) :
    n * exponentWidth n q * s ≤ n * q ^ (2 * n + k + 3) := by
  have := sample_exponent_le n q k s hs
  calc
    n * exponentWidth n q * s = s * (n * exponentWidth n q) := by ring
    _ ≤ n * q ^ (2 * n + k + 3) := this

/-- Conjugate majorant of a stage jet, on the exponential scale of the parameter. -/
theorem eventually_jetHouseScalarBound_le_exp
    (R : SolvedRelation) (c d : ℤ) (k : ℕ) (CH : ℝ) (hCH : 0 ≤ CH) :
    ∀ᶠ q : ℕ in atTop,
      ∀ (nu : R.Direction → ℕ) (Heta : ℝ) (s : ℕ),
        (∀ dir, nu dir ≤ stageOrder R.n q (k + 1)) → 0 ≤ Heta →
        Heta ≤ Real.exp (CH * (q : ℝ) ^ (2 * R.n + 3)) →
        s ≤ stageSampleCount q (k + 1) →
        R.jetHouseScalarBound c d (additiveWidth R.n q) (exponentWidth R.n q) nu Heta s ≤
          Real.exp ((2 + (1 + |(d : ℝ)|) * R.n + R.n + 2 + CH + R.baseHouseBound d * R.n) *
            (q : ℝ) ^ (2 * R.n + k + 3)) := by
  have hn0 : (0 : ℝ) ≤ (R.n : ℝ) := Nat.cast_nonneg _
  have hBd : (0 : ℝ) ≤ R.baseHouseBound d :=
    le_trans zero_le_one (R.one_le_baseHouseBound d)
  have hd0 : (0 : ℝ) ≤ 1 + |(d : ℝ)| := by positivity
  have hcols := eventually_const_pow_le_exp (2 : ℝ) (2 * R.n * R.n + 2 * R.n + 2)
  have hord := eventually_const_pow_le_exp (2 : ℝ) (2 * R.n + 2)
  have hsam := eventually_const_pow_le_exp (2 : ℝ) (k + 3)
  have hGrow := eventually_const_pow_le_exp
    (5 * (1 + |(c : ℝ)|) * (1 + R.eigenCoordinateHouseSum c)) (4 * R.n + 2)
  filter_upwards [hcols, hord, hsam, hGrow, eventually_ge_atTop 1] with
    q hcolsq hordq hsamq hGrowq hq1
  intro nu Heta s hnu hHeta0 hHeta hs
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hqpow : ∀ j : ℕ, (1 : ℝ) ≤ (q : ℝ) ^ j := fun j => one_le_pow₀ hq1R
  have hq0R : (0 : ℝ) ≤ (q : ℝ) := by linarith
  have hUV : ((additiveWidth R.n q * exponentWidth R.n q ^ R.n : ℕ) : ℝ) ≤ Real.exp q := by
    rw [columnCount_cast]; exact hcolsq
  have hnu1 : ((nu none + 1 : ℕ) : ℝ) ≤ Real.exp q := by
    refine le_trans ?_ hordq
    have h1 : nu none + 1 ≤ q ^ (2 * R.n + 2) + 1 :=
      Nat.add_le_add_right (le_trans (hnu none) (stageOrder_le _ _ _)) 1
    have h1R : ((nu none + 1 : ℕ) : ℝ) ≤ ((q ^ (2 * R.n + 2) + 1 : ℕ) : ℝ) := by
      exact_mod_cast h1
    refine h1R.trans ?_
    push_cast
    nlinarith [hqpow (2 * R.n + 2)]
  have hsle : 1 + (s : ℝ) ≤ Real.exp q := by
    refine le_trans ?_ hsamq
    have h1 : (s : ℝ) ≤ (q : ℝ) ^ (k + 3) := by
      have : s ≤ q ^ (k + 3) := by
        refine le_trans hs (le_of_eq ?_)
        unfold stageSampleCount
        congr 1
      exact_mod_cast this
    nlinarith [hqpow (k + 3)]
  have hG0 : (0 : ℝ) ≤ R.jetGrowthBase c (additiveWidth R.n q) (exponentWidth R.n q) :=
    le_trans zero_le_one (R.one_le_jetGrowthBase _ _ _)
  have hGle : R.jetGrowthBase c (additiveWidth R.n q) (exponentWidth R.n q) ≤ Real.exp q :=
    le_trans (jetGrowthBase_stage_le R c hq1) hGrowq
  have hpowD : (1 + |(d : ℝ)|) ^ (s * (R.n * exponentWidth R.n q)) ≤
      Real.exp ((1 + |(d : ℝ)|) * ((s * (R.n * exponentWidth R.n q) : ℕ) : ℝ)) :=
    pow_le_exp_mul hd0 le_exp_self _
  have hpowG : R.jetGrowthBase c (additiveWidth R.n q) (exponentWidth R.n q) ^ (∑ dir, nu dir) ≤
      Real.exp ((q : ℝ) * ((∑ dir, nu dir : ℕ) : ℝ)) := pow_le_exp_mul hG0 hGle _
  have hpowS : (1 + (s : ℝ)) ^ (additiveWidth R.n q) ≤
      Real.exp ((q : ℝ) * ((additiveWidth R.n q : ℕ) : ℝ)) :=
    pow_le_exp_mul (by positivity) hsle _
  have hpowB : R.baseHouseBound d ^ (R.n * exponentWidth R.n q * s) ≤
      Real.exp (R.baseHouseBound d * ((R.n * exponentWidth R.n q * s : ℕ) : ℝ)) :=
    pow_le_exp_mul hBd le_exp_self _
  unfold _root_.GaloisForLFunctions.RHTower.BakerGeneralProof.SolvedRelation.jetHouseScalarBound
  calc
    ((additiveWidth R.n q * exponentWidth R.n q ^ R.n : ℕ) : ℝ) *
        (1 + |(d : ℝ)|) ^ (s * (R.n * exponentWidth R.n q)) *
        (((nu none + 1 : ℕ) : ℝ) *
          R.jetGrowthBase c (additiveWidth R.n q) (exponentWidth R.n q) ^ (∑ dir, nu dir) *
          (1 + (s : ℝ)) ^ (additiveWidth R.n q)) * Heta *
        R.baseHouseBound d ^ (R.n * exponentWidth R.n q * s) ≤
        Real.exp q *
          Real.exp ((1 + |(d : ℝ)|) * ((s * (R.n * exponentWidth R.n q) : ℕ) : ℝ)) *
          (Real.exp q * Real.exp ((q : ℝ) * ((∑ dir, nu dir : ℕ) : ℝ)) *
            Real.exp ((q : ℝ) * ((additiveWidth R.n q : ℕ) : ℝ))) *
          Real.exp (CH * (q : ℝ) ^ (2 * R.n + 3)) *
          Real.exp (R.baseHouseBound d * ((R.n * exponentWidth R.n q * s : ℕ) : ℝ)) := by
      gcongr
    _ = Real.exp ((q : ℝ) +
          (1 + |(d : ℝ)|) * ((s * (R.n * exponentWidth R.n q) : ℕ) : ℝ) +
          ((q : ℝ) + (q : ℝ) * ((∑ dir, nu dir : ℕ) : ℝ) +
            (q : ℝ) * ((additiveWidth R.n q : ℕ) : ℝ)) +
          CH * (q : ℝ) ^ (2 * R.n + 3) +
          R.baseHouseBound d * ((R.n * exponentWidth R.n q * s : ℕ) : ℝ)) := by
      simp only [← Real.exp_add]
    _ ≤ Real.exp ((2 + (1 + |(d : ℝ)|) * R.n + R.n + 2 + CH + R.baseHouseBound d * R.n) *
          (q : ℝ) ^ (2 * R.n + k + 3)) := by
      refine Real.exp_le_exp.mpr ?_
      have hA : (q : ℝ) ≤ (q : ℝ) ^ (2 * R.n + k + 3) := by
        simpa using pow_le_pow_right₀ hq1R (show 1 ≤ 2 * R.n + k + 3 by omega)
      have hB : (q : ℝ) ^ (2 * R.n + 3) ≤ (q : ℝ) ^ (2 * R.n + k + 3) :=
        pow_le_pow_right₀ hq1R (by omega)
      have hsucc : (q : ℝ) * (q : ℝ) ^ (2 * R.n + 2) = (q : ℝ) ^ (2 * R.n + 3) := by
        rw [← pow_succ']
      have hsum : ((∑ dir, nu dir : ℕ) : ℝ) ≤ (R.n : ℝ) * (q : ℝ) ^ (2 * R.n + 2) := by
        have := sum_nu_le R hnu
        exact_mod_cast this
      have hC : (q : ℝ) * ((∑ dir, nu dir : ℕ) : ℝ) ≤
          (R.n : ℝ) * (q : ℝ) ^ (2 * R.n + k + 3) := by
        calc
          (q : ℝ) * ((∑ dir, nu dir : ℕ) : ℝ) ≤
              (q : ℝ) * ((R.n : ℝ) * (q : ℝ) ^ (2 * R.n + 2)) :=
            mul_le_mul_of_nonneg_left hsum hq0R
          _ = (R.n : ℝ) * (q : ℝ) ^ (2 * R.n + 3) := by rw [← hsucc]; ring
          _ ≤ (R.n : ℝ) * (q : ℝ) ^ (2 * R.n + k + 3) :=
            mul_le_mul_of_nonneg_left hB hn0
      have hD : (q : ℝ) * ((additiveWidth R.n q : ℕ) : ℝ) =
          2 * (q : ℝ) ^ (2 * R.n + 3) := by
        rw [additiveWidth_cast, ← hsucc]
        ring
      have hE : ((s * (R.n * exponentWidth R.n q) : ℕ) : ℝ) ≤
          (R.n : ℝ) * (q : ℝ) ^ (2 * R.n + k + 3) := by
        have := sample_exponent_le R.n q k s hs
        exact_mod_cast this
      have hF : ((R.n * exponentWidth R.n q * s : ℕ) : ℝ) ≤
          (R.n : ℝ) * (q : ℝ) ^ (2 * R.n + k + 3) := by
        have := sample_exponent_le' R.n q k s hs
        exact_mod_cast this
      nlinarith [hA, hB, hC, hD, hE, hF, hqpow (2 * R.n + k + 3)]

theorem stageOrder_mul_two_pow {n q k : ℕ} (hdvd : 2 ^ (k + 1) ∣ q ^ (2 * n + 2)) :
    stageOrder n q (k + 1) * 2 ^ (k + 1) = q ^ (2 * n + 2) :=
  Nat.div_mul_cancel hdvd

theorem decayExponent_mul (n q k : ℕ) (hdvd : 2 ^ (k + 1) ∣ q ^ (2 * n + 2)) :
    (stageOrder n q (k + 1) * stageSampleCount q k) * 2 ^ (k + 1) = q ^ (2 * n + k + 4) := by
  unfold stageSampleCount
  calc
    stageOrder n q (k + 1) * q ^ (k + 2) * 2 ^ (k + 1) =
        (stageOrder n q (k + 1) * 2 ^ (k + 1)) * q ^ (k + 2) := by ring
    _ = q ^ (2 * n + 2) * q ^ (k + 2) := by rw [stageOrder_mul_two_pow hdvd]
    _ = q ^ (2 * n + k + 4) := by
      rw [← pow_add]
      congr 1
      omega

/-- The Schwarz node ratio is at most `2/3` throughout the stage sample window. -/
theorem node_ratio_le {q k s : ℕ} (hq : 1 ≤ q) (hs : s ≤ stageSampleCount q (k + 1)) (P : ℕ) :
    ((s + stageSampleCount q k : ℕ) : ℝ) ^ P /
        (((stageRadius q k : ℕ) : ℝ) - ((stageSampleCount q k : ℕ) : ℝ)) ^ P ≤
      ((2 : ℝ) / 3) ^ P := by
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq0R : (0 : ℝ) ≤ (q : ℝ) := by linarith
  have hpow : (q : ℝ) ^ (k + 2) ≤ (q : ℝ) ^ (k + 3) :=
    pow_le_pow_right₀ hq1R (by omega)
  have hs' : (s : ℝ) ≤ (q : ℝ) ^ (k + 3) := by
    have h1 : s ≤ q ^ (k + 3) := by
      refine le_trans hs (le_of_eq ?_)
      unfold stageSampleCount
      congr 1
    exact_mod_cast h1
  have hSc : ((stageSampleCount q k : ℕ) : ℝ) = (q : ℝ) ^ (k + 2) := stageSampleCount_cast q k
  have hRc : ((stageRadius q k : ℕ) : ℝ) = 4 * (q : ℝ) ^ (k + 3) := stageRadius_cast q k
  have hden : (0 : ℝ) < ((stageRadius q k : ℕ) : ℝ) - ((stageSampleCount q k : ℕ) : ℝ) := by
    rw [hSc, hRc]
    nlinarith [one_le_pow₀ (n := k + 3) hq1R]
  rw [← div_pow]
  refine pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hden.le) ?_ P
  rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 3)]
  push_cast
  rw [hSc, hRc]
  nlinarith [one_le_pow₀ (n := k + 2) hq1R]

theorem decay_mul_exp_lt_one {P : ℕ} {M : ℝ} (h : M < (P : ℝ) * Real.log (3 / 2)) :
    ((2 : ℝ) / 3) ^ P * Real.exp M < 1 := by
  have hlog : Real.log ((2 : ℝ) / 3) = -Real.log (3 / 2) := by
    rw [show (2 : ℝ) / 3 = ((3 : ℝ) / 2)⁻¹ by norm_num, Real.log_inv]
  have hbase : ((2 : ℝ) / 3) ^ P = Real.exp ((P : ℝ) * Real.log ((2 : ℝ) / 3)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2 / 3)]
  rw [hbase, ← Real.exp_add, hlog]
  refine Real.exp_lt_one_iff.mpr ?_
  linarith

theorem eventually_lt_succ_pow (C κ : ℝ) (hκ : 0 < κ) (α : ℕ) :
    ∀ᶠ q : ℕ in atTop, C * (q : ℝ) ^ α < κ * (q : ℝ) ^ (α + 1) := by
  have hlin : ∀ᶠ q : ℕ in atTop, C < κ * (q : ℝ) := by
    have htend : Tendsto (fun q : ℕ => κ * (q : ℝ)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hκ (tendsto_natCast_atTop_atTop (R := ℝ))
    exact htend.eventually_gt_atTop C
  filter_upwards [hlin, eventually_ge_atTop 1] with q hq hq1
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hpos : (0 : ℝ) < (q : ℝ) ^ α := by positivity
  calc
    C * (q : ℝ) ^ α < (κ * (q : ℝ)) * (q : ℝ) ^ α := by
      exact mul_lt_mul_of_pos_right hq hpos
    _ = κ * (q : ℝ) ^ (α + 1) := by rw [pow_succ]; ring

theorem jetScalarBound_nonneg (R : SolvedRelation) (c : ℤ) (U V : ℕ)
    (nu : R.Direction → ℕ) {Heta radius : ℝ} (hHeta : 0 ≤ Heta) (hradius : 0 ≤ radius) :
    0 ≤ R.jetScalarBound c U V nu Heta radius := by
  have hG0 : (0 : ℝ) ≤ R.jetGrowthBase c U V :=
    le_trans zero_le_one (R.one_le_jetGrowthBase c U V)
  unfold _root_.GaloisForLFunctions.RHTower.BakerGeneralProof.SolvedRelation.jetScalarBound
  have h1 : (0 : ℝ) ≤ ((U * V ^ R.n : ℕ) : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ ((nu none + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 hHeta) h2)
    (pow_nonneg hG0 _)) (pow_nonneg hradius _)) (Real.exp_nonneg _)

theorem jetHouseScalarBound_nonneg (R : SolvedRelation) (c d : ℤ) (U V : ℕ)
    (nu : R.Direction → ℕ) {Heta : ℝ} (hHeta : 0 ≤ Heta) (sample : ℕ) :
    0 ≤ R.jetHouseScalarBound c d U V nu Heta sample := by
  have hG0 : (0 : ℝ) ≤ R.jetGrowthBase c U V :=
    le_trans zero_le_one (R.one_le_jetGrowthBase c U V)
  have hB0 : (0 : ℝ) ≤ R.baseHouseBound d :=
    le_trans zero_le_one (R.one_le_baseHouseBound d)
  unfold _root_.GaloisForLFunctions.RHTower.BakerGeneralProof.SolvedRelation.jetHouseScalarBound
  have h1 : (0 : ℝ) ≤ ((U * V ^ R.n : ℕ) : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ ((nu none + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ (1 + |(d : ℝ)|) ^ (sample * (R.n * V)) := by positivity
  have h4 : (0 : ℝ) ≤ (1 + (sample : ℝ)) ^ U := by positivity
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 h3)
    (mul_nonneg (mul_nonneg h2 (pow_nonneg hG0 _)) h4)) hHeta) (pow_nonneg hB0 _)

/-- Uniform stage smallness: the Schwarz decay beats the whole positive budget. -/
theorem eventually_stageSmallness
    (R : SolvedRelation) (c d : ℤ) (k : ℕ) (hk : k ≤ iterationLength R.n)
    (CH : ℝ) (hCH : 0 ≤ CH) :
    ∀ᶠ u : ℕ in atTop,
      ∀ (nu : R.Direction → ℕ) (Heta : ℝ) (s : ℕ),
        (∀ dir, nu dir ≤ stageOrder R.n (structuredBase R.n u) (k + 1)) → 0 ≤ Heta →
        Heta ≤ Real.exp (CH * ((structuredBase R.n u : ℕ) : ℝ) ^ (2 * R.n + 3)) →
        s ≤ stageSampleCount (structuredBase R.n u) (k + 1) →
        (|(d : ℝ)| ^ (s * (R.n * exponentWidth R.n (structuredBase R.n u))) *
          (((s + stageSampleCount (structuredBase R.n u) k : ℕ) : ℝ) ^
              (stageOrder R.n (structuredBase R.n u) (k + 1) *
                stageSampleCount (structuredBase R.n u) k) *
            (R.jetScalarBound c (additiveWidth R.n (structuredBase R.n u))
                (exponentWidth R.n (structuredBase R.n u)) nu Heta
                ((stageRadius (structuredBase R.n u) k : ℕ) : ℝ) /
              (((stageRadius (structuredBase R.n u) k : ℕ) : ℝ) -
                ((stageSampleCount (structuredBase R.n u) k : ℕ) : ℝ)) ^
                (stageOrder R.n (structuredBase R.n u) (k + 1) *
                  stageSampleCount (structuredBase R.n u) k)))) *
          R.jetHouseScalarBound c d (additiveWidth R.n (structuredBase R.n u))
            (exponentWidth R.n (structuredBase R.n u)) nu Heta s ^
            (Module.finrank ℚ R.CoefficientField - 1) < 1 := by
  classical
  have hn0 : (0 : ℝ) ≤ (R.n : ℝ) := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ |(d : ℝ)| := abs_nonneg _
  have hL0 : 0 ≤ R.lambdaNormSum := R.lambdaNormSum_nonneg
  have hBd : (0 : ℝ) ≤ R.baseHouseBound d :=
    le_trans zero_le_one (R.one_le_baseHouseBound d)
  have hkappa : 0 < Real.log (3 / 2) / 2 ^ (k + 1) := by
    have : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
    positivity
  have hstage := eventually_jetScalarBound_le_exp R c k CH hCH
  have hhouse := eventually_jetHouseScalarBound_le_exp R c d k CH hCH
  have hcompare := eventually_lt_succ_pow
    (|(d : ℝ)| * R.n + (2 + CH + R.n + 2 + 4 * R.lambdaNormSum) +
      (Module.finrank ℚ R.CoefficientField - 1 : ℕ) *
        (2 + (1 + |(d : ℝ)|) * R.n + R.n + 2 + CH + R.baseHouseBound d * R.n))
    (Real.log (3 / 2) / 2 ^ (k + 1)) hkappa (2 * R.n + k + 3)
  have hmain := (hstage.and (hhouse.and (hcompare.and (eventually_ge_atTop 1))))
  filter_upwards [(structuredBase_tendsto_atTop R.n).eventually hmain] with u hu
  obtain ⟨hS, hH, hcmp, hq1⟩ := hu
  intro nu Heta s hnu hHeta0 hHeta hs
  have hq1R : (1 : ℝ) ≤ ((structuredBase R.n u : ℕ) : ℝ) := by exact_mod_cast hq1
  have hrad0 : (0 : ℝ) ≤ ((stageRadius (structuredBase R.n u) k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hSbound := hS nu Heta hnu hHeta0 hHeta
  have hHbound := hH nu Heta s hnu hHeta0 hHeta hs
  have hS0 := jetScalarBound_nonneg R c (additiveWidth R.n (structuredBase R.n u))
    (exponentWidth R.n (structuredBase R.n u)) nu hHeta0 hrad0
  have hH0 := jetHouseScalarBound_nonneg R c d (additiveWidth R.n (structuredBase R.n u))
    (exponentWidth R.n (structuredBase R.n u)) nu hHeta0 s
  have hdpow : |(d : ℝ)| ^ (s * (R.n * exponentWidth R.n (structuredBase R.n u))) ≤
      Real.exp ((|(d : ℝ)| * R.n) *
        ((structuredBase R.n u : ℕ) : ℝ) ^ (2 * R.n + k + 3)) := by
    refine le_trans (pow_le_exp_mul hd0 le_exp_self _) (Real.exp_le_exp.mpr ?_)
    have hle : ((s * (R.n * exponentWidth R.n (structuredBase R.n u)) : ℕ) : ℝ) ≤
        (R.n : ℝ) * ((structuredBase R.n u : ℕ) : ℝ) ^ (2 * R.n + k + 3) := by
      have := sample_exponent_le R.n (structuredBase R.n u) k s hs
      exact_mod_cast this
    calc
      |(d : ℝ)| * ((s * (R.n * exponentWidth R.n (structuredBase R.n u)) : ℕ) : ℝ) ≤
          |(d : ℝ)| * ((R.n : ℝ) *
            ((structuredBase R.n u : ℕ) : ℝ) ^ (2 * R.n + k + 3)) :=
        mul_le_mul_of_nonneg_left hle hd0
      _ = (|(d : ℝ)| * R.n) *
          ((structuredBase R.n u : ℕ) : ℝ) ^ (2 * R.n + k + 3) := by ring
  have hhousepow :
      R.jetHouseScalarBound c d (additiveWidth R.n (structuredBase R.n u))
          (exponentWidth R.n (structuredBase R.n u)) nu Heta s ^
        (Module.finrank ℚ R.CoefficientField - 1) ≤
        Real.exp (((Module.finrank ℚ R.CoefficientField - 1 : ℕ) : ℝ) *
          (2 + (1 + |(d : ℝ)|) * R.n + R.n + 2 + CH + R.baseHouseBound d * R.n) *
          ((structuredBase R.n u : ℕ) : ℝ) ^ (2 * R.n + k + 3)) := by
    calc
      _ ≤ (Real.exp ((2 + (1 + |(d : ℝ)|) * R.n + R.n + 2 + CH + R.baseHouseBound d * R.n) *
            ((structuredBase R.n u : ℕ) : ℝ) ^ (2 * R.n + k + 3))) ^
          (Module.finrank ℚ R.CoefficientField - 1) :=
        pow_le_pow_left₀ hH0 hHbound _
      _ = Real.exp (((Module.finrank ℚ R.CoefficientField - 1 : ℕ) : ℝ) *
            ((2 + (1 + |(d : ℝ)|) * R.n + R.n + 2 + CH + R.baseHouseBound d * R.n) *
              ((structuredBase R.n u : ℕ) : ℝ) ^ (2 * R.n + k + 3))) :=
        (Real.exp_nat_mul _ _).symm
      _ = _ := by rw [mul_assoc]
  have hpos :
      |(d : ℝ)| ^ (s * (R.n * exponentWidth R.n (structuredBase R.n u))) *
        R.jetScalarBound c (additiveWidth R.n (structuredBase R.n u))
          (exponentWidth R.n (structuredBase R.n u)) nu Heta
          ((stageRadius (structuredBase R.n u) k : ℕ) : ℝ) *
        R.jetHouseScalarBound c d (additiveWidth R.n (structuredBase R.n u))
          (exponentWidth R.n (structuredBase R.n u)) nu Heta s ^
          (Module.finrank ℚ R.CoefficientField - 1) ≤
        Real.exp ((|(d : ℝ)| * R.n + (2 + CH + R.n + 2 + 4 * R.lambdaNormSum) +
          ((Module.finrank ℚ R.CoefficientField - 1 : ℕ) : ℝ) *
            (2 + (1 + |(d : ℝ)|) * R.n + R.n + 2 + CH + R.baseHouseBound d * R.n)) *
          ((structuredBase R.n u : ℕ) : ℝ) ^ (2 * R.n + k + 3)) := by
    calc
      _ ≤ Real.exp ((|(d : ℝ)| * R.n) *
            ((structuredBase R.n u : ℕ) : ℝ) ^ (2 * R.n + k + 3)) *
          Real.exp ((2 + CH + R.n + 2 + 4 * R.lambdaNormSum) *
            ((structuredBase R.n u : ℕ) : ℝ) ^ (2 * R.n + k + 3)) *
          Real.exp (((Module.finrank ℚ R.CoefficientField - 1 : ℕ) : ℝ) *
            (2 + (1 + |(d : ℝ)|) * R.n + R.n + 2 + CH + R.baseHouseBound d * R.n) *
            ((structuredBase R.n u : ℕ) : ℝ) ^ (2 * R.n + k + 3)) := by
        gcongr
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have hratio :
      ((s + stageSampleCount (structuredBase R.n u) k : ℕ) : ℝ) ^
          (stageOrder R.n (structuredBase R.n u) (k + 1) *
            stageSampleCount (structuredBase R.n u) k) /
        (((stageRadius (structuredBase R.n u) k : ℕ) : ℝ) -
          ((stageSampleCount (structuredBase R.n u) k : ℕ) : ℝ)) ^
          (stageOrder R.n (structuredBase R.n u) (k + 1) *
            stageSampleCount (structuredBase R.n u) k) ≤
        ((2 : ℝ) / 3) ^ (stageOrder R.n (structuredBase R.n u) (k + 1) *
          stageSampleCount (structuredBase R.n u) k) :=
    node_ratio_le hq1 hs _
  have hratio0 : (0 : ℝ) ≤
      ((s + stageSampleCount (structuredBase R.n u) k : ℕ) : ℝ) ^
          (stageOrder R.n (structuredBase R.n u) (k + 1) *
            stageSampleCount (structuredBase R.n u) k) /
        (((stageRadius (structuredBase R.n u) k : ℕ) : ℝ) -
          ((stageSampleCount (structuredBase R.n u) k : ℕ) : ℝ)) ^
          (stageOrder R.n (structuredBase R.n u) (k + 1) *
            stageSampleCount (structuredBase R.n u) k) := by
    have hden : (0 : ℝ) < ((stageRadius (structuredBase R.n u) k : ℕ) : ℝ) -
        ((stageSampleCount (structuredBase R.n u) k : ℕ) : ℝ) := by
      rw [stageSampleCount_cast, stageRadius_cast]
      nlinarith [one_le_pow₀ (n := k + 3) hq1R,
        pow_le_pow_right₀ hq1R (show k + 2 ≤ k + 3 by omega)]
    positivity
  have hid : ∀ A B C D E : ℝ, (A * (B * (C / D))) * E = (B / D) * (A * C * E) := by
    intro A B C D E
    field_simp
  rw [hid]
  refine lt_of_le_of_lt (mul_le_mul hratio hpos
    (mul_nonneg (mul_nonneg (pow_nonneg hd0 _) hS0) (pow_nonneg hH0 _))
    (pow_nonneg (by norm_num) _)) ?_
  refine decay_mul_exp_lt_one ?_
  have hPcast : ((stageOrder R.n (structuredBase R.n u) (k + 1) *
      stageSampleCount (structuredBase R.n u) k : ℕ) : ℝ) * 2 ^ (k + 1) =
      ((structuredBase R.n u : ℕ) : ℝ) ^ (2 * R.n + k + 4) := by
    have := decayExponent_mul R.n (structuredBase R.n u) k (structuredBase_dvd R.n u k hk)
    exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) this
  have h2pos : (0 : ℝ) < 2 ^ (k + 1) := by positivity
  have hPval : ((stageOrder R.n (structuredBase R.n u) (k + 1) *
      stageSampleCount (structuredBase R.n u) k : ℕ) : ℝ) =
      ((structuredBase R.n u : ℕ) : ℝ) ^ (2 * R.n + k + 4) / 2 ^ (k + 1) := by
    field_simp at hPcast ⊢
    linarith [hPcast]
  rw [hPval]
  have hsucc : (2 * R.n + k + 3 + 1) = 2 * R.n + k + 4 := by omega
  rw [hsucc] at hcmp
  have hlogpos : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  calc
    (|(d : ℝ)| * R.n + (2 + CH + R.n + 2 + 4 * R.lambdaNormSum) +
        ((Module.finrank ℚ R.CoefficientField - 1 : ℕ) : ℝ) *
          (2 + (1 + |(d : ℝ)|) * R.n + R.n + 2 + CH + R.baseHouseBound d * R.n)) *
        ((structuredBase R.n u : ℕ) : ℝ) ^ (2 * R.n + k + 3) <
        Real.log (3 / 2) / 2 ^ (k + 1) *
          ((structuredBase R.n u : ℕ) : ℝ) ^ (2 * R.n + k + 4) := hcmp
    _ = ((structuredBase R.n u : ℕ) : ℝ) ^ (2 * R.n + k + 4) / 2 ^ (k + 1) *
          Real.log (3 / 2) := by ring

end GeneralParameters

end GaloisForLFunctions.RHTower.BakerGeneralProof
