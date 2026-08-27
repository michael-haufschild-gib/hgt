import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenC1Coefficient
import GaloisForLFunctions.RHTower.Sieve.PrimeWindowPaperScale

/-!
# Integer Matomäki--Teräväinen `c₁,n` schedule

This file rounds the paper's real cutoffs in the direction required by their literal natural-number
uses: `z₀` is rounded up for the prime cutoff, while the Legendre truncation level is rounded down.
The rounding loses only fixed factors and retains a quadratic `log log X` Rankin exponent.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- Natural prime cutoff representing `z₀ = exp(log X / (log log X)³)`. -/
def mtLowerCutoffNat (X : ℝ) : ℕ := Nat.ceil (mtLowerCutoff X)

/-- Logarithm of the paper's Legendre truncation level. -/
def mtTruncationLog (X : ℝ) : ℝ :=
  Real.log X / Real.log (Real.log X)

/-- Real Legendre truncation level `D = exp(log X / log log X)`. -/
def mtTruncation (X : ℝ) : ℝ := Real.exp (mtTruncationLog X)

/-- Natural truncation level representing the paper's real `D`. -/
def mtTruncationNat (X : ℝ) : ℕ := Nat.floor (mtTruncation X)

/-- The logarithm of the paper's truncation level tends to infinity. -/
theorem tendsto_mtTruncationLog_atTop :
    Tendsto mtTruncationLog atTop atTop := by
  have htend : Tendsto (fun X : ℝ => Real.log (Real.log X)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hlarge := htend.eventually_ge_atTop 1
  refine tendsto_atTop_mono' atTop ?_ tendsto_mtLowerLogCutoff_atTop
  filter_upwards [hlarge, Filter.eventually_gt_atTop (Real.exp 1)] with X ht hX
  have hL : 0 < Real.log X := by
    apply Real.log_pos
    have hone : (1 : ℝ) < Real.exp 1 := by
      simpa only [Real.exp_zero] using
        Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
    exact hone.trans hX
  have htPos : 0 < Real.log (Real.log X) := lt_of_lt_of_le zero_lt_one ht
  change Real.log X / (Real.log (Real.log X)) ^ 3 ≤
    Real.log X / Real.log (Real.log X)
  rw [div_le_div_iff₀ (pow_pos htPos 3) htPos]
  have htSq : (1 : ℝ) ≤ (Real.log (Real.log X)) ^ 2 := by
    nlinarith [sq_nonneg (Real.log (Real.log X) - 1)]
  have htCube : Real.log (Real.log X) ≤ (Real.log (Real.log X)) ^ 3 := by
    calc
      Real.log (Real.log X) = Real.log (Real.log X) * 1 := by ring
      _ ≤ Real.log (Real.log X) * (Real.log (Real.log X)) ^ 2 :=
        mul_le_mul_of_nonneg_left htSq htPos.le
      _ = (Real.log (Real.log X)) ^ 3 := by ring
  exact mul_le_mul_of_nonneg_left htCube hL.le

set_option maxHeartbeats 400000 in
/-- The rounded source schedule retains the Rankin ratio and Euler-log bounds used for `c₁,n`. -/
theorem eventually_mtC1_integer_schedule :
    ∀ᶠ X : ℝ in atTop,
      2 ≤ mtLowerCutoffNat X ∧
      0 < mtTruncationNat X ∧
      (Real.log (Real.log X)) ^ 2 / 4 ≤
        Real.log (mtTruncationNat X : ℝ) /
          Real.log (mtLowerCutoffNat X : ℝ) ∧
      logLog (mtLowerCutoffNat X) ≤ Real.log (Real.log X) + 1 := by
  have htend : Tendsto (fun X : ℝ => Real.log (Real.log X)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have ht := htend.eventually_ge_atTop 1
  have hu := tendsto_mtLowerLogCutoff_atTop.eventually_ge_atTop (Real.log 2)
  have hs := tendsto_mtTruncationLog_atTop.eventually_ge_atTop (2 * Real.log 2)
  have hzReal :=
    (Real.tendsto_exp_atTop.comp tendsto_mtLowerLogCutoff_atTop).eventually_ge_atTop 2
  filter_upwards [ht, hu, hs, hzReal,
    Filter.eventually_gt_atTop (Real.exp (Real.exp 1))] with X htX huX hsX hzX hX
  let t : ℝ := Real.log (Real.log X)
  let L : ℝ := Real.log X
  let u : ℝ := mtLowerLogCutoff X
  let s : ℝ := mtTruncationLog X
  have htPos : 0 < t := lt_of_lt_of_le zero_lt_one htX
  have hLPos : 0 < L := by
    dsimp [L]
    apply Real.log_pos
    have hone : (1 : ℝ) < Real.exp (Real.exp 1) := by
      simpa only [Real.exp_zero] using
        Real.exp_lt_exp.mpr (Real.exp_pos 1)
    exact hone.trans hX
  have hLu : Real.exp u = mtLowerCutoff X := by rfl
  have hLs : Real.exp s = mtTruncation X := by rfl
  have huPos : 0 < u := by
    dsimp [u, mtLowerLogCutoff]
    exact div_pos hLPos (pow_pos htPos 3)
  have hsPos : 0 < s := by
    dsimp [s, mtTruncationLog]
    exact div_pos hLPos htPos
  have hzCastLower : mtLowerCutoff X ≤ (mtLowerCutoffNat X : ℝ) := by
    exact Nat.le_ceil _
  have hzTwo : 2 ≤ mtLowerCutoffNat X := by
    exact_mod_cast hzX.trans hzCastLower
  have hDOne : (1 : ℝ) ≤ mtTruncation X := by
    rw [← Real.exp_zero, ← hLs]
    exact Real.exp_le_exp.mpr hsPos.le
  have hDPos : 0 < mtTruncationNat X := by
    rw [mtTruncationNat, Nat.floor_pos]
    exact hDOne
  have hceilUpper : (mtLowerCutoffNat X : ℝ) < mtLowerCutoff X + 1 := by
    exact Nat.ceil_lt_add_one (Real.exp_nonneg _)
  have hexpUOne : (1 : ℝ) ≤ Real.exp u := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr huPos.le
  have hzCastUpper : (mtLowerCutoffNat X : ℝ) ≤ 2 * Real.exp u := by
    rw [← hLu] at hceilUpper
    linarith
  have hfloorLower : Real.exp s / 2 ≤ (mtTruncationNat X : ℝ) := by
    have hlt : mtTruncation X < (mtTruncationNat X : ℝ) + 1 := by
      exact Nat.lt_floor_add_one _
    rw [← hLs] at hlt
    have hexpTwo : (2 : ℝ) ≤ Real.exp s := by
      calc
        (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
        _ ≤ Real.exp s := Real.exp_le_exp.mpr (le_trans (by
          linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]) hsX)
    linarith
  have hlogDLower : s - Real.log 2 ≤ Real.log (mtTruncationNat X : ℝ) := by
    have hhalfPos : 0 < Real.exp s / 2 := by positivity
    have hmono := Real.log_le_log hhalfPos hfloorLower
    rw [Real.log_div (Real.exp_ne_zero _) (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_exp] at hmono
    exact hmono
  have hlogzUpper : Real.log (mtLowerCutoffNat X : ℝ) ≤ u + Real.log 2 := by
    have hzCastPos : (0 : ℝ) < mtLowerCutoffNat X := by positivity
    have hmono := Real.log_le_log hzCastPos hzCastUpper
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _),
      Real.log_exp] at hmono
    linarith
  have hsHalf : s / 2 ≤ s - Real.log 2 := by
    dsimp [s] at hsX ⊢
    linarith
  have huDouble : u + Real.log 2 ≤ 2 * u := by linarith
  have hlogDHalf : s / 2 ≤ Real.log (mtTruncationNat X : ℝ) :=
    hsHalf.trans hlogDLower
  have hlogzDouble : Real.log (mtLowerCutoffNat X : ℝ) ≤ 2 * u :=
    hlogzUpper.trans huDouble
  have hlogzPos : 0 < Real.log (mtLowerCutoffNat X : ℝ) :=
    log_pos_of_two_le hzTwo
  have hu0 : 0 < 2 * u := by positivity
  have hratio : t ^ 2 / 4 ≤
      Real.log (mtTruncationNat X : ℝ) /
        Real.log (mtLowerCutoffNat X : ℝ) := by
    have hratioLower : (s / 2) / (2 * u) ≤
        Real.log (mtTruncationNat X : ℝ) /
          Real.log (mtLowerCutoffNat X : ℝ) := by
      exact div_le_div₀ (le_trans (by positivity) hlogDHalf) hlogDHalf
        hlogzPos hlogzDouble
    have hsu : (s / 2) / (2 * u) = t ^ 2 / 4 := by
      dsimp [s, u, mtTruncationLog, mtLowerLogCutoff, t, L] at *
      field_simp
      ring
    rwa [hsu] at hratioLower
  have huLeL : u ≤ L := by
    dsimp [u, mtLowerLogCutoff, L, t] at *
    rw [div_le_iff₀ (pow_pos htPos 3)]
    have htCube : (1 : ℝ) ≤ (Real.log (Real.log X)) ^ 3 := by
      simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) htX 3
    nlinarith [mul_le_mul_of_nonneg_left htCube hLPos.le]
  have hlogTwoLeL : Real.log 2 ≤ L := by
    have hlogTwoLeOne :=
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hlogTwoLeOne
    have hLOne : 1 ≤ L := by
      dsimp [L]
      have hmono := Real.log_le_log (Real.exp_pos (Real.exp 1)) hX.le
      rw [Real.log_exp] at hmono
      have honeexp : (1 : ℝ) ≤ Real.exp 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by norm_num)
      exact honeexp.trans hmono
    linarith
  have hlogzTwoL : Real.log (mtLowerCutoffNat X : ℝ) ≤ 2 * L := by
    linarith
  have htwoLPos : 0 < 2 * L := by positivity
  have hlogLogUpper : logLog (mtLowerCutoffNat X) ≤ Real.log (2 * L) := by
    unfold logLog
    exact Real.log_le_log hlogzPos hlogzTwoL
  have hlogTwoL : Real.log (2 * L) = Real.log 2 + t := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hLPos)]
  have hlogTwoOne :=
    Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at hlogTwoOne
  refine ⟨hzTwo, hDPos, ?_, ?_⟩
  · simpa only [t] using hratio
  · rw [hlogTwoL] at hlogLogUpper
    dsimp [t] at hlogLogUpper ⊢
    linarith

end

end RHTower.Sieve
