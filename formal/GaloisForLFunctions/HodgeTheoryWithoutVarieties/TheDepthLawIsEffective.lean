import GaloisForLFunctions.HodgeTheoryWithoutVarieties.TheDepthOfAStarIsItsEnergy
import GaloisForLFunctions.SquareRootThreshold.EffectiveHorizons.ExplicitPrimeNumberTheorem

/-!
# The depth law with explicit horizons

For `0 < ε ≤ 1` put `Q = ⌈exp((20 log(25600/ε))²)⌉ + 3` and `H(ε) = ⌈exp(2 + 24 Q (log Q + 2)/ε)⌉`.

* **Sharp counterterm** (`atomicWeilForm_le_of_depthHorizon`): `P_N ≤ (log N − γ + ε)|x|²` for every `N ≥ H(ε)`.
* **Sharp depth law** (`renormalizedPrimeForm_starRestrict_ge_of_depthHorizon`): on the star of `d`, with `⌊N/d⌋ ≥ H(ε)`,
  `R_N ≥ (log d − ε)|x|²`.

The only input is the explicit Mertens theorem: above `Q` it gives the Mertens threshold of the tilted pole's rows, and
the horizon `H(ε)` pays the top rows.
-/

noncomputable section

open Finset
open GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties

local notation "γ" => Real.eulerMascheroniConstant

/-- The Mertens cutoff of precision `ε`. -/
def mertensCutoff (ε : ℝ) : ℕ := ⌈Real.exp ((20 * Real.log (25600 / ε)) ^ 2)⌉₊ + 2

/-- Above the cutoff the Mertens sum is within `ε/4` of `log q − γ`. -/
theorem mertensSum_sub_log_lt {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {q : ℕ} (hq : mertensCutoff ε ≤ q) :
    mertensSum q - Real.log q < -γ + ε / 2 := by
  have hq2 : (2 : ℝ) ≤ q := by
    have : 2 ≤ q := by
      have h : 2 ≤ mertensCutoff ε := by unfold mertensCutoff; omega
      omega
    exact_mod_cast this
  have hq0 : (0 : ℝ) < q := by linarith only [hq2]
  obtain ⟨B, hB⟩ : ∃ B, B = 20 * Real.log (25600 / ε) := ⟨_, rfl⟩
  have hlog0 : 0 ≤ Real.log (25600 / ε) :=
    Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith only [hε1])
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hexp : Real.exp (B ^ 2) ≤ q := by
    have h1 : (⌈Real.exp (B ^ 2)⌉₊ : ℝ) ≤ q := by
      have : ⌈Real.exp (B ^ 2)⌉₊ ≤ q := by
        rw [hB]
        unfold mertensCutoff at hq
        omega
      exact_mod_cast this
    exact (Nat.le_ceil _).trans h1
  have hlogq : B ^ 2 ≤ Real.log q := by
    rw [Real.le_log_iff_exp_le hq0]
    exact hexp
  have hsqrt : B ≤ Real.sqrt (Real.log q) := Real.le_sqrt_of_sq_le hlogq
  have hm := RHTower.ExplicitPNT.abs_mertens_sub_le hq2
  rw [Nat.floor_natCast] at hm
  have hdecay : Real.exp (-(Real.sqrt (Real.log q) / 20)) ≤ ε / 25600 := by
    have h1 : Real.exp (-(Real.sqrt (Real.log q) / 20)) ≤ Real.exp (-(B / 20)) :=
      Real.exp_le_exp.2 (by linarith only [hsqrt])
    have h2 : Real.exp (-(B / 20)) = ε / 25600 := by
      have e : -(B / 20) = Real.log (ε / 25600) := by
        rw [hB, Real.log_div (by norm_num) hε.ne', Real.log_div hε.ne' (by norm_num)]
        ring
      rw [e, Real.exp_log (by positivity)]
    rw [h2] at h1
    exact h1
  have hup := (abs_le.1 hm).2
  have hup2 : ∑ n ∈ Icc 1 q, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) - Real.log q + γ ≤ ε / 4 := by
    refine hup.trans ?_
    have := mul_le_mul_of_nonneg_left hdecay (by norm_num : (0 : ℝ) ≤ 6400)
    linarith only [this]
  have hsum : mertensSum q = ∑ n ∈ Icc 1 q, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) := rfl
  rw [hsum]
  linarith only [hup2, hε]

/-- The logarithm of the depth horizon. -/
def depthLogHorizon (ε : ℝ) : ℝ :=
  2 + 24 * ((mertensCutoff ε + 1 : ℕ) : ℝ) * (Real.log ((mertensCutoff ε + 1 : ℕ) : ℝ) + 2) / ε

/-- The explicit depth horizon. -/
def depthHorizon (ε : ℝ) : ℕ := ⌈Real.exp (depthLogHorizon ε)⌉₊

theorem depthLogHorizon_le_log {ε : ℝ} {N : ℕ} (hN : depthHorizon ε ≤ N) :
    depthLogHorizon ε ≤ Real.log N ∧ 1 ≤ N := by
  have h1 : Real.exp (depthLogHorizon ε) ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hpos := Real.exp_pos (depthLogHorizon ε)
  have hN0 : (0 : ℝ) < N := hpos.trans_le h1
  refine ⟨(Real.le_log_iff_exp_le hN0).2 h1, ?_⟩
  exact_mod_cast hN0

/-- **The sharp counterterm with an explicit horizon.** -/
theorem atomicWeilForm_le_of_depthHorizon {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {N : ℕ} (hN : depthHorizon ε ≤ N)
    (x : ℕ → ℝ) : atomicWeilForm N x ≤ (Real.log N - γ + ε) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  obtain ⟨hL, hN1⟩ := depthLogHorizon_le_log hN
  refine atomicWeilForm_le_sharp_of_row hε
    (row_tiltedPole_le_of_mertens_threshold hε (Q₀ := mertensCutoff ε)
      (fun q hq => mertensSum_sub_log_lt hε hε1 hq) ?_ hN1) x
  refine le_trans ?_ hL
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = mertensCutoff ε + 1 := ⟨_, rfl⟩
  have hQ1 : (1 : ℝ) ≤ Q := by
    rw [hQ]
    push_cast
    linarith only [(Nat.cast_nonneg (mertensCutoff ε) : (0 : ℝ) ≤ (mertensCutoff ε : ℝ))]
  rw [depthLogHorizon, ← hQ]
  have hlogQ : 0 ≤ Real.log (Q : ℝ) := Real.log_nonneg hQ1
  have hγ : γ < 1 := Real.eulerMascheroniConstant_lt_two_thirds.trans (by norm_num)
  have hγ0 : 0 < γ := (by norm_num : (0 : ℝ) < 1 / 2).trans Real.one_half_lt_eulerMascheroniConstant
  have hlog4 : Real.log 4 ≤ 2 := by
    have e : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    have := Real.log_two_lt_d9
    rw [e]
    linarith only [this]
  have hlog40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hA : mertensSum Q + γ + 1 ≤ Real.log (Q : ℝ) + 2 := by
    have := mertensSum_sub_log_lt hε hε1 (q := Q) (by rw [hQ]; omega)
    linarith only [this, hε1]
  have hA0 : 0 ≤ mertensSum Q := sum_nonneg fun t _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hη : (Q : ℝ) * (mertensSum Q + γ + 1) / (ε / (2 * (Real.log 4 + 4))) =
      (Q : ℝ) * (mertensSum Q + γ + 1) * (2 * (Real.log 4 + 4)) / ε := by
    field_simp
  rw [hη]
  have hle : (Q : ℝ) * (mertensSum Q + γ + 1) * (2 * (Real.log 4 + 4)) ≤
      (Q : ℝ) * (Real.log (Q : ℝ) + 2) * 12 := by
    have h1 : (Q : ℝ) * (mertensSum Q + γ + 1) ≤ (Q : ℝ) * (Real.log (Q : ℝ) + 2) :=
      mul_le_mul_of_nonneg_left hA (by linarith only [hQ1])
    exact mul_le_mul h1 (by linarith only [hlog4]) (by positivity) (by positivity)
  have hdiv := div_le_div_of_nonneg_right hle hε.le
  have e : 24 * (Q : ℝ) * (Real.log (Q : ℝ) + 2) / ε = 2 * ((Q : ℝ) * (Real.log (Q : ℝ) + 2) * 12 / ε) := by ring
  rw [e]
  linarith only [hdiv, hγ]

/-- **The sharp depth law with an explicit horizon.** On the star of `d`, once `⌊N/d⌋ ≥ H(ε)`, the renormalized prime
form is at least `(log d − ε)` times the mass. -/
theorem renormalizedPrimeForm_starRestrict_ge_of_depthHorizon {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {d N : ℕ} (hd : 0 < d)
    (hdN : d ≤ N) (hM : depthHorizon ε ≤ N / d) (x : ℕ → ℝ) :
    (Real.log d - ε) * ∑ n ∈ Icc 1 N, starRestrict d x n ^ 2 ≤
      renormalizedPrimeForm N (starRestrict d x) := by
  rw [renormalizedPrimeForm_starRestrict hd, sum_sq_starRestrict hd, renormalizedPrimeForm]
  have h1 := atomicWeilForm_le_of_depthHorizon hε hε1 hM (starPullback d x)
  have h2 := log_le_log_sub_log_div hd hdN
  have hmass : 0 ≤ ∑ a ∈ Icc 1 (N / d), starPullback d x a ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  nlinarith only [h1, h2, hmass]

end GaloisForLFunctions.HodgeTheoryWithoutVarieties

#print axioms GaloisForLFunctions.HodgeTheoryWithoutVarieties.atomicWeilForm_le_of_depthHorizon
#print axioms GaloisForLFunctions.HodgeTheoryWithoutVarieties.renormalizedPrimeForm_starRestrict_ge_of_depthHorizon
