import GaloisForLFunctions.RHTower.Sieve.PrimeWindowLogPowerSchedule
import GaloisForLFunctions.RHTower.Sieve.ScheduleMonomialLimits

/-!
# Matomäki--Teräväinen paper scale for short prime windows

This file substitutes the paper's lower cutoff
`z₀ = exp(log X / (log log X)³)` and relative block width
`δ_A = (log X)⁻¹⁰ᴬ` into the uniform prime-window mean square.  The exponential Mertens error is
first bounded by the stronger lower-end power with exponent `10A+1`; the spare logarithmic power
absorbs the fixed power of `log log X`.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- Logarithm of the lower sieve cutoff used in the paper. -/
def mtLowerLogCutoff (X : ℝ) : ℝ :=
  Real.log X / (Real.log (Real.log X)) ^ 3

/-- Lower sieve cutoff `z₀ = exp(log X / (log log X)³)`. -/
def mtLowerCutoff (X : ℝ) : ℝ :=
  Real.exp (mtLowerLogCutoff X)

/-- Relative adic width `δ_A = (log X)⁻¹⁰ᴬ`. -/
def mtPaperWidth (A : ℕ) (X : ℝ) : ℝ :=
  (Real.log X) ^ (-((10 * A : ℕ) : ℝ))

/-- At the lower cutoff, the spare log power absorbs all three powers of `log log X`. -/
theorem eventually_mtLowerLogCutoff_rpow_le_paperWidth (A : ℕ) :
    ∀ᶠ X : ℝ in atTop,
      (mtLowerLogCutoff X) ^ (-((10 * A + 1 : ℕ) : ℝ)) ≤ mtPaperWidth A X := by
  change ∀ᶠ X : ℝ in atTop,
    (Real.log X / (Real.log (Real.log X)) ^ 3) ^
        (-((10 * A + 1 : ℕ) : ℝ)) ≤
      (Real.log X) ^ (-((10 * A : ℕ) : ℝ))
  have hlim := tendsto_logRpow_mul_logLogPow
    (e := (-1 : ℝ)) (by norm_num) (3 * (10 * A + 1))
  have hsmall := hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hsmall, Filter.eventually_gt_atTop (Real.exp (Real.exp 1))]
    with X hs hX
  have hL : 0 < Real.log X := by
    apply Real.log_pos
    have : (1 : ℝ) < Real.exp (Real.exp 1) := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (Real.exp_pos 1)
    linarith
  have hLL : 0 < Real.log (Real.log X) := by
    apply Real.log_pos
    have hexp : Real.exp 1 < Real.log X := by
      have hmono := Real.strictMonoOn_log (Real.exp_pos (Real.exp 1))
        (lt_trans (Real.exp_pos (Real.exp 1)) hX) hX
      simpa only [Real.log_exp] using hmono
    have hone : (1 : ℝ) < Real.exp 1 := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
    linarith
  have heq :
      (Real.log X / (Real.log (Real.log X)) ^ 3) ^
          (-((10 * A + 1 : ℕ) : ℝ)) =
        (Real.log X) ^ (-((10 * A : ℕ) : ℝ)) *
          ((Real.log X) ^ (-1 : ℝ) *
            (Real.log (Real.log X)) ^ (3 * (10 * A + 1))) := by
    have hexp :
        -((10 * A + 1 : ℕ) : ℝ) =
          -((10 * A : ℕ) : ℝ) + (-1 : ℝ) := by
      push_cast
      ring
    calc
      (Real.log X / (Real.log (Real.log X)) ^ 3) ^
          (-((10 * A + 1 : ℕ) : ℝ)) =
        (Real.log X) ^ (-((10 * A + 1 : ℕ) : ℝ)) /
          ((Real.log (Real.log X)) ^ 3) ^ (-((10 * A + 1 : ℕ) : ℝ)) :=
            Real.div_rpow hL.le (pow_nonneg hLL.le 3) _
      _ = (Real.log X) ^ (-((10 * A + 1 : ℕ) : ℝ)) *
          ((Real.log (Real.log X)) ^ 3) ^ ((10 * A + 1 : ℕ) : ℝ) := by
            rw [Real.rpow_neg (pow_nonneg hLL.le 3)]
            simp only [div_eq_mul_inv, inv_inv]
      _ = (Real.log X) ^ (-((10 * A + 1 : ℕ) : ℝ)) *
          (Real.log (Real.log X)) ^ (3 * (10 * A + 1)) := by
            rw [Real.rpow_natCast, pow_mul]
      _ = (Real.log X) ^ (-((10 * A : ℕ) : ℝ)) *
          ((Real.log X) ^ (-1 : ℝ) *
            (Real.log (Real.log X)) ^ (3 * (10 * A + 1))) := by
            rw [← mul_assoc, ← Real.rpow_add hL, ← hexp]
  rw [heq]
  have hright : 0 ≤ (Real.log X) ^ (-((10 * A : ℕ) : ℝ)) :=
    Real.rpow_nonneg hL.le _
  nlinarith [hs]

/-- The logarithm of the paper's lower cutoff tends to infinity. -/
theorem tendsto_mtLowerLogCutoff_atTop : Tendsto mtLowerLogCutoff atTop atTop := by
  change Tendsto
    (fun X : ℝ => Real.log X / (Real.log (Real.log X)) ^ 3) atTop atTop
  have hll := eventually_logLogPow_le_rpow 3 (ε := (1 / 2 : ℝ)) (by norm_num)
  have hsqrt : Tendsto (fun X : ℝ => Real.sqrt (Real.log X)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  refine tendsto_atTop_mono' atTop ?_ hsqrt
  filter_upwards [hll, Filter.eventually_gt_atTop (Real.exp (Real.exp 1))]
    with X hllX hX
  have hL : 0 < Real.log X := by
    apply Real.log_pos
    have : (1 : ℝ) < Real.exp (Real.exp 1) := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (Real.exp_pos 1)
    linarith
  have hLL : 0 < Real.log (Real.log X) := by
    apply Real.log_pos
    have hexp : Real.exp 1 < Real.log X := by
      have hmono := Real.strictMonoOn_log (Real.exp_pos (Real.exp 1))
        (lt_trans (Real.exp_pos (Real.exp 1)) hX) hX
      simpa only [Real.log_exp] using hmono
    have hone : (1 : ℝ) < Real.exp 1 := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
    linarith
  have hsqrt_eq : (Real.log X) ^ (1 / 2 : ℝ) = Real.sqrt (Real.log X) := by
    rw [Real.sqrt_eq_rpow]
  rw [← hsqrt_eq, le_div_iff₀ (pow_pos hLL 3)]
  calc
    (Real.log X) ^ (1 / 2 : ℝ) * (Real.log (Real.log X)) ^ 3 ≤
        (Real.log X) ^ (1 / 2 : ℝ) * (Real.log X) ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hllX (Real.rpow_nonneg hL.le _)
    _ = Real.log X := by
      rw [← Real.rpow_add hL]
      norm_num

/-- Every endpoint above `z₀` inherits the stronger lower-end log-power bound. -/
theorem eventually_log_rpow_le_paperWidth_of_mtLowerLogCutoff_le (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ {u : ℝ},
      mtLowerLogCutoff X ≤ Real.log u →
      (Real.log u) ^ (-((10 * A + 1 : ℕ) : ℝ)) ≤ mtPaperWidth A X := by
  filter_upwards [eventually_mtLowerLogCutoff_rpow_le_paperWidth A,
    Filter.eventually_gt_atTop (Real.exp (Real.exp 1))] with X hscale hX
  intro u hu
  have hL : 0 < Real.log X := by
    apply Real.log_pos
    have : (1 : ℝ) < Real.exp (Real.exp 1) := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (Real.exp_pos 1)
    linarith
  have hLL : 0 < Real.log (Real.log X) := by
    apply Real.log_pos
    have hexp : Real.exp 1 < Real.log X := by
      have hmono := Real.strictMonoOn_log (Real.exp_pos (Real.exp 1))
        (lt_trans (Real.exp_pos (Real.exp 1)) hX) hX
      simpa only [Real.log_exp] using hmono
    have hone : (1 : ℝ) < Real.exp 1 := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
    linarith
  have hbase : 0 < mtLowerLogCutoff X :=
    div_pos hL (pow_pos hLL 3)
  exact (Real.rpow_le_rpow_of_nonpos hbase hu
    (neg_nonpos.mpr (Nat.cast_nonneg _))).trans hscale

/-- Exact `c₂,n` one-block mean square at the paper's `z₀` and `δ_A` scales. -/
theorem eventually_primeWindow_paperLogWidth (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ ⦃a b Y : ℕ⦄,
      mtLowerCutoff X ≤ ((a - 1 : ℕ) : ℝ) →
      a ≤ b →
      ((b - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((a - 1 : ℕ) : ℝ) →
      ∑ n ∈ Finset.Icc 1 Y, ((primeWindow n a b).card : ℝ) ^ 2 ≤
        6 * (Y : ℝ) * mtPaperWidth A X := by
  obtain ⟨B, c, N₀, hc, hB, hN₀, hblock⟩ :=
    exists_sum_sq_card_primeWindow_le_six_mul_delta
  have herr := eventually_two_mul_exp_neg_sqrt_log_le_log_rpow_neg
    (K := ((10 * A + 1 : ℕ) : ℝ)) hB hc
  rw [eventually_atTop] at herr
  obtain ⟨U, hU⟩ := herr
  have hcutoff : Tendsto mtLowerCutoff atTop atTop := by
    exact Real.tendsto_exp_atTop.comp tendsto_mtLowerLogCutoff_atTop
  have hlarge := hcutoff.eventually_ge_atTop (max (N₀ : ℝ) U)
  filter_upwards [hlarge,
    eventually_log_rpow_le_paperWidth_of_mtLowerLogCutoff_le A,
    Filter.eventually_ge_atTop (Real.exp 1)] with X hlargeX hscaleX hX
  intro a b Y hcut hab hband
  let δ : ℝ := mtPaperWidth A X
  have hu0R : 0 < ((a - 1 : ℕ) : ℝ) :=
    (Real.exp_pos (mtLowerLogCutoff X)).trans_le hcut
  have hu0 : 0 < a - 1 := by exact_mod_cast hu0R
  have ha : 1 ≤ a := by omega
  have hN₀R : (N₀ : ℝ) ≤ ((a - 1 : ℕ) : ℝ) :=
    (le_max_left _ _).trans (hlargeX.trans hcut)
  have hN₀a : N₀ ≤ a - 1 := by exact_mod_cast hN₀R
  have hUR : U ≤ ((a - 1 : ℕ) : ℝ) :=
    (le_max_right _ _).trans (hlargeX.trans hcut)
  have herru := hU (((a - 1 : ℕ) : ℝ)) hUR
  have hlogcut : mtLowerLogCutoff X ≤ Real.log ((a - 1 : ℕ) : ℝ) := by
    have hmono := Real.log_le_log (Real.exp_pos (mtLowerLogCutoff X)) hcut
    simpa only [mtLowerCutoff, Real.log_exp] using hmono
  have hsmallPower := hscaleX hlogcut
  have herrδ :
      2 * B * Real.exp (-c * Real.sqrt (Real.log ((a - 1 : ℕ) : ℝ))) ≤ δ :=
    herru.trans hsmallPower
  have hlog1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le ((Real.exp_pos 1).trans_le hX)]
    exact hX
  have hlogpos : 0 < Real.log X := lt_of_lt_of_le zero_lt_one hlog1
  have hδ0 : 0 ≤ δ := Real.rpow_nonneg hlogpos.le _
  have hδ1 : δ ≤ 1 := by
    dsimp [δ, mtPaperWidth]
    rw [Real.rpow_neg hlogpos.le]
    exact inv_le_one_of_one_le₀
      (Real.one_le_rpow hlog1 (by positivity : 0 ≤ ((10 * A : ℕ) : ℝ)))
  exact hblock ha hab hN₀a hδ0 hδ1 hband herrδ

end

end RHTower.Sieve
