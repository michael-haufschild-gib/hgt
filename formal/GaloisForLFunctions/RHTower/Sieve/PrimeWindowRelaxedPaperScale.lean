import GaloisForLFunctions.RHTower.Sieve.PrimePairPaperScale

/-!
# Prime-window mass at the relaxed lower paper cutoff

The first `(1+δ_A)`-adic block in Matomäki--Teräväinen starts as low as
`z₀/(1+δ_A)`.  This file extends the paper-scale reciprocal prime-window estimate to that literal
boundary.  Half the logarithm of `z₀` still tends to infinity, while two spare logarithmic powers
absorb the fixed factor introduced by this relaxation.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- Two spare lower-cutoff powers absorb the fixed factor from halving `log z₀`. -/
theorem eventually_twoPow_mul_mtLowerLogCutoff_rpow_le_paperWidth (A : ℕ) :
    ∀ᶠ X : ℝ in atTop,
      (2 : ℝ) ^ (10 * A + 2) *
        (mtLowerLogCutoff X) ^ (-((10 * A + 2 : ℕ) : ℝ)) ≤ mtPaperWidth A X := by
  have hlim0 := tendsto_logRpow_mul_logLogPow
    (e := (-2 : ℝ)) (by norm_num) (3 * (10 * A + 2))
  have hlim : Tendsto (fun X : ℝ =>
      (2 : ℝ) ^ (10 * A + 2) *
        ((Real.log X) ^ (-2 : ℝ) *
          (Real.log (Real.log X)) ^ (3 * (10 * A + 2)))) atTop (𝓝 0) := by
    simpa using hlim0.const_mul ((2 : ℝ) ^ (10 * A + 2))
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
      (mtLowerLogCutoff X) ^ (-((10 * A + 2 : ℕ) : ℝ)) =
        mtPaperWidth A X *
          ((Real.log X) ^ (-2 : ℝ) *
            (Real.log (Real.log X)) ^ (3 * (10 * A + 2))) := by
    have hexp :
        -((10 * A + 2 : ℕ) : ℝ) = -((10 * A : ℕ) : ℝ) + (-2 : ℝ) := by
      push_cast
      ring
    rw [mtLowerLogCutoff, mtPaperWidth]
    calc
      (Real.log X / (Real.log (Real.log X)) ^ 3) ^
          (-((10 * A + 2 : ℕ) : ℝ)) =
        (Real.log X) ^ (-((10 * A + 2 : ℕ) : ℝ)) /
          ((Real.log (Real.log X)) ^ 3) ^ (-((10 * A + 2 : ℕ) : ℝ)) :=
            Real.div_rpow hL.le (pow_nonneg hLL.le 3) _
      _ = (Real.log X) ^ (-((10 * A + 2 : ℕ) : ℝ)) *
          ((Real.log (Real.log X)) ^ 3) ^ ((10 * A + 2 : ℕ) : ℝ) := by
        rw [Real.rpow_neg (pow_nonneg hLL.le 3)]
        simp only [div_eq_mul_inv, inv_inv]
      _ = (Real.log X) ^ (-((10 * A + 2 : ℕ) : ℝ)) *
          (Real.log (Real.log X)) ^ (3 * (10 * A + 2)) := by
        rw [Real.rpow_natCast, pow_mul]
      _ = (Real.log X) ^ (-((10 * A : ℕ) : ℝ)) *
          ((Real.log X) ^ (-2 : ℝ) *
            (Real.log (Real.log X)) ^ (3 * (10 * A + 2))) := by
        rw [← mul_assoc, ← Real.rpow_add hL, ← hexp]
  rw [heq]
  have hwidth : 0 ≤ mtPaperWidth A X := by
    rw [mtPaperWidth]
    positivity
  have hs' : (2 : ℝ) ^ (10 * A + 2) *
      ((Real.log X) ^ (-2 : ℝ) *
        (Real.log (Real.log X)) ^ (3 * (10 * A + 2))) ≤ 1 := hs.le
  nlinarith

/-- A lower endpoint whose log is at least half `log z₀` inherits the stronger error power. -/
theorem eventually_log_rpow_le_paperWidth_of_half_mtLowerLogCutoff_le (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ {u : ℝ},
      mtLowerLogCutoff X / 2 ≤ Real.log u →
      (Real.log u) ^ (-((10 * A + 2 : ℕ) : ℝ)) ≤ mtPaperWidth A X := by
  filter_upwards [eventually_twoPow_mul_mtLowerLogCutoff_rpow_le_paperWidth A,
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
  have hbase : 0 < mtLowerLogCutoff X := div_pos hL (pow_pos hLL 3)
  calc
    (Real.log u) ^ (-((10 * A + 2 : ℕ) : ℝ)) ≤
        (mtLowerLogCutoff X / 2) ^ (-((10 * A + 2 : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hu
        (neg_nonpos.mpr (Nat.cast_nonneg _))
    _ = (2 : ℝ) ^ (10 * A + 2) *
        (mtLowerLogCutoff X) ^ (-((10 * A + 2 : ℕ) : ℝ)) := by
      rw [Real.div_rpow hbase.le (by norm_num : (0 : ℝ) ≤ 2)]
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      rw [Real.rpow_natCast]
      field_simp
    _ ≤ mtPaperWidth A X := hscale

/-- The literal relaxed cutoff `z₀/(1+δ_A)` still has log at least half `log z₀`. -/
theorem eventually_half_mtLowerLogCutoff_le_log_of_relaxedCutoff (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ {u : ℝ},
      mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ u →
      mtLowerLogCutoff X / 2 ≤ Real.log u := by
  have hlarge := tendsto_mtLowerLogCutoff_atTop.eventually_ge_atTop (2 * Real.log 2)
  filter_upwards [hlarge, Filter.eventually_ge_atTop (Real.exp 1)] with X hcut hX
  intro u hu
  have hlog1 : 1 ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos 1) hX
    simpa only [Real.log_exp] using hmono
  have hδ0 : 0 ≤ mtPaperWidth A X := by
    rw [mtPaperWidth]
    positivity
  have hδ1 : mtPaperWidth A X ≤ 1 := by
    rw [mtPaperWidth, Real.rpow_neg (by linarith : 0 ≤ Real.log X)]
    exact inv_le_one_of_one_le₀
      (Real.one_le_rpow hlog1 (by positivity : (0 : ℝ) ≤ ((10 * A : ℕ) : ℝ)))
  have hhalfExp : 2 ≤ Real.exp (mtLowerLogCutoff X / 2) := by
    have hmono := Real.exp_le_exp.mpr (by linarith : Real.log 2 ≤ mtLowerLogCutoff X / 2)
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using hmono
  have hexpFactor : Real.exp (mtLowerLogCutoff X / 2) ≤ mtLowerCutoff X / 2 := by
    rw [mtLowerCutoff]
    have hexpAdd : Real.exp (mtLowerLogCutoff X) =
        Real.exp (mtLowerLogCutoff X / 2) * Real.exp (mtLowerLogCutoff X / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexpAdd, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    nlinarith [Real.exp_pos (mtLowerLogCutoff X / 2)]
  have hfrac : mtLowerCutoff X / 2 ≤
      mtLowerCutoff X / (1 + mtPaperWidth A X) := by
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by linarith) (by linarith)
  have hexpLe : Real.exp (mtLowerLogCutoff X / 2) ≤ u := hexpFactor.trans (hfrac.trans hu)
  have hlog := Real.log_le_log (Real.exp_pos _) hexpLe
  simpa only [Real.log_exp] using hlog

/-- Reciprocal mass for a paper-width block beginning at the literal relaxed cutoff. -/
theorem eventually_sum_inv_primesIco_relaxedPaperCutoff (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ ⦃a b : ℕ⦄,
      mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((a - 1 : ℕ) : ℝ) →
      a ≤ b →
      ((b - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((a - 1 : ℕ) : ℝ) →
      ∑ p ∈ primesIco a b, 1 / (p : ℝ) ≤ 2 * mtPaperWidth A X := by
  obtain ⟨B, c, N₀, hc, hB, hN₀, hmass⟩ :=
    exists_sum_inv_primesIco_le_logLog_diff_add_exp
  have herr := eventually_two_mul_exp_neg_sqrt_log_le_log_rpow_neg
    (K := ((10 * A + 2 : ℕ) : ℝ)) hB hc
  rw [eventually_atTop] at herr
  obtain ⟨U, hU⟩ := herr
  have hhalfCutoff : Tendsto (fun X : ℝ => Real.exp (mtLowerLogCutoff X / 2)) atTop atTop := by
    apply Real.tendsto_exp_atTop.comp
    simpa only [div_eq_mul_inv, one_div, one_mul, mul_comm] using
      tendsto_mtLowerLogCutoff_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  have hlarge := hhalfCutoff.eventually_ge_atTop (max (N₀ : ℝ) U)
  filter_upwards [hlarge,
    eventually_log_rpow_le_paperWidth_of_half_mtLowerLogCutoff_le A,
    eventually_half_mtLowerLogCutoff_le_log_of_relaxedCutoff A,
    Filter.eventually_ge_atTop (Real.exp 1)] with X hlargeX hscaleX hrelaxX hX
  intro a b hcut hab hband
  let δ : ℝ := mtPaperWidth A X
  have hlogX : 0 ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos 1) hX
    rw [Real.log_exp] at hmono
    linarith
  have hδ0 : 0 ≤ δ := by
    dsimp [δ, mtPaperWidth]
    exact Real.rpow_nonneg hlogX _
  have hrelaxedPos : 0 < mtLowerCutoff X / (1 + mtPaperWidth A X) := by
    exact div_pos (Real.exp_pos _) (by linarith)
  have hu0R : 0 < ((a - 1 : ℕ) : ℝ) := hrelaxedPos.trans_le hcut
  have hu0 : 0 < a - 1 := by exact_mod_cast hu0R
  have ha : 1 ≤ a := by omega
  have hhalfLog : mtLowerLogCutoff X / 2 ≤ Real.log ((a - 1 : ℕ) : ℝ) := hrelaxX hcut
  have hhalfExp : Real.exp (mtLowerLogCutoff X / 2) ≤ ((a - 1 : ℕ) : ℝ) := by
    have hmono := Real.exp_le_exp.mpr hhalfLog
    simpa only [Real.exp_log hu0R] using hmono
  have hN₀R : (N₀ : ℝ) ≤ ((a - 1 : ℕ) : ℝ) :=
    (le_max_left _ _).trans (hlargeX.trans hhalfExp)
  have hN₀a : N₀ ≤ a - 1 := by exact_mod_cast hN₀R
  have hUR : U ≤ ((a - 1 : ℕ) : ℝ) :=
    (le_max_right _ _).trans (hlargeX.trans hhalfExp)
  have herru := hU (((a - 1 : ℕ) : ℝ)) hUR
  have herrδ :
      2 * B * Real.exp (-c * Real.sqrt (Real.log ((a - 1 : ℕ) : ℝ))) ≤ δ :=
    herru.trans (hscaleX hhalfLog)
  have hu3 : 3 ≤ a - 1 := hN₀.trans hN₀a
  have huv : a - 1 ≤ b - 1 := Nat.sub_le_sub_right hab 1
  have hlog1 : 1 ≤ Real.log ((a - 1 : ℕ) : ℝ) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have hcast : (3 : ℝ) ≤ ((a - 1 : ℕ) : ℝ) := by exact_mod_cast hu3
    linarith [Real.exp_one_lt_d9]
  have hinc := logLog_sub_le_delta_div_log hu3 huv hδ0 hband
  have hdiv : δ / Real.log ((a - 1 : ℕ) : ℝ) ≤ δ := by
    rw [div_le_iff₀ (by linarith : 0 < Real.log ((a - 1 : ℕ) : ℝ))]
    nlinarith
  have hm := hmass ha hab hN₀a
  linarith

/-- Every lower-prime fibre in the source `c₃,n` coefficient has mass at most `2δ_A`. -/
theorem eventually_lowerC3FibreMass_paperWidth (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (S : Finset ℕ) (lower : ℕ → ℕ),
      (∀ q ∈ S,
        mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((lower q - 1 : ℕ) : ℝ)) →
      (∀ q ∈ S, lower q ≤ q) →
      (∀ q ∈ S, ((q - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((lower q - 1 : ℕ) : ℝ)) →
      ∀ q ∈ S, ∑ p ∈ primesIco (lower q) q, 1 / (p : ℝ) ≤
        2 * mtPaperWidth A X := by
  filter_upwards [eventually_sum_inv_primesIco_relaxedPaperCutoff A] with X hmassX
  intro S lower hlowerCut hlower hband q hq
  exact hmassX (a := lower q) (b := q) (hlowerCut q hq) (hlower q hq) (hband q hq)

end

end RHTower.Sieve
