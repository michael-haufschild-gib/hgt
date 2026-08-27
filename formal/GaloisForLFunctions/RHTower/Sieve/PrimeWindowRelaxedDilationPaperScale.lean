import GaloisForLFunctions.RHTower.Sieve.PrimeWindowRelaxedPaperScale

/-!
# Fixed dilations of the relaxed Matomäki--Teräväinen prime window

The Mertens argument used for one paper-width block is uniform for every fixed dilation
`1 + C δ_A`.  This form is needed when finitely many coupled block coordinates widen one source
condition by a fixed multiple of the paper width.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- A prime interval of relative width `C δ_A`, beginning at the literal relaxed cutoff, has
reciprocal mass at most `(C+1)δ_A`. -/
theorem eventually_sum_inv_primesIco_relaxedPaperCutoff_fixedDilation
    (A : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ X : ℝ in atTop, ∀ ⦃a b : ℕ⦄,
      mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((a - 1 : ℕ) : ℝ) →
      a ≤ b →
      ((b - 1 : ℕ) : ℝ) ≤
        (1 + C * mtPaperWidth A X) * ((a - 1 : ℕ) : ℝ) →
      ∑ p ∈ primesIco a b, 1 / (p : ℝ) ≤
        (C + 1) * mtPaperWidth A X := by
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
  let θ : ℝ := C * δ
  have hlogX : 0 ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos 1) hX
    rw [Real.log_exp] at hmono
    linarith
  have hδ0 : 0 ≤ δ := by
    dsimp [δ, mtPaperWidth]
    exact Real.rpow_nonneg hlogX _
  have hθ0 : 0 ≤ θ := mul_nonneg hC hδ0
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
  have hinc := logLog_sub_le_delta_div_log hu3 huv hθ0 (by
    simpa only [θ, δ] using hband)
  have hdiv : θ / Real.log ((a - 1 : ℕ) : ℝ) ≤ θ := by
    rw [div_le_iff₀ (by linarith : 0 < Real.log ((a - 1 : ℕ) : ℝ))]
    nlinarith
  have hm := hmass ha hab hN₀a
  dsimp [θ, δ] at hdiv herrδ ⊢
  nlinarith

end

end RHTower.Sieve
