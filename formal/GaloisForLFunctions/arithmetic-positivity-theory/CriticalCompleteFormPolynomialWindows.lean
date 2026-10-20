import GaloisForLFunctions.«arithmetic-positivity-theory».CriticalPrimeChannelScaleWindows

/-!
# Positive definiteness of the complete critical form on polynomial scale windows

On a scale window `[M, LM]` the four channels of the complete critical form satisfy:

* **archimedean:** `Lévy(g_b) ≥ s (log M - c₀) ∑ b_n²`, since all scales are at least `M`;
* **Gamma:** `ac(0) ≤ U ∑ b_n²`, for every support;
* **polar:** `|R E| ≤ 576 ∑ b_n²`, since all scales are at least `M`;
* **prime:** `|P| ≤ C_W (3 + log L) ∑ b_n²`, the logarithmic window law.

Hence `E_crit ≥ (s (log M - c₀) - K₀ - 2 C_W (3 + log L)) ∑ b_n²`. The archimedean gain is
`log M` while the prime cost is only `log L`, so the complete critical form is positive definite on
every window `[M, M^{1+δ}]` with `δ = s/(4(C_W + 1))` once `M` is large. A positive pattern may
spread over polynomially many dyadic blocks.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal
open _root_.Zeta23

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-- Gamma-plus-polar constant `|Ω(0)| U + 1152` of the complete critical form. -/
def criticalWindowBaseConstant : ℝ := |EF.gammaBracket 0| * criticalCollarMassUpper + 1152

/-- **Window channel bound.** On a scale window `[M, LM]` (`M ≥ 2`) the Gamma, polar and prime
channels of the complete critical form cost at most `(K₀ + 2 C_W (3 + log L)) ∑ b_n²`. -/
theorem neg_le_criticalArithmeticChannels_of_window (S : Finset ℕ) (b : ℕ → ℝ) {M L : ℕ} (hM : 2 ≤ M)
    (hL : 1 ≤ L) (hS : ScaleWindow S M L) :
    -((criticalWindowBaseConstant + 2 * criticalWindowPrimeSlope * (3 + Real.log L)) *
      ∑ n ∈ S, b n ^ 2) ≤ criticalArithmeticChannels S b := by
  set E := ∑ n ∈ S, b n ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set T := ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)
  have hT : 0 ≤ T := Finset.sum_nonneg fun n _ => by positivity
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hac0 : 0 ≤ criticalAutocorrelation S b 0 := by
    unfold criticalAutocorrelation
    simp only [sub_zero]
    exact integral_nonneg fun y => mul_self_nonneg _
  have hac := criticalAutocorrelation_zero_le_sq S b
  have hΩ : -(|EF.gammaBracket 0| * (criticalCollarMassUpper * E)) ≤
      EF.gammaBracket 0 * criticalAutocorrelation S b 0 := by
    have h1 := neg_abs_le (EF.gammaBracket 0 * criticalAutocorrelation S b 0)
    rw [abs_mul, abs_of_nonneg hac0] at h1
    nlinarith [abs_nonneg (EF.gammaBracket 0)]
  have hT2 : T ^ 2 ≤ E := (sq_sum_abs_div_succ_le S b hM fun n hn => (hS n hn).1).trans (by
    have : 2 / (M : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hM2
    nlinarith)
  have hpol : |criticalFactorialPolarReadout S b * criticalFactorialPolarEndpoint S b| ≤ 576 * E := by
    rw [abs_mul]
    calc _ ≤ (24 * T) * (24 * T) := mul_le_mul (abs_criticalFactorialPolarReadout_le S b)
          (criticalFactorialPolarEndpoint_bound S b) (abs_nonneg _) (by positivity)
      _ = 576 * T ^ 2 := by ring
      _ ≤ 576 * E := by linarith
  have hpr := abs_criticalPrimeEnergy_le_of_window (by omega) hL hS b
  have h2 := neg_abs_le (criticalFactorialPolarReadout S b * criticalFactorialPolarEndpoint S b)
  have h3 := le_abs_self (criticalPrimeEnergy S b)
  unfold criticalArithmeticChannels criticalWindowBaseConstant
  nlinarith

/-- **Complete critical form on scale windows.** For every family on a window `[M, LM]` (`M ≥ 2`)
and every real coefficient vector,
`E_crit(g_b) ≥ (s (log M - c₀) - K₀ - 2 C_W (3 + log L)) ∑ b_n²`. -/
theorem criticalCompleteEnergy_ge_of_window (S : Finset ℕ) (b : ℕ → ℝ) {M L : ℕ} (hM : 2 ≤ M)
    (hL : 1 ≤ L) (hS : ScaleWindow S M L) :
    (((criticalArchLogSlope * (Real.log M - criticalArchLogOffset) - criticalWindowBaseConstant -
        2 * criticalWindowPrimeSlope * (3 + Real.log L)) * ∑ n ∈ S, b n ^ 2 : ℝ) : EReal) ≤
      criticalCompleteEnergy S b := by
  set E := ∑ n ∈ S, b n ^ 2
  set X := criticalArchLogSlope * (Real.log M - criticalArchLogOffset) * E
  have hlev : (X : EReal) ≤ (criticalLevyEnergy S b : EReal) := by
    have h1 := ofReal_le_criticalLevyEnergy S b hM fun n hn => (hS n hn).1
    have h2 := EReal.coe_ennreal_le_coe_ennreal_iff.mpr h1
    rw [EReal.coe_ennreal_ofReal] at h2
    exact le_trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _)) h2
  have hch := neg_le_criticalArithmeticChannels_of_window S b hM hL hS
  unfold criticalCompleteEnergy
  rw [show (criticalArchLogSlope * (Real.log M - criticalArchLogOffset) - criticalWindowBaseConstant -
      2 * criticalWindowPrimeSlope * (3 + Real.log L)) * E = X +
      -((criticalWindowBaseConstant + 2 * criticalWindowPrimeSlope * (3 + Real.log L)) * E) by ring,
    EReal.coe_add]
  exact add_le_add hlev (EReal.coe_le_coe_iff.mpr hch)

/-- **Positive definiteness on polynomial scale windows.** There are `δ > 0` and `M₀` such that
for every `M ≥ M₀` and every window `[M, LM]` with `L ≤ M^δ`, every nonzero real family on the
window has strictly positive complete critical energy. Patterns may spread over polynomially many
dyadic blocks, with no restriction on the number or positions of the atoms. -/
theorem exists_criticalCompleteEnergy_pos_of_window :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L : ℕ, 1 ≤ L → (L : ℝ) ≤ (M : ℝ) ^ δ →
      ∀ S : Finset ℕ, ScaleWindow S M L → ∀ b : ℕ → ℝ, (∃ n ∈ S, b n ≠ 0) →
        0 < criticalCompleteEnergy S b := by
  set s := criticalArchLogSlope
  have hs : 0 < s := criticalArchLogSlope_pos
  set W := criticalWindowPrimeSlope
  have hW : 0 ≤ W := by
    unfold W criticalWindowPrimeSlope
    have := criticalWindowConstant_nonneg
    positivity
  set δ := s / (4 * (W + 1))
  have hδ : 0 < δ := by positivity
  set K := s * criticalArchLogOffset + criticalWindowBaseConstant + 6 * W
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp ((hlog.eventually_gt_atTop (2 * K / s)).and
    (eventually_ge_atTop 2))
  refine ⟨δ, hδ, M₀, fun M hM L hL hLM S hS b hb => ?_⟩
  obtain ⟨hlogM, hM2⟩ := hM₀ M hM
  obtain ⟨j, hj, hbj⟩ := hb
  have hE : 0 < ∑ n ∈ S, b n ^ 2 :=
    lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun i _ => sq_nonneg (b i)) hj)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hlogL : Real.log L ≤ δ * Real.log M := by
    have := Real.log_le_log hL0 hLM
    rwa [Real.log_rpow hMpos] at this
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast (show 1 ≤ M by omega))
  have hgap : 0 < s * (Real.log M - criticalArchLogOffset) - criticalWindowBaseConstant -
      2 * W * (3 + Real.log L) := by
    have h1 : 2 * W * Real.log L ≤ s / 2 * Real.log M := by
      calc 2 * W * Real.log L ≤ 2 * W * (δ * Real.log M) := by gcongr
        _ = s / 2 * Real.log M * (W / (W + 1)) := by unfold δ; field_simp; ring
        _ ≤ s / 2 * Real.log M * 1 := by
            gcongr
            rw [div_le_one (by linarith)]; linarith
        _ = s / 2 * Real.log M := by ring
    have h2 : K < s / 2 * Real.log M := by
      have := (div_lt_iff₀ hs).mp hlogM
      linarith
    unfold K at h2
    nlinarith
  exact lt_of_lt_of_le (EReal.coe_pos.mpr (mul_pos hgap hE)) (criticalCompleteEnergy_ge_of_window S b hM2 hL hS)

end GaloisForLFunctions.ArithmeticPositivityTheory
