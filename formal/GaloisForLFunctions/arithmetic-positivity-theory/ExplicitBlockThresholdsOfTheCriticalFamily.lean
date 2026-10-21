import GaloisForLFunctions.«arithmetic-positivity-theory».CriticalCompleteFormHighScalePositivity
import GaloisForLFunctions.«arithmetic-positivity-theory».CriticalCompleteFormPolynomialWindows
import GaloisForLFunctions.«arithmetic-positivity-theory».CollaredCriticalCompleteFormPositivity
import GaloisForLFunctions.«arithmetic-positivity-theory».CompactCriticalSourceWeilPositivity
import GaloisForLFunctions.«arithmetic-positivity-theory».LacunaryCriticalBlockPositivity
import GaloisForLFunctions.«arithmetic-positivity-theory».CriticalCompleteFormGrowingPatterns

/-!
# Explicit block thresholds of the critical factorial family

Each positivity law of the critical family has the shape `E ≥ (s (log M − c) − C) ∑ b_n²` on a
block at scale `M`, with an archimedean slope `s > 0`, an offset `c` and an `ℓ²` channel constant
`C`. The scale beyond which the bracket is positive is therefore the explicit integer

`logLinearThreshold s c C = max 2 (⌊exp (c + C/s)⌋ + 1)`        (`sub_pos_of_logLinearThreshold_le`).

This names the block threshold of every positivity law in closed form in the named constants:

* complete critical form on dyadic blocks, and translated patterns of any size
  (`criticalBlockThreshold`);
* endpoint-collared sources (`criticalCollaredBlockThreshold`);
* doubly collared compact truncations, uniformly in the truncation, and the full Weil functional
  of `ζ` on them (`criticalTruncatedBlockThreshold`);
* lacunary unions of blocks (`lacunaryBlockThreshold`);
* polynomial windows `[M, LM]`, `L ≤ M^δ`, with the explicit exponent
  `δ = s/(4(W + 1))` and threshold `max 2 (⌊exp (2K/s)⌋ + 1)`, `K = s c + K₀ + 6W`
  (`criticalWindowExponent`, `criticalWindowThreshold`).
-/

open MeasureTheory Set Filter
open _root_.Zeta23

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositivityTheory

/-- The least scale `M ≥ 2` with `log M > c + C/s`, in closed form. -/
def logLinearThreshold (s c C : ℝ) : ℕ := max 2 (⌊Real.exp (c + C / s)⌋₊ + 1)

/-- Beyond `logLinearThreshold s c C` the bracket `s (log M − c) − C` is positive. -/
theorem sub_pos_of_logLinearThreshold_le {s c C : ℝ} (hs : 0 < s) {M : ℕ}
    (hM : logLinearThreshold s c C ≤ M) : 2 ≤ M ∧ 0 < s * (Real.log M - c) - C := by
  have h2 : 2 ≤ M := le_trans (le_max_left _ _) hM
  have hfl : ⌊Real.exp (c + C / s)⌋₊ + 1 ≤ M := le_trans (le_max_right _ _) hM
  have hexp : Real.exp (c + C / s) < M := by
    have := Nat.lt_floor_add_one (Real.exp (c + C / s))
    exact this.trans_le (by exact_mod_cast hfl)
  have hlog : c + C / s < Real.log M := by
    rw [← Real.exp_lt_exp, Real.exp_log (by exact_mod_cast (show 0 < M by omega))]
    exact hexp
  refine ⟨h2, ?_⟩
  have h1 : C / s < Real.log M - c := by linarith
  have := (div_lt_iff₀ hs).mp h1
  linarith

private theorem sum_sq_pos {S : Finset ℕ} {b : ℕ → ℝ} (hb : ∃ n ∈ S, b n ≠ 0) :
    0 < ∑ n ∈ S, b n ^ 2 := by
  obtain ⟨j, hj, hbj⟩ := hb
  exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun i _ => sq_nonneg (b i)) hj)

/-! ## The complete critical form -/

/-- The explicit dyadic block threshold of the complete critical form. -/
def criticalBlockThreshold : ℕ :=
  logLinearThreshold criticalArchLogSlope criticalArchLogOffset criticalCompleteChannelConstant

/-- **Explicit threshold.** For `M ≥ criticalBlockThreshold` the complete critical form is positive
definite on every dyadic block at scale `M`. -/
theorem criticalCompleteEnergy_pos_of_threshold_le {M : ℕ} (hM : criticalBlockThreshold ≤ M)
    (S : Finset ℕ) (hS : DyadicScaleBlock S M) (b : ℕ → ℝ) (hb : ∃ n ∈ S, b n ≠ 0) :
    0 < criticalCompleteEnergy S b := by
  obtain ⟨hM2, hgap⟩ := sub_pos_of_logLinearThreshold_le criticalArchLogSlope_pos hM
  exact lt_of_lt_of_le (EReal.coe_pos.mpr (mul_pos hgap (sum_sq_pos hb)))
    (criticalCompleteEnergy_ge_of_dyadic S b hM2 hS)

/-- Translated patterns of any size at scale `n ≥ criticalBlockThreshold` have positive complete
critical energy. -/
theorem criticalTranslatedCompleteEnergy_pos_of_threshold_le {n : ℕ}
    (hn : criticalBlockThreshold ≤ n) (S : Finset ℕ) (hS : ∀ j ∈ S, j ≤ n) (b : ℕ → ℝ)
    (hb : ∃ j ∈ S, b j ≠ 0) : 0 < criticalTranslatedCompleteEnergy S b n := by
  rw [criticalTranslatedCompleteEnergy_eq]
  refine criticalCompleteEnergy_pos_of_threshold_le (M := n + 1) (by omega) _ (fun q hq => ?_) _ ?_
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    have := hS j hj
    constructor <;> omega
  · obtain ⟨j, hj, hbj⟩ := hb
    exact ⟨n + j, Finset.mem_image.mpr ⟨j, hj, rfl⟩, by simpa using hbj⟩

/-! ## Collared, truncated and lacunary sources -/

/-- The explicit dyadic block threshold of endpoint-collared sources. -/
def criticalCollaredBlockThreshold : ℕ :=
  logLinearThreshold criticalCollarArchLogSlope criticalCollarArchLogOffset
    criticalCollaredChannelConstant

theorem criticalCollaredCompleteEnergy_pos_of_threshold_le {M : ℕ}
    (hM : criticalCollaredBlockThreshold ≤ M) (S : Finset ℕ) (hS : DyadicScaleBlock S M)
    (b : ℕ → ℝ) (hb : ∃ n ∈ S, b n ≠ 0) : 0 < criticalCollaredCompleteEnergy S b := by
  obtain ⟨hM2, hgap⟩ := sub_pos_of_logLinearThreshold_le criticalCollarArchLogSlope_pos hM
  exact lt_of_lt_of_le (EReal.coe_pos.mpr (mul_pos hgap (sum_sq_pos hb)))
    (criticalCollaredCompleteEnergy_ge S b hM2 hS)

/-- The explicit dyadic block threshold of doubly collared compact truncations. -/
def criticalTruncatedBlockThreshold : ℕ :=
  logLinearThreshold criticalTruncatedArchLogSlope criticalTruncatedArchLogOffset
    criticalTruncatedChannelConstant

theorem criticalTruncatedCompleteEnergy_pos_of_threshold_le {M : ℕ}
    (hM : criticalTruncatedBlockThreshold ≤ M) {V : ℝ} (hV : criticalTruncationThreshold ≤ V)
    (S : Finset ℕ) (hS : DyadicScaleBlock S M) (b : ℕ → ℝ) (hb : ∃ n ∈ S, b n ≠ 0) :
    0 < criticalTruncatedCompleteEnergy V S b := by
  obtain ⟨hM2, hgap⟩ := sub_pos_of_logLinearThreshold_le criticalTruncatedArchLogSlope_pos hM
  exact lt_of_lt_of_le (EReal.coe_pos.mpr (mul_pos hgap (sum_sq_pos hb)))
    (criticalTruncatedCompleteEnergy_ge S b hM2 hS hV)

/-- **Explicit threshold for the Weil functional of `ζ`.** For `M ≥ criticalTruncatedBlockThreshold`,
every truncation `V ≥ V₀` and every nonzero pattern on a dyadic block at `M`,
`Re W_Λ(g^V ⋆ g̃^V) > 0`. -/
theorem compactFullWeilEnergy_criticalTruncatedTest_pos_of_threshold_le {M : ℕ}
    (hM : criticalTruncatedBlockThreshold ≤ M) {V : ℝ} (hV : 0 < V)
    (hVt : criticalTruncationThreshold ≤ V) (S : Finset ℕ) (hS : DyadicScaleBlock S M)
    (b : ℕ → ℝ) (hb : ∃ n ∈ S, b n ≠ 0) :
    0 < compactFullWeilEnergy (criticalTruncatedTest hV S b) := by
  have h := criticalTruncatedCompleteEnergy_pos_of_threshold_le hM hVt S hS b hb
  rw [← compactFullWeilEnergy_criticalTruncatedTest hV] at h
  exact EReal.coe_pos.mp h

/-- The explicit base-scale threshold of lacunary block unions. -/
def lacunaryBlockThreshold : ℕ :=
  logLinearThreshold criticalTruncatedArchLogSlope criticalTruncatedArchLogOffset
    lacunaryChannelConstant

theorem criticalTruncatedCompleteEnergy_pos_of_lacunary_threshold_le {J : ℕ} {M : ℕ → ℕ}
    {S : ℕ → Finset ℕ} (h : IsLacunaryBlockFamily J M S) (hM : lacunaryBlockThreshold ≤ M 0)
    {V : ℝ} (hV : criticalTruncationThreshold ≤ V) (b : ℕ → ℝ)
    (hb : ∃ n ∈ (Finset.range J).biUnion S, b n ≠ 0) :
    0 < criticalTruncatedCompleteEnergy V ((Finset.range J).biUnion S) b := by
  obtain ⟨-, hgap⟩ := sub_pos_of_logLinearThreshold_le criticalTruncatedArchLogSlope_pos hM
  exact lt_of_lt_of_le (EReal.coe_pos.mpr (mul_pos hgap (sum_sq_pos hb)))
    (criticalTruncatedCompleteEnergy_ge_of_lacunary h b hV)

/-! ## Polynomial windows -/

/-- The explicit window exponent `δ = s/(4(W + 1))`. -/
def criticalWindowExponent : ℝ := criticalArchLogSlope / (4 * (criticalWindowPrimeSlope + 1))

/-- The explicit window threshold `max 2 (⌊exp (2K/s)⌋ + 1)`, `K = s c + K₀ + 6W`. -/
def criticalWindowThreshold : ℕ :=
  max 2 (⌊Real.exp (2 * (criticalArchLogSlope * criticalArchLogOffset +
    criticalWindowBaseConstant + 6 * criticalWindowPrimeSlope) / criticalArchLogSlope)⌋₊ + 1)

theorem criticalWindowExponent_pos : 0 < criticalWindowExponent := by
  have hW : 0 ≤ criticalWindowPrimeSlope := by
    unfold criticalWindowPrimeSlope
    have := criticalWindowConstant_nonneg
    positivity
  have := criticalArchLogSlope_pos
  unfold criticalWindowExponent
  positivity

/-- **Explicit polynomial windows.** For `M ≥ criticalWindowThreshold` and every window `[M, LM]`
with `L ≤ M^δ`, `δ = criticalWindowExponent`, the complete critical form is positive definite. -/
theorem criticalCompleteEnergy_pos_of_window_threshold_le {M : ℕ}
    (hM : criticalWindowThreshold ≤ M) {L : ℕ} (hL : 1 ≤ L)
    (hLM : (L : ℝ) ≤ (M : ℝ) ^ criticalWindowExponent) (S : Finset ℕ) (hS : ScaleWindow S M L)
    (b : ℕ → ℝ) (hb : ∃ n ∈ S, b n ≠ 0) : 0 < criticalCompleteEnergy S b := by
  set s := criticalArchLogSlope
  have hs : 0 < s := criticalArchLogSlope_pos
  set W := criticalWindowPrimeSlope
  have hW : 0 ≤ W := by
    unfold W criticalWindowPrimeSlope
    have := criticalWindowConstant_nonneg
    positivity
  set K := s * criticalArchLogOffset + criticalWindowBaseConstant + 6 * W
  have hM2 : 2 ≤ M := le_trans (le_max_left _ _) hM
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlogM : 2 * K / s < Real.log M := by
    have hfl : ⌊Real.exp (2 * K / s)⌋₊ + 1 ≤ M := le_trans (le_max_right _ _) hM
    have hexp : Real.exp (2 * K / s) < M :=
      (Nat.lt_floor_add_one _).trans_le (by exact_mod_cast hfl)
    rw [← Real.exp_lt_exp, Real.exp_log hMpos]
    exact hexp
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hlogL : Real.log L ≤ criticalWindowExponent * Real.log M := by
    have := Real.log_le_log hL0 hLM
    rwa [Real.log_rpow hMpos] at this
  have hgap : 0 < s * (Real.log M - criticalArchLogOffset) - criticalWindowBaseConstant -
      2 * W * (3 + Real.log L) := by
    have h1 : 2 * W * Real.log L ≤ s / 2 * Real.log M := by
      calc 2 * W * Real.log L ≤ 2 * W * (criticalWindowExponent * Real.log M) := by gcongr
        _ = s / 2 * Real.log M * (W / (W + 1)) := by
            rw [show criticalWindowExponent = s / (4 * (W + 1)) from rfl]
            field_simp; ring
        _ ≤ s / 2 * Real.log M * 1 := by
            have hlog0 : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast (show 1 ≤ M by omega))
            gcongr
            rw [div_le_one (by linarith)]; linarith
        _ = s / 2 * Real.log M := by ring
    have h2 : K < s / 2 * Real.log M := by
      have := (div_lt_iff₀ hs).mp hlogM
      linarith
    unfold K at h2
    nlinarith
  exact lt_of_lt_of_le (EReal.coe_pos.mpr (mul_pos hgap (sum_sq_pos hb)))
    (criticalCompleteEnergy_ge_of_window S b hM2 hL hS)

end GaloisForLFunctions.ArithmeticPositivityTheory
