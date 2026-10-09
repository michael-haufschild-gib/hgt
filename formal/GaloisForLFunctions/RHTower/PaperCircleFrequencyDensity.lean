import GaloisForLFunctions.RHTower.PaperCircleFrequencyGeometry

/-! # Coherent frequency counts at normalized native coupling

Scaling coupling by the grid-cell mass keeps the total native energy fixed.
The coherent frequency count then lies within explicit constant factors of the
localization width, uniformly in grid resolution. At a fixed localization scale,
its fraction of the full frequency grid tends to zero.
-/

open scoped BigOperators NNReal Topology
open Filter
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- Coupling per grid cell, so refinement does not increase total native energy. -/
def paperCircleNormalizedCoupling (M : ℕ) (lam : ℝ≥0) : ℝ≥0 :=
  lam * ⟨Period.side M, (Period.side_pos M).le⟩

theorem paperCircleNormalizedCoupling_energy (a : ι → CCMCircleBoundedSymbol)
    (M : ℕ) (lam : ℝ≥0) :
    (paperCircleNormalizedCoupling M lam : ℝ) * ∑ x, paperCircleGridEnergy a M x =
      (lam : ℝ) * paperCircleFamilyEnergy a := by
  change ((lam : ℝ) * Period.side M) * ∑ x, paperCircleGridEnergy a M x = _
  rw [mul_assoc, ← expU_paperCircleGridEnergy a M]
  rfl

/-- The normalized native interaction has a pointwise bound independent of resolution. -/
theorem paperCircleNormalizedCoupling_form_le (a : ι → CCMCircleBoundedSymbol)
    (M : ℕ) (lam : ℝ≥0) (y : Grid M) :
    Thermal.form ((paperCircleNormalizedCoupling M lam : ℝ) • paperCircleGridEnergy a M) y ≤
      2 * (lam : ℝ) * paperCircleFamilyEnergy a := by
  have H : Thermal.form (paperCircleGridEnergy a M) y ≤ (∑ x, paperCircleGridEnergy a M x) * 2 := by
    rw [Thermal.form, Finset.sum_mul]
    exact Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_left (Thermal.cost_bounds x y).2 (paperCircleGridEnergy_nonneg a M x)
  rw [Thermal.form_smul]
  calc
    _ ≤ (paperCircleNormalizedCoupling M lam : ℝ) * ((∑ x, paperCircleGridEnergy a M x) * 2) :=
      mul_le_mul_of_nonneg_left H (NNReal.coe_nonneg _)
    _ = 2 * ((paperCircleNormalizedCoupling M lam : ℝ) * ∑ x, paperCircleGridEnergy a M x) := by ring
    _ = _ := by rw [paperCircleNormalizedCoupling_energy]; ring

private theorem freeEnergy_increment_le {M : ℕ} (A D : Thermal.Form M) :
    Thermal.F (A+D) - Thermal.F A ≤ (Thermal.label A).Ex (Thermal.form D) := by
  have H := (Thermal.label A).Ex_exp (fun y => -Thermal.form D y)
  rw [Law.Ex_neg] at H
  change Real.exp (-((Thermal.label A).Ex (Thermal.form D))) ≤
    (Thermal.label A).Ex (Thermal.boltz D) at H
  rw [Thermal.boltz_mean, Real.exp_le_exp] at H
  linarith

/-- The energy correction to the spatial free energy is uniformly bounded. -/
theorem paperCircleNormalizedCoupling_freeEnergy_le (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (lam : ℝ≥0) :
    Thermal.F (paperCircleLocalizedForm a M k (paperCircleNormalizedCoupling M lam)) ≤
      Real.log (paperCircleLocalizationWidth M k) + 30 + 2 * (lam : ℝ) * paperCircleFamilyEnergy a := by
  have H := freeEnergy_increment_le
    (Thermal.S M (paperCircleLocalizationWidth M k))
    ((paperCircleNormalizedCoupling M lam : ℝ) • paperCircleGridEnergy a M)
  have H' := (Thermal.label (Thermal.S M (paperCircleLocalizationWidth M k))).Ex_mono
    (paperCircleNormalizedCoupling_form_le a M lam)
  rw [Law.Ex_const] at H'
  have HS := Thermal.F_S_upper M (paperCircleLocalizationWidth M k)
    (paperCircleLocalizationWidth_ge_one M k)
  change Thermal.F (Thermal.S M (paperCircleLocalizationWidth M k) +
    (paperCircleNormalizedCoupling M lam : ℝ) • paperCircleGridEnergy a M) ≤ _
  linarith

/-- At normalized coupling, coherent frequency count is at most a constant times the width. -/
theorem paperCircleNormalizedCoupling_coherent_card_le (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (lam : ℝ≥0) :
    ((paperCircleCoherentFrequencies a M k (paperCircleNormalizedCoupling M lam)).card : ℝ) ≤
      2 * paperCircleLocalizationWidth M k * Real.exp (30 + 2 * (lam : ℝ) * paperCircleFamilyEnergy a) := by
  apply (paperCircleCoherentFrequencies_card_le a M k (paperCircleNormalizedCoupling M lam)).trans
  calc
    _ ≤ 2 * Real.exp (Real.log (paperCircleLocalizationWidth M k) + 30 +
        2 * (lam : ℝ) * paperCircleFamilyEnergy a) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (paperCircleNormalizedCoupling_freeEnergy_le a M k lam))
        (by positivity)
    _ = _ := by
      rw [add_assoc, Real.exp_add, Real.exp_log (paperCircleLocalizationWidth_pos M k)]
      ring

/-- Two-sided scale law with constants independent of the dyadic resolution. -/
theorem paperCircleNormalizedCoupling_coherent_ratio_bounds (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (lam : ℝ≥0) :
    (1/20 : ℝ) ≤ ((paperCircleCoherentFrequencies a M k (paperCircleNormalizedCoupling M lam)).card : ℝ) /
        paperCircleLocalizationWidth M k ∧
      ((paperCircleCoherentFrequencies a M k (paperCircleNormalizedCoupling M lam)).card : ℝ) /
        paperCircleLocalizationWidth M k ≤ 2 * Real.exp (30 + 2 * (lam : ℝ) * paperCircleFamilyEnergy a) := by
  constructor
  · apply (le_div_iff₀ (paperCircleLocalizationWidth_pos M k)).mpr
    calc
      (1/20 : ℝ) * paperCircleLocalizationWidth M k = paperCircleLocalizationWidth M k / 20 := by ring
      _ ≤ _ := paperCircleCoherentFrequencies_card_ge a M k (paperCircleNormalizedCoupling M lam)
  · apply (div_le_iff₀ (paperCircleLocalizationWidth_pos M k)).mpr
    calc
      _ ≤ 2 * paperCircleLocalizationWidth M k * Real.exp (30 + 2 * (lam : ℝ) * paperCircleFamilyEnergy a) :=
        paperCircleNormalizedCoupling_coherent_card_le a M k lam
      _ = _ := by ring

/-- The proportion of all grid frequencies that remain coherent. -/
def paperCircleCoherentFraction (a : ι → CCMCircleBoundedSymbol) (M k : ℕ) (t : ℝ≥0) : ℝ :=
  Period.side M * (paperCircleCoherentFrequencies a M k t).card

theorem paperCircleCoherentFraction_eq_probability (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) :
    paperCircleCoherentFraction a M k t =
      (Law.uniform (Grid M)).prob (fun x => x ∈ paperCircleCoherentFrequencies a M k t) := by
  classical
  rw [Law.prob_eq]
  simp only [uniform_side]
  rw [← Finset.sum_filter]
  have hs : Finset.univ.filter (fun x => x ∈ paperCircleCoherentFrequencies a M k t) =
      paperCircleCoherentFrequencies a M k t := by ext x; simp
  rw [hs, Finset.sum_const, nsmul_eq_mul, paperCircleCoherentFraction, mul_comm]

/-- Refining the grid at fixed localization width makes the coherent fraction vanish. -/
theorem paperCircleNormalizedCoupling_coherent_fraction_tendsto_zero
    (a : ι → CCMCircleBoundedSymbol) (k : ℕ) (lam : ℝ≥0) :
    Tendsto (fun M => paperCircleCoherentFraction a M k (paperCircleNormalizedCoupling M lam))
      atTop (𝓝 0) := by
  let C := 2 * (2 : ℝ)^k * Real.exp (30 + 2 * (lam : ℝ) * paperCircleFamilyEnergy a)
  have H (M : ℕ) : paperCircleCoherentFraction a M k (paperCircleNormalizedCoupling M lam) ≤
      C / (2 : ℝ)^M := by
    have hR : paperCircleLocalizationWidth M k ≤ (2 : ℝ)^k :=
      pow_le_pow_right₀ (by norm_num) (min_le_left _ _)
    have hcard := paperCircleNormalizedCoupling_coherent_card_le a M k lam
    have hb : ((paperCircleCoherentFrequencies a M k (paperCircleNormalizedCoupling M lam)).card : ℝ) ≤ C :=
      hcard.trans (by dsimp [C]; gcongr)
    rw [paperCircleCoherentFraction, side_pow_two, div_eq_mul_inv, mul_comm C]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  have hu : Tendsto (fun M : ℕ => C / (2 : ℝ)^M) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_const_nhds (x := C)).mul (tendsto_inv_atTop_zero.comp
        (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)))
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hu.eventually_lt_const hε] with M hM
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (show 0 ≤ paperCircleCoherentFraction a M k
    (paperCircleNormalizedCoupling M lam) from mul_nonneg (Period.side_pos M).le (Nat.cast_nonneg _))]
  exact (H M).trans_lt hM

/-- Full-resolution localization always leaves at least one twentieth of the grid coherent. -/
theorem paperCircleCoherentFraction_full_ge (a : ι → CCMCircleBoundedSymbol)
    (M : ℕ) (t : ℝ≥0) : (1/20 : ℝ) ≤ paperCircleCoherentFraction a M M t := by
  have H := paperCircleCoherentFrequencies_card_ge a M M t
  simp only [paperCircleLocalizationWidth, min_self] at H
  rw [paperCircleCoherentFraction, side_pow_two, mul_comm, ← div_eq_mul_inv]
  apply (le_div_iff₀ (show (0 : ℝ) < 2^M by positivity)).mpr
  calc
    (1/20 : ℝ) * (2 : ℝ)^M = (2 : ℝ)^M / 20 := by ring
    _ ≤ _ := H

/-- The vanishing fraction at each fixed scale is not uniform up to the full-resolution scale. -/
theorem paperCircleCoherentFraction_full_not_tendsto_zero {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (a : (n : ℕ) → ι n → CCMCircleBoundedSymbol) (t : ℕ → ℝ≥0) :
    ¬ Tendsto (fun n => paperCircleCoherentFraction (a n) n n (t n)) atTop (𝓝 0) := by
  intro h
  have H := ge_of_tendsto h (Eventually.of_forall fun n => paperCircleCoherentFraction_full_ge (a n) n (t n))
  norm_num at H

end
end RHTower
