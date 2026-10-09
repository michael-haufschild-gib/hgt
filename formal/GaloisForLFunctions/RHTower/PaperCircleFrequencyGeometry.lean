import GaloisForLFunctions.HTGeometry.PaperFourierThermalMetric
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Thermal.Packing
import GaloisForLFunctions.RHTower.PaperCircleSubgridProbability

/-! # Native Gibbs frequency geometry and coherence counts

The actual circle energy produces a genuine metric on finite frequencies.
Its unit ball consists exactly of frequencies with correlation at least one half.
Free energy bounds this count above; spatial localization bounds it below.
-/

open scoped BigOperators NNReal Topology
open Filter
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

@[implicit_reducible]
def paperCircleFrequencyMetric (a : ι → CCMCircleBoundedSymbol) (M k : ℕ) (t : ℝ≥0) :
    MetricSpace (Grid M) := Thermal.deltaMetric (paperCircleLocalizedForm a M k t)

def paperCircleFrequencyDistance (a : ι → CCMCircleBoundedSymbol) (M k : ℕ) (t : ℝ≥0)
    (x z : Grid M) : ℝ := @dist (Grid M) (paperCircleFrequencyMetric a M k t).toDist x z

theorem paperCircleFrequencyDistance_sq (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (x z : Grid M) :
    paperCircleFrequencyDistance a M k t x z ^ 2 =
      (paperCircleLocalizedLaw a M k t).Ex (fun y => ‖chi x y - chi z y‖^2) :=
  Thermal.delta_sub_sq _ _ _

theorem paperCircleFrequencyDistance_eq_zero_iff (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (x z : Grid M) :
    paperCircleFrequencyDistance a M k t x z = 0 ↔ x = z := by
  change Thermal.delta _ (x-z) = 0 ↔ _
  rw [Thermal.delta_eq_zero_iff, sub_eq_zero]

theorem paperCircleFrequencyDistance_nonneg (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (x z : Grid M) :
    0 ≤ paperCircleFrequencyDistance a M k t x z := Real.sqrt_nonneg _

/-- Strictly positive heat coefficients keep every squared distance below two. -/
theorem paperCircleFrequencyDistance_sq_lt_two (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (x z : Grid M) :
    paperCircleFrequencyDistance a M k t x z ^ 2 < 2 := by
  change Thermal.delta _ (x-z)^2 < _
  rw [Thermal.delta_sq]
  have H : 0 < Thermal.cred (paperCircleLocalizedForm a M k t) (x-z) :=
    div_pos (paperCircleLocalizedHeat_pos a M k t _) (Thermal.q_origin_pos _)
  linarith

/-- Increasing the native energy coupling contracts every frequency distance. -/
theorem antitone_paperCircleFrequencyDistance (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (x z : Grid M) : Antitone (fun t => paperCircleFrequencyDistance a M k t x z) := by
  intro s t h
  apply Thermal.delta_mono (paperCircleLocalizedForm_nonneg a M k s)
  intro u
  change Thermal.S M (paperCircleLocalizationWidth M k) u + (s : ℝ) * paperCircleGridEnergy a M u ≤
    Thermal.S M (paperCircleLocalizationWidth M k) u + (t : ℝ) * paperCircleGridEnergy a M u
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (show (s : ℝ) ≤ (t : ℝ) from h)
    (paperCircleGridEnergy_nonneg a M u))

/-- Frequencies whose actual Gibbs correlation with zero is at least one half. -/
def paperCircleCoherentFrequencies (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) : Finset (Grid M) := Thermal.ball (paperCircleLocalizedForm a M k t) 1

theorem mem_paperCircleCoherentFrequencies_iff (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (x : Grid M) :
    x ∈ paperCircleCoherentFrequencies a M k t ↔
      (1/2 : ℝ) ≤ Thermal.cred (paperCircleLocalizedForm a M k t) x := by
  rw [paperCircleCoherentFrequencies, Thermal.mem_ball]
  have H := Thermal.delta_sq (paperCircleLocalizedForm a M k t) x
  have hp : 0 ≤ Thermal.delta (paperCircleLocalizedForm a M k t) x := Real.sqrt_nonneg _
  constructor <;> intro h <;> nlinarith

theorem monotone_paperCircleCoherentFrequencies (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) : Monotone (paperCircleCoherentFrequencies a M k) := by
  intro s t h x hx
  change x ∈ Thermal.ball _ 1 at hx ⊢
  rw [Thermal.mem_ball] at hx ⊢
  have H := antitone_paperCircleFrequencyDistance a M k x 0 h
  change Thermal.delta _ (x-0) ≤ Thermal.delta _ (x-0) at H
  simp only [sub_zero] at H
  exact H.trans hx

/-- A sharp counting bound: every coherent frequency carries half the origin heat mass. -/
theorem paperCircleCoherentFrequencies_mass_bound (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) :
    (paperCircleCoherentFrequencies a M k t).card * paperCircleLocalizedHeat a M k t 0 ≤ 2 := by
  classical
  let s := paperCircleCoherentFrequencies a M k t
  have H : (s.card : ℝ) * paperCircleLocalizedHeat a M k t 0 / 2 ≤ 1 := calc
    _ = ∑ _x ∈ s, paperCircleLocalizedHeat a M k t 0 / 2 := by simp; ring
    _ ≤ ∑ x ∈ s, paperCircleLocalizedHeat a M k t x := Finset.sum_le_sum fun x hx =>
      Thermal.half_q_ball _ _ ((Thermal.mem_ball _ _ _).mp hx)
    _ ≤ ∑ x, paperCircleLocalizedHeat a M k t x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun x _ _ => Law.nonneg _ x)
    _ = 1 := Law.total _
  change (s.card : ℝ) * paperCircleLocalizedHeat a M k t 0 ≤ 2
  linarith

/-- Free energy bounds the number of frequencies that the Gibbs observer sees as coherent. -/
theorem paperCircleCoherentFrequencies_card_le (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) :
    ((paperCircleCoherentFrequencies a M k t).card : ℝ) ≤
      2 * Real.exp (Thermal.F (paperCircleLocalizedForm a M k t)) := by
  have H := paperCircleCoherentFrequencies_mass_bound a M k t
  have hp := paperCircleLocalizedHeat_pos a M k t 0
  have he : Real.exp (Thermal.F (paperCircleLocalizedForm a M k t)) =
      (paperCircleLocalizedHeat a M k t 0)⁻¹ := by
    rw [Thermal.F, Real.exp_neg, Real.exp_log (Thermal.q_origin_pos _)]
    rfl
  rw [he, ← div_eq_mul_inv]
  exact (le_div_iff₀ hp).mpr H

/-- Localization forces a growing interval of coherent frequencies. -/
theorem paperCircleCoherentFrequencies_card_ge (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) :
    paperCircleLocalizationWidth M k / 20 ≤ ((paperCircleCoherentFrequencies a M k t).card : ℝ) := by
  have hR := paperCircleLocalizationWidth_pos M k
  have hs : arc M (paperCircleLocalizationWidth M k / 20) ⊆
      paperCircleCoherentFrequencies a M k t := by
    intro x hx
    rw [mem_paperCircleCoherentFrequencies_iff]
    exact Thermal.cred_short _ (paperCircleLocalizationWidth_ge_one M k)
      (paperCircleLocalizationWidth_le_grid M k) _ (paperCircleLocalizedForm_spatial_le a M k t)
      x ((mem_arc _ _).mp hx)
  exact (arc_card_lo M _ (by positivity)
    ((div_le_self hR.le (by norm_num : (1 : ℝ) ≤ 20)).trans
      (paperCircleLocalizationWidth_le_grid M k))).trans (Nat.cast_le.mpr (Finset.card_le_card hs))

/-- Fixed integer modes become close at an explicit rate independent of the native energy. -/
theorem paperCircleFrequencyDistance_int_le (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (x z : ℤ) :
    paperCircleFrequencyDistance a M k t (x : Grid M) (z : Grid M) ≤
      |((x-z : ℤ) : ℝ)| * (20 / paperCircleLocalizationWidth M k) := by
  change Thermal.delta _ ((x : Grid M)-(z : Grid M)) ≤ _
  rw [← Int.cast_sub]
  exact (paperCircleLocalizedLaw_phase_rms a M k t _).trans
    (mul_le_mul_of_nonneg_right (rad_le_int (x-z))
      (div_nonneg (by norm_num) (paperCircleLocalizationWidth_pos M k).le))

/-- Every fixed pair of integer modes merges in the localization limit, despite finite separation. -/
theorem paperCircleFrequencyDistance_int_tendsto_zero {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (a : (n : ℕ) → ι n → CCMCircleBoundedSymbol) (t : ℕ → ℝ≥0) (x z : ℤ) :
    Tendsto (fun n => paperCircleFrequencyDistance (a n) n n (t n) (x : Grid n) (z : Grid n))
      atTop (𝓝 0) := by
  have hu : Tendsto (fun n : ℕ => |((x-z : ℤ) : ℝ)| * (20 / (2 : ℝ)^n)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_assoc, mul_zero, Function.comp_apply] using
      (tendsto_const_nhds (x := |((x-z : ℤ) : ℝ)| * 20)).mul
        (tendsto_inv_atTop_zero.comp
          (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)))
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hu.eventually_lt_const hε] with n hn
  have H := paperCircleFrequencyDistance_int_le (a n) n n (t n) x z
  simp only [paperCircleLocalizationWidth, min_self] at H
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (paperCircleFrequencyDistance_nonneg _ _ _ _ _ _)]
  exact H.trans_lt hn

/-- Arbitrarily varying native energy still leaves unboundedly many coherent frequencies. -/
theorem paperCircleCoherentFrequencies_card_tendsto_atTop {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (a : (n : ℕ) → ι n → CCMCircleBoundedSymbol) (t : ℕ → ℝ≥0) :
    Tendsto (fun n => ((paperCircleCoherentFrequencies (a n) n n (t n)).card : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (f := fun n : ℕ => (2 : ℝ)^n / 20)
    (fun n => by simpa only [paperCircleLocalizationWidth, min_self] using
      paperCircleCoherentFrequencies_card_ge (a n) n n (t n))
  exact (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)).atTop_div_const
    (by norm_num : (0 : ℝ) < 20)

end
end RHTower
