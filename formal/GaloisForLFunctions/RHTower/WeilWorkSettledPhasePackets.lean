import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!+# Exact phase cost of positive atomic packets

A packet splits unit mass between two ordinates at least one. Its cumulative count uses a
strict ordinate cutoff. The phase defect is supported exactly between the two ordinates;
its integral is the chord length of the fractional mass times the separation. Finite families
obey the corresponding transport bound, including overlapping packets and repeated ordinates.
-/

open Complex Set MeasureTheory

noncomputable section

namespace RHTower.WeilWorkSettledPhase

def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * I)

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]

@[simp] theorem phase_one : phase 1 = 1 := by
  simp [phase, Complex.exp_two_pi_mul_I]

theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [show (((2 * Real.pi * (x + y) : ℝ) : ℂ) * I) =
    ((2 * Real.pi * x : ℝ) : ℂ) * I + ((2 * Real.pi * y : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.exp_add _ _

@[simp] theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

def mass (q : ℝ) : ℝ := (1 + Real.cos q) / 2

theorem mass_nonneg (q : ℝ) : 0 ≤ mass q := by
  unfold mass
  linarith [Real.neg_one_le_cos q]

theorem mass_le_one (q : ℝ) : mass q ≤ 1 := by
  unfold mass
  linarith [Real.cos_le_one q]

def left (a : ℝ) : ℝ := 1 + |a|

def right (a d : ℝ) : ℝ := left a + |d|

theorem left_le_right (a d : ℝ) : left a ≤ right a d := by
  unfold right
  linarith [abs_nonneg d]

theorem packet_positive (a d q : ℝ) :
    0 ≤ mass q ∧ 0 ≤ 1 - mass q ∧ 1 ≤ left a ∧ 1 ≤ right a d := by
  refine ⟨mass_nonneg q, sub_nonneg.mpr (mass_le_one q), ?_, ?_⟩
  · exact le_add_of_nonneg_right (abs_nonneg a)
  · exact (le_add_of_nonneg_right (abs_nonneg a)).trans (left_le_right a d)

def packetCount (a d q y : ℝ) : ℝ :=
  (if left a < y then mass q else 0) + (if right a d < y then 1 - mass q else 0)

def packetCost (a d q : ℝ) : ℝ → ℝ :=
  (Ioc (left a) (right a d)).indicator (fun _ => ‖phase (mass q) - 1‖)

theorem packet_phase_cost (a d q y : ℝ) :
    ‖phase (packetCount a d q y) - 1‖ = packetCost a d q y := by
  by_cases hr : right a d < y
  · have hl : left a < y := (left_le_right a d).trans_lt hr
    simp [packetCount, packetCost, hr, hl, not_le.mpr hr]
  · by_cases hl : left a < y
    · simp [packetCount, packetCost, hr, hl, le_of_not_gt hr]
    · simp [packetCount, packetCost, hr, hl]

theorem measurable_packetCount (a d q : ℝ) : Measurable (packetCount a d q) := by
  unfold packetCount
  exact (Measurable.ite measurableSet_Ioi measurable_const measurable_const).add
    (Measurable.ite measurableSet_Ioi measurable_const measurable_const)

theorem integrable_packetCost (a d q : ℝ) : Integrable (packetCost a d q) := by
  unfold packetCost
  rw [integrable_indicator_iff measurableSet_Ioc]
  exact integrableOn_const (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)

theorem integral_packetCost (a d q : ℝ) :
    ∫ y, packetCost a d q y = ‖phase (mass q) - 1‖ * |d| := by
  rw [packetCost, integral_indicator_const _ measurableSet_Ioc,
    Real.volume_real_Ioc, right, add_sub_cancel_left, max_eq_left (abs_nonneg d), smul_eq_mul]
  exact mul_comm _ _

/-- The exact cost of an arbitrary positive two-atom unit packet. -/
theorem integral_packet_phase (a d q : ℝ) :
    ∫ y, ‖phase (packetCount a d q y) - 1‖ = ‖phase (mass q) - 1‖ * |d| := by
  simp_rw [packet_phase_cost]
  exact integral_packetCost a d q

theorem phase_add_cost (x y : ℝ) :
    ‖phase (x + y) - 1‖ ≤ ‖phase x - 1‖ + ‖phase y - 1‖ := by
  rw [phase_add]
  calc
    ‖phase x * phase y - 1‖ = ‖(phase x - 1) + phase x * (phase y - 1)‖ := by
      congr 1; ring
    _ ≤ ‖phase x - 1‖ + ‖phase x * (phase y - 1)‖ := norm_add_le _ _
    _ = _ := by rw [norm_mul, norm_phase, one_mul]

theorem phase_sum_cost {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    ‖phase (∑ i ∈ s, x i) - 1‖ ≤ ∑ i ∈ s, ‖phase (x i) - 1‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (phase_add_cost _ _).trans (add_le_add le_rfl ih)

/-- Overlaps require no independence or separation assumption. -/
theorem integral_finite_packets {ι : Type*} (s : Finset ι) (a d q : ι → ℝ) :
    ∫ y, ‖phase (∑ i ∈ s, packetCount (a i) (d i) (q i) y) - 1‖ ≤
      ∑ i ∈ s, ‖phase (mass (q i)) - 1‖ * |d i| := by
  classical
  let f : ℝ → ℝ := fun y => ‖phase (∑ i ∈ s, packetCount (a i) (d i) (q i) y) - 1‖
  let g : ℝ → ℝ := fun y => ∑ i ∈ s, packetCost (a i) (d i) (q i) y
  have hle : ∀ y, f y ≤ g y := by
    intro y
    simpa only [f, g, packet_phase_cost] using
      phase_sum_cost s (fun i => packetCount (a i) (d i) (q i) y)
  have hg : Integrable g := by
    exact integrable_finsetSum s (fun i _ => integrable_packetCost (a i) (d i) (q i))
  have hm : Measurable f := by
    have hsum : Measurable fun y => ∑ i ∈ s, packetCount (a i) (d i) (q i) y :=
      Finset.measurable_sum s (fun i _ => measurable_packetCount (a i) (d i) (q i))
    exact ((Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      (measurable_const.mul hsum)).mul_const I)).sub_const 1).norm
  have hf : Integrable f := hg.mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by simpa only [f, norm_norm] using hle y)
  calc
    ∫ y, f y ≤ ∫ y, g y := integral_mono hf hg hle
    _ = ∑ i ∈ s, ‖phase (mass (q i)) - 1‖ * |d i| := by
      rw [show g = fun y => ∑ i ∈ s, packetCost (a i) (d i) (q i) y from rfl,
        integral_finsetSum s (fun i _ => integrable_packetCost (a i) (d i) (q i))]
      simp_rw [integral_packetCost]

/-- Half masses attain the maximal chord cost at every separation. -/
theorem half_packet_exact_cost (a d : ℝ) :
    ∫ y, ‖phase (packetCount a d (Real.pi / 2) y) - 1‖ = 2 * |d| := by
  rw [integral_packet_phase]
  have hm : mass (Real.pi / 2) = 1 / 2 := by simp [mass]
  have hp : phase (1 / 2) = -1 := by
    unfold phase
    rw [show 2 * Real.pi * (1 / 2 : ℝ) = Real.pi by ring]
    exact Complex.exp_pi_mul_I
  rw [hm, hp]
  norm_num

/-- Counting discrepancy stays bounded independently of the packet width. -/
theorem half_packet_count_discrepancy (a d y : ℝ) :
    |packetCount a d (Real.pi / 2) y - (if right a d < y then 1 else 0)| ≤ 1 / 2 := by
  have hm : mass (Real.pi / 2) = 1 / 2 := by simp [mass]
  by_cases hr : right a d < y
  · have hl := (left_le_right a d).trans_lt hr
    simp [packetCount, hr, hl, hm]
  · by_cases hl : left a < y <;> simp [packetCount, hr, hl, hm]

/-- No bound on integrated phase error follows from a fixed counting discrepancy alone. -/
theorem unbounded_phase_cost_with_bounded_count_discrepancy (B : ℝ) :
    ∃ d : ℝ,
      (∀ y : ℝ, |packetCount 0 d (Real.pi / 2) y -
        (if right 0 d < y then 1 else 0)| ≤ 1 / 2) ∧
      B < ∫ y, ‖phase (packetCount 0 d (Real.pi / 2) y) - 1‖ := by
  refine ⟨|B| + 1, half_packet_count_discrepancy 0 (|B| + 1), ?_⟩
  rw [half_packet_exact_cost, abs_of_pos (by positivity : 0 < |B| + 1)]
  linarith [le_abs_self B, abs_nonneg B]

end RHTower.WeilWorkSettledPhase
