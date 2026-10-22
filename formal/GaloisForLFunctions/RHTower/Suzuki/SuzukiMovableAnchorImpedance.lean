import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The movable-anchor impedance and the hard edge

Moving the defect base from `±i` to `±ic` reweights the fixed-anchor spectral law by
`r_c(u) = (u+1)/(u+c²)`.  On the nonnegative half line this weight is at least one for `c ≤ 1`,
equals one at `c = 1`, and is strictly decreasing in `c`, so the impedance `Z(c) = ∫ r_c dμ` runs
from the possibly large value `Z(0)` down to `Z(1) = 1`.

The hard edge is sharp in the abstract: perturbing the fixed law by a vanishing atom at a vanishing
point leaves the fixed limit unchanged while the movable limit acquires an atom at the origin whose
weight is exactly the limit of `ε(u+1)/(u+c²)`.  Every value in `[0,∞]` of that limit is
attainable, so fixed-anchor convergence alone does not determine the movable limit — and the value
zero does realise the target, so amplification is not a no-go either.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The movable-anchor reweighting of the fixed-anchor spectral law. -/
def movableWeight (c u : ℝ) : ℝ := (u + 1) / (u + c ^ 2)

theorem movableWeight_pos {c u : ℝ} (hu : 0 ≤ u) (hc : c ≠ 0) : 0 < movableWeight c u := by
  have h : (0 : ℝ) < u + c ^ 2 := by positivity
  rw [movableWeight]
  positivity

theorem movableWeight_one (u : ℝ) (hu : 0 ≤ u) : movableWeight 1 u = 1 := by
  rw [movableWeight, one_pow]
  exact div_self (by linarith)

theorem one_le_movableWeight {c u : ℝ} (hu : 0 ≤ u) (hc0 : c ≠ 0) (hc1 : |c| ≤ 1) :
    1 ≤ movableWeight c u := by
  have hcsq : c ^ 2 ≤ 1 := by
    have := abs_nonneg c
    nlinarith [sq_abs c, hc1]
  have hden : (0 : ℝ) < u + c ^ 2 := by positivity
  rw [movableWeight, le_div_iff₀ hden]
  linarith

/-- The weight is strictly decreasing in the anchor scale. -/
theorem movableWeight_strictAnti {c₁ c₂ u : ℝ} (hu : 0 ≤ u) (h1 : 0 < c₁) (h12 : c₁ < c₂) :
    movableWeight c₂ u < movableWeight c₁ u := by
  have hd1 : (0 : ℝ) < u + c₁ ^ 2 := by positivity
  have hd2 : (0 : ℝ) < u + c₂ ^ 2 := by nlinarith
  have hnum : (0 : ℝ) < u + 1 := by linarith
  have hsq : c₁ ^ 2 < c₂ ^ 2 := by nlinarith
  rw [movableWeight, movableWeight, div_lt_div_iff₀ hd2 hd1]
  nlinarith [hsq, hnum]

/-! ## The impedance -/

/-- The finite impedance of a fixed-anchor spectral law. -/
def impedance (μ : Measure ℝ) (c : ℝ) : ℝ := ∫ u, movableWeight c u ∂μ

/-- **`(180)`: the impedance at the fixed anchor is one.** -/
theorem impedance_one {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsupp : ∀ᵐ u ∂μ, 0 ≤ u) : impedance μ 1 = 1 := by
  rw [impedance]
  have : ∫ u, movableWeight 1 u ∂μ = ∫ _u : ℝ, (1 : ℝ) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hsupp] with u hu
    exact movableWeight_one u hu
  rw [this, integral_const]
  simp

/-- Integrability transfers from a smaller anchor to a larger one. -/
theorem integrable_movableWeight_of_lt {μ : Measure ℝ} {c₁ c₂ : ℝ}
    (hsupp : ∀ᵐ u ∂μ, 0 ≤ u) (h1 : 0 < c₁) (h12 : c₁ < c₂)
    (hint : Integrable (movableWeight c₁) μ) : Integrable (movableWeight c₂) μ := by
  refine hint.mono' ?_ ?_
  · have hm : Measurable (movableWeight c₂) := by
      unfold movableWeight
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [hsupp] with u hu
    have h2 : (0 : ℝ) < c₂ := lt_trans h1 h12
    have hpos := movableWeight_pos hu (ne_of_gt h2)
    have hlt := movableWeight_strictAnti hu h1 h12
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    linarith

/-- **`(180)`: the impedance is strictly decreasing in the anchor scale.** -/
theorem impedance_lt_of_lt {μ : Measure ℝ} [IsProbabilityMeasure μ] {c₁ c₂ : ℝ}
    (hsupp : ∀ᵐ u ∂μ, 0 ≤ u) (h1 : 0 < c₁) (h12 : c₁ < c₂)
    (hint : Integrable (movableWeight c₁) μ) :
    impedance μ c₂ < impedance μ c₁ := by
  have hint₂ := integrable_movableWeight_of_lt hsupp h1 h12 hint
  have hdiff : Integrable (fun u => movableWeight c₁ u - movableWeight c₂ u) μ := hint.sub hint₂
  have hnn : 0 ≤ᵐ[μ] fun u => movableWeight c₁ u - movableWeight c₂ u := by
    filter_upwards [hsupp] with u hu
    simp only [Pi.zero_apply, sub_nonneg]
    exact (movableWeight_strictAnti hu h1 h12).le
  have hcompl : μ (Set.Ici (0 : ℝ))ᶜ = 0 := by
    have h := ae_iff.mp hsupp
    have hset : {u : ℝ | ¬ (0 ≤ u)} = (Set.Ici (0 : ℝ))ᶜ := by
      ext u; simp
    rwa [hset] at h
  have hIci : μ (Set.Ici (0 : ℝ)) = 1 := by
    have h := measure_add_measure_compl (μ := μ) (measurableSet_Ici (a := (0 : ℝ)))
    rw [hcompl, add_zero, measure_univ] at h
    exact h
  have hsub : Set.Ici (0 : ℝ)
      ⊆ Function.support (fun u => movableWeight c₁ u - movableWeight c₂ u) := by
    intro u hu
    have hu' : (0 : ℝ) ≤ u := hu
    have hlt := movableWeight_strictAnti hu' h1 h12
    simp only [Function.mem_support, ne_eq, sub_eq_zero]
    exact fun h => absurd h (by linarith)
  have hpos : 0 < ∫ u, (movableWeight c₁ u - movableWeight c₂ u) ∂μ := by
    rw [integral_pos_iff_support_of_nonneg_ae hnn hdiff]
    calc (0 : ℝ≥0∞) < 1 := by norm_num
      _ = μ (Set.Ici (0 : ℝ)) := hIci.symm
      _ ≤ μ (Function.support fun u => movableWeight c₁ u - movableWeight c₂ u) :=
          measure_mono hsub
  rw [integral_sub hint hint₂] at hpos
  rw [impedance, impedance]
  linarith

/-! ## `(179)`: the sharp hard edge -/

/-- **`(179)`: the movable limit of a vanishing atomic perturbation.**  The fixed limit is
unaffected, while the movable limit acquires an atom at the origin of weight `ℓ`. -/
theorem tendsto_mixtureReweighted {εn ℓn Zn Jn : ℕ → ℝ} {B ℓ J f0 : ℝ}
    (hB : 0 < B) (hℓ : 0 ≤ ℓ)
    (hε : Tendsto εn atTop (𝓝 0)) (hZ : Tendsto Zn atTop (𝓝 B))
    (hJ : Tendsto Jn atTop (𝓝 J)) (hl : Tendsto ℓn atTop (𝓝 ℓ)) :
    Tendsto (fun n => ((1 - εn n) * Jn n + ℓn n * f0) / ((1 - εn n) * Zn n + ℓn n)) atTop
      (𝓝 ((J + ℓ * f0) / (B + ℓ))) := by
  have hnum : Tendsto (fun n => (1 - εn n) * Jn n + ℓn n * f0) atTop (𝓝 (J + ℓ * f0)) := by
    have h1 : Tendsto (fun n => (1 - εn n) * Jn n) atTop (𝓝 ((1 - 0) * J)) :=
      ((tendsto_const_nhds.sub hε).mul hJ)
    have h2 : Tendsto (fun n => ℓn n * f0) atTop (𝓝 (ℓ * f0)) := hl.mul tendsto_const_nhds
    have := h1.add h2
    simpa using this
  have hden : Tendsto (fun n => (1 - εn n) * Zn n + ℓn n) atTop (𝓝 (B + ℓ)) := by
    have h1 : Tendsto (fun n => (1 - εn n) * Zn n) atTop (𝓝 ((1 - 0) * B)) :=
      ((tendsto_const_nhds.sub hε).mul hZ)
    have := h1.add hl
    simpa using this
  exact hnum.div hden (by linarith)

/-- With vanishing amplification the movable limit is the target itself. -/
theorem mixtureReweighted_zero {B I f0 : ℝ} (hB : 0 < B) :
    (B * I + 0 * f0) / (B + 0) = I := by
  have hB' : B ≠ 0 := ne_of_gt hB
  field_simp
  ring

/-- With unbounded amplification the movable limit is the point mass at the origin. -/
theorem tendsto_mixtureReweighted_atTop {B I f0 : ℝ} (hB : 0 < B) :
    Tendsto (fun ℓ : ℝ => (B * I + ℓ * f0) / (B + ℓ)) atTop (𝓝 f0) := by
  have hrw : ∀ ℓ : ℝ, 0 < B + ℓ →
      (B * I + ℓ * f0) / (B + ℓ) = f0 + (B * I - B * f0) / (B + ℓ) := by
    intro ℓ hℓ
    field_simp
    ring
  have htail : Tendsto (fun ℓ : ℝ => f0 + (B * I - B * f0) / (B + ℓ)) atTop (𝓝 (f0 + 0)) := by
    refine tendsto_const_nhds.add ?_
    exact (tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ B tendsto_id))
  rw [add_zero] at htail
  refine Filter.Tendsto.congr' ?_ htail
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ℓ hℓ
  exact (hrw ℓ (by linarith)).symm

end GaloisForLFunctions.RHTower
