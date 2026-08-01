import GaloisForLFunctions.RHTower.DeningerWeightedMixedDivisorNorms
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Normed.Group.Real
import GaloisForLFunctions.RHTower.DeningerAdelicKummerGelfandTriple

/-!
# The weighted counting measure on the primes

The weighted `L¹` and `L²` quantities on finitely supported divisor coordinates are the `Lᵖ`
norms of the weighted counting measure `∑_p w_p δ_p`.  This identifies the weighted mixed
divisor space with the mixed `L¹/L²` space of that measure, so its completion is the Banach
space already constructed for an arbitrary measure.

* `deningerWeightMeasure` is the measure.
* `deningerWeightMeasure_lintegral` computes its lower integral as a weighted sum.
* `deningerWeightMeasure_lintegral_abs` identifies the weighted `L¹` quantity.
-/

namespace RHTower

open MeasureTheory ENNReal

section WeightedCounting

variable (w : ℕ → ℝ)

/-- The weighted counting measure `∑_p w_p δ_p` on the primes. -/
noncomputable def deningerWeightMeasure : Measure ℕ :=
  Measure.sum fun p => ENNReal.ofReal (w p) • Measure.dirac p

variable {w}

/-- The lower integral against the weighted counting measure is the weighted sum. -/
theorem deningerWeightMeasure_lintegral (f : ℕ → ℝ≥0∞) :
    ∫⁻ n, f n ∂(deningerWeightMeasure w) = ∑' p, ENNReal.ofReal (w p) * f p := by
  rw [deningerWeightMeasure, lintegral_sum_measure]
  refine tsum_congr fun p => ?_
  rw [lintegral_smul_measure, MeasureTheory.lintegral_dirac, smul_eq_mul]

/-- On a finitely supported vector the weighted `L¹` quantity is the lower integral of the
absolute value. -/
theorem deningerWeightMeasure_lintegral_abs (hw : ∀ p, 0 ≤ w p) (x : ℕ →₀ ℝ) :
    ∫⁻ n, ENNReal.ofReal |x n| ∂(deningerWeightMeasure w)
      = ENNReal.ofReal (deningerWeightedL1 w x) := by
  classical
  rw [deningerWeightMeasure_lintegral]
  have hzero : ∀ p ∉ x.support,
      ENNReal.ofReal (w p) * ENNReal.ofReal |x p| = 0 := by
    intro p hp
    rw [Finsupp.notMem_support_iff.mp hp]
    simp
  rw [tsum_eq_sum hzero, deningerWeightedL1, ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [ENNReal.ofReal_mul (hw p)]
  · exact fun p _ => mul_nonneg (hw p) (abs_nonneg _)

/-- On a finitely supported vector the squared weighted `L²` quantity is the lower integral of
the square. -/
theorem deningerWeightMeasure_lintegral_sq (hw : ∀ p, 0 ≤ w p) (x : ℕ →₀ ℝ) :
    ∫⁻ n, ENNReal.ofReal ((x n) ^ 2) ∂(deningerWeightMeasure w)
      = ENNReal.ofReal (deningerWeightedL2Sq w x) := by
  classical
  rw [deningerWeightMeasure_lintegral]
  have hzero : ∀ p ∉ x.support,
      ENNReal.ofReal (w p) * ENNReal.ofReal ((x p) ^ 2) = 0 := by
    intro p hp
    rw [Finsupp.notMem_support_iff.mp hp]
    simp
  rw [tsum_eq_sum hzero, deningerWeightedL2Sq, ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [ENNReal.ofReal_mul (hw p)]
  · exact fun p _ => mul_nonneg (hw p) (sq_nonneg _)

/-- **The weighted mixed quantity is the mixed `L¹/L²` quantity of the weighted counting
measure.**  Both summands are read off the corresponding lower integrals. -/
theorem deningerWeightedMix_eq_lintegrals (hw : ∀ p, 0 ≤ w p) (x : ℕ →₀ ℝ) :
    ENNReal.ofReal (deningerWeightedMix w x)
      = ∫⁻ n, ENNReal.ofReal |x n| ∂(deningerWeightMeasure w)
        + ENNReal.ofReal
            (Real.sqrt (deningerWeightedL2Sq w x)) := by
  rw [deningerWeightMeasure_lintegral_abs hw x, deningerWeightedMix,
    ENNReal.ofReal_add (deningerWeightedL1_nonneg hw x) (Real.sqrt_nonneg _)]

/-- **The weighted `L¹` quantity is an `eLpNorm`.** -/
theorem deningerWeightedL1_eq_eLpNorm (hw : ∀ p, 0 ≤ w p) (x : ℕ →₀ ℝ) :
    MeasureTheory.eLpNorm (fun n => x n) 1 (deningerWeightMeasure w)
      = ENNReal.ofReal (deningerWeightedL1 w x) := by
  rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
  rw [← deningerWeightMeasure_lintegral_abs hw x]
  refine lintegral_congr fun n => ?_
  exact Real.enorm_eq_ofReal_abs (x n)

/-- **The weighted `L²` quantity is an `eLpNorm`.** -/
theorem deningerWeightedL2_eq_eLpNorm (hw : ∀ p, 0 ≤ w p) (x : ℕ →₀ ℝ) :
    MeasureTheory.eLpNorm (fun n => x n) 2 (deningerWeightMeasure w)
      = ENNReal.ofReal (Real.sqrt (deningerWeightedL2Sq w x)) := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have htoReal : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [htoReal]
  have hint : ∫⁻ n, ‖(x n : ℝ)‖ₑ ^ (2 : ℝ) ∂(deningerWeightMeasure w)
      = ENNReal.ofReal (deningerWeightedL2Sq w x) := by
    rw [← deningerWeightMeasure_lintegral_sq hw x]
    refine lintegral_congr fun n => ?_
    have habs : |x n| ^ (2 : ℝ) = x n ^ 2 := by
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    rw [Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2), habs]
  rw [hint,
    ENNReal.ofReal_rpow_of_nonneg (deningerWeightedL2Sq_nonneg hw x)
      (by norm_num : (0:ℝ) ≤ 1 / 2), Real.sqrt_eq_rpow]

/-- A finitely supported vector lies in every `Lᵖ` of the weighted counting measure. -/
theorem deningerMemLp_one (hw : ∀ p, 0 ≤ w p) (x : ℕ →₀ ℝ) :
    MeasureTheory.MemLp (fun n => x n) 1 (deningerWeightMeasure w) := by
  refine ⟨(measurable_from_top (f := fun n : ℕ => (x n : ℝ))).aestronglyMeasurable, ?_⟩
  rw [deningerWeightedL1_eq_eLpNorm hw x]
  exact ENNReal.ofReal_lt_top

theorem deningerMemLp_two (hw : ∀ p, 0 ≤ w p) (x : ℕ →₀ ℝ) :
    MeasureTheory.MemLp (fun n => x n) 2 (deningerWeightMeasure w) := by
  refine ⟨(measurable_from_top (f := fun n : ℕ => (x n : ℝ))).aestronglyMeasurable, ?_⟩
  rw [deningerWeightedL2_eq_eLpNorm hw x]
  exact ENNReal.ofReal_lt_top

/-- **The weighted divisor coordinates sit inside the mixed `L¹/L²` Banach space.** -/
noncomputable def deningerToMixed (hw : ∀ p, 0 ≤ w p) (x : ℕ →₀ ℝ) :
    DeningerMixed (deningerWeightMeasure w) :=
  ⟨WithLp.toLp 1 ((deningerMemLp_one hw x).toLp _, (deningerMemLp_two hw x).toLp _), by
    show ((((deningerMemLp_one hw x).toLp (fun n => x n)) : ℕ → ℝ))
        =ᵐ[deningerWeightMeasure w] (((deningerMemLp_two hw x).toLp (fun n => x n)) : ℕ → ℝ)
    filter_upwards [(deningerMemLp_one hw x).coeFn_toLp,
      (deningerMemLp_two hw x).coeFn_toLp] with n h1 h2
    rw [h1, h2]⟩

/-- **The mixed quantity is the norm of the mixed space.**  This transports `(6)` and hence the
strictness statements into the completed setting: the ambient space is the Banach space
`DeningerMixed` of the weighted counting measure. -/
theorem deningerToMixed_norm (hw : ∀ p, 0 ≤ w p) (x : ℕ →₀ ℝ) :
    ‖deningerToMixed hw x‖ = deningerWeightedMix w x := by
  rw [deningerMixed_norm]
  have h1 : ‖(deningerToMixed hw x : WithLp 1 (MeasureTheory.Lp ℝ 1 (deningerWeightMeasure w)
      × MeasureTheory.Lp ℝ 2 (deningerWeightMeasure w))).fst‖ = deningerWeightedL1 w x := by
    show ‖(deningerMemLp_one hw x).toLp (fun n => x n)‖ = _
    rw [MeasureTheory.Lp.norm_toLp, deningerWeightedL1_eq_eLpNorm hw x,
      ENNReal.toReal_ofReal (deningerWeightedL1_nonneg hw x)]
  have h2 : ‖(deningerToMixed hw x : WithLp 1 (MeasureTheory.Lp ℝ 1 (deningerWeightMeasure w)
      × MeasureTheory.Lp ℝ 2 (deningerWeightMeasure w))).snd‖
      = Real.sqrt (deningerWeightedL2Sq w x) := by
    show ‖(deningerMemLp_two hw x).toLp (fun n => x n)‖ = _
    rw [MeasureTheory.Lp.norm_toLp, deningerWeightedL2_eq_eLpNorm hw x,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  rw [h1, h2, deningerWeightedMix]

end WeightedCounting

end RHTower
