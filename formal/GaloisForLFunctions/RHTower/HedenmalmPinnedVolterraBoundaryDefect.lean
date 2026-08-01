import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Universal pinned-Volterra boundary defect on L²(0,1)

This module constructs the pinned primitive

```text
(Cf)(t) = ∫₀ᵗ f(u) du - t ∫₀¹ f(u) du
```

as an actual bounded operator on infinite-dimensional complex `L²(0,1)`.  It constructs the
reverse primitive, proves by Fubini that it is the Hilbert adjoint, and identifies `C† + C` with
the affine boundary operator of kernel `1-t-u`.  The boundary range is exactly
`span {1,t}`, has algebraic rank two, and carries explicit quadratic values `+1/6` and `-1/6`.

A Lebesgue-differentiation argument proves that `C†` is injective.  Therefore any bounded operator
`A` satisfying `C† A + A C = 0` kills the constant mode, and no injective bounded composite metric
can solve this symmetry equation.  If `A` is a pointwise multiplication operator, the same argument
forces the entire operator to vanish.  This is the full operator theorem, not a formalization of
only the resulting `2 × 2` matrix.

The probability-integral transform from Hedenmalm's theta-source space and its unbounded quantile
multiplier are separate source-specialization obligations; no claim about RH or root-mode flux
neutrality is made here.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

def unitIntervalMeasure : Measure ℝ :=
  volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure unitIntervalMeasure := by
  constructor
  rw [unitIntervalMeasure, Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num

instance : NullSingletonClass unitIntervalMeasure := by
  unfold unitIntervalMeasure
  infer_instance

abbrev H : Type := Lp ℂ 2 unitIntervalMeasure

theorem integrable_coe (f : H) : Integrable (fun t => f t) unitIntervalMeasure :=
  (Lp.memLp f).integrable one_le_two

theorem integral_norm_le_norm (f : H) :
    ∫ t, ‖f t‖ ∂unitIntervalMeasure ≤ ‖f‖ := by
  have hint : Integrable (fun t => f t) unitIntervalMeasure := integrable_coe f
  have hcoe : (fun t => (hint.toL1 _) t) =ᵐ[unitIntervalMeasure] fun t => f t :=
    hint.coeFn_toL1
  have h1 : ‖hint.toL1 (fun t => f t)‖ = ∫ t, ‖f t‖ ∂unitIntervalMeasure := by
    rw [L1.norm_eq_integral_norm]
    exact integral_congr_ae (by filter_upwards [hcoe] with t ht; rw [ht])
  have h2 : ‖hint.toL1 (fun t => f t)‖ =
      (eLpNorm (fun t => f t) 1 unitIntervalMeasure).toReal := by
    rw [Lp.norm_def]
    exact congrArg ENNReal.toReal (eLpNorm_congr_ae hcoe)
  have h3 : eLpNorm (fun t => f t) 1 unitIntervalMeasure ≤
      eLpNorm (fun t => f t) 2 unitIntervalMeasure :=
    eLpNorm_le_eLpNorm_of_exponent_le one_le_two (Lp.aestronglyMeasurable f)
  have h4 : eLpNorm (fun t => f t) 2 unitIntervalMeasure ≠ ⊤ :=
    (Lp.memLp f).eLpNorm_ne_top
  rw [← h1, h2, Lp.norm_def]
  exact ENNReal.toReal_mono h4 h3

def lowerKernelSet : Set (ℝ × ℝ) := {p | p.2 ≤ p.1}

theorem measurableSet_lowerKernelSet : MeasurableSet lowerKernelSet := by
  exact measurableSet_le measurable_snd measurable_fst

def pinnedPrefix (f : H) (t : ℝ) : ℂ :=
  ∫ u, (Iic t).indicator (fun u => f u) u ∂unitIntervalMeasure

def pinnedMean (f : H) : ℂ :=
  ∫ u, f u ∂unitIntervalMeasure

def pinnedVolterraFun (f : H) (t : ℝ) : ℂ :=
  pinnedPrefix f t - t * pinnedMean f

private theorem integrable_lowerKernel (f : H) :
    Integrable
      (lowerKernelSet.indicator (fun p : ℝ × ℝ => f p.2))
      (unitIntervalMeasure.prod unitIntervalMeasure) := by
  exact (integrable_coe f).comp_snd unitIntervalMeasure
    |>.indicator measurableSet_lowerKernelSet

theorem aestronglyMeasurable_pinnedPrefix (f : H) :
    AEStronglyMeasurable (pinnedPrefix f) unitIntervalMeasure := by
  have hkernel : AEStronglyMeasurable
      (lowerKernelSet.indicator (fun p : ℝ × ℝ => f p.2))
      (unitIntervalMeasure.prod unitIntervalMeasure) :=
    (integrable_lowerKernel f).aestronglyMeasurable
  have h := hkernel.integral_prod_right'
  change AEStronglyMeasurable
    (fun t => ∫ u, if u ≤ t then f u else 0 ∂unitIntervalMeasure) unitIntervalMeasure
  simpa only [lowerKernelSet, Set.indicator_apply, mem_setOf_eq] using h

theorem aestronglyMeasurable_pinnedVolterraFun (f : H) :
    AEStronglyMeasurable (pinnedVolterraFun f) unitIntervalMeasure := by
  exact (aestronglyMeasurable_pinnedPrefix f).sub
    (Complex.continuous_ofReal.aestronglyMeasurable.mul_const _)

theorem norm_pinnedMean_le (f : H) : ‖pinnedMean f‖ ≤ ‖f‖ := by
  exact (norm_integral_le_integral_norm _).trans (integral_norm_le_norm f)

theorem norm_pinnedPrefix_le (f : H) (t : ℝ) : ‖pinnedPrefix f t‖ ≤ ‖f‖ := by
  refine (norm_integral_le_integral_norm _).trans ?_
  calc
    ∫ u, ‖(Iic t).indicator (fun u => f u) u‖ ∂unitIntervalMeasure
        ≤ ∫ u, ‖f u‖ ∂unitIntervalMeasure := by
          apply integral_mono_ae
          · exact ((integrable_coe f).indicator measurableSet_Iic).norm
          · exact (integrable_coe f).norm
          · filter_upwards [] with u
            simp only [indicator_apply]
            split_ifs <;> simp
    _ ≤ ‖f‖ := integral_norm_le_norm f

theorem norm_pinnedVolterraFun_le (f : H) (t : ℝ) (ht : t ∈ Icc 0 1) :
    ‖pinnedVolterraFun f t‖ ≤ 2 * ‖f‖ := by
  rw [pinnedVolterraFun]
  calc
    ‖pinnedPrefix f t - (t : ℝ) * pinnedMean f‖
        ≤ ‖pinnedPrefix f t‖ + ‖((t : ℝ) : ℂ) * pinnedMean f‖ := by
          exact norm_sub_le _ _
    _ ≤ ‖f‖ + ‖f‖ := by
      apply add_le_add (norm_pinnedPrefix_le f t)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
      calc
        t * ‖pinnedMean f‖ ≤ 1 * ‖pinnedMean f‖ :=
          mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
        _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_left (norm_pinnedMean_le f) zero_le_one
        _ = ‖f‖ := one_mul _
    _ = 2 * ‖f‖ := by ring

theorem memLp_pinnedVolterraFun (f : H) :
    MemLp (pinnedVolterraFun f) 2 unitIntervalMeasure :=
  MemLp.of_bound (aestronglyMeasurable_pinnedVolterraFun f) (2 * ‖f‖)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact norm_pinnedVolterraFun_le f t ht)

def pinnedVolterra (f : H) : H :=
  (memLp_pinnedVolterraFun f).toLp (pinnedVolterraFun f)

theorem pinnedPrefix_add (f g : H) (t : ℝ) :
    pinnedPrefix (f + g) t = pinnedPrefix f t + pinnedPrefix g t := by
  have hcoe : (fun u => (f + g) u) =ᵐ[unitIntervalMeasure] fun u => f u + g u :=
    Lp.coeFn_add f g
  rw [pinnedPrefix, pinnedPrefix, pinnedPrefix]
  calc
    (∫ u, (Iic t).indicator (fun u => (f + g) u) u ∂unitIntervalMeasure)
        = ∫ u, (Iic t).indicator (fun u => f u + g u) u ∂unitIntervalMeasure := by
            apply integral_congr_ae
            filter_upwards [hcoe] with u hu
            simp only [indicator_apply]
            split_ifs
            · exact hu
            · rfl
    _ = _ := by
      rw [← integral_add]
      · apply integral_congr_ae
        filter_upwards [] with u
        simp only [indicator_apply]
        split_ifs <;> simp
      · exact (integrable_coe f).indicator measurableSet_Iic
      · exact (integrable_coe g).indicator measurableSet_Iic

theorem pinnedMean_add (f g : H) : pinnedMean (f + g) = pinnedMean f + pinnedMean g := by
  rw [pinnedMean, pinnedMean, pinnedMean, ← integral_add (integrable_coe f) (integrable_coe g)]
  exact integral_congr_ae (Lp.coeFn_add f g)

theorem pinnedVolterra_add (f g : H) :
    pinnedVolterra (f + g) = pinnedVolterra f + pinnedVolterra g := by
  unfold pinnedVolterra
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (memLp_pinnedVolterraFun (f + g)),
    MemLp.coeFn_toLp (memLp_pinnedVolterraFun f),
    MemLp.coeFn_toLp (memLp_pinnedVolterraFun g), Lp.coeFn_add (pinnedVolterra f) (pinnedVolterra g)]
      with t hfg hf hg hadd
  simp only [pinnedVolterra] at hadd
  rw [hfg, hadd]
  simp only [Pi.add_apply, hf, hg, pinnedVolterraFun, pinnedVolterraFun, pinnedVolterraFun,
    pinnedPrefix_add, pinnedMean_add]
  ring

theorem pinnedPrefix_smul (c : ℂ) (f : H) (t : ℝ) :
    pinnedPrefix (c • f) t = c * pinnedPrefix f t := by
  have hcoe : (fun u => (c • f) u) =ᵐ[unitIntervalMeasure] fun u => c * f u := by
    filter_upwards [Lp.coeFn_smul c f] with u hu
    simpa [smul_eq_mul] using hu
  rw [pinnedPrefix, pinnedPrefix]
  calc
    (∫ u, (Iic t).indicator (fun u => (c • f) u) u ∂unitIntervalMeasure)
        = ∫ u, c * (Iic t).indicator (fun u => f u) u ∂unitIntervalMeasure := by
            apply integral_congr_ae
            filter_upwards [hcoe] with u hu
            simp only [indicator_apply]
            split_ifs <;> simp [hu]
    _ = _ := by rw [integral_const_mul]

theorem pinnedMean_smul (c : ℂ) (f : H) : pinnedMean (c • f) = c * pinnedMean f := by
  rw [pinnedMean, pinnedMean]
  calc
    (∫ u, (c • f) u ∂unitIntervalMeasure) =
        ∫ u, c * f u ∂unitIntervalMeasure := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul c f] with u hu
      simpa [smul_eq_mul] using hu
    _ = _ := by rw [integral_const_mul]

theorem pinnedVolterra_smul (c : ℂ) (f : H) :
    pinnedVolterra (c • f) = c • pinnedVolterra f := by
  unfold pinnedVolterra
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (memLp_pinnedVolterraFun (c • f)),
    MemLp.coeFn_toLp (memLp_pinnedVolterraFun f),
    Lp.coeFn_smul c (pinnedVolterra f)] with t hcf hf hsmul
  simp only [pinnedVolterra] at hsmul
  rw [hcf, hsmul]
  simp only [Pi.smul_apply, hf, pinnedVolterraFun, pinnedVolterraFun, pinnedPrefix_smul,
    pinnedMean_smul]
  simp only [smul_eq_mul]
  ring

theorem norm_pinnedVolterra_le (f : H) : ‖pinnedVolterra f‖ ≤ 2 * ‖f‖ := by
  rw [pinnedVolterra, Lp.norm_toLp]
  have hmono : eLpNorm (pinnedVolterraFun f) 2 unitIntervalMeasure ≤
      eLpNorm (fun _ : ℝ => (2 * ‖f‖ : ℂ)) 2 unitIntervalMeasure :=
    eLpNorm_mono_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simpa using norm_pinnedVolterraFun_le f t ht)
  have htop : eLpNorm (fun _ : ℝ => (2 * ‖f‖ : ℂ)) 2 unitIntervalMeasure ≠ ⊤ :=
    (memLp_const (2 * ‖f‖ : ℂ)).eLpNorm_ne_top
  calc
    (eLpNorm (pinnedVolterraFun f) 2 unitIntervalMeasure).toReal
        ≤ (eLpNorm (fun _ : ℝ => (2 * ‖f‖ : ℂ)) 2 unitIntervalMeasure).toReal :=
          ENNReal.toReal_mono htop hmono
    _ = 2 * ‖f‖ := by
      rw [eLpNorm_const (2 * ‖f‖ : ℂ) (by norm_num) (NeZero.ne unitIntervalMeasure)]
      simp [measure_univ]

def pinnedVolterraCLM : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := pinnedVolterra
      map_add' := pinnedVolterra_add
      map_smul' := pinnedVolterra_smul }
    2 norm_pinnedVolterra_le

def upperKernelSet : Set (ℝ × ℝ) := {p | p.1 ≤ p.2}

theorem measurableSet_upperKernelSet : MeasurableSet upperKernelSet := by
  exact measurableSet_le measurable_fst measurable_snd

def pinnedUpperPrefix (f : H) (t : ℝ) : ℂ :=
  ∫ u, (Ici t).indicator (fun u => f u) u ∂unitIntervalMeasure

def pinnedFirstMoment (f : H) : ℂ :=
  ∫ u, (u : ℂ) * f u ∂unitIntervalMeasure

def pinnedVolterraAdjointFun (f : H) (t : ℝ) : ℂ :=
  pinnedUpperPrefix f t - pinnedFirstMoment f

private theorem integrable_upperKernel (f : H) :
    Integrable
      (upperKernelSet.indicator (fun p : ℝ × ℝ => f p.2))
      (unitIntervalMeasure.prod unitIntervalMeasure) := by
  exact (integrable_coe f).comp_snd unitIntervalMeasure
    |>.indicator measurableSet_upperKernelSet

theorem aestronglyMeasurable_pinnedUpperPrefix (f : H) :
    AEStronglyMeasurable (pinnedUpperPrefix f) unitIntervalMeasure := by
  have hkernel : AEStronglyMeasurable
      (upperKernelSet.indicator (fun p : ℝ × ℝ => f p.2))
      (unitIntervalMeasure.prod unitIntervalMeasure) :=
    (integrable_upperKernel f).aestronglyMeasurable
  have h := hkernel.integral_prod_right'
  change AEStronglyMeasurable
    (fun t => ∫ u, if t ≤ u then f u else 0 ∂unitIntervalMeasure) unitIntervalMeasure
  simpa only [upperKernelSet, Set.indicator_apply, mem_setOf_eq] using h

theorem integrable_coordinate_mul (f : H) :
    Integrable (fun u : ℝ => (u : ℂ) * f u) unitIntervalMeasure := by
  refine (integrable_coe f).bdd_mul (c := 1)
    Complex.continuous_ofReal.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu.1] using hu.2

theorem aestronglyMeasurable_pinnedVolterraAdjointFun (f : H) :
    AEStronglyMeasurable (pinnedVolterraAdjointFun f) unitIntervalMeasure := by
  exact (aestronglyMeasurable_pinnedUpperPrefix f).sub aestronglyMeasurable_const

theorem norm_pinnedUpperPrefix_le (f : H) (t : ℝ) : ‖pinnedUpperPrefix f t‖ ≤ ‖f‖ := by
  refine (norm_integral_le_integral_norm _).trans ?_
  calc
    ∫ u, ‖(Ici t).indicator (fun u => f u) u‖ ∂unitIntervalMeasure
        ≤ ∫ u, ‖f u‖ ∂unitIntervalMeasure := by
          apply integral_mono_ae
          · exact ((integrable_coe f).indicator measurableSet_Ici).norm
          · exact (integrable_coe f).norm
          · filter_upwards [] with u
            simp only [indicator_apply]
            split_ifs <;> simp
    _ ≤ ‖f‖ := integral_norm_le_norm f

theorem norm_pinnedFirstMoment_le (f : H) : ‖pinnedFirstMoment f‖ ≤ ‖f‖ := by
  refine (norm_integral_le_integral_norm _).trans ?_
  calc
    ∫ u, ‖(u : ℂ) * f u‖ ∂unitIntervalMeasure
        ≤ ∫ u, ‖f u‖ ∂unitIntervalMeasure := by
          apply integral_mono_ae
          · exact (integrable_coordinate_mul f).norm
          · exact (integrable_coe f).norm
          · filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu.1]
            exact mul_le_of_le_one_left (norm_nonneg _) hu.2
    _ ≤ ‖f‖ := integral_norm_le_norm f

theorem norm_pinnedVolterraAdjointFun_le (f : H) (t : ℝ) :
    ‖pinnedVolterraAdjointFun f t‖ ≤ 2 * ‖f‖ := by
  rw [pinnedVolterraAdjointFun]
  calc
    ‖pinnedUpperPrefix f t - pinnedFirstMoment f‖
        ≤ ‖pinnedUpperPrefix f t‖ + ‖pinnedFirstMoment f‖ := norm_sub_le _ _
    _ ≤ ‖f‖ + ‖f‖ := add_le_add (norm_pinnedUpperPrefix_le f t)
      (norm_pinnedFirstMoment_le f)
    _ = 2 * ‖f‖ := by ring

theorem memLp_pinnedVolterraAdjointFun (f : H) :
    MemLp (pinnedVolterraAdjointFun f) 2 unitIntervalMeasure :=
  MemLp.of_bound (aestronglyMeasurable_pinnedVolterraAdjointFun f) (2 * ‖f‖)
    (Filter.Eventually.of_forall (norm_pinnedVolterraAdjointFun_le f))

def pinnedVolterraAdjoint (f : H) : H :=
  (memLp_pinnedVolterraAdjointFun f).toLp (pinnedVolterraAdjointFun f)

theorem pinnedUpperPrefix_add (f g : H) (t : ℝ) :
    pinnedUpperPrefix (f + g) t = pinnedUpperPrefix f t + pinnedUpperPrefix g t := by
  have hcoe : (fun u => (f + g) u) =ᵐ[unitIntervalMeasure] fun u => f u + g u :=
    Lp.coeFn_add f g
  rw [pinnedUpperPrefix, pinnedUpperPrefix, pinnedUpperPrefix]
  calc
    (∫ u, (Ici t).indicator (fun u => (f + g) u) u ∂unitIntervalMeasure)
        = ∫ u, (Ici t).indicator (fun u => f u + g u) u ∂unitIntervalMeasure := by
            apply integral_congr_ae
            filter_upwards [hcoe] with u hu
            simp only [indicator_apply]
            split_ifs
            · exact hu
            · rfl
    _ = _ := by
      rw [← integral_add]
      · apply integral_congr_ae
        filter_upwards [] with u
        simp only [indicator_apply]
        split_ifs <;> simp
      · exact (integrable_coe f).indicator measurableSet_Ici
      · exact (integrable_coe g).indicator measurableSet_Ici

theorem pinnedFirstMoment_add (f g : H) :
    pinnedFirstMoment (f + g) = pinnedFirstMoment f + pinnedFirstMoment g := by
  rw [pinnedFirstMoment, pinnedFirstMoment, pinnedFirstMoment,
    ← integral_add (integrable_coordinate_mul f) (integrable_coordinate_mul g)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add f g] with u hu
  simp only [Pi.add_apply] at hu ⊢
  rw [hu]
  ring

theorem pinnedVolterraAdjoint_add (f g : H) :
    pinnedVolterraAdjoint (f + g) = pinnedVolterraAdjoint f + pinnedVolterraAdjoint g := by
  unfold pinnedVolterraAdjoint
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (memLp_pinnedVolterraAdjointFun (f + g)),
    MemLp.coeFn_toLp (memLp_pinnedVolterraAdjointFun f),
    MemLp.coeFn_toLp (memLp_pinnedVolterraAdjointFun g),
    Lp.coeFn_add (pinnedVolterraAdjoint f) (pinnedVolterraAdjoint g)]
      with t hfg hf hg hadd
  simp only [pinnedVolterraAdjoint] at hadd
  rw [hfg, hadd]
  simp only [Pi.add_apply, hf, hg, pinnedVolterraAdjointFun, pinnedUpperPrefix_add,
    pinnedFirstMoment_add]
  ring

theorem pinnedUpperPrefix_smul (c : ℂ) (f : H) (t : ℝ) :
    pinnedUpperPrefix (c • f) t = c * pinnedUpperPrefix f t := by
  have hcoe : (fun u => (c • f) u) =ᵐ[unitIntervalMeasure] fun u => c * f u := by
    filter_upwards [Lp.coeFn_smul c f] with u hu
    simpa [smul_eq_mul] using hu
  rw [pinnedUpperPrefix, pinnedUpperPrefix]
  calc
    (∫ u, (Ici t).indicator (fun u => (c • f) u) u ∂unitIntervalMeasure)
        = ∫ u, c * (Ici t).indicator (fun u => f u) u ∂unitIntervalMeasure := by
            apply integral_congr_ae
            filter_upwards [hcoe] with u hu
            simp only [indicator_apply]
            split_ifs <;> simp [hu]
    _ = _ := by rw [integral_const_mul]

theorem pinnedFirstMoment_smul (c : ℂ) (f : H) :
    pinnedFirstMoment (c • f) = c * pinnedFirstMoment f := by
  rw [pinnedFirstMoment, pinnedFirstMoment]
  calc
    (∫ u, (u : ℂ) * (c • f) u ∂unitIntervalMeasure)
        = ∫ u, c * ((u : ℂ) * f u) ∂unitIntervalMeasure := by
            apply integral_congr_ae
            filter_upwards [Lp.coeFn_smul c f] with u hu
            rw [hu]
            simp only [Pi.smul_apply, smul_eq_mul]
            ring
    _ = _ := by rw [integral_const_mul]

theorem pinnedVolterraAdjoint_smul (c : ℂ) (f : H) :
    pinnedVolterraAdjoint (c • f) = c • pinnedVolterraAdjoint f := by
  unfold pinnedVolterraAdjoint
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (memLp_pinnedVolterraAdjointFun (c • f)),
    MemLp.coeFn_toLp (memLp_pinnedVolterraAdjointFun f),
    Lp.coeFn_smul c (pinnedVolterraAdjoint f)] with t hcf hf hsmul
  simp only [pinnedVolterraAdjoint] at hsmul
  rw [hcf, hsmul]
  simp only [Pi.smul_apply, hf, pinnedVolterraAdjointFun, pinnedUpperPrefix_smul,
    pinnedFirstMoment_smul, smul_eq_mul]
  ring

theorem norm_pinnedVolterraAdjoint_le (f : H) : ‖pinnedVolterraAdjoint f‖ ≤ 2 * ‖f‖ := by
  rw [pinnedVolterraAdjoint, Lp.norm_toLp]
  have hmono : eLpNorm (pinnedVolterraAdjointFun f) 2 unitIntervalMeasure ≤
      eLpNorm (fun _ : ℝ => (2 * ‖f‖ : ℂ)) 2 unitIntervalMeasure :=
    eLpNorm_mono_ae (Filter.Eventually.of_forall fun t => by
      simpa using norm_pinnedVolterraAdjointFun_le f t)
  have htop : eLpNorm (fun _ : ℝ => (2 * ‖f‖ : ℂ)) 2 unitIntervalMeasure ≠ ⊤ :=
    (memLp_const (2 * ‖f‖ : ℂ)).eLpNorm_ne_top
  calc
    (eLpNorm (pinnedVolterraAdjointFun f) 2 unitIntervalMeasure).toReal
        ≤ (eLpNorm (fun _ : ℝ => (2 * ‖f‖ : ℂ)) 2 unitIntervalMeasure).toReal :=
          ENNReal.toReal_mono htop hmono
    _ = 2 * ‖f‖ := by
      rw [eLpNorm_const (2 * ‖f‖ : ℂ) (by norm_num) (NeZero.ne unitIntervalMeasure)]
      simp [measure_univ]

def pinnedVolterraAdjointCLM : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := pinnedVolterraAdjoint
      map_add' := pinnedVolterraAdjoint_add
      map_smul' := pinnedVolterraAdjoint_smul }
    2 norm_pinnedVolterraAdjoint_le

theorem inner_lp_eq (f g : H) :
    inner ℂ f g = ∫ t, (starRingEnd ℂ) (f t) * g t ∂unitIntervalMeasure := by
  rw [L2.inner_def]
  exact integral_congr_ae (Filter.Eventually.of_forall fun t => RCLike.inner_apply' _ _)

theorem pinnedVolterra_coeFn (f : H) :
    (fun t => (pinnedVolterra f) t) =ᵐ[unitIntervalMeasure] pinnedVolterraFun f :=
  MemLp.coeFn_toLp (memLp_pinnedVolterraFun f)

theorem pinnedVolterraAdjoint_coeFn (f : H) :
    (fun t => (pinnedVolterraAdjoint f) t) =ᵐ[unitIntervalMeasure]
      pinnedVolterraAdjointFun f :=
  MemLp.coeFn_toLp (memLp_pinnedVolterraAdjointFun f)

private theorem integrable_conj_coe (f : H) :
    Integrable (fun t => (starRingEnd ℂ) (f t)) unitIntervalMeasure := by
  exact (integrable_coe f).norm.mono'
    (Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun t => by rw [RCLike.norm_conj])

def pinnedTriangleKernel (f g : H) (p : ℝ × ℝ) : ℂ :=
  upperKernelSet.indicator
    (fun p : ℝ × ℝ => (starRingEnd ℂ) (f p.1) * g p.2) p

theorem integrable_pinnedTriangleKernel (f g : H) :
    Integrable (pinnedTriangleKernel f g)
      (unitIntervalMeasure.prod unitIntervalMeasure) := by
  exact ((integrable_conj_coe f).mul_prod (integrable_coe g)).indicator
    measurableSet_upperKernelSet

private theorem conj_pinnedPrefix_mul_eq_integral_triangle (f g : H) (t : ℝ) :
    (starRingEnd ℂ) (pinnedPrefix f t) * g t =
      ∫ u, pinnedTriangleKernel f g (u, t) ∂unitIntervalMeasure := by
  rw [pinnedPrefix, ← integral_conj, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [pinnedTriangleKernel, upperKernelSet, indicator_apply, mem_setOf_eq, mem_Iic]
  split_ifs <;> simp

private theorem conj_mul_pinnedUpperPrefix_eq_integral_triangle (f g : H) (u : ℝ) :
    (starRingEnd ℂ) (f u) * pinnedUpperPrefix g u =
      ∫ t, pinnedTriangleKernel f g (u, t) ∂unitIntervalMeasure := by
  rw [pinnedUpperPrefix, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [pinnedTriangleKernel, upperKernelSet, indicator_apply, mem_setOf_eq, mem_Ici]
  split_ifs <;> simp

theorem integral_conj_pinnedPrefix_mul_eq_integral_conj_mul_pinnedUpperPrefix
    (f g : H) :
    ∫ t, (starRingEnd ℂ) (pinnedPrefix f t) * g t ∂unitIntervalMeasure =
      ∫ u, (starRingEnd ℂ) (f u) * pinnedUpperPrefix g u ∂unitIntervalMeasure := by
  have htri := integrable_pinnedTriangleKernel f g
  calc
    (∫ t, (starRingEnd ℂ) (pinnedPrefix f t) * g t ∂unitIntervalMeasure)
        = ∫ t, ∫ u, pinnedTriangleKernel f g (u, t) ∂unitIntervalMeasure
            ∂unitIntervalMeasure := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall
                (conj_pinnedPrefix_mul_eq_integral_triangle f g)
    _ = ∫ u, ∫ t, pinnedTriangleKernel f g (u, t) ∂unitIntervalMeasure
            ∂unitIntervalMeasure := by
              exact (integral_integral_swap
                (f := fun u t => pinnedTriangleKernel f g (u, t)) htri).symm
    _ = ∫ u, (starRingEnd ℂ) (f u) * pinnedUpperPrefix g u
            ∂unitIntervalMeasure := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall
                (fun u => (conj_mul_pinnedUpperPrefix_eq_integral_triangle f g u).symm)

private theorem integral_conj_pinnedMean (f : H) :
    (starRingEnd ℂ) (pinnedMean f) =
      ∫ u, (starRingEnd ℂ) (f u) ∂unitIntervalMeasure := by
  rw [pinnedMean, ← integral_conj]

private theorem integral_boundary_rank_one (f g : H) :
    ∫ t, (starRingEnd ℂ) (((t : ℂ) * pinnedMean f)) * g t
        ∂unitIntervalMeasure =
      ∫ u, (starRingEnd ℂ) (f u) * pinnedFirstMoment g
        ∂unitIntervalMeasure := by
  calc
    (∫ t, (starRingEnd ℂ) (((t : ℂ) * pinnedMean f)) * g t
        ∂unitIntervalMeasure)
        = ∫ t, (starRingEnd ℂ) (pinnedMean f) * ((t : ℂ) * g t)
            ∂unitIntervalMeasure := by
              apply integral_congr_ae
              filter_upwards [] with t
              have htstar : (starRingEnd ℂ) (t : ℂ) = (t : ℂ) := by simp
              rw [map_mul, htstar]
              ring
    _ = (starRingEnd ℂ) (pinnedMean f) * pinnedFirstMoment g := by
          rw [pinnedFirstMoment, integral_const_mul]
    _ = (∫ u, (starRingEnd ℂ) (f u) ∂unitIntervalMeasure) *
          pinnedFirstMoment g := by rw [integral_conj_pinnedMean]
    _ = ∫ u, (starRingEnd ℂ) (f u) * pinnedFirstMoment g
          ∂unitIntervalMeasure := by rw [integral_mul_const]

private theorem integrable_conj_pinnedPrefix_mul (f g : H) :
    Integrable (fun t => (starRingEnd ℂ) (pinnedPrefix f t) * g t)
      unitIntervalMeasure := by
  exact (integrable_pinnedTriangleKernel f g).integral_prod_right.congr
    (Filter.Eventually.of_forall fun t =>
      (conj_pinnedPrefix_mul_eq_integral_triangle f g t).symm)

private theorem integrable_boundary_rank_one (f g : H) :
    Integrable (fun t : ℝ => (starRingEnd ℂ) (((t : ℂ) * pinnedMean f)) * g t)
      unitIntervalMeasure := by
  have hbase : Integrable
      (fun t : ℝ => (starRingEnd ℂ) (pinnedMean f) * ((t : ℂ) * g t))
      unitIntervalMeasure := (integrable_coordinate_mul g).const_mul _
  refine hbase.congr (Filter.Eventually.of_forall fun t => ?_)
  have htstar : (starRingEnd ℂ) (t : ℂ) = (t : ℂ) := by simp
  change (starRingEnd ℂ) (pinnedMean f) * ((t : ℂ) * g t) =
    (starRingEnd ℂ) ((t : ℂ) * pinnedMean f) * g t
  rw [map_mul, htstar]
  ring

/-- The reverse pinned primitive is the actual Hilbert adjoint of the forward primitive. -/
theorem inner_pinnedVolterra_eq_inner_pinnedVolterraAdjoint (f g : H) :
    inner ℂ (pinnedVolterra f) g = inner ℂ f (pinnedVolterraAdjoint g) := by
  rw [inner_lp_eq, inner_lp_eq]
  calc
    (∫ t, (starRingEnd ℂ) ((pinnedVolterra f) t) * g t
        ∂unitIntervalMeasure)
        = ∫ t, (starRingEnd ℂ) (pinnedVolterraFun f t) * g t
            ∂unitIntervalMeasure := by
              apply integral_congr_ae
              filter_upwards [pinnedVolterra_coeFn f] with t ht
              rw [ht]
    _ = ∫ t, ((starRingEnd ℂ) (pinnedPrefix f t) * g t -
          (starRingEnd ℂ) (((t : ℂ) * pinnedMean f)) * g t)
          ∂unitIntervalMeasure := by
            apply integral_congr_ae
            filter_upwards [] with t
            rw [pinnedVolterraFun, map_sub]
            ring
    _ = (∫ t, (starRingEnd ℂ) (pinnedPrefix f t) * g t
          ∂unitIntervalMeasure) -
        ∫ t, (starRingEnd ℂ) (((t : ℂ) * pinnedMean f)) * g t
          ∂unitIntervalMeasure := by
            rw [integral_sub (integrable_conj_pinnedPrefix_mul f g)
              (integrable_boundary_rank_one f g)]
    _ = (∫ u, (starRingEnd ℂ) (f u) * pinnedUpperPrefix g u
          ∂unitIntervalMeasure) -
        ∫ u, (starRingEnd ℂ) (f u) * pinnedFirstMoment g
          ∂unitIntervalMeasure := by
            rw [integral_conj_pinnedPrefix_mul_eq_integral_conj_mul_pinnedUpperPrefix,
              integral_boundary_rank_one]
    _ = ∫ u, (starRingEnd ℂ) (f u) *
          (pinnedUpperPrefix g u - pinnedFirstMoment g)
          ∂unitIntervalMeasure := by
            rw [← integral_sub]
            · apply integral_congr_ae
              filter_upwards [] with u
              ring
            · exact (integrable_pinnedTriangleKernel f g).integral_prod_left.congr
                (Filter.Eventually.of_forall fun u =>
                  (conj_mul_pinnedUpperPrefix_eq_integral_triangle f g u).symm)
            · exact (integrable_conj_coe f).mul_const _
    _ = ∫ u, (starRingEnd ℂ) (f u) * pinnedVolterraAdjointFun g u
          ∂unitIntervalMeasure := by rfl
    _ = ∫ u, (starRingEnd ℂ) (f u) * (pinnedVolterraAdjoint g) u
          ∂unitIntervalMeasure := by
            apply integral_congr_ae
            filter_upwards [pinnedVolterraAdjoint_coeFn g] with u hu
            rw [hu]

theorem pinnedVolterraAdjointCLM_eq_adjoint :
    pinnedVolterraAdjointCLM = pinnedVolterraCLM.adjoint := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (inner_pinnedVolterra_eq_inner_pinnedVolterraAdjoint f g).symm

theorem pinnedUpperPrefix_eq_intervalIntegral (f : H) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    pinnedUpperPrefix f t = ∫ u in t..1, f u := by
  rw [pinnedUpperPrefix, integral_indicator measurableSet_Ici]
  change (∫ u, f u ∂(volume.restrict (Icc (0 : ℝ) 1)).restrict (Ici t)) =
    ∫ u in t..1, f u
  rw [Measure.restrict_restrict measurableSet_Ici]
  have hset : Ici t ∩ Icc (0 : ℝ) 1 = Icc t 1 := by
    ext u
    simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨htu, -, hu1⟩
      exact ⟨htu, hu1⟩
    · rintro ⟨htu, hu1⟩
      exact ⟨htu, le_trans ht.1 htu, hu1⟩
  rw [hset, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le ht.2]

theorem pinnedPrefix_eq_intervalIntegral (f : H) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    pinnedPrefix f t = ∫ u in (0 : ℝ)..t, f u := by
  rw [pinnedPrefix, integral_indicator measurableSet_Iic]
  change (∫ u, f u ∂(volume.restrict (Icc (0 : ℝ) 1)).restrict (Iic t)) =
    ∫ u in (0 : ℝ)..t, f u
  rw [Measure.restrict_restrict measurableSet_Iic]
  have hset : Iic t ∩ Icc (0 : ℝ) 1 = Icc 0 t := by
    ext u
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨hut, hu0, -⟩
      exact ⟨hu0, hut⟩
    · rintro ⟨hu0, hut⟩
      exact ⟨hut, hu0, le_trans hut ht.2⟩
  rw [hset, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le ht.1]

set_option maxHeartbeats 1000000 in
/-- The reverse pinned primitive has trivial kernel on the full infinite-dimensional `L²` space. -/
theorem pinnedVolterraAdjointCLM_injective :
    Function.Injective pinnedVolterraAdjointCLM := by
  suffices hker : ∀ f : H, pinnedVolterraAdjointCLM f = 0 → f = 0 by
    intro f g hfg
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, hfg, sub_self]
  intro f hf
  have hzero : pinnedVolterraAdjoint f = 0 := by
    exact hf
  have hadjCoe :
      (fun t => (pinnedVolterraAdjoint f) t) =ᵐ[unitIntervalMeasure]
        fun _ : ℝ => (0 : ℂ) := by
    rw [hzero]
    simp
  have hadjFun : pinnedVolterraAdjointFun f =ᵐ[unitIntervalMeasure]
      fun _ : ℝ => (0 : ℂ) :=
    (pinnedVolterraAdjoint_coeFn f).symm.trans hadjCoe
  let F : ℝ → ℂ := fun t => (∫ u in t..1, f u) - pinnedFirstMoment f
  have hIntOn : IntegrableOn (fun t => f t) (Icc (0 : ℝ) 1) volume := by
    change Integrable (fun t => f t) (volume.restrict (Icc (0 : ℝ) 1))
    simpa only [unitIntervalMeasure] using integrable_coe f
  have hIntOnU : IntegrableOn (fun t => f t) (uIcc (0 : ℝ) 1) volume := by
    simpa only [uIcc_of_le zero_le_one] using hIntOn
  have hFcontinuous : ContinuousOn F (Icc (0 : ℝ) 1) := by
    have h := intervalIntegral.continuousOn_primitive_interval_left (μ := volume) hIntOnU
    rw [uIcc_of_le zero_le_one] at h
    change ContinuousOn
      (fun t => (∫ u in t..1, f u) - pinnedFirstMoment f) (Icc (0 : ℝ) 1)
    exact h.sub continuousOn_const
  have hFae : F =ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
      fun _ : ℝ => (0 : ℂ) := by
    rw [← unitIntervalMeasure]
    filter_upwards [hadjFun, ae_restrict_mem measurableSet_Icc] with t htzero ht
    rw [pinnedVolterraAdjointFun, pinnedUpperPrefix_eq_intervalIntegral f ht] at htzero
    exact htzero
  have hclosure : Icc (0 : ℝ) 1 ⊆ closure (interior (Icc (0 : ℝ) 1)) := by
    rw [interior_Icc, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  have hFzero : Set.EqOn F (fun _ : ℝ => (0 : ℂ)) (Icc (0 : ℝ) 1) :=
    (volume : Measure ℝ).eqOn_of_ae_eq hFae hFcontinuous continuousOn_const hclosure
  have hldt := hIntOnU.intervalIntegrable.ae_hasDerivAt_integral
  have hldtRestrict :
      ∀ᵐ x ∂unitIntervalMeasure,
        x ∈ uIcc (0 : ℝ) 1 → ∀ c ∈ uIcc (0 : ℝ) 1,
          HasDerivAt (fun y => ∫ t in c..y, f t) (f x) x := by
    change ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) 1),
      x ∈ uIcc (0 : ℝ) 1 → ∀ c ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun y => ∫ t in c..y, f t) (f x) x
    exact ae_restrict_of_ae hldt
  have hfzero : (fun t => f t) =ᵐ[unitIntervalMeasure]
      fun _ : ℝ => (0 : ℂ) := by
    filter_upwards [hldtRestrict, unitIntervalMeasure.ae_ne 0,
      unitIntervalMeasure.ae_ne 1, ae_restrict_mem measurableSet_Icc]
        with x hxderiv hx0 hx1 hx
    have hxoo : x ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩
    have hprimitive : HasDerivAt (fun y => ∫ t in (1 : ℝ)..y, f t) (f x) x := by
      exact hxderiv (by simpa only [uIcc_of_le zero_le_one] using hx) 1
        (by simp)
    have hFderiv : HasDerivAt F (-f x) x := by
      have hneg := hprimitive.neg.sub_const (pinnedFirstMoment f)
      change HasDerivAt
        (fun y => (∫ t in y..(1 : ℝ), f t) - pinnedFirstMoment f) (-f x) x
      apply hneg.congr_of_eventuallyEq
      filter_upwards [] with y
      change (∫ t in y..(1 : ℝ), f t) - pinnedFirstMoment f =
        -(∫ t in (1 : ℝ)..y, f t) - pinnedFirstMoment f
      rw [intervalIntegral.integral_symm]
    have hlocal : Filter.EventuallyEq (nhds x) F (fun _ : ℝ => (0 : ℂ)) := by
      filter_upwards [Ioo_mem_nhds hxoo.1 hxoo.2] with y hy
      exact hFzero (Ioo_subset_Icc_self hy)
    have hzeroDeriv : HasDerivAt F 0 x :=
      (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq hlocal
    have hnegzero : -f x = 0 := hFderiv.unique hzeroDeriv
    exact neg_eq_zero.mp hnegzero
  apply Lp.ext
  filter_upwards [hfzero,
    (Lp.coeFn_zero ℂ (2 : ENNReal) unitIntervalMeasure)] with t ht hzeroCoe
  exact ht.trans hzeroCoe.symm

theorem pinnedPrefix_add_pinnedUpperPrefix (f : H) (t : ℝ) :
    pinnedPrefix f t + pinnedUpperPrefix f t = pinnedMean f := by
  rw [pinnedPrefix, pinnedUpperPrefix, pinnedMean,
    ← integral_add ((integrable_coe f).indicator measurableSet_Iic)
      ((integrable_coe f).indicator measurableSet_Ici)]
  apply integral_congr_ae
  filter_upwards [unitIntervalMeasure.ae_ne t] with u hu
  rcases lt_or_gt_of_ne hu with hut | htu
  · simp [hut.le, not_le.mpr hut]
  · simp [htu.le, not_le.mpr htu]

def pinnedBoundaryFun (f : H) (t : ℝ) : ℂ :=
  (1 - t) * pinnedMean f - pinnedFirstMoment f

theorem pinnedVolterraFun_add_adjointFun (f : H) (t : ℝ) :
    pinnedVolterraFun f t + pinnedVolterraAdjointFun f t = pinnedBoundaryFun f t := by
  rw [pinnedVolterraFun, pinnedVolterraAdjointFun, pinnedBoundaryFun,
    ← pinnedPrefix_add_pinnedUpperPrefix]
  ring

/-- The universal boundary operator is the sum of the forward and reverse pinned primitives. -/
def pinnedBoundaryCLM : H →L[ℂ] H :=
  pinnedVolterraCLM + pinnedVolterraAdjointCLM

theorem pinnedBoundaryCLM_coeFn (f : H) :
    (fun t => (pinnedBoundaryCLM f) t) =ᵐ[unitIntervalMeasure] pinnedBoundaryFun f := by
  filter_upwards [Lp.coeFn_add (pinnedVolterra f) (pinnedVolterraAdjoint f),
    pinnedVolterra_coeFn f, pinnedVolterraAdjoint_coeFn f] with t hadd hf ha
  change ((pinnedVolterra f + pinnedVolterraAdjoint f : H) : ℝ → ℂ) t =
    pinnedBoundaryFun f t
  rw [hadd]
  simp only [Pi.add_apply, hf, ha]
  exact pinnedVolterraFun_add_adjointFun f t

/-- Exact infinite-dimensional adjoint defect: `C† + C` is the affine boundary operator. -/
theorem adjoint_add_pinnedVolterraCLM_eq_pinnedBoundaryCLM :
    pinnedVolterraCLM.adjoint + pinnedVolterraCLM = pinnedBoundaryCLM := by
  rw [← pinnedVolterraAdjointCLM_eq_adjoint]
  exact add_comm _ _

def pinnedOne : H :=
  Lp.const 2 unitIntervalMeasure (1 : ℂ)

theorem pinnedOne_coeFn :
    (fun t => pinnedOne t) =ᵐ[unitIntervalMeasure] fun _ : ℝ => (1 : ℂ) :=
  by
    simp [pinnedOne]

theorem memLp_coordinate :
    MemLp (fun t : ℝ => (t : ℂ)) 2 unitIntervalMeasure := by
  refine MemLp.of_bound Complex.continuous_ofReal.aestronglyMeasurable 1 ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2

def pinnedCoordinate : H :=
  memLp_coordinate.toLp (fun t : ℝ => (t : ℂ))

theorem pinnedCoordinate_coeFn :
    (fun t => pinnedCoordinate t) =ᵐ[unitIntervalMeasure] fun t : ℝ => (t : ℂ) :=
  MemLp.coeFn_toLp memLp_coordinate

def pinnedAffineSubspace : Submodule ℂ H :=
  Submodule.span ℂ ({pinnedOne, pinnedCoordinate} : Set H)

theorem pinnedOne_mem_affineSubspace : pinnedOne ∈ pinnedAffineSubspace := by
  exact Submodule.subset_span (by simp)

theorem pinnedCoordinate_mem_affineSubspace : pinnedCoordinate ∈ pinnedAffineSubspace := by
  exact Submodule.subset_span (by simp)

theorem pinnedBoundaryCLM_eq_affine_combination (f : H) :
    pinnedBoundaryCLM f =
      (pinnedMean f - pinnedFirstMoment f) • pinnedOne -
        pinnedMean f • pinnedCoordinate := by
  apply Lp.ext
  filter_upwards [pinnedBoundaryCLM_coeFn f, pinnedOne_coeFn,
    pinnedCoordinate_coeFn,
    Lp.coeFn_sub ((pinnedMean f - pinnedFirstMoment f) • pinnedOne)
      (pinnedMean f • pinnedCoordinate),
    Lp.coeFn_smul (pinnedMean f - pinnedFirstMoment f) pinnedOne,
    Lp.coeFn_smul (pinnedMean f) pinnedCoordinate]
      with t hboundary hone hcoord hsub honeSmul hcoordSmul
  rw [hboundary, hsub]
  change pinnedBoundaryFun f t =
    (((pinnedMean f - pinnedFirstMoment f) • pinnedOne : H) : ℝ → ℂ) t -
      ((pinnedMean f • pinnedCoordinate : H) : ℝ → ℂ) t
  rw [honeSmul, hcoordSmul]
  simp only [Pi.smul_apply, smul_eq_mul, hone, hcoord, pinnedBoundaryFun]
  ring

/-- The full boundary defect has range contained in the two-dimensional affine trace space. -/
theorem pinnedBoundaryCLM_mem_affineSubspace (f : H) :
    pinnedBoundaryCLM f ∈ pinnedAffineSubspace := by
  rw [pinnedBoundaryCLM_eq_affine_combination]
  exact Submodule.sub_mem _
    (Submodule.smul_mem _ _ pinnedOne_mem_affineSubspace)
    (Submodule.smul_mem _ _ pinnedCoordinate_mem_affineSubspace)

theorem range_pinnedBoundaryCLM_le_affineSubspace :
    LinearMap.range pinnedBoundaryCLM.toLinearMap ≤ pinnedAffineSubspace := by
  rintro _ ⟨f, rfl⟩
  exact pinnedBoundaryCLM_mem_affineSubspace f

theorem integral_unitInterval_one :
    ∫ _ : ℝ, (1 : ℂ) ∂unitIntervalMeasure = 1 := by
  simp [integral_const]

theorem integral_unitInterval_coordinate :
    ∫ t : ℝ, (t : ℂ) ∂unitIntervalMeasure = (1 : ℂ) / 2 := by
  rw [unitIntervalMeasure, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_ofReal, integral_id]
  norm_num

theorem integral_unitInterval_coordinate_sq :
    ∫ t : ℝ, (t : ℂ) * t ∂unitIntervalMeasure = (1 : ℂ) / 3 := by
  rw [unitIntervalMeasure]
  have hfun :
      (∫ t : ℝ, (t : ℂ) * t ∂volume.restrict (Icc 0 1)) =
        ∫ t : ℝ, ((t ^ 2 : ℝ) : ℂ) ∂volume.restrict (Icc 0 1) := by
    apply integral_congr_ae
    filter_upwards [] with t
    push_cast
    ring
  rw [hfun, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_ofReal, integral_pow]
  norm_num

@[simp] theorem pinnedMean_pinnedOne : pinnedMean pinnedOne = 1 := by
  rw [pinnedMean]
  calc
    (∫ t, pinnedOne t ∂unitIntervalMeasure) =
        ∫ _ : ℝ, (1 : ℂ) ∂unitIntervalMeasure := integral_congr_ae pinnedOne_coeFn
    _ = 1 := integral_unitInterval_one

@[simp] theorem pinnedFirstMoment_pinnedOne : pinnedFirstMoment pinnedOne = (1 : ℂ) / 2 := by
  rw [pinnedFirstMoment]
  calc
    (∫ t, (t : ℂ) * pinnedOne t ∂unitIntervalMeasure) =
        ∫ t : ℝ, (t : ℂ) ∂unitIntervalMeasure := by
          apply integral_congr_ae
          filter_upwards [pinnedOne_coeFn] with t ht
          rw [ht, mul_one]
    _ = (1 : ℂ) / 2 := integral_unitInterval_coordinate

@[simp] theorem pinnedMean_pinnedCoordinate :
    pinnedMean pinnedCoordinate = (1 : ℂ) / 2 := by
  rw [pinnedMean]
  calc
    (∫ t, pinnedCoordinate t ∂unitIntervalMeasure) =
        ∫ t : ℝ, (t : ℂ) ∂unitIntervalMeasure :=
          integral_congr_ae pinnedCoordinate_coeFn
    _ = (1 : ℂ) / 2 := integral_unitInterval_coordinate

@[simp] theorem pinnedFirstMoment_pinnedCoordinate :
    pinnedFirstMoment pinnedCoordinate = (1 : ℂ) / 3 := by
  rw [pinnedFirstMoment]
  calc
    (∫ t, (t : ℂ) * pinnedCoordinate t ∂unitIntervalMeasure) =
        ∫ t : ℝ, (t : ℂ) * t ∂unitIntervalMeasure := by
          apply integral_congr_ae
          filter_upwards [pinnedCoordinate_coeFn] with t ht
          rw [ht]
    _ = (1 : ℂ) / 3 := integral_unitInterval_coordinate_sq

theorem pinnedBoundaryCLM_pinnedOne :
    pinnedBoundaryCLM pinnedOne = (1 / 2 : ℂ) • pinnedOne - pinnedCoordinate := by
  rw [pinnedBoundaryCLM_eq_affine_combination]
  simp only [pinnedMean_pinnedOne, pinnedFirstMoment_pinnedOne, one_smul]
  norm_num

theorem pinnedBoundaryCLM_pinnedCoordinate :
    pinnedBoundaryCLM pinnedCoordinate =
      (1 / 6 : ℂ) • pinnedOne - (1 / 2 : ℂ) • pinnedCoordinate := by
  rw [pinnedBoundaryCLM_eq_affine_combination]
  simp only [pinnedMean_pinnedCoordinate, pinnedFirstMoment_pinnedCoordinate]
  norm_num

theorem inner_pinnedOne_pinnedOne :
    inner ℂ pinnedOne pinnedOne = 1 := by
  rw [inner_lp_eq]
  calc
    (∫ t, (starRingEnd ℂ) (pinnedOne t) * pinnedOne t
        ∂unitIntervalMeasure) =
        ∫ _ : ℝ, (1 : ℂ) ∂unitIntervalMeasure := by
          apply integral_congr_ae
          filter_upwards [pinnedOne_coeFn] with t ht
          rw [ht]
          simp
    _ = 1 := integral_unitInterval_one

theorem inner_pinnedOne_pinnedCoordinate :
    inner ℂ pinnedOne pinnedCoordinate = (1 : ℂ) / 2 := by
  rw [inner_lp_eq]
  calc
    (∫ t, (starRingEnd ℂ) (pinnedOne t) * pinnedCoordinate t
        ∂unitIntervalMeasure) =
        ∫ t : ℝ, (t : ℂ) ∂unitIntervalMeasure := by
          apply integral_congr_ae
          filter_upwards [pinnedOne_coeFn, pinnedCoordinate_coeFn] with t hone hcoord
          rw [hone, hcoord]
          simp
    _ = (1 : ℂ) / 2 := integral_unitInterval_coordinate

theorem inner_pinnedCoordinate_pinnedOne :
    inner ℂ pinnedCoordinate pinnedOne = (1 : ℂ) / 2 := by
  rw [inner_lp_eq]
  calc
    (∫ t, (starRingEnd ℂ) (pinnedCoordinate t) * pinnedOne t
        ∂unitIntervalMeasure) =
        ∫ t : ℝ, (t : ℂ) ∂unitIntervalMeasure := by
          apply integral_congr_ae
          filter_upwards [pinnedOne_coeFn, pinnedCoordinate_coeFn] with t hone hcoord
          rw [hone, hcoord]
          simp
    _ = (1 : ℂ) / 2 := integral_unitInterval_coordinate

theorem inner_pinnedCoordinate_pinnedCoordinate :
    inner ℂ pinnedCoordinate pinnedCoordinate = (1 : ℂ) / 3 := by
  rw [inner_lp_eq]
  calc
    (∫ t, (starRingEnd ℂ) (pinnedCoordinate t) * pinnedCoordinate t
        ∂unitIntervalMeasure) =
        ∫ t : ℝ, (t : ℂ) * t ∂unitIntervalMeasure := by
          apply integral_congr_ae
          filter_upwards [pinnedCoordinate_coeFn] with t hcoord
          rw [hcoord]
          simp
    _ = (1 : ℂ) / 3 := integral_unitInterval_coordinate_sq

theorem pinnedOne_coordinate_linearIndependent :
    LinearIndependent ℂ ![pinnedOne, pinnedCoordinate] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have hone := congrArg (fun f : H => inner ℂ pinnedOne f) hab
  have hcoord := congrArg (fun f : H => inner ℂ pinnedCoordinate f) hab
  simp only [inner_add_right, inner_smul_right, inner_zero_right,
    inner_pinnedOne_pinnedOne, inner_pinnedOne_pinnedCoordinate,
    inner_pinnedCoordinate_pinnedOne, inner_pinnedCoordinate_pinnedCoordinate] at hone hcoord
  constructor
  · linear_combination 4 * hone - 6 * hcoord
  · linear_combination -6 * hone + 12 * hcoord

def pinnedCenter : H :=
  pinnedCoordinate - (1 / 2 : ℂ) • pinnedOne

def pinnedPositiveMode : H :=
  pinnedOne - pinnedCenter

def pinnedNegativeMode : H :=
  pinnedOne + pinnedCenter

theorem pinnedBoundaryCLM_pinnedCenter :
    pinnedBoundaryCLM pinnedCenter = -(1 / 12 : ℂ) • pinnedOne := by
  rw [pinnedCenter, map_sub, map_smul, pinnedBoundaryCLM_pinnedOne,
    pinnedBoundaryCLM_pinnedCoordinate]
  module

theorem pinnedBoundaryCLM_pinnedOne_eq_neg_center :
    pinnedBoundaryCLM pinnedOne = -pinnedCenter := by
  rw [pinnedBoundaryCLM_pinnedOne, pinnedCenter]
  module

theorem pinnedBoundaryCLM_pinnedPositiveMode :
    pinnedBoundaryCLM pinnedPositiveMode =
      (1 / 12 : ℂ) • pinnedOne - pinnedCenter := by
  rw [pinnedPositiveMode, map_sub, pinnedBoundaryCLM_pinnedOne_eq_neg_center,
    pinnedBoundaryCLM_pinnedCenter]
  module

theorem pinnedBoundaryCLM_pinnedNegativeMode :
    pinnedBoundaryCLM pinnedNegativeMode =
      -(1 / 12 : ℂ) • pinnedOne - pinnedCenter := by
  rw [pinnedNegativeMode, map_add, pinnedBoundaryCLM_pinnedOne_eq_neg_center,
    pinnedBoundaryCLM_pinnedCenter]
  module

private theorem star_one_div_nat (n : ℕ) :
    (starRingEnd ℂ) ((1 : ℂ) / n) = (1 : ℂ) / n := by
  rw [map_div₀, map_one, map_natCast]

private theorem star_neg_one_div_nat (n : ℕ) :
    (starRingEnd ℂ) (-((1 : ℂ) / n)) = -((1 : ℂ) / n) := by
  rw [map_neg, star_one_div_nat]

private theorem star_one_div_two :
    (starRingEnd ℂ) ((1 : ℂ) / 2) = (1 : ℂ) / 2 := by
  rw [map_div₀, map_one, map_ofNat (starRingEnd ℂ) 2]

private theorem star_one_div_twelve :
    (starRingEnd ℂ) ((1 : ℂ) / 12) = (1 : ℂ) / 12 := by
  rw [map_div₀, map_one, map_ofNat (starRingEnd ℂ) 12]

private theorem star_neg_one_div_twelve :
    (starRingEnd ℂ) (-((1 : ℂ) / 12)) = -((1 : ℂ) / 12) := by
  rw [map_neg, star_one_div_twelve]

theorem inner_pinnedOne_pinnedCenter :
    inner ℂ pinnedOne pinnedCenter = 0 := by
  simp only [pinnedCenter, inner_sub_right, inner_smul_right,
    inner_pinnedOne_pinnedCoordinate, inner_pinnedOne_pinnedOne]
  norm_num [div_eq_mul_inv]

theorem inner_pinnedCoordinate_pinnedCenter :
    inner ℂ pinnedCoordinate pinnedCenter = (1 : ℂ) / 12 := by
  simp only [pinnedCenter, inner_sub_right, inner_smul_right,
    inner_pinnedCoordinate_pinnedCoordinate, inner_pinnedCoordinate_pinnedOne]
  norm_num [div_eq_mul_inv]

theorem inner_pinnedCenter_pinnedOne :
    inner ℂ pinnedCenter pinnedOne = 0 := by
  simp only [pinnedCenter, inner_sub_left, inner_smul_left,
    inner_pinnedCoordinate_pinnedOne, inner_pinnedOne_pinnedOne]
  rw [star_one_div_two]
  norm_num [div_eq_mul_inv]

theorem inner_pinnedCenter_pinnedCenter :
    inner ℂ pinnedCenter pinnedCenter = (1 : ℂ) / 12 := by
  simp only [pinnedCenter, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, inner_pinnedCoordinate_pinnedCoordinate,
    inner_pinnedCoordinate_pinnedOne, inner_pinnedOne_pinnedCoordinate,
    inner_pinnedOne_pinnedOne]
  rw [star_one_div_two]
  norm_num [div_eq_mul_inv]

theorem inner_pinnedBoundaryCLM_pinnedPositiveMode :
    inner ℂ (pinnedBoundaryCLM pinnedPositiveMode) pinnedPositiveMode =
      (1 : ℂ) / 6 := by
  rw [pinnedBoundaryCLM_pinnedPositiveMode]
  simp only [pinnedPositiveMode, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_pinnedOne_pinnedOne, inner_pinnedOne_pinnedCenter,
    inner_pinnedCenter_pinnedOne, inner_pinnedCenter_pinnedCenter]
  rw [star_one_div_twelve]
  norm_num [div_eq_mul_inv]

theorem inner_pinnedBoundaryCLM_pinnedNegativeMode :
    inner ℂ (pinnedBoundaryCLM pinnedNegativeMode) pinnedNegativeMode =
      -(1 : ℂ) / 6 := by
  rw [pinnedBoundaryCLM_pinnedNegativeMode]
  simp only [pinnedNegativeMode, inner_sub_left, inner_add_right, inner_smul_left,
    inner_pinnedOne_pinnedOne, inner_pinnedOne_pinnedCenter,
    inner_pinnedCenter_pinnedOne, inner_pinnedCenter_pinnedCenter]
  rw [star_neg_one_div_twelve]
  norm_num [div_eq_mul_inv]

theorem pinnedVolterraCLM_pinnedOne :
    pinnedVolterraCLM pinnedOne = 0 := by
  have honeRestrict :
      (fun t => pinnedOne t) =ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
        fun _ : ℝ => (1 : ℂ) := by
    simpa only [unitIntervalMeasure] using pinnedOne_coeFn
  have honeVolume :
      ∀ᵐ t ∂volume, t ∈ Icc (0 : ℝ) 1 → pinnedOne t = (1 : ℂ) :=
    ae_imp_of_ae_restrict honeRestrict
  change pinnedVolterra pinnedOne = 0
  apply Lp.ext
  filter_upwards [pinnedVolterra_coeFn pinnedOne,
    ae_restrict_mem measurableSet_Icc] with t hcoe ht
  rw [hcoe, pinnedVolterraFun, pinnedPrefix_eq_intervalIntegral pinnedOne ht,
    pinnedMean_pinnedOne]
  have hinterval : (∫ u in (0 : ℝ)..t, pinnedOne u) = (t : ℂ) := by
    calc
      (∫ u in (0 : ℝ)..t, pinnedOne u) =
          ∫ _u in (0 : ℝ)..t, (1 : ℂ) := by
            apply intervalIntegral.integral_congr_ae
            filter_upwards [honeVolume] with u hu huInterval
            apply hu
            rw [uIoc_of_le ht.1] at huInterval
            exact ⟨huInterval.1.le, le_trans huInterval.2 ht.2⟩
      _ = (t : ℂ) := by simp
  rw [hinterval]
  simp

theorem pinnedOne_ne_zero : pinnedOne ≠ 0 := by
  intro hone
  have h := congrArg (fun f : H => inner ℂ pinnedOne f) hone
  rw [inner_pinnedOne_pinnedOne, inner_zero_right] at h
  exact one_ne_zero h

/-- Any bounded operator anticommuting with the forward/reverse pinned primitives kills the
constant mode.  Hence no injective bounded composite metric can satisfy this symmetry equation. -/
theorem anticommutator_eq_zero_imp_apply_pinnedOne_eq_zero
    (A : H →L[ℂ] H)
    (hanti : pinnedVolterraAdjointCLM.comp A + A.comp pinnedVolterraCLM = 0) :
    A pinnedOne = 0 := by
  have happ := congrArg (fun T : H →L[ℂ] H => T pinnedOne) hanti
  have hadj : pinnedVolterraAdjointCLM (A pinnedOne) = 0 := by
    simpa only [add_apply, ContinuousLinearMap.comp_apply,
      pinnedVolterraCLM_pinnedOne, map_zero, add_zero,
      zero_apply] using happ
  exact pinnedVolterraAdjointCLM_injective (by simpa using hadj)

/-- A coordinate-free bounded pointwise multiplier on the pinned `L²` space.  Its coefficient is
its value on the constant function, so the definition does not choose an `L∞` representative. -/
def IsPinnedPointwiseMultiplier (A : H →L[ℂ] H) : Prop :=
  ∀ f : H, (fun t => (A f) t) =ᵐ[unitIntervalMeasure]
    fun t => (A pinnedOne) t * f t

theorem eq_zero_of_isPinnedPointwiseMultiplier_of_apply_pinnedOne_eq_zero
    (A : H →L[ℂ] H) (hlocal : IsPinnedPointwiseMultiplier A)
    (hone : A pinnedOne = 0) : A = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  have honeAE : (fun t => (A pinnedOne) t) =ᵐ[unitIntervalMeasure] 0 :=
    Lp.eq_zero_iff_ae_eq_zero.mp hone
  apply Lp.ext
  filter_upwards [hlocal f, honeAE] with t hAf hAone
  rw [hAf, hAone]
  simp

/-- Exact bounded local-metric rigidity: a pointwise multiplication operator satisfying the
pinned-Volterra anticommutator equation is the zero operator. -/
theorem pointwiseMultiplier_anticommutator_eq_zero_imp_eq_zero
    (A : H →L[ℂ] H) (hlocal : IsPinnedPointwiseMultiplier A)
    (hanti : pinnedVolterraAdjointCLM.comp A + A.comp pinnedVolterraCLM = 0) :
    A = 0 := by
  apply eq_zero_of_isPinnedPointwiseMultiplier_of_apply_pinnedOne_eq_zero A hlocal
  exact anticommutator_eq_zero_imp_apply_pinnedOne_eq_zero A hanti

theorem no_injective_pinnedVolterra_anticommutator
    (A : H →L[ℂ] H) (hA : Function.Injective A) :
    pinnedVolterraAdjointCLM.comp A + A.comp pinnedVolterraCLM ≠ 0 := by
  intro hanti
  have hAone := anticommutator_eq_zero_imp_apply_pinnedOne_eq_zero A hanti
  apply pinnedOne_ne_zero
  apply hA
  simpa using hAone

theorem pinnedOne_mem_range_pinnedBoundaryCLM :
    pinnedOne ∈ LinearMap.range pinnedBoundaryCLM.toLinearMap := by
  let f : H := (6 : ℂ) • pinnedOne - (12 : ℂ) • pinnedCoordinate
  refine ⟨f, ?_⟩
  change pinnedBoundaryCLM f = pinnedOne
  rw [map_sub, map_smul, map_smul, pinnedBoundaryCLM_pinnedOne,
    pinnedBoundaryCLM_pinnedCoordinate]
  module

theorem pinnedCoordinate_mem_range_pinnedBoundaryCLM :
    pinnedCoordinate ∈ LinearMap.range pinnedBoundaryCLM.toLinearMap := by
  let f : H := (2 : ℂ) • pinnedOne - (6 : ℂ) • pinnedCoordinate
  refine ⟨f, ?_⟩
  change pinnedBoundaryCLM f = pinnedCoordinate
  rw [map_sub, map_smul, map_smul, pinnedBoundaryCLM_pinnedOne,
    pinnedBoundaryCLM_pinnedCoordinate]
  module

theorem affineSubspace_le_range_pinnedBoundaryCLM :
    pinnedAffineSubspace ≤ LinearMap.range pinnedBoundaryCLM.toLinearMap := by
  apply Submodule.span_le.2
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact pinnedOne_mem_range_pinnedBoundaryCLM
  · exact pinnedCoordinate_mem_range_pinnedBoundaryCLM

/-- The universal pinned-Volterra adjoint defect has exactly the affine two-channel range. -/
theorem range_pinnedBoundaryCLM_eq_affineSubspace :
    LinearMap.range pinnedBoundaryCLM.toLinearMap = pinnedAffineSubspace :=
  le_antisymm range_pinnedBoundaryCLM_le_affineSubspace
    affineSubspace_le_range_pinnedBoundaryCLM

theorem pinnedBoundaryCLM_adjoint_eq :
    pinnedBoundaryCLM.adjoint = pinnedBoundaryCLM := by
  have hadjAdj : pinnedVolterraAdjointCLM.adjoint = pinnedVolterraCLM := by
    rw [pinnedVolterraAdjointCLM_eq_adjoint,
      ContinuousLinearMap.adjoint_adjoint]
  calc
    pinnedBoundaryCLM.adjoint =
        pinnedVolterraCLM.adjoint + pinnedVolterraAdjointCLM.adjoint := by
          rw [pinnedBoundaryCLM, ContinuousLinearMap.adjoint.map_add]
    _ = pinnedVolterraAdjointCLM + pinnedVolterraCLM := by
          exact congrArg₂ (fun S T : H →L[ℂ] H => S + T)
            pinnedVolterraAdjointCLM_eq_adjoint.symm hadjAdj
    _ = pinnedBoundaryCLM := by rw [pinnedBoundaryCLM, add_comm]

theorem finrank_pinnedAffineSubspace :
    Module.finrank ℂ pinnedAffineSubspace = 2 := by
  have h := finrank_span_eq_card pinnedOne_coordinate_linearIndependent
  have hrange : Set.range ![pinnedOne, pinnedCoordinate] =
      ({pinnedOne, pinnedCoordinate} : Set H) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rw [pinnedAffineSubspace, ← hrange]
  simpa using h

theorem finrank_range_pinnedBoundaryCLM :
    Module.finrank ℂ (LinearMap.range pinnedBoundaryCLM.toLinearMap) = 2 := by
  rw [range_pinnedBoundaryCLM_eq_affineSubspace, finrank_pinnedAffineSubspace]

/-- Exact infinite-dimensional boundary-defect certificate: self-adjoint, rank two, and carrying
one explicit positive and one explicit negative mode. -/
theorem pinnedBoundaryCLM_exact_rankTwo_mixed_inertia :
    pinnedBoundaryCLM.adjoint = pinnedBoundaryCLM ∧
      Module.finrank ℂ (LinearMap.range pinnedBoundaryCLM.toLinearMap) = 2 ∧
      inner ℂ (pinnedBoundaryCLM pinnedPositiveMode) pinnedPositiveMode = (1 : ℂ) / 6 ∧
      inner ℂ (pinnedBoundaryCLM pinnedNegativeMode) pinnedNegativeMode = -(1 : ℂ) / 6 := by
  exact ⟨pinnedBoundaryCLM_adjoint_eq, finrank_range_pinnedBoundaryCLM,
    inner_pinnedBoundaryCLM_pinnedPositiveMode,
    inner_pinnedBoundaryCLM_pinnedNegativeMode⟩

end

end RHTower

