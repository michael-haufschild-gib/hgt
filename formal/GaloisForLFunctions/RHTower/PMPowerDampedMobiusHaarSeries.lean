import GaloisForLFunctions.RHTower.PMPowerDampedMobiusHaarGram
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace RHTower

def pmHaarDilationVector (a : ℝ) (ha : 0 < a) : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (memLp_pmSupportedDyadicHaar_dilation ha).toLp (fun t => pmSupportedDyadicHaar (a * t))

theorem pmHaarDilationVector_norm_sq (a : ℝ) (ha : 0 < a) :
    ‖pmHaarDilationVector a ha‖ ^ (2 : ℕ) = 1 / a := by
  rw [← pmSupportedDyadicHaar_dilation_energy ha,
    pm_integral_norm_sq_toLp (memLp_pmSupportedDyadicHaar_dilation ha)]
  rfl

theorem pmHaarDilationVector_norm (a : ℝ) (ha : 0 < a) :
    ‖pmHaarDilationVector a ha‖ = Real.sqrt (1 / a) := by
  have h := pmHaarDilationVector_norm_sq a ha
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 1 / a)
  have hn := norm_nonneg (pmHaarDilationVector a ha)
  have hp := Real.sqrt_nonneg (1 / a)
  nlinarith

theorem pmHaarDilationVector_norm_rpow (a : ℝ) (ha : 0 < a) :
    ‖pmHaarDilationVector a ha‖ = a ^ (-(1 / 2 : ℝ)) := by
  rw [pmHaarDilationVector_norm, Real.sqrt_eq_rpow, one_div, Real.inv_rpow ha.le, Real.rpow_neg ha.le]

def pmHaarDilationSeries {ι : Type*} (a : ι → ℝ) (t : ℝ) : ℂ :=
  ∑' i : ι, pmSupportedDyadicHaar (a i * t)

theorem summable_pmHaarDilationVector {ι : Type*} {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    (hs : Summable (fun i => Real.sqrt (1 / a i))) :
    Summable (fun i => pmHaarDilationVector (a i) (ha i)) := by
  apply Summable.of_norm
  simpa only [pmHaarDilationVector_norm] using hs

theorem pmHaarDilationVector_tsum_coe {ι : Type*} [Countable ι] {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) (hs : Summable (fun i => Real.sqrt (1 / a i))) :
    (fun t => (∑' i, pmHaarDilationVector (a i) (ha i)) t) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      pmHaarDilationSeries a := by
  have hn : Summable (fun i => ‖pmHaarDilationVector (a i) (ha i)‖) := by
    simpa only [pmHaarDilationVector_norm] using hs
  have hcoe := Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hn)
  have hterm : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), ∀ i,
      pmHaarDilationVector (a i) (ha i) t = pmSupportedDyadicHaar (a i * t) :=
    ae_all_iff.mpr (fun i => (memLp_pmSupportedDyadicHaar_dilation (ha i)).coeFn_toLp)
  filter_upwards [hcoe, hterm] with t ht hv
  exact ht.trans (tsum_congr hv)

theorem memLp_pmHaarDilationSeries {ι : Type*} [Countable ι] {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) (hs : Summable (fun i => Real.sqrt (1 / a i))) :
    MemLp (pmHaarDilationSeries a) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  exact (memLp_congr_ae (pmHaarDilationVector_tsum_coe ha hs)).mp (Lp.memLp _)

theorem pmHaarDilationSeries_energy {ι : Type*} [Countable ι] {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) (hs : Summable (fun i => Real.sqrt (1 / a i))) :
    (∫ t in Ioi (0 : ℝ), ‖pmHaarDilationSeries a t‖ ^ (2 : ℕ)) =
      ‖∑' i, pmHaarDilationVector (a i) (ha i)‖ ^ (2 : ℕ) := by
  have hf := memLp_pmHaarDilationSeries ha hs
  have hv : hf.toLp (pmHaarDilationSeries a) = ∑' i, pmHaarDilationVector (a i) (ha i) :=
    Lp.ext (hf.coeFn_toLp.trans (pmHaarDilationVector_tsum_coe ha hs).symm)
  rw [pm_integral_norm_sq_toLp hf, hv]

theorem pmHaarDilationVector_sum_coe {ι : Type*} [Countable ι] (S : Finset ι)
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    (fun t => (∑ i ∈ S, pmHaarDilationVector (a i) (ha i)) t) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      pmHaarDilationSum S a := by
  have hterm : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), ∀ i,
      pmHaarDilationVector (a i) (ha i) t = pmSupportedDyadicHaar (a i * t) :=
    ae_all_iff.mpr (fun i => (memLp_pmSupportedDyadicHaar_dilation (ha i)).coeFn_toLp)
  filter_upwards [Lp.coeFn_fun_finsetSum S (fun i => pmHaarDilationVector (a i) (ha i)), hterm] with t ht hv
  rw [ht]
  exact Finset.sum_congr rfl (fun i _ => hv i)

theorem pmHaarDilationVector_sum_norm_sq {ι : Type*} [Countable ι] (S : Finset ι)
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    ‖∑ i ∈ S, pmHaarDilationVector (a i) (ha i)‖ ^ (2 : ℕ) =
      (∫ t in Ioi (0 : ℝ), ‖pmHaarDilationSum S a t‖ ^ (2 : ℕ)) := by
  have hf := memLp_pmHaarDilationSum S a (fun i _ => ha i)
  have hv : hf.toLp (pmHaarDilationSum S a) = ∑ i ∈ S, pmHaarDilationVector (a i) (ha i) :=
    Lp.ext (hf.coeFn_toLp.trans (pmHaarDilationVector_sum_coe S ha).symm)
  rw [pm_integral_norm_sq_toLp hf, hv]

theorem pmHaarDilationSum_energy_le_series {ι : Type*} [Countable ι] (S : Finset ι)
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) (hs : Summable (fun i => Real.sqrt (1 / a i))) :
    (∫ t in Ioi (0 : ℝ), ‖pmHaarDilationSum S a t‖ ^ (2 : ℕ)) ≤
      (∫ t in Ioi (0 : ℝ), ‖pmHaarDilationSeries a t‖ ^ (2 : ℕ)) := by
  classical
  rw [pmHaarDilationSeries_energy ha hs]
  have hlim : Tendsto (fun T : Finset ι => ‖∑ i ∈ T, pmHaarDilationVector (a i) (ha i)‖ ^ (2 : ℕ))
      atTop (𝓝 (‖∑' i, pmHaarDilationVector (a i) (ha i)‖ ^ (2 : ℕ))) :=
    (summable_pmHaarDilationVector ha hs).hasSum.norm.pow 2
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [eventually_ge_atTop S] with T hT
  rw [pmHaarDilationVector_sum_norm_sq T ha]
  exact pmHaarDilationSum_energy_mono hT a (fun i _ => ha i)

theorem pmHaarDilationSeries_diagonal_le_energy {ι : Type*} [Countable ι] (S : Finset ι)
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) (hs : Summable (fun i => Real.sqrt (1 / a i))) :
    (∑ i ∈ S, 1 / a i) ≤ (∫ t in Ioi (0 : ℝ), ‖pmHaarDilationSeries a t‖ ^ (2 : ℕ)) :=
  (pmHaarDilationSum_diagonal_le_energy S a (fun i _ => ha i)).trans
    (pmHaarDilationSum_energy_le_series S ha hs)

theorem pmHaarDilationVector_inner (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    inner ℂ (pmHaarDilationVector a ha) (pmHaarDilationVector b hb) = (pmHaarDilationGram a b : ℂ) := by
  rw [L2.inner_def]
  have hpoint (t : ℝ) :
      inner ℂ (pmSupportedDyadicHaar (a * t)) (pmSupportedDyadicHaar (b * t)) =
        (((pmSupportedDyadicHaar (a * t)).re * (pmSupportedDyadicHaar (b * t)).re : ℝ) : ℂ) := by
    rw [RCLike.inner_apply]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, pmSupportedDyadicHaar_im, mul_comm]
  calc
    _ = ∫ t in Ioi (0 : ℝ), inner ℂ (pmSupportedDyadicHaar (a * t))
        (pmSupportedDyadicHaar (b * t)) := by
      apply integral_congr_ae
      filter_upwards [(memLp_pmSupportedDyadicHaar_dilation ha).coeFn_toLp,
        (memLp_pmSupportedDyadicHaar_dilation hb).coeFn_toLp] with t ht hu
      exact congrArg₂ (inner ℂ) ht hu
    _ = _ := by simp_rw [hpoint]; exact integral_complex_ofReal

theorem pmHaarDilationVector_inner_tsum_re {ι : Type*} {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) (hs : Summable (fun i => Real.sqrt (1 / a i))) (i : ι) :
    (inner ℂ (pmHaarDilationVector (a i) (ha i))
      (∑' j, pmHaarDilationVector (a j) (ha j))).re = ∑' j, pmHaarDilationGram (a i) (a j) := by
  let L := Complex.reCLM.comp ((innerSL ℂ (pmHaarDilationVector (a i) (ha i))).restrictScalars ℝ)
  have h := L.map_tsum (summable_pmHaarDilationVector ha hs)
  change (inner ℂ (pmHaarDilationVector (a i) (ha i))
    (∑' j, pmHaarDilationVector (a j) (ha j))).re =
      ∑' j, (inner ℂ (pmHaarDilationVector (a i) (ha i))
        (pmHaarDilationVector (a j) (ha j))).re at h
  simpa only [pmHaarDilationVector_inner, Complex.ofReal_re] using h

theorem pmHaarDilationSeries_energy_eq_tsum_gram {ι : Type*} [Countable ι] {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) (hs : Summable (fun i => Real.sqrt (1 / a i))) :
    (∫ t in Ioi (0 : ℝ), ‖pmHaarDilationSeries a t‖ ^ (2 : ℕ)) =
      ∑' i, ∑' j, pmHaarDilationGram (a i) (a j) := by
  rw [pmHaarDilationSeries_energy ha hs, @norm_sq_eq_re_inner ℂ]
  let v := ∑' j, pmHaarDilationVector (a j) (ha j)
  let L := Complex.reCLM.comp ((innerSL ℂ v).restrictScalars ℝ)
  have h : (inner ℂ v v).re = ∑' i, (inner ℂ v (pmHaarDilationVector (a i) (ha i))).re := by
    exact L.map_tsum (summable_pmHaarDilationVector ha hs)
  change (inner ℂ v v).re = _
  rw [h]
  apply tsum_congr
  intro i
  rw [show (inner ℂ v (pmHaarDilationVector (a i) (ha i))).re =
    (inner ℂ (pmHaarDilationVector (a i) (ha i)) v).re from inner_re_symm (𝕜 := ℂ) _ _]
  exact pmHaarDilationVector_inner_tsum_re ha hs i

end RHTower
