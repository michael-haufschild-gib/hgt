import GaloisForLFunctions.RHTower.WeilWorkQuantizationRadialTheta
import GaloisForLFunctions.RHTower.WeilConeAlmostPeriodicSettledLock

/-!
# Arithmetic residues of the actual reflected radial trace

The two source Hamburger identities identify the reflected transform. Integer
arithmetic support repeats its residue at each positive integer; the residue
is carried by the lower spectral half-line. No reflection lock is assumed.
-/

open Complex Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RHTower.WeilSpectral
open HamburgerStability HamburgerTwisted PhaseLockRigidity IntegerMassRigidity
  GaloisForLFunctions.HTGeometry

/-- Both actual Hamburger identities determine the reflected transform. -/
theorem quantization_reflected_defectLaplace_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {τ : ℂ} (hτ : 0 < τ.re) :
    defectLaplace (fun t => quantizationReflectedTraceF hW (2 * t)) τ =
      (∑' n : ℕ, dirichletExp (lamLog lam) (n + 1) *
        cexp (-(2 * Real.pi * ((n : ℂ) + 1) * τ))) -
      betaG (quantizationCompletion hW) / (Real.pi * τ) := by
  obtain ⟨C, _, hB⟩ := exists_quantization_trace_pair_bound hW
  have eA := quantization_hamburgerSeries_reflection hW hτ
  have eB := quantization_hamburgerSeries_eq hW hτ
  have hΨm : AEStronglyMeasurable (fun t => quantizationReflectedTraceF hW (2 * t)) volume :=
    ((measurable_quantizationReflectedTraceF hW).comp (measurable_const.mul measurable_id)).aestronglyMeasurable
  have hΦm : AEStronglyMeasurable (fun t => quantizationTraceF hW (2 * t)) volume :=
    ((measurable_quantizationTraceF hW).comp (measurable_const.mul measurable_id)).aestronglyMeasurable
  have eC := defectLaplace_indicator_eq
    (g := fun t => quantizationTraceF hW (2 * t) - quantizationReflectedTraceF hW (2 * t))
    hΨm
    (fun t => (hB t).2)
    hΦm
    (fun t => (hB t).1) MeasurableSet.univ (-1) (fun t _ => by ring) hτ
  simp only [indicator_univ] at eC
  linear_combination eA - eB + eC

/-- Integer arithmetic support repeats the reflected residue at every positive integer. -/
theorem tendsto_quantization_reflected_radial {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * defectLaplace
      (fun t => quantizationReflectedTraceF hW (2 * t)) ((ε : ℂ) + (m : ℂ) * I))
      (𝓝[>] 0) (𝓝 (betaG (quantizationCompletion hW) / Real.pi)) := by
  let Ψ : ℝ → ℂ := fun t => quantizationReflectedTraceF hW (2 * t)
  let β := betaG (quantizationCompletion hW)
  let S : ℂ → ℂ := fun τ => ∑' n : ℕ, dirichletExp (lamLog lam) (n + 1) *
    cexp (-(2 * Real.pi * ((n : ℂ) + 1) * τ))
  obtain ⟨C, _, hB⟩ := exists_quantization_trace_pair_bound hW
  have hΨm : AEStronglyMeasurable Ψ volume :=
    ((measurable_quantizationReflectedTraceF hW).comp (measurable_const.mul measurable_id)).aestronglyMeasurable
  have hzero := tendsto_mul_defectLaplace_zero hΨm (fun t => (hB t).2)
  simp only [Nat.cast_zero, zero_mul, add_zero] at hzero
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hbase : Tendsto (fun ε : ℝ => (ε : ℂ) * S ε) (𝓝[>] 0) (𝓝 (β / Real.pi)) := by
    have ht := hzero.add_const (β / Real.pi)
    rw [zero_add] at ht
    refine ht.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have hεc : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
    have he := quantization_reflected_defectLaplace_eq hW (τ := (ε : ℂ)) (by simpa using hε)
    change defectLaplace Ψ ε = S ε - β / (Real.pi * ε) at he
    rw [he]
    field_simp
    ring
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hden : (Real.pi : ℂ) * ((0 : ℂ) + (m : ℂ) * I) ≠ 0 := by simp [hπ, hm0]
  have hc := (Complex.continuous_ofReal.tendsto (0 : ℝ)).mul
    ((tendsto_const_nhds (x := β)).div ((tendsto_const_nhds (x := (Real.pi : ℂ))).mul
      ((Complex.continuous_ofReal.tendsto (0 : ℝ)).add_const ((m : ℂ) * I))) hden)
  have hcorr : Tendsto (fun ε : ℝ => (ε : ℂ) * (β / (Real.pi * ((ε : ℂ) + (m : ℂ) * I))))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hc.mono_left nhdsWithin_le_nhds
  have ht := hbase.sub hcorr
  rw [sub_zero] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [quantization_reflected_defectLaplace_eq hW (by simpa using hε)]
  have hper : S ((ε : ℂ) + (m : ℂ) * I) = S ε := by
    dsimp only [S]
    apply tsum_congr
    intro n
    rw [show -(2 * (Real.pi : ℂ) * ((n : ℂ) + 1) * ((ε : ℂ) + (m : ℂ) * I)) =
      -(2 * (Real.pi : ℂ) * ((n : ℂ) + 1) * ε) +
        (((-((n : ℤ) + 1) * (m : ℤ)) : ℤ) : ℂ) * (2 * Real.pi * I) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  change (ε : ℂ) * S ε - (ε : ℂ) * (β / (Real.pi * ((ε : ℂ) + (m : ℂ) * I))) =
    (ε : ℂ) * (S ((ε : ℂ) + (m : ℂ) * I) - β / (Real.pi * ((ε : ℂ) + (m : ℂ) * I)))
  rw [hper]
  ring

/-- The upper and compact pieces carry no positive-integer residue. -/
theorem tendsto_quantization_lower_reflected_radial {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * defectLaplace
      ((Iio (0 : ℝ)).indicator (fun t => quantizationReflectedTraceF hW (2 * t)))
      ((ε : ℂ) + (m : ℂ) * I)) (𝓝[>] 0)
      (𝓝 (betaG (quantizationCompletion hW) / Real.pi)) := by
  let Ψ : ℝ → ℂ := fun t => quantizationReflectedTraceF hW (2 * t)
  have hΨm : AEStronglyMeasurable Ψ volume :=
    ((measurable_quantizationReflectedTraceF hW).comp (measurable_const.mul measurable_id)).aestronglyMeasurable
  obtain ⟨C, _, hB⟩ := exists_quantization_trace_pair_bound hW
  have hup := tendsto_mul_defectLaplace_upper_radial hΨm (fun t => (hB t).2) (Y := 0) le_rfl m
  have hmid := tendsto_mul_abelMass_indicator_Icc hΨm (fun t => (hB t).2) 0
  simp only [neg_zero] at hmid
  have hmi := tendsto_mul_defectLaplace_radial (hΨm.indicator measurableSet_Icc)
    (fun t => (norm_indicator_le_norm_self _ t).trans (hB t).2) hmid m
  have h := ((tendsto_quantization_reflected_radial hW hm).sub hup).sub hmi
  simp only [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  change _ = (ε : ℂ) * defectLaplace ((Iio (0 : ℝ)).indicator Ψ) ((ε : ℂ) + (m : ℂ) * I)
  rw [defectLaplace_split hΨm (fun t => (hB t).2) (Y := 0) le_rfl (by simpa using hε)]
  simp only [neg_zero]
  ring

end RHTower.WeilSpectral
