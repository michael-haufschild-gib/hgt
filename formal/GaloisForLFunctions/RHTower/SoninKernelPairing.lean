import GaloisForLFunctions.HTGeometry.TruncatedPowerFourierLimit
import GaloisForLFunctions.RHTower.SoninMellinHalfPlaneExtension

/-!
# The Sonine Mellin transform as a pairing against Burnol's kernel

Plancherel turns the truncated Mellin transform of a Sonine vector into a pairing of its Fourier
transform against the conjugated Fourier transform of the truncated power.  Letting the truncation
run off to infinity — dominated by the uniform `1/|u|` bound — expresses the analytic continuation
of the Mellin transform as a single integral against **Burnol's kernel**

`C_a(u,s) = Γ(1-s)(-2πui)^{s-1} − ∫_0^a e^{2πiut}t^{-s}dt`.

## Main results

* `soninTruncMellin_eq_kernel_pairing`
* `burnolKernel`
-/

noncomputable section

open MeasureTheory Set Complex Real Filter Topology FourierTransform
open scoped InnerProductSpace

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The coefficient function of the truncated pairing. -/
def truncKernel (a T : ℝ) (s : ℂ) (u : ℝ) : ℂ :=
  ∫ t in a..T, ((t : ℝ) : ℂ) ^ (-s) * Complex.exp ((t * (2 * Real.pi * u) : ℝ) * Complex.I)

/-- **Burnol's kernel** `C_a(u,s)`. -/
def burnolKernel (a : ℝ) (s : ℂ) (u : ℝ) : ℂ :=
  Complex.Gamma (1 - s) * (-((((2 * Real.pi * u : ℝ)) : ℂ) * Complex.I)) ^ (s - 1)
    - ∫ t in (0 : ℝ)..a, ((t : ℝ) : ℂ) ^ (-s)
        * Complex.exp ((t * (2 * Real.pi * u) : ℝ) * Complex.I)

theorem coeFn_fourierUnitary_truncPowerVector {a T : ℝ} (ha : 0 < a) {s : ℂ} (hs0 : 0 < s.re) :
    ∀ᵐ u ∂(volume : Measure ℝ),
      ((fourierUnitary (truncPowerVector a T ha hs0) : SoninL2) : ℝ → ℂ) u
        = 𝓕 (truncPower a T ((starRingEnd ℂ) s)) u := by
  have hcs : 0 < ((starRingEnd ℂ) s).re := by rwa [Complex.conj_re]
  set W : SoninL2 := truncPowerVector a T ha hs0 with hW
  have hae : ((W : SoninL2) : ℝ → ℂ) =ᵐ[volume] truncPower a T ((starRingEnd ℂ) s) := by
    simpa [hW, truncPowerVector] using
      (memLp_two_truncPower (T' := T) ha hcs).coeFn_toLp
  have hWint : Integrable ((W : SoninL2) : ℝ → ℂ) volume :=
    (integrable_truncPower (T' := T) ha hcs).congr hae.symm
  have hbridge := l2_fourier_coeFn_eq_l1_fourier_of_integrable W hWint
  filter_upwards [hbridge] with u hu
  have h1 : ((fourierUnitary W : SoninL2) : ℝ → ℂ) u = ((𝓕 W : SoninL2) : ℝ → ℂ) u := rfl
  rw [h1, hu, fourierTransform_toLp]
  exact (Real.fourier_congr_ae hae) u

/-- **Plancherel form of the truncated Mellin transform.** -/
theorem soninTruncMellin_eq_kernel_pairing {a T : ℝ} (ha : 0 < a) (haT : a ≤ T) (f : SoninL2)
    {s : ℂ} (hs0 : 0 < s.re) :
    soninTruncMellin f a T s
      = ∫ u : ℝ, truncKernel a T s u * ((fourierUnitary f : SoninL2) : ℝ → ℂ) u := by
  set W : SoninL2 := truncPowerVector a T ha hs0 with hW
  have hpair : ⟪W, f⟫_ℂ = soninTruncMellin f a T s :=
    inner_truncPowerVector_eq_truncMellin ha hs0 f
  have hplanch : ⟪W, f⟫_ℂ = ⟪fourierUnitary W, fourierUnitary f⟫_ℂ :=
    (fourierUnitary.inner_map_map W f).symm
  rw [← hpair, hplanch, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_fourierUnitary_truncPowerVector (T := T) ha hs0] with u hu
  rw [RCLike.inner_apply, hu, truncKernel, ← conj_fourierIntegral_truncPower ha.le haT s u]
  ring

theorem norm_truncKernel_le {a T : ℝ} (ha : 0 < a) (haT : a ≤ T) {s : ℂ} (hs0 : 0 < s.re)
    {u : ℝ} (hu : u ≠ 0) :
    ‖truncKernel a T s u‖
      ≤ (2 * a ^ (-s.re) + ‖s‖ * a ^ (-s.re) / s.re) / (2 * Real.pi * |u|) := by
  have hcs : 0 < ((starRingEnd ℂ) s).re := by rwa [Complex.conj_re]
  have h := norm_fourierIntegral_truncPower_le ha haT hcs hu
  rw [Complex.conj_re] at h
  have hnorm : ‖(starRingEnd ℂ) s‖ = ‖s‖ := by simp
  rw [hnorm] at h
  rw [truncKernel, ← conj_fourierIntegral_truncPower ha.le haT s u, RCLike.norm_conj]
  exact h

/-- **Burnol's kernel represents the analytic continuation.** -/
theorem soninMellinExtension_eq_kernel_pairing {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hf : f ∈ centralSoninCarrier a) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    soninMellinExtension f a s
      = ∫ u : ℝ, burnolKernel a s u * ((fourierUnitary f : SoninL2) : ℝ → ℂ) u := by
  set g : ℝ → ℂ := ((fourierUnitary f : SoninL2) : ℝ → ℂ) with hg
  set Cst : ℝ := (2 * a ^ (-s.re) + ‖s‖ * a ^ (-s.re) / s.re) / (2 * Real.pi) with hCst
  have hCst0 : 0 ≤ Cst := by
    have h1 : (0:ℝ) ≤ a ^ (-s.re) := Real.rpow_nonneg ha.le _
    have h2 : (0:ℝ) < 2 * Real.pi := by positivity
    rw [hCst]
    positivity
  have hband := fourier_indicator_ae_zero_of_mem_centralSoninCarrier hf
  have hgzero : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a → g u = 0 := by
    filter_upwards [hband] with u hu hmem
    simpa [Set.indicator_of_mem hmem] using hu
  set bound : ℝ → ℝ := fun u => Cst * invAbsTail a u * ‖g u‖ with hbound
  have hboundint : Integrable bound volume := by
    have h1 : MemLp (fun u : ℝ => Cst * invAbsTail a u) 2 volume :=
      (memLp_two_invAbsTail ha).const_mul Cst
    have h2 : MemLp (fun u : ℝ => ‖g u‖) 2 volume := (Lp.memLp (fourierUnitary f)).norm
    have := h1.integrable_mul h2
    refine this.congr ?_
    filter_upwards with u
    rfl
  -- the dominated convergence
  have hdct := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure ℝ)) (l := (atTop : Filter ℝ))
    (F := fun T u => truncKernel a T s u * g u)
    (f := fun u => burnolKernel a s u * g u) bound ?_ ?_ hboundint ?_
  · -- identify the limit with the extension
    have hseq : Tendsto (fun n : ℕ => soninTruncMellin f a (a + (n : ℝ)) s) atTop
        (𝓝 (soninMellinExtension f a s)) := tendsto_soninMellinSeq ha hf hs0
    have hnat : Tendsto (fun n : ℕ => a + (n : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left _ a tendsto_natCast_atTop_atTop
    have hcomp := hdct.comp hnat
    have hcongr : (fun n : ℕ => ∫ u : ℝ, truncKernel a (a + (n : ℝ)) s u * g u)
        = fun n : ℕ => soninTruncMellin f a (a + (n : ℝ)) s := by
      funext n
      have hle : a ≤ a + (n : ℝ) := by
        have := Nat.cast_nonneg (α := ℝ) n
        linarith
      rw [soninTruncMellin_eq_kernel_pairing ha hle f hs0]
    rw [Function.comp_def, hcongr] at hcomp
    exact tendsto_nhds_unique hseq hcomp
  · -- measurability
    filter_upwards [eventually_ge_atTop a] with T hT
    have hae : (fun u => truncKernel a T s u * g u)
        =ᵐ[volume] fun u =>
          (starRingEnd ℂ) (((fourierUnitary (truncPowerVector a T ha hs0) : SoninL2) : ℝ → ℂ) u)
            * g u := by
      filter_upwards [coeFn_fourierUnitary_truncPowerVector (T := T) ha hs0] with u hu
      rw [hu, truncKernel, ← conj_fourierIntegral_truncPower ha.le hT s u]
    refine AEStronglyMeasurable.congr ?_ hae.symm
    exact ((Complex.continuous_conj.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable _)).mul (Lp.aestronglyMeasurable _))
  · -- domination
    filter_upwards [eventually_ge_atTop a] with T hT
    filter_upwards [hgzero] with u hu
    by_cases hlt : a < |u|
    · have hune : u ≠ 0 := by
        intro h
        rw [h] at hlt
        simp at hlt
        linarith
      have hk := norm_truncKernel_le ha hT hs0 hune
      have habs : (0:ℝ) < |u| := abs_pos.2 hune
      have hinv : invAbsTail a u = |u|⁻¹ := by rw [invAbsTail, if_pos hlt]
      rw [norm_mul]
      show ‖truncKernel a T s u‖ * ‖g u‖ ≤ Cst * invAbsTail a u * ‖g u‖
      rw [hinv]
      have hgn : (0:ℝ) ≤ ‖g u‖ := norm_nonneg _
      refine mul_le_mul_of_nonneg_right ?_ hgn
      refine hk.trans (le_of_eq ?_)
      rw [hCst]
      field_simp
    · have hmem : u ∈ centralInterval a := by
        rw [centralInterval, Set.mem_Icc, ← abs_le]
        exact not_lt.mp hlt
      have hg0 : g u = 0 := hu hmem
      have hinv : invAbsTail a u = 0 := by rw [invAbsTail, if_neg hlt]
      rw [norm_mul, hg0, norm_zero, mul_zero]
      show (0:ℝ) ≤ Cst * invAbsTail a u * ‖g u‖
      rw [hinv]
      simp
  · -- pointwise convergence
    have hune : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ (0:ℝ) := by
      filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0:ℝ))] with u hu
      simpa using hu
    filter_upwards [hune] with u hu
    exact (tendsto_conj_fourierIntegral_truncPower ha hs0 hs1 hu).mul_const (g u)

end RHTower
