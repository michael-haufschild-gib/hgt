import GaloisForLFunctions.RHTower.SoninNearZeroKernelVanishing
import GaloisForLFunctions.HTGeometry.PowerTailL2

/-!
# Removing the correction: the pure `χ`-kernel

Combining the kernel representation of the analytic continuation with the vanishing of the
correction term leaves, for `0 < Re s < 1/2`,

`f̂(s) = Γ(1-s) ∫ (-2πui)^{s-1} 𝓕f(u) du`,

i.e. Burnol's kernel acts on a Sonine vector exactly through its `χ`-factor
(arXiv:math/0203120, Thm. 2.1).

## Main results

* `integrable_burnolKernel_mul_fourier`
* `soninMellinExtension_eq_chi_pairing`
-/

noncomputable section

open MeasureTheory Set Complex Real Filter Topology FourierTransform
open scoped InnerProductSpace

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The `χ`-part of Burnol's kernel. -/
def chiKernel (s : ℂ) (u : ℝ) : ℂ :=
  (-((((2 * Real.pi * u : ℝ)) : ℂ) * Complex.I)) ^ (s - 1)

theorem burnolKernel_eq (a : ℝ) (s : ℂ) (u : ℝ) :
    burnolKernel a s u = Complex.Gamma (1 - s) * chiKernel s u
      - ∫ t in (0 : ℝ)..a, ((t : ℝ) : ℂ) ^ (-s)
          * Complex.exp ((t * (2 * Real.pi * u) : ℝ) * Complex.I) := rfl

theorem integrable_nearZeroKernel_mul_fourier {a : ℝ} (ha : 0 < a) (f : SoninL2) {s : ℂ}
    (hs : s.re < 1 / 2) :
    Integrable (fun u : ℝ => (∫ t in (0 : ℝ)..a, ((t : ℝ) : ℂ) ^ (-s)
        * Complex.exp ((t * (2 * Real.pi * u) : ℝ) * Complex.I))
      * ((fourierUnitary f : SoninL2) : ℝ → ℂ) u) volume := by
  set W : SoninL2 := nearZeroPowerVector a hs with hW
  have hae : (fun u : ℝ => (∫ t in (0 : ℝ)..a, ((t : ℝ) : ℂ) ^ (-s)
        * Complex.exp ((t * (2 * Real.pi * u) : ℝ) * Complex.I))
      * ((fourierUnitary f : SoninL2) : ℝ → ℂ) u)
      =ᵐ[volume] fun u : ℝ => (starRingEnd ℂ) (((fourierUnitary W : SoninL2) : ℝ → ℂ) u)
        * ((fourierUnitary f : SoninL2) : ℝ → ℂ) u := by
    filter_upwards [coeFn_fourierUnitary_nearZeroPowerVector (a := a) ha.le hs] with u hu
    rw [hu, ← conj_fourierIntegral_truncPower (le_refl (0 : ℝ)) ha.le s u]
  refine Integrable.congr ?_ hae.symm
  have h1 : MemLp (fun u : ℝ => (starRingEnd ℂ) (((fourierUnitary W : SoninL2) : ℝ → ℂ) u))
      2 volume := by
    have := Lp.memLp (fourierUnitary W)
    exact this.star
  exact h1.integrable_mul (Lp.memLp (fourierUnitary f))

/-- The `χ`-kernel pairs integrably against the Fourier transform of a Sonine vector. -/
theorem integrable_chiKernel_mul_fourier {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hf : f ∈ (centralFourierForbidden a)ᗮ) {s : ℂ} (hs : s.re < 1 / 2) :
    Integrable (fun u : ℝ => Complex.Gamma (1 - s) * chiKernel s u
      * ((fourierUnitary f : SoninL2) : ℝ → ℂ) u) volume := by
  set g : ℝ → ℂ := ((fourierUnitary f : SoninL2) : ℝ → ℂ) with hg
  set Cchi : ℝ := ‖Complex.Gamma (1 - s)‖ *
    (Real.exp (Real.pi * |s.im|) * (2 * Real.pi) ^ (s.re - 1)) with hCchi
  have hCchi0 : 0 ≤ Cchi := by
    have h1 : (0:ℝ) ≤ (2 * Real.pi) ^ (s.re - 1) := Real.rpow_nonneg (by positivity) _
    rw [hCchi]
    positivity
  have hchibound : ∀ u : ℝ, u ≠ 0 →
      ‖chiKernel s u‖ ≤ Real.exp (Real.pi * |s.im|) * (2 * Real.pi) ^ (s.re - 1)
        * |u| ^ (s.re - 1) := by
    intro u hu
    have hw : ‖(-((((2 * Real.pi * u : ℝ)) : ℂ) * Complex.I))‖ = 2 * Real.pi * |u| := by
      rw [norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
    have hle := Complex.norm_cpow_le (-((((2 * Real.pi * u : ℝ)) : ℂ) * Complex.I)) (s - 1)
    rw [chiKernel]
    refine hle.trans ?_
    rw [hw, Complex.sub_re, Complex.one_re]
    have hargbnd : -(Complex.arg (-((((2 * Real.pi * u : ℝ)) : ℂ) * Complex.I)) * (s - 1).im)
        ≤ Real.pi * |s.im| := by
      have h1 := Complex.arg_le_pi (-((((2 * Real.pi * u : ℝ)) : ℂ) * Complex.I))
      have h2 := Complex.neg_pi_lt_arg (-((((2 * Real.pi * u : ℝ)) : ℂ) * Complex.I))
      have habs : |Complex.arg (-((((2 * Real.pi * u : ℝ)) : ℂ) * Complex.I))| ≤ Real.pi := by
        rw [abs_le]
        exact ⟨le_of_lt h2, h1⟩
      have him : (s - 1).im = s.im := by simp
      rw [him]
      calc -(Complex.arg (-((((2 * Real.pi * u : ℝ)) : ℂ) * Complex.I)) * s.im)
          ≤ |Complex.arg (-((((2 * Real.pi * u : ℝ)) : ℂ) * Complex.I)) * s.im| :=
            neg_le_abs _
        _ = |Complex.arg (-((((2 * Real.pi * u : ℝ)) : ℂ) * Complex.I))| * |s.im| := abs_mul _ _
        _ ≤ Real.pi * |s.im| := mul_le_mul_of_nonneg_right habs (abs_nonneg _)
    have hdiv : (2 * Real.pi * |u|) ^ (s.re - 1)
        / Real.exp (Complex.arg (-((((2 * Real.pi * u : ℝ)) : ℂ) * Complex.I)) * (s - 1).im)
        = (2 * Real.pi * |u|) ^ (s.re - 1)
          * Real.exp (-(Complex.arg (-((((2 * Real.pi * u : ℝ)) : ℂ) * Complex.I))
            * (s - 1).im)) := by
      rw [Real.exp_neg, div_eq_mul_inv]
    rw [hdiv]
    have hsplit : (2 * Real.pi * |u|) ^ (s.re - 1)
        = (2 * Real.pi) ^ (s.re - 1) * |u| ^ (s.re - 1) :=
      Real.mul_rpow (by positivity) (abs_nonneg u)
    rw [hsplit]
    have hexpb : Real.exp (-(Complex.arg (-((((2 * Real.pi * u : ℝ)) : ℂ) * Complex.I))
        * (s - 1).im)) ≤ Real.exp (Real.pi * |s.im|) := Real.exp_le_exp.2 hargbnd
    have hnn : (0:ℝ) ≤ (2 * Real.pi) ^ (s.re - 1) * |u| ^ (s.re - 1) := by
      have h1 : (0:ℝ) ≤ (2 * Real.pi) ^ (s.re - 1) := Real.rpow_nonneg (by positivity) _
      have h2 : (0:ℝ) ≤ |u| ^ (s.re - 1) := Real.rpow_nonneg (abs_nonneg u) _
      positivity
    calc (2 * Real.pi) ^ (s.re - 1) * |u| ^ (s.re - 1)
          * Real.exp (-(Complex.arg (-((((2 * Real.pi * u : ℝ)) : ℂ) * Complex.I))
            * (s - 1).im))
        ≤ (2 * Real.pi) ^ (s.re - 1) * |u| ^ (s.re - 1) * Real.exp (Real.pi * |s.im|) := by
          exact mul_le_mul_of_nonneg_left hexpb hnn
      _ = Real.exp (Real.pi * |s.im|) * (2 * Real.pi) ^ (s.re - 1) * |u| ^ (s.re - 1) := by ring
  have hband := fourier_indicator_ae_zero_of_mem_fourierOrthogonal hf
  have hgzero : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a → g u = 0 := by
    filter_upwards [hband] with u hu hmem
    simpa [Set.indicator_of_mem hmem] using hu
  have hmajint : Integrable (fun u : ℝ => Cchi * powerTail a (s.re - 1) u * ‖g u‖) volume := by
    have h1 : MemLp (fun u : ℝ => Cchi * powerTail a (s.re - 1) u) 2 volume :=
      (memLp_two_powerTail ha (by linarith)).const_mul Cchi
    have h2 : MemLp (fun u : ℝ => ‖g u‖) 2 volume := (Lp.memLp (fourierUnitary f)).norm
    exact (h1.integrable_mul h2).congr (Filter.Eventually.of_forall fun u => rfl)
  have hchimeas : AEStronglyMeasurable
      (fun u : ℝ => Complex.Gamma (1 - s) * chiKernel s u * g u) volume := by
    have hc : Measurable (fun u : ℝ => chiKernel s u) := by
      unfold chiKernel
      fun_prop
    exact ((measurable_const.mul hc).aestronglyMeasurable).mul (Lp.aestronglyMeasurable _)
  have hchiint : Integrable (fun u : ℝ => Complex.Gamma (1 - s) * chiKernel s u * g u) volume := by
    refine Integrable.mono' hmajint hchimeas ?_
    filter_upwards [hgzero] with u hu
    by_cases hlt : a < |u|
    · have hune : u ≠ 0 := by
        intro h
        rw [h] at hlt
        simp at hlt
        linarith
      have hpt : powerTail a (s.re - 1) u = |u| ^ (s.re - 1) := by
        rw [powerTail, if_pos hlt]
      rw [norm_mul, norm_mul, hpt]
      have hgn : (0:ℝ) ≤ ‖g u‖ := norm_nonneg _
      refine mul_le_mul_of_nonneg_right ?_ hgn
      have := hchibound u hune
      rw [hCchi]
      calc ‖Complex.Gamma (1 - s)‖ * ‖chiKernel s u‖
          ≤ ‖Complex.Gamma (1 - s)‖ * (Real.exp (Real.pi * |s.im|) * (2 * Real.pi) ^ (s.re - 1)
              * |u| ^ (s.re - 1)) := by
            exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ = ‖Complex.Gamma (1 - s)‖ * (Real.exp (Real.pi * |s.im|)
              * (2 * Real.pi) ^ (s.re - 1)) * |u| ^ (s.re - 1) := by ring
    · have hmem : u ∈ centralInterval a := by
        rw [centralInterval, Set.mem_Icc, ← abs_le]
        exact not_lt.mp hlt
      have hg0 : g u = 0 := hu hmem
      have hpt : powerTail a (s.re - 1) u = 0 := by rw [powerTail, if_neg hlt]
      rw [hg0, mul_zero, norm_zero, hpt]
      simp
  exact hchiint

/-- **The pure `χ`-kernel identity, with the near-zero head kept.**  Only the vanishing of the
Fourier transform on the band is used. -/
theorem soninMellinExtension_add_head_eq_chi_pairing {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hf : f ∈ (centralFourierForbidden a)ᗮ) {s : ℂ} (hs0 : 0 < s.re) (hs : s.re < 1 / 2) :
    soninMellinExtension f a s
        + ∫ t in Set.Ioo (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t
      = ∫ u : ℝ, Complex.Gamma (1 - s) * chiKernel s u
          * ((fourierUnitary f : SoninL2) : ℝ → ℂ) u := by
  have hs1 : s.re < 1 := by linarith
  set g : ℝ → ℂ := ((fourierUnitary f : SoninL2) : ℝ → ℂ) with hg
  set E : ℝ → ℂ := fun u => ∫ t in (0 : ℝ)..a, ((t : ℝ) : ℂ) ^ (-s)
      * Complex.exp ((t * (2 * Real.pi * u) : ℝ) * Complex.I) with hE
  have hEint : Integrable (fun u : ℝ => E u * g u) volume :=
    integrable_nearZeroKernel_mul_fourier ha f hs
  have hEval : (∫ u : ℝ, E u * g u)
      = ∫ t in Set.Ioo (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t :=
    integral_nearZeroKernel_mul_fourier_eq ha f hs
  have hker := soninMellinExtension_eq_kernel_pairing ha hf hs0 hs1
  have hAeq : ∀ u : ℝ, Complex.Gamma (1 - s) * chiKernel s u * g u
      = burnolKernel a s u * g u + E u * g u := by
    intro u
    rw [burnolKernel_eq]
    ring
  have hchiint := integrable_chiKernel_mul_fourier ha hf hs
  have hburnolint : Integrable (fun u : ℝ => burnolKernel a s u * g u) volume := by
    have heq : (fun u : ℝ => burnolKernel a s u * g u)
        = fun u : ℝ => (Complex.Gamma (1 - s) * chiKernel s u * g u) - (E u * g u) := by
      funext u
      rw [hAeq u]
      ring
    rw [heq]
    exact hchiint.sub hEint
  calc soninMellinExtension f a s
        + ∫ t in Set.Ioo (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t
      = (∫ u : ℝ, burnolKernel a s u * g u) + ∫ u : ℝ, E u * g u := by rw [hker, hEval]
    _ = ∫ u : ℝ, (burnolKernel a s u * g u + E u * g u) :=
        (MeasureTheory.integral_add hburnolint hEint).symm
    _ = ∫ u : ℝ, Complex.Gamma (1 - s) * chiKernel s u * g u := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        exact (hAeq u).symm

/-- The near-zero head of a Sonine vector vanishes. -/
theorem integral_nearZeroHead_eq_zero {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hf : f ∈ centralSoninCarrier a) (s : ℂ) :
    (∫ t in Set.Ioo (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t) = 0 := by
  have hsupp := physical_indicator_ae_zero_of_mem_centralSoninCarrier hf
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = 0 := by
    filter_upwards [hsupp] with t ht hmem
    simpa [Set.indicator_of_mem hmem] using ht
  refine MeasureTheory.integral_eq_zero_of_ae ?_
  filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Ioo] with t ht hmem
  have hband : t ∈ centralInterval a := by
    rw [centralInterval, Set.mem_Icc]
    exact ⟨by linarith [hmem.1, ha], le_of_lt hmem.2⟩
  rw [ht hband, mul_zero]
  rfl

/-- **The pure `χ`-kernel identity.** -/
theorem soninMellinExtension_eq_chi_pairing {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hf : f ∈ centralSoninCarrier a) {s : ℂ} (hs0 : 0 < s.re) (hs : s.re < 1 / 2) :
    soninMellinExtension f a s
      = ∫ u : ℝ, Complex.Gamma (1 - s) * chiKernel s u
          * ((fourierUnitary f : SoninL2) : ℝ → ℂ) u := by
  have h := soninMellinExtension_add_head_eq_chi_pairing ha hf.2 hs0 hs
  rw [integral_nearZeroHead_eq_zero ha hf s, add_zero] at h
  exact h

end RHTower
