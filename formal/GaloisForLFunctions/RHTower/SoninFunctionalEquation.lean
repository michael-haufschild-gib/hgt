import GaloisForLFunctions.RHTower.SoninPureChiKernel
import GaloisForLFunctions.RHTower.SoninCarrierFourierInvariance
import GaloisForLFunctions.RHTower.SoninMixedPhysicalBlockNonvanishing
import GaloisForLFunctions.HTGeometry.ImaginaryAxisCpow
import GaloisForLFunctions.HTGeometry.ReflectionSplitIntegral

/-!
# The functional equation of the Mellin transform of a Sonine vector

On the strip `0 < Re s < 1/2` the analytic continuation of the Mellin transform of an even Sonine
vector is the `χ`-kernel pairing against `𝓕f`.  Splitting that pairing into the two half-lines and
using that `𝓕f` is even turns the two branch values `(∓i)^{s-1}` of the kernel into
`2cos(π(s-1)/2)`, leaving

`f̂(s) = Γ(1-s) (2π)^{s-1} · 2cos(π(s-1)/2) · (𝓕f)^(1-s)`,

the functional equation with Burnol's `χ`-factor (arXiv:math/0203120, Thm. 2.1).

## Main results

* `burnolChiFactor`
* `soninMellinExtension_functional_equation`
-/

noncomputable section

open MeasureTheory Set Complex Real Filter Topology FourierTransform

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Burnol's `χ`-factor `Γ(1-s) (2π)^{s-1} · 2cos(π(s-1)/2)`. -/
def burnolChiFactor (s : ℂ) : ℂ :=
  Complex.Gamma (1 - s) * (((2 * Real.pi : ℝ) : ℂ)) ^ (s - 1)
    * (2 * Complex.cos ((Real.pi : ℂ) * (s - 1) / 2))

/-- On the positive half-line the `χ`-kernel carries the branch value `(-i)^{s-1}`. -/
theorem chiKernel_of_pos (s : ℂ) {u : ℝ} (hu : 0 < u) :
    chiKernel s u = ((2 * Real.pi : ℝ) : ℂ) ^ (s - 1) * ((u : ℝ) : ℂ) ^ (s - 1)
      * (-Complex.I) ^ (s - 1) := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hune : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hu
  have hIne : (-Complex.I) ≠ 0 := neg_ne_zero.2 Complex.I_ne_zero
  have hbase : (-((((2 * Real.pi * u : ℝ)) : ℂ) * Complex.I))
      = ((2 * Real.pi : ℝ) : ℂ) * (((u : ℝ) : ℂ) * (-Complex.I)) := by
    push_cast; ring
  rw [chiKernel, hbase, ofReal_mul_cpow h2pi (mul_ne_zero hune hIne) (s - 1),
    ofReal_mul_cpow hu hIne (s - 1)]
  ring

/-- On the negative half-line the `χ`-kernel carries the branch value `i^{s-1}`. -/
theorem chiKernel_of_neg (s : ℂ) {u : ℝ} (hu : 0 < u) :
    chiKernel s (-u) = ((2 * Real.pi : ℝ) : ℂ) ^ (s - 1) * ((u : ℝ) : ℂ) ^ (s - 1)
      * Complex.I ^ (s - 1) := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hune : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hu
  have hbase : (-((((2 * Real.pi * (-u) : ℝ)) : ℂ) * Complex.I))
      = ((2 * Real.pi : ℝ) : ℂ) * (((u : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  rw [chiKernel, hbase, ofReal_mul_cpow h2pi (mul_ne_zero hune Complex.I_ne_zero) (s - 1),
    ofReal_mul_cpow hu Complex.I_ne_zero (s - 1)]
  ring

/-- The two branch values add up to the cosine factor. -/
theorem neg_I_cpow_add_I_cpow (w : ℂ) :
    (-Complex.I) ^ w + Complex.I ^ w = 2 * Complex.cos ((Real.pi : ℂ) * w / 2) := by
  rw [add_comm]
  exact I_cpow_add_neg_I_cpow w

/-- **The functional equation with the near-zero head kept.**  Only the vanishing of the Fourier
transform on the band is used, so this covers the extended Sonine space after the band constant is
subtracted. -/
theorem soninMellinExtension_add_head_functional_equation {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hev : f ∈ evenSubspace) (hf : f ∈ (centralFourierForbidden a)ᗮ) {s : ℂ}
    (hs0 : 0 < s.re) (hs : s.re < 1 / 2) :
    soninMellinExtension f a s
        + ∫ t in Set.Ioo (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t
      = burnolChiFactor s * soninMellinIntegral (fourierUnitary f) (1 - s) := by
  have hgev : fourierUnitary f ∈ evenSubspace := fourierUnitary_mem_evenSubspace hev
  have hgeven : (fun u : ℝ => ((fourierUnitary f : SoninL2) : ℝ → ℂ) (-u))
      =ᵐ[volume] ((fourierUnitary f : SoninL2) : ℝ → ℂ) := by
    have h1 := l2Reflection_ae (fourierUnitary f)
    rw [(mem_evenSubspace_iff (fourierUnitary f)).1 hgev] at h1
    exact h1.symm
  have hint : Integrable (fun u : ℝ => Complex.Gamma (1 - s) * chiKernel s u
      * ((fourierUnitary f : SoninL2) : ℝ → ℂ) u) volume :=
    integrable_chiKernel_mul_fourier ha hf hs
  have hsplit : (∫ u : ℝ, Complex.Gamma (1 - s) * chiKernel s u
        * ((fourierUnitary f : SoninL2) : ℝ → ℂ) u)
      = (∫ u in Ioi (0 : ℝ), Complex.Gamma (1 - s) * chiKernel s u
          * ((fourierUnitary f : SoninL2) : ℝ → ℂ) u)
        + ∫ u in Ioi (0 : ℝ), Complex.Gamma (1 - s) * chiKernel s (-u)
          * ((fourierUnitary f : SoninL2) : ℝ → ℂ) (-u) :=
    integral_eq_add_reflect hint
  have h1 : (∫ u in Ioi (0 : ℝ), Complex.Gamma (1 - s) * chiKernel s u
        * ((fourierUnitary f : SoninL2) : ℝ → ℂ) u)
      = (Complex.Gamma (1 - s) * ((2 * Real.pi : ℝ) : ℂ) ^ (s - 1) * (-Complex.I) ^ (s - 1))
        * ∫ u in Ioi (0 : ℝ), ((u : ℝ) : ℂ) ^ (s - 1)
            * ((fourierUnitary f : SoninL2) : ℝ → ℂ) u := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    rw [chiKernel_of_pos s hu]
    ring
  have h2 : (∫ u in Ioi (0 : ℝ), Complex.Gamma (1 - s) * chiKernel s (-u)
        * ((fourierUnitary f : SoninL2) : ℝ → ℂ) (-u))
      = (Complex.Gamma (1 - s) * ((2 * Real.pi : ℝ) : ℂ) ^ (s - 1) * Complex.I ^ (s - 1))
        * ∫ u in Ioi (0 : ℝ), ((u : ℝ) : ℂ) ^ (s - 1)
            * ((fourierUnitary f : SoninL2) : ℝ → ℂ) u := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards [hgeven] with u hu hu0
    rw [chiKernel_of_neg s hu0, hu]
    ring
  have hM : (∫ u in Ioi (0 : ℝ), ((u : ℝ) : ℂ) ^ (s - 1)
        * ((fourierUnitary f : SoninL2) : ℝ → ℂ) u)
      = soninMellinIntegral (fourierUnitary f) (1 - s) := by
    simp only [soninMellinIntegral, neg_sub]
  rw [soninMellinExtension_add_head_eq_chi_pairing ha hf hs0 hs, hsplit, h1, h2, hM, ← add_mul]
  congr 1
  rw [burnolChiFactor, ← neg_I_cpow_add_I_cpow (s - 1)]
  ring

/-- **The functional equation of the Mellin transform of an even Sonine vector.** -/
theorem soninMellinExtension_functional_equation {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hev : f ∈ evenSubspace) (hf : f ∈ centralSoninCarrier a) {s : ℂ}
    (hs0 : 0 < s.re) (hs : s.re < 1 / 2) :
    soninMellinExtension f a s
      = burnolChiFactor s * soninMellinExtension (fourierUnitary f) a (1 - s) := by
  have hgcar : fourierUnitary f ∈ centralSoninCarrier a :=
    fourierUnitary_mem_centralSoninCarrier hev hf
  have hext : soninMellinExtension (fourierUnitary f) a (1 - s)
      = soninMellinIntegral (fourierUnitary f) (1 - s) := by
    refine soninMellinExtension_eq_soninMellinIntegral ha hgcar ?_
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have h := soninMellinExtension_add_head_functional_equation ha hev hf.2 hs0 hs
  rw [integral_nearZeroHead_eq_zero ha hf s, add_zero] at h
  rw [hext]
  exact h

end RHTower

end
