import GaloisForLFunctions.HTGeometry.AtomMassLimit
import GaloisForLFunctions.HTGeometry.GramOffDiagonalBound
import GaloisForLFunctions.HTGeometry.StieltjesTransformPick
import GaloisForLFunctions.HTGeometry.LeafCauchyTransform

/-!
# Atom mass from the boundary growth of a Stieltjes transform

Multiplying the imaginary part of the Cauchy transform at `a + iy` by `y` produces the corpus's
scaled atom kernel exactly. Dominated convergence therefore recovers the mass at `a`. This is the
measure-theoretic bridge between a real pole of an algebraic Cauchy transform and a spectral atom.
-/

open Filter Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The scaled imaginary Cauchy kernel is literally the atom-selection kernel under the integral. -/
theorem mul_im_stieltjes_eq_integral_atomKernel
    (μ : Measure ℝ) [IsFiniteMeasure μ] (a y : ℝ) (hy : y ≠ 0) :
    y * (∫ t : ℝ, ((t : ℂ) - ((a : ℂ) + (y : ℂ) * Complex.I))⁻¹ ∂μ).im =
      ∫ t : ℝ, atomKernel a y t ∂μ := by
  have hz : (((a : ℂ) + (y : ℂ) * Complex.I).im) ≠ 0 := by simpa using hy
  rw [HTGeometry.im_integral (HTGeometry.integrable_cauchy_kernel μ hz),
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  change y * (((t : ℂ) - ((a : ℂ) + (y : ℂ) * Complex.I))⁻¹).im = atomKernel a y t
  rw [HTGeometry.cauchyKernel_im]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, zero_add, mul_zero, add_zero]
  rw [atomKernel]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re, Complex.add_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.sub_im, Complex.ofReal_im,
    Complex.add_im, Complex.mul_im, mul_one, mul_zero, add_zero, zero_add]
  ring

/-- **Stieltjes atom formula.** The nontangential boundary growth `y Im Sμ(a+iy)` converges to the
exact atom mass `μ({a})`. -/
theorem tendsto_mul_im_stieltjes_atomMass
    (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ) :
    Tendsto (fun y : ℝ =>
      y * (∫ t : ℝ, ((t : ℂ) - ((a : ℂ) + (y : ℂ) * Complex.I))⁻¹ ∂μ).im)
      (𝓝[≠] 0) (𝓝 (μ {a}).toReal) := by
  refine (tendsto_integral_atomKernel μ a).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (mul_im_stieltjes_eq_integral_atomKernel μ a y hy).symm

/-- The full height-scaled Cauchy kernel selects the atom with phase `i`. -/
theorem tendsto_scaledCauchy_indicator (a t : ℝ) :
    Tendsto (fun y : ℝ =>
      (y : ℂ) * ((t : ℂ) - ((a : ℂ) + (y : ℂ) * Complex.I))⁻¹)
      (𝓝[≠] 0) (𝓝 (Set.indicator {a} (fun _ => Complex.I) t)) := by
  by_cases hta : t = a
  · subst t
    have hval : Set.indicator {a} (fun _ => Complex.I) a = Complex.I := by simp
    rw [hval]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with y hy
    symm
    calc
      (y : ℂ) * ((a : ℂ) - ((a : ℂ) + (y : ℂ) * Complex.I))⁻¹ =
          (y : ℂ) * (-(y : ℂ) * Complex.I)⁻¹ := by ring_nf
      _ = (y : ℂ) * (-(y : ℂ)⁻¹ * Complex.I⁻¹) := by
        rw [mul_inv, inv_neg]
      _ = Complex.I := by
        rw [Complex.inv_I, neg_mul_neg, ← mul_assoc,
          mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hy), one_mul]
  · have hval : Set.indicator {a} (fun _ => Complex.I) t = 0 := by simp [hta]
    rw [hval]
    have hden : (t : ℂ) - (a : ℂ) ≠ 0 := by
      intro h
      apply hta
      have hre := congrArg Complex.re (sub_eq_zero.mp h)
      simpa using hre
    have hc : ContinuousAt (fun y : ℝ =>
        (y : ℂ) * ((t : ℂ) - ((a : ℂ) + (y : ℂ) * Complex.I))⁻¹) 0 := by
      apply ContinuousAt.mul Complex.continuous_ofReal.continuousAt
      apply ContinuousAt.inv₀
      · fun_prop
      · simpa using hden
    change Tendsto _ (𝓝 0 ⊓ 𝓟 {0}ᶜ) (𝓝 0)
    simpa [hta] using hc.tendsto.mono_left inf_le_left

/-- **Complex Stieltjes atom formula.** Multiplication by the boundary height recovers `i` times
the exact atom mass. -/
theorem tendsto_mul_stieltjes_atomMass
    (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ) :
    Tendsto (fun y : ℝ =>
      (y : ℂ) * ∫ t : ℝ,
        ((t : ℂ) - ((a : ℂ) + (y : ℂ) * Complex.I))⁻¹ ∂μ)
      (𝓝[≠] 0) (𝓝 (Complex.I * (μ {a}).toReal)) := by
  have hlim : Tendsto (fun y : ℝ => ∫ t : ℝ,
      (y : ℂ) * ((t : ℂ) - upperNode a y)⁻¹ ∂μ) (𝓝[≠] 0)
      (𝓝 (∫ t : ℝ, Set.indicator {a} (fun _ => Complex.I) t ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_
      (integrable_const 1) ?_
    · filter_upwards [self_mem_nhdsWithin] with y hy
      apply Continuous.aestronglyMeasurable
      apply Continuous.mul continuous_const
      apply Continuous.inv₀ (Complex.continuous_ofReal.sub continuous_const)
      intro t ht
      have him := congrArg Complex.im ht
      exact hy (by simpa [upperNode] using him)
    · filter_upwards [self_mem_nhdsWithin] with y hy
      filter_upwards with t
      have hsq := normSq_scaled_cauchy_eq_atomKernel a y t
      have hle := atomKernel_le_one a t hy
      nlinarith [norm_nonneg ((y : ℂ) * ((t : ℂ) - upperNode a y)⁻¹)]
    · filter_upwards with t
      simpa [upperNode] using tendsto_scaledCauchy_indicator a t
  have hval : ∫ t : ℝ, Set.indicator {a} (fun _ => Complex.I) t ∂μ =
      Complex.I * (μ {a}).toReal := by
    rw [integral_indicator_const _ (measurableSet_singleton a)]
    simp [measureReal_def, mul_comm]
  rw [hval] at hlim
  simpa only [upperNode, integral_const_mul] using hlim

end

end GaloisForLFunctions.HTGeometry
