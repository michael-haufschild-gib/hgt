import GaloisForLFunctions.RHTower.XiCentralDiscBound
import GaloisForLFunctions.RHTower.PrimeWeylSamplingIdealizerAnalytic

/-!
# The real divisor of the completed zeta as a sampling set

In the centred coordinate `ΞC z = ξ(½ + z i)` the real zeros of the completed zeta are the real
points of the critical-line divisor.  Two of the three structural properties required by the
sampling idealizer theorem hold unconditionally: the divisor meets every bounded window in a finite
set, because `ΞC` is entire and does not vanish at the origin, and it is symmetric under
`t ↦ -t`, because `ΞC` is even.
-/

namespace RHTower

open Complex Set Filter

noncomputable section

/-- The real divisor of the completed zeta in the centred coordinate. -/
def xiRealDivisor : Set ℝ := {t : ℝ | XiC (t : ℂ) = 0}

/-- The zeros of `ΞC` are finite in every closed disc. -/
theorem xiC_zeros_closedBall_finite (c : ℂ) (R : ℝ) :
    {z ∈ Metric.closedBall c R | XiC z = 0}.Finite := by
  have hne : XiC 0 ≠ 0 := XiC_ne_zero_of_norm_le_one (by simp)
  have hA : AnalyticOnNhd ℂ XiC Set.univ :=
    XiC_differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have hcod : (XiC ⁻¹' {0}ᶜ) ∈ codiscreteWithin (Set.univ : Set ℂ) :=
    hA.preimage_zero_mem_codiscreteWithin (x := (0 : ℂ)) hne (Set.mem_univ _) isConnected_univ
  have hcodK : (XiC ⁻¹' {0}ᶜ) ∈ codiscreteWithin (Metric.closedBall c R) :=
    Filter.codiscreteWithin_mono (Set.subset_univ _) hcod
  refine ((isCompact_closedBall c R).finite_sdiff_of_mem_codiscreteWithin hcodK).subset ?_
  intro z hz
  rw [Set.mem_sep_iff] at hz
  exact ⟨hz.1, by simp [Set.mem_preimage, hz.2]⟩

/-- **The real Xi divisor is locally finite.** -/
theorem locallyFiniteSamples_xiRealDivisor : LocallyFiniteSamples xiRealDivisor := by
  intro T
  have hfin := xiC_zeros_closedBall_finite 0 |T|
  have hpre : ((fun t : ℝ => (t : ℂ)) ⁻¹'
      {z ∈ Metric.closedBall (0 : ℂ) |T| | XiC z = 0}).Finite :=
    hfin.preimage (Complex.ofReal_injective.injOn)
  refine hpre.subset ?_
  rintro t ⟨ht, ht1, ht2⟩
  refine ⟨?_, ht⟩
  rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨le_trans (neg_le_neg (le_abs_self T)) ht1, le_trans ht2 (le_abs_self T)⟩

/-- **The real Xi divisor is symmetric.**  This is the evenness of `ΞC`, itself the functional
equation. -/
theorem neg_mem_xiRealDivisor {t : ℝ} (ht : t ∈ xiRealDivisor) : -t ∈ xiRealDivisor := by
  show XiC ((-t : ℝ) : ℂ) = 0
  rw [Complex.ofReal_neg, XiC_even]
  exact ht

theorem symmetric_xiRealDivisor : ∀ t, t ∈ xiRealDivisor → -t ∈ xiRealDivisor :=
  fun _ ht => neg_mem_xiRealDivisor ht

end

end RHTower
