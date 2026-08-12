import Mathlib

/-!
# Local-exponential test closure

A finite measure on `ℝ` that integrates one exponential window `e^{a|x|}` is determined by its
moments: the complex moment-generating functions of two such measures are analytic on the common
vertical strip, their jets at the origin are the moment sequences, and the identity theorem
propagates the vanishing difference to the imaginary axis, where it is the characteristic function.

This is the local-exponential replacement for entire-moment determinacy, and it is the closure
mechanism behind polynomial density in `L²` of such a measure.
-/

namespace HTGeometry

open MeasureTheory ProbabilityTheory Complex Filter Set

/-! ## Vanishing jets -/

/-- A vanishing jet forces a vanishing analytic germ. -/
theorem eventuallyEq_zero_of_iteratedDeriv_eq_zero {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (h : ∀ n, iteratedDeriv n f z = 0) :
    ∀ᶠ w in nhds z, f w = 0 := by
  rw [← analyticOrderAt_eq_top]
  by_contra hne
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne
  have hle : ((m + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt f z :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf).mpr fun i _ => h i
  rw [← hm] at hle
  simp only [Nat.cast_add, Nat.cast_one] at hle
  rw [ENat.add_one_le_iff (by simp)] at hle
  exact lt_irrefl _ hle

/-! ## The exponential window strip -/

/-- The open vertical strip of half-width `a`. -/
def momentStrip (a : ℝ) : Set ℂ := {z : ℂ | z.re ∈ Set.Ioo (-a) a}

theorem momentStrip_convex (a : ℝ) : Convex ℝ (momentStrip a) :=
  (convex_Ioo (-a) a).linear_preimage Complex.reLm

theorem zero_mem_momentStrip {a : ℝ} (ha : 0 < a) : (0 : ℂ) ∈ momentStrip a := by
  refine ⟨by simpa using by linarith, by simpa using ha⟩

theorem mul_I_mem_momentStrip {a : ℝ} (ha : 0 < a) (t : ℝ) : ((t : ℂ) * I) ∈ momentStrip a := by
  have hre : ((t : ℂ) * I).re = 0 := by simp
  refine ⟨?_, ?_⟩ <;> rw [hre] <;> linarith

theorem momentStrip_subset_interior {a : ℝ} {μ : Measure ℝ}
    (hμ : Set.Ioo (-a) a ⊆ integrableExpSet id μ) :
    momentStrip a ⊆ {z : ℂ | z.re ∈ interior (integrableExpSet id μ)} :=
  fun _ hz => interior_maximal hμ isOpen_Ioo hz

/-! ## Local-exponential moment determinacy -/

/-- **Local-exponential moment determinacy.**  Two finite measures on `ℝ` sharing one exponential
window and all moments coincide. -/
theorem measure_eq_of_forall_moment_eq {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {a : ℝ} (ha : 0 < a)
    (hμ : Set.Ioo (-a) a ⊆ integrableExpSet id μ)
    (hν : Set.Ioo (-a) a ⊆ integrableExpSet id ν)
    (hmom : ∀ n : ℕ, ∫ x : ℝ, (x : ℂ) ^ n ∂μ = ∫ x : ℝ, (x : ℂ) ^ n ∂ν) :
    μ = ν := by
  have hsubμ := momentStrip_subset_interior hμ
  have hsubν := momentStrip_subset_interior hν
  have hzero := zero_mem_momentStrip ha
  have hanμ : AnalyticOnNhd ℂ (complexMGF id μ) (momentStrip a) :=
    analyticOnNhd_complexMGF.mono hsubμ
  have hanν : AnalyticOnNhd ℂ (complexMGF id ν) (momentStrip a) :=
    analyticOnNhd_complexMGF.mono hsubν
  have hdiff : AnalyticOnNhd ℂ (complexMGF id μ - complexMGF id ν) (momentStrip a) :=
    hanμ.sub hanν
  have hjet : ∀ n, iteratedDeriv n (complexMGF id μ - complexMGF id ν) 0 = 0 := by
    intro n
    rw [iteratedDeriv_sub (hanμ 0 hzero).contDiffAt (hanν 0 hzero).contDiffAt,
      iteratedDeriv_complexMGF (hsubμ hzero) n, iteratedDeriv_complexMGF (hsubν hzero) n]
    simp only [id_eq, zero_mul, Complex.exp_zero, mul_one]
    rw [hmom n, sub_self]
  have hgerm : (complexMGF id μ - complexMGF id ν) =ᶠ[nhds 0] 0 :=
    eventuallyEq_zero_of_iteratedDeriv_eq_zero (hdiff 0 hzero) hjet
  have heq : Set.EqOn (complexMGF id μ - complexMGF id ν) 0 (momentStrip a) :=
    hdiff.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (momentStrip_convex a).isPreconnected hzero hgerm
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have hmem := heq (mul_I_mem_momentStrip ha t)
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hmem
  rw [← complexMGF_id_mul_I, ← complexMGF_id_mul_I, hmem]

end HTGeometry
