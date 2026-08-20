import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# The quadratic-cumulant characterization of the Gaussian law

If the moment generating function of a real random variable is finite on a neighbourhood of the
origin and equals `exp(m t + v t²/2)` there, then the law of the variable is exactly
`gaussianReal m v`.  The converse is mathlib's `mgf_gaussianReal`.

The proof needs no Marcinkiewicz theory: the complex moment generating function is analytic on the
open vertical strip `|Re z| < δ`, agrees with the entire function `exp(m z + v z²/2)` on the real
segment, hence on the whole strip; the imaginary axis lies in that strip, so the characteristic
functions agree and `Measure.ext_of_charFun` finishes.
-/

open MeasureTheory Filter Complex
open scoped Topology ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

namespace ProbabilityTheory

open _root_.ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}

/-- The entire Gaussian moment generating function on the complex plane. -/
noncomputable def gaussianComplexMGF (m : ℝ) (v : ℝ≥0) (z : ℂ) : ℂ :=
  Complex.exp ((m : ℂ) * z + (v : ℂ) * z ^ 2 / 2)

theorem analyticOnNhd_gaussianComplexMGF (m : ℝ) (v : ℝ≥0) (S : Set ℂ) :
    AnalyticOnNhd ℂ (gaussianComplexMGF m v) S := by
  intro z _
  unfold gaussianComplexMGF
  fun_prop

/-- **The quadratic-cumulant characterization of the Gaussian law.**  A moment generating function
that is finite near the origin and quadratic in the exponent there forces the law. -/
theorem map_eq_gaussianReal_of_mgf_quadratic [IsProbabilityMeasure μ]
    (hX : AEMeasurable X μ) {δ : ℝ} (hδ : 0 < δ)
    (hint : Set.Ioo (-δ) δ ⊆ integrableExpSet X μ) {m : ℝ} {v : ℝ≥0}
    (hmgf : ∀ t ∈ Set.Ioo (-δ) δ, mgf X μ t = Real.exp (m * t + v * t ^ 2 / 2)) :
    μ.map X = gaussianReal m v := by
  classical
  set S : Set ℂ := {z : ℂ | z.re ∈ Set.Ioo (-δ) δ} with hS
  have hSsub : S ⊆ {z : ℂ | z.re ∈ interior (integrableExpSet X μ)} := by
    intro z hz
    exact interior_maximal hint isOpen_Ioo hz
  have hSopen : IsOpen S := isOpen_Ioo.preimage Complex.continuous_re
  have hSconn : IsPreconnected S :=
    ((convex_Ioo (-δ) δ).linear_preimage Complex.reLm).isPreconnected
  have hf : AnalyticOnNhd ℂ (complexMGF X μ) S :=
    (analyticOnNhd_complexMGF (X := X) (μ := μ)).mono hSsub
  have hg : AnalyticOnNhd ℂ (gaussianComplexMGF m v) S :=
    analyticOnNhd_gaussianComplexMGF m v S
  have hzeroS : (0 : ℂ) ∈ S := by
    simp only [hS, Set.mem_setOf_eq, Complex.zero_re]
    exact ⟨by linarith, hδ⟩
  -- the two functions agree on the real segment
  have hreal : ∀ x : ℝ, x ∈ Set.Ioo (-δ) δ →
      complexMGF X μ (x : ℂ) = gaussianComplexMGF m v (x : ℂ) := by
    intro x hx
    rw [complexMGF_ofReal, hmgf x hx, gaussianComplexMGF, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  -- hence frequently near the origin
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ),
      complexMGF X μ z = gaussianComplexMGF m v z := by
    rw [frequently_iff_seq_forall]
    refine ⟨fun n : ℕ => ((δ / 2 / (n + 1) : ℝ) : ℂ), ?_, fun n => ?_⟩
    · rw [tendsto_nhdsWithin_iff]
      constructor
      · have h1 : Tendsto (fun n : ℕ => (δ / 2 / (n + 1) : ℝ)) atTop (𝓝 0) := by
          simpa using (tendsto_const_nhds (x := δ / 2) (f := atTop (α := ℕ))).div_atTop
            (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
        have h2 := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp h1
        simpa [Function.comp_def] using h2
      · filter_upwards with n
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
        positivity
    · refine hreal _ ?_
      constructor
      · have : (0:ℝ) < δ / 2 / (n + 1) := by positivity
        linarith
      · have h1 : (0:ℝ) < (n : ℝ) + 1 := by positivity
        rw [div_lt_iff₀ h1]
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have heq : Set.EqOn (complexMGF X μ) (gaussianComplexMGF m v) S :=
    hf.eqOn_of_preconnected_of_frequently_eq hg hSconn hzeroS hfreq
  -- compare characteristic functions
  haveI : IsProbabilityMeasure (μ.map X) := ⟨by rw [Measure.map_apply_of_aemeasurable hX MeasurableSet.univ]; simp⟩
  refine Measure.ext_of_charFun ?_
  funext t
  have hmem : ((t : ℂ) * Complex.I) ∈ S := by
    simp only [hS, Set.mem_setOf_eq, Complex.mul_I_re, Complex.ofReal_im, neg_zero]
    exact ⟨by linarith, hδ⟩
  have h1 : charFun (μ.map X) t = gaussianComplexMGF m v ((t : ℂ) * Complex.I) := by
    rw [← complexMGF_mul_I hX t]
    exact heq hmem
  rw [h1, charFun_gaussianReal, gaussianComplexMGF]
  congr 1
  have hI : ((t : ℂ) * Complex.I) ^ 2 = -(t : ℂ) ^ 2 := by
    rw [mul_pow, Complex.I_sq]
    ring
  rw [hI]
  ring

/-- The converse direction, from mathlib: the Gaussian moment generating function is exactly the
exponential of the quadratic cumulant generator. -/
theorem mgf_eq_quadratic_of_map_eq_gaussianReal {m : ℝ} {v : ℝ≥0}
    (h : μ.map X = gaussianReal m v) (t : ℝ) :
    mgf X μ t = Real.exp (m * t + v * t ^ 2 / 2) :=
  mgf_gaussianReal h t

end ProbabilityTheory

end GaloisForLFunctions.HTGeometry
