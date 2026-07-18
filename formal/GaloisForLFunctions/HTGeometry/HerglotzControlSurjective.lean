import GaloisForLFunctions.HTGeometry.HerglotzControlMap
import GaloisForLFunctions.HTGeometry.ControlPullbackNowhereDense

/-!
# Surjectivity of the bounded-reweighting Cauchy-jet control map

Indicator functions of measurable sets are bounded reweightings, and the control map sends the
indicator of `S` to the vector of Cauchy kernels integrated over `S`.  A real-linear functional
annihilating the range therefore annihilates every such set integral, and exchanging the finite jet
sum with the integral turns this into the real-part hypothesis of the signed Cauchy-jet detector.

For a finite measure with infinite support the detector forces the functional's coefficient packet
to vanish, so no nonzero real functional annihilates the range: the control map is surjective.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Each Cauchy kernel coordinate is integrable against a finite measure. -/
theorem integrable_cauchyJetKernel (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x : ι → ℂ) (hne : ∀ i, (x i).im ≠ 0) (n : ι → ℕ) (s : jetIndex n) :
    Integrable (fun t : ℝ => cauchyJetKernel x n t s) μ := by
  refine Integrable.mono' (integrable_const (cauchyJetKernelBound x n s))
    (aestronglyMeasurable_cauchyJetKernel μ x n s) ?_
  filter_upwards with t
  exact norm_cauchyJetKernel_le x hne n s t

omit [DecidableEq ι] in
/-- The control map sends the indicator of a set to the Cauchy kernels integrated over that set. -/
theorem herglotzControl_indicatorConstLp (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x : ι → ℂ) (hne : ∀ i, (x i).im ≠ 0) (n : ι → ℕ)
    {S : Set ℝ} (hS : MeasurableSet S) (s : jetIndex n) :
    herglotzControl μ x hne n
        (indicatorConstLp ⊤ hS (measure_ne_top μ S) (1 : ℝ)) s =
      ∫ t in S, cauchyJetKernel x n t s ∂μ := by
  rw [herglotzControl_apply]
  have hae : ∀ᵐ t ∂μ,
      (((indicatorConstLp ⊤ hS (measure_ne_top μ S) (1 : ℝ)) t : ℝ) : ℂ) *
          cauchyJetKernel x n t s =
        S.indicator (fun t => cauchyJetKernel x n t s) t := by
    filter_upwards [indicatorConstLp_coeFn
      (p := (⊤ : ℝ≥0∞)) (hs := hS) (hμs := measure_ne_top μ S) (c := (1 : ℝ))] with t ht
    rw [ht]
    by_cases h : t ∈ S <;> simp [h]
  rw [integral_congr_ae hae, integral_indicator hS]

omit [DecidableEq ι] in
/-- Exchanging the finite jet sum with the integral over a measurable set. -/
theorem sum_mul_setIntegral_cauchyJetKernel (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x : ι → ℂ) (hne : ∀ i, (x i).im ≠ 0) (n : ι → ℕ)
    (c : jetIndex n → ℂ) (S : Set ℝ) :
    ∑ s : jetIndex n, c s * ∫ t in S, cauchyJetKernel x n t s ∂μ =
      ∫ t in S, (∑ s : jetIndex n, c s * cauchyJetKernel x n t s) ∂μ := by
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl ?_
    intro s _
    rw [integral_const_mul]
  · intro s _
    exact ((integrable_cauchyJetKernel μ x hne n s).restrict).const_mul (c s)

/-- **Surjectivity of the Herglotz control map.**  For a finite measure with infinite support and
distinct upper-half-plane nodes, every finite Cauchy-jet vector is realized by a bounded
reweighting. -/
theorem surjective_herglotzControl (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : μ.support.Infinite)
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) :
    Function.Surjective
      (herglotzControl μ x (fun i => ne_of_gt (hupper i)) n) := by
  classical
  set hne : ∀ i, (x i).im ≠ 0 := fun i => ne_of_gt (hupper i) with hnedef
  apply surjective_of_setIntegral_pairing hsupp x hx hupper n
    (L := (herglotzControl μ x hne n).toLinearMap)
  intro c hc S hS
  have hind := hc (indicatorConstLp ⊤ hS (measure_ne_top μ S) (1 : ℝ))
  have hrw : ∀ s : jetIndex n,
      (herglotzControl μ x hne n)
          (indicatorConstLp ⊤ hS (measure_ne_top μ S) (1 : ℝ)) s =
        ∫ t in S, cauchyJetKernel x n t s ∂μ :=
    fun s => herglotzControl_indicatorConstLp μ x hne n hS s
  simp only [ContinuousLinearMap.coe_coe, hrw] at hind
  rw [← sum_mul_setIntegral_cauchyJetKernel μ x hne n c S]
  exact hind

/-- **Generic nondegeneracy of bounded reweightings.**  For a finite measure with infinite support,
the bounded reweightings on which a countable family of nonzero polynomial jet relations all fail to
degenerate form a dense set in `L^∞(μ;ℝ)`.  Controllability of the Cauchy-jet map turns each
degeneracy locus into a nowhere-dense set, and the countable Baire backbone does the rest. -/
theorem dense_nondegenerate_reweightings
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hsupp : μ.support.Infinite)
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (P : ℕ → MvPolynomial (jetIndex n) ℂ) (hP : ∀ k, P k ≠ 0) :
    Dense {f : Lp ℝ ⊤ μ | ∀ k,
      MvPolynomial.eval
        (herglotzControl μ x (fun i => ne_of_gt (hupper i)) n f) (P k) ≠ 0} := by
  classical
  exact dense_residual_nondegenerateControls
    (fun _ => herglotzControl μ x (fun i => ne_of_gt (hupper i)) n)
    (fun _ => surjective_herglotzControl μ hsupp x hx hupper n) P hP

end

end GaloisForLFunctions.HTGeometry
