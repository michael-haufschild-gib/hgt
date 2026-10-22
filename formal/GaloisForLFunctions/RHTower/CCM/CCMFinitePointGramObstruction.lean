import GaloisForLFunctions.RHTower.CCM.CCMConstrainedPointCapacity

/-!
# Finite physical point Gram forms cannot supply a Weil lower bound

An exact smooth constrained source can isolate any one of finitely many distinct physical
sample points while its full Weil quadratic is arbitrarily small.  Consequently any finite
sample Gram with a positive diagonal fails domination by that quadratic.  Every matrix cross
term is retained in the statement; the constructed witness makes those terms exactly zero.

This concerns physical source samples, not Fourier samples, integrated features, or the actual
xi Hankel form.  It is a test of a particular proposed arithmetic Gram construction, not RH.
-/

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower

/-- Smooth, exactly constrained Kronecker samples with arbitrarily small full source energy. -/
theorem exists_ccmPolarConstrained_finite_point_isolator
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : SuzukiPositiveAperture) (x : ι → ℝ) (hxi : Function.Injective x)
    (i : ι) (hi : |x i| < a.1) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : CCMComplexSmoothInteriorSource a,
      IsPolarConstrained a g.toCCMFormVector ∧
      (∀ j, g (x j) = if j = i then 1 else 0) ∧
      ‖g.toCCMFormVector‖ < ε ∧
      |ccmRestrictedWeilSourceQuadratic a g.toCCMFormVector| < ε := by
  classical
  let s : Finset ℝ := (Finset.univ.erase i).image x
  have hnot : x i ∉ (s : Set ℝ) := by
    intro hmem
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hmem
    exact (Finset.mem_erase.mp hj).1 (hxi hji)
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.mp s.finite_toSet.isClosed.isOpen_compl (x i) hnot
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp
    (continuous_ccmRestrictedWeilSourceQuadratic a).continuousAt ε hε
  obtain ⟨g, hg, hgi, hgn, hgz⟩ := exists_ccmPolarConstrained_point_one_local_norm_lt
    a (x i) hi r hr (min ε δ) (lt_min hε hδ)
  refine ⟨g, hg, ?_, hgn.trans_le (min_le_left _ _), ?_⟩
  · intro j
    split_ifs with hji
    · simpa only [hji] using hgi
    · apply hgz
      by_contra hdist
      have hm : x j ∈ Metric.ball (x i) r := by
        simpa only [Metric.mem_ball, Real.dist_eq] using lt_of_not_ge hdist
      apply hball hm
      exact Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩, rfl⟩
  · have hdist : dist g.toCCMFormVector (0 : CCMArchimedeanFormDomain a) < δ := by
      simpa only [dist_zero_right] using hgn.trans_le (min_le_right _ _)
    simpa only [ccmRestrictedWeilSourceQuadratic_zero, dist_zero_right, Real.norm_eq_abs]
      using hd hdist

/-- Any finite sample matrix with a positive real diagonal fails a uniform energy domination.
No positivity or diagonalization premise for the matrix is needed. -/
theorem not_ccmFinitePointGram_dominated_by_source
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : SuzukiPositiveAperture) (x : ι → ℝ) (hxi : Function.Injective x)
    (i : ι) (hi : |x i| < a.1) (K : ι → ι → ℂ) (hK : 0 < (K i i).re) :
    ¬ ∃ C : ℝ, ∀ g : CCMComplexSmoothInteriorSource a,
      IsPolarConstrained a g.toCCMFormVector →
        (∑ j, ∑ k, star (g (x j)) * K j k * g (x k)).re ≤
          C * |ccmRestrictedWeilSourceQuadratic a g.toCCMFormVector| := by
  classical
  rintro ⟨C, hC⟩
  obtain ⟨g, hg, hgj, _, hgq⟩ := exists_ccmPolarConstrained_finite_point_isolator
    a x hxi i hi ((K i i).re / (|C| + 1)) (by positivity)
  have hval := hC g hg
  have hGram : (∑ j, ∑ k, star (g (x j)) * K j k * g (x k)) = K i i := by
    calc
      _ = ∑ k, star (g (x i)) * K i k * g (x k) := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          simp only [hgj j, if_neg hji, star_zero, zero_mul, Finset.sum_const_zero]
        · simp
      _ = K i i := by
        rw [Finset.sum_eq_single i]
        · simp [hgj i]
        · intro k _ hki
          simp only [hgj k, if_neg hki, mul_zero]
        · simp
  rw [hGram] at hval
  have hsmall := (lt_div_iff₀ (show 0 < |C| + 1 by positivity)).mp hgq
  have hle := mul_le_mul_of_nonneg_right (le_abs_self C)
    (abs_nonneg (ccmRestrictedWeilSourceQuadratic a g.toCCMFormVector))
  nlinarith [abs_nonneg (ccmRestrictedWeilSourceQuadratic a g.toCCMFormVector)]

end RHTower
