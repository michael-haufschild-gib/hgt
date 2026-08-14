import GaloisForLFunctions.HTGeometry.HerglotzBoundaryMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# The Herglotz representation on the unit disc

A holomorphic function on the open unit disc with nonnegative real part and value one at the centre
is the Poisson integral of a probability measure on the circle.  The boundary densities at radius
`r < 1` already represent the dilations; Prokhorov compactness of the probability measures on the
compact circle produces a cluster point, and weak convergence transfers the representation to it.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory Metric Filter Topology

noncomputable section

theorem continuous_poissonKernel_circle {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    Continuous fun ζ : Circle => _root_.poissonKernel 0 w (ζ : ℂ) := by
  have hne : ∀ ζ : Circle, ((ζ : ℂ) - 0) - (w - 0) ≠ 0 := by
    intro ζ h
    have hzw : (ζ : ℂ) = w := by
      have := sub_eq_zero.mp h
      simpa using this
    rw [mem_ball, dist_zero_right] at hw
    have hnorm : ‖(ζ : ℂ)‖ = 1 := Circle.norm_coe ζ
    rw [hzw] at hnorm
    rw [hnorm] at hw
    exact absurd hw (lt_irrefl 1)
  unfold _root_.poissonKernel
  have hden : ∀ ζ : Circle, ‖((ζ : ℂ) - 0) - (w - 0)‖ ^ 2 ≠ 0 := fun ζ =>
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne ζ))
  fun_prop (disch := exact hden _)

/-- **The Herglotz representation.**  A Carathéodory germ on the unit disc is the Poisson integral
of a probability measure on the circle. -/
theorem exists_herglotz_representation {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hpos : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ (F z).re) (h1 : F 0 = 1) :
    ∃ μ : ProbabilityMeasure Circle, ∀ w ∈ ball (0 : ℂ) 1,
      (F w).re = ∫ ζ : Circle, _root_.poissonKernel 0 w (ζ : ℂ) ∂(μ : Measure Circle) := by
  classical
  set rs : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2) with hrs
  have hden : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 2 := by
    intro n
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hr0 : ∀ n, 0 < rs n := by
    intro n
    have h2 : 1 / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one (hden n)]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    simp only [hrs]
    linarith
  have hr1 : ∀ n, rs n < 1 := by
    intro n
    have h2 : 0 < 1 / ((n : ℝ) + 2) := by positivity
    simp only [hrs]
    linarith
  have hrtend : Tendsto rs atTop (𝓝 1) := by
    have hbig : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    have h1' : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) := hbig.inv_tendsto_atTop
    have hsub := tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ)) |>.sub h1'
    simpa [hrs, one_div] using hsub
  haveI hprob : ∀ n, IsProbabilityMeasure (herglotzBoundaryMeasure F (rs n)) :=
    fun n => isProbabilityMeasure_herglotzBoundaryMeasure (hr0 n) (hr1 n) hF hpos h1
  set μs : ℕ → ProbabilityMeasure Circle :=
    fun n => ⟨herglotzBoundaryMeasure F (rs n), hprob n⟩ with hμs
  obtain ⟨μ, -, hcl⟩ :=
    (isCompact_univ (X := ProbabilityMeasure Circle)).exists_clusterPt
      (f := map μs atTop) (by simp)
  refine ⟨μ, fun w hw => ?_⟩
  set P : BoundedContinuousFunction Circle ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨_, continuous_poissonKernel_circle hw⟩ with hP
  set g : ProbabilityMeasure Circle → ℝ := fun ν => ∫ ζ : Circle, P ζ ∂(ν : Measure Circle) with hg
  have hgc : Continuous g := ProbabilityMeasure.continuous_integral_boundedContinuousFunction P
  have hval : ∀ n, g (μs n) = (F ((rs n : ℂ) * w)).re := by
    intro n
    have hbridge := integral_poissonKernel_herglotzBoundaryMeasure (hr0 n) (hr1 n) hF hpos hw
    simpa [hg, hP, hμs] using hbridge
  have hcontF : ContinuousAt F w := by
    have hopen : IsOpen (ball (0 : ℂ) 1) := isOpen_ball
    exact (hF.differentiableAt (hopen.mem_nhds hw)).continuousAt
  have hargs : Tendsto (fun n : ℕ => ((rs n : ℂ) * w)) atTop (𝓝 w) := by
    have hc : Tendsto (fun n : ℕ => ((rs n : ℝ) : ℂ)) atTop (𝓝 (1 : ℂ)) := by
      simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp hrtend
    simpa using hc.mul (tendsto_const_nhds (x := w))
  have hlim : Tendsto (fun n : ℕ => (F ((rs n : ℂ) * w)).re) atTop (𝓝 (F w).re) :=
    (Complex.continuous_re.tendsto (F w)).comp (hcontF.tendsto.comp hargs)
  have hgtend : Tendsto (fun n => g (μs n)) atTop (𝓝 (F w).re) := by
    refine hlim.congr fun n => (hval n).symm
  have hmaple : map (fun n => g (μs n)) atTop ≤ 𝓝 (F w).re := hgtend
  have hclg : (𝓝 (g μ) ⊓ map (fun n => g (μs n)) atTop).NeBot := by
    haveI : (𝓝 μ ⊓ map μs atTop).NeBot := hcl
    have hmono : map g (𝓝 μ ⊓ map μs atTop)
        ≤ 𝓝 (g μ) ⊓ map (fun n => g (μs n)) atTop := by
      refine le_inf (le_trans (map_mono inf_le_left) hgc.continuousAt) ?_
      calc map g (𝓝 μ ⊓ map μs atTop) ≤ map g (map μs atTop) := map_mono inf_le_right
        _ = map (fun n => g (μs n)) atTop := by
              rw [map_map]
              rfl
    exact Filter.NeBot.mono (Filter.map_neBot (m := g) (f := 𝓝 μ ⊓ map μs atTop)) hmono
  have hne : (𝓝 (g μ) ⊓ 𝓝 (F w).re).NeBot :=
    hclg.mono (inf_le_inf_left _ hmaple)
  exact (eq_of_nhds_neBot hne).symm

end

end GaloisForLFunctions.HTGeometry
