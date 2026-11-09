import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Separation.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination

/-!
# Logarithmic rigidity of a shared exponential clock

Continuous exponential coordinates with a shared clock have proportional
logarithmic derivatives, even when no regularity is assumed of the clock.
Locally normalized logarithms have a continuous defect in a countable
period set, hence a constant defect. For entire numerators and denominators,
the cleared differential identity extends over the complex plane.
-/

open Filter Topology Complex Set
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory



/-- Two exponential coordinates with a common, possibly discontinuous clock
have a locally constant normalized logarithmic defect. -/
theorem common_exponential_clock_log_defect
    {f g : ℝ → ℂ} {a b : ℂ} (hf : Continuous f) (hg : Continuous g)
    (hclock : ∀ t, ∃ u : ℂ, f t = Complex.exp (a * u) ∧
      g t = Complex.exp (b * u)) (t₀ : ℝ) :
    (fun t => b * Complex.log (f t / f t₀) - a * Complex.log (g t / g t₀))
      =ᶠ[𝓝 t₀] fun _ => 0 := by
  have hfn (t : ℝ) : f t ≠ 0 := by
    obtain ⟨u, hu, _⟩ := hclock t
    rw [hu]
    exact Complex.exp_ne_zero _
  have hgn (t : ℝ) : g t ≠ 0 := by
    obtain ⟨u, _, hu⟩ := hclock t
    rw [hu]
    exact Complex.exp_ne_zero _
  let R : ℝ → ℂ := fun t =>
    b * Complex.log (f t / f t₀) - a * Complex.log (g t / g t₀)
  let L : ℤ × ℤ → ℂ := fun k =>
    b * (k.1 : ℂ) * (2 * Real.pi * Complex.I) -
      a * (k.2 : ℂ) * (2 * Real.pi * Complex.I)
  have hRrange : Set.range R ⊆ Set.range L := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨u, hu, hv⟩ := hclock t
    obtain ⟨u₀, hu₀, hv₀⟩ := hclock t₀
    have hfr : f t / f t₀ = Complex.exp (a * (u - u₀)) := by
      rw [hu, hu₀, ← Complex.exp_sub]
      congr 1
      ring
    have hgr : g t / g t₀ = Complex.exp (b * (u - u₀)) := by
      rw [hv, hv₀, ← Complex.exp_sub]
      congr 1
      ring
    obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp
      ((Complex.exp_log (div_ne_zero (hfn t) (hfn t₀))).trans hfr)
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp
      ((Complex.exp_log (div_ne_zero (hgn t) (hgn t₀))).trans hgr)
    refine ⟨(m, n), ?_⟩
    dsimp [L, R]
    rw [hm, hn]
    ring
  have hcount : (Set.range R).Countable :=
    (Set.countable_range L).mono hRrange
  let U : Set ℝ := {t | f t / f t₀ ∈ Complex.slitPlane ∧
    g t / g t₀ ∈ Complex.slitPlane}
  have hUopen : IsOpen U :=
    ((Complex.isOpen_slitPlane.preimage (hf.div_const _)).inter
      (Complex.isOpen_slitPlane.preimage (hg.div_const _)))
  have hU₀ : t₀ ∈ U := by simp [U, hfn t₀, hgn t₀]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen t₀ hU₀
  have hRc : ContinuousOn R (Metric.ball t₀ ε) :=
    (((hf.div_const _).continuousOn.clog (fun t ht => (hball ht).1)).const_mul b).sub
      (((hg.div_const _).continuousOn.clog (fun t ht => (hball ht).2)).const_mul a)
  have hsingle : (R '' Metric.ball t₀ ε).Subsingleton :=
    hcount.isTotallyDisconnected _ (Set.image_subset_range _ _)
      (Metric.isPreconnected_ball.image R hRc)
  have hR₀ : R t₀ = 0 := by simp [R, hfn t₀, hgn t₀]
  filter_upwards [Metric.ball_mem_nhds t₀ hε] with t ht
  exact (hsingle ⟨t, ht, rfl⟩ ⟨t₀, Metric.mem_ball_self hε, rfl⟩).trans hR₀

/-- Orbit preservation alone forces proportional logarithmic derivatives;
no differentiability or continuity of the chosen clock is required. -/
theorem common_exponential_clock_log_deriv
    {f g : ℝ → ℂ} {a b f' g' : ℂ} {t₀ : ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hclock : ∀ t, ∃ u : ℂ, f t = Complex.exp (a * u) ∧
      g t = Complex.exp (b * u))
    (hfd : HasDerivAt f f' t₀) (hgd : HasDerivAt g g' t₀) :
    b * (f' / f t₀) = a * (g' / g t₀) := by
  obtain ⟨u, hu, hv⟩ := hclock t₀
  have hfn : f t₀ ≠ 0 := hu ▸ Complex.exp_ne_zero _
  have hgn : g t₀ ≠ 0 := hv ▸ Complex.exp_ne_zero _
  have hfl := (hfd.div_const (f t₀)).clog_real (by simp [hfn])
  have hgl := (hgd.div_const (g t₀)).clog_real (by simp [hgn])
  simp only [div_self hfn, div_self hgn, div_one] at hfl hgl
  have hd := (hfl.const_mul b).sub (hgl.const_mul a)
  have heq := common_exponential_clock_log_defect hf hg hclock t₀
  have hz := (hasDerivAt_const t₀ (0 : ℂ)).congr_of_eventuallyEq heq
  exact sub_eq_zero.mp (hd.unique hz)

#print axioms common_exponential_clock_log_deriv


private theorem entire_eq_of_real_eq {F G : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F Set.univ) (hG : AnalyticOnNhd ℂ G Set.univ)
    (hreal : ∀ t : ℝ, F t = G t) : F = G := by
  apply hF.eq_of_frequently_eq hG (z₀ := 0)
  have hu : Tendsto (fun n : ℕ => (((1 / ((n : ℝ) + 1)) : ℝ) : ℂ))
      atTop (𝓝[≠] ((0 : ℝ) : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact (Complex.continuous_ofReal.tendsto 0).comp
        tendsto_one_div_add_atTop_nhds_zero_nat
    · filter_upwards with n
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_zero,
        Complex.ofReal_eq_zero]
      positivity
  exact hu.frequently (Filter.Eventually.of_forall fun n => hreal _).frequently

/-- Clearing denominators extends the clock identity from the real orbit
across every complex zero and pole. -/
theorem common_exponential_clock_cross_identity
    {N D M E : ℂ → ℂ} {a b : ℂ}
    (hN : AnalyticOnNhd ℂ N Set.univ) (hD : AnalyticOnNhd ℂ D Set.univ)
    (hM : AnalyticOnNhd ℂ M Set.univ) (hE : AnalyticOnNhd ℂ E Set.univ)
    (hDr : ∀ t : ℝ, D t ≠ 0) (hEr : ∀ t : ℝ, E t ≠ 0)
    (hclock : ∀ t : ℝ, ∃ u : ℂ,
      N t / D t = Complex.exp (a * u) ∧ M t / E t = Complex.exp (b * u))
    (z : ℂ) :
    b * (deriv N z * D z - N z * deriv D z) * M z * E z =
      a * (deriv M z * E z - M z * deriv E z) * N z * D z := by
  have hNd : Differentiable ℂ N := fun z => (hN z trivial).differentiableAt
  have hDd : Differentiable ℂ D := fun z => (hD z trivial).differentiableAt
  have hMd : Differentiable ℂ M := fun z => (hM z trivial).differentiableAt
  have hEd : Differentiable ℂ E := fun z => (hE z trivial).differentiableAt
  have hNc : Continuous (fun t : ℝ => N t / D t) :=
    (hNd.continuous.comp Complex.continuous_ofReal).div
      (hDd.continuous.comp Complex.continuous_ofReal) hDr
  have hMc : Continuous (fun t : ℝ => M t / E t) :=
    (hMd.continuous.comp Complex.continuous_ofReal).div
      (hEd.continuous.comp Complex.continuous_ofReal) hEr
  have hreal (t : ℝ) :
      b * (deriv N t * D t - N t * deriv D t) * M t * E t =
        a * (deriv M t * E t - M t * deriv E t) * N t * D t := by
    have hNd' := (hNd t).hasDerivAt.comp_ofReal
    have hDd' := (hDd t).hasDerivAt.comp_ofReal
    have hMd' := (hMd t).hasDerivAt.comp_ofReal
    have hEd' := (hEd t).hasDerivAt.comp_ofReal
    have h := common_exponential_clock_log_deriv hNc hMc hclock
      (hNd'.div hDd' (hDr t)) (hMd'.div hEd' (hEr t))
    obtain ⟨u, hu, hv⟩ := hclock t
    have hn : N t ≠ 0 := by
      intro hn
      simp only [hn, zero_div] at hu
      exact Complex.exp_ne_zero _ hu.symm
    have hm : M t ≠ 0 := by
      intro hm
      simp only [hm, zero_div] at hv
      exact Complex.exp_ne_zero _ hv.symm
    field_simp [hDr t, hEr t, hn, hm] at h
    linear_combination h
  have hleft : AnalyticOnNhd ℂ
      (fun z => b * (deriv N z * D z - N z * deriv D z) * M z * E z) Set.univ := by
    intro z _
    exact (analyticAt_const.mul (((hN z trivial).deriv.mul (hD z trivial)).sub
      ((hN z trivial).mul (hD z trivial).deriv))).mul
      (hM z trivial) |>.mul (hE z trivial)
  have hright : AnalyticOnNhd ℂ
      (fun z => a * (deriv M z * E z - M z * deriv E z) * N z * D z) Set.univ := by
    intro z _
    exact (analyticAt_const.mul (((hM z trivial).deriv.mul (hE z trivial)).sub
      ((hM z trivial).mul (hE z trivial).deriv))).mul
      (hN z trivial) |>.mul (hD z trivial)
  exact congrFun (entire_eq_of_real_eq hleft hright hreal) z

#print axioms common_exponential_clock_cross_identity

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
