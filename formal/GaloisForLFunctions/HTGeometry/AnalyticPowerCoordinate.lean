import GaloisForLFunctions.HTGeometry.PuncturedPowerRoot
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

open Filter Topology Set Metric
namespace GaloisForLFunctions.HTGeometry

/-- The inverse of an analytic open partial homeomorphism is analytic at every regular point. -/
theorem analyticAt_openPartialHomeomorph_symm
    (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ} (ha : a ∈ e.source)
    (he : AnalyticAt ℂ e a) (hd : deriv e a ≠ 0) :
    AnalyticAt ℂ e.symm (e a) := by
  apply (analyticAt_comp_iff_of_deriv_ne_zero he hd).mp
  have h : (e.symm ∘ e) =ᶠ[𝓝 a] id := e.eventually_left_inverse ha
  exact analyticAt_id.congr h.symm

/-- A finite-order zero admits an exact analytic power coordinate inside any neighborhood. -/
theorem exists_analytic_power_coordinate {f : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (hf : AnalyticAt ℂ f a) (hm : 0 < m) (ho : analyticOrderAt f a = m)
    {U : Set ℂ} (hU : U ∈ 𝓝 a) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      a ∈ e.source ∧ e.source ⊆ U ∧ e a = 0 ∧
      AnalyticOnNhd ℂ e e.source ∧ AnalyticOnNhd ℂ e.symm e.target ∧
      (∀ z ∈ e.source, deriv e z ≠ 0) ∧
      ∀ z ∈ e.source, f z = (e z) ^ m := by
  obtain ⟨u, hu, hu0, hfu⟩ := hf.analyticOrderAt_eq_natCast.mp ho
  have huord : analyticOrderAt u a = 0 := hu.analyticOrderAt_eq_zero.mpr hu0
  obtain ⟨v, hv, hvp⟩ := exists_analyticAt_power_root_of_dvd_order hm hu
    (by simp [huord]) (by simp [analyticOrderNatAt, huord])
  have hva : v a ≠ 0 := by
    intro h
    have hvpa := hvp.self_of_nhds
    simp only [Pi.pow_apply, h, zero_pow (Nat.ne_of_gt hm)] at hvpa
    exact hu0 hvpa.symm
  let s : ℂ → ℂ := fun z => (z - a) * v z
  have hs : AnalyticAt ℂ s a := (analyticAt_id.sub analyticAt_const).mul hv
  have hsa : s a = 0 := by simp [s]
  have hds : deriv s a = v a := by
    have h := ((hasDerivAt_id a).sub_const a).mul hv.differentiableAt.hasDerivAt
    change HasDerivAt s (1 * v a + (a - a) * deriv v a) a at h
    simpa only [one_mul, sub_self, zero_mul, add_zero] using h.deriv
  have hs0 : deriv s a ≠ 0 := hds ▸ hva
  have hpow : ∀ᶠ z in 𝓝 a, f z = s z ^ m := by
    filter_upwards [hfu, hvp] with z h1 h2
    change v z ^ m = u z at h2
    simpa only [s, mul_pow, h2, smul_eq_mul] using h1
  have hev : ∀ᶠ z in 𝓝 a,
      z ∈ U ∧ AnalyticAt ℂ s z ∧ deriv s z ≠ 0 ∧ f z = s z ^ m := by
    have hU' : ∀ᶠ z in 𝓝 a, z ∈ U := hU
    exact hU'.and (hs.eventually_analyticAt.and
      ((hs.deriv.continuousAt.eventually (isOpen_ne.mem_nhds hs0)).and hpow))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  let hd := hs.hasStrictDerivAt.hasStrictFDerivAt_equiv hs0
  let e₀ := hd.toOpenPartialHomeomorph s
  let e := e₀.restrOpen (ball a r) isOpen_ball
  have heq : (e : ℂ → ℂ) = s := rfl
  have hsrc : ∀ z ∈ e.source, z ∈ ball a r := fun z hz => hz.2
  have hea : a ∈ e.source := ⟨hd.mem_toOpenPartialHomeomorph_source, mem_ball_self hr⟩
  have hea' : AnalyticOnNhd ℂ e e.source := by
    intro z hz
    change AnalyticAt ℂ s z
    exact (hball (hsrc z hz)).2.1
  have hed : ∀ z ∈ e.source, deriv e z ≠ 0 := by
    intro z hz
    change deriv s z ≠ 0
    exact (hball (hsrc z hz)).2.2.1
  refine ⟨e, hea, fun z hz => (hball (hsrc z hz)).1, hsa, hea', ?_, hed, ?_⟩
  · intro z hz
    have hx := e.map_target hz
    have h := analyticAt_openPartialHomeomorph_symm e hx (hea' _ hx) (hed _ hx)
    simpa only [e.right_inv hz] using h
  · intro z hz
    exact (hball (hsrc z hz)).2.2.2

end GaloisForLFunctions.HTGeometry
