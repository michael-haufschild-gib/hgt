import GaloisForLFunctions.HTGeometry.BohrHullContinuity

/-!
# Powers do not merge boundary states

A continuous function whose `n`-th power is constant takes values in the finite set of `n`-th roots
of unity, so on a preconnected domain it is constant.  If in addition the ratio of two such
functions tends to one along some nontrivial filter, that constant is one and the functions agree.

For the boundary states of an exponential carrier the ratio does tend to one, because the carrier
decays high in the upper half plane and the constant term does not vanish.  Passing to `n`-th powers
therefore does not identify distinct phases: the boundary at every power is still a faithful copy of
the phase torus.
-/

open Filter Topology Set

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type*}

theorem finite_setOf_pow_eq_one {n : ℕ} (hn : n ≠ 0) : {w : ℂ | w ^ n = 1}.Finite := by
  have hp : (Polynomial.X ^ n - 1 : Polynomial ℂ) ≠ 0 := by
    intro h
    have h0 := congrArg (Polynomial.eval 0) h
    simp [zero_pow hn] at h0
  refine (Polynomial.finite_setOf_isRoot hp).subset fun w hw => ?_
  have hw' : w ^ n = 1 := hw
  show (Polynomial.X ^ n - 1 : Polynomial ℂ).IsRoot w
  simp [Polynomial.IsRoot, sub_eq_zero.mpr hw']

/-- **A continuous root of unity is constant.**  On a preconnected space a continuous function whose
`n`-th power is one takes a single value. -/
theorem constant_of_pow_eq_one {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {q : X → ℂ} (hq : Continuous q) {n : ℕ} (hn : n ≠ 0) (hpow : ∀ x, q x ^ n = 1) (x y : X) :
    q x = q y := by
  classical
  haveI hfin : Finite {w : ℂ // w ^ n = 1} := (finite_setOf_pow_eq_one hn).to_subtype
  haveI : DiscreteTopology {w : ℂ // w ^ n = 1} := inferInstance
  have hcont : Continuous fun x => (⟨q x, hpow x⟩ : {w : ℂ // w ^ n = 1}) :=
    hq.subtype_mk _
  have hconst := isPreconnected_univ.constant (f := fun x => (⟨q x, hpow x⟩ : {w : ℂ // w ^ n = 1}))
    hcont.continuousOn (Set.mem_univ x) (Set.mem_univ y)
  exact congrArg Subtype.val hconst

/-- **Equal powers with a common asymptotic ratio force equality.** -/
theorem eq_of_pow_eq_of_tendsto_ratio_one {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [Nonempty X] {f g : X → ℂ} {n : ℕ} (hn : n ≠ 0) (hf : Continuous f) (hg : Continuous g)
    (hgne : ∀ x, g x ≠ 0) (hpow : ∀ x, f x ^ n = g x ^ n)
    {κ : Type*} {l : Filter κ} [l.NeBot] {u : κ → X}
    (hlim : Tendsto (fun k => f (u k) / g (u k)) l (nhds 1)) :
    f = g := by
  classical
  set q : X → ℂ := fun x => f x / g x with hqdef
  have hqc : Continuous q := hf.div hg hgne
  have hqpow : ∀ x, q x ^ n = 1 := by
    intro x
    rw [hqdef, div_pow, hpow x, div_self (pow_ne_zero n (hgne x))]
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have hconst : ∀ x, q x = q x₀ := fun x => constant_of_pow_eq_one hqc hn hqpow x x₀
  have hcompose : Tendsto (fun k => q (u k)) l (nhds (q x₀)) := by
    refine Tendsto.congr (fun k => (hconst (u k)).symm) tendsto_const_nhds
  have hone : q x₀ = 1 := tendsto_nhds_unique hcompose hlim
  funext x
  have hx : q x = 1 := by rw [hconst x, hone]
  rw [hqdef] at hx
  have hmul := congrArg (fun w : ℂ => w * g x) hx
  simpa [div_mul_cancel₀ _ (hgne x)] using hmul

/-- The carrier decays along the vertical axis. -/
theorem tendsto_cexpSeriesCarrier_vertical {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) (hpos : ∀ i, 0 < omega i) :
    Tendsto (fun k : ℕ => cexpSeriesCarrier a omega ((k : ℂ) * Complex.I)) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨Y, hY0, hY⟩ := exists_im_bound_norm_cexpSeriesCarrier_le h hpos
    (show (0 : ℝ) < ε / 2 by linarith)
  obtain ⟨N, hN⟩ := exists_nat_gt Y
  refine ⟨N, fun k hk => ?_⟩
  have him : ((k : ℂ) * Complex.I).im = (k : ℝ) := by
    simp
  have hYk : Y ≤ ((k : ℂ) * Complex.I).im := by
    rw [him]
    have : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hbound := hY _ hYk
  rw [dist_zero_right]
  linarith


/-- **The boundary at every power is faithful.**  If the constant term is nonzero and the shifted
carriers of two phase families have equal `n`-th powers, the phases coincide.  The carriers vanish
high in the upper half plane, so the ratio of the shifted carriers tends to one; being a continuous
root of unity it is constant, hence identically one. -/
theorem cexpSeriesCarrier_phase_injective_pow {a : ι → ℂ} {omega : ι → ℝ} {lam mu : ι → ℂ}
    (h : ExpSeriesNormallySummable a omega) (hpos : ∀ i, 0 < omega i)
    (hlam : ∀ i, ‖lam i‖ ≤ 1) (hmu : ∀ i, ‖mu i‖ ≤ 1)
    (hane : ∀ i, a i ≠ 0) (hinj : Function.Injective omega)
    {c : ℂ} (hc : c ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (hnzM : ∀ z, c + cexpSeriesCarrier (fun i => a i * mu i) omega z ≠ 0)
    (hpow : ∀ z, (c + cexpSeriesCarrier (fun i => a i * lam i) omega z) ^ n
      = (c + cexpSeriesCarrier (fun i => a i * mu i) omega z) ^ n) :
    lam = mu := by
  classical
  have hL := expSeriesNormallySummable_phase h hlam
  have hM := expSeriesNormallySummable_phase h hmu
  have hLc : Continuous fun z => c + cexpSeriesCarrier (fun i => a i * lam i) omega z :=
    continuous_const.add (differentiable_cexpSeriesCarrier hL).continuous
  have hMc : Continuous fun z => c + cexpSeriesCarrier (fun i => a i * mu i) omega z :=
    continuous_const.add (differentiable_cexpSeriesCarrier hM).continuous
  have hLlim : Tendsto
      (fun k : ℕ => c + cexpSeriesCarrier (fun i => a i * lam i) omega ((k : ℂ) * Complex.I))
      atTop (nhds c) := by
    have := tendsto_cexpSeriesCarrier_vertical hL hpos
    simpa using tendsto_const_nhds.add this
  have hMlim : Tendsto
      (fun k : ℕ => c + cexpSeriesCarrier (fun i => a i * mu i) omega ((k : ℂ) * Complex.I))
      atTop (nhds c) := by
    have := tendsto_cexpSeriesCarrier_vertical hM hpos
    simpa using tendsto_const_nhds.add this
  have hratio : Tendsto
      (fun k : ℕ => (c + cexpSeriesCarrier (fun i => a i * lam i) omega ((k : ℂ) * Complex.I))
        / (c + cexpSeriesCarrier (fun i => a i * mu i) omega ((k : ℂ) * Complex.I)))
      atTop (nhds 1) := by
    have hdiv := hLlim.div hMlim hc
    rwa [div_self hc] at hdiv
  have hfg := eq_of_pow_eq_of_tendsto_ratio_one (X := ℂ) hn hLc hMc hnzM hpow hratio
  have hcarrier : cexpSeriesCarrier (fun i => a i * lam i) omega
      = cexpSeriesCarrier (fun i => a i * mu i) omega := by
    funext z
    have := congrFun hfg z
    simpa using this
  have hnorm := summable_norm_of_expSeriesNormallySummable h
  refine cexpSeriesCarrier_phase_injective ?_ ?_ hane hinj hcarrier
  · refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) hnorm
    rw [norm_mul]
    calc ‖a i‖ * ‖lam i‖ ≤ ‖a i‖ * 1 := mul_le_mul_of_nonneg_left (hlam i) (norm_nonneg _)
      _ = ‖a i‖ := mul_one _
  · refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) hnorm
    rw [norm_mul]
    calc ‖a i‖ * ‖mu i‖ ≤ ‖a i‖ * 1 := mul_le_mul_of_nonneg_left (hmu i) (norm_nonneg _)
      _ = ‖a i‖ := mul_one _

end

end GaloisForLFunctions
