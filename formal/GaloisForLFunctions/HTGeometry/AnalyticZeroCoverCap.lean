import GaloisForLFunctions.HTGeometry.PuncturedPowerRoot
import GaloisForLFunctions.HTGeometry.PuncturedDiskCoverClassification

/-!
# Analytic zeros force finite peripheral power charts

A continuous logarithm cannot exist on a punctured neighborhood of an analytic
zero: it would give roots of every degree, forcing each degree to divide the
finite analytic order. Continuous roots become holomorphic away from the zero
by the corpus root-upgrade theorem.

Combining this obstruction with punctured-disk covering classification, any
continuous punctured lift of an analytic zero lies in a positive power model.
Its chart coordinate extends analytically and has the exact ramification order.
No finite-sheet premise or pre-existing complex atlas on the cover is assumed.
-/

open Filter Topology Function

namespace GaloisForLFunctions.HTGeometry

private theorem eventually_nhds_of_eventually_punctured {P : ℂ → Prop} {a : ℂ}
    (h : ∀ᶠ z in 𝓝[≠] a, P z) :
    ∀ᶠ z in 𝓝[≠] a, ∀ᶠ w in 𝓝 z, P w := by
  have h' := (eventually_nhdsWithin_iff.mp h).eventually_nhds
  filter_upwards [h'.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hza
  have hne : ∀ᶠ w in 𝓝 z, w ≠ a := isOpen_ne.mem_nhds hza
  filter_upwards [hz, hne] with w hw hwa
  exact hw hwa

/-- Continuous punctured roots are holomorphic wherever their analytic power is nonzero. -/
theorem eventually_differentiable_punctured_continuous_root
    {f s : ℂ → ℂ} {a : ℂ} {n : ℕ} (hn : 0 < n) (hf : AnalyticAt ℂ f a)
    (hsc : ∀ᶠ z in 𝓝[≠] a, ContinuousAt s z)
    (hfnz : ∀ᶠ z in 𝓝[≠] a, f z ≠ 0)
    (hpow : ∀ᶠ z in 𝓝[≠] a, s z ^ n = f z) :
    ∀ᶠ z in 𝓝[≠] a, DifferentiableAt ℂ s z := by
  filter_upwards [hsc, hfnz, hf.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    eventually_nhds_of_eventually_punctured hpow] with z hscz hfnzz hfz hpowz
  exact (Bottcher.analyticAt_of_continuousAt_pow_eq hn hscz hfz hfnzz hpowz).differentiableAt

/-- Continuity of a root coordinate suffices for analytic extension in a finite cap chart. -/
theorem analyticAt_update_zero_of_punctured_continuous_root
    {f s : ℂ → ℂ} {a : ℂ} {n : ℕ} (hn : 0 < n)
    (hf : AnalyticAt ℂ f a) (hfa : f a = 0)
    (hsc : ∀ᶠ z in 𝓝[≠] a, ContinuousAt s z)
    (hfnz : ∀ᶠ z in 𝓝[≠] a, f z ≠ 0)
    (hpow : ∀ᶠ z in 𝓝[≠] a, s z ^ n = f z) :
    AnalyticAt ℂ (update s a 0) a :=
  analyticAt_update_zero_of_pow_eq_on_punctured_nhds hn hf hfa
    (eventually_differentiable_punctured_continuous_root hn hf hsc hfnz hpow) hpow

/-- No continuous logarithm exists on a punctured neighborhood of an analytic zero. -/
theorem not_exists_punctured_continuous_logarithm
    {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) (hfa : f a = 0) :
    ¬ ∃ l : ℂ → ℂ, (∀ᶠ z in 𝓝[≠] a, ContinuousAt l z) ∧
      (∀ᶠ z in 𝓝[≠] a, Complex.exp (l z) = f z) := by
  rintro ⟨l, hlc, hlog⟩
  have hfnz : ∀ᶠ z in 𝓝[≠] a, f z ≠ 0 := by
    filter_upwards [hlog] with z hz
    rw [← hz]
    exact Complex.exp_ne_zero _
  have hfinite : analyticOrderAt f a ≠ ⊤ := by
    intro htop
    have hzero : ∀ᶠ z in 𝓝[≠] a, f z = 0 :=
      (analyticOrderAt_eq_top.mp htop).filter_mono nhdsWithin_le_nhds
    obtain ⟨z, hz0, hznz⟩ := (hzero.and hfnz).exists
    exact hznz hz0
  have hm : 0 < analyticOrderNatAt f a := by
    apply Nat.pos_of_ne_zero
    intro hm0
    apply (hf.analyticOrderAt_ne_zero.mpr hfa)
    rw [← Nat.cast_analyticOrderNatAt hfinite, hm0, Nat.cast_zero]
  let n := analyticOrderNatAt f a + 1
  have hn : 0 < n := Nat.succ_pos _
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  let s : ℂ → ℂ := fun z => Complex.exp ((n : ℂ)⁻¹ * l z)
  have hsc : ∀ᶠ z in 𝓝[≠] a, ContinuousAt s z := by
    filter_upwards [hlc] with z hz
    exact (hz.const_mul _).cexp
  have hpow : ∀ᶠ z in 𝓝[≠] a, s z ^ n = f z := by
    filter_upwards [hlog] with z hz
    change Complex.exp ((n : ℂ)⁻¹ * l z) ^ n = f z
    rw [← Complex.exp_nat_mul]
    simpa [hnC] using hz
  have hdvd := dvd_analyticOrderNatAt_of_pow_eq_on_punctured_nhds hn hf hfa
    (eventually_differentiable_punctured_continuous_root hn hf hsc hfnz hpow) hpow
  exact (Nat.not_dvd_of_pos_of_lt hm (Nat.lt_succ_self _)) hdvd

/-- A continuous punctured lift of an analytic zero forces a finite power chart and extends
analytically in that chart, with its exact ramification order. No finite-sheet premise is needed. -/
theorem analytic_zero_lift_has_power_chart
    {Y : Type*} [TopologicalSpace Y] [PathConnectedSpace Y] [LocallyPathConnectedSpace Y]
    {q : Y → PuncturedUnitDisk} (hq : IsCoveringMap q)
    {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) (hfa : f a = 0)
    (g : ℂ → Y) (hgc : ∀ᶠ z in 𝓝[≠] a, ContinuousAt g z)
    (hfg : ∀ᶠ z in 𝓝[≠] a, (q (g z) : ℂ) = f z) :
    ∃ n : ℕ, ∃ hn : 0 < n, ∃ D : Y ≃ₜ PuncturedUnitDisk,
      (∀ y, q y = puncturedDiskPower n hn (D y)) ∧
      AnalyticAt ℂ (update (fun z => (D (g z) : ℂ)) a 0) a ∧
      analyticOrderAt f a = n • analyticOrderAt (update (fun z => (D (g z) : ℂ)) a 0) a := by
  rcases puncturedDisk_cover_classification hq with ⟨D, hD⟩ | ⟨n, hn, D, hD⟩
  · exfalso
    apply not_exists_punctured_continuous_logarithm hf hfa
    refine ⟨fun z => (D (g z) : ℂ), ?_, ?_⟩
    · filter_upwards [hgc] with z hz
      exact continuous_subtype_val.continuousAt.comp (D.continuous.continuousAt.comp hz)
    · filter_upwards [hfg] with z hz
      have hd : (q (g z) : ℂ) = Complex.exp (D (g z) : ℂ) :=
        congrArg Subtype.val (hD (g z))
      exact hd.symm.trans hz
  · have hsc : ∀ᶠ z in 𝓝[≠] a, ContinuousAt (fun z => (D (g z) : ℂ)) z := by
      filter_upwards [hgc] with z hz
      exact continuous_subtype_val.continuousAt.comp (D.continuous.continuousAt.comp hz)
    have hfnz : ∀ᶠ z in 𝓝[≠] a, f z ≠ 0 := by
      filter_upwards [hfg] with z hz
      rw [← hz]
      exact (q (g z)).property.1
    have hpow : ∀ᶠ z in 𝓝[≠] a, (D (g z) : ℂ) ^ n = f z := by
      filter_upwards [hfg] with z hz
      have hd : (q (g z) : ℂ) = (D (g z) : ℂ) ^ n := congrArg Subtype.val (hD (g z))
      exact hd.symm.trans hz
    have hsd := eventually_differentiable_punctured_continuous_root hn hf hsc hfnz hpow
    exact ⟨n, hn, D, hD,
      analyticAt_update_zero_of_pow_eq_on_punctured_nhds hn hf hfa hsd hpow,
      analyticOrderAt_update_zero_mul_of_pow_eq_on_punctured_nhds hn hf hfa hsd hpow⟩

end GaloisForLFunctions.HTGeometry
