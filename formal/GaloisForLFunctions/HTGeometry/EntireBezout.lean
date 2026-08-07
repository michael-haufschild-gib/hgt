import GaloisForLFunctions.HTGeometry.EntireInterpolation

/-!
# Analytic division and the Bezout identity for entire functions

Two theorems about the ring of entire functions.

* `exists_entire_quotient` — if the analytic order of `g` never exceeds that of `f`, then `f = q g`
  for an entire `q`.  The quotient is the normal form of the pointwise quotient, which is analytic
  because its divisor is non-negative, and the factorization propagates from a punctured
  neighbourhood of a non-zero of `g` by the identity theorem.

* `exists_entire_bezout` — **Wedderburn's lemma**: if `f` and `g` have no common zero, all zeros of
  `f` are simple and escape to infinity, and none of them is the origin, then `b f + a g = 1` for
  entire `a`, `b`.  The coefficient `a` interpolates `1 / g` at the zeros of `f`; the residual
  `1 - a g` then vanishes on the zero set of `f` and is divisible by it.
-/

open Complex Filter Metric Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Monotonicity of the coercion `ℕ∞ → WithTop ℤ` used to compare analytic and meromorphic
orders. -/
theorem enat_map_natCast_mono {a b : ℕ∞} (hab : a ≤ b) :
    ENat.map (Nat.cast : ℕ → ℤ) a ≤ ENat.map (Nat.cast : ℕ → ℤ) b := by
  rcases eq_or_ne b ⊤ with rfl | hb
  · simp
  · have hb' := hb
    lift b to ℕ using hb
    lift a to ℕ using ne_top_of_le_ne_top hb' hab
    simp only [ENat.map_coe]
    exact_mod_cast hab

/-- **Analytic division.**  An entire function whose analytic order dominates that of a nonzero
entire `g` at every point is an entire multiple of `g`. -/
theorem exists_entire_quotient {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hg0 : ∃ z₀, g z₀ ≠ 0) (hord : ∀ z, analyticOrderAt g z ≤ analyticOrderAt f z) :
    ∃ q : ℂ → ℂ, Differentiable ℂ q ∧ ∀ z, f z = q z * g z := by
  have hfA : AnalyticOnNhd ℂ f univ := fun z _ => hf.differentiableOn.analyticAt Filter.univ_mem
  have hgA : AnalyticOnNhd ℂ g univ := fun z _ => hg.differentiableOn.analyticAt Filter.univ_mem
  -- `g` does not vanish identically near any point
  have hgnz : ∀ z : ℂ, analyticOrderAt g z ≠ ⊤ := by
    intro z hz
    obtain ⟨z₀, hz₀⟩ := hg0
    refine hz₀ ?_
    exact hgA.eqOn_of_preconnected_of_eventuallyEq (g := fun _ => (0 : ℂ)) analyticOnNhd_const
      isPreconnected_univ (mem_univ z) (analyticOrderAt_eq_top.mp hz) (mem_univ z₀)
  have hmord : ∀ z : ℂ, meromorphicOrderAt g z ≤ meromorphicOrderAt f z := by
    intro z
    rw [(hgA z (mem_univ z)).meromorphicOrderAt_eq, (hfA z (mem_univ z)).meromorphicOrderAt_eq]
    exact enat_map_natCast_mono (hord z)
  have hmgtop : ∀ z : ℂ, meromorphicOrderAt g z ≠ ⊤ := by
    intro z
    rw [(hgA z (mem_univ z)).meromorphicOrderAt_eq]
    intro h
    exact hgnz z (ENat.map_eq_top_iff.mp h)
  have hmf : MeromorphicOn f univ := hfA.meromorphicOn
  have hmg : MeromorphicOn g univ := hgA.meromorphicOn
  have hmq : MeromorphicOn (fun z => f z / g z) univ := hmf.fun_div hmg
  set q : ℂ → ℂ := toMeromorphicNFOn (fun z => f z / g z) univ with hq_def
  have hqNF : MeromorphicNFOn q univ := meromorphicNFOn_toMeromorphicNFOn _ _
  have hdiv : 0 ≤ MeromorphicOn.divisor q univ := by
    rw [hq_def, MeromorphicOn.divisor_of_toMeromorphicNFOn hmq]
    intro z
    rw [MeromorphicOn.divisor_apply hmq (mem_univ z)]
    have hordz : meromorphicOrderAt (fun z => f z / g z) z
        = meromorphicOrderAt f z - meromorphicOrderAt g z :=
      meromorphicOrderAt_div (hmf z (mem_univ z)) (hmg z (mem_univ z))
    rw [hordz]
    have hle := hmord z
    have hne := hmgtop z
    rcases eq_or_ne (meromorphicOrderAt f z) ⊤ with hft | hft
    · simp [hft]
    · lift meromorphicOrderAt f z to ℤ using hft with m hm
      lift meromorphicOrderAt g z to ℤ using hne with n hn
      have hsub : ((m : WithTop ℤ) - (n : WithTop ℤ)) = ((m - n : ℤ) : WithTop ℤ) := by norm_cast
      rw [hsub]
      simp only [WithTop.untop₀_coe, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply,
        sub_nonneg]
      exact_mod_cast hle
  have hqA : AnalyticOnNhd ℂ q univ := hqNF.divisor_nonneg_iff_analyticOnNhd.mp hdiv
  obtain ⟨z₀, hz₀⟩ := hg0
  refine ⟨q, fun z => (hqA z (mem_univ z)).differentiableAt, ?_⟩
  have hfreq : ∀ᶠ z in 𝓝[≠] z₀, q z * g z = f z := by
    have h1 : q =ᶠ[𝓝[≠] z₀] fun z => f z / g z :=
      hmq.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z₀)
    have h2 : ∀ᶠ z in 𝓝[≠] z₀, g z ≠ 0 :=
      nhdsWithin_le_nhds (((hgA z₀ (mem_univ z₀)).continuousAt).eventually_ne hz₀)
    filter_upwards [h1, h2] with z hz hgz
    rw [hz, div_mul_cancel₀ _ hgz]
  have := (hqA.mul hgA).eqOn_of_preconnected_of_frequently_eq hfA isPreconnected_univ
    (mem_univ z₀) (hfreq.frequently)
  intro z
  exact (this (mem_univ z)).symm

/-- **Wedderburn's lemma for entire functions.**  Two entire functions without a common zero, the
zeros of the first being simple, nonzero and escaping to infinity, generate the unit ideal. -/
theorem exists_entire_bezout {ι : Type*} [Countable ι] {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) {w : ι → ℂ}
    (hw0 : ∀ i, w i ≠ 0) (hfw : ∀ i, f (w i) = 0) (hfw' : ∀ i, deriv f (w i) ≠ 0)
    (hinj : Function.Injective w) (hesc : Tendsto (fun i => ‖w i‖) cofinite atTop)
    (hzeros : ∀ z, f z = 0 → ∃ i, z = w i) (hf0 : ∃ z₀, f z₀ ≠ 0)
    (hgw : ∀ i, g (w i) ≠ 0) :
    ∃ a b : ℂ → ℂ, Differentiable ℂ a ∧ Differentiable ℂ b ∧ ∀ z, b z * f z + a z * g z = 1 := by
  obtain ⟨a, ha, hav⟩ :=
    exists_entire_interpolation hf hw0 hfw hfw' hinj hesc (fun i => (g (w i))⁻¹)
  have hres : Differentiable ℂ fun z => 1 - a z * g z :=
    (differentiable_const 1).sub (ha.mul hg)
  have hordle : ∀ z, analyticOrderAt f z ≤ analyticOrderAt (fun z => 1 - a z * g z) z := by
    intro z
    rcases eq_or_ne (f z) 0 with hz | hz
    · obtain ⟨i, rfl⟩ := hzeros z hz
      have hone : analyticOrderAt f (w i) = 1 :=
        ((hf.differentiableOn.analyticAt (s := univ) Filter.univ_mem).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
          (hfw i) (hfw' i))
      rw [hone]
      have hvan : (fun z => 1 - a z * g z) (w i) = 0 := by
        simp [hav i, inv_mul_cancel₀ (hgw i)]
      have hA : AnalyticAt ℂ (fun z => 1 - a z * g z) (w i) :=
        hres.differentiableOn.analyticAt (s := univ) Filter.univ_mem
      exact Order.one_le_iff_ne_zero.mpr (fun h => by
        rw [hA.analyticOrderAt_eq_zero] at h
        exact h hvan)
    · have : analyticOrderAt f z = 0 :=
        (hf.differentiableOn.analyticAt (s := univ) Filter.univ_mem).analyticOrderAt_eq_zero.mpr hz
      simp [this]
  obtain ⟨b, hb, hbeq⟩ := exists_entire_quotient hres hf hf0 hordle
  refine ⟨a, b, ha, hb, fun z => ?_⟩
  have := hbeq z
  linear_combination -this
