import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.DenseEmbedding
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Tactic

/-!
# Period rigidity

The paired elliptic-gamma argument collapses the common fixed field because three independent
periods generate a nondiscrete additive subgroup of `ℂ`. Such a subgroup need not be dense in
`ℂ`; meromorphicity is essential in the general case. This file formalizes the stronger dense
subgroup subcase and the analytic rigidity supplied by arbitrarily small nonzero periods.
-/

namespace GaloisForLFunctions

open Filter
open scoped Topology

/-- A pointwise-avoiding net converging to `y` also converges through the punctured
neighborhood of `y`. -/
lemma tendsto_nhdsNE_of_forall_ne
    {X Y : Type*} [TopologicalSpace Y] {l : Filter X} {f : X → Y} {y : Y}
    (hf : Tendsto f l (nhds y)) (hne : ∀ x, f x ≠ y) :
    Tendsto f l (nhdsWithin y {y}ᶜ) := by
  rw [tendsto_nhdsWithin_iff]
  exact ⟨hf, Eventually.of_forall fun x => by simpa using hne x⟩

/-- A continuous function invariant under a dense additive subgroup is constant. This is the
topological core of the joint-period constant collapse used by the paired telescoping theorem. -/
theorem continuous_constant_of_dense_addPeriods
    {G Y : Type*} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [TopologicalSpace Y] [T2Space Y]
    (f : G → Y) (hf : Continuous f) (P : AddSubgroup G) (hP : Dense (P : Set G))
    (hperiod : ∀ p : P, Function.Periodic f p.1) : ∀ x y, f x = f y := by
  intro x y
  let g : G → Y := fun t => f (x + t)
  let c : G → Y := fun _ => f x
  have hg : Continuous g := hf.comp (continuous_const.add continuous_id)
  have hc : Continuous c := continuous_const
  have heq : g = c := hP.denseRange_val.equalizer hg hc (by
    funext p
    exact hperiod p x)
  have hxy := congrFun heq (y - x)
  have hsum : x + (y - x) = y := by abel
  simpa [g, c, hsum] using hxy.symm

/-- A complex-differentiable function with arbitrarily small nonzero periods is constant. Unlike
the dense-subgroup theorem, this applies to nondiscrete period groups whose closure may be a line
or a union of parallel lines. -/
theorem differentiable_constant_of_small_periods
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (p : ℕ → ℂ)
    (hp0 : Tendsto p atTop (𝓝 0)) (hpne : ∀ n, p n ≠ 0)
    (hperiod : ∀ n, Function.Periodic f (p n)) : ∀ x y, f x = f y := by
  have hpwithin : Tendsto p atTop (𝓝[≠] 0) := by
    exact tendsto_nhdsNE_of_forall_ne hp0 hpne
  have hderiv : ∀ z, deriv f z = 0 := by
    intro z
    have hlim := (hf z).hasDerivAt.tendsto_slope_zero.comp hpwithin
    have hzero : (fun n => (p n)⁻¹ * (f (z + p n) - f z)) = fun _ => (0 : ℂ) := by
      funext n
      rw [hperiod n z, sub_self, mul_zero]
    change Tendsto (fun n => (p n)⁻¹ * (f (z + p n) - f z)) atTop
      (𝓝 (deriv f z)) at hlim
    rw [hzero] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  have heq : f = fun _ => f 0 := by
    have hg : Differentiable ℂ (fun _ : ℂ => f 0) := differentiable_const _
    have hfd : ∀ z, fderiv ℂ f z = fderiv ℂ (fun _ : ℂ => f 0) z := by
      intro z
      rw [← toSpanSingleton_deriv, hderiv]
      simp
    exact eq_of_fderiv_eq hf hg hfd 0 rfl
  intro x y
  rw [heq]

lemma meromorphicOrderAt_add_period
    (f : ℂ → ℂ) (p z : ℂ) (hp : Function.Periodic f p) :
    meromorphicOrderAt f (z + p) = meromorphicOrderAt f z := by
  let g : ℂ → ℂ := fun w => w + p
  have hg : AnalyticAt ℂ g z := by fun_prop
  have hgd : deriv g z ≠ 0 := by
    simp [g]
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero (f := f) hg hgd
  have hfg : f ∘ g = f := by
    funext w
    exact hp w
  rw [hfg] at hcomp
  exact hcomp.symm

/-- A meromorphic function in normal form with arbitrarily small nonzero periods is constant. The
normal-form hypothesis removes the irrelevant freedom to assign arbitrary values at isolated
poles. -/
theorem meromorphicNF_constant_of_small_periods
    (f : ℂ → ℂ) (hf : MeromorphicNFOn f Set.univ) (p : ℕ → ℂ)
    (hp0 : Tendsto p atTop (𝓝 0)) (hpne : ∀ n, p n ≠ 0)
    (hperiod : ∀ n, Function.Periodic f (p n)) : ∀ x y, f x = f y := by
  have hpwithin : Tendsto p atTop (𝓝[≠] 0) := by
    exact tendsto_nhdsNE_of_forall_ne hp0 hpne
  have han : ∀ z, AnalyticAt ℂ f z := by
    intro z
    apply (hf (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    by_contra hnonneg
    have hneg : meromorphicOrderAt f z < 0 := lt_of_not_ge hnonneg
    have hpz : Tendsto (fun n => z + p n) atTop (𝓝[≠] z) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · simpa using (tendsto_const_nhds.add hp0 :
          Tendsto (fun n => z + p n) atTop (𝓝 (z + 0)))
      · exact Filter.Eventually.of_forall fun n => by
          simp [hpne n]
    have hset : Set.univ \ {z} = {z}ᶜ := by ext w; simp
    have hnear : ∀ᶠ w in 𝓝[≠] z, AnalyticAt ℂ f w := by
      rw [← hset]
      exact hf.meromorphicOn.eventually_analyticAt (Set.mem_univ z)
    have hevent : ∀ᶠ n in atTop, AnalyticAt ℂ f (z + p n) := hpz.eventually hnear
    rcases hevent.exists with ⟨n, hn⟩
    have hnonneg_n := hn.meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_add_period f (p n) z (hperiod n)] at hnonneg_n
    exact (not_le_of_gt hneg) hnonneg_n
  exact differentiable_constant_of_small_periods f (fun z => (han z).differentiableAt) p hp0
    hpne hperiod

end GaloisForLFunctions
