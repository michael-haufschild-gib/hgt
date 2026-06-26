/-
# Zeros of a nonzero analytic function on a connected open set are countable

The germ-extraction step of the Kummer non-squareness needs to choose a circle radius avoiding the
zeros of the analytic numerator/denominator. The enabling general fact:

> An analytic function `f`, not identically `0` on a connected open `U ⊆ ℂ`, has a **countable** zero
> set on `U`.

Proof shape (constraint, not flow): the identity theorem makes every zero **isolated**
(`AnalyticOnNhd.preimage_zero_mem_codiscreteWithin`: the non-zero set is codiscrete within `U`), so the
zero set is a **discrete** subset of `ℂ` (`isDiscrete_of_codiscreteWithin`). A discrete subset of the
second-countable space `ℂ` is **Lindelöf** (`HereditarilyLindelofSpace.isLindelof`) hence **countable**
(`IsLindelof.countable_of_isDiscrete`).

Corollary (`exists_radius_avoiding_zeros`): the norms of the zeros form a countable subset of `ℝ`, so
every nondegenerate interval `(a,b)` (which is uncountable, `Real.Ioo_countable_iff`) contains a radius
`R` with no zero of norm `R` — the avoiding circle the period/winding argument runs on.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Analysis.Real.Cardinality

open Filter Topology

namespace Bottcher

/-- **A nonzero analytic function on a connected open set has a countable zero set.** With a witness
`x₀ ∈ U` where `f x₀ ≠ 0`, the identity theorem forces every zero to be isolated, so the zero set is a
discrete subset of `ℂ`; discrete subsets of the second-countable space `ℂ` are Lindelöf, hence
countable. -/
theorem analyticOnNhd_zeros_countable {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hUc : IsPreconnected U)
    {x₀ : ℂ} (hx₀ : x₀ ∈ U) (hfx₀ : f x₀ ≠ 0) :
    {z ∈ U | f z = 0}.Countable := by
  have hU : IsConnected U := ⟨⟨x₀, hx₀⟩, hUc⟩
  -- the non-zero set is codiscrete within `U` (identity theorem), i.e. the zero set's complement
  have hcod : f ⁻¹' {0}ᶜ ∈ codiscreteWithin U :=
    hf.preimage_zero_mem_codiscreteWithin hfx₀ hx₀ hU
  have hcompl : ({z | f z = 0} : Set ℂ)ᶜ ∈ codiscreteWithin U := by
    have hset : ({z | f z = 0} : Set ℂ)ᶜ = f ⁻¹' {0}ᶜ := by
      ext z; simp [Set.mem_preimage]
    rw [hset]; exact hcod
  -- so the zero set is a discrete subset of `ℂ`
  have hdisc : IsDiscrete ({z | f z = 0} ∩ U) := isDiscrete_of_codiscreteWithin hcompl
  -- discrete subset of the second-countable space `ℂ` is Lindelöf, hence countable
  have hlind : IsLindelof ({z | f z = 0} ∩ U) := HereditarilyLindelofSpace.isLindelof _
  have hcount : ({z | f z = 0} ∩ U).Countable := hlind.countable_of_isDiscrete hdisc
  have hZeq : {z ∈ U | f z = 0} = {z | f z = 0} ∩ U := by ext z; simp [and_comm]
  rw [hZeq]; exact hcount

/-- **An avoiding radius exists in every nondegenerate interval.** For `f` analytic and not identically
`0` on a connected open `U`, and any `a < b`, there is a radius `R ∈ (a,b)` such that `f` has no zero of
norm `R` on `U`. The zeros are countable, so their norms form a countable subset of `ℝ`, which cannot
fill the uncountable interval `(a,b)`. This is the circle the Kummer period/winding obstruction runs
on. -/
theorem exists_radius_avoiding_zeros {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hUc : IsPreconnected U)
    {x₀ : ℂ} (hx₀ : x₀ ∈ U) (hfx₀ : f x₀ ≠ 0) {a b : ℝ} (hab : a < b) :
    ∃ R ∈ Set.Ioo a b, ∀ z ∈ U, ‖z‖ = R → f z ≠ 0 := by
  have hcount : {z ∈ U | f z = 0}.Countable :=
    analyticOnNhd_zeros_countable hf hUc hx₀ hfx₀
  set S : Set ℝ := (fun z : ℂ => ‖z‖) '' {z ∈ U | f z = 0} with hS
  have hScount : S.Countable := hcount.image _
  by_contra hcon
  push Not at hcon
  have hsub : Set.Ioo a b ⊆ S := by
    intro R hR
    obtain ⟨z, hzU, hznorm, hzf⟩ := hcon R hR
    exact ⟨z, ⟨hzU, hzf⟩, hznorm⟩
  have hIcount : (Set.Ioo a b).Countable := hScount.mono hsub
  rw [← Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_Ioo_real hab] at hIcount
  exact absurd hIcount (not_le.mpr Cardinal.aleph0_lt_continuum)

end Bottcher
