import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Extension by zero along a bump

A section over an open set, multiplied by a bump whose closed support lies inside that open set,
extends by zero to a continuous function on the whole space: on the open set the extension is the
product, and off the closed support of the bump it vanishes, and these two open sets cover.

This is what makes a fine sheaf fine: multiplying a section by a member of a subordinate partition
of unity produces a global section, which is the operation the contracting homotopy of the Čech
complex is built from.

* `deningerExtendByZero` : the extension.
* `deningerExtendByZero_continuous` : it is continuous.
* `deningerExtendByZero_eq_of_mem`, `deningerExtendByZero_eq_zero` : its two defining properties.
-/

namespace RHTower

open Set Topology
open scoped Classical

section ExtendByZero

variable {X : Type*} [TopologicalSpace X]

/-- The extension by zero of `ρ · f` from an open set to the whole space. -/
noncomputable def deningerExtendByZero (U : Set X) (ρ f : X → ℝ) (x : X) : ℝ :=
  if x ∈ U then ρ x * f x else 0

omit [TopologicalSpace X] in
theorem deningerExtendByZero_eq_of_mem {U : Set X} {ρ f : X → ℝ} {x : X} (hx : x ∈ U) :
    deningerExtendByZero U ρ f x = ρ x * f x := if_pos hx

omit [TopologicalSpace X] in
theorem deningerExtendByZero_eq_zero {U : Set X} {ρ f : X → ℝ} {x : X} (hx : x ∉ U) :
    deningerExtendByZero U ρ f x = 0 := if_neg hx

/-- Off the closed support of the bump the extension vanishes, whether or not the point lies in the
open set. -/
theorem deningerExtendByZero_eq_zero_of_notMem_tsupport {U : Set X} {ρ f : X → ℝ} {x : X}
    (hx : x ∉ tsupport ρ) : deningerExtendByZero U ρ f x = 0 := by
  by_cases hxU : x ∈ U
  · rw [deningerExtendByZero_eq_of_mem hxU]
    have : ρ x = 0 := by
      by_contra hne
      exact hx (subset_tsupport ρ hne)
    rw [this, zero_mul]
  · exact deningerExtendByZero_eq_zero hxU

/-- **The extension by zero is continuous.**  The open set and the complement of the closed support
of the bump cover the space: on the first the extension is the product, on the second it is zero. -/
theorem deningerExtendByZero_continuous {U : Set X} (hU : IsOpen U) {ρ f : X → ℝ}
    (hρ : Continuous ρ) (hsupp : tsupport ρ ⊆ U) (hf : ContinuousOn f U) :
    Continuous (deningerExtendByZero U ρ f) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ U
  · have hmem : U ∈ 𝓝 x := hU.mem_nhds hx
    have heq : deningerExtendByZero U ρ f =ᶠ[𝓝 x] fun y => ρ y * f y := by
      filter_upwards [hmem] with y hy
      exact deningerExtendByZero_eq_of_mem hy
    refine ContinuousAt.congr ?_ heq.symm
    exact (hρ.continuousAt.mul ((hf x hx).continuousAt hmem))
  · have hxs : x ∉ tsupport ρ := fun hc => hx (hsupp hc)
    have hopen : IsOpen ((tsupport ρ)ᶜ) := (isClosed_tsupport ρ).isOpen_compl
    have hmem : (tsupport ρ)ᶜ ∈ 𝓝 x := hopen.mem_nhds hxs
    have heq : deningerExtendByZero U ρ f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [hmem] with y hy
      exact deningerExtendByZero_eq_zero_of_notMem_tsupport hy
    exact ContinuousAt.congr continuousAt_const heq.symm

end ExtendByZero

end RHTower

namespace RHTower

open Set Topology
open scoped Classical

section RelativeExtend

variable {X : Type*} [TopologicalSpace X]

/-- **The extension by zero is continuous on any open region.**  On the part of the region inside
the open set the extension is the product; on the part outside the closed support of the bump it
vanishes; and every point of the region lies in one of these two opens. -/
theorem deningerExtendByZero_continuousOn {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    {ρ f : X → ℝ} (hρ : Continuous ρ) (hsupp : tsupport ρ ⊆ U)
    (hf : ContinuousOn f (U ∩ V)) : ContinuousOn (deningerExtendByZero U ρ f) V := by
  intro x hx
  refine ContinuousAt.continuousWithinAt ?_
  by_cases hxU : x ∈ U
  · have hmem : U ∩ V ∈ 𝓝 x := (hU.inter hV).mem_nhds ⟨hxU, hx⟩
    have heq : deningerExtendByZero U ρ f =ᶠ[𝓝 x] fun y => ρ y * f y := by
      filter_upwards [hmem] with y hy
      exact deningerExtendByZero_eq_of_mem hy.1
    refine ContinuousAt.congr ?_ heq.symm
    exact hρ.continuousAt.mul ((hf x ⟨hxU, hx⟩).continuousAt hmem)
  · have hxs : x ∉ tsupport ρ := fun hc => hxU (hsupp hc)
    have hmem : (tsupport ρ)ᶜ ∈ 𝓝 x := ((isClosed_tsupport ρ).isOpen_compl).mem_nhds hxs
    have heq : deningerExtendByZero U ρ f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [hmem] with y hy
      exact deningerExtendByZero_eq_zero_of_notMem_tsupport hy
    exact ContinuousAt.congr continuousAt_const heq.symm

/-- Off the open set the bump vanishes, so the extension records the bump value there. -/
theorem deningerExtendByZero_bump_zero {U : Set X} {ρ : X → ℝ} (hsupp : tsupport ρ ⊆ U) {x : X}
    (hx : x ∉ U) : ρ x = 0 := by
  by_contra hne
  exact hx (hsupp (subset_tsupport ρ hne))

end RelativeExtend

end RHTower
