import GaloisForLFunctions.RHTower.DeningerClopenPartition
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Transverse partitions of unity on a product with a profinite factor

Multiplying the indicators of a clopen partition of the first factor by partitions of unity on the
second factor assembles a partition of unity on the product that is locally constant along the
first factor and inherits its regularity along the second.  It is subordinate to any cover refined
by the corresponding boxes.

This is the fineness construction on a packet: clopen in the profinite direction, smooth in the
circle direction.

* `deningerTransverseSum` : the assembled function.
* `deningerTransverseSum_sum` : the assembled family is a partition of unity.
* `deningerTransverseSum_locallyConstant` : it is locally constant along the profinite factor.
* `deningerTransverseSum_subordinate` : it is subordinate to the box cover.
-/

namespace RHTower

open Set

section Transverse

variable {B S : Type*} [TopologicalSpace B] [TopologicalSpace S] {ι κ : Type*}
  [Fintype ι] [Fintype κ] {D : ι → Set B} {ψ : ι → κ → S → ℝ}

omit [Fintype ι] [Fintype κ] in
/-- **The indicator of a clopen set is continuous.**  A clopen set has empty frontier. -/
theorem deningerClopenIndicator_continuous {D : Set B} (hD : IsClopen D) :
    Continuous (D.indicator fun _ => (1 : ℝ)) := by
  classical
  have heq : D.indicator (fun _ => (1 : ℝ)) = D.piecewise (fun _ => (1 : ℝ)) fun _ => 0 := by
    funext b
    by_cases hb : b ∈ D
    · rw [Set.indicator_of_mem hb, Set.piecewise_eq_of_mem _ _ _ hb]
    · rw [Set.indicator_of_notMem hb, Set.piecewise_eq_of_notMem _ _ _ hb]
  rw [heq]
  exact Continuous.piecewise (by rw [hD.frontier_eq]; simp) continuous_const continuous_const

omit [TopologicalSpace B] [Fintype κ] in
/-- **The indicators of a partition sum to one.** -/
theorem deningerIndicator_sum (hpart : ∀ b : B, ∃! α : ι, b ∈ D α) (b : B) :
    ∑ α : ι, (D α).indicator (fun _ => (1 : ℝ)) b = 1 := by
  classical
  obtain ⟨α₀, hα₀, huniq⟩ := hpart b
  rw [Finset.sum_eq_single α₀]
  · rw [Set.indicator_of_mem hα₀]
  · intro α _ hne
    refine Set.indicator_of_notMem ?_ _
    intro hmem
    exact hne (huniq α hmem)
  · intro h
    exact absurd (Finset.mem_univ α₀) h

/-- **The transverse assembly**: indicators of the first factor times functions of the second. -/
noncomputable def deningerTransverseSum (D : ι → Set B) (ψ : ι → κ → S → ℝ) (j : κ)
    (p : B × S) : ℝ :=
  ∑ α : ι, (D α).indicator (fun _ => (1 : ℝ)) p.1 * ψ α j p.2

omit [TopologicalSpace B] [TopologicalSpace S] [Fintype κ] in
/-- On a member of the partition the assembly is the corresponding transverse function. -/
theorem deningerTransverseSum_eq_of_mem (hpart : ∀ b : B, ∃! α : ι, b ∈ D α) {α₀ : ι} {b : B}
    (hb : b ∈ D α₀) (j : κ) (t : S) : deningerTransverseSum D ψ j (b, t) = ψ α₀ j t := by
  classical
  obtain ⟨α₁, hα₁, huniq⟩ := hpart b
  have hα₀ : α₀ = α₁ := huniq α₀ hb
  rw [deningerTransverseSum, Finset.sum_eq_single α₀]
  · rw [Set.indicator_of_mem hb, one_mul]
  · intro α _ hne
    rw [Set.indicator_of_notMem, zero_mul]
    intro hmem
    exact hne (hα₀ ▸ huniq α hmem)
  · intro h
    exact absurd (Finset.mem_univ α₀) h

omit [TopologicalSpace B] [TopologicalSpace S] in
/-- **The assembled family is a partition of unity.** -/
theorem deningerTransverseSum_sum (hpart : ∀ b : B, ∃! α : ι, b ∈ D α)
    (hone : ∀ (α : ι) (b : B), b ∈ D α → ∀ t : S, ∑ j : κ, ψ α j t = 1) (p : B × S) :
    ∑ j : κ, deningerTransverseSum D ψ j p = 1 := by
  have hswap : ∑ j : κ, deningerTransverseSum D ψ j p
      = ∑ α : ι, (D α).indicator (fun _ => (1 : ℝ)) p.1 * ∑ j : κ, ψ α j p.2 := by
    simp only [deningerTransverseSum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun α _ => by rw [Finset.mul_sum]
  rw [hswap]
  have hterm : ∀ α : ι, (D α).indicator (fun _ => (1 : ℝ)) p.1 * ∑ j : κ, ψ α j p.2
      = (D α).indicator (fun _ => (1 : ℝ)) p.1 := by
    intro α
    by_cases hb : p.1 ∈ D α
    · rw [hone α p.1 hb p.2, mul_one]
    · rw [Set.indicator_of_notMem hb, zero_mul]
  rw [Finset.sum_congr rfl fun α _ => hterm α]
  exact deningerIndicator_sum hpart p.1

omit [Fintype κ] in
/-- **The assembly is continuous.** -/
theorem deningerTransverseSum_continuous (hD : ∀ α, IsClopen (D α))
    (hψ : ∀ (α : ι) (j : κ), Continuous (ψ α j)) (j : κ) :
    Continuous (deningerTransverseSum D ψ j) := by
  refine continuous_finsetSum _ fun α _ => ?_
  exact ((deningerClopenIndicator_continuous (hD α)).comp continuous_fst).mul
    ((hψ α j).comp continuous_snd)

omit [TopologicalSpace S] [Fintype κ] in
/-- **The assembly is locally constant along the profinite factor.**  Each member of the partition
is a clopen neighbourhood on which the assembly is the corresponding transverse function. -/
theorem deningerTransverseSum_locallyConstant (hD : ∀ α, IsClopen (D α))
    (hpart : ∀ b : B, ∃! α : ι, b ∈ D α) (j : κ) (t : S) :
    IsLocallyConstant fun b : B => deningerTransverseSum D ψ j (b, t) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro b
  obtain ⟨α₀, hα₀, _⟩ := hpart b
  refine ⟨D α₀, (hD α₀).isOpen, hα₀, fun b' hb' => ?_⟩
  rw [deningerTransverseSum_eq_of_mem hpart hb' j t,
    deningerTransverseSum_eq_of_mem hpart hα₀ j t]

omit [TopologicalSpace B] [TopologicalSpace S] [Fintype κ] in
/-- Where the assembly is nonzero, some member of the partition contains the point and the
corresponding transverse function is nonzero there. -/
theorem deningerTransverseSum_ne_zero {j : κ} {p : B × S}
    (h : deningerTransverseSum D ψ j p ≠ 0) :
    ∃ α : ι, p.1 ∈ D α ∧ ψ α j p.2 ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  refine h ?_
  rw [deningerTransverseSum]
  refine Finset.sum_eq_zero fun α _ => ?_
  by_cases hb : p.1 ∈ D α
  · rw [hcon α hb, mul_zero]
  · rw [Set.indicator_of_notMem hb, zero_mul]

omit [TopologicalSpace B] [TopologicalSpace S] [Fintype κ] in
/-- **The assembly is subordinate to the box cover.** -/
theorem deningerTransverseSum_subordinate {U : κ → Set (B × S)} {I : ι → κ → Set S}
    (hsupp : ∀ (α : ι) (j : κ) (t : S), ψ α j t ≠ 0 → t ∈ I α j)
    (hbox : ∀ (α : ι) (j : κ), (D α) ×ˢ (I α j) ⊆ U j)
    {j : κ} {p : B × S} (h : deningerTransverseSum D ψ j p ≠ 0) : p ∈ U j := by
  obtain ⟨α, hα, hψ⟩ := deningerTransverseSum_ne_zero h
  exact hbox α j ⟨hα, hsupp α j p.2 hψ⟩

end Transverse

end RHTower
