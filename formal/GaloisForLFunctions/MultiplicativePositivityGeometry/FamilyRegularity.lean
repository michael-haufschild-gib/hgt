import GaloisForLFunctions.MultiplicativePositivityGeometry.FamilyLocallyFinite
import GaloisForLFunctions.MultiplicativePositivityGeometry.BoundaryRegularity

/-!
# Regularity of family divisors: the integer simple-pole classification for families

Let `𝒟` be an integer joint boundary divisor of a family over a finite abelian group `G`, with
`𝒟(0) = 1`. No pole isolation is assumed.

* **The origin fibre is a boundary divisor** (`originFibre_isBoundaryDivisor`): at `g = 0` the joint
  trace is the cosine trace of the same weights, so `u ↦ 𝒟(0, u)` falls under the simple-pole
  classification without local finiteness (`boundary_locallyFinite`).
* **Dichotomy** (`joint_locallyFinite_or_fibreConstant`). Either `𝒟` is locally finite on `G × ℝ`, or
  `𝒟(g, u) = 𝒟(g, 0)` for all `g, u`. The nonvanishing set is a subgroup, so each fibre is a coset
  of the origin fibre's support; a constant origin fibre `𝒟(0, ·) = 1` propagates by
  multiplicativity.
* **Classification** (`joint_integer_classification`). An integer configuration with `𝒟(0) = 1` is a
  joint boundary divisor iff it is positive definite and either locally finite or constant along
  the fibres; the locally finite ones are realized by the family Bochner theorem, the fibre-constant
  ones by weights at frequency `0`.
-/

open Finset Filter Topology Complex

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

universe u

variable {G : Type u} [AddCommGroup G] [Fintype G] [DecidableEq G]

omit [DecidableEq G] in
/-- At `g = 0` a joint mode is a cosine. -/
theorem jointMode_origin (ψ : AddChar G ℂ) (lam u : ℝ) :
    jointMode ψ lam (0, u) = Real.cos (lam * u) := by
  simp [jointMode, jointPhase, Complex.exp_ofReal_mul_I_re]

omit [DecidableEq G] in
/-- **The origin fibre of a joint divisor is a boundary divisor of the same weights.** -/
theorem originFibre_isBoundaryDivisor {ι : Type*} {ψ : ι → AddChar G ℂ} {lam : ι → ℝ}
    {w : ℝ → ι → ℝ} {𝒟 : G × ℝ → ℝ} (hw : IsJointBoundaryDivisor ψ lam w 𝒟) :
    IsBoundaryDivisor lam w fun u => 𝒟 (0, u) where
  nonneg := hw.nonneg
  summable := hw.summable
  tendsto u := by
    refine (hw.tendsto (0, u)).congr fun x => ?_
    unfold jointTrace cosineTrace
    simp only [jointMode_origin]

omit [DecidableEq G] in
/-- **Dichotomy.** An integer joint divisor with `𝒟(0) = 1` is locally finite or constant along the
fibres. -/
theorem joint_locallyFinite_or_fibreConstant {ι : Type*} {ψ : ι → AddChar G ℂ} {lam : ι → ℝ}
    {w : ℝ → ι → ℝ} {𝒟 : G × ℝ → ℝ} (hw : IsJointBoundaryDivisor ψ lam w 𝒟) (h0 : 𝒟 0 = 1)
    (hint : ∀ p, ∃ n : ℤ, 𝒟 p = n) :
    (∀ R : ℝ, {p : G × ℝ | 𝒟 p ≠ 0 ∧ |p.2| ≤ R}.Finite) ∨ ∀ g u, 𝒟 (g, u) = 𝒟 (g, 0) := by
  classical
  have hD := hw.isEvenPosDef
  have hfib := originFibre_isBoundaryDivisor hw
  rcases boundary_locallyFinite hfib (by simpa using h0) (fun u => hint (0, u)) with hfin | hone
  · left
    intro R
    -- Each fibre lies in a translate of the origin fibre's support.
    have hfibre : ∀ g : G, {u : ℝ | 𝒟 (g, u) ≠ 0 ∧ |u| ≤ R}.Finite := by
      intro g
      by_cases hne : ∃ u₀, 𝒟 (g, u₀) ≠ 0 ∧ |u₀| ≤ R
      · obtain ⟨u₀, hu₀, hu₀R⟩ := hne
        refine ((hfin (2 * R)).image fun v => v + u₀).subset fun u hu => ?_
        refine ⟨u - u₀, ⟨?_, ?_⟩, by ring⟩
        · have hmem1 : (g, u) ∈ nonvanishingSubgroup hD h0 hint := hu.1
          have hmem2 : (g, u₀) ∈ nonvanishingSubgroup hD h0 hint := hu₀
          have := (nonvanishingSubgroup hD h0 hint).sub_mem hmem1 hmem2
          rw [mem_nonvanishingSubgroup] at this
          simpa [Prod.mk_sub_mk] using this
        · have := abs_sub u u₀
          linarith [hu.2]
      · push Not at hne
        refine Set.finite_empty.subset fun u hu => ?_
        exact absurd (hne u hu.1) (not_le.mpr (lt_of_le_of_ne hu.2 ?_)) |>.elim
    have hcover : {p : G × ℝ | 𝒟 p ≠ 0 ∧ |p.2| ≤ R} ⊆
        ⋃ g : G, (fun u => (g, u)) '' {u : ℝ | 𝒟 (g, u) ≠ 0 ∧ |u| ≤ R} := by
      rintro ⟨g, u⟩ hp
      exact Set.mem_iUnion.mpr ⟨g, ⟨u, hp, rfl⟩⟩
    exact (Set.finite_iUnion fun g => (hfibre g).image _).subset hcover
  · right
    intro g u
    have hu : 𝒟 (0, u) ≠ 0 := by rw [hone u]; exact one_ne_zero
    have h := intValued_mul hD h0 hint hu (g, 0)
    rw [show ((0 : G), u) + (g, 0) = (g, u) by simp, hone u, one_mul] at h
    exact h

end GaloisForLFunctions.MultiplicativePositivityGeometry
