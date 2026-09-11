import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedCoordinateExtension
import Mathlib.Topology.Sequences
/-! The exact original-L2 completion of backward evolution on actual bounded chains.
Its closed graph is the full inverse relation of the causal semigroup. Every point
of that relation is approached by genuine chains; the nonzero kernel describes
precisely the loss of closability at positive backward time. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The actual backward-time graph in a fixed derivative coordinate, using the
original L2 norm on both coordinates. -/
def causalBoundedBackwardGraph (j : ℕ) (s : ℝ≥0) : Set (hardyL2ᗮ × hardyL2ᗮ) :=
  Set.range (fun u : causalBoundedChain =>
    (causalBoundedChainCoordinate j u,
      causalBoundedChainCoordinate j (causalBoundedChainExponential (-((s : ℝ) : ℂ)) u)))

/-- Completing a backward chain graph in the original L2 topology gives exactly
the full inverse relation of the genuine forward causal evolution. -/
theorem closure_causalBoundedBackwardGraph (j : ℕ) (s : ℝ≥0) :
    closure (causalBoundedBackwardGraph j s) =
      {p : hardyL2ᗮ × hardyL2ᗮ | p.1 = causalLowerCauchyEvolution s p.2} := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · rintro _ ⟨u, rfl⟩
      change causalBoundedChainCoordinate j u = causalLowerCauchyEvolution s
        (causalBoundedChainCoordinate j (causalBoundedChainExponential (-((s : ℝ) : ℂ)) u))
      exact (congrArg (causalBoundedChainCoordinate j)
        (causalBoundedChainExponential_apply_neg ((s : ℝ) : ℂ) u)).symm.trans
          (causalBoundedEntireOrbit_eq_evolution j
            (causalBoundedChainExponential (-((s : ℝ) : ℂ)) u) s)
    · exact isClosed_eq continuous_fst ((causalLowerCauchyEvolution s).continuous.comp continuous_snd)
  · rintro ⟨x, y⟩ h
    change x = causalLowerCauchyEvolution s y at h
    have hd : (causalLowerCauchyEvolution s y, y) ∈ closure (causalBoundedBackwardGraph j s) := by
      refine (causalBoundedChainCoordinate_denseRange j).induction_on
        (p := fun v : hardyL2ᗮ => (causalLowerCauchyEvolution s v, v) ∈
          closure (causalBoundedBackwardGraph j s)) y ?_ ?_
      · exact isClosed_closure.preimage ((causalLowerCauchyEvolution s).continuous.prodMk continuous_id)
      · intro u
        apply subset_closure
        refine ⟨causalBoundedChainExponential ((s : ℝ) : ℂ) u, ?_⟩
        apply Prod.ext
        · exact causalBoundedEntireOrbit_eq_evolution j u s
        · exact congrArg (causalBoundedChainCoordinate j)
            (causalBoundedChainExponential_neg_apply ((s : ℝ) : ℂ) u)
    rw [h]
    exact hd

/-- Every inverse-relation pair, and only such a pair, is the simultaneous L2
limit of a sequence of actual chain coordinates and their backward evolutions. -/
theorem causalBoundedBackwardGraph_sequential_iff (j : ℕ) (s : ℝ≥0) (x y : hardyL2ᗮ) :
    (∃ u : ℕ → causalBoundedChain,
      Tendsto (fun n => causalBoundedChainCoordinate j (u n)) atTop (𝓝 x) ∧
      Tendsto (fun n => causalBoundedChainCoordinate j
        (causalBoundedChainExponential (-((s : ℝ) : ℂ)) (u n))) atTop (𝓝 y)) ↔
      x = causalLowerCauchyEvolution s y := by
  constructor
  · rintro ⟨u, hx, hy⟩
    have hm : (x, y) ∈ closure (causalBoundedBackwardGraph j s) :=
      mem_closure_iff_seq_limit.mpr
        ⟨fun n => (causalBoundedChainCoordinate j (u n), causalBoundedChainCoordinate j
          (causalBoundedChainExponential (-((s : ℝ) : ℂ)) (u n))),
          fun n => ⟨u n, rfl⟩, hx.prodMk_nhds hy⟩
    rw [closure_causalBoundedBackwardGraph] at hm
    exact hm
  · intro h
    have hm : (x, y) ∈ closure (causalBoundedBackwardGraph j s) := by
      rw [closure_causalBoundedBackwardGraph]
      exact h
    have hseq : ∃ v : ℕ → hardyL2ᗮ × hardyL2ᗮ,
        (∀ n, v n ∈ causalBoundedBackwardGraph j s) ∧ Tendsto v atTop (𝓝 (x, y)) :=
      (mem_closure_iff_seq_limit (X := hardyL2ᗮ × hardyL2ᗮ)
        (s := causalBoundedBackwardGraph j s) (a := (x, y))).mp hm
    obtain ⟨v, hv, ht⟩ := hseq
    change ∀ n, ∃ u : causalBoundedChain,
      (causalBoundedChainCoordinate j u,
        causalBoundedChainCoordinate j (causalBoundedChainExponential (-((s : ℝ) : ℂ)) u)) = v n at hv
    let u : ℕ → causalBoundedChain := fun n => Classical.choose (hv n)
    have hu (n : ℕ) : (causalBoundedChainCoordinate j (u n), causalBoundedChainCoordinate j
        (causalBoundedChainExponential (-((s : ℝ) : ℂ)) (u n))) = v n :=
      Classical.choose_spec (hv n)
    have hx : (fun n => causalBoundedChainCoordinate j (u n)) = fun n => (v n).1 :=
      funext (fun n => congrArg Prod.fst (hu n))
    have hy : (fun n => causalBoundedChainCoordinate j
        (causalBoundedChainExponential (-((s : ℝ) : ℂ)) (u n))) = fun n => (v n).2 :=
      funext (fun n => congrArg Prod.snd (hu n))
    exact ⟨u, (congrArg (fun f : ℕ → hardyL2ᗮ => Tendsto f atTop (𝓝 x)) hx).mpr ht.fst_nhds,
      (congrArg (fun f : ℕ → hardyL2ᗮ => Tendsto f atTop (𝓝 y)) hy).mpr ht.snd_nhds⟩

/-- Positive backward time admits actual chains whose input coordinate vanishes
in L2 while the backward output converges to a nonzero vector. Zero time is the
sole exception, so failure of closability has a sharp boundary. -/
theorem causalBoundedBackwardGraph_nonclosable_iff (j : ℕ) (s : ℝ≥0) :
    (∃ u : ℕ → causalBoundedChain, ∃ y : hardyL2ᗮ, y ≠ 0 ∧
      Tendsto (fun n => causalBoundedChainCoordinate j (u n)) atTop (𝓝 0) ∧
      Tendsto (fun n => causalBoundedChainCoordinate j
        (causalBoundedChainExponential (-((s : ℝ) : ℂ)) (u n))) atTop (𝓝 y)) ↔ s ≠ 0 := by
  classical
  constructor
  · rintro ⟨u, y, hy, h0, ht⟩ hs
    have he := (causalBoundedBackwardGraph_sequential_iff j s 0 y).mp ⟨u, h0, ht⟩
    rw [hs, causalLowerCauchyEvolution_zero] at he
    exact hy he.symm
  · intro hs
    have hn : ¬Function.Injective (causalLowerCauchyEvolution s) := by
      intro h
      exact hs ((causalLowerCauchyEvolution_injective_iff s).mp h)
    simp only [Function.Injective, not_forall] at hn
    obtain ⟨a, b, hab, hne⟩ := hn
    have hz : causalLowerCauchyEvolution s (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    have hseq : ∃ u : ℕ → causalBoundedChain,
        Tendsto (fun n => causalBoundedChainCoordinate j (u n)) atTop (𝓝 (0 : hardyL2ᗮ)) ∧
        Tendsto (fun n => causalBoundedChainCoordinate j
          (causalBoundedChainExponential (-((s : ℝ) : ℂ)) (u n))) atTop (𝓝 (a-b)) :=
      (causalBoundedBackwardGraph_sequential_iff j s 0 (a-b)).mpr hz.symm
    exact hseq.elim (fun u hu => ⟨u, a-b, sub_ne_zero.mpr hne, hu.1, hu.2⟩)
end
end RHTower.FokasLenells
