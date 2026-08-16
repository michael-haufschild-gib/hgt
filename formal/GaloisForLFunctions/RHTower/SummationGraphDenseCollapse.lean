import GaloisForLFunctions.RHTower.OneSidedCompressionUnbounded
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Hilbert closure of the finite summation rule is maximally multivalued

The graph of the finite summation functional `S x = ∑ x n` on finitely supported sequences is the
span of the pairs `(e n, 1)` inside `ℓ² ⊕ ℂ`.  A vector orthogonal to all of them has constant
first coordinate, and the only constant sequence in `ℓ²` is zero; hence the orthogonal complement
is trivial and the closure of the graph is the whole space.

Therefore the closed relation assigns every scalar to every coefficient vector: the summation rule
is not closable, and no scalar information survives Hilbert closure.
-/

noncomputable section

namespace RHTower

open scoped InnerProductSpace ENNReal

/-- Ambient graph space `ℓ²(ℕ) ⊕ ℂ`. -/
abbrev SummationGraphSpace : Type := WithLp 2 (OneSidedEllTwo × ℂ)

/-- The graph of the finite summation rule: the span of the pairs `(e n, 1)`. -/
def summationGraph : Submodule ℂ SummationGraphSpace :=
  Submodule.span ℂ (Set.range fun n : ℕ => (WithLp.toLp 2 (ellTwoBasis n, (1 : ℂ))))

theorem inner_summationGenerator (n : ℕ) (p : SummationGraphSpace) :
    ⟪(WithLp.toLp 2 (ellTwoBasis n, (1 : ℂ))), p⟫_ℂ = (WithLp.ofLp p).1 n + (WithLp.ofLp p).2 := by
  rw [WithLp.prod_inner_apply]
  rw [ellTwoBasis, lp.inner_single_left]
  simp

/-- A vector orthogonal to the summation graph has constant first coordinate. -/
theorem mem_summationGraph_orthogonal_iff (p : SummationGraphSpace) :
    p ∈ summationGraphᗮ ↔ ∀ n : ℕ, (WithLp.ofLp p).1 n + (WithLp.ofLp p).2 = 0 := by
  constructor
  · intro hp n
    have := hp _ (Submodule.subset_span ⟨n, rfl⟩)
    rwa [inner_summationGenerator] at this
  · intro h
    rw [Submodule.mem_orthogonal]
    intro u hu
    refine Submodule.span_induction (p := fun w _ => ⟪w, p⟫_ℂ = 0) ?_ ?_ ?_ ?_ hu
    · rintro w ⟨n, rfl⟩
      rw [inner_summationGenerator]
      exact h n
    · simp
    · intro a b _ _ ha hb
      rw [inner_add_left, ha, hb, add_zero]
    · intro c a _ ha
      rw [inner_smul_left, ha, mul_zero]

/-- The only constant sequence in `ℓ²` is zero. -/
theorem ellTwo_const_eq_zero {f : OneSidedEllTwo} {a : ℂ} (hf : ∀ n : ℕ, (f : ℕ → ℂ) n = a) : a = 0 := by
  by_contra hne
  have hsummable : Summable fun n : ℕ => ‖(f : ℕ → ℂ) n‖ ^ (2 : ℝ) := by
    have hmem : Memℓp (f : ∀ _ : ℕ, ℂ) 2 := lp.memℓp f
    have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
    exact (memℓp_gen_iff hp).mp hmem
  have hconst : (fun n : ℕ => ‖(f : ℕ → ℂ) n‖ ^ (2 : ℝ)) = fun _ : ℕ => ‖a‖ ^ (2 : ℝ) := by
    funext n
    rw [hf n]
  rw [hconst] at hsummable
  have hzero := hsummable.tendsto_atTop_zero
  have hlim : Filter.Tendsto (fun _ : ℕ => ‖a‖ ^ (2 : ℝ)) Filter.atTop
      (nhds (‖a‖ ^ (2 : ℝ))) := tendsto_const_nhds
  have heq := tendsto_nhds_unique hzero hlim
  have hpos : 0 < ‖a‖ ^ (2 : ℝ) := Real.rpow_pos_of_pos (norm_pos_iff.mpr hne) 2
  rw [← heq] at hpos
  exact lt_irrefl 0 hpos

/-- **Trivial orthogonal complement.** -/
theorem summationGraph_orthogonal_eq_bot : summationGraphᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro p hp
  rw [mem_summationGraph_orthogonal_iff] at hp
  have hconst : ∀ n : ℕ, ((WithLp.ofLp p).1 : ℕ → ℂ) n = -(WithLp.ofLp p).2 := by
    intro n
    have := hp n
    linear_combination this
  have hsnd : (WithLp.ofLp p).2 = 0 := by
    have := ellTwo_const_eq_zero hconst
    linear_combination -this
  have hfst : (WithLp.ofLp p).1 = 0 := by
    refine lp.ext ?_
    funext n
    rw [hconst n, hsnd]
    simp
  have : WithLp.ofLp p = 0 := Prod.ext hfst hsnd
  have hp0 : p = 0 := by
    apply WithLp.ofLp_injective
    simpa using this
  exact hp0

/-- **Dense collapse.**  The closure of the finite summation graph is the whole space. -/
theorem summationGraph_topologicalClosure_eq_top :
    summationGraph.topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff]
  exact summationGraph_orthogonal_eq_bot

/-- **Maximal multivaluedness.**  Every coefficient vector is paired with every scalar in the
closed relation; in particular the summation rule is not closable. -/
theorem summationGraph_closure_multivalued (y : OneSidedEllTwo) (c : ℂ) :
    WithLp.toLp 2 (y, c) ∈ summationGraph.topologicalClosure := by
  rw [summationGraph_topologicalClosure_eq_top]
  exact Submodule.mem_top

theorem summationGraph_not_closable :
    WithLp.toLp 2 ((0 : OneSidedEllTwo), (0 : ℂ)) ∈ summationGraph.topologicalClosure ∧
      WithLp.toLp 2 ((0 : OneSidedEllTwo), (1 : ℂ)) ∈ summationGraph.topologicalClosure :=
  ⟨summationGraph_closure_multivalued 0 0, summationGraph_closure_multivalued 0 1⟩

end RHTower
