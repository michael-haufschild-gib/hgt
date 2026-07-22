/-
# Finite-grade detection for Suzuki boundary transport

The completed zero-mode program produces a finite-dimensional square-Evans characteristic
packet, but its logarithmic endpoint and prime-seam residuals are naturally indexed by an
unbounded grade.  This file proves the finite-dimensional compactness statement needed to keep
that analytic hierarchy honest: if all scalar residual coordinates jointly separate the packet,
then at most `finrank` of them already separate it.  For a hierarchy indexed by `ℕ`, one finite
initial grade therefore suffices.

The result is unconditional linear algebra.  It does not assert that Suzuki's analytic residual
hierarchy exists or is jointly separating; those are the remaining source-specific steps.
-/
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dual.Lemmas

open LinearMap Set Submodule

namespace GaloisForLFunctions
namespace RHTower

/-- **Finite trace detector.**  A jointly separating family of scalar linear traces on a
finite-dimensional packet contains a separating subfamily of cardinality at most the packet
dimension. -/
theorem exists_finite_trace_detector
    {𝕜 E ι : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [FiniteDimensional 𝕜 E]
    (trace : ι → Module.Dual 𝕜 E)
    (hsep : ∀ x : E, (∀ i : ι, trace i x = 0) → x = 0) :
    ∃ (n : ℕ) (pick : Fin n → ι),
      n ≤ Module.finrank 𝕜 E ∧
        ∀ x : E, (∀ j, trace (pick j) x = 0) → x = 0 := by
  have hker : (⨅ i, LinearMap.ker (trace i)) = (⊥ : Submodule 𝕜 E) := by
    apply le_antisymm
    · intro x hx
      rw [Submodule.mem_bot]
      apply hsep x
      intro i
      exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hx i)
    · exact bot_le
  have hspan : Submodule.span 𝕜 (Set.range trace) = ⊤ := by
    apply top_unique
    intro K _
    apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
    rw [hker]
    exact bot_le
  obtain ⟨f, hf_range, hf_span, _⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq 𝕜 (Set.range trace)
  choose pick hpick using hf_range
  refine ⟨Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range trace)), pick, ?_, fun x hx => ?_⟩
  · rw [hspan]
    simp [Subspace.dual_finrank_eq]
  apply (Module.forall_dual_apply_eq_zero_iff 𝕜 x).mp
  intro K
  have hK : K ∈ Submodule.span 𝕜 (Set.range f) := by
    rw [hf_span, hspan]
    exact Submodule.mem_top
  refine Submodule.span_induction (fun y hy => ?_) (by simp)
    (fun y z _ _ hy hz => by simp [hy, hz]) (fun c y _ hy => by simp [hy]) hK
  obtain ⟨j, rfl⟩ := hy
  rw [← hpick j]
  exact hx j

/-- **Finite initial-grade detector.**  If every nonzero vector in a finite-dimensional packet is
seen by some grade of a scalar trace hierarchy, then vanishing through one finite grade already
forces the vector to vanish. -/
theorem exists_finite_grade_trace_cutoff
    {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [FiniteDimensional 𝕜 E]
    (trace : ℕ → Module.Dual 𝕜 E)
    (hsep : ∀ x : E, (∀ k : ℕ, trace k x = 0) → x = 0) :
    ∃ N : ℕ, ∀ x : E, (∀ k ≤ N, trace k x = 0) → x = 0 := by
  obtain ⟨n, pick, _, hdet⟩ := exists_finite_trace_detector trace hsep
  refine ⟨∑ j, pick j, fun x hx => hdet x fun j => hx (pick j) ?_⟩
  exact Finset.single_le_sum (fun i _ => Nat.zero_le (pick i)) (Finset.mem_univ j)

end RHTower
end GaloisForLFunctions
