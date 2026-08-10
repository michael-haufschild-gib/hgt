import GaloisForLFunctions.HTGeometry.ChoquetBoundaryFunctionSystem
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.Complex.Order

/-!
# The extreme states of `C(X, ℂ)` are the point evaluations

Milman's theorem shows that every extreme point of the state body of a function system is a point
evaluation.  For the *full* system `S = ⊤` the converse also holds: every point evaluation is
extreme.  So the extreme points of the state body of `C(X, ℂ)` are exactly the point evaluations,
and the Choquet boundary of `C(X, ℂ)` is all of `X`.

The proof is Urysohn's lemma plus the observation that a property of functionals which is closed,
convex, and true at every point evaluation holds throughout the state body
(`stateBody_subset_of_isClosed_convex`).  Linearity, unitality, positivity, contractivity, and the
domination `|φ(h f)| ≤ ‖h‖ φ(f)` for `f ≥ 0` are all of this shape, so none of them has to be
carried as a hypothesis.

Given `δₓ = a φ + b ψ` and a Urysohn function `f` vanishing at `x` and equal to `1` off a
neighbourhood where `g - g x` is small, positivity forces `φ f = 0`, and then domination kills the
far-away part of `g`.
-/

namespace GaloisForLFunctions.HTGeometry

namespace ShilovLocal

open Set

open scoped ComplexOrder

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- A closed convex property true at every point evaluation holds on the whole state body. -/
theorem stateBody_subset_of_isClosed_convex {S : Submodule ℂ C(X, ℂ)} {P : Set (↥S → ℂ)}
    (hclosed : IsClosed P) (hconv : Convex ℝ P) (hδ : ∀ x : X, evalPoint S x ∈ P) :
    stateBody S ⊆ P :=
  closure_minimal (convexHull_min (by rintro _ ⟨x, rfl⟩; exact hδ x) hconv) hclosed

/-- Evaluation of a functional on the full system at a continuous function. -/
def topEval (φ : ↥(⊤ : Submodule ℂ C(X, ℂ)) → ℂ) (f : C(X, ℂ)) : ℂ :=
  φ ⟨f, Submodule.mem_top⟩

@[simp]
theorem topEval_evalPoint (x : X) (f : C(X, ℂ)) : topEval (evalPoint ⊤ x) f = f x := rfl

theorem continuous_topEval (f : C(X, ℂ)) :
    Continuous fun φ : ↥(⊤ : Submodule ℂ C(X, ℂ)) → ℂ => topEval φ f :=
  continuous_apply _

/-! ### Properties inherited by the whole state body -/

theorem topEval_add_of_mem {φ : ↥(⊤ : Submodule ℂ C(X, ℂ)) → ℂ}
    (hφ : φ ∈ stateBody (⊤ : Submodule ℂ C(X, ℂ))) (a b : C(X, ℂ)) :
    topEval φ (a + b) = topEval φ a + topEval φ b := by
  refine stateBody_subset_of_isClosed_convex (P := {ψ | topEval ψ (a + b) = topEval ψ a
      + topEval ψ b}) ?_ ?_ ?_ hφ
  · exact isClosed_eq (continuous_topEval _) ((continuous_topEval _).add (continuous_topEval _))
  · intro ψ₁ h₁ ψ₂ h₂ s t hs ht hst
    simp only [Set.mem_setOf_eq, topEval, Pi.add_apply, Pi.smul_apply, Complex.real_smul] at *
    rw [h₁, h₂]
    ring
  · intro x
    simp

theorem topEval_smul_of_mem {φ : ↥(⊤ : Submodule ℂ C(X, ℂ)) → ℂ}
    (hφ : φ ∈ stateBody (⊤ : Submodule ℂ C(X, ℂ))) (c : ℂ) (a : C(X, ℂ)) :
    topEval φ (c • a) = c * topEval φ a := by
  refine stateBody_subset_of_isClosed_convex (P := {ψ | topEval ψ (c • a) = c * topEval ψ a})
    ?_ ?_ ?_ hφ
  · exact isClosed_eq (continuous_topEval _) (continuous_const.mul (continuous_topEval _))
  · intro ψ₁ h₁ ψ₂ h₂ s t hs ht hst
    simp only [Set.mem_setOf_eq, topEval, Pi.add_apply, Pi.smul_apply, Complex.real_smul] at *
    rw [h₁, h₂]
    ring
  · intro x
    simp

theorem topEval_one_of_mem {φ : ↥(⊤ : Submodule ℂ C(X, ℂ)) → ℂ}
    (hφ : φ ∈ stateBody (⊤ : Submodule ℂ C(X, ℂ))) : topEval φ 1 = 1 := by
  refine stateBody_subset_of_isClosed_convex (P := {ψ | topEval ψ 1 = 1}) ?_ ?_ ?_ hφ
  · exact isClosed_eq (continuous_topEval _) continuous_const
  · intro ψ₁ h₁ ψ₂ h₂ s t hs ht hst
    simp only [Set.mem_setOf_eq, topEval, Pi.add_apply, Pi.smul_apply, Complex.real_smul] at *
    rw [h₁, h₂, mul_one, mul_one, ← Complex.ofReal_add, hst, Complex.ofReal_one]
  · intro x
    simp

theorem topEval_nonneg_of_mem {φ : ↥(⊤ : Submodule ℂ C(X, ℂ)) → ℂ}
    (hφ : φ ∈ stateBody (⊤ : Submodule ℂ C(X, ℂ))) {f : C(X, ℂ)} (hf : ∀ y : X, 0 ≤ f y) :
    0 ≤ topEval φ f := by
  refine stateBody_subset_of_isClosed_convex (P := {ψ | 0 ≤ topEval ψ f}) ?_ ?_ ?_ hφ
  · exact isClosed_le continuous_const (continuous_topEval _)
  · intro ψ₁ h₁ ψ₂ h₂ s t hs ht hst
    simp only [Set.mem_setOf_eq, topEval, Pi.add_apply, Pi.smul_apply, Complex.real_smul] at *
    exact add_nonneg (mul_nonneg (by exact_mod_cast hs) h₁)
      (mul_nonneg (by exact_mod_cast ht) h₂)
  · intro x
    simpa using hf x

theorem topEval_norm_le_of_mem {φ : ↥(⊤ : Submodule ℂ C(X, ℂ)) → ℂ}
    (hφ : φ ∈ stateBody (⊤ : Submodule ℂ C(X, ℂ))) (f : C(X, ℂ)) :
    ‖topEval φ f‖ ≤ ‖f‖ := by
  refine stateBody_subset_of_isClosed_convex (P := {ψ | ‖topEval ψ f‖ ≤ ‖f‖}) ?_ ?_ ?_ hφ
  · exact isClosed_le ((continuous_topEval _).norm) continuous_const
  · intro ψ₁ h₁ ψ₂ h₂ s t hs ht hst
    simp only [Set.mem_setOf_eq, topEval, Pi.add_apply, Pi.smul_apply, Complex.real_smul] at *
    calc ‖(s : ℂ) * ψ₁ ⟨f, _⟩ + (t : ℂ) * ψ₂ ⟨f, _⟩‖
        ≤ ‖(s : ℂ) * ψ₁ ⟨f, _⟩‖ + ‖(t : ℂ) * ψ₂ ⟨f, _⟩‖ := norm_add_le _ _
      _ = s * ‖ψ₁ ⟨f, _⟩‖ + t * ‖ψ₂ ⟨f, _⟩‖ := by
          simp [norm_mul, abs_of_nonneg hs, abs_of_nonneg ht]
      _ ≤ s * ‖f‖ + t * ‖f‖ := by
          gcongr
      _ = ‖f‖ := by rw [← add_mul, hst, one_mul]
  · intro x
    exact f.norm_coe_le_norm x

end ShilovLocal

end GaloisForLFunctions.HTGeometry
