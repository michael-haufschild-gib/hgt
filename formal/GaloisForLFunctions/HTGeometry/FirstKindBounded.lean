import GaloisForLFunctions.HTGeometry.ChristoffelBoundedKernel

/-!
# The first-kind half of `BoundedKernel`

`BoundedKernel` asks for uniform bounds on two kernel roots, the first-kind one built from
`monicOrthoC` and the second-kind one built from `secondKindC`.  The Christoffel limit sees only the
first.  Isolating that half gives a predicate which positivity of `λ` characterises exactly, and
makes the asymmetry between the two conditions explicit rather than implicit.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- At a real point the first-kind kernel root squares to the Christoffel--Darboux diagonal. -/
theorem kernelRoot_sq_ofReal (h : PositiveMomentForm s) (x : ℝ) (n : ℕ) :
    kernelRoot s (fun j => monicOrthoC s j (x : ℂ)) n ^ (2 : ℕ) = (cdKernel s n x).eval x := by
  rw [kernelRoot_sq_eq_normSq_sum h, cdKernel_eval_self]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [normSq_monicOrthoC_ofReal]

/-- Uniform boundedness of the first-kind kernel root alone. -/
def FirstKindBounded (s : ℕ → ℝ) (z : ℂ) : Prop :=
  ∃ S : ℝ, 0 < S ∧ ∀ N, kernelRoot s (fun j => monicOrthoC s j z) N ≤ S

/-- `BoundedKernel` is the stronger condition: it carries the second-kind bound as well. -/
theorem firstKindBounded_of_boundedKernel {z : ℂ} (hz : BoundedKernel s z) :
    FirstKindBounded s z := by
  obtain ⟨S, _, hS0, _, hS, _⟩ := hz
  exact ⟨S, hS0, hS⟩

/-- **The Christoffel limit characterises the first-kind bound exactly.** -/
theorem firstKindBounded_iff_christoffelLimit_pos (h : PositiveMomentForm s) (x : ℝ) :
    FirstKindBounded s (x : ℂ) ↔ 0 < christoffelLimit s x := by
  constructor
  · rintro ⟨S, hS0, hS⟩
    rw [christoffelLimit_pos_iff_bddAbove h x]
    refine ⟨S ^ (2 : ℕ), ?_⟩
    rintro y ⟨n, rfl⟩
    show (cdKernel s n x).eval x ≤ S ^ (2 : ℕ)
    rw [← kernelRoot_sq_ofReal h x n]
    exact pow_le_pow_left₀ (kernelRoot_nonneg _ _ _) (hS n) 2
  · intro hpos
    refine ⟨Real.sqrt (christoffelLimit s x)⁻¹,
      Real.sqrt_pos.mpr (inv_pos.mpr hpos), fun N => ?_⟩
    have hKpos := cdKernel_eval_self_pos h N x
    have hle : christoffelLimit s x ≤ christoffel s N x := christoffelLimit_le h N x
    rw [christoffel] at hle
    have h1 : (cdKernel s N x).eval x * christoffelLimit s x ≤ 1 := by
      have h2 := mul_le_mul_of_nonneg_left hle hKpos.le
      rwa [mul_inv_cancel₀ hKpos.ne'] at h2
    have hbd : (cdKernel s N x).eval x ≤ (christoffelLimit s x)⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ hpos]
      exact h1
    have h3 : kernelRoot s (fun j => monicOrthoC s j (x : ℂ)) N ^ (2 : ℕ)
        ≤ (christoffelLimit s x)⁻¹ := by
      rw [kernelRoot_sq_ofReal h x N]
      exact hbd
    calc kernelRoot s (fun j => monicOrthoC s j (x : ℂ)) N
        = Real.sqrt (kernelRoot s (fun j => monicOrthoC s j (x : ℂ)) N ^ (2 : ℕ)) :=
          (Real.sqrt_sq (kernelRoot_nonneg _ _ _)).symm
      _ ≤ Real.sqrt (christoffelLimit s x)⁻¹ := Real.sqrt_le_sqrt h3

end HTGeometry
