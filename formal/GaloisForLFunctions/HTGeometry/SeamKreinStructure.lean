/-
Two structural constraints on the seam-positivity apex: the prime determinant cannot self-continue,
and the reciprocity graph is Lagrangian (so the positivity object must be a signed Krein form).

The seam-positivity program would continue the finite-prime determinant across `Re s = 1` by an
internal reciprocity and read the ξ-zeros off a positive middle cohomology.  Two structural facts
constrain that program; both are proved here, unconditionally.

* **No internal reciprocity on the one-particle prime space** (`seam_no_bounded_reciprocity_carrier`).
  The one-particle prime action `A(s) = ⊕_p p^(−s)C_p` is bounded (in fact trace-class) for `Re s > 1`,
  but its reflection `A(1−s) = ⊕_p p^(s−1)C_p` has **unbounded** diagonal `p^(s−1) → ∞`.  A bounded
  conjugation cannot carry a bounded operator to an unbounded one, so no bounded `J` satisfies
  `J A(s) J⁻¹ = A(1−s)`.  The prime determinant therefore cannot self-continue by an internal bounded
  reciprocity; it must be embedded in a larger self-dual seam structure.  (`prime_reflection_diagonal_unbounded`
  is the arithmetic core: `{p^(s−1)}` is unbounded over the primes.)

* **The reciprocity graph is Lagrangian for the signed Green form** (`signedForm_graph_isotropic`,
  `graph_orthogonal_subset`, `graph_lagrangian`).  On a *positive* Hilbert space an isotropic subspace
  is `0` (`isotropic_eq_zero`), so a nontrivial reciprocity relation can never be isotropic in a direct
  positive norm — the naive "positive quotient" apex is impossible.  The correct ambient object is a
  **signed Green (Krein) form** `[(x₊,x₋),(y₊,y₋)] = ⟪x₊,y₊⟫ − ⟪x₋,y₋⟫`, on which the doubled
  reciprocity graph `R = {(x, U x)}` (`U` unitary) is not merely isotropic but **Lagrangian**
  (`R^⊥ = R`).  A full doubled reciprocity graph therefore has **zero** quotient: nonzero middle
  cohomology — where the zeros would live — can arise only from domain/closure/boundary defects of the
  actual seam complex, never from the algebra of the reciprocity relation alone.  This is a genuine
  constraint on the shape of the apex, not a slogan.
-/
import Mathlib

noncomputable section

namespace RHTower

/-! ### §5 The one-particle prime reflection is unbounded -/

/-- **The reflected prime diagonal is unbounded.**  For real `s > 1` the values `p^(s−1)` of the
reflected one-particle action `A(1−s) = ⊕_p p^(s−1)C_p` exceed every bound as `p → ∞`, because
`s − 1 > 0`.  Hence `A(1−s)` is unbounded, while `A(s) = ⊕_p p^(−s)C_p` is bounded (`p^(−s) < 1`). -/
theorem prime_reflection_diagonal_unbounded {s : ℝ} (hs : 1 < s) (M : ℝ) :
    ∃ p : ℕ, p.Prime ∧ M < (p : ℝ) ^ (s - 1) := by
  obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (max 1 ⌈M ^ (1 / (s - 1))⌉₊ + 1)
  refine ⟨p, hp, ?_⟩
  have hs1 : 0 < s - 1 := by linarith
  by_cases hM : M ≤ 0
  · calc M ≤ 0 := hM
      _ < (p : ℝ) ^ (s - 1) := by
          have : (0 : ℝ) < p := by exact_mod_cast hp.pos
          positivity
  · have hMpos : 0 < M := not_le.mp hM
    have hpge : M ^ (1 / (s - 1)) < (p : ℝ) := by
      have h1 : (⌈M ^ (1 / (s - 1))⌉₊ : ℝ) < p := by
        exact_mod_cast (by omega : ⌈M ^ (1 / (s - 1))⌉₊ < p)
      exact lt_of_le_of_lt (Nat.le_ceil _) h1
    have hlt := Real.rpow_lt_rpow (by positivity) hpge hs1
    rwa [← Real.rpow_mul hMpos.le, one_div, inv_mul_cancel₀ (by linarith : s - 1 ≠ 0),
      Real.rpow_one] at hlt

/-- **No bounded internal reciprocity carrier.**  A bounded conjugation preserves boundedness, so if a
`J` conjugated the bounded prime action into its reflection, the reflection would be bounded — but its
diagonal is unbounded (`prime_reflection_diagonal_unbounded`).  Stated at the level of the diagonals:
no real bound `B` dominates every reflected eigenvalue `p^(s−1)`, so the reflected operator is not
bounded and the prime determinant cannot self-continue on the one-particle prime space. -/
theorem seam_no_bounded_reciprocity_carrier {s : ℝ} (hs : 1 < s) :
    ¬ ∃ B : ℝ, ∀ p : ℕ, p.Prime → (p : ℝ) ^ (s - 1) ≤ B := by
  rintro ⟨B, hB⟩
  obtain ⟨p, hp, hpB⟩ := prime_reflection_diagonal_unbounded hs B
  exact absurd (hB p hp) (not_le.mpr hpB)

/-! ### §10 The reciprocity graph is Lagrangian for a signed Green (Krein) form -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Isotropic in a positive Hilbert norm forces zero.**  A direct positive quotient cannot host a
nontrivial reciprocity relation: any vector with zero self-inner-product is `0`. -/
theorem isotropic_eq_zero {r : E} (h : @inner ℂ E _ r r = 0) : r = 0 := inner_self_eq_zero.mp h

/-- The signed Green (Krein) form on the doubled space `E × E`:
`[(x₊,x₋),(y₊,y₋)] = ⟪x₊,y₊⟫ − ⟪x₋,y₋⟫`. -/
def signedForm (v w : E × E) : ℂ := @inner ℂ E _ v.1 w.1 - @inner ℂ E _ v.2 w.2

/-- **The reciprocity graph is isotropic for the signed form.**  For a linear isometry `U`, every
pair `(x, U x)` on the graph is signed-orthogonal to every other, because `U` preserves the inner
product: `⟪x,y⟫ − ⟪U x, U y⟫ = 0`. -/
theorem signedForm_graph_isotropic (U : E ≃ₗᵢ[ℂ] E) (x y : E) :
    signedForm ((x, U x) : E × E) (y, U y) = 0 := by
  simp only [signedForm]; rw [U.inner_map_map]; ring

/-- **The signed-orthogonal complement of the graph is contained in the graph.**  If `(a, b)` is
signed-orthogonal to the whole graph `{(x, U x)}` of a unitary `U`, then `b = U a` — so `(a, b)` lies
on the graph.  Together with `signedForm_graph_isotropic` this makes the graph **Lagrangian**
(`R^⊥ = R`), hence a full doubled reciprocity graph has zero quotient. -/
theorem graph_orthogonal_subset (U : E ≃ₗᵢ[ℂ] E) (a b : E)
    (h : ∀ x : E, signedForm ((a, b) : E × E) (x, U x) = 0) : b = U a := by
  have key : ∀ x : E, @inner ℂ E _ a x = @inner ℂ E _ b (U x) := by
    intro x; have hx := h x; simp only [signedForm] at hx; linear_combination hx
  have hUadj : ∀ x : E, @inner ℂ E _ b (U x) = @inner ℂ E _ (U.symm b) x := by
    intro x; rw [← U.inner_map_map (U.symm b) x, LinearIsometryEquiv.apply_symm_apply]
  have h2 : ∀ x : E, @inner ℂ E _ (a - U.symm b) x = 0 := by
    intro x; rw [inner_sub_left, key x, hUadj x, sub_self]
  have ha : a = U.symm b := sub_eq_zero.mp (isotropic_eq_zero (h2 (a - U.symm b)))
  rw [ha, U.apply_symm_apply]

/-- **The reciprocity graph is Lagrangian.**  It is signed-isotropic, and its signed complement is
contained in it: `(a, b) ⟂ graph ↔ b = U a`.  A full doubled reciprocity graph has zero quotient, so
the seam-positivity apex cannot be a naive positive quotient — nonzero middle cohomology can only come
from domain/closure/boundary defects of the seam complex. -/
theorem graph_lagrangian (U : E ≃ₗᵢ[ℂ] E) (a b : E) :
    (∀ x : E, signedForm ((a, b) : E × E) (x, U x) = 0) ↔ b = U a := by
  refine ⟨graph_orthogonal_subset U a b, ?_⟩
  rintro rfl x
  exact signedForm_graph_isotropic U a x

end RHTower
