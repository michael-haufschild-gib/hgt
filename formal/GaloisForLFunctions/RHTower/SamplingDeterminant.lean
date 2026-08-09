import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Sampling detects linear independence

A finite family of functions is linearly independent exactly when some finite sample of points separates
it: there are points `x₁,…,xₙ` at which the evaluation matrix `[fᵢ(xⱼ)]` is invertible.

* `exists_det_ne_zero_of_linearIndependent` — independence produces such a sample, by induction: expand the
  determinant along the last column, which exhibits `t ↦ det[fᵢ(x₁),…,fᵢ(xₙ₋₁),fᵢ(t)]` as a combination of
  the `fᵢ` whose leading coefficient is the (nonzero, by induction) smaller determinant, so independence
  forbids it from vanishing identically;
* `not_linearIndependent_of_forall_det_eq_zero` — the contrapositive, which is the usable direction: a
  determinant vanishing at *every* sample forces a linear relation among the functions.

Both statements are for arbitrary functions into a field, with no structure on the domain.
-/

noncomputable section

namespace RHTower

variable {K α : Type*} [Field K]

/-- **Independence is detected by a finite sample.**  For a linearly independent family of `K`-valued
functions there are sample points making the evaluation matrix invertible. -/
theorem exists_det_ne_zero_of_linearIndependent :
    ∀ {n : ℕ} (f : Fin n → (α → K)), LinearIndependent K f →
      ∃ x : Fin n → α, (Matrix.of fun i j => f i (x j)).det ≠ 0 := by
  intro n
  induction n with
  | zero =>
      intro f _
      exact ⟨Fin.elim0, by rw [Matrix.det_fin_zero]; exact one_ne_zero⟩
  | succ n ih =>
      intro f hf
      obtain ⟨x, hx⟩ := ih (fun i => f i.castSucc) (hf.comp Fin.castSucc (Fin.castSucc_injective n))
      set y : α → Fin (n + 1) → α := fun t => (Fin.snoc x t : Fin (n + 1) → α) with hy
      have hylast : ∀ t : α, y t (Fin.last n) = t := by intro t; simp [hy]
      have hycast : ∀ (t : α) (j : Fin n), y t j.castSucc = x j := by intro t j; simp [hy]
      -- the coefficients of the last-column expansion
      set c : Fin (n + 1) → K := fun i =>
        (-1 : K) ^ ((i : ℕ) + ((Fin.last n : Fin (n + 1)) : ℕ))
          * (Matrix.of fun (i' j : Fin n) => f (i.succAbove i') (x j)).det with hc
      have hexp : ∀ t : α,
          (Matrix.of fun (i j : Fin (n + 1)) => f i (y t j)).det = ∑ i, c i * f i t := by
        intro t
        rw [Matrix.det_succ_column _ (Fin.last n)]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hminor : ((Matrix.of fun (i j : Fin (n + 1)) => f i (y t j)).submatrix
              i.succAbove (Fin.last n).succAbove)
            = Matrix.of fun (i' j : Fin n) => f (i.succAbove i') (x j) := by
          refine Matrix.ext fun i' j => ?_
          simp [Fin.succAbove_last, hycast]
        rw [hminor, hc]
        simp only [Matrix.of_apply, hylast]
        ring
      -- the last coefficient is the determinant supplied by the induction hypothesis
      have hclast : c (Fin.last n) ≠ 0 := by
        have hsign : ((-1 : K) ^ (((Fin.last n : Fin (n + 1)) : ℕ)
            + ((Fin.last n : Fin (n + 1)) : ℕ))) = 1 := by
          rw [← two_mul, pow_mul]
          norm_num
        have hmin : (Matrix.of fun (i' j : Fin n) => f ((Fin.last n).succAbove i') (x j))
            = Matrix.of fun (i' j : Fin n) => f i'.castSucc (x j) := by
          refine Matrix.ext fun i' j => ?_
          simp [Fin.succAbove_last]
        rw [hc]
        simp only [hsign, hmin, one_mul]
        exact hx
      -- so the expansion is a nontrivial relation and cannot vanish identically
      have hne : ∃ t : α, (∑ i, c i * f i t) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        have hrel : ∑ i, c i • f i = (0 : α → K) := by
          funext t
          simpa using hcon t
        exact hclast (Fintype.linearIndependent_iff.1 hf c hrel (Fin.last n))
      obtain ⟨t, ht⟩ := hne
      refine ⟨y t, ?_⟩
      rw [hexp t]
      exact ht

/-- **A determinant vanishing at every sample forces a relation.**  The contrapositive form. -/
theorem not_linearIndependent_of_forall_det_eq_zero {n : ℕ} (f : Fin n → (α → K))
    (h : ∀ x : Fin n → α, (Matrix.of fun i j => f i (x j)).det = 0) :
    ¬ LinearIndependent K f := fun hf => by
  obtain ⟨x, hx⟩ := exists_det_ne_zero_of_linearIndependent f hf
  exact hx (h x)

end RHTower

end
