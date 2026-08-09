import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Separating functionals detect linear independence

A finite independent family is separated by a finite sample of any *separating* family of functionals:
there are indices `x₁,…,xₙ` at which the matrix `[Φ_{xⱼ}(fᵢ)]` is invertible.

* **`exists_det_ne_zero_of_linearIndependent_of_separating`** — the general law.  Induction on `n`: expand
  the determinant along the last column, which by linearity presents it as `Φ_t(∑ᵢ cᵢ fᵢ)` with the last
  coefficient the (nonzero, by induction) smaller determinant; independence makes that combination a nonzero
  vector, and separation finds an index where a functional does not kill it;
* `exists_det_ne_zero_of_linearIndependent`, `not_linearIndependent_of_forall_det_eq_zero` — the
  point-evaluation case, for `K`-valued functions on any domain, and its contrapositive: a determinant
  vanishing at *every* sample forces a linear relation;
* `exists_det_inner_ne_zero_of_linearIndependent` — the inner-product case: independent vectors have an
  invertible cross-Gram matrix against some finite sample of test vectors.

Only `Field K` and the separation property are assumed; no topology, no finite-dimensionality.
-/

noncomputable section

namespace RHTower

/-- **Separating functionals detect independence.**  If the functionals `Φ` kill no nonzero vector, then a
linearly independent family has a finite sample of them with invertible evaluation matrix. -/
theorem exists_det_ne_zero_of_linearIndependent_of_separating
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Φ : ι → (V →ₗ[K] K)) (hsep : ∀ v : V, v ≠ 0 → ∃ i, Φ i v ≠ 0) :
    ∀ {n : ℕ} (f : Fin n → V), LinearIndependent K f →
      ∃ x : Fin n → ι, (Matrix.of fun a b => Φ (x b) (f a)).det ≠ 0 := by
  intro n
  induction n with
  | zero =>
      intro f _
      exact ⟨Fin.elim0, by rw [Matrix.det_fin_zero]; exact one_ne_zero⟩
  | succ n ih =>
      intro f hf
      obtain ⟨x, hx⟩ := ih (fun i => f i.castSucc) (hf.comp Fin.castSucc (Fin.castSucc_injective n))
      set y : ι → Fin (n + 1) → ι := fun t => (Fin.snoc x t : Fin (n + 1) → ι) with hy
      have hylast : ∀ t : ι, y t (Fin.last n) = t := by intro t; simp [hy]
      have hycast : ∀ (t : ι) (j : Fin n), y t j.castSucc = x j := by intro t j; simp [hy]
      -- the coefficients of the last-column expansion
      set c : Fin (n + 1) → K := fun a =>
        (-1 : K) ^ ((a : ℕ) + ((Fin.last n : Fin (n + 1)) : ℕ))
          * (Matrix.of fun (a' b : Fin n) => Φ (x b) (f (a.succAbove a'))).det with hc
      have hexp : ∀ t : ι,
          (Matrix.of fun (a b : Fin (n + 1)) => Φ (y t b) (f a)).det = Φ t (∑ a, c a • f a) := by
        intro t
        rw [Matrix.det_succ_column _ (Fin.last n), map_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        have hminor : ((Matrix.of fun (a b : Fin (n + 1)) => Φ (y t b) (f a)).submatrix
              a.succAbove (Fin.last n).succAbove)
            = Matrix.of fun (a' b : Fin n) => Φ (x b) (f (a.succAbove a')) := by
          refine Matrix.ext fun a' b => ?_
          simp [Fin.succAbove_last, hycast]
        rw [hminor, hc]
        simp only [Matrix.of_apply, hylast, map_smul, smul_eq_mul]
        ring
      -- the last coefficient is the determinant supplied by the induction hypothesis
      have hclast : c (Fin.last n) ≠ 0 := by
        have hsign : ((-1 : K) ^ (((Fin.last n : Fin (n + 1)) : ℕ)
            + ((Fin.last n : Fin (n + 1)) : ℕ))) = 1 := by
          rw [← two_mul, pow_mul]
          norm_num
        have hmin : (Matrix.of fun (a' b : Fin n) => Φ (x b) (f ((Fin.last n).succAbove a')))
            = Matrix.of fun (a' b : Fin n) => Φ (x b) (f a'.castSucc) := by
          refine Matrix.ext fun a' b => ?_
          simp [Fin.succAbove_last]
        rw [hc]
        simp only [hsign, hmin, one_mul]
        exact hx
      -- the combination is a nonzero vector, so some functional does not kill it
      have hvne : (∑ a, c a • f a) ≠ 0 := by
        intro h
        exact hclast (Fintype.linearIndependent_iff.1 hf c h (Fin.last n))
      obtain ⟨t, ht⟩ := hsep _ hvne
      refine ⟨y t, ?_⟩
      rw [hexp t]
      exact ht

variable {K α : Type*} [Field K]

/-- **Point evaluations detect independence.**  For a linearly independent family of `K`-valued functions
there are sample points making the evaluation matrix invertible. -/
theorem exists_det_ne_zero_of_linearIndependent {n : ℕ} (f : Fin n → (α → K))
    (hf : LinearIndependent K f) :
    ∃ x : Fin n → α, (Matrix.of fun i j => f i (x j)).det ≠ 0 :=
  exists_det_ne_zero_of_linearIndependent_of_separating
    (fun a : α => (LinearMap.proj a : (α → K) →ₗ[K] K))
    (fun v hv => by
      obtain ⟨a, ha⟩ := Function.ne_iff.1 hv
      exact ⟨a, ha⟩) f hf

/-- **A determinant vanishing at every sample forces a relation.**  The contrapositive form. -/
theorem not_linearIndependent_of_forall_det_eq_zero {n : ℕ} (f : Fin n → (α → K))
    (h : ∀ x : Fin n → α, (Matrix.of fun i j => f i (x j)).det = 0) :
    ¬ LinearIndependent K f := fun hf => by
  obtain ⟨x, hx⟩ := exists_det_ne_zero_of_linearIndependent f hf
  exact hx (h x)

/-- **Inner products detect independence.**  Independent vectors of an inner product space have an
invertible cross-Gram matrix against a finite sample of test vectors. -/
theorem exists_det_inner_ne_zero_of_linearIndependent {𝕜 H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {n : ℕ} (f : Fin n → H)
    (hf : LinearIndependent 𝕜 f) :
    ∃ w : Fin n → H, (Matrix.of fun a b => inner 𝕜 (w b) (f a)).det ≠ 0 :=
  exists_det_ne_zero_of_linearIndependent_of_separating
    (fun w : H => (innerSL 𝕜 w).toLinearMap)
    (fun v hv => ⟨v, fun h => hv (inner_self_eq_zero.1 h)⟩) f hf

end RHTower

end
