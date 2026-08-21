import GaloisForLFunctions.HTGeometry.ShiftedMatrixDegree

/-!
# Constant changes of basis do not move the matrix degree

A shear `diag(∂^{k_i})` is only a *diagonal* change of lattice, and a diagonal change is not enough
to decide the phase: for `A = I + ∂M` with `M` a nonzero nilpotent constant matrix the twisted chain
`A_n = I + n∂M` has bounded degree, yet every shear leaves the shifted degree at least one.  A
constant change of basis puts `M` in Jordan form and then a shear works.

Constant changes of basis are free: multiplying by matrices whose entries all have degree zero
cannot raise the matrix degree, and the twisted chain of a constant conjugate is the constant
conjugate of the twisted chain — with the right-hand factor twisted `n` times.  So the bounded phase
is detected by a pair (constant basis, shear), and the criterion is invariant.

* `matDeg_mul_le`, `matDeg_mul_le_of_deg_zero`;
* `twistedChain_conj` — **the twisted chain of a constant conjugate**;
* `matDeg_twistedChain_le_conj` — the degree does not go up;
* `matDeg_twistedChain_le_of_conj_shiftDegLE_zero` — **the bounded phase from a constant basis and
  a shear**.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
theorem matDeg_mul_le (P Q : Matrix ι ι (DiffOp K)) :
    matDeg (P * Q) ≤ matDeg P + matDeg Q :=
  matDeg_le fun i j =>
    degree_matrix_mul_le P Q (matDeg P) (matDeg Q)
      (fun i j => degree_le_matDeg P i j) (fun i j => degree_le_matDeg Q i j) i j

omit [DecidableEq ι] [Nonempty ι] in
/-- Multiplying by matrices of degree zero cannot raise the matrix degree. -/
theorem matDeg_mul_le_of_deg_zero {C C' P : Matrix ι ι (DiffOp K)}
    (hC : matDeg C = 0) (hC' : matDeg C' = 0) : matDeg (C * P * C') ≤ matDeg P := by
  have h1 := matDeg_mul_le (C * P) C'
  have h2 := matDeg_mul_le C P
  omega

omit [Nonempty ι] in
/-- **The twisted chain of a constant conjugate.** -/
theorem twistedChain_conj (σ : DiffOp K →+* DiffOp K) (S S' A : Matrix ι ι (DiffOp K))
    (hSS : S * S' = 1) (hS'S : S' * S = 1) (n : ℕ) :
    twistedChain σ (S' * A * S.map σ) n
      = S' * twistedChain σ A n * S.map (iterHom σ n) := by
  have hcancel : ∀ m : ℕ, S.map (iterHom σ m) * S'.map (iterHom σ m) = 1 := by
    intro m
    rw [← Matrix.map_mul, hSS]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  induction n with
  | zero =>
      show (1 : Matrix ι ι (DiffOp K)) = S' * 1 * S.map (iterHom σ 0)
      have hid : S.map (iterHom σ 0) = S := by
        ext i j
        rfl
      rw [hid, mul_one]
      exact hS'S.symm
  | succ n ih =>
      rw [twistedChain_succ, ih, twistedFamily]
      have hmap : (S' * A * S.map σ).map (iterHom σ n)
          = S'.map (iterHom σ n) * A.map (iterHom σ n) * S.map (iterHom σ (n + 1)) := by
        have hcomm : ∀ p : DiffOp K, iterHom σ n (σ p) = iterHom σ (n + 1) p := by
          intro p
          rw [iterHom_add σ n 1, RingHom.comp_apply]
          rfl
        rw [Matrix.map_mul, Matrix.map_mul]
        congr 1
        refine Matrix.ext fun i j => ?_
        rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply]
        exact hcomm (S i j)
      rw [hmap, twistedChain_succ, twistedFamily]
      calc S' * twistedChain σ A n * S.map (iterHom σ n)
            * (S'.map (iterHom σ n) * A.map (iterHom σ n) * S.map (iterHom σ (n + 1)))
          = S' * twistedChain σ A n * (S.map (iterHom σ n) * S'.map (iterHom σ n))
              * (A.map (iterHom σ n) * S.map (iterHom σ (n + 1))) := by
            simp only [Matrix.mul_assoc]
        _ = S' * (twistedChain σ A n * A.map (iterHom σ n)) * S.map (iterHom σ (n + 1)) := by
            rw [hcancel n]
            simp only [Matrix.mul_assoc, Matrix.mul_one]

omit [DecidableEq ι] [Nonempty ι] in
theorem matDeg_map_eq_zero (σ : DiffOp K →+* DiffOp K) (hσ : ∀ p, degree (σ p) = degree p)
    {S : Matrix ι ι (DiffOp K)} (hS : matDeg S = 0) (m : ℕ) :
    matDeg (S.map (iterHom σ m)) = 0 := by
  have hiter : ∀ (t : ℕ) (p : DiffOp K), degree (iterHom σ t p) = degree p := by
    intro t
    induction t with
    | zero => exact fun p => rfl
    | succ t ih =>
        intro p
        rw [iterHom, RingHom.comp_apply, hσ, ih]
  refine Nat.le_zero.mp (le_trans (matDeg_le fun i j => ?_) (le_of_eq hS))
  rw [Matrix.map_apply, hiter]
  exact degree_le_matDeg S i j

omit [Nonempty ι] in
/-- The constant conjugate has at least the matrix degree of the original. -/
theorem matDeg_twistedChain_le_conj (σ : DiffOp K →+* DiffOp K)
    (hσ : ∀ p, degree (σ p) = degree p) (S S' A : Matrix ι ι (DiffOp K))
    (hSS : S * S' = 1) (hS'S : S' * S = 1) (hS : matDeg S = 0) (hS' : matDeg S' = 0) (n : ℕ) :
    matDeg (twistedChain σ A n) ≤ matDeg (twistedChain σ (S' * A * S.map σ) n) := by
  have hcancel : S.map (iterHom σ n) * S'.map (iterHom σ n) = 1 := by
    rw [← Matrix.map_mul, hSS]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hback : twistedChain σ A n
      = S * twistedChain σ (S' * A * S.map σ) n * S'.map (iterHom σ n) := by
    rw [twistedChain_conj σ S S' A hSS hS'S n]
    calc twistedChain σ A n
        = S * S' * twistedChain σ A n
            * (S.map (iterHom σ n) * S'.map (iterHom σ n)) := by
          rw [hSS, hcancel, mul_one, one_mul]
      _ = S * (S' * twistedChain σ A n * S.map (iterHom σ n)) * S'.map (iterHom σ n) := by
          simp only [Matrix.mul_assoc]
  rw [hback]
  exact matDeg_mul_le_of_deg_zero hS (matDeg_map_eq_zero σ hσ hS' n)

/-- **The bounded phase from a constant basis and a shear.**  If some constant change of basis makes
the shifted degree vanish for some shear, the whole twisted chain stays inside a band of width the
spread of the shear. -/
theorem matDeg_twistedChain_le_of_conj_shiftDegLE_zero (k : ι → ℤ) (σ : DiffOp K →+* DiffOp K)
    (hσ : ∀ p, degree (σ p) = degree p) (S S' A : Matrix ι ι (DiffOp K))
    (hSS : S * S' = 1) (hS'S : S' * S = 1) (hS : matDeg S = 0) (hS' : matDeg S' = 0)
    (hC : ShiftDegLE k (S' * A * S.map σ) 0) (n : ℕ) :
    (matDeg (twistedChain σ A n) : ℤ) ≤ shearSpread k := by
  have h1 := matDeg_twistedChain_le_conj σ hσ S S' A hSS hS'S hS hS' n
  have h2 := matDeg_twistedChain_le_of_shiftDegLE_zero k σ hσ hC n
  have h1' : (matDeg (twistedChain σ A n) : ℤ)
      ≤ (matDeg (twistedChain σ (S' * A * S.map σ) n) : ℤ) := by exact_mod_cast h1
  linarith

end

end DiffOp

end GaloisForLFunctions.HTGeometry
