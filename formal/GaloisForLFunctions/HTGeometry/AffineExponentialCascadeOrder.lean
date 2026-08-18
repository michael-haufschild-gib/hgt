/-
# Affine postcomposition and the affine-exponential cascade

Exact algebraic-differential order is invariant under `f ↦ a·f + b` for `a ≠ 0`: the jets transform
by the invertible substitution `jetAffineSub`, whose inverse is the substitution for `(a⁻¹, -b/a)`.
No regularity is needed — the identities `deriv_add_const`, `deriv_const_mul_field` and
`iteratedDeriv_const_mul_field` are all unconditional.

The card's family `f_j(w) = a_j + b_j exp(c_j w)` is then reduced to the pure exponential cascade
already carried by `ExpAffineCascade`: composing the affine layer of one map with the exponential of
the next gives `exp(c_{j+1} b_j w + c_{j+1} a_j)`, so a cascade of affine-exponential maps is a
single affine map applied to a cascade of maps `w ↦ exp(α w + β)`.  Hence its minimal
algebraic-differential order is exactly the cascade length.
-/
import GaloisForLFunctions.HTGeometry.ExactDifferentialOrderAffine
import GaloisForLFunctions.HTGeometry.ExpAffineCascade

noncomputable section

open MvPolynomial

namespace GaloisForLFunctions

open GaloisForLFunctions

/-- The jet substitution inverting an affine postcomposition `f ↦ a·f + b`. -/
def jetAffineSub (n : ℕ) (a b : ℂ) : Fin (n + 2) → MvPolynomial (Fin (n + 2)) ℂ :=
  Fin.cases (X 0) (fun j : Fin (n + 1) =>
    Fin.cases (C a⁻¹ * (X (Fin.succ (0 : Fin (n + 1))) - C b))
      (fun l : Fin n => C a⁻¹ * X (Fin.succ (Fin.succ l))) j)

theorem iteratedDeriv_const_mul_add_succ (f : ℂ → ℂ) (a b : ℂ) (l : ℕ) :
    iteratedDeriv (l + 1) (fun z => a * f z + b) = fun z => a * iteratedDeriv (l + 1) f z := by
  rw [iteratedDeriv_succ']
  have hderiv : deriv (fun z => a * f z + b) = fun z => a * deriv f z := by
    funext z
    rw [deriv_add_const, deriv_const_mul_field]
  rw [hderiv, iteratedDeriv_const_mul_field, iteratedDeriv_succ']

theorem DifferentiallyAlgebraicOfOrder.const_mul_add {f : ℂ → ℂ} {n : ℕ}
    (h : DifferentiallyAlgebraicOfOrder f n) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    DifferentiallyAlgebraicOfOrder (fun z => a * f z + b) n := by
  obtain ⟨P, hP0, hPz⟩ := h
  refine ⟨bind₁ (jetAffineSub n a b) P, ?_, ?_⟩
  · intro hzero
    apply hP0
    have hback : bind₁ (jetAffineSub n a⁻¹ (-(b / a))) (bind₁ (jetAffineSub n a b) P) = P := by
      rw [bind₁_bind₁]
      have hσ : (fun i => bind₁ (jetAffineSub n a⁻¹ (-(b / a))) (jetAffineSub n a b i)) =
          (X : Fin (n + 2) → MvPolynomial (Fin (n + 2)) ℂ) := by
        funext i
        have h1 : (C a⁻¹ : MvPolynomial (Fin (n + 2)) ℂ) * C a = 1 := by
          rw [← C_mul, inv_mul_cancel₀ ha, C_1]
        induction i using Fin.cases with
        | zero => simp [jetAffineSub]
        | succ j =>
            induction j using Fin.cases with
            | zero =>
                simp only [jetAffineSub, Fin.cases_succ, Fin.cases_zero, map_mul, map_sub,
                  bind₁_C_right, bind₁_X_right]
                rw [inv_inv, map_neg]
                have h2 : (C a⁻¹ : MvPolynomial (Fin (n + 2)) ℂ) * C b = C (b / a) := by
                  rw [← C_mul]
                  congr 1
                  field_simp
                linear_combination
                  (X (Fin.succ (0 : Fin (n + 1))) + C (b / a)) * h1 - h2
            | succ l =>
                simp only [jetAffineSub, Fin.cases_succ, map_mul, bind₁_C_right, bind₁_X_right]
                rw [inv_inv, ← mul_assoc, h1, one_mul]
      rw [hσ, bind₁_X_left]
      rfl
    rw [← hback, hzero, map_zero]
  · intro z
    rw [eval_bind₁]
    have hvec : (fun i => eval
          (Fin.cons z fun j : Fin (n + 1) =>
            iteratedDeriv (j : ℕ) (fun w => a * f w + b) z)
          (jetAffineSub n a b i)) =
        Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) := by
      funext i
      induction i using Fin.cases with
      | zero => simp [jetAffineSub]
      | succ j =>
          induction j using Fin.cases with
          | zero =>
              simp only [jetAffineSub, Fin.cases_succ, Fin.cases_zero, eval_mul, eval_sub, eval_C,
                eval_X, Fin.cons_succ]
              rw [Fin.val_zero, iteratedDeriv_zero, iteratedDeriv_zero]
              field_simp
              ring
          | succ l =>
              simp only [jetAffineSub, Fin.cases_succ, eval_mul, eval_C, eval_X, Fin.cons_succ]
              rw [Fin.val_succ, iteratedDeriv_const_mul_add_succ f a b (l : ℕ), ← mul_assoc,
                inv_mul_cancel₀ ha, one_mul]
    rw [hvec]
    exact hPz z


theorem differentiallyAlgebraicOfOrder_const_mul_add_iff {f : ℂ → ℂ} {n : ℕ} {a : ℂ} (ha : a ≠ 0)
    (b : ℂ) :
    DifferentiallyAlgebraicOfOrder (fun z => a * f z + b) n ↔
      DifferentiallyAlgebraicOfOrder f n := by
  constructor
  · intro h
    have hback := DifferentiallyAlgebraicOfOrder.const_mul_add h (a := a⁻¹) (inv_ne_zero ha) (-(b / a))
    have heq : (fun z => a⁻¹ * (a * f z + b) + -(b / a)) = f := by
      funext z
      field_simp
      ring
    rwa [heq] at hback
  · intro h
    exact DifferentiallyAlgebraicOfOrder.const_mul_add h ha b

/-- **Exact differential order is invariant under invertible affine postcomposition.** -/
theorem exactDifferentialOrder_const_mul_add_iff {f : ℂ → ℂ} {n : ℕ} {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    ExactDifferentialOrder (fun z => a * f z + b) n ↔ ExactDifferentialOrder f n := by
  simp only [ExactDifferentialOrder, differentiallyAlgebraicOfOrder_const_mul_add_iff ha]

end GaloisForLFunctions

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- The card's affine-exponential maps `w ↦ a_j + b_j·exp(c_j·w)`. -/
noncomputable def affExp (a b c : ℕ → ℂ) (j : ℕ) : ℂ → ℂ :=
  fun w => a j + b j * Complex.exp (c j * w)

/-- Linear part of the exponential cascade absorbing the affine layers. -/
noncomputable def affExpAlpha (b c : ℕ → ℂ) : ℕ → ℂ
  | 0 => c 0
  | (j + 1) => c (j + 1) * b j

/-- Shift of the exponential cascade absorbing the affine layers. -/
noncomputable def affExpBeta (a c : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | (j + 1) => c (j + 1) * a j

/-- **Absorption of the affine layers.**  A cascade of affine-exponential maps is one affine map
applied to a cascade of pure exponentials. -/
theorem entireCascade_affExp (a b c : ℕ → ℂ) (k : ℕ) (z : ℂ) :
    entireCascade (affExp a b c) (k + 1) z
      = a k + b k
        * entireCascade (expAffine (affExpAlpha b c) (affExpBeta a c)) (k + 1) z := by
  induction k with
  | zero =>
      show affExp a b c 0 z = a 0 + b 0 * expAffine (affExpAlpha b c) (affExpBeta a c) 0 z
      rw [affExp, expAffine]
      show a 0 + b 0 * Complex.exp (c 0 * z)
        = a 0 + b 0 * Complex.exp (affExpAlpha b c 0 * z + affExpBeta a c 0)
      rw [show affExpAlpha b c 0 = c 0 from rfl, show affExpBeta a c 0 = 0 from rfl, add_zero]
  | succ k ih =>
      show affExp a b c (k + 1) (entireCascade (affExp a b c) (k + 1) z)
        = a (k + 1) + b (k + 1)
          * expAffine (affExpAlpha b c) (affExpBeta a c) (k + 1)
              (entireCascade (expAffine (affExpAlpha b c) (affExpBeta a c)) (k + 1) z)
      rw [ih, affExp, expAffine]
      show a (k + 1) + b (k + 1)
          * Complex.exp (c (k + 1)
            * (a k + b k * entireCascade (expAffine (affExpAlpha b c) (affExpBeta a c))
                (k + 1) z))
        = a (k + 1) + b (k + 1)
          * Complex.exp (affExpAlpha b c (k + 1)
              * entireCascade (expAffine (affExpAlpha b c) (affExpBeta a c)) (k + 1) z
            + affExpBeta a c (k + 1))
      rw [show affExpAlpha b c (k + 1) = c (k + 1) * b k from rfl,
        show affExpBeta a c (k + 1) = c (k + 1) * a k from rfl]
      ring_nf

/-- **Exact differential order of the affine-exponential cascade.**  A length-`n` composition of
maps `w ↦ a_j + b_j exp(c_j w)` with `b_j, c_j ≠ 0` has minimal algebraic-differential order
exactly `n`. -/
theorem exactDifferentialOrder_affExpCascade {a b c : ℕ → ℂ}
    (hb : ∀ j, b j ≠ 0) (hc : ∀ j, c j ≠ 0) (m : ℕ) :
    ExactDifferentialOrder (entireCascade (affExp a b c) (m + 1)) (m + 1) := by
  have halpha : ∀ k, affExpAlpha b c k ≠ 0 := by
    intro k
    cases k with
    | zero => exact hc 0
    | succ j => exact mul_ne_zero (hc (j + 1)) (hb j)
  have hbase := exactDifferentialOrder_expAffineCascade
    (a := affExpAlpha b c) (b := affExpBeta a c) halpha m
  have hfun : entireCascade (affExp a b c) (m + 1)
      = fun z => b m
        * entireCascade (expAffine (affExpAlpha b c) (affExpBeta a c)) (m + 1) z + a m := by
    funext z
    rw [entireCascade_affExp]
    ring
  rw [hfun]
  exact (exactDifferentialOrder_const_mul_add_iff (hb m) (a m)).mpr hbase

end GaloisForLFunctions.HTGeometry
