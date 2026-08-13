import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Triangular substitutions in countably many variables

A substitution `X n ↦ c * X n + q n`, with `q n` involving only variables below `n`, is
injective over a field whenever `c ≠ 0`.  The proof constructs a left inverse by strong recursion.
This form handles infinitely many variables because every multivariate polynomial has finite
support; no topology or completion is used.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

/-- Recursive inverse coordinates for a triangular substitution. -/
def triangularMvPolynomialInverseVar {K : Type*} [Field K]
    (c : K) (q : ℕ → MvPolynomial ℕ K) (n : ℕ) : MvPolynomial ℕ K :=
  Nat.strongRec (motive := fun _ => MvPolynomial ℕ K)
    (fun n ih =>
      C c⁻¹ * (X n - eval₂ C
        (fun i => if _ : i < n then ih i (by assumption) else 0) (q n))) n

theorem triangularMvPolynomialInverseVar_eq {K : Type*} [Field K]
    (c : K) (q : ℕ → MvPolynomial ℕ K) (n : ℕ) :
    triangularMvPolynomialInverseVar c q n =
      C c⁻¹ * (X n - eval₂ C
        (fun i => if _ : i < n then triangularMvPolynomialInverseVar c q i else 0) (q n)) := by
  rw [triangularMvPolynomialInverseVar, Nat.strongRec_eq]
  congr 4

/-- The triangular coordinate family `c X_n + q_n`. -/
def triangularMvPolynomial {K : Type*} [Field K]
    (c : K) (q : ℕ → MvPolynomial ℕ K) (n : ℕ) : MvPolynomial ℕ K :=
  C c * X n + q n

theorem triangularMvPolynomialInverse_eval_remainder {K : Type*} [Field K]
    (c : K) (q : ℕ → MvPolynomial ℕ K)
    (hq : ∀ n i, i ∈ (q n).vars → i < n) (n : ℕ) :
    eval₂ C (triangularMvPolynomialInverseVar c q) (q n) =
      eval₂ C
        (fun i => if _ : i < n then triangularMvPolynomialInverseVar c q i else 0) (q n) := by
  apply MvPolynomial.eval₂_congr
  intro i d hid hcoeff
  have hi := hq n i
    ((MvPolynomial.mem_vars_iff_mem_support i).mpr
      ⟨d, MvPolynomial.mem_support_iff.mpr hcoeff, hid⟩)
  simp [hi]

theorem triangularMvPolynomialInverse_eval {K : Type*} [Field K]
    (c : K) (hc : c ≠ 0) (q : ℕ → MvPolynomial ℕ K)
    (hq : ∀ n i, i ∈ (q n).vars → i < n) (n : ℕ) :
    eval₂ C (triangularMvPolynomialInverseVar c q)
        (triangularMvPolynomial c q n) = X n := by
  rw [triangularMvPolynomial, eval₂_add, eval₂_mul, eval₂_C, eval₂_X]
  rw [triangularMvPolynomialInverseVar_eq]
  rw [triangularMvPolynomialInverse_eval_remainder c q hq]
  rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hc]
  simp

/-- A countable lower-triangular polynomial substitution with nonzero constant diagonal is
injective. -/
theorem triangularMvPolynomial_eval₂Hom_injective {K : Type*} [Field K]
    (c : K) (hc : c ≠ 0) (q : ℕ → MvPolynomial ℕ K)
    (hq : ∀ n i, i ∈ (q n).vars → i < n) :
    Function.Injective (eval₂Hom C (triangularMvPolynomial c q)) := by
  let left : MvPolynomial ℕ K →+* MvPolynomial ℕ K :=
    eval₂Hom C (triangularMvPolynomialInverseVar c q)
  have hleft : left.comp (eval₂Hom C (triangularMvPolynomial c q)) =
      RingHom.id (MvPolynomial ℕ K) := by
    apply MvPolynomial.ringHom_ext
    · intro k
      simp [left]
    · intro n
      simp only [RingHom.comp_apply, eval₂Hom_X', RingHom.id_apply]
      dsimp only [left]
      change eval₂ C (triangularMvPolynomialInverseVar c q)
          (triangularMvPolynomial c q n) = X n
      exact triangularMvPolynomialInverse_eval c hc q hq n
  intro p r hpr
  have hmap := congrArg left hpr
  have hp := DFunLike.congr_fun hleft p
  have hr := DFunLike.congr_fun hleft r
  exact hp.symm.trans (hmap.trans hr)

end

end GaloisForLFunctions.HTGeometry
