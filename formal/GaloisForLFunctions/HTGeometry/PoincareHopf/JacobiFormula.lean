import GaloisForLFunctions.HTGeometry.PoincareHopf.CofactorPermutation
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Jacobi's formula

The derivative of the determinant of a differentiable matrix path is the cofactor pairing with the
derivative of the path:

  `d/dt det (M t) = ∑ i j, cof (M t)_{i j} · (M' t)_{i j}`.

Differentiating the permutation expansion of the determinant produces one term for each pair
(permutation, coordinate hit by the derivative); regrouping those terms by the value of the
permutation at that coordinate reassembles the cofactors.
-/

open Matrix Finset Equiv

namespace GaloisForLFunctions.HTGeometry.PoincareHopf

variable {n : ℕ}

/-- **Jacobi's formula.** -/
theorem hasDerivAt_det {M : ℝ → Matrix (Fin n) (Fin n) ℝ} {M' : Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (h : ∀ i j, HasDerivAt (fun s => M s i j) (M' i j) t) :
    HasDerivAt (fun s => (M s).det) (∑ i, ∑ j, cofSum (M t) i j * M' i j) t := by
  classical
  have hprod : ∀ σ : Equiv.Perm (Fin n),
      HasDerivAt (fun s => ∏ k, M s (σ k) k)
        (∑ l, (∏ k ∈ univ.erase l, M t (σ k) k) * M' (σ l) l) t := by
    intro σ
    have hp := HasDerivAt.finsetProd (u := (univ : Finset (Fin n)))
      (f := fun k s => M s (σ k) k) (f' := fun k => M' (σ k) k) (fun k _ => h (σ k) k)
    have hfun : (∏ k ∈ (univ : Finset (Fin n)), fun s => M s (σ k) k)
        = fun s => ∏ k, M s (σ k) k := by
      funext s
      rw [Finset.prod_apply]
    rw [hfun] at hp
    simpa [smul_eq_mul] using hp
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      HasDerivAt (fun s => ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ k, M s (σ k) k)
        (((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ l, (∏ k ∈ univ.erase l, M t (σ k) k) * M' (σ l) l) t := by
    intro σ
    simpa [smul_eq_mul] using (hprod σ).const_mul (((Equiv.Perm.sign σ : ℤ) : ℝ))
  have hsum := HasDerivAt.sum (u := (univ : Finset (Equiv.Perm (Fin n))))
    (A := fun σ s => ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ k, M s (σ k) k)
    (A' := fun σ => ((Equiv.Perm.sign σ : ℤ) : ℝ) *
      ∑ l, (∏ k ∈ univ.erase l, M t (σ k) k) * M' (σ l) l) (fun σ _ => hterm σ)
  have hfun : (∑ σ ∈ (univ : Finset (Equiv.Perm (Fin n))),
        fun s => ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ k, M s (σ k) k)
      = fun s => (M s).det := by
    funext s
    rw [Finset.sum_apply, Matrix.det_apply']
  rw [hfun] at hsum
  have hreindex : (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ l, (∏ k ∈ univ.erase l, M t (σ k) k) * M' (σ l) l)
      = ∑ i, ∑ j, cofSum (M t) i j * M' i j := by
    have step1 : (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ l, (∏ k ∈ univ.erase l, M t (σ k) k) * M' (σ l) l)
        = ∑ l, ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ((∏ k ∈ univ.erase l, M t (σ k) k) * M' (σ l) l) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun σ _ => Finset.mul_sum _ _ _
    have step2 : ∀ l : Fin n, (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ((∏ k ∈ univ.erase l, M t (σ k) k) * M' (σ l) l))
        = ∑ i, cofSum (M t) i l * M' i l := by
      intro l
      have hpart : ∀ σ : Equiv.Perm (Fin n),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((∏ k ∈ univ.erase l, M t (σ k) k) * M' (σ l) l)
            = ∑ i, if σ l = i then
                ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ k ∈ univ.erase l, M t (σ k) k) * M' i l
              else 0 := by
        intro σ
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_assoc]
      rw [Finset.sum_congr rfl fun σ _ => hpart σ, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [cofSum, Finset.sum_mul, Finset.sum_filter]
    rw [step1, Finset.sum_congr rfl fun l _ => step2 l, Finset.sum_comm]
  rw [hreindex] at hsum
  exact hsum

end GaloisForLFunctions.HTGeometry.PoincareHopf
