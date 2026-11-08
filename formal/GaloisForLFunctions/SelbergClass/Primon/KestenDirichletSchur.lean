import GaloisForLFunctions.SelbergClass.Primon.KestenDirichletGreen
import GaloisForLFunctions.SelbergClass.Primon.KestenGreenConditioning

/-!
# Dirichlet inversion as a terminal Schur complement

The finite Dirichlet Green matrix is the Schur complement of the next
site in the infinite Green covariance. This identifies its rank-one
correction with the coefficient of Gaussian terminal regression.
-/

open _root_.RHTower
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Propagation from a finite section to its next terminal site. -/
theorem kestenGreenEntry_terminal_step (p : Nat.Primes) (n : ℕ) (i : Fin (n + 1)) :
    kestenGreenEntry p i (n + 1) = primeReciprocal p * kestenGreenEntry p i n := by
  have hi : i.val ≤ n := by omega
  have h0 := kestenGreenEntry_propagation p i (n - i.val)
  have h1 := kestenGreenEntry_propagation p i (n - i.val + 1)
  rw [Nat.add_sub_of_le hi] at h0
  rw [show i.val + (n - i.val + 1) = n + 1 by omega, pow_succ] at h1
  rw [h1, h0]
  ring

/-- The Woodbury scalar is the squared one-step propagation divided by terminal variance. -/
theorem kestenDirichletCorrection_eq_terminal_variance (p : Nat.Primes) (n : ℕ) :
    kestenDirichletCorrection p n =
      primeReciprocal p ^ 2 / kestenGreenEntry p (n + 1) (n + 1) := by
  have hq := (primeReciprocal_pos p).ne'
  have hd := (add_pos (inv_pos.mpr (primeReciprocal_pos p))
    (kestenGreenEntry_pos p n n)).ne'
  have ht := (kestenGreenEntry_pos p (n + 1) (n + 1)).ne'
  rw [kestenDirichletCorrection]
  apply (eq_div_iff ht).mpr
  rw [kestenGreenEntry_variance_recursion]
  field_simp [hq, hd] <;> ring

/-- Removing the next terminal coordinate gives exactly the Dirichlet inverse. -/
theorem kestenDirichletGreen_eq_terminal_schur (p : Nat.Primes) (n : ℕ)
    (i j : Fin (n + 1)) :
    kestenDirichletGreen p n i j = kestenGreenEntry p i j -
      kestenGreenEntry p i (n + 1) * kestenGreenEntry p (n + 1) j /
        kestenGreenEntry p (n + 1) (n + 1) := by
  rw [kestenDirichletGreen_entry, kestenDirichletCorrection_eq_terminal_variance,
    kestenGreenEntry_symm p (n + 1) j,
    kestenGreenEntry_terminal_step p n i, kestenGreenEntry_terminal_step p n j]
  ring

end
end GaloisForLFunctions.SelbergClass.Primon

#print axioms GaloisForLFunctions.SelbergClass.Primon.kestenGreenEntry_terminal_step
#print axioms GaloisForLFunctions.SelbergClass.Primon.kestenDirichletCorrection_eq_terminal_variance
#print axioms GaloisForLFunctions.SelbergClass.Primon.kestenDirichletGreen_eq_terminal_schur
