import GaloisForLFunctions.RHTower.PolyatomicSourceApplications
import GaloisForLFunctions.RHTower.DeningerRationalWittHazewinkelHankel

/-!
# Exact infinite rank of the collision Laplace separation

Equation (29) of arXiv:2608.29825 separates a fractional energy denominator by
an exact continuous Laplace integral. Combining its completed features with the
corpus's Gamma atoms and rational-Witt Hankel machinery gives a sharp boundary:
no fixed finite separable tensor represents the kernel exactly, and its
sampled Hankel series has no normalized rational representation. The positive
survivor is full rank at every finite size, proved through actual Hilbert atoms.
This does not obstruct finite approximations such as the paper's quadrature.
-/

open scoped BigOperators InnerProductSpace
open GaloisForLFunctions.HTGeometry
namespace RHTower
noncomputable section

/-- Exact Gamma-weighted samples of the fractional collision denominator. -/
def polyatomicHankelMoment (a : ℝ) (n : ℕ) : ℂ :=
  ↑(Real.Gamma (Real.exp a) * (2 + (n : ℝ)) ^ (-Real.exp a))

/-- The sampled moment matrix is the Gram matrix of existing Gamma atoms. -/
theorem gammaLaplaceAtom_inner_polyatomicHankel (a : ℝ) (m n : ℕ) :
    inner ℂ (gammaLaplaceAtom ⟨Real.exp a, Real.exp_pos a⟩ m)
      (gammaLaplaceAtom ⟨Real.exp a, Real.exp_pos a⟩ n) =
        polyatomicHankelMoment a (m + n) := by
  rw [gammaLaplaceAtom_eq_collisionLaplaceAtom, gammaLaplaceAtom_eq_collisionLaplaceAtom,
    collisionLaplaceAtom_inner]
  simp only [collisionFractionalKernel, polyatomicHankelMoment, Real.exp_zero,
    Real.sq_sqrt (show 0 ≤ (m : ℝ) + 1 / 2 by positivity),
    Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 / 2 by positivity), Nat.cast_add]
  congr 3
  ring

/-- Every leading Hankel minor is nonzero; no finite rank ceiling survives. -/
theorem polyatomicHankel_det_ne_zero (a : ℝ) (N : ℕ) :
    Matrix.det (fun i j : Fin N => polyatomicHankelMoment a (i.val + j.val)) ≠ 0 := by
  convert gammaLaplaceAtom_gram_det_ne_zero a N using 1
  congr 1
  ext i j
  exact (gammaLaplaceAtom_inner_polyatomicHankel a i j).symm

/-- Any proposed finite separable tensor fails on a concrete pair of natural samples. -/
theorem polyatomicHankel_no_finite_separation (a : ℝ) (d : ℕ)
    (F G : Fin d → ℕ → ℂ) :
    ∃ m n : ℕ, polyatomicHankelMoment a (m + n) ≠ ∑ j : Fin d, F j m * G j n := by
  classical
  by_contra h
  push Not at h
  let U : Matrix (Fin (d + 1)) (Fin d) ℂ := fun i j => F j i.val
  let V : Matrix (Fin d) (Fin (d + 1)) ℂ := fun j i => G j i.val
  have hm : (fun i j : Fin (d + 1) => polyatomicHankelMoment a (i.val + j.val)) = U * V := by
    ext i j
    exact h i.val j.val
  have hd := polyatomicHankel_det_ne_zero a (d + 1)
  rw [hm, det_rectangular_factor_succ_eq_zero] at hd
  exact hd rfl

/-- The existing rational-Witt column-generation property fails at every order. -/
theorem polyatomicHankel_not_columnGenerated (a : ℝ) (d : ℕ) :
    ¬ DeningerHankelColumnGenerated (polyatomicHankelMoment a) d := by
  intro h
  have hd := hankelRankLT_succ_of_columnGenerated (polyatomicHankelMoment a) d h
    (fun i => i.val) (fun i => i.val)
  exact polyatomicHankel_det_ne_zero a (d + 1) hd

/-- No exact eventual linear recurrence of the corpus's rational-series form exists. -/
theorem polyatomicHankel_no_linearRecurrence (a : ℝ) (q : ℕ → ℂ) (d : ℕ) :
    ¬ DeningerLinearRecurrenceFrom (polyatomicHankelMoment a) q d := by
  intro h
  exact polyatomicHankel_not_columnGenerated a d
    (columnGenerated_of_linearRecurrenceFrom _ _ _ h)

/-- The actual formal generating series of collision Laplace samples. -/
def polyatomicHankelSeries (a : ℝ) : PowerSeries ℂ :=
  PowerSeries.mk (polyatomicHankelMoment a)

/-- No normalized rational fraction gives this formal series, at any shape. -/
theorem polyatomicHankelSeries_not_rational (a : ℝ) :
    ¬ ∃ P Q : Polynomial ℂ, Q.coeff 0 = 1 ∧
      polyatomicHankelSeries a * (Q : PowerSeries ℂ) = (P : PowerSeries ℂ) := by
  rintro ⟨P, Q, hQ, hPQ⟩
  have hrec := linearRecurrenceFrom_of_powerSeries_mul_polynomial
    (polyatomicHankelSeries a) P Q hQ hPQ
  simp only [polyatomicHankelSeries, PowerSeries.coeff_mk] at hrec
  exact polyatomicHankel_no_linearRecurrence a Q.coeff _ hrec

end
end RHTower
