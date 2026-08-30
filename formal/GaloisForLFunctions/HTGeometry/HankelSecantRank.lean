import Mathlib

/-!
# Hankel matrices of secant type have bounded rank

A coefficient window that is a sum of `t` geometric sequences gives a Hankel matrix factoring
through a `t`-column Vandermonde matrix, so its rank is at most `t` and its corank at least
`m − t`.  This is the parametrized inclusion of the `t`-secant of the rational normal curve into the
Hankel determinantal locus.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

/-- The Vandermonde-type matrix of a finite family of ratios. -/
def secantVandermonde {K : Type*} [CommRing K] (m t : ℕ) (lam : Fin t → K) :
    Matrix (Fin m) (Fin t) K :=
  Matrix.of fun i k => lam k ^ (i : ℕ)

/-- The Hankel matrix of a sum of geometric sequences. -/
def secantHankel {K : Type*} [CommRing K] (m t : ℕ) (c lam : Fin t → K) :
    Matrix (Fin m) (Fin m) K :=
  Matrix.of fun i j => ∑ k, c k * lam k ^ ((i : ℕ) + (j : ℕ))

theorem secantHankel_eq {K : Type*} [CommRing K] (m t : ℕ) (c lam : Fin t → K) :
    secantHankel m t c lam
      = secantVandermonde m t lam * (Matrix.diagonal c * (secantVandermonde m t lam)ᵀ) := by
  ext i j
  rw [secantHankel]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply, secantVandermonde,
    Matrix.of_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k (fun b _ hb => by rw [if_neg (fun h => hb h.symm)]; ring)
    (fun h => absurd (Finset.mem_univ k) h), if_pos rfl, pow_add]
  ring

/-- **Secant windows have small Hankel rank.** -/
theorem rank_secantHankel_le {K : Type*} [Field K] (m t : ℕ) (c lam : Fin t → K) :
    (secantHankel m t c lam).rank ≤ t := by
  rw [secantHankel_eq]
  refine le_trans (Matrix.rank_mul_le_left _ _) ?_
  refine le_trans (Matrix.rank_le_card_width _) ?_
  simp

/-- **Secant windows have large Hankel corank.** -/
theorem corank_secantHankel_ge {K : Type*} [Field K] (m t : ℕ) (c lam : Fin t → K) :
    m - t ≤ m - (secantHankel m t c lam).rank :=
  Nat.sub_le_sub_left (rank_secantHankel_le m t c lam) m

end GaloisForLFunctions.HTGeometry
