import GaloisForLFunctions.HTGeometry.OneDepthHankelBound
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# The Hankel hypersurface of a base jet, at any depth

At depth `m` the unknown jet is `a₀ + a₁ t + ... + a_{m-1} t^{m-1}` above the observed packet, so the
product of a fixed fibre point's jet with it is affine-linear in the `m` unknown coefficients.  The
Padé–Hankel matrix is linear in the jet, so its entries are affine-linear forms in those
coefficients and its determinant is a hypersurface of degree the second depth.

Every point of the fibre other than the base one lies on that hypersurface, by the product
obstruction.  At `m = 2` this is the plane curve of the depth-two count; for larger `m` it is the
object any dimension or degree argument has to consume.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-! ## Linearity of the Hankel matrix in the jet -/

section Linear

variable {R : Type*} [CommRing R] {m n : ℕ}

theorem padeHankel_add (S T : R[X]) (m n : ℕ) :
    padeHankel (S + T) m n = padeHankel S m n + padeHankel T m n := by
  ext r j
  simp only [padeHankel, Matrix.of_apply, Matrix.add_apply, mul_add, Polynomial.coeff_add]

theorem padeHankel_C_mul (a : R) (S : R[X]) (m n : ℕ) :
    padeHankel (C a * S) m n = a • padeHankel S m n := by
  ext r j
  simp only [padeHankel, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [show (X : R[X]) ^ (j : ℕ) * (C a * S) = C a * ((X : R[X]) ^ (j : ℕ) * S) by ring,
    Polynomial.coeff_C_mul]

theorem padeHankel_zero (m n : ℕ) : padeHankel (0 : R[X]) m n = 0 := by
  ext r j
  simp [padeHankel]

theorem padeHankel_finsetSum {ι : Type*} (s : Finset ι) (f : ι → R[X]) (m n : ℕ) :
    padeHankel (∑ i ∈ s, f i) m n = ∑ i ∈ s, padeHankel (f i) m n := by
  classical
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, padeHankel_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, padeHankel_add, ih]

/-- **The Hankel matrix of a jet with unknown low coefficients.** -/
theorem padeHankel_mul_jet (P₀ U : R[X]) (x : Fin m → R) :
    padeHankel (P₀ * ((∑ i : Fin m, C (x i) * X ^ (i : ℕ)) + U)) m n
      = padeHankel (P₀ * U) m n
        + ∑ i : Fin m, x i • padeHankel ((X : R[X]) ^ (i : ℕ) * P₀) m n := by
  have hexp : P₀ * ((∑ i : Fin m, C (x i) * X ^ (i : ℕ)) + U)
      = P₀ * U + ∑ i : Fin m, C (x i) * ((X : R[X]) ^ (i : ℕ) * P₀) := by
    rw [mul_add, Finset.mul_sum,
      add_comm (∑ i : Fin m, P₀ * (C (x i) * X ^ (i : ℕ))) (P₀ * U)]
    refine congrArg (fun z => P₀ * U + z) ?_
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hexp, padeHankel_add, padeHankel_finsetSum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => padeHankel_C_mul _ _ _ _

end Linear

/-! ## The universal affine matrix over the jet coordinates -/

section Universal

variable {K : Type*} [CommRing K] [Nontrivial K] {m N : ℕ}

/-- **A matrix of affine-linear forms in `m` variables.** -/
noncomputable def affineMvMatrix (H₀ : Matrix (Fin N) (Fin N) K)
    (H : Fin m → Matrix (Fin N) (Fin N) K) : Matrix (Fin N) (Fin N) (MvPolynomial (Fin m) K) :=
  Matrix.of fun r j =>
    MvPolynomial.C (H₀ r j) + ∑ i : Fin m, MvPolynomial.C (H i r j) * MvPolynomial.X i

theorem totalDegree_affineMvMatrix_le (H₀ : Matrix (Fin N) (Fin N) K)
    (H : Fin m → Matrix (Fin N) (Fin N) K) (r j : Fin N) :
    (affineMvMatrix H₀ H r j).totalDegree ≤ 1 := by
  rw [affineMvMatrix, Matrix.of_apply]
  refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
  · rw [MvPolynomial.totalDegree_C]
    exact Nat.zero_le 1
  · refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) (Finset.sup_le fun i _ => ?_)
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    rw [MvPolynomial.totalDegree_C, zero_add, MvPolynomial.totalDegree_X]

/-- **The determinant of a matrix of affine-linear forms is a hypersurface of the matrix size.** -/
theorem totalDegree_det_affineMvMatrix_le (H₀ : Matrix (Fin N) (Fin N) K)
    (H : Fin m → Matrix (Fin N) (Fin N) K) :
    ((affineMvMatrix H₀ H).det).totalDegree ≤ N := by
  classical
  rw [Matrix.det_apply']
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) (Finset.sup_le fun σ _ => ?_)
  have hprod : (∏ i : Fin N, affineMvMatrix H₀ H (σ i) i).totalDegree ≤ N := by
    refine le_trans (MvPolynomial.totalDegree_finsetProd _ _) ?_
    calc ∑ i : Fin N, (affineMvMatrix H₀ H (σ i) i).totalDegree
        ≤ ∑ _i : Fin N, 1 :=
          Finset.sum_le_sum fun i _ => totalDegree_affineMvMatrix_le H₀ H _ _
      _ = N := by simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ
  · rw [hσ]
    simpa using hprod
  · rw [hσ]
    have hne : ((((-1 : ℤˣ) : ℤ) : MvPolynomial (Fin m) K))
        * (∏ i : Fin N, affineMvMatrix H₀ H (σ i) i)
        = -(∏ i : Fin N, affineMvMatrix H₀ H (σ i) i) := by
      push_cast
      ring
    rw [hne, MvPolynomial.totalDegree_neg]
    exact hprod

omit [Nontrivial K] in
theorem eval_affineMvMatrix (H₀ : Matrix (Fin N) (Fin N) K)
    (H : Fin m → Matrix (Fin N) (Fin N) K) (x : Fin m → K) (r j : Fin N) :
    MvPolynomial.eval x (affineMvMatrix H₀ H r j)
      = H₀ r j + ∑ i : Fin m, H i r j * x i := by
  rw [affineMvMatrix, Matrix.of_apply, map_add, MvPolynomial.eval_C, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]

end Universal

/-! ## The Hankel hypersurface -/

section Hypersurface

variable {K : Type*} [Field K] {m n : ℕ}

/-- **The universal Padé–Hankel matrix of a base jet at depth `m`.** -/
noncomputable def hankelMvMatrix (P₀ U : K[X]) (m n : ℕ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) K) :=
  affineMvMatrix (padeHankel (P₀ * U) m n) (fun i => padeHankel ((X : K[X]) ^ (i : ℕ) * P₀) m n)

/-- **The Hankel hypersurface of a base jet has degree the second depth.** -/
theorem totalDegree_det_hankelMvMatrix_le (P₀ U : K[X]) :
    ((hankelMvMatrix P₀ U m n).det).totalDegree ≤ n :=
  totalDegree_det_affineMvMatrix_le _ _

/-- **Specialising the Hankel hypersurface at a jet.** -/
theorem eval_det_hankelMvMatrix (P₀ U : K[X]) (x : Fin m → K) :
    MvPolynomial.eval x (hankelMvMatrix P₀ U m n).det
      = (padeHankel (P₀ * ((∑ i : Fin m, C (x i) * X ^ (i : ℕ)) + U)) m n).det := by
  have hmat : (hankelMvMatrix P₀ U m n).map (MvPolynomial.eval x)
      = padeHankel (P₀ * ((∑ i : Fin m, C (x i) * X ^ (i : ℕ)) + U)) m n := by
    ext r j
    rw [Matrix.map_apply, hankelMvMatrix, eval_affineMvMatrix, padeHankel_mul_jet,
      Matrix.add_apply, Matrix.sum_apply]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by
      rw [Matrix.smul_apply, smul_eq_mul, mul_comm]
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hmat]

/-- **Every fibre point other than the base one lies on the base point's Hankel
hypersurface.** -/
theorem eval_det_hankelMvMatrix_eq_zero {U V : K[X]} (hm : 0 < m) (hn : 0 < n)
    (hU : (X : K[X]) ^ m ∣ U) (hV : (X : K[X]) ^ n ∣ V)
    (hU0 : U.coeff 0 = 0) (hV0 : V.coeff 0 = 0)
    (p q : criticalFibre K m n U V) (hpq : p ≠ q) :
    MvPolynomial.eval (fun i : Fin m => q.1.1.coeff (i : ℕ))
        (hankelMvMatrix (p.1.1 + U) U m n).det = 0 := by
  have hjet : (∑ i : Fin m, C (q.1.1.coeff (i : ℕ)) * X ^ (i : ℕ)) = q.1.1 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => C (q.1.1.coeff i) * X ^ i) m]
    exact sum_range_C_coeff_mul_X_pow q.2.1
  rw [eval_det_hankelMvMatrix, hjet]
  exact det_padeHankel_product_eq_zero hm hn hU hV hU0 hV0 p q hpq

end Hypersurface

end GaloisForLFunctions.HTGeometry
