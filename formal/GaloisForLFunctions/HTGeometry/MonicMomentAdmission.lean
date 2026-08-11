import GaloisForLFunctions.HTGeometry.FiniteHankelBoundaryQuadrature
import Mathlib.Topology.Instances.Matrix

/-!
# Canonical monic admission from a finite moment Hankel solve

A finite moment sequence need not lie on a singular Hankel face.  Nevertheless, whenever its
leading `n` by `n` Hankel block is invertible, there is a unique monic degree-`n` polynomial
orthogonal to `1, X, ..., X^(n-1)`.  It is obtained by solving the leading Hankel system.  At a
flat next face the same coefficient vector is the terminal-normalized Hankel null flag.

This is the admission object needed by source-first constructions: it exists in the open positive
chamber and specializes to the boundary null polynomial, so no post-aggregation reporter is used.
-/

open Filter Matrix Polynomial Topology
open scoped BigOperators

namespace HTGeometry

noncomputable section

/-- Right-hand side of the monic degree-`n` moment orthogonality system. -/
def momentHankelTail (s : ℕ → ℝ) (n : ℕ) : Fin n → ℝ :=
  fun i => s ((i : ℕ) + n)

/-- Lower coefficients of the canonical monic degree-`n` admission. -/
def monicMomentAdmissionCoefficients (s : ℕ → ℝ) (n : ℕ) : Fin n → ℝ :=
  -((momentHankelMatrix s n)⁻¹ *ᵥ momentHankelTail s n)

/-- Terminal-normalized coefficient vector, including the monic top coefficient. -/
def monicMomentAdmissionVector (s : ℕ → ℝ) (n : ℕ) : Fin (n + 1) → ℝ :=
  Fin.snoc (monicMomentAdmissionCoefficients s n) 1

/-- Canonical monic moment admission polynomial. -/
def monicMomentAdmissionPolynomial (s : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  finiteHankelNullPolynomial (monicMomentAdmissionVector s n)

@[simp] theorem monicMomentAdmissionVector_castSucc
    (s : ℕ → ℝ) (n : ℕ) (i : Fin n) :
    monicMomentAdmissionVector s n i.castSucc = monicMomentAdmissionCoefficients s n i := by
  simp [monicMomentAdmissionVector]

@[simp] theorem monicMomentAdmissionVector_last (s : ℕ → ℝ) (n : ℕ) :
    monicMomentAdmissionVector s n (Fin.last n) = 1 := by
  simp [monicMomentAdmissionVector]

theorem monicMomentAdmissionPolynomial_eq
    (s : ℕ → ℝ) (n : ℕ) :
    monicMomentAdmissionPolynomial s n =
      X ^ n + Polynomial.ofFn n (monicMomentAdmissionCoefficients s n) := by
  rw [monicMomentAdmissionPolynomial, finiteHankelNullPolynomial,
    monicMomentAdmissionVector, Polynomial.ofFn_eq_sum_monomial,
    Fin.sum_univ_castSucc, Fin.snoc_last, Polynomial.ofFn_eq_sum_monomial]
  simp only [Fin.snoc_castSucc, Fin.val_castSucc, Fin.val_last,
    Polynomial.monomial_one_right_eq_X_pow]
  ac_rfl

theorem monicMomentAdmissionPolynomial_monic (s : ℕ → ℝ) (n : ℕ) :
    (monicMomentAdmissionPolynomial s n).Monic := by
  rw [monicMomentAdmissionPolynomial_eq]
  exact Polynomial.monic_X_pow_add
    (Polynomial.ofFn_degree_lt (monicMomentAdmissionCoefficients s n))

theorem monicMomentAdmissionPolynomial_natDegree (s : ℕ → ℝ) (n : ℕ) :
    (monicMomentAdmissionPolynomial s n).natDegree = n := by
  exact finiteHankelNullPolynomial_natDegree (monicMomentAdmissionVector s n) (by simp)

/-- Invertibility makes the lower coefficients solve the monic Hankel system exactly. -/
theorem momentHankelMatrix_mulVec_monicMomentAdmissionCoefficients
    {s : ℕ → ℝ} {n : ℕ} (hdet : (momentHankelMatrix s n).det ≠ 0) :
    momentHankelMatrix s n *ᵥ monicMomentAdmissionCoefficients s n =
      -momentHankelTail s n := by
  rw [monicMomentAdmissionCoefficients]
  rw [Matrix.mulVec_neg]
  change -(momentHankelMatrix s n *ᵥ
    ((momentHankelMatrix s n)⁻¹ *ᵥ momentHankelTail s n)) = _
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]

/-- Multiplication by a monomial shifts every moment coordinate of an `ofFn` polynomial. -/
theorem momentFunctional_X_pow_mul_ofFn
    (s : ℕ → ℝ) (r n : ℕ) (c : Fin n → ℝ) :
    momentFunctional s (X ^ r * Polynomial.ofFn n c) =
      ∑ j : Fin n, c j * s (r + (j : ℕ)) := by
  rw [Polynomial.ofFn_eq_sum_monomial, Finset.mul_sum, momentFunctional_finset_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Polynomial.monomial_one_right_eq_X_pow,
    Polynomial.monomial_mul_monomial, momentFunctional_monomial]
  ring

/-- The solved polynomial is orthogonal to every lower monomial. -/
theorem momentFunctional_X_pow_mul_monicMomentAdmissionPolynomial_eq_zero
    {s : ℕ → ℝ} {n : ℕ} (hdet : (momentHankelMatrix s n).det ≠ 0)
    (i : Fin n) :
    momentFunctional s (X ^ (i : ℕ) * monicMomentAdmissionPolynomial s n) = 0 := by
  rw [monicMomentAdmissionPolynomial,
    momentFunctional_X_pow_mul_finiteHankelNullPolynomial,
    Fin.sum_univ_castSucc]
  have hsolve := congrFun
    (momentHankelMatrix_mulVec_monicMomentAdmissionCoefficients hdet) i
  simp only [Matrix.mulVec, dotProduct, momentHankelMatrix, momentHankelTail,
    Pi.neg_apply] at hsolve
  simp only [monicMomentAdmissionVector_castSucc,
    monicMomentAdmissionVector_last, Fin.val_castSucc, Fin.val_last, one_mul]
  rw [show (i : ℕ) + n = n + (i : ℕ) by omega]
  rw [show (∑ x : Fin n,
      monicMomentAdmissionCoefficients s n x * s ((i : ℕ) + (x : ℕ))) =
      ∑ x : Fin n,
        s ((i : ℕ) + (x : ℕ)) * monicMomentAdmissionCoefficients s n x by
        apply Finset.sum_congr rfl
        intro j _
        ring]
  rw [Nat.add_comm n (i : ℕ)]
  calc
    (∑ x : Fin n,
        s ((i : ℕ) + (x : ℕ)) * monicMomentAdmissionCoefficients s n x) +
          s ((i : ℕ) + n) =
        -s ((i : ℕ) + n) + s ((i : ℕ) + n) := by rw [hsolve]
    _ = 0 := by ring

/-- A monic degree-`n` polynomial is its top monomial plus its first `n` coefficients. -/
theorem eq_X_pow_add_ofFn_toFn_of_monic
    {p : Polynomial ℝ} {n : ℕ} (hp : p.Monic) (hdegree : p.natDegree = n) :
    p = X ^ n + Polynomial.ofFn n (Polynomial.toFn n p) := by
  ext k
  by_cases hk : k < n
  · simp [hk, ne_of_lt hk, Polynomial.coeff_X_pow, Polynomial.toFn]
  · by_cases hkn : k = n
    · subst k
      rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_pos rfl,
        Polynomial.ofFn_coeff_eq_zero_of_ge _ le_rfl, add_zero,
        ← hdegree, hp.coeff_natDegree]
    · have hnk : n < k := lt_of_le_of_ne (Nat.le_of_not_gt hk) (Ne.symm hkn)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hdegree.symm ▸ hnk),
        Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg hkn,
        Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_lt hnk), zero_add]

/-- The Hankel solve is the unique monic polynomial satisfying the lower moment equations. -/
theorem eq_monicMomentAdmissionPolynomial_of_monic_of_orthogonal
    {s : ℕ → ℝ} {n : ℕ} (hdet : (momentHankelMatrix s n).det ≠ 0)
    {p : Polynomial ℝ} (hp : p.Monic) (hdegree : p.natDegree = n)
    (horth : ∀ i : Fin n, momentFunctional s (X ^ (i : ℕ) * p) = 0) :
    p = monicMomentAdmissionPolynomial s n := by
  let a : Fin n → ℝ := Polynomial.toFn n p
  have hpform : p = X ^ n + Polynomial.ofFn n a :=
    eq_X_pow_add_ofFn_toFn_of_monic hp hdegree
  have hsystem : momentHankelMatrix s n *ᵥ a = -momentHankelTail s n := by
    funext i
    have hi := horth i
    rw [hpform, mul_add, momentFunctional_add,
      ← pow_add, momentFunctional_X_pow, momentFunctional_X_pow_mul_ofFn] at hi
    simp only [Matrix.mulVec, dotProduct, momentHankelMatrix, momentHankelTail,
      Pi.neg_apply]
    rw [show (∑ j : Fin n, s ((i : ℕ) + (j : ℕ)) * a j) =
        ∑ j : Fin n, a j * s ((i : ℕ) + (j : ℕ)) by
      apply Finset.sum_congr rfl
      intro j _
      ring]
    linarith
  have hinj : Function.Injective (momentHankelMatrix s n).mulVec := by
    intro u v huv
    have hstep : (momentHankelMatrix s n)⁻¹ *ᵥ
        (momentHankelMatrix s n *ᵥ u) =
        (momentHankelMatrix s n)⁻¹ *ᵥ
          (momentHankelMatrix s n *ᵥ v) := by rw [huv]
    simpa only [Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec] using hstep
  have ha : a = monicMomentAdmissionCoefficients s n := by
    apply hinj
    rw [hsystem, momentHankelMatrix_mulVec_monicMomentAdmissionCoefficients hdet]
  rw [hpform, monicMomentAdmissionPolynomial_eq, ha]

/-- A terminal-normalized flat-face kernel is exactly the canonical admission vector. -/
theorem eq_monicMomentAdmissionVector_of_kernel_of_last_eq_one
    {s : ℕ → ℝ} {n : ℕ} (hdet : (momentHankelMatrix s n).det ≠ 0)
    {c : Fin (n + 1) → ℝ}
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) = 1) :
    c = monicMomentAdmissionVector s n := by
  have hlower :
      momentHankelMatrix s n *ᵥ (fun j : Fin n => c j.castSucc) =
        -momentHankelTail s n := by
    funext i
    have hrow := congrFun hc i.castSucc
    simp only [Matrix.mulVec, dotProduct, momentHankelMatrix, Pi.zero_apply] at hrow
    rw [Fin.sum_univ_castSucc] at hrow
    simp only [Fin.val_castSucc, Fin.val_last, hlast, mul_one] at hrow
    simp only [Matrix.mulVec, dotProduct, momentHankelMatrix, momentHankelTail,
      Pi.neg_apply]
    linarith
  have hinj : Function.Injective (momentHankelMatrix s n).mulVec := by
    intro a b hab
    have hstep : (momentHankelMatrix s n)⁻¹ *ᵥ
        (momentHankelMatrix s n *ᵥ a) =
        (momentHankelMatrix s n)⁻¹ *ᵥ
          (momentHankelMatrix s n *ᵥ b) := by rw [hab]
    simpa only [Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec] using hstep
  have heq : (fun j : Fin n => c j.castSucc) =
      monicMomentAdmissionCoefficients s n := by
    apply hinj
    rw [hlower, momentHankelMatrix_mulVec_monicMomentAdmissionCoefficients hdet]
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [hlast]
  · simpa [monicMomentAdmissionVector] using congrFun heq j

/-- Coefficientwise moment convergence implies convergence of the canonical Hankel solve at every
nonsingular limiting block. -/
theorem tendsto_monicMomentAdmissionCoefficients
    {α : Type*} {l : Filter α} {f : α → ℕ → ℝ} {s : ℕ → ℝ} {n : ℕ}
    (hs : ∀ k, Tendsto (fun x => f x k) l (nhds (s k)))
    (hdet : (momentHankelMatrix s n).det ≠ 0) :
    Tendsto (fun x => monicMomentAdmissionCoefficients (f x) n) l
      (nhds (monicMomentAdmissionCoefficients s n)) := by
  have hH : Tendsto (fun x => momentHankelMatrix (f x) n) l
      (nhds (momentHankelMatrix s n)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    simpa only [momentHankelMatrix] using hs ((i : ℕ) + (j : ℕ))
  have hb : Tendsto (fun x => momentHankelTail (f x) n) l
      (nhds (momentHankelTail s n)) := by
    rw [tendsto_pi_nhds]
    intro i
    simpa [momentHankelTail] using hs ((i : ℕ) + n)
  have hinv : Tendsto (fun x => (momentHankelMatrix (f x) n)⁻¹) l
      (nhds ((momentHankelMatrix s n)⁻¹)) := by
    exact (continuousAt_matrix_inv (momentHankelMatrix s n)
      (by simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet)).tendsto.comp hH
  rw [tendsto_pi_nhds]
  intro i
  simp only [monicMomentAdmissionCoefficients, Pi.neg_apply, Matrix.mulVec, dotProduct]
  apply Filter.Tendsto.neg
  apply tendsto_finsetSum
  intro j _
  exact ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hinv i) j).mul
    (tendsto_pi_nhds.mp hb j))

/-- Every coefficient of the canonical admission polynomial varies continuously under moment
convergence at a nonsingular limiting block. -/
theorem tendsto_monicMomentAdmissionPolynomial_coeff
    {α : Type*} {l : Filter α} {f : α → ℕ → ℝ} {s : ℕ → ℝ} {n : ℕ}
    (hs : ∀ k, Tendsto (fun x => f x k) l (nhds (s k)))
    (hdet : (momentHankelMatrix s n).det ≠ 0) (k : ℕ) :
    Tendsto (fun x => (monicMomentAdmissionPolynomial (f x) n).coeff k) l
      (nhds ((monicMomentAdmissionPolynomial s n).coeff k)) := by
  have hcoeff := tendsto_monicMomentAdmissionCoefficients hs hdet
  by_cases hk : k < n
  · have hk' := (tendsto_pi_nhds.mp hcoeff ⟨k, hk⟩)
    simpa [monicMomentAdmissionPolynomial_eq, hk, ne_of_lt hk,
      Polynomial.coeff_X_pow] using hk'
  · have hle : n ≤ k := Nat.le_of_not_gt hk
    simp [monicMomentAdmissionPolynomial_eq, hle,
      Polynomial.coeff_X_pow, tendsto_const_nhds]

end

end HTGeometry
