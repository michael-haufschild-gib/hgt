import GaloisForLFunctions.HTGeometry.FibrePairProductObstruction
import GaloisForLFunctions.HTGeometry.RankDropMatrixCriterion

/-!
# The obstruction is a Padé–Hankel determinant

The degeneracy of the convolution pairing at a jet `S` says that `S` is congruent below the horizon
to a ratio of a polynomial of degree below the first depth by one of degree below the second — that
is, that `S` admits a Padé approximant of type `(m-1, n-1)` to order `m + n`.  Since the number of
unknowns equals the number of equations, this is a codimension-one condition, and it is classically
the vanishing of a Hankel determinant in the coefficients of `S`.

Two distinct points of one fibre force exactly this degeneracy at the product of their jets.  So the
products of pairs of distinct fibre points all lie on the Padé–Hankel hypersurface of the
observation.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-! ## The Hankel matrix of a jet -/

section Hankel

variable {R : Type*} [CommRing R] {m n : ℕ}

/-- **The Padé–Hankel matrix of a jet at a pair of depths.**  Its `(r, j)` entry is the coefficient
of the jet at `m + r - j`, read as the coefficient of the `j`-th shift at `m + r`. -/
noncomputable def padeHankel (S : R[X]) (m n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun r j => ((X : R[X]) ^ (j : ℕ) * S).coeff (m + (r : ℕ))

theorem padeHankel_apply (S : R[X]) (r j : Fin n) :
    padeHankel S m n r j = ((X : R[X]) ^ (j : ℕ) * S).coeff (m + (r : ℕ)) := rfl

/-- The Hankel matrix acts on a coefficient vector as the shifted product. -/
theorem mulVec_padeHankel (S : R[X]) (b : ℕ → R) (r : Fin n) :
    (padeHankel S m n).mulVec (fun j : Fin n => b (j : ℕ)) r
      = ((∑ j ∈ Finset.range n, C (b j) * X ^ j) * S).coeff (m + (r : ℕ)) := by
  rw [coeff_sum_range_mul, ← Fin.sum_univ_eq_sum_range
    (fun j => b j * ((X : R[X]) ^ j * S).coeff (m + (r : ℕ))) n]
  have hexp : (padeHankel S m n).mulVec (fun j : Fin n => b (j : ℕ)) r
      = ∑ j : Fin n, padeHankel S m n r j * b (j : ℕ) := rfl
  rw [hexp]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [padeHankel_apply, mul_comm]

end Hankel

/-! ## The determinant vanishes on a degeneracy -/

section Vanishing

variable {K : Type*} [Field K] {m n : ℕ}

/-- **A degeneracy of the convolution pairing makes the Padé–Hankel determinant vanish.**  Above the
first depth the numerator contributes nothing, so the coefficients of the denominator are a nonzero
kernel vector of the Hankel matrix. -/
theorem det_padeHankel_eq_zero {S α β : K[X]} (hβ0 : β ≠ 0)
    (hα : α.degree < (m : ℕ)) (hβ : β.degree < (n : ℕ))
    (hdvd : (X : K[X]) ^ (m + n) ∣ (α - S * β)) :
    (padeHankel S m n).det = 0 := by
  classical
  refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨fun j : Fin n => β.coeff (j : ℕ), ?_, ?_⟩
  · intro h0
    refine hβ0 (Polynomial.ext fun i => ?_)
    rcases lt_or_ge i n with hi | hi
    · have := congrFun h0 (⟨i, hi⟩ : Fin n)
      simpa using this
    · rw [Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le hβ (by exact_mod_cast hi)), Polynomial.coeff_zero]
  · funext r
    rw [mulVec_padeHankel, sum_range_C_coeff_mul_X_pow hβ]
    have hcoeff : (α - S * β).coeff (m + (r : ℕ)) = 0 :=
      (Polynomial.X_pow_dvd_iff.1 hdvd) (m + (r : ℕ)) (by omega)
    have hα0 : α.coeff (m + (r : ℕ)) = 0 :=
      Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le hα (by exact_mod_cast Nat.le_add_right m (r : ℕ)))
    rw [Polynomial.coeff_sub, hα0, zero_sub, neg_eq_zero] at hcoeff
    rw [mul_comm]
    exact hcoeff

/-- **The product of the jets of two distinct fibre points lies on the Padé–Hankel
hypersurface.** -/
theorem det_padeHankel_product_eq_zero (hm : 0 < m) (hn : 0 < n) {U V : K[X]}
    (hU : (X : K[X]) ^ m ∣ U) (hV : (X : K[X]) ^ n ∣ V)
    (hU0 : U.coeff 0 = 0) (hV0 : V.coeff 0 = 0)
    (p q : criticalFibre K m n U V) (hpq : p ≠ q) :
    (padeHankel ((p.1.1 + U) * (q.1.1 + U)) m n).det = 0 := by
  obtain ⟨α, β, hα0, hα, hβ, hdvd⟩ := exists_kernel_of_fibre_ne hm hn hU hV hU0 hV0 p q hpq
  refine det_padeHankel_eq_zero ?_ hα hβ hdvd
  intro hβ0
  rw [hβ0, mul_zero, sub_zero] at hdvd
  refine hα0 (Polynomial.eq_zero_of_dvd_of_degree_lt hdvd ?_)
  rw [Polynomial.degree_X_pow]
  exact lt_of_lt_of_le hα (by exact_mod_cast Nat.le_add_right m n)


/-- **A vanishing Padé–Hankel determinant produces a Padé approximant.**  A kernel vector of the
Hankel matrix is the denominator; the numerator is the truncation of the product below the first
depth, and the remaining coefficients vanish exactly by the kernel relation. -/
theorem exists_pade_of_det_padeHankel_eq_zero {S : K[X]} (h : (padeHankel S m n).det = 0) :
    ∃ α β : K[X], β ≠ 0 ∧ α.degree < (m : ℕ) ∧ β.degree < (n : ℕ) ∧
      (X : K[X]) ^ (m + n) ∣ (α - S * β) := by
  classical
  obtain ⟨w, hw, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  set c : ℕ → K := fun j => if hj : j < n then w ⟨j, hj⟩ else 0 with hc
  set β : K[X] := ∑ j ∈ Finset.range n, C (c j) * X ^ j with hβdef
  have hβcoeff : ∀ i, β.coeff i = if i < n then c i else 0 := fun i =>
    coeff_sum_range_C_mul_X_pow c n i
  have hβ : β.degree < (n : ℕ) := degree_sum_range_C_mul_X_pow_lt c n
  have hβ0 : β ≠ 0 := by
    intro h0
    refine hw (funext fun j => ?_)
    have := hβcoeff (j : ℕ)
    rw [h0, Polynomial.coeff_zero, if_pos j.isLt, hc] at this
    simpa using this.symm
  refine ⟨∑ k ∈ Finset.range m, C ((S * β).coeff k) * X ^ k, β, hβ0,
    degree_sum_range_C_mul_X_pow_lt _ m, hβ, ?_⟩
  refine Polynomial.X_pow_dvd_iff.2 fun k hk => ?_
  rw [Polynomial.coeff_sub, coeff_sum_range_C_mul_X_pow]
  by_cases hkm : k < m
  · rw [if_pos hkm, sub_self]
  · rw [if_neg hkm, zero_sub, neg_eq_zero]
    have hr : k - m < n := by omega
    have hkeq : k = m + (k - m) := by omega
    have hwc : (fun j : Fin n => c (j : ℕ)) = w := by
      funext j
      rw [hc]
      simp
    have hker := congrFun hmul (⟨k - m, hr⟩ : Fin n)
    rw [← hwc, mulVec_padeHankel] at hker
    rw [hkeq, mul_comm]
    simpa using hker


/-- **The Padé criterion.**  A jet admits a Padé approximant of type `(m-1, n-1)` to order `m + n`
exactly when its Padé–Hankel determinant vanishes.  Mathlib has no Padé theory; this is the
classical existence criterion, and the degeneracy locus of the convolution pairing is precisely this
hypersurface. -/
theorem det_padeHankel_eq_zero_iff (S : K[X]) :
    (padeHankel S m n).det = 0 ↔
      ∃ α β : K[X], β ≠ 0 ∧ α.degree < (m : ℕ) ∧ β.degree < (n : ℕ) ∧
        (X : K[X]) ^ (m + n) ∣ (α - S * β) :=
  ⟨exists_pade_of_det_padeHankel_eq_zero,
    fun ⟨_, _, h0, ha, hb, hd⟩ => det_padeHankel_eq_zero h0 ha hb hd⟩

end Vanishing

end GaloisForLFunctions.HTGeometry
