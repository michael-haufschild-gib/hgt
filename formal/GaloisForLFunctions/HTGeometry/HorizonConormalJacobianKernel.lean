import GaloisForLFunctions.HTGeometry.LowTangentJacobianKernel

/-!
# The conormal vector lies in the kernel of the observation Jacobian

The conormal functional of a low tangent pair `(U, V)` is, in the observation coordinate basis, the
vector whose reciprocal-block entries are the reversed coefficients of `U` and whose raw-block
entries are the negated reversed coefficients of `V`.  The observation Jacobian is the transpose of
the differential of the horizon map, so:

```text
sum_fin_toeplitz_eq_coeff_mul          a truncated Toeplitz row is a coefficient of a product
sum_toeplitz_rev_eq_neg_coeff          the same, against reversed coefficients
horizonConormalVector, horizonObservationJacobian
horizonObservationJacobian_mulVec_conormal
    ** the conormal vector of a low tangent is a kernel vector of the observation Jacobian **
```

The proof is the identity `V ≡ -Y² U` below the horizon: on the reciprocal block the Toeplitz row
computes `-(Y²U)` at an index at least `n`, where `V` vanishes, and on the raw block it computes
`-(Y²U) = V` at the matching index, cancelling the diagonal entry.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

set_option maxHeartbeats 2000000

variable {F : Type*} [CommRing F]

/-- A truncated Toeplitz row against the coefficients of a low polynomial is a coefficient of the
product. -/
theorem sum_fin_toeplitz_eq_coeff_mul {m : ℕ} (h U : F[X])
    (hU : U.degree < (m : ℕ)) (k : ℕ) :
    ∑ c : Fin m, (if (c : ℕ) ≤ k then h.coeff (k - (c : ℕ)) else 0) * U.coeff (c : ℕ)
      = (h * U).coeff k := by
  classical
  have hzero : ∀ c : ℕ, m ≤ c → U.coeff c = 0 := by
    intro c hc
    exact Polynomial.coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le hU (by exact_mod_cast hc))
  have hL : ∑ c : Fin m, (if (c : ℕ) ≤ k then h.coeff (k - (c : ℕ)) else 0) * U.coeff (c : ℕ)
      = ∑ c ∈ Finset.range m, (if c ≤ k then h.coeff (k - c) else 0) * U.coeff c :=
    Fin.sum_univ_eq_sum_range
      (fun c => (if c ≤ k then h.coeff (k - c) else 0) * U.coeff c) m
  have hR : (h * U).coeff k = ∑ c ∈ Finset.range (k + 1), h.coeff (k - c) * U.coeff c := by
    rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => h.coeff i * U.coeff j)]
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [Finset.mem_range] at hc
    congr 2
    omega
  rw [hL, hR]
  have hLN : ∑ c ∈ Finset.range m, (if c ≤ k then h.coeff (k - c) else 0) * U.coeff c
      = ∑ c ∈ Finset.range (max m (k + 1)),
          (if c ≤ k then h.coeff (k - c) else 0) * U.coeff c := by
    refine Finset.sum_subset (fun x hx => Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_max_left _ _))) ?_
    intro c _ hc
    rw [Finset.mem_range] at hc
    rw [hzero c (by omega), mul_zero]
  have hRN : ∑ c ∈ Finset.range (k + 1), h.coeff (k - c) * U.coeff c
      = ∑ c ∈ Finset.range (max m (k + 1)),
          (if c ≤ k then h.coeff (k - c) else 0) * U.coeff c := by
    have h1 : ∑ c ∈ Finset.range (k + 1), (if c ≤ k then h.coeff (k - c) else 0) * U.coeff c
        = ∑ c ∈ Finset.range (max m (k + 1)),
            (if c ≤ k then h.coeff (k - c) else 0) * U.coeff c := by
      refine Finset.sum_subset (fun x hx => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_max_right _ _))) ?_
      intro c _ hc
      rw [Finset.mem_range] at hc
      rw [if_neg (by omega), zero_mul]
    rw [← h1]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [Finset.mem_range] at hc
    rw [if_pos (by omega)]
  rw [hLN, hRN]

/-- The conormal coefficient vector of a low tangent pair, in block order. -/
noncomputable def horizonConormalVector (U V : F[X]) (m n : ℕ) : Fin m ⊕ Fin n → F
  | Sum.inl s => U.coeff (m - 1 - (s : ℕ))
  | Sum.inr s => -V.coeff (n - 1 - (s : ℕ))

open Matrix in
/-- The observation Jacobian in block order, for a general reciprocal jet. -/
noncomputable def horizonObservationJacobian (Y : F[X]) (n m : ℕ) :
    Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) F :=
  Matrix.of fun t s =>
    match s with
    | Sum.inl s' =>
        if ((finSumFinEquiv t : Fin (m + n)) : ℕ) ≤ n + (s' : ℕ) then
          -((Y * Y).coeff (n + (s' : ℕ) - ((finSumFinEquiv t : Fin (m + n)) : ℕ)))
        else 0
    | Sum.inr s' => if t = Sum.inr s' then 1 else 0

/-- The Toeplitz row of the observation Jacobian, summed against the reversed coefficients of a
low polynomial, is a coefficient of the product. -/
theorem sum_toeplitz_rev_eq_neg_coeff {m n : ℕ} (Y U : F[X]) (hU : U.degree < (m : ℕ))
    (τ : ℕ) (hτ : τ < m + n) :
    ∑ s' : Fin m, (if τ ≤ n + (s' : ℕ) then -((Y * Y).coeff (n + (s' : ℕ) - τ)) else 0) *
        U.coeff (m - 1 - (s' : ℕ))
      = -((Y * Y * U).coeff (n + m - 1 - τ)) := by
  classical
  rw [← Fintype.sum_equiv (Fin.revPerm (n := m))
    (fun c : Fin m => (if τ ≤ n + ((Fin.rev c : Fin m) : ℕ) then
        -((Y * Y).coeff (n + ((Fin.rev c : Fin m) : ℕ) - τ)) else 0) *
      U.coeff (m - 1 - ((Fin.rev c : Fin m) : ℕ)))
    (fun s' : Fin m => (if τ ≤ n + (s' : ℕ) then -((Y * Y).coeff (n + (s' : ℕ) - τ)) else 0) *
      U.coeff (m - 1 - (s' : ℕ))) (fun c => rfl)]
  have hstep : ∀ c : Fin m,
      (if τ ≤ n + ((Fin.rev c : Fin m) : ℕ) then
          -((Y * Y).coeff (n + ((Fin.rev c : Fin m) : ℕ) - τ)) else 0) *
        U.coeff (m - 1 - ((Fin.rev c : Fin m) : ℕ))
        = -((if (c : ℕ) ≤ n + m - 1 - τ then (Y * Y).coeff (n + m - 1 - τ - (c : ℕ)) else 0) *
          U.coeff (c : ℕ)) := by
    intro c
    have hcv : ((Fin.rev c : Fin m) : ℕ) = m - 1 - (c : ℕ) := by
      rw [Fin.val_rev]
      omega
    have hclt : (c : ℕ) < m := c.isLt
    rw [hcv, show m - 1 - (m - 1 - (c : ℕ)) = (c : ℕ) by omega]
    by_cases hcase : τ ≤ n + (m - 1 - (c : ℕ))
    · rw [if_pos hcase, if_pos (by omega), show n + (m - 1 - (c : ℕ)) - τ
        = n + m - 1 - τ - (c : ℕ) by omega]
      ring
    · rw [if_neg hcase, if_neg (by omega), zero_mul, neg_zero]
  rw [Finset.sum_congr rfl (fun c _ => hstep c), Finset.sum_neg_distrib,
    sum_fin_toeplitz_eq_coeff_mul (Y * Y) U hU (n + m - 1 - τ)]

section FieldCase

variable {E : Type*} [Field E]

/-- **The conormal vector of a low tangent is in the kernel of the observation Jacobian.** -/
theorem horizonObservationJacobian_mulVec_conormal {m n : ℕ} {A Y U V : E[X]}
    (hInv : (X : E[X]) ^ (m + n) ∣ A * Y - 1)
    (hU : U.degree < (m : ℕ)) (hV : V.degree < (n : ℕ))
    (htan : (X : E[X]) ^ (m + n) ∣ U * Y + A * V) :
    (horizonObservationJacobian Y n m).mulVec (horizonConormalVector U V m n) = 0 := by
  classical
  obtain ⟨w, hw⟩ := dvd_reciprocal_of_low_tangent hInv htan
  have hcoeff : ∀ k : ℕ, k < m + n → (Y * Y * U).coeff k = -V.coeff k := by
    intro k hk
    have h0 : (V + Y * Y * U).coeff k = 0 := by
      rw [hw, Polynomial.coeff_X_pow_mul']
      simp only [ite_eq_right_iff]
      intro hle
      omega
    rw [Polynomial.coeff_add] at h0
    linear_combination h0
  funext t
  show (∑ s : Fin m ⊕ Fin n, horizonObservationJacobian Y n m t s *
    horizonConormalVector U V m n s) = 0
  rw [Fintype.sum_sum_type]
  cases t with
  | inl a =>
    have hsecond : ∑ s'' : Fin n,
        horizonObservationJacobian Y n m (Sum.inl a) (Sum.inr s'') *
          horizonConormalVector U V m n (Sum.inr s'') = 0 := by
      refine Finset.sum_eq_zero fun s'' _ => ?_
      show (if (Sum.inl a : Fin m ⊕ Fin n) = Sum.inr s'' then (1 : E) else 0) * _ = 0
      rw [if_neg (by simp), zero_mul]
    rw [hsecond, add_zero]
    have hfirst : ∑ s' : Fin m,
        horizonObservationJacobian Y n m (Sum.inl a) (Sum.inl s') *
          horizonConormalVector U V m n (Sum.inl s')
        = -((Y * Y * U).coeff (n + m - 1 - (a : ℕ))) := by
      rw [← sum_toeplitz_rev_eq_neg_coeff Y U hU (a : ℕ) (by have := a.isLt; omega)]
      refine Finset.sum_congr rfl fun s' _ => ?_
      rfl
    rw [hfirst, hcoeff _ (by have := a.isLt; omega)]
    have hVzero : V.coeff (n + m - 1 - (a : ℕ)) = 0 := by
      refine Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hV ?_)
      have ha := a.isLt
      exact_mod_cast (by omega : n ≤ n + m - 1 - (a : ℕ))
    rw [hVzero]
    simp
  | inr b =>
    have hsecond : ∑ s'' : Fin n,
        horizonObservationJacobian Y n m (Sum.inr b) (Sum.inr s'') *
          horizonConormalVector U V m n (Sum.inr s'')
        = -V.coeff (n - 1 - (b : ℕ)) := by
      rw [Finset.sum_eq_single b]
      · show (if (Sum.inr b : Fin m ⊕ Fin n) = Sum.inr b then (1 : E) else 0) * _ = _
        rw [if_pos rfl, one_mul]
        rfl
      · intro s'' _ hne
        show (if (Sum.inr b : Fin m ⊕ Fin n) = Sum.inr s'' then (1 : E) else 0) * _ = 0
        rw [if_neg (by simp [Ne.symm hne]), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ b) h
    have hfirst : ∑ s' : Fin m,
        horizonObservationJacobian Y n m (Sum.inr b) (Sum.inl s') *
          horizonConormalVector U V m n (Sum.inl s')
        = -((Y * Y * U).coeff (n + m - 1 - (m + (b : ℕ)))) := by
      rw [← sum_toeplitz_rev_eq_neg_coeff Y U hU (m + (b : ℕ)) (by have := b.isLt; omega)]
      refine Finset.sum_congr rfl fun s' _ => ?_
      rfl
    rw [hfirst, hsecond, hcoeff _ (by have := b.isLt; omega)]
    have hidx : n + m - 1 - (m + (b : ℕ)) = n - 1 - (b : ℕ) := by
      have := b.isLt
      omega
    rw [hidx]
    ring

end FieldCase

end GaloisForLFunctions.HTGeometry
