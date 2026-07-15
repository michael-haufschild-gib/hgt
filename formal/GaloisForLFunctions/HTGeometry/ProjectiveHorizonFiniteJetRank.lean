import GaloisForLFunctions.HTGeometry.JacobianAlgebraicIndependence
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonPageTransition

/-!
# Exact algebraic rank of two finite projective jet horizons

This module closes the algebraic-geometric step behind the finite scalar Page transition.  It
constructs the universal reciprocal differential-jet polynomials, proves a nonzero consecutive
Jacobian minor at an exponential base point, and promotes that minor through the characteristic-zero
Jacobian criterion.  For a hypertranscendental source, the resulting mixed raw/reciprocal packet has
exact algebraic-matroid rank

`min (N + 1) ((N + 1 - m) + (N + 1 - n))`.

The final section proves the binomial Leibniz rule for algebraic differential jets and identifies
the universal reciprocal polynomials with the actual jets of `x⁻¹`.  Thus the rank statement applies
to the differential observations in the paper card, not merely to a formal recurrence.
-/

open scoped BigOperators
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable def universalReciprocalJetPolynomial : (n : ℕ) → MvPolynomial ℕ ℚ
  | 0 => X 0
  | n + 1 =>
      -X 0 * ∑ k ∈ Finset.range (n + 1),
        C ((Nat.choose (n + 1) (k + 1) : ℚ)) * X (k + 1) *
          universalReciprocalJetPolynomial (n - k)
termination_by n => n
decreasing_by omega

def reciprocalExponentialBase (k : ℕ) : ℚ :=
  if k = 0 then 1 else (-1 / 2 : ℚ) ^ k

private theorem shifted_binomial_base_sum (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (Nat.choose (n + 1) (k + 1) : ℚ) *
          (-1 / 2 : ℚ) ^ (k + 1) * (1 / 2 : ℚ) ^ (n - k) =
      -(1 / 2 : ℚ) ^ (n + 1) := by
  have h := add_pow (-1 / 2 : ℚ) (1 / 2 : ℚ) (n + 1)
  rw [show (-1 / 2 : ℚ) + 1 / 2 = 0 by norm_num, zero_pow (by omega)] at h
  rw [Finset.sum_range_succ'] at h
  simp only [Nat.choose_zero_right, pow_zero, one_mul, Nat.cast_one] at h
  simp only [Nat.sub_zero] at h
  have htail :
      ∑ x ∈ Finset.range (n + 1),
          (-1 / 2 : ℚ) ^ (x + 1) *
            (1 / 2 : ℚ) ^ (n + 1 - (x + 1)) *
              (Nat.choose (n + 1) (x + 1) : ℚ) =
        -(1 / 2 : ℚ) ^ (n + 1) := by
    rw [pow_succ] at h ⊢
    linarith
  simpa [mul_assoc, mul_left_comm, mul_comm] using htail

private theorem shifted_binomial_raw_sum (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (Nat.choose (n + 1) (k + 1) : ℚ) *
          (-1 / 2 : ℚ) ^ (k + 1) =
      (1 / 2 : ℚ) ^ (n + 1) - 1 := by
  have h := add_pow (-1 / 2 : ℚ) 1 (n + 1)
  rw [show (-1 / 2 : ℚ) + 1 = 1 / 2 by norm_num] at h
  rw [Finset.sum_range_succ'] at h
  simp only [Nat.choose_zero_right, pow_zero, one_mul, Nat.cast_one] at h
  simp only [one_pow, Nat.sub_zero] at h
  norm_num only [mul_one, one_mul] at h
  have htail :
      ∑ x ∈ Finset.range (n + 1),
          (-1 / 2 : ℚ) ^ (x + 1) *
            (Nat.choose (n + 1) (x + 1) : ℚ) =
        (1 / 2 : ℚ) ^ (n + 1) - 1 := by
    linarith
  simpa [mul_comm] using htail

private theorem choose_convolution_factor {N j s : ℕ} (hj : j ≤ N)
    (hs : s ≤ N - j) :
    (Nat.choose N s : ℚ) * (Nat.choose (N - s) j : ℚ) =
      (Nat.choose N j : ℚ) * (Nat.choose (N - j) s : ℚ) := by
  have hjNs : j ≤ N - s := by omega
  have h := Nat.choose_mul (n := N) (k := N - j) (s := s) hs
  rw [Nat.choose_symm hj] at h
  have hidx : N - j - s = (N - s) - j := by omega
  rw [hidx, Nat.choose_symm hjNs] at h
  exact_mod_cast h.symm

private theorem reciprocal_deriv_convolution {N j : ℕ} (hj : j ≤ N) :
    ∑ s ∈ Finset.range (N - j + 1),
        (Nat.choose N s : ℚ) * (-1 / 2 : ℚ) ^ s *
          (Nat.choose (N - s) j : ℚ) =
      (Nat.choose N j : ℚ) * (1 / 2 : ℚ) ^ (N - j) := by
  have hpow := add_pow (-1 / 2 : ℚ) 1 (N - j)
  rw [show (-1 / 2 : ℚ) + 1 = 1 / 2 by norm_num] at hpow
  simp only [one_pow, mul_one] at hpow
  calc
    ∑ s ∈ Finset.range (N - j + 1),
        (Nat.choose N s : ℚ) * (-1 / 2 : ℚ) ^ s *
          (Nat.choose (N - s) j : ℚ) =
      ∑ s ∈ Finset.range (N - j + 1),
        (Nat.choose N j : ℚ) *
          ((-1 / 2 : ℚ) ^ s * (Nat.choose (N - j) s : ℚ)) := by
        apply Finset.sum_congr rfl
        intro s hs
        have hsle : s ≤ N - j := by simp only [Finset.mem_range] at hs; omega
        calc
          (Nat.choose N s : ℚ) * (-1 / 2 : ℚ) ^ s *
              (Nat.choose (N - s) j : ℚ) =
            ((Nat.choose N s : ℚ) * (Nat.choose (N - s) j : ℚ)) *
              (-1 / 2 : ℚ) ^ s := by ring
          _ = ((Nat.choose N j : ℚ) * (Nat.choose (N - j) s : ℚ)) *
              (-1 / 2 : ℚ) ^ s := by rw [choose_convolution_factor hj hsle]
          _ = (Nat.choose N j : ℚ) *
              ((-1 / 2 : ℚ) ^ s * (Nat.choose (N - j) s : ℚ)) := by ring
    _ = (Nat.choose N j : ℚ) *
        ∑ s ∈ Finset.range (N - j + 1),
          ((-1 / 2 : ℚ) ^ s * (Nat.choose (N - j) s : ℚ)) := by
      rw [Finset.mul_sum]
    _ = (Nat.choose N j : ℚ) * (1 / 2 : ℚ) ^ (N - j) := by
      rw [← hpow]

private theorem reciprocal_deriv_convolution_tail {N j : ℕ} (hj : j ≤ N) :
    ∑ x ∈ Finset.range (N - j),
        (Nat.choose N (x + 1) : ℚ) * (-1 / 2 : ℚ) ^ (x + 1) *
          (Nat.choose (N - (x + 1)) j : ℚ) =
      (Nat.choose N j : ℚ) * (1 / 2 : ℚ) ^ (N - j) -
        (Nat.choose N j : ℚ) := by
  have h := reciprocal_deriv_convolution hj
  rw [Finset.sum_range_succ'] at h
  simp only [Nat.choose_zero_right, pow_zero, one_mul, Nat.sub_zero, Nat.cast_one] at h
  linarith

private theorem reciprocal_deriv_direct_sum {N j : ℕ} (hj : 0 < j) (hjN : j ≤ N) :
    ∑ x ∈ Finset.range N,
        (Nat.choose N (x + 1) : ℚ) *
          (if x + 1 = j then 1 else 0) *
            (1 / 2 : ℚ) ^ (N - 1 - x) =
      (Nat.choose N j : ℚ) * (1 / 2 : ℚ) ^ (N - j) := by
  rw [Finset.sum_eq_single (j - 1)]
  · have hidx : j - 1 + 1 = j := by omega
    have hexp : N - 1 - (j - 1) = N - j := by
      rw [Nat.sub_sub]
      congr 1
      omega
    rw [hidx, if_pos rfl]
    rw [hexp]
    ring
  · intro x hx hne
    have hneq : x + 1 ≠ j := by
      intro heq
      apply hne
      omega
    simp [hneq]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (by omega))).elim

private theorem reciprocal_deriv_recursive_sum {n j : ℕ} (hj : j ≤ n + 1) :
    ∑ x ∈ Finset.range (n + 1),
        (Nat.choose (n + 1) (x + 1) : ℚ) * (-1 / 2 : ℚ) ^ (x + 1) *
          (if j ≤ n - x then (Nat.choose (n - x) j : ℚ) else 0) =
      (Nat.choose (n + 1) j : ℚ) * (1 / 2 : ℚ) ^ (n + 1 - j) -
        (Nat.choose (n + 1) j : ℚ) := by
  have hsubset : Finset.range (n + 1 - j) ⊆ Finset.range (n + 1) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hrestrict :
      ∑ x ∈ Finset.range (n + 1),
          (Nat.choose (n + 1) (x + 1) : ℚ) * (-1 / 2 : ℚ) ^ (x + 1) *
            (if j ≤ n - x then (Nat.choose (n - x) j : ℚ) else 0) =
        ∑ x ∈ Finset.range (n + 1 - j),
          (Nat.choose (n + 1) (x + 1) : ℚ) * (-1 / 2 : ℚ) ^ (x + 1) *
            (Nat.choose ((n + 1) - (x + 1)) j : ℚ) := by
    let F : ℕ → ℚ := fun x =>
      (Nat.choose (n + 1) (x + 1) : ℚ) * (-1 / 2 : ℚ) ^ (x + 1) *
        (Nat.choose ((n + 1) - (x + 1)) j : ℚ)
    have hsum :
        ∑ x ∈ Finset.range (n + 1 - j), F x =
          ∑ x ∈ Finset.range (n + 1), F x := by
      apply Finset.sum_subset hsubset
      intro x hxN hxq
      have hxN' : x < n + 1 := Finset.mem_range.mp hxN
      have hxq' : ¬x < n + 1 - j := by
        simpa only [Finset.mem_range] using hxq
      have hlt : n + 1 - (x + 1) < j := by omega
      change F x = 0
      dsimp only [F]
      rw [Nat.choose_eq_zero_of_lt hlt]
      simp
    calc
      _ = ∑ x ∈ Finset.range (n + 1), F x := by
        apply Finset.sum_congr rfl
        intro x hx
        have hx' : x < n + 1 := Finset.mem_range.mp hx
        have hsub : n + 1 - (x + 1) = n - x := by omega
        dsimp only [F]
        rw [hsub]
        by_cases hle : j ≤ n - x
        · simp [hle]
        · have hlt : n - x < j := by omega
          rw [if_neg hle, Nat.choose_eq_zero_of_lt hlt]
          simp
      _ = _ := hsum.symm
  rw [hrestrict]
  exact reciprocal_deriv_convolution_tail hj

theorem universalReciprocalJetPolynomial_aeval_base (n : ℕ) :
    aeval reciprocalExponentialBase (universalReciprocalJetPolynomial n) =
      (1 / 2 : ℚ) ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | n
      · simp [universalReciprocalJetPolynomial, reciprocalExponentialBase]
      · rw [universalReciprocalJetPolynomial]
        simp only [map_neg, map_mul, aeval_X, map_sum, aeval_C]
        simp only [reciprocalExponentialBase, if_pos]
        have hrec : ∀ k,
            aeval reciprocalExponentialBase
                (universalReciprocalJetPolynomial (n - k)) =
              (1 / 2 : ℚ) ^ (n - k) := by
          intro k
          apply ih
          omega
        simp_rw [hrec]
        simp only [map_natCast, if_neg (Nat.succ_ne_zero _)]
        rw [shifted_binomial_base_sum]
        ring

theorem universalReciprocalJetPolynomial_pderiv_zero_aeval (n : ℕ) :
    aeval reciprocalExponentialBase
        (pderiv 0 (universalReciprocalJetPolynomial n)) = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | n
      · simp [universalReciprocalJetPolynomial]
      · rw [universalReciprocalJetPolynomial]
        simp only [map_neg, pderiv_mul, pderiv_X, Pi.single_apply, if_pos,
          map_add, map_mul, map_sum, aeval_X, pderiv_C, map_one]
        have hderiv : ∀ k,
            aeval reciprocalExponentialBase
                (pderiv 0 (universalReciprocalJetPolynomial (n - k))) = 1 := by
          intro k
          apply ih
          omega
        have hbase : ∀ k,
            aeval reciprocalExponentialBase
                (universalReciprocalJetPolynomial (n - k)) =
              (1 / 2 : ℚ) ^ (n - k) := by
          intro k
          exact universalReciprocalJetPolynomial_aeval_base (n - k)
        simp_rw [hderiv, hbase]
        simp only [reciprocalExponentialBase, if_pos, if_neg (Nat.succ_ne_zero _),
          map_natCast, mul_one]
        simp only [map_zero, mul_zero, zero_mul, zero_add]
        rw [shifted_binomial_base_sum, shifted_binomial_raw_sum]
        ring

theorem universalReciprocalJetPolynomial_pderiv_pos_aeval (j n : ℕ) (hj : 0 < j) :
    aeval reciprocalExponentialBase
        (pderiv j (universalReciprocalJetPolynomial n)) =
      if j ≤ n then -(Nat.choose n j : ℚ) else 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | n
      · simp [universalReciprocalJetPolynomial, hj.ne']
      · rw [universalReciprocalJetPolynomial]
        simp only [map_neg, pderiv_mul, pderiv_X, Pi.single_apply,
          zero_mul, zero_add, map_add, map_mul, map_sum, aeval_X, pderiv_C]
        have hderiv : ∀ k,
            aeval reciprocalExponentialBase
                (pderiv j (universalReciprocalJetPolynomial (n - k))) =
              if j ≤ n - k then -(Nat.choose (n - k) j : ℚ) else 0 := by
          intro k
          apply ih
          omega
        have hbase : ∀ k,
            aeval reciprocalExponentialBase
                (universalReciprocalJetPolynomial (n - k)) =
              (1 / 2 : ℚ) ^ (n - k) := by
          intro k
          exact universalReciprocalJetPolynomial_aeval_base (n - k)
        simp_rw [hderiv, hbase]
        simp only [reciprocalExponentialBase, if_pos,
          if_neg (Nat.succ_ne_zero _), map_natCast]
        have hz :
            aeval reciprocalExponentialBase
                ((if 0 = j then 1 else 0) : MvPolynomial ℕ ℚ) = 0 := by
          have h0j : 0 ≠ j := by omega
          simp [h0j]
        rw [hz]
        simp only [neg_zero, zero_mul, zero_add]
        have hmap : ∀ x : ℕ,
            aeval reciprocalExponentialBase
                ((if x + 1 = j then 1 else 0) : MvPolynomial ℕ ℚ) =
              (if x + 1 = j then 1 else 0) := by
          intro x
          by_cases h : x + 1 = j <;> simp [h]
        simp_rw [hmap]
        by_cases hjN : j ≤ n + 1
        · rw [if_pos hjN]
          have hdirect := reciprocal_deriv_direct_sum hj hjN
          have hdirect' :
              ∑ x ∈ Finset.range (n + 1),
                  (Nat.choose (n + 1) (x + 1) : ℚ) *
                    (if x + 1 = j then 1 else 0) * (1 / 2 : ℚ) ^ (n - x) =
                (Nat.choose (n + 1) j : ℚ) *
                  (1 / 2 : ℚ) ^ (n + 1 - j) := by
            simpa only [Nat.add_sub_cancel] using hdirect
          have hrecursive := reciprocal_deriv_recursive_sum hjN
          have hneg :
              ∑ x ∈ Finset.range (n + 1),
                  (Nat.choose (n + 1) (x + 1) : ℚ) * (-1 / 2 : ℚ) ^ (x + 1) *
                    (if j ≤ n - x then -(Nat.choose (n - x) j : ℚ) else 0) =
                -∑ x ∈ Finset.range (n + 1),
                  (Nat.choose (n + 1) (x + 1) : ℚ) * (-1 / 2 : ℚ) ^ (x + 1) *
                    (if j ≤ n - x then (Nat.choose (n - x) j : ℚ) else 0) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro x hx
            by_cases hle : j ≤ n - x <;> simp [hle]
          rw [Finset.sum_add_distrib, hdirect', hneg, hrecursive]
          ring
        · rw [if_neg hjN]
          have hzero :
              ∑ x ∈ Finset.range (n + 1),
                  ((Nat.choose (n + 1) (x + 1) : ℚ) *
                        (if x + 1 = j then 1 else 0) * (1 / 2 : ℚ) ^ (n - x) +
                    (Nat.choose (n + 1) (x + 1) : ℚ) * (-1 / 2 : ℚ) ^ (x + 1) *
                      (if j ≤ n - x then -(Nat.choose (n - x) j : ℚ) else 0)) = 0 := by
            apply Finset.sum_eq_zero
            intro x hx
            have hxlt : x < n + 1 := Finset.mem_range.mp hx
            have hneq : x + 1 ≠ j := by omega
            have hnot : ¬j ≤ n - x := by omega
            simp [hneq, hnot]
          rw [hzero]
          ring

noncomputable def universalReciprocalJetPolynomialOver
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K]
    (n : ℕ) : MvPolynomial ℕ K :=
  MvPolynomial.map (algebraMap ℚ K) (universalReciprocalJetPolynomial n)

noncomputable def reciprocalExponentialBaseOver
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K] (k : ℕ) : K :=
  algebraMap ℚ K (reciprocalExponentialBase k)

@[simp]
theorem universalReciprocalJetPolynomialOver_zero
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K] :
    universalReciprocalJetPolynomialOver K 0 = MvPolynomial.X 0 := by
  simp [universalReciprocalJetPolynomialOver, universalReciprocalJetPolynomial]

theorem universalReciprocalJetPolynomialOver_succ
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K] (n : ℕ) :
    universalReciprocalJetPolynomialOver K (n + 1) =
      -MvPolynomial.X 0 * ∑ k ∈ Finset.range (n + 1),
        MvPolynomial.C (algebraMap ℚ K (Nat.choose (n + 1) (k + 1))) *
          MvPolynomial.X (k + 1) * universalReciprocalJetPolynomialOver K (n - k) := by
  simp only [universalReciprocalJetPolynomialOver,
    universalReciprocalJetPolynomial, map_neg, map_mul, MvPolynomial.map_X,
    map_sum, MvPolynomial.map_C]

private theorem aeval_universalReciprocalJetPolynomialOver
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K]
    (P : MvPolynomial ℕ ℚ) :
    MvPolynomial.aeval (reciprocalExponentialBaseOver K)
        (MvPolynomial.map (algebraMap ℚ K) P) =
      algebraMap ℚ K (MvPolynomial.aeval reciprocalExponentialBase P) := by
  simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  rw [MvPolynomial.eval₂_comp_right]
  have hmapid : MvPolynomial.map (algebraMap ℚ ℚ) P = P := by
    change MvPolynomial.map (RingHom.id ℚ) P = P
    exact MvPolynomial.map_id P
  rw [hmapid]
  rfl

theorem universalReciprocalJetPolynomialOver_pderiv_aeval
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K] (j n : ℕ) :
    MvPolynomial.aeval (reciprocalExponentialBaseOver K)
        (MvPolynomial.pderiv j (universalReciprocalJetPolynomialOver K n)) =
      algebraMap ℚ K
        (MvPolynomial.aeval reciprocalExponentialBase
          (MvPolynomial.pderiv j (universalReciprocalJetPolynomial n))) := by
  rw [universalReciprocalJetPolynomialOver, MvPolynomial.pderiv_map]
  exact aeval_universalReciprocalJetPolynomialOver K _

theorem universalReciprocalJetPolynomialOver_pderiv_aeval_eq
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K] (j n : ℕ) :
    MvPolynomial.aeval (reciprocalExponentialBaseOver K)
        (MvPolynomial.pderiv j (universalReciprocalJetPolynomialOver K n)) =
      if j = 0 then 1 else -(Nat.choose n j : K) := by
  rw [universalReciprocalJetPolynomialOver_pderiv_aeval]
  by_cases hj : j = 0
  · subst j
    rw [universalReciprocalJetPolynomial_pderiv_zero_aeval]
    simp
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
    rw [universalReciprocalJetPolynomial_pderiv_pos_aeval j n hjpos]
    by_cases hjn : j ≤ n
    · simp [hj, hjn]
    · have hchoose : Nat.choose n j = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [hj, hjn, hchoose]

noncomputable def reciprocalJetZLinearizationMinorOver
    (K : Type*) [Field K] [CharZero K] (n r : ℕ) :
    Matrix (Fin r) (Fin r) K :=
  fun i k => if (k : ℕ) = 0 then 1 else -(Nat.choose (n + i) k : K)

theorem reciprocalJetZLinearizationMinorOver_det_ne_zero
    (K : Type*) [Field K] [CharZero K] (n r : ℕ) :
    (reciprocalJetZLinearizationMinorOver K n r).det ≠ 0 := by
  classical
  let R : Matrix (Fin r) (Fin r) K :=
    (reciprocalJetLinearizationMinor n r).map (Int.castRingHom K)
  let d : Fin r → K := fun k => if (k : ℕ) = 0 then -1 else 1
  have hmatrix : reciprocalJetZLinearizationMinorOver K n r =
      R * Matrix.diagonal d := by
    ext i k
    simp only [Matrix.mul_diagonal, reciprocalJetZLinearizationMinorOver]
    by_cases hk : (k : ℕ) = 0
    · simp [R, d, hk, reciprocalJetLinearizationMinor, shiftedPascalMatrix]
    · simp [R, d, hk, reciprocalJetLinearizationMinor, shiftedPascalMatrix]
  have hRdet : R.det ≠ 0 := by
    have hmap := (Int.castRingHom K).map_det
      (reciprocalJetLinearizationMinor n r)
    change (Int.castRingHom K) (reciprocalJetLinearizationMinor n r).det = R.det at hmap
    rw [reciprocalJetLinearizationMinor_det] at hmap
    rw [← hmap]
    simp
  have hddet : (Matrix.diagonal d).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    rw [Finset.prod_ne_zero_iff]
    intro k hk
    change (if (k : ℕ) = 0 then (-1 : K) else 1) ≠ 0
    split_ifs <;> norm_num
  rw [hmatrix, Matrix.det_mul]
  exact mul_ne_zero hRdet hddet

noncomputable def finiteHorizonSelectedPolynomial
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K]
    (m n a r : ℕ) : Fin r ⊕ Fin a → MvPolynomial ℕ K
  | Sum.inl i => universalReciprocalJetPolynomialOver K (n + i)
  | Sum.inr i => MvPolynomial.X (m + i)

def finiteHorizonSelectedCoordinate (m a r : ℕ) : Fin r ⊕ Fin a → ℕ
  | Sum.inl k => k
  | Sum.inr k => m + k

theorem finiteHorizonSelectedPolynomial_algebraicIndependent
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K]
    (m n a r : ℕ) (hrm : r ≤ m) :
    AlgebraicIndependent K (finiteHorizonSelectedPolynomial K m n a r) := by
  classical
  let f := finiteHorizonSelectedPolynomial K m n a r
  let coordinate := finiteHorizonSelectedCoordinate m a r
  let M := MvPolynomial.polynomialJacobianMinor f coordinate
  let J := M.map (MvPolynomial.aeval (reciprocalExponentialBaseOver K))
  let C : Matrix (Fin a) (Fin r) K := fun i k => J (Sum.inr i) (Sum.inl k)
  have hJ : J = Matrix.fromBlocks
      (reciprocalJetZLinearizationMinorOver K n r).transpose 0 C 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp only [J, M, Matrix.map_apply, MvPolynomial.polynomialJacobianMinor,
        f, coordinate, finiteHorizonSelectedPolynomial,
        finiteHorizonSelectedCoordinate, Matrix.fromBlocks_apply₁₁,
        Matrix.transpose_apply, reciprocalJetZLinearizationMinorOver]
      rw [universalReciprocalJetPolynomialOver_pderiv_aeval_eq]
    · have hne : (i : ℕ) ≠ m + (j : ℕ) := by omega
      simp [J, M, f, coordinate, finiteHorizonSelectedPolynomial,
        finiteHorizonSelectedCoordinate, MvPolynomial.polynomialJacobianMinor,
        Matrix.fromBlocks_apply₁₂, hne]
    · rfl
    · by_cases hij : i = j
      · subst j
        simp [J, M, f, coordinate, finiteHorizonSelectedPolynomial,
          finiteHorizonSelectedCoordinate, MvPolynomial.polynomialJacobianMinor]
      · have hval : (j : ℕ) ≠ (i : ℕ) := by
          intro h
          apply hij
          apply Fin.ext
          exact h.symm
        have hne : m + (j : ℕ) ≠ m + (i : ℕ) := by omega
        simp [J, M, f, coordinate, finiteHorizonSelectedPolynomial,
          finiteHorizonSelectedCoordinate, MvPolynomial.polynomialJacobianMinor,
          hij]
        rw [Pi.single_apply, if_neg hne]
        simp
  have hJdet : J.det ≠ 0 := by
    rw [hJ, Matrix.det_fromBlocks_zero₁₂, Matrix.det_transpose, Matrix.det_one, mul_one]
    exact reciprocalJetZLinearizationMinorOver_det_ne_zero K n r
  have hMdet : M.det ≠ 0 := by
    intro hzero
    have hmap := (MvPolynomial.aeval (reciprocalExponentialBaseOver K)).map_det M
    change MvPolynomial.aeval (reciprocalExponentialBaseOver K) M.det = J.det at hmap
    rw [hzero, map_zero] at hmap
    exact hJdet hmap.symm
  exact MvPolynomial.algebraicIndependent_of_jacobian_det_ne_zero f coordinate hMdet

def natEquivOption : ℕ ≃ Option ℕ where
  toFun
    | 0 => none
    | n + 1 => some n
  invFun
    | none => 0
    | some n => n + 1
  left_inv n := by cases n <;> rfl
  right_inv o := by cases o <;> rfl

noncomputable def reciprocalCoordinateFamily
    {E : Type*} [Field E] (x : ℕ → E) : ℕ → E
  | 0 => (x 0)⁻¹
  | n + 1 => x (n + 1)

theorem reciprocalCoordinateFamily_algebraicIndependent
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (x : ℕ → E) (hx : AlgebraicIndependent F x) :
    AlgebraicIndependent F (reciprocalCoordinateFamily x) := by
  let tail : ℕ → E := fun n => x (n + 1)
  have hsucc : Function.Injective (fun n : ℕ => n + 1) := by
    intro i j h
    exact Nat.add_right_cancel h
  have htail : AlgebraicIndependent F tail := hx.comp _ hsucc
  let withZero : Option ℕ → E := fun o => o.elim (x 0) tail
  have hcompZero : withZero ∘ natEquivOption = x := by
    funext n
    cases n <;> rfl
  have hwithZero : AlgebraicIndependent F withZero :=
    (algebraicIndependent_equiv' natEquivOption hcompZero).mp hx
  have hx0trans : Transcendental (Algebra.adjoin F (Set.range tail)) (x 0) :=
    (htail.option_iff_transcendental (x 0)).mp hwithZero
  have hinvtrans : Transcendental (Algebra.adjoin F (Set.range tail)) (x 0)⁻¹ := by
    intro hinv
    exact hx0trans (by simpa using hinv.inv)
  let withInverse : Option ℕ → E := fun o => o.elim (x 0)⁻¹ tail
  have hwithInverse : AlgebraicIndependent F withInverse :=
    (htail.option_iff_transcendental (x 0)⁻¹).mpr hinvtrans
  have hcompInverse : withInverse ∘ natEquivOption = reciprocalCoordinateFamily x := by
    funext n
    cases n <;> rfl
  exact (algebraicIndependent_equiv' natEquivOption hcompInverse).mpr hwithInverse

noncomputable def finiteHorizonSelectedObservation
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero F] [Algebra ℚ F]
    (x : ℕ → E) (m n a r : ℕ) : Fin r ⊕ Fin a → E :=
  fun i => MvPolynomial.aeval (reciprocalCoordinateFamily x)
    (finiteHorizonSelectedPolynomial F m n a r i)

theorem finiteHorizonSelectedObservation_algebraicIndependent
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero F] [Algebra ℚ F]
    (x : ℕ → E) (hx : AlgebraicIndependent F x)
    (m n a r : ℕ) (hrm : r ≤ m) :
    AlgebraicIndependent F
      (finiteHorizonSelectedObservation (F := F) (E := E) x m n a r) := by
  have hpoly := finiteHorizonSelectedPolynomial_algebraicIndependent F m n a r hrm
  have hcoord := reciprocalCoordinateFamily_algebraicIndependent x hx
  have hinj : Function.Injective
      (MvPolynomial.aeval (reciprocalCoordinateFamily x) :
        MvPolynomial ℕ F → E) :=
    algebraicIndependent_iff_injective_aeval.mp hcoord
  exact hpoly.map hinj.injOn

noncomputable def finiteReciprocalJetValue
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero F] [Algebra ℚ F]
    (x : ℕ → E) (j : ℕ) : E :=
  MvPolynomial.aeval (reciprocalCoordinateFamily x)
    (universalReciprocalJetPolynomialOver F j)

noncomputable def finiteHorizonObservation
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero F] [Algebra ℚ F]
    (x : ℕ → E) (m n N : ℕ) :
    Fin (finiteHorizonObservableCount N n) ⊕
      Fin (finiteHorizonObservableCount N m) → E
  | Sum.inl i => finiteReciprocalJetValue (F := F) (E := E) x (n + i)
  | Sum.inr i => reciprocalCoordinateFamily x (m + i)

noncomputable def finiteReciprocalAmbientCoordinate
    {E : Type*} [Field E] (x : ℕ → E) (N : ℕ) : Fin (N + 1) → E :=
  fun i => reciprocalCoordinateFamily x i

theorem finiteReciprocalAmbientCoordinate_algebraicIndependent
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (x : ℕ → E) (hx : AlgebraicIndependent F x) (N : ℕ) :
    AlgebraicIndependent F (finiteReciprocalAmbientCoordinate x N) := by
  have hcoord := reciprocalCoordinateFamily_algebraicIndependent x hx
  exact hcoord.comp Fin.val Fin.val_injective

theorem finiteReciprocalJetValue_mem_adjoin_ambient
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero F] [Algebra ℚ F]
    (x : ℕ → E) {j N : ℕ} (hjN : j ≤ N) :
    finiteReciprocalJetValue (F := F) x j ∈
      Algebra.adjoin F
        (Set.range (finiteReciprocalAmbientCoordinate x N)) := by
  let J := Algebra.adjoin F
    (Set.range (finiteReciprocalAmbientCoordinate x N))
  induction j using Nat.strong_induction_on with
  | h j ih =>
      rcases j with _ | n
      · rw [finiteReciprocalJetValue, universalReciprocalJetPolynomialOver_zero]
        simp only [MvPolynomial.aeval_X]
        exact Algebra.subset_adjoin
          (Set.mem_range_self (⟨0, by omega⟩ : Fin (N + 1)))
      · rw [finiteReciprocalJetValue, universalReciprocalJetPolynomialOver_succ]
        simp only [map_neg, map_mul, map_sum, MvPolynomial.aeval_X,
          MvPolynomial.aeval_C]
        apply J.mul_mem
        · apply J.neg_mem
          exact Algebra.subset_adjoin
            (Set.mem_range_self (⟨0, by omega⟩ : Fin (N + 1)))
        · apply J.sum_mem
          intro k hk
          apply J.mul_mem
          · apply J.mul_mem
            · exact J.algebraMap_mem _
            · have hklt : k < n + 1 := Finset.mem_range.mp hk
              exact Algebra.subset_adjoin
                (Set.mem_range_self (⟨k + 1, by omega⟩ : Fin (N + 1)))
          · apply ih (n - k) (by omega)
            omega

theorem finiteHorizonObservation_range_subset_closure
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero F] [Algebra ℚ F]
    (x : ℕ → E) {m n N : ℕ}
    (hm : m ≤ N + 1) (hn : n ≤ N + 1) :
    Set.range (finiteHorizonObservation (F := F) (E := E) x m n N) ⊆
      (AlgebraicIndependent.matroid F E).closure
        (Set.range (finiteReciprocalAmbientCoordinate x N)) := by
  intro z hz
  obtain ⟨i, rfl⟩ := hz
  rw [AlgebraicIndependent.matroid_closure_eq]
  change IsAlgebraic
    (Algebra.adjoin F (Set.range (finiteReciprocalAmbientCoordinate x N))) _
  rcases i with i | i
  · have hjN : n + (i : ℕ) ≤ N := by
      have hi : (i : ℕ) < finiteHorizonObservableCount N n := i.isLt
      simp only [finiteHorizonObservableCount] at hi
      omega
    have hmem := finiteReciprocalJetValue_mem_adjoin_ambient
      (F := F) (E := E) x hjN
    exact isAlgebraic_algebraMap
      (⟨finiteReciprocalJetValue (F := F) x (n + i), hmem⟩ :
        Algebra.adjoin F (Set.range (finiteReciprocalAmbientCoordinate x N)))
  · have hidx : m + (i : ℕ) ≤ N := by
      have hi : (i : ℕ) < finiteHorizonObservableCount N m := i.isLt
      simp only [finiteHorizonObservableCount] at hi
      omega
    have hmem : reciprocalCoordinateFamily x (m + i) ∈
        Algebra.adjoin F (Set.range (finiteReciprocalAmbientCoordinate x N)) :=
      Algebra.subset_adjoin
        (Set.mem_range_self (⟨m + i, by omega⟩ : Fin (N + 1)))
    exact isAlgebraic_algebraMap
      (⟨reciprocalCoordinateFamily x (m + i), hmem⟩ :
        Algebra.adjoin F (Set.range (finiteReciprocalAmbientCoordinate x N)))

theorem algebraicIndependent_function_injective
    {F E I : Type*} [Field F] [Field E] [Algebra F E]
    {v : I → E} (hv : AlgebraicIndependent F v) : Function.Injective v := by
  intro i j hij
  have heval : MvPolynomial.aeval v
      (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial I F) = 0 := by
    simp [hij]
  have hinj := algebraicIndependent_iff_injective_aeval.mp hv
  have hpoly : (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial I F) = 0 :=
    hinj (by simpa using heval)
  have hX : (MvPolynomial.X i : MvPolynomial I F) = MvPolynomial.X j :=
    sub_eq_zero.mp hpoly
  exact MvPolynomial.X_injective hX

noncomputable def finiteHorizonObservationTranscendenceRank
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero F] [Algebra ℚ F]
    (x : ℕ → E) (m n N : ℕ) : ℕ :=
  ((AlgebraicIndependent.matroid F E).eRk
    (Set.range (finiteHorizonObservation (F := F) (E := E) x m n N))).toNat

theorem finiteHorizonObservationTranscendenceRank_eq
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero F] [Algebra ℚ F]
    (x : ℕ → E) (hx : AlgebraicIndependent F x)
    {m n N : ℕ} (hm : m ≤ N + 1) (hn : n ≤ N + 1) :
    finiteHorizonObservationTranscendenceRank
        (F := F) (E := E) x m n N =
      finiteHorizonObservationRank m n N := by
  classical
  let a := finiteHorizonObservableCount N m
  let b := finiteHorizonObservableCount N n
  let r := min m b
  let selected := finiteHorizonSelectedObservation
    (F := F) (E := E) x m n a r
  let observed := finiteHorizonObservation (F := F) (E := E) x m n N
  let M := AlgebraicIndependent.matroid F E
  have hrm : r ≤ m := min_le_left _ _
  have hrb : r ≤ b := min_le_right _ _
  have hselected : AlgebraicIndependent F selected := by
    simpa [selected] using
      finiteHorizonSelectedObservation_algebraicIndependent
        (F := F) (E := E) x hx m n a r hrm
  have hselinj : Function.Injective selected :=
    algebraicIndependent_function_injective hselected
  have hselRange : M.Indep (Set.range selected) := by
    rw [AlgebraicIndependent.matroid_indep_iff]
    exact (algebraicIndependent_subtype_range hselinj).mpr hselected
  have hselCard : (Set.range selected).encard = ENat.card (Fin r ⊕ Fin a) := by
    calc
      (Set.range selected).encard = (Set.univ : Set (Fin r ⊕ Fin a)).encard := by
        simpa only [Set.image_univ] using hselinj.encard_image Set.univ
      _ = ENat.card (Fin r ⊕ Fin a) := Set.encard_univ _
  have hsubset : Set.range selected ⊆ Set.range observed := by
    intro z hz
    obtain ⟨i, rfl⟩ := hz
    rcases i with i | i
    · let j : Fin b := ⟨i, by omega⟩
      refine ⟨Sum.inl j, ?_⟩
      simp [selected, observed, finiteHorizonSelectedObservation,
        finiteHorizonSelectedPolynomial, finiteHorizonObservation,
        finiteReciprocalJetValue, j]
    · refine ⟨Sum.inr i, ?_⟩
      simp [selected, observed, finiteHorizonSelectedObservation,
        finiteHorizonSelectedPolynomial, finiteHorizonObservation]
  have hlowerEN : ((r + a : ℕ) : ℕ∞) ≤ M.eRk (Set.range observed) := by
    have h := hselRange.encard_le_eRk_of_subset hsubset
    rw [hselCard] at h
    simpa [selected, add_comm] using h
  have hambientAI := finiteReciprocalAmbientCoordinate_algebraicIndependent x hx N
  have hambientInj : Function.Injective (finiteReciprocalAmbientCoordinate x N) :=
    algebraicIndependent_function_injective hambientAI
  have hambientIndep : M.Indep
      (Set.range (finiteReciprocalAmbientCoordinate x N)) := by
    rw [AlgebraicIndependent.matroid_indep_iff]
    exact (algebraicIndependent_subtype_range hambientInj).mpr hambientAI
  have hambientCard :
      (Set.range (finiteReciprocalAmbientCoordinate x N)).encard =
        ENat.card (Fin (N + 1)) := by
    calc
      (Set.range (finiteReciprocalAmbientCoordinate x N)).encard =
          (Set.univ : Set (Fin (N + 1))).encard := by
        simpa only [Set.image_univ] using hambientInj.encard_image Set.univ
      _ = ENat.card (Fin (N + 1)) := Set.encard_univ _
  have hambientEN : M.eRk (Set.range observed) ≤ ((N + 1 : ℕ) : ℕ∞) := by
    have hsub := finiteHorizonObservation_range_subset_closure
      (F := F) (E := E) x (m := m) (n := n) (N := N) hm hn
    have h := M.eRk_mono hsub
    rw [M.eRk_closure_eq, hambientIndep.eRk_eq_encard,
      hambientCard] at h
    simpa using h
  have hdisplayEN : M.eRk (Set.range observed) ≤ ((a + b : ℕ) : ℕ∞) := by
    refine (M.eRk_le_encard (Set.range observed)).trans ?_
    calc
      (Set.range observed).encard = (observed '' Set.univ).encard := by
        rw [Set.image_univ]
      _ ≤ Set.univ.encard := Set.encard_image_le observed Set.univ
      _ = ENat.card (Fin b ⊕ Fin a) := Set.encard_univ _
      _ = ((a + b : ℕ) : ℕ∞) := by simp [Nat.add_comm]
  have hfinite : M.eRk (Set.range observed) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) hambientEN
  have hlower : r + a ≤ (M.eRk (Set.range observed)).toNat :=
    ENat.toNat_le_toNat hlowerEN hfinite
  have hambient : (M.eRk (Set.range observed)).toNat ≤ N + 1 :=
    ENat.toNat_le_toNat hambientEN (ENat.coe_ne_top _)
  have hdisplay : (M.eRk (Set.range observed)).toNat ≤ a + b :=
    ENat.toNat_le_toNat hdisplayEN (ENat.coe_ne_top _)
  change (M.eRk (Set.range observed)).toNat = _
  rw [finiteHorizonObservationRank_eq_min hm hn]
  simp only [finiteJetAmbientCount]
  change (M.eRk (Set.range observed)).toNat = min (N + 1) (a + b)
  have hrank : r + a = min (N + 1) (a + b) := by
    simp [r, a, b, finiteHorizonObservableCount]
    omega
  omega

/-- Binomial Leibniz rule for the algebraic differential jets. -/
theorem differentialJet_mul_binomial
    {K : Type*} [CommRing K] [Differential K] (n : ℕ) (x y : K) :
    differentialJet n (x * y) =
      ∑ k ∈ Finset.range (n + 1),
        n.choose k • (differentialJet (n - k) x * differentialJet k y) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        differentialJet (n + 1) (x * y) =
            (Differential.deriv : Derivation ℤ K K)
              (∑ k ∈ Finset.range (n + 1),
                n.choose k •
                  (differentialJet (n - k) x * differentialJet k y)) := by
          rw [differentialJet_succ, ih]
        _ = (∑ k ∈ Finset.range (n + 1),
              n.choose k •
                (differentialJet (n - k + 1) x * differentialJet k y)) +
            ∑ k ∈ Finset.range (n + 1),
              n.choose k •
                (differentialJet (n - k) x * differentialJet (k + 1) y) := by
          simp_rw [map_sum, map_nsmul, Derivation.leibniz, smul_add,
            Finset.sum_add_distrib]
          have hsucc : ∀ (m : ℕ) (z : K),
              (differentialJet m z)′ = differentialJet (m + 1) z :=
            fun m z => (differentialJet_succ m z).symm
          simp_rw [hsucc]
          rw [add_comm]
          congr 1
          · apply Finset.sum_congr rfl
            intro k hk
            simp only [smul_eq_mul]
            ring
        _ = (∑ k ∈ Finset.range (n + 1),
                n.choose (k + 1) •
                  (differentialJet (n - k) x * differentialJet (k + 1) y)) +
              1 • (differentialJet (n + 1) x * differentialJet 0 y) +
            ∑ k ∈ Finset.range (n + 1),
              n.choose k •
                (differentialJet (n - k) x * differentialJet (k + 1) y) := by
          congr 1
          refine (Finset.sum_range_succ' _ _).trans (congrArg₂ (fun a b => a + b) ?_ ?_)
          · rw [Finset.sum_range_succ, Nat.choose_succ_self, zero_smul, add_zero]
            refine Finset.sum_congr rfl fun k hk => ?_
            rw [Finset.mem_range] at hk
            congr
            omega
          · rw [Nat.choose_zero_right, Nat.sub_zero]
        _ = ((∑ k ∈ Finset.range (n + 1),
              n.choose k •
                (differentialJet (n - k) x * differentialJet (k + 1) y)) +
            ∑ k ∈ Finset.range (n + 1),
              n.choose (k + 1) •
                (differentialJet (n - k) x * differentialJet (k + 1) y)) +
            1 • (differentialJet (n + 1) x * differentialJet 0 y) := by
          rw [add_comm, add_assoc]
        _ = (∑ i ∈ Finset.range (n + 1),
              (n + 1).choose (i + 1) •
                (differentialJet (n + 1 - (i + 1)) x *
                  differentialJet (i + 1) y)) +
            1 • (differentialJet (n + 1) x * differentialJet 0 y) := by
          simp_rw [Nat.choose_succ_succ, Nat.succ_sub_succ, add_smul,
            Finset.sum_add_distrib]
        _ = ∑ k ∈ Finset.range (n + 2),
              (n + 1).choose k •
                (differentialJet (n + 1 - k) x * differentialJet k y) := by
          rw [Finset.sum_range_succ' _ (n + 1), Nat.choose_zero_right,
            Nat.sub_zero]

/-- Symmetric binomial Leibniz rule, indexed by the jet order of the first factor. -/
theorem differentialJet_mul_binomial'
    {K : Type*} [CommRing K] [Differential K] (n : ℕ) (x y : K) :
    differentialJet n (x * y) =
      ∑ k ∈ Finset.range (n + 1),
        n.choose k • (differentialJet k x * differentialJet (n - k) y) := by
  simpa only [mul_comm] using differentialJet_mul_binomial n y x

/-- Every positive reciprocal jet is forced by the lower raw and reciprocal jets. -/
theorem differentialJet_inv_succ_recurrence
    {K : Type*} [Field K] [Differential K] (x : K) (hx : x ≠ 0) (n : ℕ) :
    differentialJet (n + 1) x⁻¹ =
      -x⁻¹ * ∑ k ∈ Finset.range (n + 1),
        (Nat.choose (n + 1) (k + 1) : K) *
          differentialJet (k + 1) x * differentialJet (n - k) x⁻¹ := by
  have hprod := differentialJet_mul_binomial' (n + 1) x x⁻¹
  rw [mul_inv_cancel₀ hx] at hprod
  rw [Finset.sum_range_succ'] at hprod
  simp only [Nat.choose_zero_right, one_smul, differentialJet_zero,
    Nat.sub_zero] at hprod
  have honeAll : ∀ q : ℕ, differentialJet (q + 1) (1 : K) = 0 := by
    intro q
    induction q with
    | zero => simp [differentialJet_succ]
    | succ q ih =>
        rw [differentialJet_succ, ih]
        simp
  have hone : differentialJet (n + 1) (1 : K) = 0 := honeAll n
  rw [hone] at hprod
  have htail :
      ∑ k ∈ Finset.range (n + 1),
          (n + 1).choose (k + 1) •
            (differentialJet (k + 1) x *
              differentialJet (n + 1 - (k + 1)) x⁻¹) =
        ∑ k ∈ Finset.range (n + 1),
          (Nat.choose (n + 1) (k + 1) : K) *
            differentialJet (k + 1) x * differentialJet (n - k) x⁻¹ := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.add_sub_add_right]
    simp only [nsmul_eq_mul]
    ring
  rw [htail] at hprod
  calc
    differentialJet (n + 1) x⁻¹ = x⁻¹ *
        (x * differentialJet (n + 1) x⁻¹) := by
      field_simp
    _ = -x⁻¹ * ∑ k ∈ Finset.range (n + 1),
        (Nat.choose (n + 1) (k + 1) : K) *
          differentialJet (k + 1) x * differentialJet (n - k) x⁻¹ := by
      rw [show x * differentialJet (n + 1) x⁻¹ =
          -∑ k ∈ Finset.range (n + 1),
            (Nat.choose (n + 1) (k + 1) : K) *
              differentialJet (k + 1) x * differentialJet (n - k) x⁻¹ by
        linear_combination -hprod]
      ring

/-- The universal reciprocal polynomial specializes to the actual reciprocal differential jet. -/
theorem finiteReciprocalJetValue_differentialJet_eq
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero F] [Algebra ℚ F] [Differential E]
    (x : E) (hx : x ≠ 0) (j : ℕ) :
    finiteReciprocalJetValue (F := F) (E := E)
        (fun k => differentialJet k x) j = differentialJet j x⁻¹ := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
      rcases j with _ | n
      · simp [finiteReciprocalJetValue, universalReciprocalJetPolynomialOver,
          universalReciprocalJetPolynomial, reciprocalCoordinateFamily]
      · rw [finiteReciprocalJetValue,
          universalReciprocalJetPolynomialOver_succ]
        simp only [map_neg, map_mul, map_sum, MvPolynomial.aeval_X,
          MvPolynomial.aeval_C]
        have hrec : ∀ k,
            MvPolynomial.aeval
                (reciprocalCoordinateFamily (fun j => differentialJet j x))
                (universalReciprocalJetPolynomialOver F (n - k)) =
              differentialJet (n - k) x⁻¹ := by
          intro k
          change finiteReciprocalJetValue (F := F)
              (fun j => differentialJet j x) (n - k) = _
          apply ih
          omega
        simp_rw [hrec]
        simp only [reciprocalCoordinateFamily, differentialJet_zero, map_natCast]
        exact (differentialJet_inv_succ_recurrence x hx n).symm

/-- The card's mixed finite packet of reciprocal and raw differential jets. -/
noncomputable def finiteDifferentialHorizonObservation
    {E : Type*} [Field E] [Differential E]
    (x : E) (m n N : ℕ) :
    Fin (finiteHorizonObservableCount N n) ⊕
      Fin (finiteHorizonObservableCount N m) → E
  | Sum.inl i => differentialJet (n + i) x⁻¹
  | Sum.inr i => differentialJet (m + i) x

theorem finiteHorizonObservation_differentialJet_eq
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero F] [Algebra ℚ F] [Differential E]
    (x : E) (hx : x ≠ 0) {m n N : ℕ} (hm0 : 0 < m) :
    finiteHorizonObservation (F := F) (E := E)
        (fun j => differentialJet j x) m n N =
      finiteDifferentialHorizonObservation x m n N := by
  funext i
  rcases i with i | i
  · exact finiteReciprocalJetValue_differentialJet_eq x hx (n + i)
  · rcases m with _ | m
    · omega
    · simp [finiteHorizonObservation, finiteDifferentialHorizonObservation,
        reciprocalCoordinateFamily, Nat.succ_add]

/-- Algebraic-matroid transcendence rank of the actual differential observation field. -/
noncomputable def finiteDifferentialHorizonObservationTranscendenceRank
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential E] (x : E) (m n N : ℕ) : ℕ :=
  ((AlgebraicIndependent.matroid F E).eRk
    (Set.range (finiteDifferentialHorizonObservation x m n N))).toNat

/-- Exact generic rank of the mixed raw/reciprocal finite differential-jet packet. -/
theorem finiteDifferentialHorizonObservationTranscendenceRank_eq
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero F] [Algebra ℚ F] [Differential E]
    (x : E) (hx : HypertranscendentalOver F x)
    {m n N : ℕ} (hm0 : 0 < m) (hm : m ≤ N + 1) (hn : n ≤ N + 1) :
    finiteDifferentialHorizonObservationTranscendenceRank
        (F := F) x m n N = finiteHorizonObservationRank m n N := by
  have hx0 : x ≠ 0 := by
    intro hzero
    apply hypertranscendentalOver_jet_transcendental hx 0
    simpa [hzero] using (isAlgebraic_zero : IsAlgebraic F (0 : E))
  have hjets : AlgebraicIndependent F (fun j => differentialJet j x) :=
    algebraicIndependent_differentialJet_of_hypertranscendentalOver hx
  have hrank := finiteHorizonObservationTranscendenceRank_eq
    (F := F) (E := E) (fun j => differentialJet j x) hjets hm hn
  unfold finiteHorizonObservationTranscendenceRank at hrank
  unfold finiteDifferentialHorizonObservationTranscendenceRank
  rw [finiteHorizonObservation_differentialJet_eq x hx0 hm0] at hrank
  exact hrank

end GaloisForLFunctions.HTGeometry
