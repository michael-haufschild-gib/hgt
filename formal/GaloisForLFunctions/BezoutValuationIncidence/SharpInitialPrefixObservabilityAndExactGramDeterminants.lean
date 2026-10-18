import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.PosDef
import GaloisForLFunctions.BezoutValuationIncidence.ExactFinitePrefixDiscrepancyDualityAndReturnTimes

/-!
# Sharp initial-prefix observability and exact Gram determinants

At level `N`, the first `N - 1` centered divisor-sum prefixes determine every
coefficient at divisors `2, ..., N`. At a shorter horizon, the exact kernel
consists of zero visible coefficients and one harmonic conservation law on the
hidden tail. A two-point weight proves that this horizon is sharp.

An explicit Möbius lift followed by the existing harmonic endpoint correction
interpolates arbitrary real prefix data. The actual floor-response matrix at
level `n + 1` has determinant `(-1)^n / (n + 1)`. Its factorization through the
Ramanujan primitive matrix gives determinant `(-1)^n * n!` for that matrix and
`(n!)^2 / ∏ e : Fin n, φ(e + 2)` for the positive definite variance-dual Gram
matrix. These are exact finite statements, including dimension zero; they make
no uniform conditioning or asymptotic cancellation claim.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section

/-- Discrepancy starts at zero, without any condition on the weights. -/
@[simp]
theorem sievePrefixDiscrepancy_zero (N : ℕ) (c : ℕ → ℝ) :
    sievePrefixDiscrepancy N 0 c = 0 := by
  rw [sievePrefixDiscrepancy_eq_neg_sievedFractSum, sievedFractSum_zero, neg_zero]

/-- The observed first difference is the divisor sum after removing harmonic drift. -/
theorem sievePrefixDiscrepancy_succ_sub (N M : ℕ) (c : ℕ → ℝ) :
    sievePrefixDiscrepancy N (M + 1) c - sievePrefixDiscrepancy N M c =
      sievedDivisorSum N c (M + 1) - finiteHarmonicSum N c := by
  rw [sievePrefixDiscrepancy_eq_neg_sievedFractSum,
    sievePrefixDiscrepancy_eq_neg_sievedFractSum]
  have h := sievedFractSum_succ_sub_eq N c M
  rw [selbergMultiplesCoord_one_eq_finiteHarmonicSum] at h
  linarith

/-- Discrepancy respects subtraction of weights. -/
theorem sievePrefixDiscrepancy_sub (N M : ℕ) (c b : ℕ → ℝ) :
    sievePrefixDiscrepancy N M (fun d => c d - b d) =
      sievePrefixDiscrepancy N M c - sievePrefixDiscrepancy N M b := by
  simp only [sievePrefixDiscrepancy, finiteFloorSum, finiteHarmonicSum,
    sub_mul, sub_div, Finset.sum_sub_distrib]
  ring

private theorem prefix_full_divisorSum (N m : ℕ) (c : ℕ → ℝ)
    (hm : m ∈ Finset.Icc 1 N) :
    sievedDivisorSum N c m = ∑ d ∈ m.divisors, c d := by
  unfold sievedDivisorSum truncatedSieveWeight
  apply Finset.sum_congr rfl
  intro d hd
  have hd1 := Nat.pos_of_mem_divisors hd
  have hdm := Nat.le_of_dvd (Finset.mem_Icc.mp hm).1 (Nat.dvd_of_mem_divisors hd)
  rw [if_pos (Finset.mem_Icc.mpr ⟨hd1, le_trans hdm (Finset.mem_Icc.mp hm).2⟩)]

private theorem prefix_harmonic_split (N S : ℕ) (c : ℕ → ℝ)
    (hS1 : 1 ≤ S) (hSN : S ≤ N) (hc : ∀ d ∈ Finset.Icc 2 S, c d = 0) :
    finiteHarmonicSum N c = c 1 + ∑ d ∈ Finset.Icc (S + 1) N, c d / (d : ℝ) := by
  have hhead : (∑ d ∈ Finset.Icc 1 S, c d / (d : ℝ)) = c 1 := by
    rw [Finset.sum_eq_single 1]
    · simp
    · intro d hd hd1
      rw [hc d (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hd).1; omega,
        (Finset.mem_Icc.mp hd).2⟩), zero_div]
    · intro h
      exact False.elim (h (Finset.mem_Icc.mpr ⟨by omega, hS1⟩))
  have h := Finset.sum_Ico_consecutive (fun d => c d / (d : ℝ))
    (show 1 ≤ S + 1 by omega) (show S + 1 ≤ N + 1 by omega)
  simp only [Finset.Ico_add_one_right_eq_Icc] at h
  rw [hhead] at h
  exact h.symm

/-- Exact hidden-weight kernel for every level and every initial observation horizon. -/
theorem sievePrefix_initial_kernel_iff (N T : ℕ) (c : ℕ → ℝ) :
    (∀ M ∈ Finset.Icc 1 T, sievePrefixDiscrepancy N M c = 0) ↔
      T = 0 ∨ ((∀ d ∈ Finset.Icc 2 (min T N), c d = 0) ∧
        (∑ d ∈ Finset.Icc (min T N + 1) N, c d / (d : ℝ)) = 0) := by
  by_cases hN : N = 0
  · subst N
    simp [sievePrefixDiscrepancy_eq_neg_sievedFractSum, sievedFractSum]
  by_cases hT : T = 0
  · subst T
    simp
  simp only [hT, false_or]
  let S := min T N
  have hN1 : 1 ≤ N := by omega
  have hT1 : 1 ≤ T := by omega
  have hS1 : 1 ≤ S := le_min hT1 hN1
  have hSN : S ≤ N := min_le_right T N
  have hST : S ≤ T := min_le_left T N
  change (∀ M ∈ Finset.Icc 1 T, sievePrefixDiscrepancy N M c = 0) ↔
    (∀ d ∈ Finset.Icc 2 S, c d = 0) ∧
      (∑ d ∈ Finset.Icc (S + 1) N, c d / (d : ℝ)) = 0
  constructor
  · intro hobs
    have hz : ∀ M, M ≤ T → sievePrefixDiscrepancy N M c = 0 := by
      intro M hM
      by_cases h0 : M = 0
      · subst M; simp
      · exact hobs M (Finset.mem_Icc.mpr ⟨by omega, hM⟩)
    have hdiv : ∀ m ∈ Finset.Icc 1 S,
        sievedDivisorSum N c m = finiteHarmonicSum N c := by
      intro m hm
      have hm1 := (Finset.mem_Icc.mp hm).1
      have hmT : m ≤ T := le_trans (Finset.mem_Icc.mp hm).2 hST
      have h := sievePrefixDiscrepancy_succ_sub N (m - 1) c
      rw [Nat.sub_add_cancel hm1, hz m hmT, hz (m - 1) (by omega)] at h
      linarith
    have hH : finiteHarmonicSum N c = c 1 := by
      have h := hdiv 1 (Finset.mem_Icc.mpr ⟨by omega, hS1⟩)
      simpa [sievedDivisorSum, truncatedSieveWeight, Finset.mem_Icc, hN1] using h.symm
    have hhead : ∀ m, m ≤ S → 2 ≤ m → c m = 0 := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        intro hmS hm2
        have hmN : m ≤ N := le_trans hmS hSN
        have hsumH : (∑ d ∈ m.divisors, c d) = c 1 := by
          rw [← prefix_full_divisorSum N m c (Finset.mem_Icc.mpr ⟨by omega, hmN⟩),
            hdiv m (Finset.mem_Icc.mpr ⟨by omega, hmS⟩), hH]
        have hsum : (∑ d ∈ m.divisors, c d) = c 1 + c m := by
          calc
            _ = ∑ d ∈ m.divisors,
                ((if d = 1 then c 1 else 0) + (if d = m then c m else 0)) := by
              apply Finset.sum_congr rfl
              intro d hd
              by_cases hd1 : d = 1
              · subst d; simp [show 1 ≠ m by omega]
              by_cases hdm : d = m
              · subst d; simp [show m ≠ 1 by omega]
              have hdpos := Nat.pos_of_mem_divisors hd
              have hdle := Nat.le_of_dvd (show 0 < m by omega) (Nat.dvd_of_mem_divisors hd)
              have hdlt : d < m := by omega
              have hdz := ih d hdlt (le_trans hdle hmS) (by omega)
              simp [hd1, hdm, hdz]
            _ = _ := by
              rw [Finset.sum_add_distrib]
              simp [Nat.mem_divisors, show m ≠ 0 by omega]
        linarith
    have hc : ∀ d ∈ Finset.Icc 2 S, c d = 0 :=
      fun d hd => hhead d (Finset.mem_Icc.mp hd).2 (Finset.mem_Icc.mp hd).1
    refine ⟨hc, ?_⟩
    have h := prefix_harmonic_split N S c hS1 hSN hc
    rw [hH] at h
    linarith
  · rintro ⟨hc, htail⟩ M hM
    have hH := prefix_harmonic_split N S c hS1 hSN hc
    rw [htail, add_zero] at hH
    have hdiv : ∀ m ∈ Finset.Icc 1 M, sievedDivisorSum N c m = c 1 := by
      intro m hm
      have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
      unfold sievedDivisorSum truncatedSieveWeight
      calc
        _ = ∑ d ∈ m.divisors, if d = 1 then c 1 else 0 := by
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hd1 : d = 1
          · subst d; simp [hN1]
          by_cases hdN : d ∈ Finset.Icc 1 N
          · have hdle := Nat.le_of_dvd hmpos (Nat.dvd_of_mem_divisors hd)
            have hdS : d ≤ S := le_min
              (le_trans hdle (le_trans (Finset.mem_Icc.mp hm).2 (Finset.mem_Icc.mp hM).2))
              (Finset.mem_Icc.mp hdN).2
            have hd2 : 2 ≤ d := by have := (Finset.mem_Icc.mp hdN).1; omega
            simp [hdN, hd1, hc d (Finset.mem_Icc.mpr ⟨hd2, hdS⟩)]
          · simp [hdN, hd1]
        _ = _ := by simp [Nat.mem_divisors, ne_of_gt hmpos]
    rw [sievePrefixDiscrepancy_eq_sum_sub_drift, hH]
    have hs : (∑ m ∈ Finset.Icc 1 M, sievedDivisorSum N c m) = (M : ℝ) * c 1 := by
      calc
        _ = ∑ _m ∈ Finset.Icc 1 M, c 1 := Finset.sum_congr rfl hdiv
        _ = _ := by simp
    rw [hs, sub_self]

/-- The first `N-1` prefix observations have exactly the constant-weight kernel. -/
theorem sievePrefix_initial_zero_iff_tail_zero (N : ℕ) (c : ℕ → ℝ) :
    (∀ M ∈ Finset.Icc 1 (N - 1), sievePrefixDiscrepancy N M c = 0) ↔
      ∀ d ∈ Finset.Icc 2 N, c d = 0 := by
  rw [sievePrefix_initial_kernel_iff,
    min_eq_left (Nat.sub_le N 1)]
  constructor
  · intro h d hd
    rcases h with hzero | ⟨hhead, htail⟩
    · have := (Finset.mem_Icc.mp hd).1
      have := (Finset.mem_Icc.mp hd).2
      omega
    · by_cases hdN : d = N
      · subst d
        have hN1 : 1 ≤ N := by have := (Finset.mem_Icc.mp hd).1; omega
        rw [Nat.sub_add_cancel hN1] at htail
        simp only [Finset.Icc_self, Finset.sum_singleton] at htail
        have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
        exact (div_eq_zero_iff.mp htail).resolve_right hn
      · exact hhead d (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
          by have := (Finset.mem_Icc.mp hd).2; omega⟩)
  · intro hc
    by_cases hzero : N - 1 = 0
    · exact Or.inl hzero
    right
    constructor
    · intro d hd
      exact hc d (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
        le_trans (Finset.mem_Icc.mp hd).2 (Nat.sub_le N 1)⟩)
    · apply Finset.sum_eq_zero
      intro d hd
      have hd2 : 2 ≤ d := by have := (Finset.mem_Icc.mp hd).1; omega
      rw [hc d (Finset.mem_Icc.mpr ⟨hd2, (Finset.mem_Icc.mp hd).2⟩), zero_div]

/-- Two weights have the same initial observations exactly when their nonconstant coefficients agree. -/
theorem sievePrefix_initial_eq_iff_tail_eq (N : ℕ) (c b : ℕ → ℝ) :
    (∀ M ∈ Finset.Icc 1 (N - 1),
      sievePrefixDiscrepancy N M c = sievePrefixDiscrepancy N M b) ↔
      ∀ d ∈ Finset.Icc 2 N, c d = b d := by
  have h := sievePrefix_initial_zero_iff_tail_zero N (fun d => c d - b d)
  simpa only [sievePrefixDiscrepancy_sub, sub_eq_zero] using h

/-- The exact variance kernel is the nonconstant coefficient kernel. -/
theorem sieveVariance_eq_zero_iff_tail_zero (N : ℕ) (c : ℕ → ℝ) :
    sieveVariance N c = 0 ↔ ∀ d ∈ Finset.Icc 2 N, c d = 0 := by
  have hY := selbergMultiplesCoord_tail_zero_iff N 1 c
  change (∑ e ∈ Finset.Icc 2 N,
      (Nat.totient e : ℝ) * (selbergMultiplesCoord N c e)^2) = 0 ↔ _
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun e _ => mul_nonneg (Nat.cast_nonneg e.totient) (sq_nonneg _))]
  rw [← hY]
  apply forall_congr'
  intro e
  apply forall_congr'
  intro he
  have hp : 0 < (Nat.totient e : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < e by have := (Finset.mem_Icc.mp he).1; omega)
  simp [ne_of_gt hp]

/-- Exactly `N-1` initial observations detect every nonzero-variance sieve profile. -/
theorem sievePrefix_initial_zero_iff_variance_zero (N : ℕ) (c : ℕ → ℝ) :
    (∀ M ∈ Finset.Icc 1 (N - 1), sievePrefixDiscrepancy N M c = 0) ↔
      sieveVariance N c = 0 := by
  rw [sievePrefix_initial_zero_iff_tail_zero, sieveVariance_eq_zero_iff_tail_zero]

/-- Initial-prefix data differentiated with the unobserved origin normalized to zero. -/
def sievePrefixDataIncrement (a : ℕ → ℝ) (m : ℕ) : ℝ :=
  if m = 1 then a 1 else a m - a (m - 1)

/-- The existing Möbius inversion applied to prescribed prefix increments. -/
def sievePrefixMobiusLift (a : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ p ∈ d.divisorsAntidiagonal, (moebius p.1 : ℝ) * sievePrefixDataIncrement a p.2

private theorem prefix_lift_divisorSum (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m) :
    (∑ d ∈ m.divisors, sievePrefixMobiusLift a d) = sievePrefixDataIncrement a m := by
  exact (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := sievePrefixMobiusLift a) (g := sievePrefixDataIncrement a)).mpr
      (fun _ _ => rfl) m hm

/-- Canonical zero-harmonic realization of arbitrary `n` initial prefix observations. -/
def sievePrefixInterpolatingWeight (n : ℕ) (a : ℕ → ℝ) : ℕ → ℝ :=
  kerPEndpointWeight (n + 1) (sievePrefixMobiusLift a)

/-- Every real initial-prefix data vector is realized, without any premise at the origin. -/
theorem sievePrefixInterpolatingWeight_realizes (n : ℕ) (a : ℕ → ℝ) :
    finiteHarmonicSum (n + 1) (sievePrefixInterpolatingWeight n a) = 0 ∧
      ∀ M ∈ Finset.Icc 1 n,
        sievePrefixDiscrepancy (n + 1) M (sievePrefixInterpolatingWeight n a) = a M := by
  have hH : finiteHarmonicSum (n + 1) (sievePrefixInterpolatingWeight n a) = 0 :=
    finiteHarmonicSum_kerPEndpointWeight_eq_zero (by omega) _
  refine ⟨hH, ?_⟩
  have hdiv : ∀ m ∈ Finset.Icc 1 n,
      sievedDivisorSum (n + 1) (sievePrefixInterpolatingWeight n a) m =
        sievePrefixDataIncrement a m := by
    intro m hm
    rw [sievePrefixInterpolatingWeight,
      sievedDivisorSum_kerPEndpointWeight_eq_of_lt (Finset.mem_Icc.mp hm).1
        (by have := (Finset.mem_Icc.mp hm).2; omega),
      prefix_full_divisorSum (n + 1) m _ (Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hm).1, by have := (Finset.mem_Icc.mp hm).2; omega⟩),
      prefix_lift_divisorSum a m (Finset.mem_Icc.mp hm).1]
  have hL : ∀ M, M ≤ n →
      sievePrefixDiscrepancy (n + 1) M (sievePrefixInterpolatingWeight n a) =
        if M = 0 then 0 else a M := by
    intro M
    induction M with
    | zero => intro _; simp
    | succ M ih =>
      intro hM
      have h := sievePrefixDiscrepancy_succ_sub (n + 1) M (sievePrefixInterpolatingWeight n a)
      rw [hdiv (M + 1) (Finset.mem_Icc.mpr ⟨by omega, hM⟩), hH,
        sub_zero, ih (by omega)] at h
      have he : sievePrefixDataIncrement a (M + 1) =
          a (M + 1) - (if M = 0 then 0 else a M) := by
        by_cases h0 : M = 0
        · subst M; simp [sievePrefixDataIncrement]
        · simp [sievePrefixDataIncrement, h0]
      rw [he] at h
      rw [if_neg (by omega : M + 1 ≠ 0)]
      linarith
  intro M hM
  rw [hL M (Finset.mem_Icc.mp hM).2, if_neg (by have := (Finset.mem_Icc.mp hM).1; omega)]

/-- Explicit reconstruction of all nonconstant coefficients from the initial observations. -/
theorem sievePrefixInterpolatingWeight_recovers_tail (n : ℕ) (c : ℕ → ℝ) :
    ∀ d ∈ Finset.Icc 2 (n + 1),
      sievePrefixInterpolatingWeight n (fun M => sievePrefixDiscrepancy (n + 1) M c) d = c d := by
  apply (sievePrefix_initial_eq_iff_tail_eq (n + 1) _ c).mp
  simpa only [Nat.add_sub_cancel] using
    (sievePrefixInterpolatingWeight_realizes n
      (fun M => sievePrefixDiscrepancy (n + 1) M c)).2

private theorem prefix_prod_denominators (n : ℕ) :
    (∏ i : Fin n, ((i.val + 2 : ℕ) : ℝ)) = ((n + 1).factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    change (∏ i : Fin n, ((i.val + 2 : ℕ) : ℝ)) * ((n + 2 : ℕ) : ℝ) =
      ((n + 2).factorial : ℝ)
    rw [ih, Nat.factorial_succ (n + 1)]
    push_cast
    ring

private def prefixFloorMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (((i.val + 1) / (j.val + 1) : ℕ) : ℝ)

private theorem prefixFloorMatrix_det (n : ℕ) : (prefixFloorMatrix n).det = 1 := by
  have htri : (prefixFloorMatrix n).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hlt : i.val < j.val := hij
    change (((i.val + 1) / (j.val + 1) : ℕ) : ℝ) = 0
    rw [Nat.div_eq_of_lt (by omega), Nat.cast_zero]
  rw [Matrix.det_of_lowerTriangular _ htri]
  simp [prefixFloorMatrix]

/-- The first `n` discrepancies against the nonconstant weights at level `n+1`. -/
def sievePrefixObservationMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (((i.val + 1) / (j.val + 2) : ℕ) : ℝ) -
    ((i.val + 1 : ℕ) : ℝ) / ((j.val + 2 : ℕ) : ℝ)

/-- Exact determinant of the initial-prefix observation matrix, including dimension zero. -/
theorem sievePrefixObservationMatrix_det (n : ℕ) :
    (sievePrefixObservationMatrix n).det = (-1 : ℝ)^n / ((n + 1 : ℕ) : ℝ) := by
  cases n with
  | zero => simp
  | succ n =>
    let A := sievePrefixObservationMatrix (n + 1)
    let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      fun i j => ((j.val + 2 : ℕ) : ℝ) * A i j
    let v : Fin (n + 1) → ℝ :=
      fun j => if j = Fin.last n then -1 else ((j.val + 2 : ℕ) : ℝ)
    let C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      fun i j => v j * prefixFloorMatrix (n + 1) i (finRotate (n + 1) j)
    have hB : B.det = ((n + 2).factorial : ℝ) * A.det := by
      change (Matrix.of fun i j : Fin (n + 1) => ((j.val + 2 : ℕ) : ℝ) * A i j).det = _
      simpa only [prefix_prod_denominators, show n + 1 + 1 = n + 2 from by omega] using
        (Matrix.det_mul_row (fun j : Fin (n + 1) => ((j.val + 2 : ℕ) : ℝ)) A)
    have hv : (∏ j, v j) = -((n + 1).factorial : ℝ) := by
      rw [Fin.prod_univ_castSucc]
      have hm : (∏ j : Fin n, v j.castSucc) = ((n + 1).factorial : ℝ) := by
        calc
          _ = ∏ j : Fin n, ((j.val + 2 : ℕ) : ℝ) := by
            apply Finset.prod_congr rfl
            intro j _
            simp [v]
          _ = _ := prefix_prod_denominators n
      rw [hm]
      simp [v]
    have hC : C.det = (-1 : ℝ)^(n + 1) * ((n + 1).factorial : ℝ) := by
      change (Matrix.of fun i j => v j *
        ((prefixFloorMatrix (n + 1)).submatrix id (finRotate (n + 1))) i j).det = _
      rw [Matrix.det_mul_row, hv]
      calc
        _ = -((n + 1).factorial : ℝ) * (-1 : ℝ)^n := by
          simp [Matrix.det_permute', sign_finRotate, prefixFloorMatrix_det]
        _ = _ := by rw [pow_succ]; ring
    have hlast (i : Fin (n + 1)) : B i (Fin.last n) = -((i.val + 1 : ℕ) : ℝ) := by
      have hdiv : (i.val + 1) / (n + 2) = 0 := Nat.div_eq_of_lt (by omega)
      have hn : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
      dsimp [B, A, sievePrefixObservationMatrix]
      rw [hdiv]
      simp only [Nat.cast_zero, zero_sub, mul_neg]
      field_simp
    have heq : C.det = B.det := by
      rw [← Matrix.det_transpose C, ← Matrix.det_transpose B]
      apply Matrix.det_eq_of_forall_row_eq_smul_add_const
        (fun j => if j = Fin.last n then (0 : ℝ) else -1) (Fin.last n) (by simp)
      intro j i
      change C i j = B i j + (if j = Fin.last n then (0 : ℝ) else -1) * B i (Fin.last n)
      rw [hlast]
      by_cases hj : j = Fin.last n
      · subst j
        rw [hlast]
        simp [C, v, prefixFloorMatrix]
      · have hd : ((j.val + 2 : ℕ) : ℝ) ≠ 0 := by positivity
        simp only [C, v, if_neg hj, prefixFloorMatrix, coe_finRotate_of_ne_last hj,
          B, A, sievePrefixObservationMatrix]
        have he : j.val + 1 + 1 = j.val + 2 := by omega
        rw [he]
        field_simp
        ring
    have h : ((n + 2).factorial : ℝ) * A.det =
        (-1 : ℝ)^(n + 1) * ((n + 1).factorial : ℝ) := by
      rw [← hB, ← heq, hC]
    have hf : ((n + 1).factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (n + 1)
    have hn : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    change A.det = (-1 : ℝ)^(n + 1) / ((n + 2 : ℕ) : ℝ)
    apply (eq_div_iff hn).mpr
    apply mul_left_cancel₀ hf
    rw [Nat.factorial_succ] at h
    push_cast at h ⊢
    nlinarith [h]

private theorem prefix_delta_fract (N M d : ℕ) (v : ℝ) (hd : d ∈ Finset.Icc 1 N) :
    sievePrefixDiscrepancy N M (fun k => if k = d then v else 0) =
      -v * fractDivSeq d M := by
  rw [sievePrefixDiscrepancy_eq_neg_sievedFractSum]
  simp [sievedFractSum, ite_mul, hd]

private theorem prefix_neg_fract (M d : ℕ) (hd : 0 < d) :
    -fractDivSeq d M = (((M / d : ℕ) : ℝ) - (M : ℝ) / (d : ℝ)) := by
  unfold fractDivSeq
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  have hm : ((M % d : ℕ) : ℝ) + (d : ℝ) * ((M / d : ℕ) : ℝ) = (M : ℝ) := by
    exact_mod_cast Nat.mod_add_div M d
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  field_simp
  nlinarith [hm]

/-- Exact response of each coefficient atom, linking prefix data to the centered floor matrix. -/
theorem sievePrefix_single_response (N M d : ℕ) (v : ℝ) (hd : d ∈ Finset.Icc 1 N) :
    sievePrefixDiscrepancy N M (fun k => if k = d then v else 0) =
      v * (((M / d : ℕ) : ℝ) - (M : ℝ) / (d : ℝ)) := by
  rw [prefix_delta_fract N M d v hd]
  calc
    _ = v * (-fractDivSeq d M) := by ring
    _ = _ := by rw [prefix_neg_fract M d (Finset.mem_Icc.mp hd).1]

/-- The explicit pair invisible until the last necessary observation. -/
def sievePrefixLastPairWeight (n d : ℕ) : ℝ :=
  (if d = n + 1 then ((n + 1 : ℕ) : ℝ) else 0) -
    (if d = n + 2 then ((n + 2 : ℕ) : ℝ) else 0)

/-- The initial horizon cannot be shortened at any nontrivial level. -/
theorem sievePrefixLastPairWeight_sharp_horizon (n : ℕ) :
    finiteHarmonicSum (n + 2) (sievePrefixLastPairWeight n) = 0 ∧
      (∀ M ∈ Finset.Icc 1 n,
        sievePrefixDiscrepancy (n + 2) M (sievePrefixLastPairWeight n) = 0) ∧
      sievePrefixDiscrepancy (n + 2) (n + 1) (sievePrefixLastPairWeight n) =
        ((n + 1 : ℕ) : ℝ) ∧
      0 < sieveVariance (n + 2) (sievePrefixLastPairWeight n) := by
  have h1 : n + 1 ∈ Finset.Icc 1 (n + 2) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have h2 : n + 2 ∈ Finset.Icc 1 (n + 2) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hn2 : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hH : finiteHarmonicSum (n + 2) (sievePrefixLastPairWeight n) = 0 := by
    simp only [sievePrefixLastPairWeight, finiteHarmonicSum, sub_div,
      Finset.sum_sub_distrib, ite_div, zero_div]
    rw [Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos h1, if_pos h2,
      div_self hn1, div_self hn2, sub_self]
  have hresponse (M : ℕ) :
      sievePrefixDiscrepancy (n + 2) M (sievePrefixLastPairWeight n) =
        -((n + 1 : ℕ) : ℝ) * fractDivSeq (n + 1) M -
          (-((n + 2 : ℕ) : ℝ) * fractDivSeq (n + 2) M) := by
    change sievePrefixDiscrepancy (n + 2) M
      (fun d => (if d = n + 1 then ((n + 1 : ℕ) : ℝ) else 0) -
        (if d = n + 2 then ((n + 2 : ℕ) : ℝ) else 0)) = _
    rw [sievePrefixDiscrepancy_sub, prefix_delta_fract _ _ _ _ h1,
      prefix_delta_fract _ _ _ _ h2]
  have hearly : ∀ M ∈ Finset.Icc 1 n,
      sievePrefixDiscrepancy (n + 2) M (sievePrefixLastPairWeight n) = 0 := by
    intro M hM
    rw [hresponse]
    unfold fractDivSeq
    rw [Int.fract_div_natCast_eq_div_natCast_mod,
      Int.fract_div_natCast_eq_div_natCast_mod,
      Nat.mod_eq_of_lt (by have := (Finset.mem_Icc.mp hM).2; omega : M < n + 1),
      Nat.mod_eq_of_lt (by have := (Finset.mem_Icc.mp hM).2; omega : M < n + 2)]
    field_simp
    ring
  have hlast : sievePrefixDiscrepancy (n + 2) (n + 1) (sievePrefixLastPairWeight n) =
      ((n + 1 : ℕ) : ℝ) := by
    rw [hresponse]
    unfold fractDivSeq
    rw [Int.fract_div_natCast_eq_div_natCast_mod,
      Int.fract_div_natCast_eq_div_natCast_mod,
      Nat.mod_self, Nat.mod_eq_of_lt (by omega : n + 1 < n + 2)]
    simp only [Nat.cast_zero, zero_div, mul_zero, zero_sub, neg_mul, neg_neg]
    field_simp
  have hv : 0 ≤ sieveVariance (n + 2) (sievePrefixLastPairWeight n) :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hvne : sieveVariance (n + 2) (sievePrefixLastPairWeight n) ≠ 0 := by
    intro hzero
    have hobs := (sievePrefix_initial_zero_iff_variance_zero (n + 2)
      (sievePrefixLastPairWeight n)).mpr hzero
    have h := hobs (n + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    rw [hlast] at h
    exact hn1 h
  refine ⟨hH, hearly, hlast, ?_⟩
  by_contra hle
  exact hvne (le_antisymm (le_of_not_gt hle) hv)

private theorem prefix_sum_Icc_two (n : ℕ) (f : ℕ → ℝ) :
    (∑ e ∈ Finset.Icc 2 (n + 1), f e) = ∑ e : Fin n, f (e.val + 2) := by
  calc
    _ = ∑ e ∈ Finset.range n, f (e + 2) := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
        show n + 1 + 1 - 2 = n from by omega]
      apply Finset.sum_congr rfl
      intro e _
      congr 1
      omega
    _ = _ := (Fin.sum_univ_eq_sum_range (fun e => f (e + 2)) n).symm

private theorem prefix_delta_coordinate (N e d : ℕ) (hd : d ∈ Finset.Icc 1 N) :
    selbergMultiplesCoord N (fun k => if k = d then (1 : ℝ) else 0) e =
      if e ∣ d then 1 / (d : ℝ) else 0 := by
  simp [selbergMultiplesCoord, ite_div, hd]

/-- Ramanujan primitives evaluated at the complete initial observation horizon. -/
def sievePrefixRamanujanMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i e => (pmRamanujanPrimitive (e.val + 2) (i.val + 1)).re

/-- The nonconstant triangular multiples transform at level `n+1`. -/
def sieveTailMultiplesMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun e d => if e.val + 2 ∣ d.val + 2 then 1 / ((d.val + 2 : ℕ) : ℝ) else 0

/-- Exact arithmetic factorization of the prefix observation map. -/
theorem sievePrefixObservationMatrix_factorization (n : ℕ) :
    sievePrefixObservationMatrix n = sievePrefixRamanujanMatrix n * sieveTailMultiplesMatrix n := by
  ext i j
  rw [Matrix.mul_apply]
  have hd : j.val + 2 ∈ Finset.Icc 1 (n + 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have h := sievePrefix_single_response (n + 1) (i.val + 1) (j.val + 2) 1 hd
  simp only [one_mul] at h
  change (((i.val + 1) / (j.val + 2) : ℕ) : ℝ) -
    ((i.val + 1 : ℕ) : ℝ) / ((j.val + 2 : ℕ) : ℝ) = _
  rw [← h, sievePrefixDiscrepancy_eq_ramanujan_diagonal, prefix_sum_Icc_two]
  apply Finset.sum_congr rfl
  intro e _
  rw [prefix_delta_coordinate _ _ _ hd]
  rfl

/-- Exact determinant of the nonconstant multiples transform. -/
theorem sieveTailMultiplesMatrix_det (n : ℕ) :
    (sieveTailMultiplesMatrix n).det = 1 / ((n + 1).factorial : ℝ) := by
  have htri : (sieveTailMultiplesMatrix n).BlockTriangular id := by
    intro e d hde
    have hlt : d.val < e.val := hde
    unfold sieveTailMultiplesMatrix
    apply if_neg
    intro hdiv
    have hle := Nat.le_of_dvd (by omega : 0 < d.val + 2) hdiv
    omega
  rw [Matrix.det_of_upperTriangular htri]
  simp only [sieveTailMultiplesMatrix, dvd_refl, ↓reduceIte, one_div,
    Finset.prod_inv_distrib, prefix_prod_denominators]

/-- Exact nonzero determinant of the Ramanujan prefix matrix at every dimension. -/
theorem sievePrefixRamanujanMatrix_det (n : ℕ) :
    (sievePrefixRamanujanMatrix n).det = (-1 : ℝ)^n * (n.factorial : ℝ) := by
  have h := congrArg Matrix.det (sievePrefixObservationMatrix_factorization n)
  rw [sievePrefixObservationMatrix_det, Matrix.det_mul, sieveTailMultiplesMatrix_det] at h
  have hf : ((n + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n + 1)
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hdiv : (sievePrefixRamanujanMatrix n).det / ((n + 1).factorial : ℝ) =
      (-1 : ℝ)^n / ((n + 1 : ℕ) : ℝ) := by
    simpa only [one_div, div_eq_mul_inv, one_mul] using h.symm
  rw [(div_eq_iff hf).mp hdiv, Nat.factorial_succ]
  push_cast
  field_simp

/-- The variance-dual Gram kernel of the complete initial prefix observations. -/
def sievePrefixGramMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∑ e : Fin n,
    sievePrefixRamanujanMatrix n i e * sievePrefixRamanujanMatrix n j e /
      (Nat.totient (e.val + 2) : ℝ)

/-- Gram factorization with the inverse totient metric. -/
theorem sievePrefixGramMatrix_factorization (n : ℕ) :
    sievePrefixGramMatrix n =
      sievePrefixRamanujanMatrix n *
        Matrix.diagonal (fun e : Fin n => 1 / (Nat.totient (e.val + 2) : ℝ)) *
          (sievePrefixRamanujanMatrix n).transpose := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [sievePrefixGramMatrix, Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- The Gram diagonal is exactly the previously established sharp prefix dual energy. -/
theorem sievePrefixGramMatrix_diagonal (n : ℕ) (i : Fin n) :
    sievePrefixGramMatrix n i i = sievePrefixDualEnergy (n + 1) (i.val + 1) := by
  unfold sievePrefixGramMatrix sievePrefixDualEnergy
  rw [prefix_sum_Icc_two]
  apply Finset.sum_congr rfl
  intro e _
  unfold sievePrefixRamanujanMatrix
  ring

/-- Exact Gram determinant, with no hidden degeneracy at any sieve level. -/
theorem sievePrefixGramMatrix_det (n : ℕ) :
    (sievePrefixGramMatrix n).det = (n.factorial : ℝ)^2 /
      (∏ e : Fin n, (Nat.totient (e.val + 2) : ℝ)) := by
  rw [sievePrefixGramMatrix_factorization, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, Matrix.det_transpose, sievePrefixRamanujanMatrix_det]
  have hv : (∏ e : Fin n, 1 / (Nat.totient (e.val + 2) : ℝ)) =
      1 / (∏ e : Fin n, (Nat.totient (e.val + 2) : ℝ)) := by
    simp
  have hs : (-1 : ℝ)^n * (-1 : ℝ)^n = 1 := by rw [← mul_pow]; simp
  rw [hv]
  calc
    _ = ((-1 : ℝ)^n * (-1 : ℝ)^n) * (n.factorial : ℝ)^2 /
        (∏ e : Fin n, (Nat.totient (e.val + 2) : ℝ)) := by ring
    _ = _ := by rw [hs, one_mul]

private theorem prefix_index_totient_pos {n : ℕ} (e : Fin n) :
    0 < (Nat.totient (e.val + 2) : ℝ) := by
  exact_mod_cast Nat.totient_pos.mpr (show 0 < e.val + 2 by omega)

/-- Strict positivity of the exact determinant, including the empty Gram matrix. -/
theorem sievePrefixGramMatrix_det_pos (n : ℕ) : 0 < (sievePrefixGramMatrix n).det := by
  rw [sievePrefixGramMatrix_det]
  apply div_pos
  · exact pow_pos (by exact_mod_cast Nat.factorial_pos n) 2
  · exact Finset.prod_pos fun e _ => prefix_index_totient_pos e

/-- Initial prefix observations carry a positive definite variance-dual metric. -/
theorem sievePrefixGramMatrix_posDef (n : ℕ) : (sievePrefixGramMatrix n).PosDef := by
  have hR : IsUnit (sievePrefixRamanujanMatrix n) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, sievePrefixRamanujanMatrix_det]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (by exact_mod_cast Nat.factorial_ne_zero n)
  have hD : (Matrix.diagonal (fun e : Fin n => 1 / (Nat.totient (e.val + 2) : ℝ))).PosDef :=
    Matrix.posDef_diagonal_iff.mpr fun e => one_div_pos.mpr (prefix_index_totient_pos e)
  rw [sievePrefixGramMatrix_factorization]
  have h := (Matrix.IsUnit.posDef_star_right_conjugate_iff hR).mpr hD
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using h

end
end GaloisForLFunctions.BezoutValuationIncidence
