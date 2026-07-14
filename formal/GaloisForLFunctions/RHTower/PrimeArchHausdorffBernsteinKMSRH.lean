import GaloisForLFunctions.RHTower.PrimeArchFiniteKMSLocalMomentClosure
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.RingTheory.Polynomial.Bernstein

open scoped BigOperators Polynomial
open Polynomial

namespace RHTower

noncomputable section

open MvPolynomial hiding X

theorem mul_descFactorial_eq (n j : ℕ) :
    n * n.descFactorial j =
      n.descFactorial (j + 1) + j * n.descFactorial j := by
  by_cases h : j ≤ n
  · rw [Nat.descFactorial_succ]
    nth_rewrite 1 [show n = (n - j) + j by omega]
    ring
  · have hnj : n < j := Nat.lt_of_not_ge h
    have hz : n.descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr hnj
    simp [hz]

theorem pow_eq_sum_stirlingSecond_descFactorial (n p : ℕ) :
    n ^ p = ∑ j ∈ Finset.range (p + 1),
      Nat.stirlingSecond p j * n.descFactorial j := by
  induction p with
  | zero => simp
  | succ p ih =>
      have hshift :
          (∑ k ∈ Finset.range (p + 1),
              (k + 1) * Nat.stirlingSecond p (k + 1) *
                n.descFactorial (k + 1)) =
            ∑ k ∈ Finset.range (p + 1),
              k * Nat.stirlingSecond p k * n.descFactorial k := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ']
        simp only [Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self p), mul_zero,
          zero_mul, add_zero]
      rw [pow_succ, ih, Finset.sum_mul]
      conv_lhs =>
        enter [2, k]
        rw [show Nat.stirlingSecond p k * n.descFactorial k * n =
            Nat.stirlingSecond p k * (n * n.descFactorial k) by ring,
          mul_descFactorial_eq]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      conv_rhs => rw [Finset.sum_range_succ']
      simp only [Nat.stirlingSecond_succ_succ, Nat.stirlingSecond_succ_zero,
        zero_mul, add_zero]
      have hsplit :
          (∑ k ∈ Finset.range (p + 1),
              ((k + 1) * Nat.stirlingSecond p (k + 1) +
                Nat.stirlingSecond p k) * n.descFactorial (k + 1)) =
            (∑ k ∈ Finset.range (p + 1),
              (k + 1) * Nat.stirlingSecond p (k + 1) *
                n.descFactorial (k + 1)) +
            ∑ k ∈ Finset.range (p + 1),
              Nat.stirlingSecond p k * n.descFactorial (k + 1) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      rw [hsplit]
      have hC :
          (∑ k ∈ Finset.range (p + 1),
              Nat.stirlingSecond p k * (k * n.descFactorial k)) =
            ∑ k ∈ Finset.range (p + 1),
              k * Nat.stirlingSecond p k * n.descFactorial k := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      rw [hC]
      rw [← hshift]
      apply add_comm

theorem iterate_pderiv_add_pow (N j : ℕ) :
    (pderiv true)^[j]
        ((MvPolynomial.X true + MvPolynomial.X false : MvPolynomial Bool ℝ) ^ N) =
      N.descFactorial j •
        (MvPolynomial.X true + MvPolynomial.X false : MvPolynomial Bool ℝ) ^ (N - j) := by
  have hx : pderiv true (MvPolynomial.X true : MvPolynomial Bool ℝ) = 1 := by
    rw [MvPolynomial.pderiv_X]
    rfl
  have hy : pderiv true (MvPolynomial.X false : MvPolynomial Bool ℝ) = 0 := by
    rw [MvPolynomial.pderiv_X]
    rfl
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      by_cases h : j < N
      · have hsub : N - (j + 1) = N - j - 1 := by omega
        rw [Nat.descFactorial_succ, hsub]
        simp only [(pderiv true).leibniz, (pderiv true).leibniz_pow,
          (pderiv true).map_add,
          hx, hy, add_zero, mul_one, nsmul_eq_mul, smul_eq_mul,
          Derivation.map_natCast]
        push_cast
        ring
      · have hNj : N ≤ j := Nat.le_of_not_gt h
        obtain rfl | hNj := hNj.eq_or_lt
        · simp [Nat.descFactorial_succ]
        · have hzero : N.descFactorial j = 0 :=
            Nat.descFactorial_eq_zero_iff_lt.mpr hNj
          simp [hzero]

theorem iterate_pderiv_X_pow_mul (N k j : ℕ) :
    (pderiv true)^[j]
        ((MvPolynomial.X true : MvPolynomial Bool ℝ) ^ k *
          (MvPolynomial.X false) ^ (N - k)) =
      k.descFactorial j •
        ((MvPolynomial.X true : MvPolynomial Bool ℝ) ^ (k - j) *
          (MvPolynomial.X false) ^ (N - k)) := by
  have hx : pderiv true (MvPolynomial.X true : MvPolynomial Bool ℝ) = 1 := by
    rw [MvPolynomial.pderiv_X]
    rfl
  have hy : pderiv true (MvPolynomial.X false : MvPolynomial Bool ℝ) = 0 := by
    rw [MvPolynomial.pderiv_X]
    rfl
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      by_cases h : j < k
      · have hsub : k - (j + 1) = k - j - 1 := by omega
        rw [Nat.descFactorial_succ, hsub]
        simp only [(pderiv true).leibniz, (pderiv true).leibniz_pow,
          hx, hy, mul_zero, add_zero, nsmul_eq_mul, smul_eq_mul,
          mul_one, Derivation.map_natCast]
        push_cast
        ring
      · have hkj : k ≤ j := Nat.le_of_not_gt h
        obtain rfl | hkj := hkj.eq_or_lt
        · simp [Nat.descFactorial_succ]
        · have hzero : k.descFactorial j = 0 :=
            Nat.descFactorial_eq_zero_iff_lt.mpr hkj
          simp [hzero]

theorem iterate_pderiv_nsmul (c j : ℕ) (z : MvPolynomial Bool ℝ) :
    (pderiv true)^[j] (c • z) = c • (pderiv true)^[j] z := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih, map_nsmul,
        Function.iterate_succ_apply']

theorem sum_descFactorial_smul_bernstein (N j : ℕ) :
    (∑ k ∈ Finset.range (N + 1),
        k.descFactorial j • bernsteinPolynomial ℝ N k) =
      N.descFactorial j • (Polynomial.X : Polynomial ℝ) ^ j := by
  let x : MvPolynomial Bool ℝ := MvPolynomial.X true
  let y : MvPolynomial Bool ℝ := MvPolynomial.X false
  let e : Bool → Polynomial ℝ := fun i => cond i Polynomial.X (1 - Polynomial.X)
  have hterm : ∀ k : ℕ,
      k.descFactorial j • bernsteinPolynomial ℝ N k =
        MvPolynomial.aeval e
            (N.choose k • (pderiv true)^[j] (x ^ k * y ^ (N - k))) *
          Polynomial.X ^ j := by
    intro k
    rw [iterate_pderiv_X_pow_mul]
    by_cases h : j ≤ k
    · simp only [e, bernsteinPolynomial, map_mul, map_pow,
        map_natCast,
        MvPolynomial.aeval_X, Bool.cond_true, Bool.cond_false, nsmul_eq_mul]
      have hxpow :
          (Polynomial.X : Polynomial ℝ) ^ (k - j) * Polynomial.X ^ j =
            Polynomial.X ^ k := by
        rw [← pow_add, Nat.sub_add_cancel h]
      calc
        _ = (N.choose k : Polynomial ℝ) * (k.descFactorial j : Polynomial ℝ) *
              (Polynomial.X ^ k * (1 - Polynomial.X) ^ (N - k)) := by
          ring
        _ = (N.choose k : Polynomial ℝ) * (k.descFactorial j : Polynomial ℝ) *
              ((Polynomial.X ^ (k - j) * Polynomial.X ^ j) *
                (1 - Polynomial.X) ^ (N - k)) := by
          rw [hxpow]
        _ = _ := by ring
    · have hjk : k < j := Nat.lt_of_not_ge h
      have hz : k.descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr hjk
      simp [hz]
  have hmap_sum :
      (pderiv true)^[j]
          (∑ k ∈ Finset.range (N + 1), N.choose k • (x ^ k * y ^ (N - k))) =
        ∑ k ∈ Finset.range (N + 1),
          (pderiv true)^[j] (N.choose k • (x ^ k * y ^ (N - k))) := by
    clear hterm
    induction j with
    | zero => simp
    | succ j ih =>
        rw [Function.iterate_succ_apply', ih, map_sum (pderiv true)]
        apply Finset.sum_congr rfl
        intro k hk
        rw [Function.iterate_succ_apply']
  have hadd :
      (x + y) ^ N =
        ∑ k ∈ Finset.range (N + 1), N.choose k • (x ^ k * y ^ (N - k)) := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [nsmul_eq_mul]
    ring
  calc
    (∑ k ∈ Finset.range (N + 1),
        k.descFactorial j • bernsteinPolynomial ℝ N k) =
        ∑ k ∈ Finset.range (N + 1),
          MvPolynomial.aeval e
              (N.choose k • (pderiv true)^[j] (x ^ k * y ^ (N - k))) *
            Polynomial.X ^ j := by
      exact Finset.sum_congr rfl fun k _ => hterm k
    _ = MvPolynomial.aeval e
          ((pderiv true)^[j]
            ((x + y) ^ N)) * Polynomial.X ^ j := by
      rw [hadd, hmap_sum]
      simp only [map_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [iterate_pderiv_nsmul, map_nsmul]
    _ = N.descFactorial j • (Polynomial.X : Polynomial ℝ) ^ j := by
      rw [iterate_pderiv_add_pow]
      simp [e]

open HTGeometry

/-- All Bernstein basis values of the moment functional are nonnegative. -/
def HausdorffBernsteinNonnegative (m : ℕ → ℝ) : Prop :=
  ∀ N k : ℕ, 0 ≤ momentFunctional m (bernsteinPolynomial ℝ N k)

/-- The canonical degree-`N+1` Bernstein atomic approximation. -/
def hausdorffBernsteinAtomicMoment (m : ℕ → ℝ) (N n : ℕ) : ℝ :=
  ∑ i : Fin (N + 2),
    momentFunctional m (bernsteinPolynomial ℝ (N + 1) i) *
      (((i : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ)) ^ n

theorem finitePositiveAtomicMomentSequence_hausdorffBernsteinAtomicMoment
    {m : ℕ → ℝ} (h : HausdorffBernsteinNonnegative m) (N : ℕ) :
    FinitePositiveAtomicMomentSequence (hausdorffBernsteinAtomicMoment m N) := by
  let mass : Fin (N + 2) → ℝ := fun i =>
    momentFunctional m (bernsteinPolynomial ℝ (N + 1) i)
  let node : Fin (N + 2) → ℝ := fun i =>
    ((i : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ)
  refine ⟨N + 2, mass, node, ?_, ?_, ?_⟩
  · intro i
    exact h (N + 1) i
  · intro i
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · rfl

theorem hausdorffBernstein_factorialMoment (m : ℕ → ℝ) (M j : ℕ) :
    (∑ i : Fin (M + 1),
        ((i : ℕ).descFactorial j : ℝ) *
          momentFunctional m (bernsteinPolynomial ℝ M i)) =
      (M.descFactorial j : ℝ) * m j := by
  let f : ℕ → ℝ := fun i =>
    (i.descFactorial j : ℝ) *
      momentFunctional m (bernsteinPolynomial ℝ M i)
  change (∑ i : Fin (M + 1), f i) = _
  rw [Fin.sum_univ_eq_sum_range f (M + 1)]
  have hpoly := sum_descFactorial_smul_bernstein M j
  have hfun := congrArg (momentFunctional m) hpoly
  have hscale (c : ℕ) (p : Polynomial ℝ) :
      momentFunctional m ((c : Polynomial ℝ) * p) =
        (c : ℝ) * momentFunctional m p := by
    rw [show (c : Polynomial ℝ) * p = (c : ℝ) • p by
      simp [Polynomial.smul_eq_C_mul]]
    exact momentFunctional_smul m (c : ℝ) p
  simpa only [momentFunctional_sum, nsmul_eq_mul, hscale,
    momentFunctional_X_pow, f] using hfun

theorem hausdorffBernsteinAtomicMoment_eq_stirling
    (m : ℕ → ℝ) (N n : ℕ) :
    hausdorffBernsteinAtomicMoment m N n =
      ∑ j ∈ Finset.range (n + 1),
        (Nat.stirlingSecond n j : ℝ) *
          (((N + 1).descFactorial j : ℝ) /
            (((N + 1 : ℕ) : ℝ) ^ n)) * m j := by
  let mass : Fin (N + 2) → ℝ := fun i =>
    momentFunctional m (bernsteinPolynomial ℝ (N + 1) i)
  have hpow (i : Fin (N + 2)) :
      (((i : ℕ) : ℝ) ^ n) =
        ∑ j ∈ Finset.range (n + 1),
          (Nat.stirlingSecond n j : ℝ) * ((i : ℕ).descFactorial j : ℝ) := by
    exact_mod_cast pow_eq_sum_stirlingSecond_descFactorial (i : ℕ) n
  rw [hausdorffBernsteinAtomicMoment]
  change (∑ i : Fin (N + 2),
    mass i * ((((i : ℕ) : ℝ) / (((N + 1 : ℕ) : ℝ))) ^ n) = _)
  simp_rw [div_pow, hpow]
  calc
    (∑ i : Fin (N + 2),
        mass i *
          ((∑ j ∈ Finset.range (n + 1),
              (Nat.stirlingSecond n j : ℝ) *
                ((i : ℕ).descFactorial j : ℝ)) /
            (((N + 1 : ℕ) : ℝ) ^ n))) =
        ∑ i : Fin (N + 2), ∑ j ∈ Finset.range (n + 1),
          (Nat.stirlingSecond n j : ℝ) /
              (((N + 1 : ℕ) : ℝ) ^ n) *
            (((i : ℕ).descFactorial j : ℝ) * mass i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_div, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ j ∈ Finset.range (n + 1),
          (Nat.stirlingSecond n j : ℝ) /
              (((N + 1 : ℕ) : ℝ) ^ n) *
            (∑ i : Fin (N + 2),
              ((i : ℕ).descFactorial j : ℝ) * mass i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hausdorffBernstein_factorialMoment m (N + 1) j]
      ring

open Asymptotics Filter Topology

theorem tendsto_descFactorial_self_div_pow (j : ℕ) :
    Tendsto
        (fun N : ℕ =>
          (((N + 1).descFactorial j : ℝ) /
            (((N + 1 : ℕ) : ℝ) ^ j)))
        atTop (𝓝 1) := by
  have hz : ∀ᶠ N : ℕ in atTop, ((N : ℝ) ^ j) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact pow_ne_zero j (by positivity)
  have h :=
    (isEquivalent_iff_tendsto_one hz).mp (isEquivalent_descFactorial j)
  change Tendsto
    (fun N : ℕ => (N.descFactorial j : ℝ) / ((N : ℝ) ^ j))
    atTop (𝓝 1) at h
  have hadd : Tendsto (fun N : ℕ => N + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  exact h.comp hadd

theorem tendsto_descFactorial_div_higher_pow {j n : ℕ} (hjn : j < n) :
    Tendsto
        (fun N : ℕ =>
          (((N + 1).descFactorial j : ℝ) /
            (((N + 1 : ℕ) : ℝ) ^ n)))
        atTop (𝓝 0) := by
  have hcast : Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hpows : Tendsto
      (fun N : ℕ =>
        ((((N + 1 : ℕ) : ℝ) ^ j) / (((N + 1 : ℕ) : ℝ) ^ n)))
      atTop (𝓝 0) :=
    (tendsto_pow_div_pow_atTop_zero hjn).comp hcast
  have hprod := (tendsto_descFactorial_self_div_pow j).mul hpows
  have heq :
      (fun N : ℕ =>
        (((N + 1).descFactorial j : ℝ) /
            (((N + 1 : ℕ) : ℝ) ^ j)) *
          ((((N + 1 : ℕ) : ℝ) ^ j) /
            (((N + 1 : ℕ) : ℝ) ^ n))) =ᶠ[atTop]
        (fun N : ℕ =>
          (((N + 1).descFactorial j : ℝ) /
            (((N + 1 : ℕ) : ℝ) ^ n))) := by
    filter_upwards with N
    have hne : (((N + 1 : ℕ) : ℝ) ^ j) ≠ 0 := by positivity
    field_simp
  simpa using hprod.congr' heq

theorem tendsto_hausdorffBernsteinAtomicMoment_coordinate
    (m : ℕ → ℝ) (n : ℕ) :
    Tendsto (fun N : ℕ => hausdorffBernsteinAtomicMoment m N n)
      atTop (𝓝 (m n)) := by
  rw [tendsto_congr' (Eventually.of_forall fun N =>
    hausdorffBernsteinAtomicMoment_eq_stirling m N n)]
  have hsum : Tendsto
      (fun N : ℕ =>
        ∑ j ∈ Finset.range (n + 1),
          (Nat.stirlingSecond n j : ℝ) *
            (((N + 1).descFactorial j : ℝ) /
              (((N + 1 : ℕ) : ℝ) ^ n)) * m j)
      atTop
      (𝓝 (∑ j ∈ Finset.range (n + 1), if j = n then m n else 0)) := by
    apply tendsto_finsetSum
    intro j hj
    have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rcases hjle.eq_or_lt with hEq | hjn
    · subst j
      simpa [Nat.stirlingSecond_self] using
        ((tendsto_descFactorial_self_div_pow n).const_mul
          (Nat.stirlingSecond n n : ℝ)).mul_const (m n)
    · have hzero := tendsto_descFactorial_div_higher_pow hjn
      simpa [Nat.ne_of_lt hjn] using
        (hzero.const_mul (Nat.stirlingSecond n j : ℝ)).mul_const (m j)
  simpa using hsum

theorem tendsto_hausdorffBernsteinAtomicMoment (m : ℕ → ℝ) :
    Tendsto (hausdorffBernsteinAtomicMoment m) atTop (𝓝 m) := by
  apply tendsto_pi_nhds.mpr
  intro n
  exact tendsto_hausdorffBernsteinAtomicMoment_coordinate m n

theorem finitePositiveAtomicLocalMomentClosure_of_hausdorffBernsteinNonnegative
    {m : ℕ → ℝ} (h : HausdorffBernsteinNonnegative m) :
    FinitePositiveAtomicLocalMomentClosure m := by
  exact finitePositiveAtomicLocalMomentClosure_of_tendsto
    (fun N => finitePositiveAtomicMomentSequence_hausdorffBernsteinAtomicMoment h N)
    (tendsto_hausdorffBernsteinAtomicMoment m)

/-- The `r`-fold complementary forward difference based at moment `k`. -/
def hausdorffMomentDifference (m : ℕ → ℝ) (k : ℕ) : ℕ → ℝ
  | 0 => m k
  | r + 1 => hausdorffMomentDifference m k r -
      hausdorffMomentDifference m (k + 1) r

/-- Every complementary finite difference of the moment sequence is nonnegative. -/
def HausdorffMomentDifferencesNonnegative (m : ℕ → ℝ) : Prop :=
  ∀ k r : ℕ, 0 ≤ hausdorffMomentDifference m k r

theorem hausdorffMomentDifference_eq_momentFunctional
    (m : ℕ → ℝ) (k r : ℕ) :
    hausdorffMomentDifference m k r =
      momentFunctional m
        ((Polynomial.X : Polynomial ℝ) ^ k * (1 - Polynomial.X) ^ r) := by
  induction r generalizing k with
  | zero =>
      simp [hausdorffMomentDifference, momentFunctional_X_pow]
  | succ r ih =>
      rw [hausdorffMomentDifference, ih k, ih (k + 1),
        ← HTGeometry.momentFunctional_sub]
      congr 1
      rw [pow_succ, pow_succ]
      ring

theorem hausdorffBernsteinNonnegative_of_momentDifferencesNonnegative
    {m : ℕ → ℝ} (h : HausdorffMomentDifferencesNonnegative m) :
    HausdorffBernsteinNonnegative m := by
  intro N k
  by_cases hk : k ≤ N
  · have hscale :
        momentFunctional m (bernsteinPolynomial ℝ N k) =
          (N.choose k : ℝ) *
            momentFunctional m
              ((Polynomial.X : Polynomial ℝ) ^ k *
                (1 - Polynomial.X) ^ (N - k)) := by
      rw [bernsteinPolynomial]
      rw [show (N.choose k : Polynomial ℝ) * Polynomial.X ^ k *
            (1 - Polynomial.X) ^ (N - k) =
          (N.choose k : ℝ) •
            (Polynomial.X ^ k * (1 - Polynomial.X) ^ (N - k)) by
        simp [Polynomial.smul_eq_C_mul]
        ring]
      exact momentFunctional_smul m (N.choose k : ℝ) _
    rw [hscale, ← hausdorffMomentDifference_eq_momentFunctional]
    exact mul_nonneg (Nat.cast_nonneg _) (h k (N - k))
  · rw [bernsteinPolynomial.eq_zero_of_lt ℝ (Nat.lt_of_not_ge hk),
      momentFunctional_zero]

theorem finitePositiveAtomicLocalMomentClosure_of_hausdorffMomentDifferencesNonnegative
    {m : ℕ → ℝ} (h : HausdorffMomentDifferencesNonnegative m) :
    FinitePositiveAtomicLocalMomentClosure m :=
  finitePositiveAtomicLocalMomentClosure_of_hausdorffBernsteinNonnegative
    (hausdorffBernsteinNonnegative_of_momentDifferencesNonnegative h)

/-- Complete Hausdorff finite-difference positivity for the normalized prime--Gamma source. -/
def PrimeArchHausdorffMomentDifferencesNonnegative : Prop :=
  HausdorffMomentDifferencesNonnegative normalizedPrimeArchMoment

/-- Complete source finite-difference positivity produces canonical finite positive atomic
systems converging to the prime--Gamma moment tower. -/
theorem primeArchFinitePositiveAtomicLocalMomentClosure_of_hausdorffMomentDifferences
    (h : PrimeArchHausdorffMomentDifferencesNonnegative) :
    PrimeArchFinitePositiveAtomicLocalMomentClosure :=
  finitePositiveAtomicLocalMomentClosure_of_hausdorffMomentDifferencesNonnegative h

/-- **Hausdorff finite-difference RH capstone.**  It is enough to prove the explicit linear
complementary finite differences of the normalized prime--Gamma moments are all nonnegative. -/
theorem riemannHypothesis_of_primeArchHausdorffMomentDifferencesNonnegative
    (h : PrimeArchHausdorffMomentDifferencesNonnegative) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeArchFinitePositiveAtomicLocalMomentClosure
    (primeArchFinitePositiveAtomicLocalMomentClosure_of_hausdorffMomentDifferences h)

open HTGeometry

/-- Every reciprocal-square thermal node lies strictly below one. -/
theorem xiThermalNode_lt_one (q : XiZeroCopy) : xiThermalNode q < 1 := by
  have hweight := xiThermalReflectionWeight_lt_one q
  rw [xiThermalReflectionWeight] at hweight
  rw [xiThermalNode, xiZeroCopyReciprocalSquare]
  rw [xiReciprocalCoordinate] at hweight
  simp only [pow_two, Complex.mul_re]
  nlinarith [sq_nonneg ((xiSpectralPoint q)⁻¹).im]

/-- The Hausdorff difference of a finite Xi thermal truncation is its positive unit-interval
atomic expansion. -/
theorem hausdorffMomentDifference_xiThermalTruncation (N k r : ℕ) :
    hausdorffMomentDifference (xiThermalTruncation N) k r =
      ∑ j ∈ Finset.range N,
        xiThermalNode (xiThermalEnumeration j) ^ (k + 1) *
          (1 - xiThermalNode (xiThermalEnumeration j)) ^ r := by
  induction r generalizing k with
  | zero =>
      simp only [hausdorffMomentDifference, pow_zero, mul_one, xiThermalTruncation]
      apply Finset.sum_congr rfl
      intro j hj
      rw [pow_succ]
      exact mul_comm _ _
  | succ r ih =>
      rw [hausdorffMomentDifference, ih k, ih (k + 1), ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [pow_succ]
      ring

/-- Every finite Xi thermal truncation has all complementary Hausdorff differences nonnegative. -/
theorem hausdorffMomentDifferencesNonnegative_xiThermalTruncation (N : ℕ) :
    HausdorffMomentDifferencesNonnegative (xiThermalTruncation N) := by
  intro k r
  rw [hausdorffMomentDifference_xiThermalTruncation]
  exact Finset.sum_nonneg fun j hj => mul_nonneg
    (pow_nonneg (xiThermalNode_pos _).le _)
    (pow_nonneg (sub_nonneg.mpr (xiThermalNode_lt_one _).le) _)

/-- Complementary Hausdorff differences are continuous under pointwise convergence of moment
sequences. -/
theorem tendsto_hausdorffMomentDifference_of_tendsto
    {m : ℕ → ℕ → ℝ} {target : ℕ → ℝ}
    (h : Tendsto m atTop (nhds target)) (k r : ℕ) :
    Tendsto (fun N => hausdorffMomentDifference (m N) k r) atTop
      (nhds (hausdorffMomentDifference target k r)) := by
  induction r generalizing k with
  | zero =>
      simpa only [hausdorffMomentDifference] using (tendsto_pi_nhds.mp h) k
  | succ r ih =>
      simpa only [hausdorffMomentDifference] using (ih k).sub (ih (k + 1))

/-- RH makes every complementary Hausdorff difference of the normalized prime--Gamma source
nonnegative. -/
theorem primeArchHausdorffMomentDifferencesNonnegative_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    PrimeArchHausdorffMomentDifferencesNonnegative := by
  intro k r
  exact le_of_tendsto_of_tendsto tendsto_const_nhds
    (tendsto_hausdorffMomentDifference_of_tendsto
      (tendsto_xiThermalTruncation_of_rh hRH) k r)
    (Eventually.of_forall fun N =>
      hausdorffMomentDifferencesNonnegative_xiThermalTruncation N k r)

/-- **Complete Hausdorff value law for RH.** -/
theorem primeArchHausdorffMomentDifferencesNonnegative_iff_riemannHypothesis :
    PrimeArchHausdorffMomentDifferencesNonnegative ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_primeArchHausdorffMomentDifferencesNonnegative,
    primeArchHausdorffMomentDifferencesNonnegative_of_riemannHypothesis⟩

/-- The exact prime--polar abscissa endpoint is equivalent to complete Hausdorff finite-difference
positivity of the normalized prime--Gamma values. -/
theorem rectangularPrimePolarSource_negativeAbscissa_le_one_iff_primeArchHausdorffMomentDifferencesNonnegative
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    LSeries.abscissaOfAbsConv
        (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
          ((1 : ℝ) : EReal) ↔
      PrimeArchHausdorffMomentDifferencesNonnegative := by
  exact
    (riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one
      hL hN).symm.trans
    primeArchHausdorffMomentDifferencesNonnegative_iff_riemannHypothesis.symm


end
end RHTower
