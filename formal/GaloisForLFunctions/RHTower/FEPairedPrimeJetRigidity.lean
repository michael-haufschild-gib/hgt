import GaloisForLFunctions.RHTower.PinnedAffinePrimeJetRigidity

/-!
# Functional-equation-paired prime-jet rigidity

A one-sided packet of `k` prime-log evaluations can imitate the origin derivation only below
degree `k`.  The first natural objection is functional-equation reflection: perhaps adjoining the
opposite nodes `± log p` turns that finite approximation into a compatible source.

This file gives the exact answer.  Antisymmetric evaluation on each reflected pair kills every even
degree, while its odd degree `2j+1` is a Vandermonde moment at the squared node `(log p)^(2 : ℕ)`.
Consequently, `k` distinct reflected prime pairs uniquely match the derivation at every degree
below `2k+1`.  The first omitted odd defect is not merely nonzero; it is exactly

`-∏ i, (-(log p_i)^(2 : ℕ))`.

Functional-equation symmetry therefore doubles the finite matching depth but does not produce a
compatible finite source.  Moreover, a packet cannot be extended by appending one pair while
retaining its old coefficients: the degree-one equation forces the appended coefficient to zero,
leaving the previous exact omitted defect unchanged.

The argument is a fixed polynomial constraint, not a cutoff, limiting process, or propagated
carrier.  It does not prove RH; it rules out the entire finite reflected-carrier repair and exposes
the remaining interface as genuinely non-finite.
-/

namespace RHTower

open Polynomial
open scoped BigOperators

noncomputable section

/-- Antisymmetric evaluation on a finite family of reflected nodes. -/
def fePairedMoment {k : ℕ} (r a : Fin k → ℂ) (n : ℕ) : ℂ :=
  ∑ i : Fin k, a i * (r i ^ n - (-r i) ^ n)

@[simp]
theorem fePairedMoment_even {k : ℕ} (r a : Fin k → ℂ) (j : ℕ) :
    fePairedMoment r a (2 * j) = 0 := by
  classical
  simp [fePairedMoment, pow_mul]

theorem fePairedMoment_odd_eq {k : ℕ} (r a : Fin k → ℂ) (j : ℕ) :
    fePairedMoment r a (2 * j + 1) =
      ∑ i : Fin k, (2 * a i * r i) * (r i ^ (2 : ℕ)) ^ j := by
  classical
  unfold fePairedMoment
  apply Finset.sum_congr rfl
  intro i _
  simp only [pow_add, pow_mul, pow_one, neg_sq]
  ring

/-- Distinct positive natural labels have distinct squared positive logarithms. -/
theorem log_sq_nat_injective {k : ℕ} (p : Fin k → ℕ)
    (hp : ∀ i, 1 < p i) (hpinj : Function.Injective p) :
    Function.Injective (fun i => (Real.log (p i) : ℂ) ^ (2 : ℕ)) := by
  intro i j hij
  have hsqR : Real.log (p i) ^ (2 : ℕ) = Real.log (p j) ^ (2 : ℕ) := by
    have h := congrArg Complex.re hij
    simpa only [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero] using h
  have hi : 0 < Real.log (p i) := Real.log_pos (by exact_mod_cast hp i)
  have hj : 0 < Real.log (p j) := Real.log_pos (by exact_mod_cast hp j)
  have hlog : Real.log (p i) = Real.log (p j) := by
    nlinarith
  apply hpinj
  exact_mod_cast Real.log_injOn_pos
    (by exact_mod_cast (Nat.zero_lt_one.trans (hp i)) : (0 : ℝ) < p i)
    (by exact_mod_cast (Nat.zero_lt_one.trans (hp j)) : (0 : ℝ) < p j) hlog

/-- A square packet of distinct reflected prime-log pairs uniquely matches the origin derivation
at the first `k` odd degrees. -/
theorem existsUnique_fePairedPrimeDerivationInterpolation {k : ℕ}
    (p : Fin k → ℕ) (hp : ∀ i, 1 < p i) (hpinj : Function.Injective p) :
    ∃! a : Fin k → ℂ, ∀ j : Fin k,
      fePairedMoment (fun i => (Real.log (p i) : ℂ)) a (2 * (j : ℕ) + 1) =
        archimedeanDerivationMoment (2 * (j : ℕ) + 1) := by
  obtain ⟨a, ha, hua⟩ := existsUnique_weightedFiniteMoments
    (fun i => (Real.log (p i) : ℂ) ^ (2 : ℕ))
    (fun i => 2 * (Real.log (p i) : ℂ))
    (log_sq_nat_injective p hp hpinj)
    (fun i => mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hp i)).ne'))
    (fun j => archimedeanDerivationMoment (2 * (j : ℕ) + 1))
  refine ⟨a, ?_, ?_⟩
  · intro j
    rw [fePairedMoment_odd_eq]
    simpa [mul_assoc, mul_comm, mul_left_comm] using ha j
  · intro b hb
    apply hua
    intro j
    have hj := hb j
    rw [fePairedMoment_odd_eq] at hj
    simpa [mul_assoc, mul_comm, mul_left_comm] using hj

/-- Moments of evaluation at the origin. -/
def originValueMoment (n : ℕ) : ℂ := if n = 0 then 1 else 0

/-- Matching all moments below `k` to evaluation at the origin makes weighted evaluation of every
degree-`< k` polynomial equal its constant coefficient. -/
theorem weighted_eval_eq_coeff_zero_of_finMoments {k : ℕ} (hk : 0 < k)
    (f a : Fin k → ℂ) (P : Polynomial ℂ) (hdeg : P.natDegree < k)
    (hmom : ∀ j : Fin k,
      (∑ i : Fin k, a i * f i ^ (j : ℕ)) = originValueMoment (j : ℕ)) :
    (∑ i : Fin k, a i * P.eval (f i)) = P.coeff 0 := by
  simp_rw [Polynomial.eval_eq_sum_range' hdeg]
  calc
    (∑ i : Fin k, a i * ∑ n ∈ Finset.range k, P.coeff n * f i ^ n) =
        ∑ n ∈ Finset.range k, P.coeff n * ∑ i : Fin k, a i * f i ^ n := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ n ∈ Finset.range k, P.coeff n * originValueMoment n := by
      apply Finset.sum_congr rfl
      intro n hn
      exact congrArg (P.coeff n * ·) (hmom ⟨n, Finset.mem_range.mp hn⟩)
    _ = P.coeff 0 := by
      rw [Finset.sum_eq_single 0]
      · simp [originValueMoment]
      · intro n _ hne
        simp [originValueMoment, hne]
      · intro hnot
        exact (hnot (Finset.mem_range.mpr hk)).elim

/-- Exact first omitted moment for a finite interpolation of evaluation at the origin. -/
theorem finiteOriginValueInterpolation_nextOrderDefect_eq {k : ℕ}
    (hk : 0 < k) (f : Fin k → ℝ) (a : Fin k → ℂ)
    (hmatch : ∀ j : Fin k,
      (∑ i : Fin k, a i * (f i : ℂ) ^ (j : ℕ)) =
        originValueMoment (j : ℕ)) :
    (∑ i : Fin k, a i * (f i : ℂ) ^ k) =
      -(((negativeNodePolynomial f).eval (0 : ℝ) : ℝ) : ℂ) := by
  classical
  let Qr : Polynomial ℝ := negativeNodePolynomial f
  let Q : Polynomial ℂ := Qr.map Complex.ofRealHom
  have hQrMonic : Qr.Monic := by
    dsimp [Qr, negativeNodePolynomial]
    exact Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hQMonic : Q.Monic := by
    dsimp [Q]
    exact hQrMonic.map Complex.ofRealHom
  have hQdeg : Q.natDegree = k := by
    dsimp [Q]
    rw [Polynomial.natDegree_map_eq_of_injective Complex.ofReal_injective]
    exact negativeNodePolynomial_natDegree f
  have hQiso : Q.IsMonicOfDegree k := ⟨hQdeg, hQMonic⟩
  let P : Polynomial ℂ := Q - X ^ k
  have hPdeg : P.natDegree < k := by
    dsimp [P]
    exact hQiso.natDegree_sub_X_pow hk.ne'
  have hweighted := weighted_eval_eq_coeff_zero_of_finMoments hk
    (fun i => (f i : ℂ)) a P hPdeg hmatch
  have hQprod : Q = ∏ i : Fin k, (X - C (f i : ℂ)) := by
    dsimp [Q, Qr, negativeNodePolynomial]
    rw [Polynomial.map_prod]
    apply Finset.prod_congr rfl
    intro i _
    simp
  have hPeval : ∀ i : Fin k, P.eval (f i : ℂ) = -(f i : ℂ) ^ k := by
    intro i
    have hroot : Q.eval (f i : ℂ) = 0 := by
      rw [hQprod]
      change (Polynomial.evalRingHom (f i : ℂ))
        (∏ j : Fin k, (X - C (f j : ℂ))) = 0
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    simp [P, hroot]
  have hleft : (∑ i : Fin k, a i * P.eval (f i : ℂ)) =
      -(∑ i : Fin k, a i * (f i : ℂ) ^ k) := by
    simp_rw [hPeval]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hPcoeff : P.coeff 0 =
      (((negativeNodePolynomial f).eval (0 : ℝ) : ℝ) : ℂ) := by
    dsimp [P]
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    have hQcoeff : Q.coeff 0 =
        (((negativeNodePolynomial f).eval (0 : ℝ) : ℝ) : ℂ) := by
      dsimp [Q, Qr]
      rw [Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero]
      rfl
    rw [hQcoeff, if_neg hk.ne'.symm, sub_zero]
  rw [hleft, hPcoeff] at hweighted
  linear_combination -hweighted

@[simp]
theorem archimedeanDerivationMoment_odd_eq_originValueMoment (j : ℕ) :
    archimedeanDerivationMoment (2 * j + 1) = originValueMoment j := by
  by_cases hj : j = 0
  · subst j
    simp [archimedeanDerivationMoment, originValueMoment]
  · have hodd : 2 * j + 1 ≠ 1 := by omega
    simp [archimedeanDerivationMoment, originValueMoment, hj]

/-- **FE-paired exact defect.** If `k` reflected prime-log pairs match the origin derivation at the
first `k` odd degrees, their first omitted odd moment is the negative constant term of the squared
log node polynomial. -/
theorem fePairedPrimeDerivationInterpolation_firstOmitted_eq {k : ℕ}
    (hk : 0 < k) (p : Fin k → ℕ) (a : Fin k → ℂ)
    (hmatch : ∀ j : Fin k,
      fePairedMoment (fun i => (Real.log (p i) : ℂ)) a (2 * (j : ℕ) + 1) =
        archimedeanDerivationMoment (2 * (j : ℕ) + 1)) :
    fePairedMoment (fun i => (Real.log (p i) : ℂ)) a (2 * k + 1) -
        archimedeanDerivationMoment (2 * k + 1) =
      -(((negativeNodePolynomial (fun i => Real.log (p i) ^ (2 : ℕ))).eval
        (0 : ℝ) : ℝ) : ℂ) := by
  have hmom : ∀ j : Fin k,
      (∑ i : Fin k,
        (2 * a i * (Real.log (p i) : ℂ)) *
          ((Real.log (p i) ^ (2 : ℕ) : ℝ) : ℂ) ^ (j : ℕ)) =
        originValueMoment (j : ℕ) := by
    intro j
    have hj := hmatch j
    rw [fePairedMoment_odd_eq] at hj
    calc
      (∑ i : Fin k,
          (2 * a i * (Real.log (p i) : ℂ)) *
            ((Real.log (p i) ^ (2 : ℕ) : ℝ) : ℂ) ^ (j : ℕ)) =
          ∑ i : Fin k,
            (2 * a i * (Real.log (p i) : ℂ)) *
              ((Real.log (p i) : ℂ) ^ (2 : ℕ)) ^ (j : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        congr 2
        norm_num
      _ = archimedeanDerivationMoment (2 * (j : ℕ) + 1) := hj
      _ = originValueMoment (j : ℕ) :=
        archimedeanDerivationMoment_odd_eq_originValueMoment (j : ℕ)
  have hdef := finiteOriginValueInterpolation_nextOrderDefect_eq hk
    (fun i => Real.log (p i) ^ (2 : ℕ))
    (fun i => 2 * a i * (Real.log (p i) : ℂ)) hmom
  rw [fePairedMoment_odd_eq]
  have htarget : archimedeanDerivationMoment (2 * k + 1) = 0 := by
    simp [archimedeanDerivationMoment]
    omega
  rw [htarget, sub_zero]
  convert hdef using 1
  all_goals norm_num

/-- The constant term of the real node polynomial is the product of the negated nodes. -/
theorem negativeNodePolynomial_eval_zero_eq_prod_neg {k : ℕ} (f : Fin k → ℝ) :
    (negativeNodePolynomial f).eval 0 = ∏ i : Fin k, -f i := by
  classical
  rw [negativeNodePolynomial]
  change (Polynomial.evalRingHom 0) (∏ i : Fin k, (X - C (f i))) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp

/-- A node polynomial with no zero node has nonzero constant term. -/
theorem negativeNodePolynomial_eval_zero_ne_zero {k : ℕ} (f : Fin k → ℝ)
    (hf : ∀ i, f i ≠ 0) : (negativeNodePolynomial f).eval 0 ≠ 0 := by
  rw [negativeNodePolynomial_eval_zero_eq_prod_neg]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact neg_ne_zero.mpr (hf i)

/-- Product form of the exact FE-paired first omitted defect. -/
theorem fePairedPrimeDerivationInterpolation_firstOmitted_eq_neg_prod {k : ℕ}
    (hk : 0 < k) (p : Fin k → ℕ) (a : Fin k → ℂ)
    (hmatch : ∀ j : Fin k,
      fePairedMoment (fun i => (Real.log (p i) : ℂ)) a (2 * (j : ℕ) + 1) =
        archimedeanDerivationMoment (2 * (j : ℕ) + 1)) :
    fePairedMoment (fun i => (Real.log (p i) : ℂ)) a (2 * k + 1) -
        archimedeanDerivationMoment (2 * k + 1) =
      -(((∏ i : Fin k, -(Real.log (p i) ^ (2 : ℕ))) : ℝ) : ℂ) := by
  rw [fePairedPrimeDerivationInterpolation_firstOmitted_eq hk p a hmatch,
    negativeNodePolynomial_eval_zero_eq_prod_neg]

/-- The first omitted odd moment of a reflected positive-prime packet cannot match the origin
derivation.  Distinctness is unnecessary for this obstruction. -/
theorem fePairedPrimeDerivationInterpolation_firstOmitted_ne {k : ℕ}
    (hk : 0 < k) (p : Fin k → ℕ) (hp : ∀ i, 1 < p i) (a : Fin k → ℂ)
    (hmatch : ∀ j : Fin k,
      fePairedMoment (fun i => (Real.log (p i) : ℂ)) a (2 * (j : ℕ) + 1) =
        archimedeanDerivationMoment (2 * (j : ℕ) + 1)) :
    fePairedMoment (fun i => (Real.log (p i) : ℂ)) a (2 * k + 1) ≠
      archimedeanDerivationMoment (2 * k + 1) := by
  intro heq
  have hdef := fePairedPrimeDerivationInterpolation_firstOmitted_eq hk p a hmatch
  rw [heq, sub_self] at hdef
  have hnode :
      (negativeNodePolynomial (fun i => Real.log (p i) ^ (2 : ℕ))).eval 0 ≠ 0 :=
    negativeNodePolynomial_eval_zero_ne_zero _ fun i =>
      pow_ne_zero 2 (Real.log_pos (by exact_mod_cast hp i)).ne'
  have hrhs :
      -(((negativeNodePolynomial (fun i => Real.log (p i) ^ (2 : ℕ))).eval
        (0 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hnode)
  exact hrhs hdef.symm

/-- Odd matching plus antisymmetry gives matching at every degree below `2k+1`: the even degrees
vanish automatically. -/
theorem fePairedMoment_matches_derivation_through_double {k : ℕ}
    (r a : Fin k → ℂ)
    (hodd : ∀ j : Fin k,
      fePairedMoment r a (2 * (j : ℕ) + 1) =
        archimedeanDerivationMoment (2 * (j : ℕ) + 1)) :
    ∀ n : ℕ, n < 2 * k + 1 →
      fePairedMoment r a n = archimedeanDerivationMoment n := by
  intro n hn
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' n
  · rw [hj, fePairedMoment_even]
    simp [archimedeanDerivationMoment]
  · rw [hj]
    have hjk : j < k := by omega
    exact hodd ⟨j, hjk⟩

/-- **FE symmetry doubles finite matching depth.** Any fixed square packet of distinct positive
prime-log pairs uniquely matches the origin derivation at every degree below `2k+1`. -/
theorem existsUnique_fePairedPrimeDerivationInterpolation_through_double {k : ℕ}
    (p : Fin k → ℕ) (hp : ∀ i, 1 < p i) (hpinj : Function.Injective p) :
    ∃! a : Fin k → ℂ, ∀ n : ℕ, n < 2 * k + 1 →
      fePairedMoment (fun i => (Real.log (p i) : ℂ)) a n =
        archimedeanDerivationMoment n := by
  obtain ⟨a, ha, hua⟩ :=
    existsUnique_fePairedPrimeDerivationInterpolation p hp hpinj
  refine ⟨a, fePairedMoment_matches_derivation_through_double _ _ ha, ?_⟩
  intro b hb
  apply hua
  intro j
  exact hb (2 * (j : ℕ) + 1) (by omega)

/-- Complete finite FE-paired boundary: a unique packet matches through degree `2k`, its first
omitted odd defect is the explicit nonzero squared-log product. -/
theorem existsUnique_fePairedPrimeDerivationInterpolation_with_firstOmittedDefect {k : ℕ}
    (hk : 0 < k) (p : Fin k → ℕ) (hp : ∀ i, 1 < p i)
    (hpinj : Function.Injective p) :
    ∃! a : Fin k → ℂ,
      (∀ n : ℕ, n < 2 * k + 1 →
        fePairedMoment (fun i => (Real.log (p i) : ℂ)) a n =
          archimedeanDerivationMoment n) ∧
      fePairedMoment (fun i => (Real.log (p i) : ℂ)) a (2 * k + 1) -
          archimedeanDerivationMoment (2 * k + 1) =
        -(((∏ i : Fin k, -(Real.log (p i) ^ (2 : ℕ))) : ℝ) : ℂ) ∧
      fePairedMoment (fun i => (Real.log (p i) : ℂ)) a (2 * k + 1) ≠
        archimedeanDerivationMoment (2 * k + 1) := by
  obtain ⟨a, ha, hua⟩ :=
    existsUnique_fePairedPrimeDerivationInterpolation p hp hpinj
  have hthrough := fePairedMoment_matches_derivation_through_double _ _ ha
  refine ⟨a, ⟨hthrough,
    fePairedPrimeDerivationInterpolation_firstOmitted_eq_neg_prod hk p a ha,
    fePairedPrimeDerivationInterpolation_firstOmitted_ne hk p hp a ha⟩, ?_⟩
  intro b hb
  apply hua
  intro j
  exact hb.1 (2 * (j : ℕ) + 1) (by omega)

/-- **No coefficient-preserving FE-paired support extension.** Appending one reflected prime pair
cannot add two further matched degrees while retaining all old coefficients.  Degree one forces the
new coefficient to zero, so the old exact omitted odd defect survives. -/
theorem no_fePairedPrimeDerivationInterpolation_coefficientPreserving_extension {k : ℕ}
    (hk : 0 < k) (p : Fin (k + 1) → ℕ) (hp : ∀ i, 1 < p i)
    (a : Fin k → ℂ) (b : Fin (k + 1) → ℂ)
    (ha : ∀ j : Fin k,
      fePairedMoment (fun i => (Real.log (p i.castSucc) : ℂ)) a
          (2 * (j : ℕ) + 1) =
        archimedeanDerivationMoment (2 * (j : ℕ) + 1))
    (hb : ∀ j : Fin (k + 1),
      fePairedMoment (fun i => (Real.log (p i) : ℂ)) b
          (2 * (j : ℕ) + 1) =
        archimedeanDerivationMoment (2 * (j : ℕ) + 1))
    (hrestrict : ∀ i : Fin k, b i.castSucc = a i) : False := by
  have ha0 := ha ⟨0, hk⟩
  have hb0 := hb ⟨0, Nat.zero_lt_succ k⟩
  rw [fePairedMoment_odd_eq] at ha0 hb0
  simp only [mul_zero, zero_add, pow_zero, mul_one] at ha0 hb0
  rw [Fin.sum_univ_castSucc] at hb0
  have hold :
      (∑ i : Fin k, 2 * b i.castSucc * (Real.log (p i.castSucc) : ℂ)) =
        ∑ i : Fin k, 2 * a i * (Real.log (p i.castSucc) : ℂ) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hrestrict]
  rw [hold, ha0] at hb0
  have hblastTerm :
      2 * b (Fin.last k) * (Real.log (p (Fin.last k)) : ℂ) = 0 := by
    linear_combination hb0
  have hloglast : (Real.log (p (Fin.last k)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hp (Fin.last k))).ne'
  have htwoB : 2 * b (Fin.last k) = 0 :=
    (mul_eq_zero.mp hblastTerm).resolve_right hloglast
  have hblast : b (Fin.last k) = 0 :=
    (mul_eq_zero.mp htwoB).resolve_left (by norm_num)
  have hbk := hb (Fin.last k)
  rw [fePairedMoment_odd_eq, Fin.sum_univ_castSucc] at hbk
  simp only [Fin.val_last] at hbk
  have holdk :
      (∑ i : Fin k,
        (2 * b i.castSucc * (Real.log (p i.castSucc) : ℂ)) *
          ((Real.log (p i.castSucc) : ℂ) ^ (2 : ℕ)) ^ k) =
        ∑ i : Fin k,
          (2 * a i * (Real.log (p i.castSucc) : ℂ)) *
            ((Real.log (p i.castSucc) : ℂ) ^ (2 : ℕ)) ^ k := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hrestrict]
  rw [holdk] at hbk
  simp only [hblast, mul_zero, zero_mul, add_zero] at hbk
  have hkEq :
      fePairedMoment (fun i => (Real.log (p i.castSucc) : ℂ)) a (2 * k + 1) =
        archimedeanDerivationMoment (2 * k + 1) := by
    rw [fePairedMoment_odd_eq]
    exact hbk
  exact fePairedPrimeDerivationInterpolation_firstOmitted_ne hk
    (fun i => p i.castSucc) (fun i => hp i.castSucc) a ha hkEq

end

end RHTower

