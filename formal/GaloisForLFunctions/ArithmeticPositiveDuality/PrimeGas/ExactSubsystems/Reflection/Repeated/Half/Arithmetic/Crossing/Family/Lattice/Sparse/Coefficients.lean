import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Clearing

/-! # Thermal polynomial coefficients and occupation multiplicities -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Sparse

open Finset Real Polynomial

variable {I : Type*} [Fintype I]

/-- Number of states with the indicated occupation, before centering. -/
def multiplicity (k : I → ℕ) (m : ℕ) := (univ.filter (fun i => k i=m)).card

theorem simple_multiplicity {k : I → ℕ} (inj : Function.Injective k) (m : ℕ) :
    multiplicity k m ≤ 1 := by
  apply card_le_one.mpr
  intro i hi j hj
  exact inj ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)

private theorem fiber_bound {k g : I → ℕ} {M : ℕ} (cap : ∀ m, multiplicity k m ≤ M)
    (separates : ∀ i j, g i=g j → k i=k j) (e : ℕ) :
    (univ.filter (fun i => e=g i)).card ≤ M := by
  by_cases ex : ∃ i, e=g i
  · obtain ⟨j,hj⟩ := ex
    apply le_trans _ (cap (k j))
    apply card_le_card
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _,separates i j ((mem_filter.mp hi).2.symm.trans hj)⟩
  · have empty : univ.filter (fun i => e=g i)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact ex ⟨i,(mem_filter.mp hi).2⟩
    rw [empty,card_empty]
    exact Nat.zero_le _

/-- Each coefficient is a difference of two level multiplicities. -/
theorem coefficient_bound (k : I → ℕ) {M : ℕ} (cap : ∀ m, multiplicity k m ≤ M) (e : ℕ) :
    ((imbalancePolynomial k).coeff e).natAbs ≤ M := by
  classical
  rcases isEmpty_or_nonempty I with he | hn
  · letI := he
    simp [imbalancePolynomial]
  · letI := hn
    let n := Fintype.card I
    let m := ∑ i, k i
    let a (i : I) := n*(m+k i)
    let b (i : I) := n*(m-k i)+2*m
    have np : 0 < n := Fintype.card_pos
    have top (i : I) : k i ≤ m :=
      single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (mem_univ i)
    have A := fiber_bound cap (g := a) (fun i j eq => by
      have h := Nat.eq_of_mul_eq_mul_left np eq
      exact Nat.add_left_cancel h) e
    have B := fiber_bound cap (g := b) (fun i j eq => by
      have h : n*(m-k i)=n*(m-k j) := Nat.add_right_cancel eq
      have diff := Nat.eq_of_mul_eq_mul_left np h
      have := top i
      have := top j
      omega) e
    have coeff : (imbalancePolynomial k).coeff e =
        (((univ.filter (fun i => e=a i)).card : ℕ) : ℤ) -
          (((univ.filter (fun i => e=b i)).card : ℕ) : ℤ) := by
      simp only [imbalancePolynomial,finsetSum_coeff,coeff_sub,coeff_X_pow,sum_sub_distrib,sum_boole,a,b,m,n]
    rw [coeff]
    omega

/-- Both reciprocal exponential coordinates become integral after multiplication
by the same nonzero leading coefficient. -/
theorem scaled_integral (k : I → ℕ) {t : ℝ} (hit : agrees (fun i => (k i : ℝ)) t) :
    let c := (imbalancePolynomial k).leadingCoeff
    IsIntegral ℤ ((c : ℝ)*exp (t/Fintype.card I)) ∧
      IsIntegral ℤ ((c : ℝ)*exp (-(t/Fintype.card I))) := by
  rcases isEmpty_or_nonempty I with he | hn
  · letI := he
    simp [imbalancePolynomial]
    simpa only [Nat.cast_zero] using (isIntegral_natCast (B := ℝ) 0)
  · letI := hn
    have neg : agrees (fun i => (k i : ℝ)) (-t) := by
      simpa only [agrees,neg_neg] using hit.symm
    have posRoot := (imbalancePolynomial_root k t).mpr hit
    have negRoot := (imbalancePolynomial_root k (-t)).mpr neg
    constructor
    · simpa only [zsmul_eq_mul] using isIntegral_leadingCoeff_smul _ _ posRoot
    · simpa only [zsmul_eq_mul,neg_div] using isIntegral_leadingCoeff_smul _ _ negRoot

/-- For distinct occupations a nonreflecting blind spectrum gives an algebraic
unit, even when the mean occupation is fractional. -/
theorem unit_coordinates (k : I → ℕ) (inj : Function.Injective k) {t : ℝ}
    (asym : ¬Reflects (fun i => (k i : ℝ))) (hit : agrees (fun i => (k i : ℝ)) t) :
    IsIntegral ℤ (exp (t/Fintype.card I)) ∧ IsIntegral ℤ (exp (t/Fintype.card I))⁻¹ := by
  let c := (imbalancePolynomial k).leadingCoeff
  have small : c.natAbs ≤ 1 := coefficient_bound k (simple_multiplicity inj) _
  have nz : c ≠ 0 := leadingCoeff_ne_zero.mpr (imbalancePolynomial_ne_zero asym)
  have h := scaled_integral k hit
  change IsIntegral ℤ ((c : ℝ)*_) ∧ IsIntegral ℤ ((c : ℝ)*_) at h
  rw [exp_neg] at h
  rcases (show c=1 ∨ c= -1 by omega) with eq | eq
  · simpa only [eq,Int.cast_one,one_mul] using h
  · simp only [eq,Int.cast_neg,Int.cast_one,neg_one_mul] at h
    exact ⟨by simpa only [neg_neg] using h.1.neg,by simpa only [neg_neg] using h.2.neg⟩

#print axioms coefficient_bound
#print axioms scaled_integral
#print axioms unit_coordinates

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Sparse
