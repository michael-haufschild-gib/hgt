import GaloisForLFunctions.HTGeometry.RealExponentialPolynomial

/-!
# Polynomially weighted exponential independence

Baker's general logarithm theorem ends with an exponential polynomial whose additive frequencies
are distinct, although their exponentials can collide.  This file proves that a nonzero family of
polynomial coefficients gives a nonzero entire exponential polynomial.  The proof uses the
frequency-killing operator `D - ν`; it never samples the functions at the natural numbers.
-/

open scoped Classical
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

/-- The constant-coefficient differential operator `D - ν`. -/
noncomputable def expKill (ν : ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => deriv f z - ν * f z

/-- On a polynomial exponential of frequency `μ`, `D - ν` acts on the polynomial coefficient by
`P ↦ P' + (μ - ν)P`. -/
theorem expKill_polyExpC (ν μ : ℂ) (P : Polynomial ℂ) :
    expKill ν (polyExpC P μ) = polyExpC (expShiftPoly (μ - ν) P) μ := by
  funext z
  rw [expKill, deriv_polyExpC]
  simp only [polyExpC, expShiftPoly, Polynomial.eval_add, Polynomial.eval_smul,
    smul_eq_mul]
  ring

/-- Iterating `D - ν` iterates the corresponding shifted polynomial derivative. -/
theorem expKill_iterate_polyExpC (ν μ : ℂ) (P : Polynomial ℂ) (r : ℕ) :
    (expKill ν)^[r] (polyExpC P μ) =
      polyExpC ((expShiftPoly (μ - ν))^[r] P) μ := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [Function.iterate_succ_apply', ih]
      calc
        expKill ν (polyExpC ((expShiftPoly (μ - ν))^[r] P) μ) =
            polyExpC (expShiftPoly (μ - ν) ((expShiftPoly (μ - ν))^[r] P)) μ :=
          expKill_polyExpC ν μ _
        _ = polyExpC ((expShiftPoly (μ - ν))^[r + 1] P) μ := by
          rw [Function.iterate_succ_apply']

/-- If the scalar part is nonzero, `P ↦ P' + μP` cannot kill a nonzero polynomial.  Its top
coefficient is `μ` times the old top coefficient. -/
theorem expShiftPoly_ne_zero (μ : ℂ) (hμ : μ ≠ 0) (P : Polynomial ℂ) (hP : P ≠ 0) :
    expShiftPoly μ P ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun Q : Polynomial ℂ => Q.coeff P.natDegree) hzero
  have hhigh : P.coeff (P.natDegree + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)
  simp only [expShiftPoly, Polynomial.coeff_add, Polynomial.coeff_derivative,
    Polynomial.coeff_smul, hhigh, zero_mul, zero_add, Polynomial.coeff_natDegree,
    smul_eq_mul] at hcoeff
  exact (mul_ne_zero hμ (Polynomial.leadingCoeff_ne_zero.mpr hP)) hcoeff

theorem expShiftPoly_eq_zero_iff (μ : ℂ) (hμ : μ ≠ 0) (P : Polynomial ℂ) :
    expShiftPoly μ P = 0 ↔ P = 0 := by
  constructor
  · contrapose!
    exact expShiftPoly_ne_zero μ hμ P
  · rintro rfl
    simp [expShiftPoly]

/-- Every iterate of `P ↦ P' + μP` is injective when `μ ≠ 0`. -/
theorem expShiftPoly_iterate_eq_zero_iff (μ : ℂ) (hμ : μ ≠ 0)
    (P : Polynomial ℂ) (r : ℕ) :
    (expShiftPoly μ)^[r] P = 0 ↔ P = 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply', expShiftPoly_eq_zero_iff μ hμ, ih]

/-- The frequency-killing operator distributes through a finite exponential-polynomial sum. -/
theorem expKill_iterate_finset {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (ν : ℂ) (μ : ι → ℂ) (P : ι → Polynomial ℂ) (r : ℕ) :
    (expKill ν)^[r] (fun z => ∑ i ∈ s, polyExpC (P i) (μ i) z) =
      fun z => ∑ i ∈ s,
        polyExpC ((expShiftPoly (μ i - ν))^[r] (P i)) (μ i) z := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [Function.iterate_succ_apply', ih]
      funext z
      rw [expKill, deriv_fun_sum]
      · simp only [Finset.mul_sum]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [show deriv (polyExpC ((expShiftPoly (μ i - ν))^[r] (P i)) (μ i)) z -
              ν * polyExpC ((expShiftPoly (μ i - ν))^[r] (P i)) (μ i) z =
            expKill ν (polyExpC ((expShiftPoly (μ i - ν))^[r] (P i)) (μ i)) z by rfl]
        rw [congrFun (expKill_polyExpC ν (μ i) _) z]
        rw [Function.iterate_succ_apply']
      · intro i hi
        exact differentiable_polyExpC _ _ z

/-- A finite sum of polynomially weighted exponentials with distinct frequencies is the zero
function only when every polynomial coefficient is zero. -/
theorem expPoly_finset_eq_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (μ : ι → ℂ) (P : ι → Polynomial ℂ)
    (hμ : Set.InjOn μ s)
    (hsum : (fun z => ∑ i ∈ s, polyExpC (P i) (μ i) z) = 0) :
    ∀ i ∈ s, P i = 0 := by
  induction s using Finset.induction_on generalizing P with
  | empty => simp
  | @insert a s ha ih =>
      have hμs : Set.InjOn μ s := hμ.mono (Finset.subset_insert a s)
      let r := (P a).natDegree + 1
      have hrzero : (expShiftPoly (μ a - μ a))^[r] (P a) = 0 := by
        have hzeroShift : expShiftPoly (μ a - μ a) = Polynomial.derivative := by
          funext Q
          simp [expShiftPoly]
        rw [hzeroShift]
        exact Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_self _)
      have hop :
          (fun z => ∑ i ∈ insert a s,
            polyExpC ((expShiftPoly (μ i - μ a))^[r] (P i)) (μ i) z) = 0 := by
        calc
          _ = (expKill (μ a))^[r]
                (fun z => ∑ i ∈ insert a s, polyExpC (P i) (μ i) z) :=
            (expKill_iterate_finset (insert a s) (μ a) μ P r).symm
          _ = (expKill (μ a))^[r] 0 := congrArg ((expKill (μ a))^[r]) hsum
          _ = 0 := by
            induction r with
            | zero => rfl
            | succ r ihr =>
                rw [Function.iterate_succ_apply', ihr]
                funext z
                simp [expKill]
      have hrzero0 : (expShiftPoly 0)^[r] (P a) = 0 := by
        simpa using hrzero
      have hsrel :
          (fun z => ∑ i ∈ s,
            polyExpC ((expShiftPoly (μ i - μ a))^[r] (P i)) (μ i) z) = 0 := by
        simpa [Finset.sum_insert, ha, hrzero0, polyExpC_zero_poly] using hop
      have htrans := ih (P := fun i =>
        (expShiftPoly (μ i - μ a))^[r] (P i)) hμs hsrel
      have hPs : ∀ i ∈ s, P i = 0 := by
        intro i hi
        have hia : i ≠ a := fun h => ha (h ▸ hi)
        have hfreq : μ i - μ a ≠ 0 := sub_ne_zero.mpr fun hfreqEq =>
          hia (hμ (Finset.mem_insert_of_mem hi) (Finset.mem_insert_self a s) hfreqEq)
        exact (expShiftPoly_iterate_eq_zero_iff (μ i - μ a) hfreq (P i) r).mp
          (htrans i hi)
      have hPa : P a = 0 := by
        apply Polynomial.funext
        intro z
        have hz := congrFun hsum z
        rw [Finset.sum_insert ha] at hz
        have hszero : ∑ i ∈ s, polyExpC (P i) (μ i) z = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          rw [hPs i hi, polyExpC_zero_poly]
          rfl
        rw [hszero, add_zero] at hz
        have hprod : (P a).eval z * Complex.exp (μ a * z) = 0 := by
          simpa [polyExpC] using hz
        simpa using (mul_eq_zero.mp hprod).resolve_right (Complex.exp_ne_zero _)
      intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · exact hPa
      · exact hPs i hi

/-- Fintype form used by the Baker auxiliary function. -/
theorem expPoly_sum_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → ℂ) (P : ι → Polynomial ℂ) (hμ : Function.Injective μ)
    (hP : P ≠ 0) :
    (fun z => ∑ i, polyExpC (P i) (μ i) z) ≠ 0 := by
  intro hsum
  have hzero := expPoly_finset_eq_zero Finset.univ μ P hμ.injOn hsum
  apply hP
  funext i
  exact hzero i (Finset.mem_univ i)

end GaloisForLFunctions.RHTower.BakerGeneralProof
