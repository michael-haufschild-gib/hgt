import GaloisForLFunctions.RHTower.BakerGeneralProof.FrequencyModulus
import GaloisForLFunctions.HTGeometry.RealExponentialPolynomial

/-!
# Gap-free interpolation of exponential polynomials

This module identifies the initial time derivatives of a finite exponential polynomial with a
confluent frequency-jet functional. Applying that functional to the contour Hermite polynomial
gives an exact representation of the exponential polynomial by its initial time derivatives.
Neither the identity nor its contour construction uses a lower bound on pairwise frequency gaps.
-/

open scoped Classical
open Complex Metric
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

theorem iteratedDeriv_polynomial_eval
    (P : Polynomial ℂ) (k : ℕ) (x : ℂ) :
    iteratedDeriv k (fun y : ℂ => P.eval y) x =
      (Polynomial.derivative^[k] P).eval x := by
  induction k generalizing P with
  | zero => simp
  | succ k ih =>
      rw [show k + 1 = k.succ by omega, Function.iterate_succ_apply]
      rw [show iteratedDeriv k.succ (fun y : ℂ => P.eval y) =
          iteratedDeriv k (deriv fun y : ℂ => P.eval y) by
            simpa using (iteratedDeriv_succ' (n := k) (f := fun y : ℂ => P.eval y))]
      have hderiv : deriv (fun y : ℂ => P.eval y) =
          fun y : ℂ => P.derivative.eval y := by
        funext y
        exact (P.hasDerivAt y).deriv
      rw [hderiv, ih]

theorem iteratedDeriv_finset_sum_complex {I : Type*} (s : Finset I)
    (n : ℕ) {f : I → ℂ → ℂ}
    (hf : ∀ i ∈ s, ContDiff ℂ n (f i)) (x : ℂ) :
    iteratedDeriv n (fun z => ∑ i ∈ s, f i z) x =
      ∑ i ∈ s, iteratedDeriv n (f i) x := by
  simp only [iteratedDeriv_eq_iteratedFDeriv]
  rw [iteratedFDeriv_sum hf, Finset.sum_apply, _root_.sum_apply]

/-- Time/frequency duality for a monomial times an exponential. -/
theorem iteratedDeriv_exp_mul_pow_zero
    (mu : ℂ) (n k : ℕ) :
    iteratedDeriv n
        (fun z : ℂ => Complex.exp (mu * z) * z ^ k) 0 =
      (Polynomial.derivative^[k] (Polynomial.X ^ n : Polynomial ℂ)).eval mu := by
  change
    iteratedDeriv n
        ((fun z : ℂ => Complex.exp (mu * z)) *
          (fun z : ℂ => z ^ k)) 0 = _
  rw [iteratedDeriv_mul (by fun_prop) (by fun_prop)]
  simp only [iteratedDeriv_cexp_const_mul, mul_zero,
    Complex.exp_zero, mul_one, iteratedDeriv_fun_pow_zero]
  rw [Polynomial.iterate_derivative_X_pow_eq_C_mul,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  by_cases hkn : k ≤ n
  · rw [Finset.sum_eq_single (n - k)]
    · simp [Nat.sub_sub_self hkn, Nat.choose_symm hkn,
        Nat.descFactorial_eq_factorial_mul_choose, mul_comm]
      ring
    · intro b hb hbne
      have hneq : n - b ≠ k := by
        have hblt : b < n + 1 := Finset.mem_range.mp hb
        omega
      simp [hneq]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega))).elim
  · have hnk : n < k := Nat.lt_of_not_ge hkn
    have hdesc : n.descFactorial k = 0 :=
      Nat.descFactorial_eq_zero_iff_lt.mpr hnk
    rw [hdesc]
    simp only [Nat.cast_zero, zero_mul]
    apply Finset.sum_eq_zero
    intro b hb
    have hblt : b < n + 1 := Finset.mem_range.mp hb
    have hneq : n - b ≠ k := by omega
    simp [hneq]

noncomputable def exponentialPolynomial {I : Type*} [Fintype I]
    (P : I → Polynomial ℂ) (mu : I → ℂ) : ℂ → ℂ :=
  fun z => ∑ i, polyExpC (P i) (mu i) z

noncomputable def frequencyJetLinearMap {I : Type*} [Fintype I]
    (P : I → Polynomial ℂ) (mu : I → ℂ) (K : ℕ) :
    Polynomial ℂ →ₗ[ℂ] ℂ where
  toFun H := ∑ i, ∑ k ∈ Finset.range K,
    (P i).coeff k * (Polynomial.derivative^[k] H).eval (mu i)
  map_add' H J := by
    simp only [← Module.End.pow_apply, map_add, Polynomial.eval_add, mul_add,
      Finset.sum_add_distrib]
  map_smul' c H := by
    simp only [← Module.End.pow_apply, map_smul, Polynomial.eval_smul,
      smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring

theorem iteratedDeriv_polyExpC_zero_eq_frequencyJet
    (P : Polynomial ℂ) (mu : ℂ) (K n : ℕ)
    (hP : P.natDegree < K) :
    iteratedDeriv n (polyExpC P mu) 0 =
      ∑ k ∈ Finset.range K, P.coeff k *
        (Polynomial.derivative^[k] (Polynomial.X ^ n : Polynomial ℂ)).eval mu := by
  have hfun : polyExpC P mu = fun z : ℂ =>
      ∑ k ∈ Finset.range K,
        P.coeff k * (Complex.exp (mu * z) * z ^ k) := by
    funext z
    rw [polyExpC_apply, Polynomial.eval_eq_sum_range' hP, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hfun, iteratedDeriv_finset_sum_complex]
  · apply Finset.sum_congr rfl
    intro k hk
    simp only [iteratedDeriv_const_mul_field]
    rw [iteratedDeriv_exp_mul_pow_zero]
  · intro k hk
    fun_prop

theorem iteratedDeriv_exponentialPolynomial_zero_eq_frequencyJet
    {I : Type*} [Fintype I]
    (P : I → Polynomial ℂ) (mu : I → ℂ) (K n : ℕ)
    (hP : ∀ i, (P i).natDegree < K) :
    iteratedDeriv n (exponentialPolynomial P mu) 0 =
      frequencyJetLinearMap P mu K (Polynomial.X ^ n) := by
  unfold exponentialPolynomial
  rw [iteratedDeriv_finset_sum_complex]
  · unfold frequencyJetLinearMap
    apply Finset.sum_congr rfl
    intro i hi
    exact iteratedDeriv_polyExpC_zero_eq_frequencyJet (P i) (mu i) K n (hP i)
  · intro i hi
    apply (contDiff_polyExpC (P i) (mu i)).of_le
    exact WithTop.coe_le_coe.mpr le_top

theorem frequencyJet_contourHermitePolynomial_eq_exponentialPolynomial
    {I : Type*} [Fintype I]
    (P : I → Polynomial ℂ) (mu : I → ℂ) (K : ℕ)
    (hP : ∀ i, (P i).natDegree < K)
    (Q : Polynomial ℂ) {rho delta : ℝ}
    (hrho : 0 < rho) (hdelta : 0 < delta)
    (hden : ∀ zeta ∈ sphere (0 : ℂ) rho, delta ≤ ‖Q.eval zeta‖)
    (hdvd : ∀ i, (Polynomial.X - Polynomial.C (mu i)) ^ K ∣ Q)
    (hmu : ∀ i, mu i ∈ ball (0 : ℂ) rho)
    (z : ℂ) :
    frequencyJetLinearMap P mu K (contourHermitePolynomial Q rho z) =
      exponentialPolynomial P mu z := by
  unfold frequencyJetLinearMap exponentialPolynomial
  apply Finset.sum_congr rfl
  intro i hi
  rw [polyExpC_apply, Polynomial.eval_eq_sum_range' (hP i), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkK : k < K := Finset.mem_range.mp hk
  rw [← iteratedDeriv_polynomial_eval]
  rw [iteratedDeriv_contourHermitePolynomial_eq_exp Q hrho hdelta hden
    z (mu i) (hdvd i) (hmu i) hkK]
  rw [iteratedDeriv_cexp_const_mul]
  ring

/-- Gap-free contour representation of a finite exponential polynomial by its initial jets. -/
theorem exponentialPolynomial_eq_contourHermite_jet_sum
    {I : Type*} [Fintype I]
    (P : I → Polynomial ℂ) (mu : I → ℂ) (K : ℕ)
    (hP : ∀ i, (P i).natDegree < K)
    (Q : Polynomial ℂ) {rho delta : ℝ}
    (hrho : 0 < rho) (hdelta : 0 < delta)
    (hden : ∀ zeta ∈ sphere (0 : ℂ) rho, delta ≤ ‖Q.eval zeta‖)
    (hdvd : ∀ i, (Polynomial.X - Polynomial.C (mu i)) ^ K ∣ Q)
    (hmu : ∀ i, mu i ∈ ball (0 : ℂ) rho)
    (z : ℂ) :
    exponentialPolynomial P mu z =
      ∑ m ∈ Finset.range ((contourHermitePolynomial Q rho z).natDegree + 1),
        (contourHermitePolynomial Q rho z).coeff m *
          iteratedDeriv m (exponentialPolynomial P mu) 0 := by
  let H := contourHermitePolynomial Q rho z
  let L := frequencyJetLinearMap P mu K
  calc
    exponentialPolynomial P mu z = L H := by
      symm
      exact frequencyJet_contourHermitePolynomial_eq_exponentialPolynomial
        P mu K hP Q hrho hdelta hden hdvd hmu z
    _ = L (∑ m ∈ Finset.range (H.natDegree + 1), H.coeff m • Polynomial.X ^ m) := by
      congr 1
      simpa [Polynomial.smul_eq_C_mul] using H.as_sum_range_C_mul_X_pow
    _ = ∑ m ∈ Finset.range (H.natDegree + 1),
        H.coeff m * L (Polynomial.X ^ m) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = ∑ m ∈ Finset.range (H.natDegree + 1),
        H.coeff m * iteratedDeriv m (exponentialPolynomial P mu) 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [iteratedDeriv_exponentialPolynomial_zero_eq_frequencyJet P mu K m hP]

end GaloisForLFunctions.RHTower.BakerGeneralProof
