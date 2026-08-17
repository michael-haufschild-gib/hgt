import GaloisForLFunctions.HTGeometry.PrimeValueJacobianCriterion
import GaloisForLFunctions.HTGeometry.FinitePrimeCoefficientField

/-!
# The prime-value criterion over the finite-prime coefficient field

The prime-value Jacobian criterion uses the prime derivations at *every* prime.  A polynomial
relation with coefficients in the finite-prime field exposes only finitely many prime directions, so
all the derivations outside that finite set annihilate its coefficients — and the criterion's
induction tolerates a finite exceptional set, because tail independence does.

Hence a finite family of arithmetic functions with tail-independent prime values stays algebraically
independent over the finite-prime coefficient field, with no restriction on the support of the
functions.  This is the `E_fin(s)`-level form of Pong's conclusion for a Dirichlet series that is not
prime-supported.
-/

open MvPolynomial ArithmeticFunction Finset

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **The induction of the prime-value criterion, with a finite set of primes excluded.** -/
theorem eq_zero_of_sum_mul_primeDeriv_eq_zero {ι : Type*} [Fintype ι]
    (g R : ι → ArithmeticFunction ℂ) (S : Set Nat.Primes) (hS : S.Finite)
    (htail : TailCoefficientIndependent (fun i => fun p : Nat.Primes => g i (p : ℕ)))
    (hrel : ∀ q : Nat.Primes, q ∉ S → ∑ j, R j * primeDeriv (q : ℕ) (g j) = 0) :
    ∀ j, R j = 0 := by
  classical
  have hzero : ∀ n : ℕ, ∀ j, R j n = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases eq_or_ne n 0 with rfl | hn0
      · intro j
        simp
      · have hc : ∀ q : Nat.Primes, q ∉ S → ∑ j, R j n * g j (q : ℕ) = 0 := by
          intro q hq
          have h0 : ∑ j, (R j * primeDeriv (q : ℕ) (g j)) n = 0 := by
            rw [← sum_arithmeticFunction_apply, hrel q hq]
            simp
          rw [← h0]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [ArithmeticFunction.mul_apply]
          have hmem : (n, 1) ∈ n.divisorsAntidiagonal :=
            Nat.mem_divisorsAntidiagonal.2 ⟨by simp, hn0⟩
          have hother : ∀ x ∈ n.divisorsAntidiagonal, x ≠ (n, 1) →
              R j x.1 * primeDeriv (q : ℕ) (g j) x.2 = 0 := by
            intro x hx hxne
            have hx1 : x.1 * x.2 = n := (Nat.mem_divisorsAntidiagonal.1 hx).1
            have hdvd : x.1 ∣ n := ⟨x.2, hx1.symm⟩
            have hle : x.1 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
            have hne : x.1 ≠ n := by
              intro hxeq
              refine hxne ?_
              have hx2 : x.2 = 1 := by
                have hmul : n * x.2 = n * 1 := by rw [← hxeq, hx1, mul_one, hxeq]
                exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn0) hmul
              exact Prod.ext_iff.2 ⟨hxeq, hx2⟩
            rw [ih x.1 (lt_of_le_of_ne hle hne) j, zero_mul]
          rw [Finset.sum_eq_single_of_mem (n, 1) hmem hother, primeDeriv_apply, one_mul,
            q.2.factorization_self]
          push_cast
          ring
        have hfin : {p : Nat.Primes | ∑ j, R j n * g j (p : ℕ) ≠ 0}.Finite := by
          refine hS.subset fun p hp => ?_
          by_contra hpS
          exact hp (hc p hpS)
        have hzero' := htail (fun j => R j n) hfin
        intro j
        exact congrFun hzero' j
  intro j
  ext n
  exact hzero n j

/-- **Independence over the common kernel field of the primes outside a finite set.** -/
theorem algebraicIndependent_over_primeCommonKernelField_compl {ι : Type*} [Fintype ι]
    [DecidableEq ι] (g : ι → ArithmeticFunction ℂ)
    (htail : TailCoefficientIndependent (fun i => fun p : Nat.Primes => g i (p : ℕ)))
    (S : Set Nat.Primes) (hS : S.Finite) :
    AlgebraicIndependent
      (primeCommonKernelField (fun p : {p : Nat.Primes // p ∉ S} => (p : Nat.Primes)))
      (fun i => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField (g i)) := by
  classical
  set points : {p : Nat.Primes // p ∉ S} → Nat.Primes := fun p => (p : Nat.Primes) with hpoints
  set G : ι → arithmeticFunctionFractionField :=
    fun i => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField (g i) with hG
  rw [algebraicIndependent_iff_ker_eq_bot]
  by_contra hker
  obtain ⟨P, hPI, hP0, hmin⟩ :=
    GaloisForLFunctions.Ideal.exists_minimal_mvPolynomial_totalDegree_ne_zero hker
  have hPeval : MvPolynomial.aeval G P = 0 := RingHom.mem_ker.mp hPI
  set Qj : ι → arithmeticFunctionFractionField :=
    fun j => MvPolynomial.aeval G (MvPolynomial.pderiv j P) with hQj
  -- clear denominators uniformly
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples
    (nonZeroDivisors (ArithmeticFunction ℂ)) Finset.univ Qj
  choose R hR using fun j => (hb j (Finset.mem_univ j))
  -- the relation in the ring, at every prime outside `S`
  have hring : ∀ q : Nat.Primes, q ∉ S → ∑ j, R j * primeDeriv (q : ℕ) (g j) = 0 := by
    intro q hq
    have hchain := jacobian_aeval_eq_sum_pderiv
      (K := primeCommonKernelField points) (primeCommonKernelDerivation points ⟨q, hq⟩)
      (fun x y => map_add _ x y)
      (fun x y => by
        simpa only [Algebra.smul_def] using!
          (primeCommonKernelDerivation points ⟨q, hq⟩).leibniz x y)
      (fun c => (primeCommonKernelDerivation points ⟨q, hq⟩).map_algebraMap c) G P
    rw [hPeval, _root_.map_zero] at hchain
    have hD : ∀ j, primeCommonKernelDerivation points ⟨q, hq⟩ (G j)
        = algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (primeDeriv (q : ℕ) (g j)) := by
      intro j
      rw [primeCommonKernelDerivation_apply, hG]
      exact primeFractionDerivation_algebraMap (points ⟨q, hq⟩) (g j)
    have hsum : ∑ j, Qj j * algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (primeDeriv (q : ℕ) (g j)) = 0 := by
      have hrw : ∑ j, Qj j * algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
            (primeDeriv (q : ℕ) (g j))
          = ∑ j, MvPolynomial.aeval G (MvPolynomial.pderiv j P)
              * primeCommonKernelDerivation points ⟨q, hq⟩ (G j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hD j]
      rw [hrw, ← hchain]
    have hmul : algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (∑ j, R j * primeDeriv (q : ℕ) (g j)) = 0 := by
      rw [map_sum]
      have hterm : ∀ j, algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (R j * primeDeriv (q : ℕ) (g j))
          = algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField (b : ArithmeticFunction ℂ)
            * (Qj j * algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
              (primeDeriv (q : ℕ) (g j))) := by
        intro j
        rw [map_mul, hR j]
        rw [Algebra.smul_def]
        ring
      rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.mul_sum, hsum, mul_zero]
    exact IsFractionRing.injective (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (by simpa using hmul)
  have hRzero := eq_zero_of_sum_mul_primeDeriv_eq_zero g R S hS htail hring
  have hQzero : ∀ j, Qj j = 0 := by
    intro j
    have hbne : algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (b : ArithmeticFunction ℂ) ≠ 0 := by
      intro h0
      have hb0 : (b : ArithmeticFunction ℂ) = 0 :=
        IsFractionRing.injective (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (by rw [h0, _root_.map_zero])
      exact (nonZeroDivisors.coe_ne_zero b) hb0
    have hval : algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (b : ArithmeticFunction ℂ) * Qj j = 0 := by
      have := hR j
      rw [hRzero j] at this
      rw [Algebra.smul_def] at this
      simpa using this.symm
    exact (mul_eq_zero.mp hval).resolve_left hbne
  -- minimality contradiction
  have hPvars : P.vars.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hvars
    have hPC := MvPolynomial.vars_eq_empty_iff_eq_C.mp hvars
    rw [hPC] at hPeval hP0
    have hcmap : algebraMap (primeCommonKernelField points) arithmeticFunctionFractionField
        (P.coeff 0) = 0 := by simpa using hPeval
    have hc : P.coeff 0 = 0 :=
      FaithfulSMul.algebraMap_injective (primeCommonKernelField points)
        arithmeticFunctionFractionField (by simpa using hcmap)
    exact hP0 (by simp [hc])
  obtain ⟨i, hi⟩ := hPvars
  obtain ⟨s, hsP, his⟩ := (MvPolynomial.mem_vars_iff_mem_support i).mp hi
  have hpderiv0 : MvPolynomial.pderiv i P ≠ 0 :=
    GaloisForLFunctions.pderiv_ne_zero_of_mem_support hsP his
  have hpI : MvPolynomial.pderiv i P ∈ RingHom.ker (MvPolynomial.aeval G).toRingHom :=
    RingHom.mem_ker.mpr (hQzero i)
  have hle := hmin hpI hpderiv0
  have hlt := GaloisForLFunctions.totalDegree_pderiv_lt P i hpderiv0
  exact (not_lt_of_ge hle) hlt

/-- **Pong's conclusion over `E_fin`.**  A finite family of arithmetic functions whose prime values
are tail independent is algebraically independent over the finite-prime coefficient field — with no
restriction on the support of the functions. -/
theorem algebraicIndependent_over_finitePrimeCoefficientField_of_tailIndependent
    {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → ArithmeticFunction ℂ)
    (htail : TailCoefficientIndependent (fun i => fun p : Nat.Primes => g i (p : ℕ))) :
    AlgebraicIndependent finitePrimeCoefficientField
      (fun i => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField (g i)) := by
  classical
  set G : ι → arithmeticFunctionFractionField :=
    fun i => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField (g i) with hG
  rw [algebraicIndependent_iff]
  intro P hPeval
  by_contra hPne
  have hSfin : (polynomialPrimeActivity P).Finite := polynomialPrimeActivity_finite P
  set points : {p : Nat.Primes // p ∉ polynomialPrimeActivity P} → Nat.Primes :=
    fun p => (p : Nat.Primes) with hpoints
  have havoid : ∀ j, points j ∉ polynomialPrimeActivity P := fun j => j.2
  have hAI := algebraicIndependent_over_primeCommonKernelField_compl g htail
    (polynomialPrimeActivity P) hSfin
  set Q : MvPolynomial ι (primeCommonKernelField points) :=
    liftPolynomialToPrimeCommonKernel points P havoid with hQ
  have hQne : Q ≠ 0 := liftPolynomialToPrimeCommonKernel_ne_zero points P havoid hPne
  have hmap := map_liftPolynomialToPrimeCommonKernel points P havoid
  have heval := congrArg (MvPolynomial.eval G) hmap
  have hQeval : MvPolynomial.aeval G Q = 0 := by
    have heq : MvPolynomial.aeval G Q = MvPolynomial.aeval G P := by
      simpa [hQ, MvPolynomial.aeval_def, MvPolynomial.eval_map] using heval
    exact heq.trans hPeval
  exact hQne (hAI.eq_zero_of_aeval_eq_zero Q hQeval)

end GaloisForLFunctions.HTGeometry

end
