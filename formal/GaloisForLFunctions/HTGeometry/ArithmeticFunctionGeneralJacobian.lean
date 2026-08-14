import GaloisForLFunctions.HTGeometry.ArithmeticFunctionJacobianCriterion
import GaloisForLFunctions.HTGeometry.PrimePowerDynamicCoefficientField

/-!
# The prime-evaluation criterion without a support restriction

The Shapiro--Sparer bridge reads a full-rank prime-evaluation matrix into algebraic independence of
*prime-supported* arithmetic functions: there the prime derivation `∂_q` of a member of the family
is a scalar, so the Jacobian is a matrix over the base field.  A Dirichlet series whose coefficients
live on all of `ℕ` — a completely multiplicative one, for instance — has no such Jacobian.

The restriction is unnecessary.  The Jacobian is a matrix over the Dirichlet algebra, which is a
domain, so the criterion only needs its determinant to be nonzero, and that is decided at the
identity component: evaluation at `n = 1` is a ring homomorphism, `(∂_q b)(1) = b q`, so the
constant term of the Jacobian determinant is the determinant of the prime-evaluation matrix.

The same computation runs over the fraction field, so the criterion also holds over the common
kernel of the chosen prime derivations, and hence — by the finiteness of the prime activity of a
polynomial — over the whole intrinsic finite-prime coefficient field.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Matrix

noncomputable section

/-! ## Evaluation at the identity component -/

/-- Evaluation at `n = 1` is a ring homomorphism of the Dirichlet-convolution algebra: the only
factorization of `1` is `1 · 1`. -/
def arithmeticEvalOne : ArithmeticFunction ℂ →+* ℂ where
  toFun f := f 1
  map_one' := by simp
  map_mul' f g := by
    rw [ArithmeticFunction.mul_apply, Nat.divisorsAntidiagonal_one]
    simp
  map_zero' := by simp
  map_add' f g := by simp

@[simp] theorem arithmeticEvalOne_apply (f : ArithmeticFunction ℂ) : arithmeticEvalOne f = f 1 :=
  rfl

/-- The prime derivation reads off the value at `q` on the identity component, with no hypothesis
on the support. -/
theorem primeDeriv_apply_one (q : ℕ) (hq : q.Prime) (b : ArithmeticFunction ℂ) :
    primeDeriv q b 1 = b q := by
  rw [primeDeriv_apply, one_mul, hq.factorization_self]
  simp

/-! ## The Jacobian of an arbitrary family -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The prime-derivation Jacobian of an arbitrary finite family of arithmetic functions. -/
def arithmeticPrimeJacobian (g : ι → ArithmeticFunction ℂ) (q : ι → Nat.Primes) :
    Matrix ι ι (ArithmeticFunction ℂ) :=
  Matrix.of fun i j => primeDeriv (q i : ℕ) (g j)

/-- The constant term of the Jacobian is the prime-evaluation matrix. -/
theorem arithmeticPrimeJacobian_evalOne (g : ι → ArithmeticFunction ℂ) (q : ι → Nat.Primes) :
    arithmeticEvalOne.mapMatrix (arithmeticPrimeJacobian g q)
      = (Matrix.of fun i j => g j (q i : ℕ) : Matrix ι ι ℂ) := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, arithmeticPrimeJacobian, Matrix.of_apply,
    arithmeticEvalOne_apply]
  exact primeDeriv_apply_one (q i : ℕ) (q i).2 (g j)

/-- **A nonzero prime-evaluation determinant makes the Jacobian determinant nonzero.** -/
theorem det_arithmeticPrimeJacobian_ne_zero (g : ι → ArithmeticFunction ℂ) (q : ι → Nat.Primes)
    (hdet : (Matrix.of fun i j => g j (q i : ℕ) : Matrix ι ι ℂ).det ≠ 0) :
    (arithmeticPrimeJacobian g q).det ≠ 0 := by
  intro hzero
  refine hdet ?_
  rw [← arithmeticPrimeJacobian_evalOne g q, ← RingHom.map_det, hzero, _root_.map_zero]

/-- **The Shapiro--Sparer bridge without a support restriction.**  An arbitrary finite family of
arithmetic functions with a nonsingular prime-evaluation matrix is algebraically independent
over `ℂ`. -/
theorem algebraicIndependent_arithmeticFunctions_of_primeEvaluation
    (g : ι → ArithmeticFunction ℂ) (q : ι → Nat.Primes)
    (hdet : (Matrix.of fun i j => g j (q i : ℕ) : Matrix ι ι ℂ).det ≠ 0) :
    AlgebraicIndependent ℂ g :=
  algebraicIndependent_of_domain_jacobian (K := ℂ) (R := ArithmeticFunction ℂ) g
    (fun i => primeDeriv (q i : ℕ))
    (fun i => primeDeriv_add (q i : ℕ))
    (fun i => primeDeriv_mul (q i : ℕ) (q i).2)
    (fun i => primeDeriv_algebraMap (q i : ℕ) (q i).2)
    (arithmeticPrimeJacobian g q) (det_arithmeticPrimeJacobian_ne_zero g q hdet)
    (fun _ _ => rfl)

/-! ## Over the common kernel of the chosen derivations -/

/-- The Jacobian embedded in the fraction field. -/
def fractionArithmeticPrimeJacobian (g : ι → ArithmeticFunction ℂ) (q : ι → Nat.Primes) :
    Matrix ι ι arithmeticFunctionFractionField :=
  fun i j => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
    (arithmeticPrimeJacobian g q i j)

omit [Fintype ι] [DecidableEq ι] in
theorem fractionArithmeticPrimeJacobian_apply (g : ι → ArithmeticFunction ℂ)
    (q : ι → Nat.Primes) (i j : ι) :
    fractionArithmeticPrimeJacobian g q i j =
      primeFractionDerivation (q i)
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField (g j)) := by
  rw [fractionArithmeticPrimeJacobian, primeFractionDerivation_algebraMap]
  rfl

theorem det_fractionArithmeticPrimeJacobian_ne_zero (g : ι → ArithmeticFunction ℂ)
    (q : ι → Nat.Primes)
    (hdet : (Matrix.of fun i j => g j (q i : ℕ) : Matrix ι ι ℂ).det ≠ 0) :
    (fractionArithmeticPrimeJacobian g q).det ≠ 0 := by
  have hsource : (arithmeticPrimeJacobian g q).det ≠ 0 :=
    det_arithmeticPrimeJacobian_ne_zero g q hdet
  change ((algebraMap (ArithmeticFunction ℂ)
    arithmeticFunctionFractionField).mapMatrix (arithmeticPrimeJacobian g q)).det ≠ 0
  rw [← RingHom.map_det]
  intro hzero
  refine hsource ?_
  refine FaithfulSMul.algebraMap_injective (ArithmeticFunction ℂ)
    arithmeticFunctionFractionField ?_
  simpa using hzero

/-- **The criterion over the common kernel of the chosen prime derivations.**  Coefficients killed
by every derivation in the packet do not reduce independence. -/
theorem algebraicIndependent_fractionArithmetic_over_commonKernel
    (g : ι → ArithmeticFunction ℂ) (q : ι → Nat.Primes)
    (hdet : (Matrix.of fun i j => g j (q i : ℕ) : Matrix ι ι ℂ).det ≠ 0) :
    AlgebraicIndependent (primeCommonKernelField q)
      (fun j => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField (g j)) := by
  refine algebraicIndependent_of_domain_jacobian
    (K := primeCommonKernelField q) (R := arithmeticFunctionFractionField)
    (fun j => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField (g j))
    (fun i => primeCommonKernelDerivation q i)
    (fun i x y => map_add (primeCommonKernelDerivation q i) x y)
    (fun i x y => by
      simpa only [Algebra.smul_def] using!
        (primeCommonKernelDerivation q i).leibniz x y)
    (fun i c => (primeCommonKernelDerivation q i).map_algebraMap c)
    (fractionArithmeticPrimeJacobian g q)
    (det_fractionArithmeticPrimeJacobian_ne_zero g q hdet) ?_
  intro i j
  exact (fractionArithmeticPrimeJacobian_apply g q i j).symm

/-! ## Over the whole finite-prime coefficient field -/

/-- Every finite forbidden set of primes admits an evaluation packet avoiding it. -/
def CofiniteArithmeticEvaluationPacket (g : ι → ArithmeticFunction ℂ) : Prop :=
  ∀ forbidden : Set Nat.Primes, forbidden.Finite →
    ∃ q : ι → Nat.Primes, (∀ i, q i ∉ forbidden) ∧
      (Matrix.of fun i j => g j (q i : ℕ) : Matrix ι ι ℂ).det ≠ 0

/-- **Dynamic finite-prime theorem for arbitrary arithmetic functions.**  A family with cofinite
nonsingular prime-evaluation packets is algebraically independent over the entire intrinsic
finite-prime coefficient field. -/
theorem algebraicIndependent_fractionArithmetic_over_finitePrimeCoefficientField
    (g : ι → ArithmeticFunction ℂ) (hpacket : CofiniteArithmeticEvaluationPacket g) :
    AlgebraicIndependent finitePrimeCoefficientField
      (fun j => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField (g j)) := by
  rw [algebraicIndependent_iff]
  intro P hPeval
  by_contra hPne
  have hPne' : P ≠ 0 := hPne
  obtain ⟨q, havoid, hdet⟩ :=
    hpacket (polynomialPrimeActivity P) (polynomialPrimeActivity_finite P)
  have hAIK : AlgebraicIndependent (primeCommonKernelField q)
      (fun j => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField (g j)) :=
    algebraicIndependent_fractionArithmetic_over_commonKernel g q hdet
  let Q : MvPolynomial ι (primeCommonKernelField q) :=
    liftPolynomialToPrimeCommonKernel q P havoid
  have hQne : Q ≠ 0 :=
    liftPolynomialToPrimeCommonKernel_ne_zero q P havoid hPne'
  have hmap := map_liftPolynomialToPrimeCommonKernel q P havoid
  let gf : ι → arithmeticFunctionFractionField := fun j =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField (g j)
  have heval := congrArg (MvPolynomial.eval gf) hmap
  have hQeval : MvPolynomial.aeval gf Q = 0 := by
    have heq : MvPolynomial.aeval gf Q = MvPolynomial.aeval gf P := by
      simpa [Q, gf, MvPolynomial.aeval_def, MvPolynomial.eval_map] using heval
    exact heq.trans hPeval
  exact hQne (hAIK.eq_zero_of_aeval_eq_zero Q hQeval)

/-! ## From tail independence of the prime restrictions -/

/-- Tail independence of the prime restrictions supplies packets avoiding every finite set. -/
theorem cofiniteArithmeticEvaluationPacket_of_tailIndependent (g : ι → ArithmeticFunction ℂ)
    (h : TailCoefficientIndependent fun i (p : Nat.Primes) => g i (p : ℕ)) :
    CofiniteArithmeticEvaluationPacket g := by
  intro forbidden hforbidden
  obtain ⟨points, havoid, hunit⟩ :=
    TailCoefficientIndependent.exists_fullRank_evaluation_packet_avoiding
      (fun i (p : Nat.Primes) => g i (p : ℕ)) h forbidden hforbidden
  refine ⟨points, havoid, ?_⟩
  have hdet : IsUnit (Matrix.of fun i j => g j (points i : ℕ) : Matrix ι ι ℂ).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hunit
  exact isUnit_iff_ne_zero.mp hdet

/-- **Tail independence of the prime restrictions is enough, over `ℂ`.** -/
theorem algebraicIndependent_arithmeticFunctions_of_tailIndependent (g : ι → ArithmeticFunction ℂ)
    (h : TailCoefficientIndependent fun i (p : Nat.Primes) => g i (p : ℕ)) :
    AlgebraicIndependent ℂ g := by
  obtain ⟨q, _, hdet⟩ :=
    cofiniteArithmeticEvaluationPacket_of_tailIndependent g h ∅ Set.finite_empty
  exact algebraicIndependent_arithmeticFunctions_of_primeEvaluation g q hdet

/-- **Tail independence of the prime restrictions is enough, over the finite-prime coefficient
field.**  This is the descent the Helson palettes need: the coefficients live on all of `ℕ`, and
only their prime restrictions are constrained. -/
theorem algebraicIndependent_fractionArithmetic_of_tailIndependent (g : ι → ArithmeticFunction ℂ)
    (h : TailCoefficientIndependent fun i (p : Nat.Primes) => g i (p : ℕ)) :
    AlgebraicIndependent finitePrimeCoefficientField
      (fun j => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField (g j)) :=
  algebraicIndependent_fractionArithmetic_over_finitePrimeCoefficientField g
    (cofiniteArithmeticEvaluationPacket_of_tailIndependent g h)

end

end GaloisForLFunctions.HTGeometry
