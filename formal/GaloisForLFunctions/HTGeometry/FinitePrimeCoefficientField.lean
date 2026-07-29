import GaloisForLFunctions.HTGeometry.ArithmeticFunctionDomain
import GaloisForLFunctions.HTGeometry.ArithmeticFunctionJacobianCriterion
import GaloisForLFunctions.HTGeometry.FractionRingDerivation
import GaloisForLFunctions.HTGeometry.FiniteRangeProjectiveTail

/-!
# The finite-prime coefficient field

The coefficient field used by the prime-tail differential matroid is most naturally characterized
inside the fraction field of the Dirichlet-convolution algebra: an element belongs to it exactly
when only finitely many prime-coordinate derivations detect it.  This intrinsic definition is
closed under every field operation and avoids choosing a presentation by finite Euler products.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction

noncomputable section

/-- The prime-coordinate operator as an honest complex derivation of the arithmetic-function
Dirichlet-convolution algebra. -/
def primeArithmeticDerivation (q : ℕ) (hq : q.Prime) :
    Derivation ℂ (ArithmeticFunction ℂ) (ArithmeticFunction ℂ) :=
  Derivation.mk'
    { toFun := primeDeriv q
      map_add' := primeDeriv_add q
      map_smul' := primeDeriv_smul q }
    (by
      intro f g
      simpa only [Algebra.smul_def] using! primeDeriv_mul q hq f g)

@[simp]
theorem primeArithmeticDerivation_apply (q : ℕ) (hq : q.Prime)
    (f : ArithmeticFunction ℂ) :
    primeArithmeticDerivation q hq f = primeDeriv q f := rfl

/-- The ambient fraction field in which finite-prime coefficients and prime-supported carriers are
compared. -/
abbrev arithmeticFunctionFractionField := FractionRing (ArithmeticFunction ℂ)

/-- Extension of a prime-coordinate derivation to the full fraction field. -/
def primeFractionDerivation (p : Nat.Primes) :
    Derivation ℂ arithmeticFunctionFractionField arithmeticFunctionFractionField :=
  fractionRingDerivation
    ((Algebra.linearMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField).compDer
      (primeArithmeticDerivation p.1 p.2))

@[simp]
theorem primeFractionDerivation_algebraMap (p : Nat.Primes)
    (f : ArithmeticFunction ℂ) :
    primeFractionDerivation p
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f) =
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField (primeDeriv p.1 f) := by
  exact fractionRingDerivation_algebraMap
    ((Algebra.linearMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField).compDer
      (primeArithmeticDerivation p.1 p.2)) f

/-- The prime directions which detect a fraction of arithmetic functions. -/
def finitePrimeActivity (x : arithmeticFunctionFractionField) : Set Nat.Primes :=
  {p | primeFractionDerivation p x ≠ 0}

/-- **Finite-prime coefficient field.**  These are exactly the fractions detected by only finitely
many prime-coordinate derivations.  The definition is presentation-free and is stable under
addition, multiplication, negation, and inversion. -/
def finitePrimeCoefficientField : Subfield arithmeticFunctionFractionField where
  carrier := {x | (finitePrimeActivity x).Finite}
  zero_mem' := by
    change (finitePrimeActivity 0).Finite
    simp [finitePrimeActivity]
  one_mem' := by
    change (finitePrimeActivity 1).Finite
    simp [finitePrimeActivity]
  add_mem' := by
    intro x y hx hy
    apply (hx.union hy).subset
    intro p hp
    change primeFractionDerivation p (x + y) ≠ 0 at hp
    change primeFractionDerivation p x ≠ 0 ∨ primeFractionDerivation p y ≠ 0
    by_contra hnot
    rw [not_or, not_ne_iff, not_ne_iff] at hnot
    simp [hnot.1, hnot.2] at hp
  mul_mem' := by
    intro x y hx hy
    apply (hx.union hy).subset
    intro p hp
    change primeFractionDerivation p (x * y) ≠ 0 at hp
    change primeFractionDerivation p x ≠ 0 ∨ primeFractionDerivation p y ≠ 0
    by_contra hnot
    rw [not_or, not_ne_iff, not_ne_iff] at hnot
    simp [Derivation.leibniz, hnot.1, hnot.2] at hp
  neg_mem' := by
    intro x hx
    apply hx.subset
    intro p hp
    simp only [finitePrimeActivity, Set.mem_setOf_eq] at hp ⊢
    intro hzero
    apply hp
    simp [hzero]
  inv_mem' := by
    intro x hx
    apply hx.subset
    intro p hp
    simp only [finitePrimeActivity, Set.mem_setOf_eq] at hp ⊢
    intro hzero
    apply hp
    simp [(primeFractionDerivation p).leibniz_inv, hzero]

@[simp]
theorem mem_finitePrimeCoefficientField_iff
    (x : arithmeticFunctionFractionField) :
    x ∈ finitePrimeCoefficientField ↔ (finitePrimeActivity x).Finite :=
  Iff.rfl

/-- A scalar complex constant has no active prime directions. -/
theorem finitePrimeActivity_algebraMap_complex (c : ℂ) :
    finitePrimeActivity
        (algebraMap ℂ arithmeticFunctionFractionField c) = ∅ := by
  ext p
  simp [finitePrimeActivity]

/-- Tail independence supplies a full-rank evaluation packet outside any prescribed finite set of
coordinates.  This is the dynamic form needed when the forbidden primes are read from the
coefficients of a putative algebraic relation. -/
theorem TailCoefficientIndependent.exists_fullRank_evaluation_packet_avoiding
    {I P : Type*} [Fintype I] [DecidableEq I]
    (a : I → P → ℂ) (h : TailCoefficientIndependent a)
    (forbidden : Set P) (hforbidden : forbidden.Finite) :
    ∃ points : I → P, (∀ i, points i ∉ forbidden) ∧
      IsUnit (Matrix.of fun row i => a i (points row) : Matrix I I ℂ) := by
  let P' := {p : P // p ∉ forbidden}
  let a' : I → P' → ℂ := fun i p => a i p.1
  have htail' : TailCoefficientIndependent a' := by
    intro c hc
    apply h c
    apply (hforbidden.union (hc.image Subtype.val)).subset
    intro p hp
    by_cases hpf : p ∈ forbidden
    · exact Set.mem_union_left _ hpf
    · apply Set.mem_union_right
      refine ⟨⟨p, hpf⟩, ?_, rfl⟩
      exact hp
  obtain ⟨points, hpoints⟩ := htail'.exists_fullRank_evaluation_packet a'
  refine ⟨fun i => (points i).1, fun i => (points i).2, ?_⟩
  exact hpoints

/-- The common constant field of a finite packet of prime-coordinate derivations. -/
def primeCommonKernelField {I : Type*} (points : I → Nat.Primes) :
    IntermediateField ℂ arithmeticFunctionFractionField where
  carrier := {x | ∀ i, primeFractionDerivation (points i) x = 0}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro x y hx hy i
    simp [hx i, hy i]
  mul_mem' := by
    intro x y hx hy i
    simp [Derivation.leibniz, hx i, hy i]
  algebraMap_mem' := by
    intro c i
    exact (primeFractionDerivation (points i)).map_algebraMap c
  inv_mem' := by
    intro x hx i
    simp [(primeFractionDerivation (points i)).leibniz_inv, hx i]

@[simp]
theorem mem_primeCommonKernelField_iff {I : Type*}
    (points : I → Nat.Primes) (x : arithmeticFunctionFractionField) :
    x ∈ primeCommonKernelField points ↔
      ∀ i, primeFractionDerivation (points i) x = 0 :=
  Iff.rfl

/-- A prime derivation becomes linear over the packet's common kernel field. -/
def primeCommonKernelDerivation {I : Type*} (points : I → Nat.Primes) (i : I) :
    Derivation (primeCommonKernelField points)
      arithmeticFunctionFractionField arithmeticFunctionFractionField :=
  Derivation.mk'
    { toFun := primeFractionDerivation (points i)
      map_add' := map_add _
      map_smul' := by
        intro c x
        change primeFractionDerivation (points i) ((c.1 : arithmeticFunctionFractionField) * x) =
          (c.1 : arithmeticFunctionFractionField) * primeFractionDerivation (points i) x
        rw [Derivation.leibniz, c.2 i, smul_eq_mul, smul_eq_mul, mul_zero, add_zero] }
    (by
      intro x y
      simpa only [Algebra.smul_def] using!
        (primeFractionDerivation (points i)).leibniz x y)

@[simp]
theorem primeCommonKernelDerivation_apply {I : Type*}
    (points : I → Nat.Primes) (i : I) (x : arithmeticFunctionFractionField) :
    primeCommonKernelDerivation points i x =
      primeFractionDerivation (points i) x := rfl

/-- The finite set of prime directions visible in the supported coefficients of a polynomial over
the finite-prime coefficient field. -/
def polynomialPrimeActivity {I : Type*}
    (P : MvPolynomial I finitePrimeCoefficientField) : Set Nat.Primes :=
  ⋃ s ∈ P.support, finitePrimeActivity (P.coeff s).1

/-- A polynomial over the finite-prime field exposes only finitely many prime directions. -/
theorem polynomialPrimeActivity_finite {I : Type*}
    (P : MvPolynomial I finitePrimeCoefficientField) :
    (polynomialPrimeActivity P).Finite := by
  classical
  apply P.support.finite_toSet.biUnion
  intro s hs
  exact (P.coeff s).2

/-- A supported coefficient is constant for every packet derivation chosen outside the polynomial's
activity set. -/
theorem polynomial_coeff_mem_primeCommonKernelField
    {I J : Type*} (points : J → Nat.Primes)
    (P : MvPolynomial I finitePrimeCoefficientField)
    (havoid : ∀ j, points j ∉ polynomialPrimeActivity P)
    {s : I →₀ ℕ} (hs : s ∈ P.support) :
    ((P.coeff s).1 : arithmeticFunctionFractionField) ∈
      primeCommonKernelField points := by
  intro j
  by_contra hne
  exact havoid j (Set.mem_iUnion₂.mpr ⟨s, hs, hne⟩)

/-- Every coefficient, including the zero coefficients off support, lifts to the packet's common
kernel field. -/
def liftPolynomialCoefficientToPrimeCommonKernel
    {I J : Type*} (points : J → Nat.Primes)
    (P : MvPolynomial I finitePrimeCoefficientField)
    (havoid : ∀ j, points j ∉ polynomialPrimeActivity P)
    (s : I →₀ ℕ) : primeCommonKernelField points := by
  refine ⟨(P.coeff s).1, ?_⟩
  by_cases hs : s ∈ P.support
  · exact polynomial_coeff_mem_primeCommonKernelField points P havoid hs
  · have hzero : P.coeff s = 0 := MvPolynomial.notMem_support_iff.mp hs
    intro j
    rw [hzero]
    simp

/-- Lift one polynomial relation into the common kernel field of a packet which avoids every active
prime of its coefficients. -/
def liftPolynomialToPrimeCommonKernel
    {I J : Type*} (points : J → Nat.Primes)
    (P : MvPolynomial I finitePrimeCoefficientField)
    (havoid : ∀ j, points j ∉ polynomialPrimeActivity P) :
    MvPolynomial I (primeCommonKernelField points) :=
  ∑ s ∈ P.support,
    MvPolynomial.monomial s
      (liftPolynomialCoefficientToPrimeCommonKernel points P havoid s)

/-- The lifted polynomial has exactly the same image in the ambient fraction field. -/
theorem map_liftPolynomialToPrimeCommonKernel
    {I J : Type*} (points : J → Nat.Primes)
    (P : MvPolynomial I finitePrimeCoefficientField)
    (havoid : ∀ j, points j ∉ polynomialPrimeActivity P) :
    MvPolynomial.map
        (algebraMap (primeCommonKernelField points) arithmeticFunctionFractionField)
        (liftPolynomialToPrimeCommonKernel points P havoid) =
      MvPolynomial.map
        (algebraMap finitePrimeCoefficientField arithmeticFunctionFractionField) P := by
  classical
  have hright :
      MvPolynomial.map
          (algebraMap finitePrimeCoefficientField arithmeticFunctionFractionField) P =
        ∑ s ∈ P.support, MvPolynomial.monomial s
          (algebraMap finitePrimeCoefficientField arithmeticFunctionFractionField (P.coeff s)) := by
    calc
      MvPolynomial.map
          (algebraMap finitePrimeCoefficientField arithmeticFunctionFractionField) P =
          MvPolynomial.map
            (algebraMap finitePrimeCoefficientField arithmeticFunctionFractionField)
            (∑ s ∈ P.support, MvPolynomial.monomial s (P.coeff s)) :=
        congrArg _ P.as_sum
      _ = ∑ s ∈ P.support, MvPolynomial.monomial s
          (algebraMap finitePrimeCoefficientField arithmeticFunctionFractionField (P.coeff s)) := by
        simp only [map_sum, MvPolynomial.map_monomial]
  rw [hright]
  change MvPolynomial.map
      (algebraMap (primeCommonKernelField points) arithmeticFunctionFractionField)
      (∑ s ∈ P.support, MvPolynomial.monomial s
        (liftPolynomialCoefficientToPrimeCommonKernel points P havoid s)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [MvPolynomial.map_monomial]
  rfl

/-- Lifting coefficients into a common kernel does not annihilate a nonzero polynomial. -/
theorem liftPolynomialToPrimeCommonKernel_ne_zero
    {I J : Type*} (points : J → Nat.Primes)
    (P : MvPolynomial I finitePrimeCoefficientField)
    (havoid : ∀ j, points j ∉ polynomialPrimeActivity P)
    (hP : P ≠ 0) :
    liftPolynomialToPrimeCommonKernel points P havoid ≠ 0 := by
  intro hlift
  have hmap := map_liftPolynomialToPrimeCommonKernel points P havoid
  rw [hlift] at hmap
  simp only [_root_.map_zero] at hmap
  apply hP
  apply MvPolynomial.map_injective
    (algebraMap finitePrimeCoefficientField arithmeticFunctionFractionField)
    (FaithfulSMul.algebraMap_injective finitePrimeCoefficientField
      arithmeticFunctionFractionField)
  exact hmap.symm

/-- A prime-coordinate derivation evaluates a prime-supported column at its packet prime. -/
theorem primeFractionDerivation_arithmeticOfPrimeColumn
    (p : Nat.Primes) (a : Nat.Primes → ℂ) :
    primeFractionDerivation p
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (arithmeticOfPrimeColumn a)) =
      algebraMap ℂ arithmeticFunctionFractionField (a p) := by
  rw [primeFractionDerivation_algebraMap,
    primeDeriv_prime_supported p.1 p.2 (arithmeticOfPrimeColumn a)
      (fun m hm => arithmeticOfPrimeColumn_support a hm)]
  simp [Algebra.smul_def, arithmeticOfPrimeColumn_apply_prime]
  rw [IsScalarTower.algebraMap_apply ℂ (ArithmeticFunction ℂ)
    arithmeticFunctionFractionField]

/-- **Dynamic finite-prime Jacobian theorem.**  Tail-independent prime columns remain algebraically
independent over the entire finite-prime coefficient field.  For a putative relation, the proof
reads the finite set of active primes from its supported coefficients, chooses a full-rank packet
outside that set, lifts the relation to the packet's common kernel field, and applies the ordinary
Jacobian criterion there. -/
theorem algebraicIndependent_fractionPrimeColumns_over_finitePrimeCoefficientField
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → Nat.Primes → ℂ) (htail : TailCoefficientIndependent a) :
    AlgebraicIndependent finitePrimeCoefficientField
      (fun i => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (arithmeticOfPrimeColumn (a i))) := by
  rw [algebraicIndependent_iff]
  intro P hPeval
  by_contra hPne
  have hPne' : P ≠ 0 := hPne
  obtain ⟨points, havoid, hpacket⟩ :=
    htail.exists_fullRank_evaluation_packet_avoiding a
      (polynomialPrimeActivity P) (polynomialPrimeActivity_finite P)
  let K := primeCommonKernelField points
  let g : I → arithmeticFunctionFractionField := fun i =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (arithmeticOfPrimeColumn (a i))
  let M0 : Matrix I I ℂ := Matrix.of fun row i => a i (points row)
  let M : Matrix I I K := (algebraMap ℂ K).mapMatrix M0
  have hM : IsUnit M := by
    exact hpacket.map (RingHom.mapMatrix (algebraMap ℂ K))
  have hAIK : AlgebraicIndependent K g := by
    refine algebraicIndependent_of_jacobian (K := K) g
      (fun i => primeCommonKernelDerivation points i)
      (fun i x y => map_add (primeCommonKernelDerivation points i) x y)
      (fun i x y => by
        simpa only [Algebra.smul_def] using!
          (primeCommonKernelDerivation points i).leibniz x y)
      (fun i c => (primeCommonKernelDerivation points i).map_algebraMap c)
      M hM ?_
    intro i j
    change primeFractionDerivation (points i) (g j) =
      algebraMap K arithmeticFunctionFractionField (M i j)
    rw [show g j = algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (arithmeticOfPrimeColumn (a j)) from rfl,
      primeFractionDerivation_arithmeticOfPrimeColumn]
    change algebraMap ℂ arithmeticFunctionFractionField (a j (points i)) =
      algebraMap K arithmeticFunctionFractionField
        (algebraMap ℂ K (a j (points i)))
    rw [IsScalarTower.algebraMap_apply ℂ K arithmeticFunctionFractionField]
  let Q : MvPolynomial I K :=
    liftPolynomialToPrimeCommonKernel points P havoid
  have hQne : Q ≠ 0 :=
    liftPolynomialToPrimeCommonKernel_ne_zero points P havoid hPne'
  have hmap := map_liftPolynomialToPrimeCommonKernel points P havoid
  have heval := congrArg (MvPolynomial.eval g) hmap
  have hQeval : MvPolynomial.aeval g Q = 0 := by
    have heq : MvPolynomial.aeval g Q = MvPolynomial.aeval g P := by
      simpa [Q, MvPolynomial.aeval_def, MvPolynomial.eval_map] using heval
    exact heq.trans hPeval
  exact hQne (hAIK.eq_zero_of_aeval_eq_zero Q hQeval)

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction

noncomputable section

/-- The intrinsic finite-prime field contains the scalar complex constants. -/
def complexToFinitePrimeCoefficientField : ℂ →+* finitePrimeCoefficientField :=
  (algebraMap ℂ arithmeticFunctionFractionField).codRestrict
    finitePrimeCoefficientField (by
      intro c
      rw [mem_finitePrimeCoefficientField_iff,
        finitePrimeActivity_algebraMap_complex]
      exact Set.finite_empty)

noncomputable instance finitePrimeCoefficientFieldAlgebraComplex :
    Algebra ℂ finitePrimeCoefficientField :=
  complexToFinitePrimeCoefficientField.toAlgebra

instance finitePrimeCoefficientFieldIsScalarTower :
    IsScalarTower ℂ finitePrimeCoefficientField arithmeticFunctionFractionField :=
  .of_algebraMap_eq fun _c => rfl

/-- **Exact tail-matroid theorem.** A finite family of prime-supported arithmetic columns is
algebraically independent over the intrinsic finite-prime coefficient field exactly when its
coefficient vectors are linearly independent modulo finite prime support.

The reverse implication is the dynamic finite-prime Jacobian theorem above. For the converse, a
finite-support coefficient relation is itself an element of the coefficient field; adjoining it as
the constant term of a nonzero linear multivariable polynomial contradicts algebraic
independence. -/
theorem algebraicIndependent_fractionPrimeColumns_over_finitePrimeCoefficientField_iff
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → Nat.Primes → ℂ) :
    AlgebraicIndependent finitePrimeCoefficientField
        (fun i => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (arithmeticOfPrimeColumn (a i))) ↔
      TailCoefficientIndependent a := by
  let x : I → arithmeticFunctionFractionField := fun i =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (arithmeticOfPrimeColumn (a i))
  constructor
  · intro hAI c hfinite
    by_contra hc
    have hc' : c ≠ 0 := hc
    let b : Nat.Primes → ℂ := fun p => ∑ i, c i * a i p
    let r : arithmeticFunctionFractionField :=
      ∑ i, algebraMap ℂ arithmeticFunctionFractionField (c i) * x i
    have hrmem : r ∈ finitePrimeCoefficientField := by
      rw [mem_finitePrimeCoefficientField_iff]
      apply hfinite.subset
      intro p hp
      change primeFractionDerivation p r ≠ 0 at hp
      have hdr : primeFractionDerivation p r =
          algebraMap ℂ arithmeticFunctionFractionField (b p) := by
        rw [show r = ∑ i, algebraMap ℂ arithmeticFunctionFractionField (c i) * x i
          from rfl, map_sum]
        calc
          ∑ i, primeFractionDerivation p
              (algebraMap ℂ arithmeticFunctionFractionField (c i) * x i) =
              ∑ i, algebraMap ℂ arithmeticFunctionFractionField (c i * a i p) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Derivation.leibniz, (primeFractionDerivation p).map_algebraMap,
              primeFractionDerivation_arithmeticOfPrimeColumn]
            simp only [smul_eq_mul, mul_zero, add_zero, map_mul]
          _ = algebraMap ℂ arithmeticFunctionFractionField (∑ i, c i * a i p) := by
            rw [map_sum]
          _ = algebraMap ℂ arithmeticFunctionFractionField (b p) := rfl
      rw [hdr] at hp
      intro hzero
      apply hp
      rw [show b p = ∑ i, c i * a i p from rfl, hzero]
      exact _root_.map_zero _
    let k : finitePrimeCoefficientField := ⟨r, hrmem⟩
    let P : MvPolynomial I finitePrimeCoefficientField :=
      MvPolynomial.C (-k) +
        ∑ i, MvPolynomial.C (algebraMap ℂ finitePrimeCoefficientField (c i)) *
          MvPolynomial.X i
    have hsum :
        ∑ i, algebraMap ℂ arithmeticFunctionFractionField (c i) * x i = r := by
      rfl
    have hPeval : MvPolynomial.aeval x P = 0 := by
      simp only [P, map_add, map_neg, MvPolynomial.aeval_C, map_sum, map_mul,
        MvPolynomial.aeval_X]
      change -(k : arithmeticFunctionFractionField) +
        ∑ i, algebraMap ℂ arithmeticFunctionFractionField (c i) * x i = 0
      change -r + ∑ i, algebraMap ℂ arithmeticFunctionFractionField (c i) * x i = 0
      rw [hsum]
      exact neg_add_cancel r
    have hc_exists : ∃ i, c i ≠ 0 := by
      simpa only [Pi.zero_apply] using (Function.ne_iff.mp hc')
    obtain ⟨i, hi⟩ := hc_exists
    have hPne : P ≠ 0 := by
      intro hzero
      have hmon : (0 : I →₀ ℕ) ≠ Finsupp.single i 1 := by
        exact Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero)
      have hcoeff := congrArg (fun Q : MvPolynomial I finitePrimeCoefficientField =>
        Q.coeff (Finsupp.single i 1)) hzero
      simp [P, MvPolynomial.coeff_add, MvPolynomial.coeff_C,
        MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
        MvPolynomial.coeff_X, Finsupp.single_eq_single_iff, hmon] at hcoeff
      exact hi hcoeff
    exact hPne (hAI.eq_zero_of_aeval_eq_zero P hPeval)
  · exact algebraicIndependent_fractionPrimeColumns_over_finitePrimeCoefficientField a

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction

noncomputable section

/-- The active prime set of a prime-supported arithmetic column is exactly its nonzero coefficient
support. -/
theorem finitePrimeActivity_arithmeticOfPrimeColumn (a : Nat.Primes → ℂ) :
    finitePrimeActivity
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (arithmeticOfPrimeColumn a)) =
      {p | a p ≠ 0} := by
  ext p
  simp only [finitePrimeActivity, Set.mem_setOf_eq,
    primeFractionDerivation_arithmeticOfPrimeColumn]
  constructor
  · intro hmap ha
    apply hmap
    rw [ha, _root_.map_zero]
  · intro ha hmap
    apply ha
    apply FaithfulSMul.algebraMap_injective ℂ arithmeticFunctionFractionField
    simpa using hmap

/-- A prime-supported arithmetic column is a finite-prime coefficient exactly when its coefficient
support is finite. -/
theorem arithmeticOfPrimeColumn_mem_finitePrimeCoefficientField_iff
    (a : Nat.Primes → ℂ) :
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (arithmeticOfPrimeColumn a) ∈ finitePrimeCoefficientField ↔
      {p | a p ≠ 0}.Finite := by
  rw [mem_finitePrimeCoefficientField_iff,
    finitePrimeActivity_arithmeticOfPrimeColumn]

end

end GaloisForLFunctions.HTGeometry
