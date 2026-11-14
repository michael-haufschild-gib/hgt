import GaloisForLFunctions.HTGeometry.FinitePrimeCoefficientField

/-!
# Coefficient fields defined by filters on primes

A filter specifies which prime directions remain available after exceptional primes are removed.
Fractions killed by the prime derivations eventually along this filter form a coefficient field.
For prime-supported series, algebraic independence over this field is exactly linear independence
of their prime coefficients modulo eventual equality. A putative polynomial relation uses only
finitely many coefficients, so one full-rank evaluation packet annihilates all of them at once.
-/

namespace GaloisForLFunctions.SelbergClass.DirichletSeries

open ArithmeticFunction HTGeometry Filter
open scoped Classical

noncomputable section

/-- Fractions whose prime-coordinate derivatives vanish eventually along a filter. -/
def primeFilterCoefficientField (F : Filter Nat.Primes) :
    IntermediateField ℂ arithmeticFunctionFractionField where
  carrier := {x | ∀ᶠ p in F, primeFractionDerivation p x = 0}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro x y hx hy
    filter_upwards [hx, hy] with p hpx hpy
    simp only [map_add, hpx, hpy, add_zero]
  mul_mem' := by
    intro x y hx hy
    filter_upwards [hx, hy] with p hpx hpy
    simp only [Derivation.leibniz, hpx, hpy, smul_zero, add_zero]
  algebraMap_mem' := by
    intro c
    exact Eventually.of_forall fun p => (primeFractionDerivation p).map_algebraMap c
  inv_mem' := by
    intro x hx
    filter_upwards [hx] with p hp
    simp only [(primeFractionDerivation p).leibniz_inv, hp, smul_zero]

@[simp]
theorem mem_primeFilterCoefficientField_iff (F : Filter Nat.Primes)
    (x : arithmeticFunctionFractionField) :
    x ∈ primeFilterCoefficientField F ↔ ∀ᶠ p in F, primeFractionDerivation p x = 0 :=
  Iff.rfl

/-- A finer filter permits a larger coefficient field. -/
theorem primeFilterCoefficientField_antitone : Antitone primeFilterCoefficientField := by
  intro F G hFG x hx
  exact hFG hx

/-- Linear independence of prime coefficient vectors modulo eventual equality. -/
def FilterCoefficientIndependent {I : Type*} [Fintype I]
    (F : Filter Nat.Primes) (a : I → Nat.Primes → ℂ) : Prop :=
  ∀ c : I → ℂ, (∀ᶠ p in F, ∑ i, c i * a i p = 0) → c = 0

/-- Every filter-large prime set contains a full-rank evaluation packet. -/
theorem FilterCoefficientIndependent.exists_fullRank_packet
    {I : Type*} [Fintype I] [DecidableEq I]
    {F : Filter Nat.Primes} {a : I → Nat.Primes → ℂ}
    (h : FilterCoefficientIndependent F a) {S : Set Nat.Primes} (hS : S ∈ F) :
    ∃ points : I → Nat.Primes, (∀ i, points i ∈ S) ∧
      IsUnit (Matrix.of fun row i => a i (points row) : Matrix I I ℂ) := by
  have hlin : LinearIndependent ℂ (fun i (p : S) => a i p.1) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hzero : c = 0 := h c (by
      filter_upwards [hS] with p hp
      have heval := congrFun hc (⟨p, hp⟩ : S)
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using heval)
    exact congrFun hzero i
  obtain ⟨points, hpoints⟩ :=
    HTGeometry.exists_fullRank_evaluation_packet (fun i (p : S) => a i p.1) hlin
  exact ⟨fun i => (points i).1, fun i => (points i).2, hpoints⟩

/-- All coefficients of one polynomial are constant in a filter-large set of prime directions. -/
theorem eventually_polynomial_coeff_derivation_eq_zero
    {I : Type*} (F : Filter Nat.Primes)
    (P : MvPolynomial I (primeFilterCoefficientField F)) :
    ∀ᶠ p in F, ∀ s, primeFractionDerivation p (P.coeff s).1 = 0 := by
  have hs : ∀ᶠ p in F, ∀ s ∈ P.support,
      primeFractionDerivation p (P.coeff s).1 = 0 := by
    exact (Filter.eventually_all_finset P.support).mpr fun s _ => (P.coeff s).2
  filter_upwards [hs] with p hp s
  by_cases hmem : s ∈ P.support
  · exact hp s hmem
  · rw [MvPolynomial.notMem_support_iff.mp hmem]
    exact map_zero _

/-- A square invertible prime evaluation matrix proves independence over its common kernel. -/
theorem algebraicIndependent_primeColumns_over_commonKernel
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → Nat.Primes → ℂ) (points : I → Nat.Primes)
    (hpacket : IsUnit (Matrix.of fun row i => a i (points row) : Matrix I I ℂ)) :
    AlgebraicIndependent (primeCommonKernelField points)
      (fun i => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (arithmeticOfPrimeColumn (a i))) := by
  let K := primeCommonKernelField points
  let g : I → arithmeticFunctionFractionField := fun i =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (arithmeticOfPrimeColumn (a i))
  let M : Matrix I I K :=
    (algebraMap ℂ K).mapMatrix (Matrix.of fun row i => a i (points row))
  have hM : IsUnit M := hpacket.map (RingHom.mapMatrix (algebraMap ℂ K))
  refine algebraicIndependent_of_jacobian (K := K) g
    (fun i => primeCommonKernelDerivation points i)
    (fun i x y => map_add (primeCommonKernelDerivation points i) x y)
    (fun i x y => by
      simpa only [Algebra.smul_def] using! (primeCommonKernelDerivation points i).leibniz x y)
    (fun i c => (primeCommonKernelDerivation points i).map_algebraMap c) M hM ?_
  intro i j
  change primeFractionDerivation (points i)
      (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (arithmeticOfPrimeColumn (a j))) = _
  rw [primeFractionDerivation_arithmeticOfPrimeColumn]
  exact IsScalarTower.algebraMap_apply ℂ K arithmeticFunctionFractionField (a j (points i))

/-- Prime columns independent modulo the filter stay algebraically independent over its entire
coefficient field. The evaluation packet is chosen separately for each polynomial relation. -/
theorem algebraicIndependent_primeColumns_over_filterField
    {I : Type*} [Fintype I] [DecidableEq I]
    (F : Filter Nat.Primes) (a : I → Nat.Primes → ℂ)
    (h : FilterCoefficientIndependent F a) :
    AlgebraicIndependent (primeFilterCoefficientField F)
      (fun i => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (arithmeticOfPrimeColumn (a i))) := by
  rw [algebraicIndependent_iff]
  intro P hP
  obtain ⟨points, hpoints, hpacket⟩ := h.exists_fullRank_packet
    (eventually_polynomial_coeff_derivation_eq_zero F P)
  let K := primeCommonKernelField points
  let g : I → arithmeticFunctionFractionField := fun i =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (arithmeticOfPrimeColumn (a i))
  let c : (I →₀ ℕ) → K := fun s => ⟨(P.coeff s).1, fun j => hpoints j s⟩
  let Q : MvPolynomial I K := ∑ s ∈ P.support, MvPolynomial.monomial s (c s)
  have hmap : MvPolynomial.map (algebraMap K arithmeticFunctionFractionField) Q =
      MvPolynomial.map
        (algebraMap (primeFilterCoefficientField F) arithmeticFunctionFractionField) P := by
    calc
      _ = ∑ s ∈ P.support, MvPolynomial.monomial s
          ((P.coeff s).1 : arithmeticFunctionFractionField) := by
        simp only [Q, map_sum, MvPolynomial.map_monomial]
        rfl
      _ = _ := by
        conv_rhs => rw [P.as_sum]
        simp only [map_sum, MvPolynomial.map_monomial]
        rfl
  have hQ : MvPolynomial.aeval g Q = 0 := by
    have heval := congrArg (MvPolynomial.eval g) hmap
    have heq : MvPolynomial.aeval g Q = MvPolynomial.aeval g P := by
      simpa only [MvPolynomial.aeval_def, MvPolynomial.eval_map] using heval
    exact heq.trans hP
  have hzero :=
    (algebraicIndependent_primeColumns_over_commonKernel a points hpacket).eq_zero_of_aeval_eq_zero Q hQ
  apply MvPolynomial.map_injective
    (algebraMap (primeFilterCoefficientField F) arithmeticFunctionFractionField)
    (FaithfulSMul.algebraMap_injective _ _)
  rw [← hmap, hzero, _root_.map_zero, _root_.map_zero]

/-- A linear combination of columns has the corresponding linear combination of prime derivatives. -/
theorem primeFractionDerivation_sum_primeColumns
    {I : Type*} [Fintype I] (a : I → Nat.Primes → ℂ) (c : I → ℂ) (p : Nat.Primes) :
    primeFractionDerivation p
      (∑ i, algebraMap ℂ arithmeticFunctionFractionField (c i) *
        algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (arithmeticOfPrimeColumn (a i))) =
      algebraMap ℂ arithmeticFunctionFractionField (∑ i, c i * a i p) := by
  simp only [map_sum, Derivation.leibniz, Derivation.map_algebraMap,
    primeFractionDerivation_arithmeticOfPrimeColumn, smul_eq_mul, mul_zero, add_zero, map_mul]

/-- Exact criterion: algebraic independence of prime columns is linear independence of their
coefficient vectors modulo the filter. No infinitude or properness assumption on the filter is
needed; the criterion also detects the degenerate cases. -/
theorem algebraicIndependent_primeColumns_over_filterField_iff
    {I : Type*} [Fintype I] [DecidableEq I]
    (F : Filter Nat.Primes) (a : I → Nat.Primes → ℂ) :
    AlgebraicIndependent (primeFilterCoefficientField F)
        (fun i => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (arithmeticOfPrimeColumn (a i))) ↔
      FilterCoefficientIndependent F a := by
  constructor
  · intro hAI c hc
    let x : I → arithmeticFunctionFractionField := fun i =>
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (arithmeticOfPrimeColumn (a i))
    let r : arithmeticFunctionFractionField :=
      ∑ i, algebraMap ℂ arithmeticFunctionFractionField (c i) * x i
    have hr : r ∈ primeFilterCoefficientField F := by
      filter_upwards [hc] with p hp
      change primeFractionDerivation p
        (∑ i, algebraMap ℂ arithmeticFunctionFractionField (c i) *
          algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
            (arithmeticOfPrimeColumn (a i))) = 0
      rw [primeFractionDerivation_sum_primeColumns, hp, _root_.map_zero]
    let k : primeFilterCoefficientField F := ⟨r, hr⟩
    let P : MvPolynomial I (primeFilterCoefficientField F) :=
      MvPolynomial.C (-k) +
        ∑ i, MvPolynomial.C (algebraMap ℂ (primeFilterCoefficientField F) (c i)) *
          MvPolynomial.X i
    have hPeval : MvPolynomial.aeval x P = 0 := by
      simp only [P, map_add, map_neg, MvPolynomial.aeval_C, map_sum, map_mul,
        MvPolynomial.aeval_X]
      change -r + r = 0
      exact neg_add_cancel r
    have hzero := hAI.eq_zero_of_aeval_eq_zero P hPeval
    funext i
    have hmon : (0 : I →₀ ℕ) ≠ Finsupp.single i 1 :=
      Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero)
    have hcoeff := congrArg (fun Q : MvPolynomial I (primeFilterCoefficientField F) =>
      Q.coeff (Finsupp.single i 1)) hzero
    simpa [P, MvPolynomial.coeff_add, MvPolynomial.coeff_C,
      MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_X, Finsupp.single_eq_single_iff, hmon] using hcoeff
  · exact algebraicIndependent_primeColumns_over_filterField F a

#print axioms algebraicIndependent_primeColumns_over_filterField_iff

end
end GaloisForLFunctions.SelbergClass.DirichletSeries
