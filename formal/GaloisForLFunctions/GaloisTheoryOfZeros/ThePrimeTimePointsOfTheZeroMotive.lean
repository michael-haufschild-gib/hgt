import GaloisForLFunctions.GaloisTheoryOfZeros.TheIntegralZeroMotive
import GaloisForLFunctions.RHTower.PrimeSourceCancellationBudget
import GaloisForLFunctions.HTGeometry.IncommensuratePeriodMeromorphicModel

/-!
# Prime-time points of the integral zero motive

The coordinate algebra of the full integral zero motive is the complex group
algebra of the actual integer zero relation group. Its exponential evaluation
at every prime logarithm outside any finite exceptional set is injective.
Prime-time points are therefore Zariski
dense in this coordinate-algebra sense, without any independence assumption.

Every polynomial identity at prime times is determined exactly by grouping
monomials with equal actual zero exponent sums. Prime-log uniqueness for
entire functions of finite exponential type and independence of exponential
characters prove the result on the full, unbounded zero group.
-/

noncomputable section
set_option autoImplicit false
open Complex Set RHTower
open scoped BigOperators
namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- Every cofinite prime-log family separates finite sums of distinct complex exponentials. -/
theorem exponential_coefficients_eq_zero_of_cofinite_prime_values {ι : Type*}
    (s : Finset ι) (μ c : ι → ℂ) (hμ : Set.InjOn μ s) (E : Finset ℕ)
    (hprime : ∀ p : ℕ, p.Prime → p ∉ E →
      ∑ i ∈ s, c i*Complex.exp (μ i*(Real.log p : ℂ)) = 0) :
    ∀ i ∈ s, c i = 0 := by
  classical
  let A : ℝ := ∑ i ∈ s, ‖μ i‖
  let C : ℝ := 1+∑ i ∈ s, ‖c i‖
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => norm_nonneg (μ i)
  have hC : 1 ≤ C := by
    have h := Finset.sum_nonneg (s := s) (fun i _ => norm_nonneg (c i))
    dsimp [C]
    linarith only [h]
  have hgrow (z : ℂ) :
      ‖∑ i ∈ s, c i*Complex.exp (μ i*z)‖ ≤ C*Real.exp (A*‖z‖) := by
    calc
      ‖∑ i ∈ s, c i*Complex.exp (μ i*z)‖ ≤
          ∑ i ∈ s, ‖c i*Complex.exp (μ i*z)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ s, ‖c i‖*Real.exp (A*‖z‖) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        calc
          ‖Complex.exp (μ i*z)‖ ≤ Real.exp ‖μ i*z‖ := Complex.norm_exp_le_exp_norm _
          _ ≤ Real.exp (A*‖z‖) := by
            apply Real.exp_le_exp.mpr
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right
              (Finset.single_le_sum (fun j _ => norm_nonneg (μ j)) hi) (norm_nonneg z)
      _ = (∑ i ∈ s, ‖c i‖)*Real.exp (A*‖z‖) := (Finset.sum_mul _ _ _).symm
      _ ≤ C*Real.exp (A*‖z‖) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        dsimp [C]
        linarith
  have hzero : (fun z : ℂ => ∑ i ∈ s, c i*Complex.exp (μ i*z)) = 0 :=
    GaloisForLFunctions.RHTower.PrimeCancellation.eq_zero_of_exponentialType_of_cofinite_primeLog_zeros
      (by fun_prop) hA hC hgrow E hprime
  exact HTGeometry.exp_coeff_eq_zero_of_sum_eq_zero s μ hμ c
    (fun z => congrFun hzero z)

/-- All prime logarithms separate finite sums of distinct complex exponentials. -/
theorem exponential_coefficients_eq_zero_of_prime_values {ι : Type*}
    (s : Finset ι) (μ c : ι → ℂ) (hμ : Set.InjOn μ s)
    (hprime : ∀ p : ℕ, p.Prime →
      ∑ i ∈ s, c i*Complex.exp (μ i*(Real.log p : ℂ)) = 0) :
    ∀ i ∈ s, c i = 0 :=
  exponential_coefficients_eq_zero_of_cofinite_prime_values s μ c hμ ∅
    (fun p hp _ => hprime p hp)

/-- The coordinate algebra of the full original integral zero motive. -/
abbrev ZeroMotiveAlgebra := AddMonoidAlgebra ℂ rawZeroRelationGroup

private def zeroExponentialMonoidHom (u : ℂ) : Multiplicative rawZeroRelationGroup →* ℂ where
  toFun z := Complex.exp (u*(z.toAdd : ℂ))
  map_one' := by
    change Complex.exp (u*0) = 1
    rw [mul_zero,Complex.exp_zero]
  map_mul' x y := by
    change Complex.exp (u*((x.toAdd : ℂ)+(y.toAdd : ℂ))) = _
    rw [mul_add,Complex.exp_add]

/-- Evaluate a regular function on the complex-time exponential character. -/
def zeroMotiveEvaluation (u : ℂ) : ZeroMotiveAlgebra →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ rawZeroRelationGroup (zeroExponentialMonoidHom u)

/-- The exponential character evaluates a group-algebra basis element by its actual exponent. -/
theorem zeroMotiveEvaluation_single (u : ℂ) (z : rawZeroRelationGroup) (c : ℂ) :
    zeroMotiveEvaluation u (AddMonoidAlgebra.single z c) = c*Complex.exp (u*(z : ℂ)) := by
  simp only [zeroMotiveEvaluation,AddMonoidAlgebra.lift_single,smul_eq_mul]
  rfl

/-- Evaluation is the finite exponential sum on the exact coefficient support. -/
theorem zeroMotiveEvaluation_eq_sum (u : ℂ) (f : ZeroMotiveAlgebra) :
    zeroMotiveEvaluation u f =
      ∑ z ∈ f.coeff.support, f.coeff z*Complex.exp ((z : ℂ)*u) := by
  rw [zeroMotiveEvaluation,AddMonoidAlgebra.lift_apply]
  change (∑ z ∈ f.coeff.support, f.coeff z*Complex.exp (u*(z : ℂ))) = _
  simp_rw [mul_comm u]

/-- The original real-time flow is the point used by the coordinate-algebra evaluation. -/
theorem zeroMotiveEvaluation_flow (u : ℝ) (z : rawZeroRelationGroup) :
    zeroMotiveEvaluation (u : ℂ) (AddMonoidAlgebra.single z 1) =
      ((rawZeroMotiveFlow u z).toMul : ℂ) := by
  rw [zeroMotiveEvaluation_single,one_mul]
  rfl

/-- All prime-time values of a regular function on the full zero motive. -/
def primeZeroEvaluation : ZeroMotiveAlgebra →ₐ[ℂ] (Nat.Primes → ℂ) :=
  AlgHom.pi (fun p => zeroMotiveEvaluation (Real.log (p : ℕ) : ℂ))

/-- Prime-time points distinguish every regular function on the full integral zero motive. -/
theorem primeZeroEvaluation_injective : Function.Injective primeZeroEvaluation := by
  apply (injective_iff_map_eq_zero _).mpr
  intro f hf
  have hc : ∀ z ∈ f.coeff.support, f.coeff z = 0 :=
    exponential_coefficients_eq_zero_of_prime_values f.coeff.support
      (fun z : rawZeroRelationGroup => (z : ℂ)) f.coeff
      (fun _ _ _ _ he => Subtype.ext he) (by
        intro p hp
        have h := congrFun hf (⟨p,hp⟩ : Nat.Primes)
        change zeroMotiveEvaluation (Real.log p : ℂ) f = 0 at h
        rwa [zeroMotiveEvaluation_eq_sum] at h)
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro z
  by_cases hz : z ∈ f.coeff.support
  · exact hc z hz
  · exact Finsupp.notMem_support_iff.mp hz

/-- Equality on all prime-time points is equality in the coordinate algebra. -/
theorem zeroMotive_eq_iff_prime_values (f g : ZeroMotiveAlgebra) :
    f = g ↔ ∀ p : ℕ, p.Prime →
      zeroMotiveEvaluation (Real.log p : ℂ) f = zeroMotiveEvaluation (Real.log p : ℂ) g := by
  constructor
  · rintro rfl p hp
    rfl
  · intro h
    apply primeZeroEvaluation_injective
    funext p
    exact h p p.property

/-- Each zero defines its character coordinate in the full motive algebra. -/
def zeroMotiveCoordinates : MvPolynomial XiZeroCopy ℂ →ₐ[ℂ] ZeroMotiveAlgebra :=
  MvPolynomial.aeval (fun q => AddMonoidAlgebra.single (rawZeroRelationRoot q) 1)

/-- The actual exponential values of all zeros at a prime time. -/
def zeroPrimeCoordinates (p : ℕ) : MvPolynomial XiZeroCopy ℂ →ₐ[ℂ] ℂ :=
  MvPolynomial.aeval (fun q => Complex.exp ((Real.log p : ℂ)*(q.1 : ℂ)))

/-- Prime evaluation factors through the integral zero-motive coordinate algebra. -/
theorem zeroPrimeCoordinates_factorization (p : ℕ) :
    zeroPrimeCoordinates p =
      (zeroMotiveEvaluation (Real.log p : ℂ)).comp zeroMotiveCoordinates := by
  apply MvPolynomial.algHom_ext
  intro q
  simp only [zeroPrimeCoordinates,zeroMotiveCoordinates,MvPolynomial.aeval_X,
    AlgHom.comp_apply,zeroMotiveEvaluation_single,one_mul]
  rfl

/-- Polynomial identities at every prime time are exactly the identities in the zero motive. -/
theorem zeroPolynomial_prime_relation_iff (P : MvPolynomial XiZeroCopy ℂ) :
    (∀ p : ℕ, p.Prime → zeroPrimeCoordinates p P = 0) ↔ zeroMotiveCoordinates P = 0 := by
  constructor
  · intro h
    apply primeZeroEvaluation_injective
    rw [map_zero]
    funext p
    change zeroMotiveEvaluation (Real.log (p : ℕ) : ℂ) (zeroMotiveCoordinates P) = 0
    rw [← AlgHom.comp_apply,← zeroPrimeCoordinates_factorization]
    exact h p p.property
  · intro h p hp
    rw [zeroPrimeCoordinates_factorization,AlgHom.comp_apply,h,map_zero]

/-- The exponent of a zero-coordinate monomial, in the actual integral relation group. -/
def zeroMonomialExponent (m : XiZeroCopy →₀ ℕ) : rawZeroRelationGroup :=
  m.sum (fun q n => n • rawZeroRelationRoot q)

private theorem zeroMonomialExponent_add (m n : XiZeroCopy →₀ ℕ) :
    zeroMonomialExponent (m+n) = zeroMonomialExponent m+zeroMonomialExponent n :=
  Finsupp.sum_add_index' (fun _ => zero_nsmul _) (fun _ _ _ => add_nsmul _ _ _)

private theorem zeroMonomialExponent_single (q : XiZeroCopy) (n : ℕ) :
    zeroMonomialExponent (Finsupp.single q n) = n • rawZeroRelationRoot q := by
  simp only [zeroMonomialExponent,Finsupp.sum_single_index,zero_nsmul]

/-- Every zero monomial maps to the basis element indexed by its actual exponent sum. -/
theorem zeroMotiveCoordinates_monomial (m : XiZeroCopy →₀ ℕ) (c : ℂ) :
    zeroMotiveCoordinates (MvPolynomial.monomial m c) =
      AddMonoidAlgebra.single (zeroMonomialExponent m) c := by
  classical
  induction m using Finsupp.induction with
  | zero =>
    simp [zeroMotiveCoordinates,zeroMonomialExponent]
  | @single_add q n m hq hn ih =>
    rw [MvPolynomial.monomial_single_add,map_mul,map_pow,ih]
    simp [zeroMotiveCoordinates,zeroMonomialExponent_add,zeroMonomialExponent_single,
      AddMonoidAlgebra.single_pow,AddMonoidAlgebra.single_mul_single]

/-- Coefficients collect exactly the monomials with equal actual zero exponent sums. -/
theorem zeroMotiveCoordinates_coefficient (P : MvPolynomial XiZeroCopy ℂ)
    (z : rawZeroRelationGroup) :
    (zeroMotiveCoordinates P).coeff z =
      ∑ m ∈ P.support, if zeroMonomialExponent m = z then MvPolynomial.coeff m P else 0 := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum,AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro m hm
  rw [zeroMotiveCoordinates_monomial,AddMonoidAlgebra.coeff_single]
  simp only [Finsupp.single_apply]

/-- Complete prime-time polynomial relation test, with no assumed independence of zero ordinates. -/
theorem zeroPolynomial_prime_relation_iff_grouped_coefficients (P : MvPolynomial XiZeroCopy ℂ) :
    (∀ p : ℕ, p.Prime → zeroPrimeCoordinates p P = 0) ↔
      ∀ z : rawZeroRelationGroup,
        (∑ m ∈ P.support, if zeroMonomialExponent m = z then MvPolynomial.coeff m P else 0) = 0 := by
  rw [zeroPolynomial_prime_relation_iff]
  simp_rw [← zeroMotiveCoordinates_coefficient]
  constructor
  · intro h z
    rw [h]
    rfl
  · intro h
    apply AddMonoidAlgebra.coeff_injective
    exact Finsupp.ext h

private def rawCharacterMonoidHom (χ : RawZeroMotivePoint) :
    Multiplicative rawZeroRelationGroup →* ℂ where
  toFun z := ((χ z.toAdd).toMul : ℂ)
  map_one' := by
    change ((χ 0).toMul : ℂ) = 1
    rw [map_zero]
    rfl
  map_mul' x y := by
    change ((χ (x.toAdd+y.toAdd)).toMul : ℂ) = _
    rw [map_add]
    rfl

/-- Every complex character of the zero relation group is a point of its coordinate algebra. -/
def zeroMotiveCharacterEvaluation (χ : RawZeroMotivePoint) : ZeroMotiveAlgebra →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ rawZeroRelationGroup (rawCharacterMonoidHom χ)

theorem zeroMotiveCharacterEvaluation_single (χ : RawZeroMotivePoint)
    (z : rawZeroRelationGroup) (c : ℂ) :
    zeroMotiveCharacterEvaluation χ (AddMonoidAlgebra.single z c) =
      c*((χ z).toMul : ℂ) := by
  rw [zeroMotiveCharacterEvaluation,AddMonoidAlgebra.lift_single]
  rfl

private def zeroMotivePointCharacter (f : ZeroMotiveAlgebra →ₐ[ℂ] ℂ) : RawZeroMotivePoint where
  toFun z := Additive.ofMul {
    val := f (AddMonoidAlgebra.single z 1)
    inv := f (AddMonoidAlgebra.single (-z) 1)
    val_inv := by
      rw [← map_mul,AddMonoidAlgebra.single_mul_single,add_neg_cancel,one_mul]
      exact map_one f
    inv_val := by
      rw [← map_mul,AddMonoidAlgebra.single_mul_single,neg_add_cancel,one_mul]
      exact map_one f }
  map_zero' := by
    apply Additive.toMul.injective
    apply Units.ext
    exact map_one f
  map_add' z w := by
    apply Additive.toMul.injective
    apply Units.ext
    change f (AddMonoidAlgebra.single (z+w) 1) =
      f (AddMonoidAlgebra.single z 1)*f (AddMonoidAlgebra.single w 1)
    rw [← map_mul,AddMonoidAlgebra.single_mul_single,one_mul]

/-- Complex points of the coordinate algebra are exactly all characters of the original zero motive. -/
def zeroMotivePointEquiv : RawZeroMotivePoint ≃ (ZeroMotiveAlgebra →ₐ[ℂ] ℂ) where
  toFun := zeroMotiveCharacterEvaluation
  invFun := zeroMotivePointCharacter
  left_inv χ := by
    apply AddMonoidHom.ext
    intro z
    apply Additive.toMul.injective
    apply Units.ext
    change zeroMotiveCharacterEvaluation χ (AddMonoidAlgebra.single z 1) = ((χ z).toMul : ℂ)
    rw [zeroMotiveCharacterEvaluation_single,one_mul]
  right_inv f := by
    apply (AddMonoidAlgebra.lift ℂ ℂ rawZeroRelationGroup).symm.injective
    apply MonoidHom.ext
    intro z
    change zeroMotiveCharacterEvaluation (zeroMotivePointCharacter f)
      (AddMonoidAlgebra.single z.toAdd 1) = f (AddMonoidAlgebra.single z.toAdd 1)
    rw [zeroMotiveCharacterEvaluation_single,one_mul]
    rfl

/-- The established real-time flow agrees with the corresponding algebra point. -/
theorem zeroMotivePointEquiv_flow (u : ℝ) :
    zeroMotivePointEquiv (rawZeroMotiveFlow u) = zeroMotiveEvaluation (u : ℂ) := by
  apply (AddMonoidAlgebra.lift ℂ ℂ rawZeroRelationGroup).symm.injective
  apply MonoidHom.ext
  intro z
  rfl

/-- Every cofinite prime family determines a regular function of the full zero motive. -/
theorem zeroMotive_eq_zero_of_cofinite_prime_values (E : Finset ℕ) (f : ZeroMotiveAlgebra)
    (h : ∀ p : ℕ, p.Prime → p ∉ E → zeroMotiveEvaluation (Real.log p : ℂ) f = 0) : f = 0 := by
  have hc : ∀ z ∈ f.coeff.support, f.coeff z = 0 :=
    exponential_coefficients_eq_zero_of_cofinite_prime_values f.coeff.support
      (fun z : rawZeroRelationGroup => (z : ℂ)) f.coeff
      (fun _ _ _ _ he => Subtype.ext he) E (by
        intro p hp hpE
        simpa only [zeroMotiveEvaluation_eq_sum] using h p hp hpE)
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro z
  by_cases hz : z ∈ f.coeff.support
  · exact hc z hz
  · exact Finsupp.notMem_support_iff.mp hz

/-- Evaluation after any finite set of primes is discarded. -/
def primeZeroEvaluationOutside (E : Finset ℕ) :
    ZeroMotiveAlgebra →ₐ[ℂ] ({p : Nat.Primes // (p : ℕ) ∉ E} → ℂ) :=
  AlgHom.pi (fun p => zeroMotiveEvaluation (Real.log (p.1 : ℕ) : ℂ))

/-- Removing finitely many primes preserves faithful sampling of the full coordinate algebra. -/
theorem primeZeroEvaluationOutside_injective (E : Finset ℕ) :
    Function.Injective (primeZeroEvaluationOutside E) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro f hf
  apply zeroMotive_eq_zero_of_cofinite_prime_values E f
  intro p hp hpE
  exact congrFun hf (⟨⟨p,hp⟩,hpE⟩ : {p : Nat.Primes // (p : ℕ) ∉ E})

/-- Every nonzero regular function is detected beyond any prescribed finite prime set. -/
theorem zeroMotive_nonzero_prime_witness (f : ZeroMotiveAlgebra) (hf : f ≠ 0) (E : Finset ℕ) :
    ∃ p : ℕ, p.Prime ∧ p ∉ E ∧ zeroMotiveEvaluation (Real.log p : ℂ) f ≠ 0 := by
  by_contra h
  push Not at h
  exact hf (zeroMotive_eq_zero_of_cofinite_prime_values E f h)

/-- Discarding any finite set of primes leaves the same complete polynomial relation ideal. -/
theorem zeroPolynomial_cofinite_prime_relation_iff (E : Finset ℕ) (P : MvPolynomial XiZeroCopy ℂ) :
    (∀ p : ℕ, p.Prime → p ∉ E → zeroPrimeCoordinates p P = 0) ↔ zeroMotiveCoordinates P = 0 := by
  constructor
  · intro h
    apply zeroMotive_eq_zero_of_cofinite_prime_values E
    intro p hp hpE
    rw [← AlgHom.comp_apply,← zeroPrimeCoordinates_factorization]
    exact h p hp hpE
  · intro h p hp hpE
    rw [zeroPrimeCoordinates_factorization,AlgHom.comp_apply,h,map_zero]

/-- The same exponent-collision test characterizes identities on every cofinite prime family. -/
theorem zeroPolynomial_cofinite_relation_iff_grouped_coefficients
    (E : Finset ℕ) (P : MvPolynomial XiZeroCopy ℂ) :
    (∀ p : ℕ, p.Prime → p ∉ E → zeroPrimeCoordinates p P = 0) ↔
      ∀ z : rawZeroRelationGroup,
        (∑ m ∈ P.support, if zeroMonomialExponent m = z then MvPolynomial.coeff m P else 0) = 0 :=
  (zeroPolynomial_cofinite_prime_relation_iff E P).trans
    ((zeroPolynomial_prime_relation_iff P).symm.trans
      (zeroPolynomial_prime_relation_iff_grouped_coefficients P))

end GaloisForLFunctions.GaloisTheoryOfZeros
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.exponential_coefficients_eq_zero_of_prime_values
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeZeroEvaluation_injective
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotive_eq_iff_prime_values
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotiveEvaluation_flow
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroPolynomial_prime_relation_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotiveCoordinates_monomial
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotiveCoordinates_coefficient
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroPolynomial_prime_relation_iff_grouped_coefficients
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotivePointEquiv
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotivePointEquiv_flow
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeZeroEvaluationOutside_injective
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotive_nonzero_prime_witness
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroPolynomial_cofinite_relation_iff_grouped_coefficients
