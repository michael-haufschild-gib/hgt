import GaloisForLFunctions.HTGeometry.FiniteBlaschkeNumberOperator
import GaloisForLFunctions.HTGeometry.HardyBlaschkeCoefficients
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSievePrimeKernelIsABoundedOperator

/-!
# The actual finite-sieve operator has the torsion-adjunction eigenbasis

The complete Blaschke product basis diagonalizes the original logarithmic
number operator minus the actual prime kernel. Its energies are logarithmic
degree plus the tame different and one shared Euler constant.
-/

noncomputable section

open scoped Classical InnerProductSpace LinearPMap

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open HTGeometry ArithmeticIntersectionTheory

/-- The actual weighted number/KMS operator in full valuation coordinates. -/
def sieveValuationNumberOperator (Q : Finset Nat.Primes) :
    FiniteNumberSpace Q →ₗ.[ℂ] FiniteNumberSpace Q :=
  finiteBlaschkeNumberOperator (fun p : Q => primeBlaschkeParameter p)
    (fun p => primeBlaschkeParameter_norm_lt_one p)
    (fun p => Real.log ((p : Nat.Primes) : ℕ)) (sieveEuler Q)

/-- The matched finite-prime operator on the actual supported-integer carrier. -/
def sieveAdjunctionOperator (Q : Finset Nat.Primes) :
    SieveClassL2 Q →ₗ.[ℂ] SieveClassL2 Q :=
  unitaryConjugateLinearPMap (sieveCoordinateUnitary Q) (sieveValuationNumberOperator Q)

/-- The arithmetic energy of a supported-integer excitation. -/
def matchedSieveEnergy (Q : Finset Nat.Primes) (m : SieveClass Q) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (m : ℕ) + tameDifferent (m : ℕ)

/-- The explicit complete product basis, labelled by actual supported integers. -/
def sieveAdjunctionBasis (Q : Finset Nat.Primes) : HilbertBasis (SieveClass Q) ℂ (SieveClassL2 Q) :=
  HilbertBasis.ofRepr ((sieveCoordinateUnitary Q).trans
    ((finiteBlaschkeBasis (fun p : Q => primeBlaschkeParameter p)
      (fun p => primeBlaschkeParameter_norm_lt_one p)).repr.trans
        (sieveCoordinateUnitary Q).symm))

theorem sieveAdjunctionBasis_eq (Q : Finset Nat.Primes) (m : SieveClass Q) :
    sieveAdjunctionBasis Q m = (sieveCoordinateUnitary Q).symm
      (finiteBlaschkeBasis (fun p : Q => primeBlaschkeParameter p)
        (fun p => primeBlaschkeParameter_norm_lt_one p) (sieveValuationEquiv Q m)) := by
  rw [← (sieveAdjunctionBasis Q).repr_symm_single m]
  change (sieveCoordinateUnitary Q).symm
    ((finiteBlaschkeBasis (fun p : Q => primeBlaschkeParameter p)
      (fun p => primeBlaschkeParameter_norm_lt_one p)).repr.symm
        (lpReindexEquiv (sieveValuationEquiv Q) (lp.single 2 m (1 : ℂ)))) = _
  rw [lpReindexEquiv_single, HilbertBasis.repr_symm_single]

theorem sieveCoordinateUnitary_basis (Q : Finset Nat.Primes) (m : SieveClass Q) :
    sieveCoordinateUnitary Q (sieveAdjunctionBasis Q m) =
      finiteBlaschkeBasis (fun p : Q => primeBlaschkeParameter p)
        (fun p => primeBlaschkeParameter_norm_lt_one p) (sieveValuationEquiv Q m) := by
  rw [sieveAdjunctionBasis_eq, LinearIsometryEquiv.apply_symm_apply]

/-- Every basis coefficient is the product of the explicit local ground/excitation coefficients. -/
theorem sieveAdjunctionBasis_apply (Q : Finset Nat.Primes) (m n : SieveClass Q) :
    sieveAdjunctionBasis Q m n = ∏ p : Q,
      hardyNumberBasis (primeBlaschkeParameter_norm_lt_one p)
        ((m : ℕ).factorization (p : Nat.Primes)) ((n : ℕ).factorization (p : Nat.Primes)) := by
  rw [sieveAdjunctionBasis_eq]
  exact lpFiniteProductBasis_apply Q _ _ _

/-- Closed coefficient formulas exhibit every normalized arithmetic eigenmode. -/
theorem sieveAdjunctionBasis_coefficients (Q : Finset Nat.Primes) (m n : SieveClass Q) :
    sieveAdjunctionBasis Q m n = ∏ p : Q,
      hardyBlaschkeCoefficient (primeBlaschkeParameter p)
        ((m : ℕ).factorization (p : Nat.Primes)) ((n : ℕ).factorization (p : Nat.Primes)) := by
  rw [sieveAdjunctionBasis_apply]
  simp_rw [hardyNumberBasis_coefficient]

theorem finiteNumberDegree_sieve (Q : Finset Nat.Primes) (e : Q → ℕ) :
    finiteNumberDegree (fun p : Q => Real.log ((p : Nat.Primes) : ℕ)) e =
      Real.log (((sieveValuationEquiv Q).symm e : ℕ) : ℝ) := by
  rw [log_sieveValuationEquiv_symm]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- The pulled-back domain is precisely the maximal logarithmically weighted domain. -/
theorem sieveAdjunctionOperator_domain (Q : Finset Nat.Primes) (x : SieveClassL2 Q) :
    x ∈ (sieveAdjunctionOperator Q).domain ↔
      Memℓp (fun n : SieveClass Q => (Real.log (n : ℕ) : ℂ) * x n) 2 := by
  change Memℓp (fun e : Q → ℕ =>
    (finiteNumberDegree (fun p : Q => Real.log ((p : Nat.Primes) : ℕ)) e : ℂ) *
      sieveCoordinateUnitary Q x e) 2 ↔ _
  simp only [finiteNumberDegree_sieve, sieveCoordinateUnitary, lpReindexEquiv_apply]
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal),
    memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
  exact (sieveValuationEquiv Q).symm.summable_iff
    (f := fun n : SieveClass Q => ‖(Real.log (n : ℕ) : ℂ) * x n‖ ^ (2 : ENNReal).toReal)

theorem sieveValuationCorrection_eq (Q : Finset Nat.Primes) :
    finiteBlaschkeCorrection (fun p : Q => primeBlaschkeParameter p)
      (fun p => primeBlaschkeParameter_norm_lt_one p)
      (fun p => Real.log ((p : Nat.Primes) : ℕ)) (sieveEuler Q) =
      (sieveEuler Q : ℂ) • 1 - sievePrimeCoordinateOperator Q := by
  rw [finiteBlaschkeCorrection, sievePrimeCoordinateOperator]
  conv_rhs => rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  module

/-- The literal action is logarithmic degree minus the actual prime kernel plus the shared constant. -/
theorem sieveAdjunctionOperator_apply (Q : Finset Nat.Primes)
    (x : (sieveAdjunctionOperator Q).domain) (n : SieveClass Q) :
    sieveAdjunctionOperator Q x n =
      ((Real.log (n : ℕ) + sieveEuler Q : ℝ) : ℂ) * (x : SieveClassL2 Q) n -
        sievePrimeOperator Q (x : SieveClassL2 Q) n := by
  change finiteBlaschkeNumberOperator (fun p : Q => primeBlaschkeParameter p)
    (fun p => primeBlaschkeParameter_norm_lt_one p)
    (fun p => Real.log ((p : Nat.Primes) : ℕ)) (sieveEuler Q)
    (unitaryConjugateDomainMap (sieveCoordinateUnitary Q) (sieveValuationNumberOperator Q) x)
      (sieveValuationEquiv Q n) = _
  rw [finiteBlaschkeNumberOperator_apply, sieveValuationCorrection_eq, finiteNumberDegree_sieve,
    Equiv.symm_apply_apply]
  change (sieveEuler Q : ℂ) * sieveCoordinateUnitary Q (x : SieveClassL2 Q)
      (sieveValuationEquiv Q n) -
      sievePrimeOperator Q (x : SieveClassL2 Q) n +
        (Real.log (n : ℕ) : ℂ) * sieveCoordinateUnitary Q (x : SieveClassL2 Q)
          (sieveValuationEquiv Q n) = _
  have hcoord : sieveCoordinateUnitary Q (x : SieveClassL2 Q)
      (sieveValuationEquiv Q n) = (x : SieveClassL2 Q) n := by
    change (x : SieveClassL2 Q) ((sieveValuationEquiv Q).symm (sieveValuationEquiv Q n)) = _
    rw [Equiv.symm_apply_apply]
  rw [hcoord]
  push_cast
  ring

theorem sieveAdjunctionOperator_isClosed (Q : Finset Nat.Primes) :
    (sieveAdjunctionOperator Q).IsClosed :=
  LinearPMap.IsClosed.unitaryConjugate
    (finiteBlaschkeNumberOperator_isClosed _ _ _ _)

theorem sieveAdjunctionOperator_formalSelfAdjoint (Q : Finset Nat.Primes) :
    (sieveAdjunctionOperator Q).IsFormalAdjoint (sieveAdjunctionOperator Q) :=
  LinearPMap.IsFormalAdjoint.unitaryConjugate (sieveCoordinateUnitary Q)
    (finiteBlaschkeNumberOperator_formalSelfAdjoint _ _ _ _)

theorem sieveAdjunctionOperator_isSelfAdjoint (Q : Finset Nat.Primes) :
    IsSelfAdjoint (sieveAdjunctionOperator Q) :=
  IsSelfAdjoint.unitaryConjugate (sieveCoordinateUnitary Q)
    (finiteBlaschkeNumberOperator_isSelfAdjoint _ _ _ _)

/-- The local Euler corrections cancel precisely on unexcited primes. -/
theorem finiteBlaschkeEnergy_sieve (Q : Finset Nat.Primes) (m : SieveClass Q) :
    finiteBlaschkeEnergy (fun p : Q => primeBlaschkeParameter p)
      (fun p => Real.log ((p : Nat.Primes) : ℕ)) (sieveEuler Q) (sieveValuationEquiv Q m) =
      matchedSieveEnergy Q m := by
  have hsum :
      (∑ p : Q, Real.log ((p : Nat.Primes) : ℕ) / (((p : Nat.Primes) : ℕ) - (1 : ℝ))) +
      (∑ p : Q, Real.log ((p : Nat.Primes) : ℕ) *
        hardyNumberEnergy (primeBlaschkeParameter p) (sieveValuationEquiv Q m p)) =
      finitePrimeExcitationEnergy Q (sieveValuationEquiv Q m) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    have h := congrArg (fun r : ℝ => Real.log ((p : Nat.Primes) : ℕ) * r)
      (hardyNumberEnergy_prime_add p (sieveValuationEquiv Q m p))
    linear_combination h
  rw [finitePrimeExcitationEnergy_eq, Equiv.symm_apply_apply] at hsum
  rw [finiteBlaschkeEnergy, sieveEuler, ← Finset.sum_coe_sort Q, matchedSieveEnergy]
  linear_combination hsum

theorem sieveAdjunctionBasis_mem_domain (Q : Finset Nat.Primes) (m : SieveClass Q) :
    sieveAdjunctionBasis Q m ∈ (sieveAdjunctionOperator Q).domain := by
  change sieveCoordinateUnitary Q (sieveAdjunctionBasis Q m) ∈ (sieveValuationNumberOperator Q).domain
  rw [sieveCoordinateUnitary_basis]
  exact finiteBlaschkeBasis_mem_domain _ _ _ _ _

/-- Exact eigenvector equations hold on the actual maximal logarithmic domain. -/
theorem sieveAdjunctionOperator_basis (Q : Finset Nat.Primes) (m : SieveClass Q) :
    sieveAdjunctionOperator Q ⟨sieveAdjunctionBasis Q m, sieveAdjunctionBasis_mem_domain Q m⟩ =
      (matchedSieveEnergy Q m : ℂ) • sieveAdjunctionBasis Q m := by
  apply (sieveCoordinateUnitary Q).injective
  rw [map_smul, sieveCoordinateUnitary_basis]
  change sieveCoordinateUnitary Q ((sieveCoordinateUnitary Q).symm (sieveValuationNumberOperator Q
    (unitaryConjugateDomainMap (sieveCoordinateUnitary Q) (sieveValuationNumberOperator Q)
      ⟨sieveAdjunctionBasis Q m, sieveAdjunctionBasis_mem_domain Q m⟩))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  have hd : unitaryConjugateDomainMap (sieveCoordinateUnitary Q) (sieveValuationNumberOperator Q)
      ⟨sieveAdjunctionBasis Q m, sieveAdjunctionBasis_mem_domain Q m⟩ =
      ⟨finiteBlaschkeBasis (fun p : Q => primeBlaschkeParameter p)
        (fun p => primeBlaschkeParameter_norm_lt_one p) (sieveValuationEquiv Q m),
        finiteBlaschkeBasis_mem_domain _ _ _ _ _⟩ :=
    Subtype.ext (sieveCoordinateUnitary_basis Q m)
  rw [hd]
  have h := finiteBlaschkeNumberOperator_basis
    (fun p : Q => primeBlaschkeParameter p)
    (fun p => primeBlaschkeParameter_norm_lt_one p)
    (fun p => Real.log ((p : Nat.Primes) : ℕ)) (sieveEuler Q) (sieveValuationEquiv Q m)
  rw [finiteBlaschkeEnergy_sieve] at h
  exact h

/-- Spectral coefficients identify the entire original maximal domain. -/
theorem sieveAdjunctionOperator_spectral_domain (Q : Finset Nat.Primes) (x : SieveClassL2 Q) :
    x ∈ (sieveAdjunctionOperator Q).domain ↔
      Memℓp (fun m => (matchedSieveEnergy Q m : ℂ) * (sieveAdjunctionBasis Q).repr x m) 2 :=
  closed_eigenbasis_domain_iff _ _ _ (sieveAdjunctionOperator_isClosed Q)
    (sieveAdjunctionOperator_formalSelfAdjoint Q) (sieveAdjunctionBasis_mem_domain Q)
    (sieveAdjunctionOperator_basis Q) x

theorem sieveAdjunctionOperator_spectral_action (Q : Finset Nat.Primes)
    (x : (sieveAdjunctionOperator Q).domain) (m : SieveClass Q) :
    (sieveAdjunctionBasis Q).repr (sieveAdjunctionOperator Q x) m =
      (matchedSieveEnergy Q m : ℂ) * (sieveAdjunctionBasis Q).repr (x : SieveClassL2 Q) m :=
  eigenbasis_graph_coordinates _ _ _ (sieveAdjunctionOperator_formalSelfAdjoint Q)
    (sieveAdjunctionBasis_mem_domain Q) (sieveAdjunctionOperator_basis Q) x m

/-- Distinct supported integers have distinct eigenvalues. -/
theorem matchedSieveEnergy_injective (Q : Finset Nat.Primes) :
    Function.Injective (matchedSieveEnergy Q) := by
  intro m n h
  apply sieveAdjunctionEnergy_injective Q
  dsimp only [matchedSieveEnergy] at h
  linarith only [h]

/-- Every eigenspace at an arithmetic energy is exactly its displayed basis line. -/
theorem sieveAdjunctionOperator_eigenvector_line (Q : Finset Nat.Primes)
    (m : SieveClass Q) (x : (sieveAdjunctionOperator Q).domain)
    (hx : sieveAdjunctionOperator Q x = (matchedSieveEnergy Q m : ℂ) • (x : SieveClassL2 Q)) :
    (x : SieveClassL2 Q) = (sieveAdjunctionBasis Q).repr (x : SieveClassL2 Q) m •
      sieveAdjunctionBasis Q m := by
  apply (sieveAdjunctionBasis Q).repr.injective
  rw [map_smul, HilbertBasis.repr_self]
  apply lp.ext
  funext j
  by_cases hj : j = m
  · subst j
    simp only [lp.coeFn_smul, Pi.smul_apply, lp.single_apply, Pi.single_eq_same,
      smul_eq_mul, mul_one]
  · change (sieveAdjunctionBasis Q).repr (x : SieveClassL2 Q) j =
      (sieveAdjunctionBasis Q).repr (x : SieveClassL2 Q) m *
        (lp.single 2 m (1 : ℂ) : SieveClassL2 Q) j
    rw [lp.single_apply_ne _ _ _ hj, mul_zero]
    by_contra hne
    have hc := sieveAdjunctionOperator_spectral_action Q x j
    rw [hx, map_smul] at hc
    change (matchedSieveEnergy Q m : ℂ) * (sieveAdjunctionBasis Q).repr (x : SieveClassL2 Q) j =
      (matchedSieveEnergy Q j : ℂ) * (sieveAdjunctionBasis Q).repr (x : SieveClassL2 Q) j at hc
    have he := mul_right_cancel₀ hne hc
    have heR : matchedSieveEnergy Q m = matchedSieveEnergy Q j := Complex.ofReal_injective he
    exact hj ((matchedSieveEnergy_injective Q heR).symm)

/-- There are no additional point eigenvalues outside the arithmetic list. -/
theorem sieveAdjunctionOperator_eigenvalue_mem_range (Q : Finset Nat.Primes)
    (x : (sieveAdjunctionOperator Q).domain) (hx : (x : SieveClassL2 Q) ≠ 0)
    (z : ℂ) (heigen : sieveAdjunctionOperator Q x = z • (x : SieveClassL2 Q)) :
    ∃ m : SieveClass Q, z = (matchedSieveEnergy Q m : ℂ) := by
  obtain ⟨m, hm⟩ : ∃ m, (sieveAdjunctionBasis Q).repr (x : SieveClassL2 Q) m ≠ 0 := by
    by_contra! h
    apply hx
    apply (sieveAdjunctionBasis Q).repr.injective
    rw [map_zero]
    apply lp.ext
    funext m
    exact h m
  refine ⟨m, ?_⟩
  have hc := sieveAdjunctionOperator_spectral_action Q x m
  rw [heigen, map_smul] at hc
  exact mul_right_cancel₀ hm hc

/-- Torsion adjunction gives the equivalent self-intersection expression. -/
theorem matchedSieveEnergy_eq_selfIntersection (Q : Finset Nat.Primes) (m : SieveClass Q) :
    matchedSieveEnergy Q m =
      Real.eulerMascheroniConstant + 2 * Real.log (m : ℕ) - selfIntersection (m : ℕ) := by
  rw [matchedSieveEnergy, selfIntersection_eq m.property.pos]
  ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
