import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheInversePrimeKernelHasSubcriticalValuationCoordinates
import GaloisForLFunctions.HTGeometry.FiniteBlaschkeEnergyForm

/-!
# Occupation energy of the inverse-prime number operator

The literal inverse-prime kernel is the bounded KMS correction at parameter
`1/p`. Its logarithmic number operator has a complete product eigenbasis.
The finite Euler offset cancels every ground energy and leaves a positive
valuation weight on each occupied prime.
-/

noncomputable section
open Finset
open scoped Classical InnerProductSpace LinearPMap

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
open HTGeometry ArithmeticIntersectionTheory

/-- The geometric parameter of inverse-prime incidence. -/
def inversePrimeParameter (p : Nat.Primes) : ℝ := 1 / ((p : ℕ) : ℝ)

theorem inversePrimeParameter_norm_lt_one (p : Nat.Primes) :
    ‖(inversePrimeParameter p : ℂ)‖ < 1 := by
  have hp : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.property.one_lt
  rw [Complex.norm_real, Real.norm_eq_abs, inversePrimeParameter,
    abs_of_pos (by positivity), div_lt_one (by positivity)]
  exact hp

/-- The diagonal cost of completing the selected outgoing prime ladders. -/
def inversePrimeEuler (Q : Finset Nat.Primes) : ℝ :=
  ∑ p : Q, Real.log ((p : Nat.Primes) : ℕ) /
    ((((p : Nat.Primes) : ℕ) : ℝ) ^ 2 - 1)

/-- The entire valuation excitation is retained, including its occupied-prime correction. -/
def inversePrimeOccupationEnergy (Q : Finset Nat.Primes) (e : Q → ℕ) : ℝ :=
  ∑ p : Q, Real.log ((p : Nat.Primes) : ℕ) *
    (if e p = 0 then 0 else (e p : ℝ) +
      1 / ((((p : Nat.Primes) : ℕ) : ℝ) ^ 2 - 1))

private theorem inversePrimeGroundCorrection (p : Nat.Primes) :
    inversePrimeParameter p ^ 2 / (1 - inversePrimeParameter p ^ 2) =
      1 / (((p : ℕ) : ℝ) ^ 2 - 1) := by
  have hp : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.property.one_lt
  have hp2 : 1 < ((p : ℕ) : ℝ) ^ 2 := by nlinarith only [hp]
  have hd : 1 - (1 / (((p : ℕ) : ℝ))) ^ 2 ≠ 0 := by
    apply ne_of_gt
    rw [div_pow, one_pow]
    exact sub_pos.mpr ((div_lt_one (by positivity)).mpr hp2)
  unfold inversePrimeParameter
  field_simp [hd, (sub_pos.mpr hp2).ne']

theorem inversePrime_energy_eq (Q : Finset Nat.Primes) (e : Q → ℕ) :
    finiteBlaschkeEnergy (fun p : Q => inversePrimeParameter p)
      (fun p => Real.log ((p : Nat.Primes) : ℕ)) (inversePrimeEuler Q) e =
        inversePrimeOccupationEnergy Q e := by
  unfold finiteBlaschkeEnergy inversePrimeEuler inversePrimeOccupationEnergy
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  by_cases he : e p = 0
  · rw [hardyNumberEnergy, if_pos he, if_pos he, mul_zero, neg_div,
      inversePrimeGroundCorrection]
    ring
  · rw [hardyNumberEnergy, if_neg he, if_neg he]
    ring

theorem inversePrimeOccupationEnergy_nonneg (Q : Finset Nat.Primes) (e : Q → ℕ) :
    0 ≤ inversePrimeOccupationEnergy Q e := by
  apply sum_nonneg
  intro p _
  have hp : (1 : ℝ) < (((p : Nat.Primes) : ℕ) : ℝ) :=
    by exact_mod_cast p.val.property.one_lt
  apply mul_nonneg (Real.log_nonneg hp.le)
  split_ifs
  · exact le_rfl
  · have hden : 0 < (((p : Nat.Primes) : ℕ) : ℝ) ^ 2 - 1 := by
      nlinarith only [hp]
    positivity

/-- The original inverse-prime operator in complete valuation coordinates. -/
def inversePrimeCoordinateKernel (Q : Finset Nat.Primes) :
    FiniteNumberSpace Q →L[ℂ] FiniteNumberSpace Q :=
  ∑ p : Q, (Real.log ((p : Nat.Primes) : ℕ) : ℂ) •
    (lpCoordinateOperator p (hardyGeometricKMS (inversePrimeParameter_norm_lt_one p)) - 1)

private theorem lpSingle_decidable_eq {I : Type} (d₁ d₂ : DecidableEq I) (i : I) :
    (@lp.single I (fun _ => ℂ) (fun _ => inferInstance) d₁ 2 i (1 : ℂ) :
      lp (fun _ : I => ℂ) 2) =
      @lp.single I (fun _ => ℂ) (fun _ => inferInstance) d₂ 2 i (1 : ℂ) :=
  congrArg (fun d : DecidableEq I =>
    (@lp.single I (fun _ => ℂ) (fun _ => inferInstance) d 2 i (1 : ℂ) :
      lp (fun _ : I => ℂ) 2)) (Subsingleton.elim d₁ d₂)

private theorem inversePrimeCoordinateTerm_single (Q : Finset Nat.Primes)
    (p : Q) (m n : SieveClass Q) :
    (Real.log ((p : Nat.Primes) : ℕ) : ℂ) *
      ((lpCoordinateOperator p (hardyGeometricKMS (inversePrimeParameter_norm_lt_one p)) - 1)
        (lp.single 2 (sieveValuationEquiv Q n) (1 : ℂ))) (sieveValuationEquiv Q m) =
      (inversePrimeLadderKernel ((p : Nat.Primes) : ℕ) (m : ℕ) (n : ℕ) : ℂ) := by
  have hiff := sieveValuations_agree_off_prime_iff Q m n p
  have hmatrix := congrArg (fun z : ℂ => (Real.log ((p : Nat.Primes) : ℕ) : ℂ) * z)
    (lpCoordinateKMS_sub_one_single_apply (I := Q) p
      (q := inversePrimeParameter (p : Nat.Primes))
      (inversePrimeParameter_norm_lt_one p) (sieveValuationEquiv Q n) (sieveValuationEquiv Q m))
  have hsingle : (lp.single 2 (sieveValuationEquiv Q n) (1 : ℂ) : FiniteNumberSpace Q) =
      @lp.single (Q → ℕ) (fun _ => ℂ) (fun _ => inferInstance)
        (fun a b => Classical.propDecidable (a = b)) 2 (sieveValuationEquiv Q n) (1 : ℂ) :=
    lpSingle_decidable_eq _ _ _
  apply (congrArg (fun v : FiniteNumberSpace Q =>
    (Real.log ((p : Nat.Primes) : ℕ) : ℂ) *
      ((lpCoordinateOperator p (hardyGeometricKMS (inversePrimeParameter_norm_lt_one p)) - 1) v)
        (sieveValuationEquiv Q m)) hsingle).trans
  apply hmatrix.trans
  rw [inversePrimeLadderKernel_tensor p.val.property m.property.pos.ne' n.property.pos.ne']
  by_cases hrest : (fun j : {j : Q // j ≠ p} => sieveValuationEquiv Q m j) =
      (fun j : {j : Q // j ≠ p} => sieveValuationEquiv Q n j)
  · rw [if_pos hrest, if_pos (hiff.mpr hrest)]
    change (Real.log ((p : Nat.Primes) : ℕ) : ℂ) *
      ((inversePrimeParameter p : ℂ) ^
        (max ((m : ℕ).factorization (p : Nat.Primes)) ((n : ℕ).factorization (p : Nat.Primes)) -
          min ((m : ℕ).factorization (p : Nat.Primes)) ((n : ℕ).factorization (p : Nat.Primes))) -
        if (m : ℕ).factorization (p : Nat.Primes) = (n : ℕ).factorization (p : Nat.Primes)
          then 1 else 0) = _
    by_cases hp : (m : ℕ).factorization (p : Nat.Primes) = (n : ℕ).factorization (p : Nat.Primes)
    · simp only [if_pos hp, kmsEntry, inversePrimeParameter, Complex.ofReal_mul,
        Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_one]
    · simp only [if_neg hp, kmsEntry, inversePrimeParameter, Complex.ofReal_mul,
        Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_zero]
  · rw [if_neg hrest, if_neg (fun h => hrest (hiff.mp h))]
    simp only [mul_zero, Complex.ofReal_zero]

/-- Matrix entries of the bounded operator are the literal inverse-prime quotient kernel. -/
theorem inversePrimeCoordinateKernel_single (Q : Finset Nat.Primes) (m n : SieveClass Q) :
    inversePrimeCoordinateKernel Q (lp.single 2 (sieveValuationEquiv Q n) (1 : ℂ))
      (sieveValuationEquiv Q m) = (inversePrimeKernel (m : ℕ) (n : ℕ) : ℂ) := by
  simp only [inversePrimeCoordinateKernel, _root_.sum_apply, _root_.smul_apply,
    lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [inversePrimeKernel_sieve_sum m.property n.property, Complex.ofReal_sum,
    ← Finset.sum_coe_sort Q]
  exact sum_congr rfl fun p _ => inversePrimeCoordinateTerm_single Q p m n

/-- The maximal-domain logarithmic number operator with the exact outgoing offset. -/
def inversePrimeNumberOperator (Q : Finset Nat.Primes) :
    FiniteNumberSpace Q →ₗ.[ℂ] FiniteNumberSpace Q :=
  finiteBlaschkeNumberOperator (fun p : Q => inversePrimeParameter p)
    (fun p => inversePrimeParameter_norm_lt_one p)
    (fun p => Real.log ((p : Nat.Primes) : ℕ)) (inversePrimeEuler Q)

theorem inversePrimeNumberOperator_apply (Q : Finset Nat.Primes)
    (x : (inversePrimeNumberOperator Q).domain) (e : Q → ℕ) :
    inversePrimeNumberOperator Q x e =
      ((finiteNumberDegree (fun p : Q => Real.log ((p : Nat.Primes) : ℕ)) e +
        inversePrimeEuler Q : ℝ) : ℂ) * (x : FiniteNumberSpace Q) e -
        inversePrimeCoordinateKernel Q (x : FiniteNumberSpace Q) e := by
  have hc : finiteBlaschkeCorrection (fun p : Q => inversePrimeParameter p)
      (fun p => inversePrimeParameter_norm_lt_one p)
      (fun p => Real.log ((p : Nat.Primes) : ℕ)) (inversePrimeEuler Q) =
      (inversePrimeEuler Q : ℂ) • 1 - inversePrimeCoordinateKernel Q := by
    rw [finiteBlaschkeCorrection, inversePrimeCoordinateKernel]
    conv_rhs => rw [sub_eq_add_neg, ← sum_neg_distrib]
    congr 1
    apply sum_congr rfl
    intro p _
    module
  rw [inversePrimeNumberOperator, finiteBlaschkeNumberOperator_apply, hc]
  change (inversePrimeEuler Q : ℂ) * (x : FiniteNumberSpace Q) e -
      inversePrimeCoordinateKernel Q (x : FiniteNumberSpace Q) e +
      (finiteNumberDegree (fun p : Q => Real.log ((p : Nat.Primes) : ℕ)) e : ℂ) *
        (x : FiniteNumberSpace Q) e = _
  push_cast
  ring

/-- A literal finite coefficient vector, embedded without an exponent cutoff. -/
def inversePrimeFiniteVector (Q : Finset Nat.Primes) (S : Finset (SieveClass Q))
    (f : SieveClass Q → ℝ) : FiniteNumberSpace Q :=
  ∑ n ∈ S, (f n : ℂ) • lp.single 2 (sieveValuationEquiv Q n) (1 : ℂ)

theorem inversePrimeFiniteVector_apply (Q : Finset Nat.Primes) (S : Finset (SieveClass Q))
    (f : SieveClass Q → ℝ) (m : SieveClass Q) :
    inversePrimeFiniteVector Q S f (sieveValuationEquiv Q m) =
      if m ∈ S then (f m : ℂ) else 0 := by
  simp only [inversePrimeFiniteVector, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hm : m ∈ S
  · rw [if_pos hm, sum_eq_single m]
    · rw [lp.single_apply, Pi.single_eq_same, mul_one]
    · intro n _ hnm
      rw [lp.single_apply_ne _ _ _ (fun h => hnm ((sieveValuationEquiv Q).injective h.symm)),
        mul_zero]
    · exact fun h => (h hm).elim
  · rw [if_neg hm]
    apply sum_eq_zero
    intro n hn
    have hmn : sieveValuationEquiv Q m ≠ sieveValuationEquiv Q n :=
      fun h => hm (((sieveValuationEquiv Q).injective h).symm ▸ hn)
    rw [lp.single_apply_ne _ _ _ hmn, mul_zero]

private theorem inversePrimeSingle_mem_domain (Q : Finset Nat.Primes) (e : Q → ℕ) :
    lp.single 2 e (1 : ℂ) ∈ (inversePrimeNumberOperator Q).domain := by
  let w := finiteNumberDegree (fun p : Q => Real.log ((p : Nat.Primes) : ℕ))
  change Memℓp (fun j => (w j : ℂ) * (lp.single 2 e (1 : ℂ) : FiniteNumberSpace Q) j) 2
  have he : (fun j => (w j : ℂ) * (lp.single 2 e (1 : ℂ) : FiniteNumberSpace Q) j) =
      fun j => (lp.single 2 e (w e : ℂ) : FiniteNumberSpace Q) j := by
    funext j
    by_cases hj : j = e
    · subst j
      simp only [lp.single_apply, Pi.single_eq_same, mul_one]
    · rw [lp.single_apply_ne _ _ _ hj, lp.single_apply_ne _ _ _ hj, mul_zero]
  rw [he]
  exact lp.memℓp _

/-- Finite literal sources belong to the original maximal operator domain. -/
theorem inversePrimeFiniteVector_mem_domain (Q : Finset Nat.Primes)
    (S : Finset (SieveClass Q)) (f : SieveClass Q → ℝ) :
    inversePrimeFiniteVector Q S f ∈ (inversePrimeNumberOperator Q).domain := by
  apply (inversePrimeNumberOperator Q).domain.sum_mem
  intro n _
  exact (inversePrimeNumberOperator Q).domain.smul_mem _
    (inversePrimeSingle_mem_domain Q (sieveValuationEquiv Q n))

private theorem inversePrimeFiniteVector_inner (Q : Finset Nat.Primes)
    (S : Finset (SieveClass Q)) (f : SieveClass Q → ℝ) (y : FiniteNumberSpace Q) :
    inner ℂ (inversePrimeFiniteVector Q S f) y =
      ∑ n ∈ S, (f n : ℂ) * y (sieveValuationEquiv Q n) := by
  simp only [inversePrimeFiniteVector, sum_inner, inner_smul_left, Complex.conj_ofReal,
    lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]

private theorem inversePrimeCoordinateKernel_finite (Q : Finset Nat.Primes)
    (S : Finset (SieveClass Q)) (f : SieveClass Q → ℝ) (m : SieveClass Q) :
    inversePrimeCoordinateKernel Q (inversePrimeFiniteVector Q S f) (sieveValuationEquiv Q m) =
      ∑ n ∈ S, ((f n * inversePrimeKernel (m : ℕ) (n : ℕ) : ℝ) : ℂ) := by
  simp only [inversePrimeFiniteVector, map_sum, map_smul, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, inversePrimeCoordinateKernel_single,
    Complex.ofReal_mul]

/-- The complete finite-prime quadratic form on the original integer labels. -/
def inversePrimeFiniteEnergy (Q : Finset Nat.Primes) (S : Finset (SieveClass Q))
    (f : SieveClass Q → ℝ) : ℝ :=
  ∑ m ∈ S, (Real.log (m : ℕ) + inversePrimeEuler Q) * f m ^ 2 -
    ∑ m ∈ S, ∑ n ∈ S, f m * f n * inversePrimeKernel (m : ℕ) (n : ℕ)

theorem inversePrimeFiniteEnergy_eq_inner (Q : Finset Nat.Primes)
    (S : Finset (SieveClass Q)) (f : SieveClass Q → ℝ) :
    (inversePrimeFiniteEnergy Q S f : ℂ) =
      inner ℂ (inversePrimeFiniteVector Q S f)
        (inversePrimeNumberOperator Q
          ⟨inversePrimeFiniteVector Q S f, inversePrimeFiniteVector_mem_domain Q S f⟩) := by
  rw [inversePrimeFiniteVector_inner]
  have hdegree (m : SieveClass Q) :
      finiteNumberDegree (fun p : Q => Real.log ((p : Nat.Primes) : ℕ))
        (sieveValuationEquiv Q m) = Real.log (m : ℕ) := by
    have h := log_sieveValuationEquiv_symm Q (sieveValuationEquiv Q m)
    rw [Equiv.symm_apply_apply] at h
    rw [h, finiteNumberDegree]
    exact sum_congr rfl fun _ _ => mul_comm _ _
  unfold inversePrimeFiniteEnergy
  rw [Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro m hm
  rw [inversePrimeNumberOperator_apply, hdegree, inversePrimeFiniteVector_apply,
    if_pos hm, inversePrimeCoordinateKernel_finite]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow, mul_sub, mul_sum]
  congr 1
  · ring
  · exact sum_congr rfl fun _ _ => by ring

/-- The complete product basis diagonalizes the original operator's quadratic form. -/
theorem inversePrimeNumberOperator_hasSum_energy (Q : Finset Nat.Primes)
    (x : (inversePrimeNumberOperator Q).domain) :
    HasSum (fun e => inversePrimeOccupationEnergy Q e *
      ‖(finiteBlaschkeBasis (fun p : Q => inversePrimeParameter p)
        (fun p => inversePrimeParameter_norm_lt_one p)).repr (x : FiniteNumberSpace Q) e‖ ^ 2)
      (inner ℂ (x : FiniteNumberSpace Q) (inversePrimeNumberOperator Q x)).re := by
  simpa only [inversePrime_energy_eq] using finiteBlaschkeNumberOperator_hasSum_energy
    (fun p : Q => inversePrimeParameter p) (fun p => inversePrimeParameter_norm_lt_one p)
    (fun p => Real.log ((p : Nat.Primes) : ℕ)) (inversePrimeEuler Q) x

/-- Every finite original source has its full summable occupation-energy expansion. -/
theorem inversePrimeFiniteEnergy_hasSum (Q : Finset Nat.Primes)
    (S : Finset (SieveClass Q)) (f : SieveClass Q → ℝ) :
    HasSum (fun e => inversePrimeOccupationEnergy Q e *
      ‖(finiteBlaschkeBasis (fun p : Q => inversePrimeParameter p)
        (fun p => inversePrimeParameter_norm_lt_one p)).repr (inversePrimeFiniteVector Q S f) e‖ ^ 2)
      (inversePrimeFiniteEnergy Q S f) := by
  have h := inversePrimeNumberOperator_hasSum_energy Q
    ⟨inversePrimeFiniteVector Q S f, inversePrimeFiniteVector_mem_domain Q S f⟩
  rwa [← inversePrimeFiniteEnergy_eq_inner, Complex.ofReal_re] at h

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
