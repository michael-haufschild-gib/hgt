import GaloisForLFunctions.HTGeometry.LpGeometricCoordinateKernel
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSieveExcitationsHaveAdjunctionEnergy

/-!
# The actual prime kernel is bounded on finite-sieve class coordinates

The transverse-tower formula identifies each literal matrix entry with a
bounded KMS fibre operator. Finite addition and valuation reindexing give a
self-adjoint extension on the complete space of supported integer classes.
-/

noncomputable section

open scoped Classical InnerProductSpace

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open HTGeometry ArithmeticIntersectionTheory ArithmeticEffectivityTheory

/-- Square-summable coordinates indexed by all supported positive integers. -/
abbrev SieveClassL2 (Q : Finset Nat.Primes) := lp (fun _ : SieveClass Q => ℂ) 2

/-- The actual valuation-coordinate unitary, without any exponent cutoff. -/
def sieveCoordinateUnitary (Q : Finset Nat.Primes) :
    SieveClassL2 Q ≃ₗᵢ[ℂ] lp (fun _ : Q → ℕ => ℂ) 2 :=
  lpReindexEquiv (sieveValuationEquiv Q)

/-- The bounded prime operator on the full exponent-function carrier. -/
def sievePrimeCoordinateOperator (Q : Finset Nat.Primes) :
    lp (fun _ : Q → ℕ => ℂ) 2 →L[ℂ] lp (fun _ : Q → ℕ => ℂ) 2 :=
  ∑ p : Q, (Real.log ((p : Nat.Primes) : ℕ) : ℂ) •
    (lpCoordinateOperator p (hardyGeometricKMS (primeBlaschkeParameter_norm_lt_one p)) - 1)

theorem sievePrimeCoordinateOperator_isSelfAdjoint (Q : Finset Nat.Primes) :
    IsSelfAdjoint (sievePrimeCoordinateOperator Q) := by
  apply isSelfAdjoint_sum
  intro p _
  exact (show IsSelfAdjoint (Real.log ((p : Nat.Primes) : ℕ) : ℂ) from
    Complex.conj_ofReal _).smul
      ((lpCoordinateOperator_isSelfAdjoint p _
        (hardyGeometricKMS_isSelfAdjoint (primeBlaschkeParameter_norm_lt_one p))).sub
          (IsSelfAdjoint.one _))

private theorem lpSingle_eq_of_decidable {I : Type}
    (d₁ d₂ : DecidableEq I) (i : I) :
    (@lp.single I (fun _ => ℂ) (fun _ => inferInstance) d₁ 2 i (1 : ℂ) :
      lp (fun _ : I => ℂ) 2) =
      @lp.single I (fun _ => ℂ) (fun _ => inferInstance) d₂ 2 i (1 : ℂ) :=
  congrArg (fun d : DecidableEq I =>
    (@lp.single I (fun _ => ℂ) (fun _ => inferInstance) d 2 i (1 : ℂ) :
      lp (fun _ : I => ℂ) 2)) (Subsingleton.elim d₁ d₂)

/-- Each bounded fibre has exactly the corresponding arithmetic ladder matrix. -/
theorem sievePrimeCoordinateTerm_single (Q : Finset Nat.Primes)
    (p : Q) (m n : SieveClass Q) :
    (Real.log ((p : Nat.Primes) : ℕ) : ℂ) *
      ((lpCoordinateOperator p (hardyGeometricKMS (primeBlaschkeParameter_norm_lt_one p)) - 1)
        (lp.single 2 (sieveValuationEquiv Q n) (1 : ℂ))) (sieveValuationEquiv Q m) =
      (ladderKernel ((p : Nat.Primes) : ℕ) (m : ℕ) (n : ℕ) : ℂ) := by
  have hiff := sieveValuations_agree_off_prime_iff Q m n p
  have hmatrix := congrArg (fun z : ℂ => (Real.log ((p : Nat.Primes) : ℕ) : ℂ) * z)
    (lpCoordinateKMS_sub_one_single_apply (I := Q) p
      (q := primeBlaschkeParameter (p : Nat.Primes))
      (primeBlaschkeParameter_norm_lt_one p) (sieveValuationEquiv Q n) (sieveValuationEquiv Q m))
  have hsingle : (lp.single 2 (sieveValuationEquiv Q n) (1 : ℂ) :
      lp (fun _ : Q → ℕ => ℂ) 2) =
      @lp.single (Q → ℕ) (fun _ => ℂ) (fun _ => inferInstance)
        (fun a b => Classical.propDecidable (a = b)) 2 (sieveValuationEquiv Q n) (1 : ℂ) :=
    lpSingle_eq_of_decidable _ _ _
  apply (congrArg (fun v : lp (fun _ : Q → ℕ => ℂ) 2 =>
    (Real.log ((p : Nat.Primes) : ℕ) : ℂ) *
      ((lpCoordinateOperator p (hardyGeometricKMS (primeBlaschkeParameter_norm_lt_one p)) - 1) v)
        (sieveValuationEquiv Q m)) hsingle).trans
  apply hmatrix.trans
  rw [ladderKernel_eq_tensor p.val.property m.property.pos.ne' n.property.pos.ne']
  by_cases hrest : (fun j : {j : Q // j ≠ p} => sieveValuationEquiv Q m j) =
      (fun j : {j : Q // j ≠ p} => sieveValuationEquiv Q n j)
  · rw [if_pos hrest, if_pos (hiff.mpr hrest)]
    change (Real.log ((p : Nat.Primes) : ℕ) : ℂ) *
      ((primeBlaschkeParameter p : ℂ) ^
          (max ((m : ℕ).factorization (p : Nat.Primes)) ((n : ℕ).factorization (p : Nat.Primes)) -
            min ((m : ℕ).factorization (p : Nat.Primes)) ((n : ℕ).factorization (p : Nat.Primes))) -
        if (m : ℕ).factorization (p : Nat.Primes) = (n : ℕ).factorization (p : Nat.Primes)
          then 1 else 0) =
      ((Real.log ((p : Nat.Primes) : ℕ) *
        (kmsEntry (primeBlaschkeParameter p) ((m : ℕ).factorization (p : Nat.Primes))
          ((n : ℕ).factorization (p : Nat.Primes)) -
            if (m : ℕ).factorization (p : Nat.Primes) = (n : ℕ).factorization (p : Nat.Primes)
              then 1 else 0) : ℝ) : ℂ)
    by_cases hp : (m : ℕ).factorization (p : Nat.Primes) = (n : ℕ).factorization (p : Nat.Primes)
    · simp only [if_pos hp, kmsEntry, Complex.ofReal_mul, Complex.ofReal_sub,
        Complex.ofReal_pow, Complex.ofReal_one]
    · simp only [if_neg hp, kmsEntry, Complex.ofReal_mul, Complex.ofReal_sub,
        Complex.ofReal_pow, Complex.ofReal_zero]
  · rw [if_neg hrest, if_neg (fun h => hrest (hiff.mp h))]
    simp only [mul_zero, Complex.ofReal_zero]

theorem sievePrimeCoordinateOperator_single (Q : Finset Nat.Primes) (m n : SieveClass Q) :
    sievePrimeCoordinateOperator Q (lp.single 2 (sieveValuationEquiv Q n) (1 : ℂ))
      (sieveValuationEquiv Q m) = (weilPrimeKernel (m : ℕ) (n : ℕ) : ℂ) := by
  simp only [sievePrimeCoordinateOperator, _root_.sum_apply,
    _root_.smul_apply, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [weilPrimeKernel_sieve_sum m.property n.property, Complex.ofReal_sum,
    ← Finset.sum_coe_sort Q]
  exact Finset.sum_congr rfl fun p _ => sievePrimeCoordinateTerm_single Q p m n

/-- The bounded extension of the literal prime kernel on supported integer classes. -/
def sievePrimeOperator (Q : Finset Nat.Primes) : SieveClassL2 Q →L[ℂ] SieveClassL2 Q :=
  (sieveCoordinateUnitary Q).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    sievePrimeCoordinateOperator Q ∘L
      (sieveCoordinateUnitary Q).toContinuousLinearEquiv.toContinuousLinearMap

theorem sievePrimeOperator_single (Q : Finset Nat.Primes) (m n : SieveClass Q) :
    sievePrimeOperator Q (lp.single 2 n (1 : ℂ)) m =
      (weilPrimeKernel (m : ℕ) (n : ℕ) : ℂ) := by
  change sievePrimeCoordinateOperator Q
    (lpReindexEquiv (sieveValuationEquiv Q) (lp.single 2 n (1 : ℂ)))
      (sieveValuationEquiv Q m) = _
  rw [lpReindexEquiv_single, sievePrimeCoordinateOperator_single]

theorem sievePrimeOperator_isSelfAdjoint (Q : Finset Nat.Primes) :
    IsSelfAdjoint (sievePrimeOperator Q) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  let U := sieveCoordinateUnitary Q
  let P := sievePrimeCoordinateOperator Q
  have hP := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (sievePrimeCoordinateOperator_isSelfAdjoint Q)
  change inner ℂ (U.symm (P (U x))) y = inner ℂ x (U.symm (P (U y)))
  calc
    inner ℂ (U.symm (P (U x))) y = inner ℂ (P (U x)) (U y) := by
      simpa only [U.symm_apply_apply] using U.symm.inner_map_map (P (U x)) (U y)
    _ = inner ℂ (U x) (P (U y)) := hP _ _
    _ = inner ℂ x (U.symm (P (U y))) := by
      simpa only [U.symm_apply_apply] using (U.symm.inner_map_map (U x) (P (U y))).symm

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
