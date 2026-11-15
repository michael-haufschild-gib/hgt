import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerBranchUnit


/-!
# Integral radical monomials

Removing complete covering-degree powers of the branch factor leaves
radical monomials integral over the polynomial ring. Their defining
powers have the reduced branch multiplicities given by Euclidean remainders.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable {K : Type*} [Field K] (c : Kˣ) (b R n i : ℕ)

/-- A radical monomial with every full covering-degree power of the branch factor removed. -/
def kummerIntegralMonomial : KummerBranchField c b R n :=
  AdjoinRoot.root (kummerBranchFieldPolynomial c b R n) ^ i /
    algebraMap K[X] (KummerBranchField c b R n) (1 - X ^ (b + 1)) ^ (i * R / (n + 1))

/-- The covering-degree power has the reduced branch multiplicity `i R mod N`. -/
theorem kummerIntegralMonomial_pow :
    kummerIntegralMonomial c b R n i ^ (n + 1) =
      algebraMap K[X] (KummerBranchField c b R n)
        (C ((c : K) ^ i) * X ^ i * (1 - X ^ (b + 1)) ^ (i * R % (n + 1))) := by
  let L := KummerBranchField c b R n
  let t := algebraMap K[X] L (1 - X ^ (b + 1))
  have hinj : Function.Injective (algebraMap K[X] L) := by
    rw [IsScalarTower.algebraMap_eq K[X] (FractionRing K[X]) L]
    exact (algebraMap (FractionRing K[X]) L).injective.comp (IsFractionRing.injective K[X] _)
  have ht : t ≠ 0 := fun h => kummerBranchFactor_ne_zero (K := K) b
    (hinj (h.trans (map_zero _).symm))
  let z := AdjoinRoot.root (kummerBranchFieldPolynomial c b R n)
  let A := algebraMap K[X] L (C (c : K))
  let y := algebraMap K[X] L X
  have hz : z ^ (n + 1) = A * y * t ^ R := by
    rw [kummerBranchField_root_pow, ← IsScalarTower.algebraMap_apply,
      kummerBranch, map_mul, map_mul, map_pow]
  have hiR : R * i = i * R / (n + 1) * (n + 1) + i * R % (n + 1) := by
    rw [Nat.mul_comm R i]
    simpa only [Nat.mul_comm (n + 1) (i * R / (n + 1))] using
      (Nat.div_add_mod (i * R) (n + 1)).symm
  have hright : algebraMap K[X] L
      (C ((c : K) ^ i) * X ^ i * (1 - X ^ (b + 1)) ^ (i * R % (n + 1))) =
      A ^ i * y ^ i * t ^ (i * R % (n + 1)) := by
    simp only [map_mul, map_pow]
    rfl
  rw [hright]
  change (z ^ i / t ^ (i * R / (n + 1))) ^ (n + 1) = _
  rw [div_pow, ← pow_mul, Nat.mul_comm i (n + 1), pow_mul, hz,
    mul_pow, mul_pow, ← pow_mul, hiR, pow_add, ← pow_mul]
  rw [show A ^ i * y ^ i *
      (t ^ (i * R / (n + 1) * (n + 1)) * t ^ (i * R % (n + 1))) =
      (A ^ i * y ^ i * t ^ (i * R % (n + 1))) *
        t ^ (i * R / (n + 1) * (n + 1)) by ring,
    mul_div_cancel_right₀ _ (pow_ne_zero _ ht)]

/-- Every reduced radical monomial is integral over the polynomial coordinate ring. -/
theorem kummerIntegralMonomial_integral : IsIntegral K[X] (kummerIntegralMonomial c b R n i) := by
  apply IsIntegral.of_pow (Nat.succ_pos n)
  rw [kummerIntegralMonomial_pow]
  exact isIntegral_algebraMap

/-- Reduced radical monomials are actual elements of the integral closure. -/
def kummerNormalizedMonomial : integralClosure K[X] (KummerBranchField c b R n) :=
  ⟨kummerIntegralMonomial c b R n i, kummerIntegralMonomial_integral c b R n i⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
