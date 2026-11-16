import GaloisForLFunctions.OrderSixMetaplecticTheory.TheConstantTermOfTheFractionalTraceReadsTheConjugateTwist
import GaloisForLFunctions.MetaplecticMobiusDescent.ThePrimaryCubicGaussSumFixesTheSign

/-!
# The primary generator evaluates the fractional Jacobi phase

The middle-cusp sum `J = ∑ s, χ(1-s²)` is exactly `-χ(4)p` at every
primary Eisenstein prime. In odd characteristic, the substitution
`s = 2x-1` reduces it to the primary cubic Jacobi evaluation. In
characteristic two, the sum of the nontrivial character `χ²` vanishes.

Thus the fractional-trace weight has an explicit primary-generator phase.
The coefficient vanishes precisely in characteristic two; at odd primes
its cube is `-p³`. These are phase identities, with no positivity assertion
for the bilinear theta correlations in the trace.
-/

noncomputable section
open scoped BigOperators Classical

namespace GaloisForLFunctions.OrderSixMetaplecticTheory
open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
  MetaplecticMobiusDescent.CubicJacobi MetaplecticMobiusDescent.CubicEisenstein

namespace PrimaryPrime
variable (P : PrimaryPrime)

/-- The actual cubic character has Jacobi sum minus the chosen primary generator. -/
theorem jacobiSum_chi_chi : jacobiSum P.chi P.chi = -ringComplex P.p := by
  letI : (Ideal.span {P.p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible P.prime.irreducible
  have hg : lambda ∉ (Ideal.span {P.p} : Ideal O) :=
    primary_maximal_divisor_good P.p P.primary _ (Ideal.subset_span (by simp))
  change jacobiSum ((cubicChar (Ideal.span {P.p}) hg).ringHomComp ringComplex)
    ((cubicChar (Ideal.span {P.p}) hg).ringHomComp ringComplex) = _
  rw [jacobiSum_ringHomComp,
    cubicJacobi_eq_neg_primary_generator_of_principal (Ideal.span {P.p}) hg
      P.p rfl P.primary, map_neg]

private def affineDouble (h2 : (2 : P.Res) ≠ 0) : P.Res ≃ P.Res where
  toFun x := 2 * x - 1
  invFun t := (t + 1) / 2
  left_inv := by intro x; field_simp; ring
  right_inv := by intro t; field_simp; ring

private theorem fracJacobi_eq_four_mul_jacobiSum (h2 : (2 : P.Res) ≠ 0) :
    P.fracJacobi = P.chi 4 * jacobiSum P.chi P.chi := by
  have h := Equiv.sum_comp (affineDouble P h2) (fun t : P.Res => P.chi (1 - t ^ 2))
  rw [fracJacobi, ← h]
  change (∑ x : P.Res, P.chi (1 - (2 * x - 1) ^ 2)) = _
  simp_rw [show ∀ x : P.Res, 1 - (2 * x - 1) ^ 2 = 4 * x * (1 - x) by intro x; ring,
    map_mul]
  rw [jacobiSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

private def oneSub : P.Res ≃ P.Res where
  toFun x := 1 - x
  invFun x := 1 - x
  left_inv := by intro x; ring
  right_inv := by intro x; ring

/-- In characteristic two the fractional Jacobi phase is the sum of `χ²`, hence zero. -/
theorem fracJacobi_of_two_eq_zero (h2 : (2 : P.Res) = 0) : P.fracJacobi = 0 := by
  have heq (x : P.Res) : 1 - x ^ 2 = (1 - x) ^ 2 := by
    have h := congrArg (fun a : P.Res => a * (x ^ 2 - x)) h2
    linear_combination -h
  unfold fracJacobi
  simp_rw [heq, map_pow, ← MulChar.pow_apply' _ (by decide : 2 ≠ 0)]
  exact (Equiv.sum_comp (oneSub P) (fun u : P.Res => (P.chi ^ 2) u)).trans
    (MulChar.sum_eq_zero_of_ne_one P.chi_sq_ne_one)

/-- The fractional Jacobi phase is `-χ(4)p`, including the prime above two. -/
theorem fracJacobi_eq_primary : P.fracJacobi = -(P.chi 4 * ringComplex P.p) := by
  by_cases h2 : (2 : P.Res) = 0
  · have h4 : (4 : P.Res) = 0 := by
      calc (4 : P.Res) = 2 * 2 := by ring
           _ = 0 := by rw [h2, zero_mul]
    rw [P.fracJacobi_of_two_eq_zero h2, h4, MulChar.map_zero, zero_mul, neg_zero]
  · rw [fracJacobi_eq_four_mul_jacobiSum P h2, P.jacobiSum_chi_chi, mul_neg]

/-- The local phase vanishes exactly in characteristic two. -/
theorem fracJacobi_eq_zero_iff : P.fracJacobi = 0 ↔ (2 : P.Res) = 0 := by
  constructor
  · intro hJ
    by_contra h2
    have h4 : (4 : P.Res) ≠ 0 := by
      convert mul_ne_zero h2 h2 using 1
      ring
    rw [P.fracJacobi_eq_primary] at hJ
    exact (mul_ne_zero (P.chi_ne_zero_of_ne 4 h4) P.ringComplex_ne_zero) (neg_eq_zero.mp hJ)
  · exact P.fracJacobi_of_two_eq_zero

/-- The fractional-trace weight retains the exact primary-generator phase. -/
theorem fracWeight_eq_primary (k : O) : P.fracWeight k =
    P.normC ^ 2 + P.normC + P.chi 4 * ringComplex P.p -
      if P.p ∣ k then P.normC * (P.chi 4 * ringComplex P.p) else 0 := by
  rw [fracWeight, P.fracJacobi_eq_primary]
  split_ifs <;> ring

/-- At every odd primary prime, cubing removes the cubic phase from the Jacobi coefficient. -/
theorem fracJacobi_cube (h2 : (2 : P.Res) ≠ 0) :
    P.fracJacobi ^ 3 = -(ringComplex P.p ^ 3) := by
  have h4 : (4 : P.Res) ≠ 0 := by
    convert mul_ne_zero h2 h2 using 1
    ring
  rw [P.fracJacobi_eq_primary, neg_pow, mul_pow, P.chi_cube 4 h4]
  ring

end PrimaryPrime
end GaloisForLFunctions.OrderSixMetaplecticTheory
