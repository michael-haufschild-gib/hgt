import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.PrimeRamanujanMoments

/-!
# Ramanujan moments on product residue rings

The product character and the unit set both factor by coordinates. Therefore
all moments factor, even when the moduli share prime factors. For products of
prime fields this gives an explicit formula in every degree and the exact
cubic unit-walk count.
-/

open Finset
open scoped BigOperators Classical

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
noncomputable section
variable {ι : Type*} [Fintype ι]

local instance residue_neZero (q : ι → ℕ+) (i : ι) : NeZero (q i : ℕ) :=
  ⟨(q i).pos.ne'⟩

/-- The Ramanujan character sum on a product of finite cyclic residue rings. -/
def productRingRamanujanSum (q : ι → ℕ+) (g : ∀ i, ZMod (q i : ℕ)) : ℂ :=
  ∑ u : ∀ i, (ZMod (q i : ℕ))ˣ,
    ∏ i, ZMod.stdAddChar (g i * (u i : ZMod (q i : ℕ)))

/-- Product-ring Ramanujan sums factor without coprimality restrictions. -/
theorem productRingRamanujanSum_eq_prod (q : ι → ℕ+) (g : ∀ i, ZMod (q i : ℕ)) :
    productRingRamanujanSum q g =
      ∏ i, _root_.RHTower.cglRamanujanAdditiveSum ⟨q i, (q i).pos⟩ (g i) := by
  classical
  unfold productRingRamanujanSum
  calc
    _ = ∏ i, ∑ u : (ZMod (q i : ℕ))ˣ,
        ZMod.stdAddChar (g i * (u : ZMod (q i : ℕ))) :=
      (Fintype.prod_sum (fun i (u : (ZMod (q i : ℕ))ˣ) =>
        ZMod.stdAddChar (g i * (u : ZMod (q i : ℕ))))).symm
    _ = _ := ?_
  apply prod_congr rfl
  intro i _
  rw [← _root_.RHTower.Sieve.stadlmannReciprocalPhaseSum_eq_direct,
    _root_.RHTower.Sieve.stadlmannReciprocalPhaseSum_eq_cglRamanujan]

/-- Every moment is multiplicative under arbitrary finite ring products. -/
theorem sum_productRingRamanujanSum_pow (q : ι → ℕ+) (k : ℕ) :
    (∑ g : ∀ i, ZMod (q i : ℕ), productRingRamanujanSum q g ^ k) =
      ∏ i, ∑ g : ZMod (q i : ℕ),
        _root_.RHTower.cglRamanujanAdditiveSum ⟨q i, (q i).pos⟩ g ^ k := by
  classical
  simp_rw [productRingRamanujanSum_eq_prod, ← prod_pow]
  exact (Fintype.prod_sum (fun i (g : ZMod (q i : ℕ)) =>
    _root_.RHTower.cglRamanujanAdditiveSum ⟨q i, (q i).pos⟩ g ^ k)).symm

/-- All product-ring moments are natural multiples of the ring's cardinality. -/
theorem productRingRamanujan_moment_is_nat (q : ι → ℕ+) (k : ℕ) :
    ∃ n : ℕ,
      (∑ g : ∀ i, ZMod (q i : ℕ), productRingRamanujanSum q g ^ k) =
        ((∏ i, (q i : ℕ)) * n : ℕ) := by
  refine ⟨∏ i, unitTupleCount (q i) (fun _ : Fin k => 1) 0, ?_⟩
  rw [sum_productRingRamanujanSum_pow]
  simp_rw [sum_ramanujan_pow]
  rw [prod_mul_distrib, Nat.cast_mul, Nat.cast_prod, Nat.cast_prod]

/-- The full moment formula for products of prime fields, including repeated primes. -/
theorem sum_primeProductRingRamanujanSum_pow
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (k : ℕ) :
    (∑ g : ∀ i, ZMod (p i),
      productRingRamanujanSum (fun i => (⟨p i, (Fact.out : (p i).Prime).pos⟩ : ℕ+)) g ^ k) =
      ∏ i, ((p i : ℂ) - 1) ^ k + ((p i : ℂ) - 1) * (-1) ^ k := by
  refine (sum_productRingRamanujanSum_pow
    (fun i => (⟨p i, (Fact.out : (p i).Prime).pos⟩ : ℕ+)) k).trans ?_
  apply prod_congr rfl
  intro i _
  exact sum_prime_ramanujan_pow (p i) k

/-- The third moment counts oriented triangles in the product unitary Cayley graph. -/
theorem sum_primeProductRingRamanujanSum_cube
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] :
    (∑ g : ∀ i, ZMod (p i),
      productRingRamanujanSum (fun i => (⟨p i, (Fact.out : (p i).Prime).pos⟩ : ℕ+)) g ^ 3) =
      ∏ i, (p i : ℂ) * ((p i : ℂ) - 1) * ((p i : ℂ) - 2) := by
  refine (sum_productRingRamanujanSum_pow
    (fun i => (⟨p i, (Fact.out : (p i).Prime).pos⟩ : ℕ+)) 3).trans ?_
  apply prod_congr rfl
  intro i _
  exact sum_prime_ramanujan_cube (p i)

/-- A binary factor is exactly the obstruction to triangular unit walks. -/
theorem primeProductRingRamanujan_cube_eq_zero_iff
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] :
    (∑ g : ∀ i, ZMod (p i),
      productRingRamanujanSum (fun i => (⟨p i, (Fact.out : (p i).Prime).pos⟩ : ℕ+)) g ^ 3) = 0 ↔
      ∃ i, p i = 2 := by
  rw [sum_primeProductRingRamanujanSum_cube, prod_eq_zero_iff]
  constructor
  · rintro ⟨i, _, hi⟩
    have hp0 : (p i : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : (p i).Prime).ne_zero
    have hp1 : (p i : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by
      exact_mod_cast (Fact.out : (p i).Prime).ne_one)
    have hi2 := (mul_eq_zero.mp hi).resolve_left (mul_ne_zero hp0 hp1)
    refine ⟨i, ?_⟩
    exact_mod_cast sub_eq_zero.mp hi2
  · rintro ⟨i, hi⟩
    refine ⟨i, mem_univ i, ?_⟩
    rw [hi]
    ring

#print axioms productRingRamanujanSum_eq_prod
#print axioms sum_productRingRamanujanSum_pow
#print axioms productRingRamanujan_moment_is_nat
#print axioms sum_primeProductRingRamanujanSum_pow
#print axioms sum_primeProductRingRamanujanSum_cube
#print axioms primeProductRingRamanujan_cube_eq_zero_iff

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
