import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiBooleanParityGram
import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiOddDivisorGramAndFrameBounds
import GaloisForLFunctions.HTGeometry.OrbitSumKorobovParameters

/-!
# Literal prime-cube realization of the odd-divisor Gram

Boolean prime choices give distinct positive integers with exactly the selected
prime exponents. For odd primes these indices are odd, and their normalized GCD
kernel is exactly the product Boolean kernel. The native odd-divisor Gram pulls
back with its single global odd reciprocal-square mass factor.

The arithmetic coordinate formula reuses the corpus's existing
`OrbitVanishing.factorization_prod_pow`. This is support for the positive
prime-bank construction, not the full antichain capacity classification.
-/

open scoped BigOperators
open Finset


namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section
set_option autoImplicit false

private def primeCubeExponent (P : Finset ℕ) (x : P → Bool) (p : ℕ) : ℕ :=
  if hp : p ∈ P then if x ⟨p,hp⟩ then 1 else 0 else 0

/-- The squarefree integer represented by a Boolean choice of the allowed primes. -/
def fermiPrimeCubeIndex (P : Finset ℕ) (x : P → Bool) : ℕ :=
  ∏ p ∈ P, p^(primeCubeExponent P x p)

private theorem cube_factorization (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (x : P → Bool) (q : ℕ) :
    (fermiPrimeCubeIndex P x).factorization q = if q ∈ P then primeCubeExponent P x q else 0 :=
  GaloisForLFunctions.HTGeometry.OrbitVanishing.factorization_prod_pow hP (primeCubeExponent P x) q

theorem fermiPrimeCubeIndex_factorization (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (x : P → Bool) (p : P) :
    (fermiPrimeCubeIndex P x).factorization p = if x p then 1 else 0 := by
  rw [cube_factorization P hP x p]
  simp [primeCubeExponent, p.property]

theorem fermiPrimeCubeIndex_primeFactors_subset (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (x : P → Bool) : (fermiPrimeCubeIndex P x).primeFactors ⊆ P := by
  intro q hq
  by_contra hqP
  have hne : (fermiPrimeCubeIndex P x).factorization q ≠ 0 := by
    apply Finsupp.mem_support_iff.mp
    rw [Nat.support_factorization]
    exact hq
  exact hne (by rw [cube_factorization P hP x q, if_neg hqP])

theorem fermiPrimeCubeIndex_pos (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (x : P → Bool) : 0 < fermiPrimeCubeIndex P x := by
  exact Finset.prod_pos (fun p hp => pow_pos (hP p hp).pos _)

theorem fermiPrimeCubeIndex_odd (P : Finset ℕ) (hP : ∀ p ∈ P, Odd p)
    (x : P → Bool) : Odd (fermiPrimeCubeIndex P x) := by
  exact Finset.prod_induction (fun p => p^(primeCubeExponent P x p)) Odd
    (fun _ _ ha hb => ha.mul hb) (by decide : Odd (1 : ℕ)) (fun p hp => (hP p hp).pow)

theorem fermiPrimeCubeIndex_injective (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Function.Injective (fermiPrimeCubeIndex P) := by
  intro x y hxy
  funext p
  have h := congrArg (fun n : ℕ => n.factorization p) hxy
  rw [fermiPrimeCubeIndex_factorization P hP x p, fermiPrimeCubeIndex_factorization P hP y p] at h
  cases hx : x p <;> cases hy : y p <;> simp_all


/-- The literal normalized GCD kernel is the Boolean prime-product kernel. -/
theorem fermiPrimeCubeIndex_gcd_gram (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (x y : P → Bool) :
    (Nat.gcd (fermiPrimeCubeIndex P x) (fermiPrimeCubeIndex P y) : ℝ)^2 /
      ((fermiPrimeCubeIndex P x : ℝ)*(fermiPrimeCubeIndex P y : ℝ)) =
      fermiBooleanGram (fun p : P => 1/(p : ℝ)) x y := by
  rw [gcdSquareRatio_eq_primeProduct P hP
    (fermiPrimeCubeIndex_pos P hP x).ne' (fermiPrimeCubeIndex_pos P hP y).ne'
    (fermiPrimeCubeIndex_primeFactors_subset P hP x)
    (fermiPrimeCubeIndex_primeFactors_subset P hP y)]
  unfold fermiBooleanGram
  rw [← Finset.prod_coe_sort P (fun p => (1/(p : ℝ))^
    (((fermiPrimeCubeIndex P x).factorization p - (fermiPrimeCubeIndex P y).factorization p) +
      ((fermiPrimeCubeIndex P y).factorization p - (fermiPrimeCubeIndex P x).factorization p)))]
  apply Finset.prod_congr rfl
  intro p _
  rw [fermiPrimeCubeIndex_factorization P hP x p, fermiPrimeCubeIndex_factorization P hP y p]
  cases x p <;> cases y p <;> norm_num

/-- Exact pullback of the native odd-divisor Gram to the finite Boolean prime cube. -/
theorem fermiPrimeCubeIndex_profile_gram (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p) (x y : P → Bool) :
    (∑' m : ℕ, fermiOddDivisorProfile (fermiPrimeCubeIndex P x) m*
      fermiOddDivisorProfile (fermiPrimeCubeIndex P y) m) =
      fermiOddHomogeneousMass*fermiBooleanGram (fun p : P => 1/(p : ℝ)) x y := by
  rw [fermiOddDivisorProfile_gram (fermiPrimeCubeIndex_odd P hodd x)
    (fermiPrimeCubeIndex_odd P hodd y), fermiPrimeCubeIndex_gcd_gram P hP x y]

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
