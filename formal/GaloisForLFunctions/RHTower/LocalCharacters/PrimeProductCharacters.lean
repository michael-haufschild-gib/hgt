import GaloisForLFunctions.HTGeometry.Topology.ProductCircleCharacters
import GaloisForLFunctions.RHTower.LocalCharacters.PadicFiniteConductor

/-!
# Finite conductor on the product of p-adic unit groups

Every continuous circle character of `∏ p, ℤ_pˣ` is a finite product of
finite residue-unit characters. Continuity first removes all but finitely
many prime coordinates; local finite-conductor descent handles each
remaining coordinate. The resulting finite quotient character is unique.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.RHTower.LocalCharacters
open GaloisForLFunctions.HTGeometry.ProductCircleCharacters

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The prime-power reductions at a finite set of primes. -/
def primeProductReduction (S : Finset Nat.Primes) (n : Nat.Primes → ℕ) :
    (∀ p : Nat.Primes, ℤ_[p]ˣ) →* (∀ p : S, (ZMod (p.1.1 ^ n p.1))ˣ) where
  toFun u p := fieldOnePadicUnitReduction p.1.1 (n p.1) (u p.1)
  map_one' := by funext p; exact map_one _
  map_mul' u v := by funext p; exact map_mul _ _ _

theorem continuous_primeProductReduction (S : Finset Nat.Primes) (n : Nat.Primes → ℕ) :
    Continuous (primeProductReduction S n) := by
  apply continuous_pi
  intro p
  exact (fieldOnePadicUnitReduction_continuous p.1.1 (n p.1)).comp (continuous_apply p.1)

theorem primeProductReduction_surjective (S : Finset Nat.Primes) (n : Nat.Primes → ℕ) :
    Function.Surjective (primeProductReduction S n) := by
  intro r
  choose u hu using fun p : S => fieldOnePadicUnitReduction_surjective p.1.1 (n p.1) (r p)
  refine ⟨fun p => if h : p ∈ S then u ⟨p, h⟩ else 1, ?_⟩
  funext p
  change fieldOnePadicUnitReduction p.1.1 (n p.1)
    (if h : p.1 ∈ S then u ⟨p.1, h⟩ else 1) = r p
  rw [dif_pos p.2]
  exact hu p

/-- The local character formula has only finitely many prime factors. -/
theorem exists_finite_prime_character_product
    (χ : (∀ p : Nat.Primes, ℤ_[p]ˣ) →ₜ* Circle) :
    ∃ S : Finset Nat.Primes, ∃ n : Nat.Primes → ℕ,
      ∃ θ : ∀ p : Nat.Primes, (ZMod (p.1 ^ n p))ˣ →* Circle,
        ∀ u : ∀ p : Nat.Primes, ℤ_[p]ˣ,
          χ u = ∏ p ∈ S, θ p (fieldOnePadicUnitReduction p.1 (n p) (u p)) := by
  obtain ⟨S, hS⟩ := exists_finite_coordinate_product χ
  have hlocal (p : Nat.Primes) :
      ∃ n : ℕ, ∃ θ : (ZMod (p.1 ^ n))ˣ →* Circle,
        ∀ u : ℤ_[p]ˣ, θ (fieldOnePadicUnitReduction p.1 n u) = coordinateCharacter χ p u := by
    obtain ⟨n, θ, hθ, _⟩ := exists_unique_finite_character p.1 (coordinateCharacter χ p)
    exact ⟨n, θ, hθ⟩
  choose n θ hθ using hlocal
  refine ⟨S, n, θ, fun u => ?_⟩
  rw [hS]
  apply Finset.prod_congr rfl
  intro p _
  exact (hθ p (u p)).symm

/-- Every continuous character descends uniquely to a finite product of residue-unit groups. -/
theorem exists_unique_prime_product_character
    (χ : (∀ p : Nat.Primes, ℤ_[p]ˣ) →ₜ* Circle) :
    ∃ S : Finset Nat.Primes, ∃ n : Nat.Primes → ℕ,
      ∃! θ : (∀ p : S, (ZMod (p.1.1 ^ n p.1))ˣ) →* Circle,
        ∀ u : ∀ p : Nat.Primes, ℤ_[p]ˣ, θ (primeProductReduction S n u) = χ u := by
  obtain ⟨S, n, θ, hχ⟩ := exists_finite_prime_character_product χ
  have hker : (primeProductReduction S n).ker ≤ χ.toMonoidHom.ker := by
    intro u hu
    change χ u = 1
    rw [hχ]
    apply Finset.prod_eq_one
    intro p hp
    have hr : fieldOnePadicUnitReduction p.1 (n p) (u p) = 1 := congrFun hu ⟨p, hp⟩
    rw [hr, map_one]
  let ψ := (primeProductReduction S n).liftOfSurjective
    (primeProductReduction_surjective S n) ⟨χ.toMonoidHom, hker⟩
  have hψ (u : ∀ p : Nat.Primes, ℤ_[p]ˣ) : ψ (primeProductReduction S n u) = χ u := by
    simp [ψ]
  refine ⟨S, n, ψ, hψ, ?_⟩
  intro φ hφ
  apply MonoidHom.ext
  intro r
  obtain ⟨u, rfl⟩ := primeProductReduction_surjective S n r
  exact (hφ u).trans (hψ u).symm

#print axioms exists_finite_prime_character_product
#print axioms exists_unique_prime_product_character

end GaloisForLFunctions.RHTower.LocalCharacters
