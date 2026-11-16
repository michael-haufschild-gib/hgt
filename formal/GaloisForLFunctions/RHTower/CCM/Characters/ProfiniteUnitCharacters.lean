import GaloisForLFunctions.RHTower.CCM.Characters.ProfiniteUnitProduct
import GaloisForLFunctions.RHTower.LocalCharacters.PrimeProductCharacters

/-!
# Continuous characters of the actual rational profinite units

Every continuous character of the integral finite ideles factors uniquely
through finitely many prime-power unit reductions. Conversely every such
finite character defines a continuous character of the actual profinite
group. Thus finite ramification and finite local depth follow from continuity.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.RHTower.CCMCharacters
open LocalCharacters GaloisForLFunctions.HTGeometry.ProductCircleCharacters

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- Pullback along the actual topological product decomposition. -/
def productPullback (χ : CCMRationalProfiniteUnit →ₜ* Circle) :
    (∀ p : Nat.Primes, ℤ_[p]ˣ) →ₜ* Circle :=
  χ.comp { toMonoidHom := profiniteUnitProductEquiv.toMulEquiv.toMonoidHom
           continuous_toFun := profiniteUnitProductEquiv.continuous_toFun }

/-- Finite prime-power reduction of an actual integral finite idele. -/
def profiniteUnitReduction (S : Finset Nat.Primes) (n : Nat.Primes → ℕ) :
    CCMRationalProfiniteUnit →* (∀ p : S, (ZMod (p.1.1 ^ n p.1))ˣ) :=
  (primeProductReduction S n).comp profiniteUnitProductEquiv.symm.toMulEquiv.toMonoidHom

theorem continuous_profiniteUnitReduction (S : Finset Nat.Primes) (n : Nat.Primes → ℕ) :
    Continuous (profiniteUnitReduction S n) :=
  (continuous_primeProductReduction S n).comp profiniteUnitProductEquiv.symm.continuous_toFun

theorem profiniteUnitReduction_surjective (S : Finset Nat.Primes) (n : Nat.Primes → ℕ) :
    Function.Surjective (profiniteUnitReduction S n) :=
  (primeProductReduction_surjective S n).comp profiniteUnitProductEquiv.symm.toMulEquiv.surjective

/-- A finite residue-unit character defines a continuous character on the actual group. -/
def finiteDataCharacter (S : Finset Nat.Primes) (n : Nat.Primes → ℕ)
    (θ : (∀ p : S, (ZMod (p.1.1 ^ n p.1))ˣ) →* Circle) :
    CCMRationalProfiniteUnit →ₜ* Circle where
  toMonoidHom := θ.comp (profiniteUnitReduction S n)
  continuous_toFun := (continuous_of_discreteTopology : Continuous θ).comp
    (continuous_profiniteUnitReduction S n)

/-- An actual profinite-unit character is a finite product of local residue characters. -/
theorem exists_finite_prime_formula (χ : CCMRationalProfiniteUnit →ₜ* Circle) :
    ∃ S : Finset Nat.Primes, ∃ n : Nat.Primes → ℕ,
      ∃ θ : ∀ p : Nat.Primes, (ZMod (p.1 ^ n p))ˣ →* Circle,
        ∀ u : CCMRationalProfiniteUnit,
          χ u = ∏ p ∈ S, θ p (fieldOnePadicUnitReduction p.1 (n p)
            (profiniteUnitProductEquiv.symm u p)) := by
  obtain ⟨S, n, θ, hθ⟩ := exists_finite_prime_character_product (productPullback χ)
  refine ⟨S, n, θ, fun u => ?_⟩
  have h := hθ (profiniteUnitProductEquiv.symm u)
  change χ (profiniteUnitProductMulEquiv (profiniteUnitProductMulEquiv.symm u)) = _ at h
  rwa [MulEquiv.apply_symm_apply] at h

/-- Every continuous profinite-unit character descends uniquely to a finite residue quotient. -/
theorem exists_unique_finite_quotient_character (χ : CCMRationalProfiniteUnit →ₜ* Circle) :
    ∃ S : Finset Nat.Primes, ∃ n : Nat.Primes → ℕ,
      ∃! θ : (∀ p : S, (ZMod (p.1.1 ^ n p.1))ˣ) →* Circle,
        ∀ u : CCMRationalProfiniteUnit, θ (profiniteUnitReduction S n u) = χ u := by
  obtain ⟨S, n, θ, hθ, _⟩ := exists_unique_prime_product_character (productPullback χ)
  have hfactor (u : CCMRationalProfiniteUnit) : θ (profiniteUnitReduction S n u) = χ u := by
    have h := hθ (profiniteUnitProductEquiv.symm u)
    change θ (profiniteUnitReduction S n u) =
      χ (profiniteUnitProductMulEquiv (profiniteUnitProductMulEquiv.symm u)) at h
    rwa [MulEquiv.apply_symm_apply] at h
  refine ⟨S, n, θ, hfactor, ?_⟩
  intro ψ hψ
  apply MonoidHom.ext
  intro r
  obtain ⟨u, rfl⟩ := profiniteUnitReduction_surjective S n r
  exact (hψ u).trans (hfactor u).symm

/-- Finite residue data exhaust all continuous characters of the literal profinite units. -/
theorem exists_finiteDataCharacter (χ : CCMRationalProfiniteUnit →ₜ* Circle) :
    ∃ S : Finset Nat.Primes, ∃ n : Nat.Primes → ℕ,
      ∃ θ : (∀ p : S, (ZMod (p.1.1 ^ n p.1))ˣ) →* Circle,
        χ = finiteDataCharacter S n θ := by
  obtain ⟨S, n, θ, hθ, _⟩ := exists_unique_finite_quotient_character χ
  refine ⟨S, n, θ, ?_⟩
  apply ContinuousMonoidHom.ext
  intro u
  exact (hθ u).symm

/-- Only finitely many prime restrictions of an actual profinite-unit character are nontrivial. -/
theorem finite_nontrivial_prime_restrictions (χ : CCMRationalProfiniteUnit →ₜ* Circle) :
    {p : Nat.Primes | coordinateCharacter (productPullback χ) p ≠ 1}.Finite :=
  finite_nontrivial_coordinates (productPullback χ)

#print axioms exists_unique_finite_quotient_character
#print axioms exists_finite_prime_formula
#print axioms exists_finiteDataCharacter
#print axioms finite_nontrivial_prime_restrictions

end GaloisForLFunctions.RHTower.CCMCharacters
