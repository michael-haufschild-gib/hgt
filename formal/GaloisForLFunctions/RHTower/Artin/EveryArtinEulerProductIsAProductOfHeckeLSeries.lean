import GaloisForLFunctions.RHTower.Artin.TheReciprocityLawForLinearCharacters
import GaloisForLFunctions.RHTower.Artin.ArtinEulerProductIsAProductOfAbelianEulerProducts

/-!
# Every Artin Euler product is a product of integer powers of Hecke `L`-series

Let `L/K` be a Galois extension of number fields with group `G` and `ρ` a representation of
`G`. There are integers `n_q`, for finitely many pairs `q = (E, χ)` of a Brauer-elementary
subgroup `E ≤ G` and a linear character `χ` of `E`, and for every pair an integer `c_q ≥ 1` and
a ray class character `ψ_q` modulo `(c_q) ∞` of the fixed field `F_q` of `E`, such that for
`Re s > 1`

  `L(s, ρ, L/K) = Π_q ( L(s, ψ_q) · Π_{v | c_q} (1 − (χ_q, v) N(v)^{-s})^{-1} )^{n_q}`

(`exists_artinEulerProduct_eq_prod_zpow_heckeL`). The factors at the primes `v | c_q` of `F_q`
are finitely many Euler factors of the linear characters `χ_q`.

Proof: Brauer's theorem writes the Euler product of `ρ` as a product of integer powers of the
Euler products of the `χ_q` over the fixed fields; by the reciprocity law each of them is a
Hecke `L`-series up to the Euler factors at the modulus.
-/

open scoped Classical BigOperators NumberField
open NumberField IsDedekindDomain

noncomputable section

universe u

namespace GaloisForLFunctions

open HeckeLFunctions

variable (K L : Type u) {G V : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The Hecke side of a Brauer pair `q = (E, χ)`: for a ray class character `ψ` modulo `(c) ∞`
of the fixed field of `E`, the product `L(s, ψ) · Π_{v | c} (1 − (χ, v) N(v)^{-s})^{-1}`. -/
def brauerHeckeEulerProduct (q : brauerElementaryMonomialIndex G) (c : ℕ) [NeZero c]
    (ψ : HeckeCharacter (normModulus
      (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L) c)) (s : ℂ) : ℂ :=
  heckeL (normModulus (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L) c)
      ψ s *
    ∏ v ∈ (finite_primes_dvd (normModulus
        (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L) c)).toFinset,
      (1 - artinSymbol (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L) L
        q.2 v * (v.asIdeal.absNorm : ℂ) ^ (-s))⁻¹

/-- **The abelian Euler product of a Brauer pair is a Hecke `L`-series of the fixed field**, up
to the Euler factors at the modulus. -/
theorem exists_brauerAbelianEulerProduct_eq_brauerHeckeEulerProduct
    (q : brauerElementaryMonomialIndex G) :
    ∃ (c : ℕ) (_ : NeZero c) (ψ : HeckeCharacter (normModulus
        (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L) c)),
      ∀ s : ℂ, 1 < s.re →
        brauerAbelianEulerProduct K L q s = brauerHeckeEulerProduct K L q c ψ s := by
  obtain ⟨c, hc, ψ, -, hψ⟩ := exists_artinEulerProduct_linearCharacter_eq_heckeL_mul
    (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L) L q.2
  exact ⟨c, hc, ψ, hψ⟩

/-- **Every Artin Euler product is a product of integer powers of Hecke `L`-series** of fixed
fields of Brauer-elementary subgroups, each with finitely many Euler factors at its modulus,
for `Re s > 1`. -/
theorem exists_artinEulerProduct_eq_prod_zpow_heckeL (ρ : Representation ℂ G V) :
    ∃ (n : brauerElementaryMonomialIndex G →₀ ℤ) (c : brauerElementaryMonomialIndex G → ℕ)
      (_ : ∀ q, NeZero (c q))
      (ψ : ∀ q, HeckeCharacter (normModulus
        (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L) (c q))),
      ∀ s : ℂ, 1 < s.re →
        numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L) ρ s =
          n.prod fun q k => brauerHeckeEulerProduct K L q (c q) (ψ q) s ^ k := by
  obtain ⟨n, hn⟩ := exists_artinEulerProduct_eq_prod_zpow_abelian K L ρ
  choose c hc ψ hψ using fun q : brauerElementaryMonomialIndex G =>
    exists_brauerAbelianEulerProduct_eq_brauerHeckeEulerProduct K L q
  refine ⟨n, c, hc, ψ, fun s hs => ?_⟩
  rw [hn s hs]
  exact Finsupp.prod_congr fun q _ => by rw [hψ q s hs]

end GaloisForLFunctions
