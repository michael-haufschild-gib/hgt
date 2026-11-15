import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.ArtinSchreierIrreducibility
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RationalFrobeniusPrimitives
import Mathlib.FieldTheory.Galois.Basic

/-!
# Irreducible additive covers of the rational function field

A polynomial of positive degree prime to the characteristic cannot be a
rational Artin–Schreier difference. Consequently its additive root equation
is irreducible. In particular, `Y^p-Y=X^(pt+1)` gives an irreducible cover
in every prime characteristic. In contrast, the Frobenius differences
`X^(p^n)-X` always have explicit trace primitives.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
open GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]

/-- A polynomial degree not divisible by the characteristic forces additive irreducibility. -/
theorem irreducible_ratFunc_artinSchreier_of_degree (g : K[X])
    (hg : g.natDegree ≠ 0) (hdiv : ¬ p ∣ g.natDegree) :
    Irreducible (artinSchreierPolynomial p (algebraMap K[X] (RatFunc K) g)) := by
  apply (irreducible_artinSchreierPolynomial_iff p _).mpr
  rintro ⟨f, hf⟩
  rcases ratFunc_power_sub_degree p (Fact.out : p.Prime).one_lt f g hf with hz | hd
  · exact hg hz
  · exact hdiv hd

/-- Every monomial of degree `pt+1` defines an irreducible Artin–Schreier cover. -/
theorem irreducible_ratFunc_artinSchreier_monomial (t : ℕ) :
    Irreducible (artinSchreierPolynomial p
      (algebraMap K[X] (RatFunc K) (X ^ (p * t + 1)))) := by
  apply irreducible_ratFunc_artinSchreier_of_degree p
  · rw [natDegree_X_pow]
    omega
  · rw [natDegree_X_pow]
    intro hd
    have hrem := Nat.mod_eq_zero_of_dvd hd
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod,
      Nat.zero_add, Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt] at hrem
    exact Nat.one_ne_zero hrem

instance artinSchreierMonomial_irreducible (t : ℕ) :
    Fact (Irreducible (artinSchreierPolynomial p
      (algebraMap K[X] (RatFunc K) (X ^ (p * t + 1))))) :=
  ⟨irreducible_ratFunc_artinSchreier_monomial p t⟩

/-- The function field obtained by adjoining a root of `Y^p-Y=X^(pt+1)`. -/
abbrev ArtinSchreierMonomialField (t : ℕ) :=
  AdjoinRoot (artinSchreierPolynomial p
    (algebraMap K[X] (RatFunc K) (X ^ (p * t + 1))))

/-- The additive cover has degree exactly the characteristic. -/
theorem artinSchreierMonomial_finrank (t : ℕ) :
    Module.finrank (RatFunc K) (ArtinSchreierMonomialField (K := K) p t) = p := by
  rw [(AdjoinRoot.powerBasis (monic_artinSchreierPolynomial p
    (algebraMap K[X] (RatFunc K) (X ^ (p * t + 1)))).ne_zero).finrank,
    AdjoinRoot.powerBasis_dim, natDegree_artinSchreierPolynomial]

instance artinSchreierMonomial_finiteDimensional (t : ℕ) :
    FiniteDimensional (RatFunc K) (ArtinSchreierMonomialField (K := K) p t) :=
  Module.finite_of_finrank_pos (by
    rw [artinSchreierMonomial_finrank]
    exact (Fact.out : p.Prime).pos)

/-- Prime-field translations act faithfully on the irreducible function field. -/
theorem artinSchreierMonomial_deck_faithful (t : ℕ) :
    Function.Injective (artinSchreierDeckEquiv p
      (algebraMap K[X] (RatFunc K) (X ^ (p * t + 1)))) :=
  artinSchreierDeckEquiv_injective p _

/-- Prime-field addition acts on the monomial cover by root translations. -/
def artinSchreierMonomialDeckHom (t : ℕ) :
    Multiplicative (ZMod p) →*
      (ArtinSchreierMonomialField (K := K) p t ≃ₐ[RatFunc K]
        ArtinSchreierMonomialField (K := K) p t) where
  toFun b := artinSchreierDeckEquiv p
    (algebraMap K[X] (RatFunc K) (X ^ (p * t + 1))) b.toAdd
  map_one' := artinSchreierDeckEquiv_zero p _
  map_mul' b c := artinSchreierDeckEquiv_add p _ b.toAdd c.toAdd

/-- Degree bounds force the faithful translations to exhaust every base-field automorphism. -/
theorem artinSchreierMonomialDeckHom_bijective (t : ℕ) :
    Function.Bijective (artinSchreierMonomialDeckHom (K := K) p t) := by
  classical
  have hinj : Function.Injective (artinSchreierMonomialDeckHom (K := K) p t) := by
    intro b c he
    exact Multiplicative.toAdd.injective (artinSchreierMonomial_deck_faithful p t he)
  apply hinj.bijective_of_nat_card_le
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_multiplicative, ZMod.card]
  exact (AlgEquiv.card_le (F := RatFunc K)
    (K := ArtinSchreierMonomialField (K := K) p t)).trans_eq
      (artinSchreierMonomial_finrank p t)

/-- The full group over the rational base is explicitly the additive prime field. -/
def artinSchreierMonomialDeckEquiv (t : ℕ) :
    Multiplicative (ZMod p) ≃*
      (ArtinSchreierMonomialField (K := K) p t ≃ₐ[RatFunc K]
        ArtinSchreierMonomialField (K := K) p t) :=
  MulEquiv.ofBijective (artinSchreierMonomialDeckHom p t)
    (artinSchreierMonomialDeckHom_bijective p t)

/-- There are exactly `p` automorphisms over the rational function field. -/
theorem artinSchreierMonomial_aut_card (t : ℕ) :
    Nat.card (ArtinSchreierMonomialField (K := K) p t ≃ₐ[RatFunc K]
      ArtinSchreierMonomialField (K := K) p t) = p :=
  (Nat.card_congr (artinSchreierMonomialDeckEquiv (K := K) p t).symm.toEquiv).trans
    ((Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod p))

/-- The monomial additive extension is Galois, with no additional splitting hypothesis. -/
theorem artinSchreierMonomial_isGalois (t : ℕ) :
    IsGalois (RatFunc K) (ArtinSchreierMonomialField (K := K) p t) :=
  IsGalois.of_card_aut_eq_finrank _ _ (by
    rw [artinSchreierMonomial_aut_card, artinSchreierMonomial_finrank])

/-- Every automorphism of the additive cover is a power of a single root translation. -/
theorem artinSchreierMonomial_aut_isCyclic (t : ℕ) :
    IsCyclic (ArtinSchreierMonomialField (K := K) p t ≃ₐ[RatFunc K]
      ArtinSchreierMonomialField (K := K) p t) :=
  isCyclic_of_surjective (artinSchreierMonomialDeckHom p t)
    (artinSchreierMonomialDeckHom_bijective p t).2

/-- Frobenius-difference equations have rational trace roots and are never irreducible. -/
theorem not_irreducible_ratFunc_artinSchreier_frobeniusDifference (n : ℕ) :
    ¬ Irreducible (artinSchreierPolynomial p
      (algebraMap K[X] (RatFunc K) (X ^ p ^ n - X))) := by
  rw [irreducible_artinSchreierPolynomial_iff]
  apply not_not.mpr
  have he := (exists_ratFunc_frobenius_primitive_iff (K := K) p 0 n).mpr (one_dvd n)
  simpa only [Nat.zero_add, pow_one] using he

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.irreducible_ratFunc_artinSchreier_of_degree
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.irreducible_ratFunc_artinSchreier_monomial
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.artinSchreierMonomial_finrank
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.artinSchreierMonomial_deck_faithful
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.artinSchreierMonomialDeckHom_bijective
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.artinSchreierMonomialDeckEquiv
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.artinSchreierMonomial_aut_card
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.artinSchreierMonomial_isGalois
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.artinSchreierMonomial_aut_isCyclic
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.not_irreducible_ratFunc_artinSchreier_frobeniusDifference
