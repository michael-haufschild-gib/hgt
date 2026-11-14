import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.ArtinSchreierCoordinateReduction
import Mathlib.FieldTheory.Finite.Basic

/-!
# Faithful deck translations and equivariant Frobenius reduction

For every coefficient ring of prime characteristic, translation of an
Artin–Schreier root by a prime-field scalar extends to an algebra automorphism.
The additive composition law makes these the cyclic deck transformations.
Over a domain the action is faithful, without irreducibility of the defining
polynomial. The trace substitution removing powers of Frobenius intertwines
the entire action, refining the characteristic reduction in Proposition 2.1
of Kazemifard–Tafazolian, *Automorphisms of Kummer and Artin–Schreier curves
defined by Chebyshev polynomials*.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Polynomial
variable {A : Type*} [CommRing A] (p : ℕ) [Fact p.Prime] [CharP A p]

/-- Translate the universal root by a prime-field scalar. -/
def artinSchreierDeckHom (f : A) (b : ZMod p) :
    AdjoinRoot (artinSchreierPolynomial p f) →ₐ[A]
      AdjoinRoot (artinSchreierPolynomial p f) :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId A _)
    (AdjoinRoot.root (artinSchreierPolynomial p f) +
      algebraMap A _ (ZMod.castHom (dvd_refl p) A b)) (by
    have hr := AdjoinRoot.eval₂_root (artinSchreierPolynomial p f)
    change (X ^ p - X - C f).eval₂
      (AdjoinRoot.of (artinSchreierPolynomial p f))
      (AdjoinRoot.root (artinSchreierPolynomial p f)) = 0 at hr
    change (X ^ p - X - C f).eval₂
      (algebraMap A (AdjoinRoot (artinSchreierPolynomial p f)))
      (AdjoinRoot.root (artinSchreierPolynomial p f) +
        algebraMap A _ (ZMod.castHom (dvd_refl p) A b)) = 0
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at hr ⊢
    have hb : (ZMod.castHom (dvd_refl p) A b) ^ p =
        ZMod.castHom (dvd_refl p) A b := by rw [← map_pow, ZMod.pow_card]
    -- Prove the binomial identity before quotienting: the quotient may be trivial.
    have hadd := congrArg (AdjoinRoot.mk (artinSchreierPolynomial p f))
      (add_pow_char (X : A[X]) (C (ZMod.castHom (dvd_refl p) A b)) p)
    simp only [map_pow, map_add, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at hadd
    rw [AdjoinRoot.algebraMap_eq, hadd, ← map_pow, hb]
    linear_combination hr)

@[simp] theorem artinSchreierDeckHom_root (f : A) (b : ZMod p) :
    artinSchreierDeckHom p f b (AdjoinRoot.root (artinSchreierPolynomial p f)) =
      AdjoinRoot.root (artinSchreierPolynomial p f) +
        algebraMap A _ (ZMod.castHom (dvd_refl p) A b) := by
  simp [artinSchreierDeckHom]

@[simp] theorem artinSchreierDeckHom_zero (f : A) :
    artinSchreierDeckHom p f 0 = AlgHom.id A _ := by
  apply AdjoinRoot.algHom_ext
  simp

@[simp] theorem artinSchreierDeckHom_add (f : A) (b c : ZMod p) :
    artinSchreierDeckHom p f (b + c) =
      (artinSchreierDeckHom p f b).comp (artinSchreierDeckHom p f c) := by
  apply AdjoinRoot.algHom_ext
  simp only [AlgHom.comp_apply, artinSchreierDeckHom_root, map_add, AlgHom.commutes,
    add_assoc]

/-- Opposite prime-field translations are inverse algebra automorphisms. -/
def artinSchreierDeckEquiv (f : A) (b : ZMod p) :
    AdjoinRoot (artinSchreierPolynomial p f) ≃ₐ[A]
      AdjoinRoot (artinSchreierPolynomial p f) :=
  AlgEquiv.ofAlgHom (artinSchreierDeckHom p f b) (artinSchreierDeckHom p f (-b))
    (by rw [← artinSchreierDeckHom_add, add_neg_cancel, artinSchreierDeckHom_zero])
    (by rw [← artinSchreierDeckHom_add, neg_add_cancel, artinSchreierDeckHom_zero])

@[simp] theorem artinSchreierDeckEquiv_root (f : A) (b : ZMod p) :
    artinSchreierDeckEquiv p f b (AdjoinRoot.root (artinSchreierPolynomial p f)) =
      AdjoinRoot.root (artinSchreierPolynomial p f) +
        algebraMap A _ (ZMod.castHom (dvd_refl p) A b) :=
  artinSchreierDeckHom_root p f b

@[simp] theorem artinSchreierDeckEquiv_zero (f : A) :
    artinSchreierDeckEquiv p f 0 = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro x
  exact congrArg (fun k : _ →ₐ[A] _ => k x) (artinSchreierDeckHom_zero p f)

@[simp] theorem artinSchreierDeckEquiv_add (f : A) (b c : ZMod p) :
    artinSchreierDeckEquiv p f (b + c) =
      (artinSchreierDeckEquiv p f c).trans (artinSchreierDeckEquiv p f b) := by
  apply AlgEquiv.ext
  intro x
  exact congrArg (fun k : _ →ₐ[A] _ => k x) (artinSchreierDeckHom_add p f b c)

private theorem translated_root (f g : A[X]) (t : A)
    (h : g = f.comp (X + C t)) :
    (Eq.mpr (congrArg (fun q => AdjoinRoot q ≃ₐ[A] AdjoinRoot f) h)
      (HTGeometry.adjoinRootTranslationEquiv f t)) (AdjoinRoot.root g) =
      AdjoinRoot.root f - algebraMap A _ t := by
  subst g
  simp [HTGeometry.adjoinRootTranslationEquiv, HTGeometry.adjoinRootTranslationHom]

/-- The root of the higher-degree equation maps to the root plus the Frobenius trace. -/
theorem artinSchreierCoordinateReduction_root (s : ℕ) (f : A) :
    artinSchreierCoordinateReduction p s f
      (AdjoinRoot.root (artinSchreierPolynomial p (f ^ (p ^ s)))) =
    AdjoinRoot.root (artinSchreierPolynomial p f) +
      algebraMap A _ (frobeniusTraceSum p 1 s f) := by
  simpa only [artinSchreierCoordinateReduction, map_neg, sub_neg_eq_add] using
    translated_root (artinSchreierPolynomial p f) _
      (-frobeniusTraceSum p 1 s f) (artinSchreierPolynomial_trace_comp p s f).symm

/-- Frobenius reduction intertwines the deck actions on the entire root algebras. -/
theorem artinSchreierCoordinateReduction_deck (s : ℕ) (f : A) (b : ZMod p) :
    (artinSchreierDeckEquiv p (f ^ (p ^ s)) b).trans
        (artinSchreierCoordinateReduction p s f) =
      (artinSchreierCoordinateReduction p s f).trans (artinSchreierDeckEquiv p f b) := by
  have h :
      ((artinSchreierCoordinateReduction p s f).toAlgHom.comp
        (artinSchreierDeckEquiv p (f ^ (p ^ s)) b).toAlgHom) =
      ((artinSchreierDeckEquiv p f b).toAlgHom.comp
        (artinSchreierCoordinateReduction p s f).toAlgHom) := by
    apply AdjoinRoot.algHom_ext
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, artinSchreierDeckEquiv_root,
      artinSchreierCoordinateReduction_root, map_add, AlgEquiv.commutes]
    abel
  apply AlgEquiv.ext
  intro x
  exact congrArg (fun k : _ →ₐ[A] _ => k x) h

omit [CharP A p] in
/-- An Artin–Schreier polynomial has degree equal to the prime exponent. -/
theorem degree_artinSchreierPolynomial [Nontrivial A] (f : A) :
    (artinSchreierPolynomial p f).degree = p := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hd : (X ^ p - X : A[X]).degree = p := by
    rw [degree_sub_eq_left_of_degree_lt, degree_X_pow]
    rw [degree_X, degree_X_pow]
    exact_mod_cast hp
  have hc : (C f).degree < (X ^ p - X : A[X]).degree := by
    rw [hd]
    exact degree_C_le.trans_lt (by exact_mod_cast (Fact.out : p.Prime).pos)
  exact (degree_sub_eq_left_of_degree_lt hc).trans hd

/-- Distinct prime-field scalars induce distinct deck automorphisms over any domain. -/
theorem artinSchreierDeckEquiv_injective [IsDomain A] (f : A) :
    Function.Injective (artinSchreierDeckEquiv p f) := by
  intro b c h
  have hr := congrArg (fun e : _ ≃ₐ[A] _ =>
    e (AdjoinRoot.root (artinSchreierPolynomial p f))) h
  rw [artinSchreierDeckEquiv_root, artinSchreierDeckEquiv_root] at hr
  have hinj := AdjoinRoot.of.injective_of_degree_ne_zero
    (f := artinSchreierPolynomial p f) (by
      rw [degree_artinSchreierPolynomial]
      exact_mod_cast (Fact.out : p.Prime).ne_zero)
  exact (ZMod.castHom (dvd_refl p) A).injective (hinj (add_left_cancel hr))

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.artinSchreierDeckEquiv_add
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.artinSchreierCoordinateReduction_deck
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.artinSchreierDeckEquiv_injective
