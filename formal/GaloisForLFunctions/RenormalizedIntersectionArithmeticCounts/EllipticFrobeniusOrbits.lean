import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticClosedPoints
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.FiniteFieldOrbitCounts
import Mathlib.FieldTheory.Normal.Basic

/-!
# Closed places as actual Frobenius orbits

Finite-field normality and cyclic Galois groups make Frobenius transitive
on residue-field embeddings. Actual affine point maps have a common prime
kernel exactly when a Frobenius power joins them. The projective point
comparison retains the unique point at infinity and its fixed orbit.
-/

noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open FiniteField
variable (F K E : Type*) [Field F] [Field K] [Field E]
  [Algebra F K] [Algebra F E] [Fintype F] [Finite K] [Finite E]

/-- Frobenius is transitive on the actual embeddings of a finite residue field. -/
theorem finiteField_embeddings_frobenius_transitive (f g : K →ₐ[F] E) :
    ∃ n : ℕ, ∀ x : K,
      (frobeniusAlgEquivOfAlgebraic F E ^ n) (f x) = g x := by
  letI : Algebra K E := f.toRingHom.toAlgebra
  letI : IsScalarTower F K E := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  let σ := g.restrictNormal' K
  obtain ⟨k, hk⟩ := (bijective_frobeniusAlgEquivOfAlgebraic_pow F K).surjective σ
  have hc (n : ℕ) (x : K) :
      f ((frobeniusAlgEquivOfAlgebraic F K ^ n) x) =
        (frobeniusAlgEquivOfAlgebraic F E ^ n) (f x) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', pow_succ']
      change f (((frobeniusAlgEquivOfAlgebraic F K ^ n) x) ^ Fintype.card F) =
        ((frobeniusAlgEquivOfAlgebraic F E ^ n) (f x)) ^ Fintype.card F
      rw [map_pow, ih]
  refine ⟨k.val, fun x => ?_⟩
  have hg := g.restrictNormal_commutes K x
  change f (σ x) = g x at hg
  rw [← hk] at hg
  exact (hc k.val x).symm.trans hg

#print axioms finiteField_embeddings_frobenius_transitive
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open FiniteField
open GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
variable (E : Type*) [Field E] [Algebra Constants E] [Finite E]

/-- Frobenius acts on the actual coordinate-algebra point maps. -/
def ellipticAffineFrobenius : Equiv.Perm (A →ₐ[Constants] E) where
  toFun f := (frobeniusAlgEquivOfAlgebraic Constants E).toAlgHom.comp f
  invFun f := (frobeniusAlgEquivOfAlgebraic Constants E).symm.toAlgHom.comp f
  left_inv f := AlgHom.ext fun a => (frobeniusAlgEquivOfAlgebraic Constants E).symm_apply_apply (f a)
  right_inv f := AlgHom.ext fun a => (frobeniusAlgEquivOfAlgebraic Constants E).apply_symm_apply (f a)

/-- Iteration is the coordinatewise arithmetic Frobenius power. -/
theorem ellipticAffineFrobenius_pow (n : ℕ) (f : A →ₐ[Constants] E) (a : A) :
    ((ellipticAffineFrobenius E ^ n) f) a =
      (frobeniusAlgEquivOfAlgebraic Constants E ^ n) (f a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ']
    change (frobeniusAlgEquivOfAlgebraic Constants E) (((ellipticAffineFrobenius E ^ n) f) a) = _
    rw [ih]
    rfl

/-- Frobenius preserves the actual prime kernel of a point map. -/
theorem ellipticAffineFrobenius_place (n : ℕ) (f : A →ₐ[Constants] E) :
    affinePointPlace E ((ellipticAffineFrobenius E ^ n) f) = affinePointPlace E f := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  ext a
  change ((ellipticAffineFrobenius E ^ n) f) a = 0 ↔ f a = 0
  rw [ellipticAffineFrobenius_pow]
  exact (frobeniusAlgEquivOfAlgebraic Constants E ^ n).map_eq_zero_iff

/-- Two actual affine points lie over the same closed place exactly when Frobenius joins them. -/
theorem ellipticAffine_same_place_iff_frobenius (f g : A →ₐ[Constants] E) :
    affinePointPlace E f = affinePointPlace E g ↔
      ∃ n : ℕ, (ellipticAffineFrobenius E ^ n) f = g := by
  constructor
  · intro h
    let v := affinePointPlace E f
    let f' := affinePointFiberEquiv E v ⟨f, rfl⟩
    let g' := affinePointFiberEquiv E v ⟨g, h.symm⟩
    obtain ⟨n, hn⟩ := finiteField_embeddings_frobenius_transitive Constants
      (A ⧸ v.asIdeal) E f' g'
    refine ⟨n, AlgHom.ext fun a => ?_⟩
    rw [ellipticAffineFrobenius_pow]
    exact hn (Ideal.Quotient.mk v.asIdeal a)
  · rintro ⟨n, rfl⟩
    exact (ellipticAffineFrobenius_place E n f).symm

/-- Add the unique projective place at infinity to the affine prime-kernel map. -/
def ellipticPointPlace (p : Points E) : Option (IsDedekindDomain.HeightOneSpectrum A) :=
  (pointsAlgHomEquiv E p).map (affinePointPlace E)

/-- Arithmetic Frobenius powers on actual projective points, with infinity fixed. -/
def ellipticPointFrobeniusPower (n : ℕ) (p : Points E) : Points E :=
  (pointsAlgHomEquiv E).symm ((pointsAlgHomEquiv E p).map (ellipticAffineFrobenius E ^ n))

private theorem option_same_place_iff_frobenius
    (f g : Option (A →ₐ[Constants] E)) :
    f.map (affinePointPlace E) = g.map (affinePointPlace E) ↔
      ∃ n : ℕ, f.map (ellipticAffineFrobenius E ^ n) = g := by
  cases f with
  | none => cases g <;> simp
  | some f =>
    cases g with
    | none => simp
    | some g =>
      simp only [Option.map_some, Option.some.injEq]
      exact ellipticAffine_same_place_iff_frobenius E f g

/-- Closed-place fibres are exactly the arithmetic Frobenius orbits of projective points. -/
theorem ellipticPoint_same_place_iff_frobenius (p q : Points E) :
    ellipticPointPlace E p = ellipticPointPlace E q ↔
      ∃ n : ℕ, ellipticPointFrobeniusPower E n p = q := by
  rw [ellipticPointPlace, ellipticPointPlace, option_same_place_iff_frobenius]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [ellipticPointFrobeniusPower, hn, Equiv.symm_apply_apply]
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h := congrArg (pointsAlgHomEquiv E) hn
    simpa only [ellipticPointFrobeniusPower, Equiv.apply_symm_apply] using h

/-- The zeroth arithmetic Frobenius power fixes every projective point. -/
theorem ellipticPointFrobeniusPower_zero (p : Points E) :
    ellipticPointFrobeniusPower E 0 p = p := by
  simp [ellipticPointFrobeniusPower]

#print axioms ellipticPointFrobeniusPower_zero

/-- The constructed powers satisfy the actual Frobenius semigroup law. -/
theorem ellipticPointFrobeniusPower_add (n m : ℕ) (p : Points E) :
    ellipticPointFrobeniusPower E (n + m) p =
      ellipticPointFrobeniusPower E n (ellipticPointFrobeniusPower E m p) := by
  unfold ellipticPointFrobeniusPower
  rw [Equiv.apply_symm_apply]
  congr 1
  cases pointsAlgHomEquiv E p with
  | none => rfl
  | some f =>
    simp only [Option.map_some, pow_add, Equiv.Perm.mul_apply]

#print axioms ellipticPoint_same_place_iff_frobenius
#print axioms ellipticPointFrobeniusPower_add
#print axioms ellipticAffineFrobenius_pow
#print axioms ellipticAffineFrobenius_place
#print axioms ellipticAffine_same_place_iff_frobenius
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
