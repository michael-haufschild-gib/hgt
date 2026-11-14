import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerOriginRamification
import Mathlib.RingTheory.Polynomial.Quotient

/-!
# The full constant field of a Kummer cover

The residue field at the normalized origin is the specified constant field.
An algebraic constant and its inverse are integral over the polynomial base;
thus a nonzero algebraic constant is a unit in the normalization and cannot
vanish at this place. Specialization therefore forces every algebraic
constant to belong to the original finite field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial

/-- A rational residue field rules out additional algebraic constants in the fraction field. -/
theorem constant_of_integral_of_rational_residue
    {k A L : Type*} [Field k] [CommRing A] [Field L]
    [Algebra k A] [Algebra k L] [Algebra A L] [IsScalarTower k A L]
    (P : Ideal (integralClosure A L)) [P.IsPrime]
    (hsurj : Function.Surjective (algebraMap k (integralClosure A L ⧸ P)))
    {x : L} (hx : IsIntegral k x) : ∃ a : k, algebraMap k L a = x := by
  let xB : integralClosure A L := ⟨x, hx.tower_top⟩
  obtain ⟨a, ha⟩ := hsurj (Ideal.Quotient.mk P xB)
  refine ⟨a, ?_⟩
  by_contra h
  have hne : x - algebraMap k L a ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hy : IsIntegral k (x - algebraMap k L a) := hx.sub (isIntegral_algebraMap)
  let yB : integralClosure A L := xB - algebraMap k (integralClosure A L) a
  let vB : integralClosure A L := ⟨(x - algebraMap k L a)⁻¹, hy.inv.tower_top⟩
  have hunit : IsUnit yB := by
    refine ⟨⟨yB, vB, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      exact mul_inv_cancel₀ hne
    · apply Subtype.ext
      exact inv_mul_cancel₀ hne
  have hzero : Ideal.Quotient.mk P yB = 0 := by
    change Ideal.Quotient.mk P (xB - algebraMap k (integralClosure A L) a) = 0
    rw [map_sub, Ideal.Quotient.mk_algebraMap, ha, sub_self]
  exact not_isUnit_zero (hzero ▸ hunit.map (Ideal.Quotient.mk P))

/-- Evaluation at zero identifies the residue field of the polynomial origin. -/
private def polynomialOriginResidueEquiv (K : Type*) [Field K] :
    (K[X] ⧸ Ideal.span {(X : K[X])}) ≃ₐ[K] K :=
  (Ideal.quotientEquivAlgOfEq K
    (show Ideal.span {(X : K[X])} = Ideal.span {X - C (0 : K)} by rw [map_zero, sub_zero])).trans
      (Polynomial.quotientSpanXSubCAlgEquiv (0 : K))

variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)

/-- Every residue at the normalized origin is represented by a constant. -/
theorem squareKummerOrigin_residue_surjective : Function.Surjective
    (algebraMap (SquareConstantField p s)
      (SquareKummerNormalization p s c b R ⧸ squareKummerOriginIdeal p s c b R)) := by
  letI : (Ideal.span {(X : (SquareConstantField p s)[X])}).IsMaximal :=
    ((Ideal.span_singleton_prime X_ne_zero).mpr prime_X).isMaximal
      (mt Ideal.span_singleton_eq_bot.mp X_ne_zero)
  letI := Ideal.Quotient.field (Ideal.span {(X : (SquareConstantField p s)[X])})
  have hdim := squareKummerOriginIdeal_inertia p s c b R
  rw [Ideal.inertiaDeg'_algebraMap] at hdim
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hdim
  have hsurj := (bijective_algebraMap_of_linearEquiv e).surjective
  intro x
  obtain ⟨y, hy⟩ := hsurj x
  let e0 := polynomialOriginResidueEquiv (SquareConstantField p s)
  have hbase : algebraMap (SquareConstantField p s)
      ((SquareConstantField p s)[X] ⧸ Ideal.span {(X : (SquareConstantField p s)[X])}) (e0 y) = y := by
    apply e0.injective
    rw [e0.commutes]
    rfl
  refine ⟨e0 y, ?_⟩
  rw [IsScalarTower.algebraMap_apply (SquareConstantField p s)
    ((SquareConstantField p s)[X] ⧸ Ideal.span {(X : (SquareConstantField p s)[X])}), hbase, hy]

/-- The residue field of the normalized origin is the stated constant field. -/
def squareKummerOriginResidueEquiv :
    (SquareKummerNormalization p s c b R ⧸ squareKummerOriginIdeal p s c b R)
      ≃ₐ[SquareConstantField p s] SquareConstantField p s :=
  (AlgEquiv.ofBijective (Algebra.ofId _ _)
    ⟨(algebraMap (SquareConstantField p s) _).injective,
      squareKummerOrigin_residue_surjective p s c b R⟩).symm

/-- Every element of the Kummer field algebraic over its constants is already constant. -/
theorem squareKummer_constantField (x : SquareKummerField p s c b R)
    (hx : IsAlgebraic (SquareConstantField p s) x) :
    ∃ a : SquareConstantField p s, algebraMap (SquareConstantField p s)
      (SquareKummerField p s c b R) a = x :=
  constant_of_integral_of_rational_residue (squareKummerOriginIdeal p s c b R)
    (squareKummerOrigin_residue_surjective p s c b R) hx.isIntegral

/-- The integral closure of the constants inside the Kummer field is exactly the constants. -/
theorem squareKummer_integralConstants :
    integralClosure (SquareConstantField p s) (SquareKummerField p s c b R) = ⊥ := by
  apply bot_unique
  intro x hx
  exact Algebra.mem_bot.mpr (squareKummer_constantField p s c b R x
    (show IsIntegral (SquareConstantField p s) x from hx).isAlgebraic)
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
