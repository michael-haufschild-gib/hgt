import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerCharacterRegularity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerFiniteRegularCoefficients


/-!
# Polynomial coordinates for global regular differentials

The inverse radical characters identify the actual global regular
differential space with a product of bounded-degree polynomial spaces.
Finite regularity removes denominators; infinity imposes each degree bound.
The inverse radical basis makes the resulting coordinate map bijective.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)

/-- Polynomial coefficients in each inverse character, bounded by its infinity cutoff. -/
abbrev SquareKummerRegularCoefficientSpace :=
  (i : Fin (p ^ (s + 1) + 1)) →
    degreeLT (SquareConstantField p s) (kummerDifferentialCutoff p s d r i.val)

private def coefficientFormMap :
    SquareKummerRegularCoefficientSpace p s d r →ₗ[SquareConstantField p s]
      KaehlerDifferential (SquareConstantField p s)
        (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) where
  toFun a := ∑ i : Fin (p ^ (s + 1) + 1),
    ((IsScalarTower.toAlgHom (SquareConstantField p s) (SquareConstantField p s)[X]
      (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)))
        (a i : (SquareConstantField p s)[X]) /
      kummerIntegralMonomial c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)
        (p ^ (s + 1)) i.val) •
      KaehlerDifferential.D (SquareConstantField p s)
        (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r))
        (algebraMap (SquareConstantField p s)[X]
          (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) X)
  map_add' a b := by
    simp only [Pi.add_apply, Submodule.coe_add, map_add, add_div, add_smul, Finset.sum_add_distrib]
  map_smul' t a := by
    simp only [Pi.smul_apply, Submodule.coe_smul, map_smul, smul_div_assoc,
      smul_assoc, Finset.smul_sum, RingHom.id_apply]

/-- Bounded polynomial character coefficients define actual global regular differentials. -/
def squareKummerRegularCoefficientMap :
    SquareKummerRegularCoefficientSpace p s d r →ₗ[SquareConstantField p s]
      globalRegularDifferentials (SquareConstantField p s)
        (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) :=
  (coefficientFormMap p s c d r).codRestrict _ (fun a => by
    apply Submodule.sum_mem
    intro i _
    exact (squareKummer_characterForm_regular_iff_degreeLT p s c d r
      (a i : (SquareConstantField p s)[X]) i).mpr (a i).property)

private theorem coefficientMap_coordinate (a : SquareKummerRegularCoefficientSpace p s d r) :
    squareKummerDifferentialEquiv p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)
      (squareKummerRegularCoefficientMap p s c d r a).val =
      (squareKummerInverseMonomialBasis p s c (p ^ (d + 1) - 2)
        (kummerExponent (p ^ (d + 1)) r)).equivFun.symm
        (fun i => algebraMap (SquareConstantField p s)[X]
          (FractionRing (SquareConstantField p s)[X]) (a i : (SquareConstantField p s)[X])) := by
  let K := SquareConstantField p s
  let F := FractionRing K[X]
  let b := p ^ (d + 1) - 2
  let R := kummerExponent (p ^ (d + 1)) r
  let L := SquareKummerField p s c b R
  let E := squareKummerDifferentialEquiv p s c b R
  let B := squareKummerInverseMonomialBasis p s c b R
  change E (∑ i : Fin (p ^ (s + 1) + 1),
    (algebraMap K[X] L (a i : K[X]) / kummerIntegralMonomial c b R (p ^ (s + 1)) i.val) •
      KaehlerDifferential.D K L (algebraMap K[X] L X)) = _
  rw [map_sum, Module.Basis.equivFun_symm_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, squareKummerDifferentialEquiv_D_polynomial, derivative_X, map_one,
    smul_eq_mul, mul_one, squareKummerInverseMonomialBasis_apply, Algebra.smul_def,
    ← IsScalarTower.algebraMap_apply K[X] F L, div_eq_mul_inv]

/-- The inverse radical basis makes polynomial differential coordinates unique. -/
theorem squareKummerRegularCoefficientMap_injective :
    Function.Injective (squareKummerRegularCoefficientMap p s c d r) := by
  intro a b h
  let K := SquareConstantField p s
  let F := FractionRing K[X]
  let B := squareKummerInverseMonomialBasis p s c (p ^ (d + 1) - 2)
    (kummerExponent (p ^ (d + 1)) r)
  let L := SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)
  have he := congrArg (fun ω : globalRegularDifferentials K L =>
    squareKummerDifferentialEquiv p s c (p ^ (d + 1) - 2)
    (kummerExponent (p ^ (d + 1)) r) ω.val) h
  rw [coefficientMap_coordinate, coefficientMap_coordinate] at he
  have hc := B.equivFun.symm.injective he
  funext i
  apply Subtype.ext
  exact IsFractionRing.injective K[X] F (congrFun hc i)

/-- Every actual global regular differential has bounded polynomial inverse-character coordinates. -/
theorem squareKummerRegularCoefficientMap_surjective :
    Function.Surjective (squareKummerRegularCoefficientMap p s c d r) := by
  intro ω
  let K := SquareConstantField p s
  let F := FractionRing K[X]
  let b := p ^ (d + 1) - 2
  let R := kummerExponent (p ^ (d + 1)) r
  let L := SquareKummerField p s c b R
  let E := squareKummerDifferentialEquiv p s c b R
  let B := squareKummerInverseMonomialBasis p s c b R
  let dy := KaehlerDifferential.D K L (algebraMap K[X] L X)
  let f := E ω.val
  have hform : f • dy = ω.val := by
    apply E.injective
    rw [map_smul, squareKummerDifferentialEquiv_D_polynomial, derivative_X,
      map_one, smul_eq_mul, mul_one]
  have hf : f • dy ∈ globalRegularDifferentials K L := by rw [hform]; exact ω.property
  have hpoly (i : Fin (p ^ (s + 1) + 1)) : ∃ a : K[X], algebraMap K[X] F a = B.repr f i :=
    squareKummer_regular_basis_coordinate_polynomial p s d c R f hf i
  choose a ha using hpoly
  have hdegree (i : Fin (p ^ (s + 1) + 1)) :
      a i ∈ degreeLT K (kummerDifferentialCutoff p s d r i.val) := by
    have hc := squareKummer_regular_character_component p s c b R f hf i
    rw [← ha i, squareKummerInverseMonomialBasis_apply, Algebra.smul_def,
      ← IsScalarTower.algebraMap_apply K[X] F L, ← div_eq_mul_inv] at hc
    exact (squareKummer_characterForm_regular_iff_degreeLT p s c d r (a i) i).mp hc
  let a' : SquareKummerRegularCoefficientSpace p s d r := fun i => ⟨a i, hdegree i⟩
  refine ⟨a', ?_⟩
  apply Subtype.ext
  apply E.injective
  rw [coefficientMap_coordinate]
  change B.equivFun.symm (fun i => algebraMap K[X] F (a i)) = f
  calc
    B.equivFun.symm (fun i => algebraMap K[X] F (a i)) = B.equivFun.symm (B.equivFun f) := by
      congr 1
      funext i
      simpa only [Module.Basis.equivFun_apply] using ha i
    _ = f := B.equivFun.symm_apply_apply f

/-- Global regular differentials are exactly the product of the bounded polynomial character spaces. -/
def squareKummerRegularDifferentialEquiv :
    SquareKummerRegularCoefficientSpace p s d r ≃ₗ[SquareConstantField p s]
      globalRegularDifferentials (SquareConstantField p s)
        (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) :=
  LinearEquiv.ofBijective (squareKummerRegularCoefficientMap p s c d r)
    ⟨squareKummerRegularCoefficientMap_injective p s c d r,
      squareKummerRegularCoefficientMap_surjective p s c d r⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
