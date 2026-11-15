import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerNormalizationCoordinates

/-!
# An explicit polynomial basis of the Kummer normalization

The reduced radical monomials form an integral basis over the polynomial
ring. Polynomial coefficients give an explicit linear equivalence with
the normalization; the rational monomial basis proves uniqueness, and
the integral-coordinate criterion proves that every element occurs.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (s d : ℕ) (c : (SquareConstantField p s)ˣ) (R : ℕ)

private def integralSynthesis :
    (Fin (p ^ (s + 1) + 1) → (SquareConstantField p s)[X]) →ₗ[(SquareConstantField p s)[X]]
      SquareKummerNormalization p s c (p ^ (d + 1) - 2) R where
  toFun a := ∑ i, a i • kummerNormalizedMonomial c (p ^ (d + 1) - 2) R (p ^ (s + 1)) i.val
  map_add' a b := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a b := by
    simp only [Pi.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum, RingHom.id_apply]

private theorem integralSynthesis_val
    (a : Fin (p ^ (s + 1) + 1) → (SquareConstantField p s)[X]) :
    (integralSynthesis p s d c R a : SquareKummerField p s c (p ^ (d + 1) - 2) R) =
      (kummerIntegralMonomialBasis c (p ^ (d + 1) - 2) R (p ^ (s + 1))).equivFun.symm
        (fun i => algebraMap (SquareConstantField p s)[X]
          (FractionRing (SquareConstantField p s)[X]) (a i)) := by
  let K := SquareConstantField p s
  let A := K[X]
  let F := FractionRing A
  let L := SquareKummerField p s c (p ^ (d + 1) - 2) R
  change (integralClosure A L).val
    (∑ i : Fin (p ^ (s + 1) + 1),
      a i • kummerNormalizedMonomial c (p ^ (d + 1) - 2) R (p ^ (s + 1)) i.val) = _
  rw [map_sum, Module.Basis.equivFun_symm_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, kummerIntegralMonomialBasis_apply]
  simp only [Algebra.smul_def]
  change algebraMap A L (a i) * kummerIntegralMonomial c (p ^ (d + 1) - 2) R (p ^ (s + 1)) i.val =
    algebraMap F L (algebraMap A F (a i)) *
      kummerIntegralMonomial c (p ^ (d + 1) - 2) R (p ^ (s + 1)) i.val
  rw [← IsScalarTower.algebraMap_apply A F L]

private theorem integralSynthesis_bijective :
    Function.Bijective (integralSynthesis p s d c R) := by
  let K := SquareConstantField p s
  let A := K[X]
  let F := FractionRing A
  let L := SquareKummerField p s c (p ^ (d + 1) - 2) R
  let B := kummerIntegralMonomialBasis c (p ^ (d + 1) - 2) R (p ^ (s + 1))
  constructor
  · intro a b h
    have hv := congrArg (fun x : integralClosure A L => (x : L)) h
    rw [integralSynthesis_val, integralSynthesis_val] at hv
    have he := B.equivFun.symm.injective hv
    funext i
    exact IsFractionRing.injective A F (congrFun he i)
  · intro x
    have hpoly (i : Fin (p ^ (s + 1) + 1)) : ∃ a : A, algebraMap A F a = B.repr x.val i :=
      squareKummer_integral_basis_coordinate p s d c R x.val x.property i
    choose a ha using hpoly
    refine ⟨a, Subtype.ext ?_⟩
    rw [integralSynthesis_val]
    change B.equivFun.symm (fun i => algebraMap A F (a i)) = x.val
    have he : (fun i => algebraMap A F (a i)) = B.equivFun x.val := by
      funext i
      simpa only [Module.Basis.equivFun_apply] using ha i
    rw [he, B.equivFun.symm_apply_apply]

/-- Polynomial coefficient vectors parametrize the actual normalization uniquely and linearly. -/
def squareKummerNormalizationCoordinateEquiv :
    (Fin (p ^ (s + 1) + 1) → (SquareConstantField p s)[X]) ≃ₗ[(SquareConstantField p s)[X]]
      SquareKummerNormalization p s c (p ^ (d + 1) - 2) R :=
  LinearEquiv.ofBijective (integralSynthesis p s d c R) (integralSynthesis_bijective p s d c R)

/-- The coordinate equivalence is the explicit sum of reduced integral radical monomials. -/
theorem squareKummerNormalizationCoordinateEquiv_apply
    (a : Fin (p ^ (s + 1) + 1) → (SquareConstantField p s)[X]) :
    squareKummerNormalizationCoordinateEquiv p s d c R a =
      ∑ i, a i • kummerNormalizedMonomial c (p ^ (d + 1) - 2) R (p ^ (s + 1)) i.val := rfl

/-- The reduced radical monomials give an explicit basis over the polynomial coordinate ring. -/
def squareKummerNormalizationBasis :
    Module.Basis (Fin (p ^ (s + 1) + 1)) (SquareConstantField p s)[X]
      (SquareKummerNormalization p s c (p ^ (d + 1) - 2) R) :=
  Module.Basis.ofEquivFun (squareKummerNormalizationCoordinateEquiv p s d c R).symm

/-- The integral basis vectors are the literal reduced radical monomials. -/
theorem squareKummerNormalizationBasis_apply (i : Fin (p ^ (s + 1) + 1)) :
    squareKummerNormalizationBasis p s d c R i =
      kummerNormalizedMonomial c (p ^ (d + 1) - 2) R (p ^ (s + 1)) i.val := by
  classical
  rw [squareKummerNormalizationBasis, Module.Basis.coe_ofEquivFun]
  change squareKummerNormalizationCoordinateEquiv p s d c R (Pi.single i 1) = _
  rw [squareKummerNormalizationCoordinateEquiv_apply]
  simp only [Pi.single_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
