import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerPoleSpaces
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerPoleExpansions
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerPoleCutoffs
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerIntegralBasis

/-!
# Polynomial coordinates for one-point pole spaces

The integral radical basis identifies functions regular away from infinity
with polynomial coefficient vectors. Distinct infinity orders impose one
independent degree cutoff per character. The resulting coordinates give
an explicit linear equivalence with the actual bounded-pole space.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r m : ℕ)

/-- Polynomial coefficient vectors satisfying each character's pole bound. -/
abbrev SquareKummerPoleCoefficientSpace :=
  (i : Fin (p ^ (s + 1) + 1)) →
    degreeLT (SquareConstantField p s) (kummerPoleCutoff p s d r m i.val)

/-- Normalization coordinates have the expected value in the function field. -/
theorem squareKummerNormalizationCoordinateEquiv_val
    (a : Fin (p ^ (s + 1) + 1) → (SquareConstantField p s)[X]) :
    (squareKummerNormalizationCoordinateEquiv p s d c (kummerExponent (p ^ (d + 1)) r) a :
      SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) =
      squareKummerPolynomialExpansion p s c d r a := by
  let K := SquareConstantField p s
  let A := K[X]
  let L := SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)
  rw [squareKummerNormalizationCoordinateEquiv_apply]
  change (integralClosure A L).val
    (∑ i, a i • kummerNormalizedMonomial c (p ^ (d + 1) - 2)
      (kummerExponent (p ^ (d + 1)) r) (p ^ (s + 1)) i.val) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, Algebra.smul_def]
  rfl

private def poleCoefficientMap :
    SquareKummerPoleCoefficientSpace p s d r m →ₗ[SquareConstantField p s]
      SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r) where
  toFun a := ∑ i, (IsScalarTower.toAlgHom (SquareConstantField p s) (SquareConstantField p s)[X]
    (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)))
      (a i : (SquareConstantField p s)[X]) *
      kummerIntegralMonomial c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)
        (p ^ (s + 1)) i.val
  map_add' a b := by
    simp only [Pi.add_apply, Submodule.coe_add, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' t a := by
    simp only [Pi.smul_apply, Submodule.coe_smul, map_smul, smul_mul_assoc,
      Finset.smul_sum, RingHom.id_apply]

/-- Bounded polynomial coefficients synthesize functions with only the prescribed infinity pole. -/
def squareKummerPoleCoefficientMap :
    SquareKummerPoleCoefficientSpace p s d r m →ₗ[SquareConstantField p s]
      squareKummerPoleSpace p s c d r m :=
  (poleCoefficientMap p s c d r m).codRestrict _ (fun a => by
    rw [mem_squareKummerPoleSpace_iff]
    constructor
    · have hx := (squareKummerNormalizationCoordinateEquiv p s d c
        (kummerExponent (p ^ (d + 1)) r) (fun i => (a i : (SquareConstantField p s)[X]))).property
      rw [squareKummerNormalizationCoordinateEquiv_val] at hx
      exact hx
    · exact (squareKummerPolynomialExpansion_pole_bound_iff p s c d r _ m).mpr
        (fun i => (mem_degreeLT_kummerPoleCutoff_iff p s d r m i _).mp (a i).property))

/-- The pole-space coordinate map is the explicit reduced radical expansion. -/
theorem squareKummerPoleCoefficientMap_val (a : SquareKummerPoleCoefficientSpace p s d r m) :
    (squareKummerPoleCoefficientMap p s c d r m a).val =
      squareKummerPolynomialExpansion p s c d r (fun i => (a i : (SquareConstantField p s)[X])) := rfl

/-- Bounded polynomial coordinates in a pole space are unique. -/
theorem squareKummerPoleCoefficientMap_injective :
    Function.Injective (squareKummerPoleCoefficientMap p s c d r m) := by
  intro a b h
  have hv := congrArg Subtype.val h
  rw [squareKummerPoleCoefficientMap_val, squareKummerPoleCoefficientMap_val,
    ← squareKummerNormalizationCoordinateEquiv_val,
    ← squareKummerNormalizationCoordinateEquiv_val] at hv
  have he := (squareKummerNormalizationCoordinateEquiv p s d c
    (kummerExponent (p ^ (d + 1)) r)).injective (Subtype.ext hv)
  funext i
  exact Subtype.ext (congrFun he i)

/-- Every function in the actual one-point pole space has the prescribed bounded coordinates. -/
theorem squareKummerPoleCoefficientMap_surjective :
    Function.Surjective (squareKummerPoleCoefficientMap p s c d r m) := by
  intro x
  let K := SquareConstantField p s
  let L := SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)
  let E := squareKummerNormalizationCoordinateEquiv p s d c (kummerExponent (p ^ (d + 1)) r)
  have hx := (mem_squareKummerPoleSpace_iff p s c d r m x.val).mp x.property
  let y : SquareKummerNormalization p s c (p ^ (d + 1) - 2)
      (kummerExponent (p ^ (d + 1)) r) := ⟨x.val, hx.1⟩
  let a := E.symm y
  have ha : squareKummerPolynomialExpansion p s c d r a = x.val := by
    rw [← squareKummerNormalizationCoordinateEquiv_val]
    exact congrArg (fun z : SquareKummerNormalization p s c (p ^ (d + 1) - 2)
      (kummerExponent (p ^ (d + 1)) r) => (z : L)) (E.apply_symm_apply y)
  have hb := (squareKummerPolynomialExpansion_pole_bound_iff p s c d r a m).mp
    (show squareKummerInfinityValuation p s c d r
      (squareKummerPolynomialExpansion p s c d r a) ≤ WithZero.exp (m : ℤ) by rw [ha]; exact hx.2)
  let a' : SquareKummerPoleCoefficientSpace p s d r m := fun i =>
    ⟨a i, (mem_degreeLT_kummerPoleCutoff_iff p s d r m i _).mpr (hb i)⟩
  refine ⟨a', Subtype.ext ?_⟩
  exact ha

/-- One-point pole spaces are exactly products of their bounded polynomial character spaces. -/
def squareKummerPoleSpaceCoordinateEquiv :
    SquareKummerPoleCoefficientSpace p s d r m ≃ₗ[SquareConstantField p s]
      squareKummerPoleSpace p s c d r m :=
  LinearEquiv.ofBijective (squareKummerPoleCoefficientMap p s c d r m)
    ⟨squareKummerPoleCoefficientMap_injective p s c d r m,
      squareKummerPoleCoefficientMap_surjective p s c d r m⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
