import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerNormalization
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionInversion

/-!
# Coordinate inversion of Kummer function fields

Transporting the irreducible radical polynomial along `y ↦ t⁻¹` gives
an isomorphic constant-field extension. The new rational base uses `t`,
so normalization over its polynomial ring supplies the chart at infinity.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
open scoped nonZeroDivisors

/-- Inversion of the rational coordinate, fixing the constant field. -/
def kummerCoordinateInversion (K : Type*) [Field K] :
    FractionRing K[X] ≃ₐ[K] FractionRing K[X] :=
  ((IsLocalization.algEquiv K[X]⁰ (FractionRing K[X]) (RatFunc K)).restrictScalars K).trans
    ((GaloisForLFunctions.HTGeometry.ABHN.rationalFunctionInversionAlgEquiv K).trans
      ((IsLocalization.algEquiv K[X]⁰ (FractionRing K[X]) (RatFunc K)).restrictScalars K).symm)

/-- The coordinate is sent to its reciprocal. -/
theorem kummerCoordinateInversion_X (K : Type*) [Field K] :
    kummerCoordinateInversion K (algebraMap K[X] (FractionRing K[X]) X) =
      (algebraMap K[X] (FractionRing K[X]) X)⁻¹ := by
  let e := IsLocalization.algEquiv K[X]⁰ (FractionRing K[X]) (RatFunc K)
  change e.symm (GaloisForLFunctions.HTGeometry.ABHN.rationalFunctionInversionAlgEquiv K
    (e (algebraMap K[X] (FractionRing K[X]) X))) = _
  rw [e.commutes, RatFunc.algebraMap_X,
    GaloisForLFunctions.HTGeometry.ABHN.rationalFunctionInversionAlgEquiv_X, map_inv₀,
    ← RatFunc.algebraMap_X, e.symm.commutes]

variable {K : Type*} [Field K]
/-- The radical polynomial with its rational-function coefficients inverted. -/
def kummerInfinityPolynomial (c : Kˣ) (b R n : ℕ) : (FractionRing K[X])[X] :=
  (kummerBranchFieldPolynomial c b R n).map (kummerCoordinateInversion K)


/-- Coordinate inversion changes only the branch function. -/
theorem kummerInfinityPolynomial_eq (c : Kˣ) (b R n : ℕ) :
    kummerInfinityPolynomial c b R n = X ^ (n + 1) - C
      (kummerCoordinateInversion K
        (algebraMap K[X] (FractionRing K[X]) (kummerBranch c b R))) := by
  simp only [kummerInfinityPolynomial, kummerBranchFieldPolynomial,
    Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  rfl

/-- A coefficient-field automorphism preserves irreducibility. -/
instance kummerInfinityPolynomial_irreducible (c : Kˣ) (b R n : ℕ) :
    Fact (Irreducible (kummerInfinityPolynomial c b R n)) := by
  constructor
  apply (MulEquiv.irreducible_iff (Polynomial.mapEquiv
    (kummerCoordinateInversion K).toRingEquiv)).mpr
  exact (kummerBranchFieldPolynomial_irreducible c b R n).out

/-- The inverted defining polynomial remains monic. -/
theorem kummerInfinityPolynomial_monic (c : Kˣ) (b R n : ℕ) :
    (kummerInfinityPolynomial c b R n).Monic := by
  rw [kummerInfinityPolynomial_eq]
  exact monic_X_pow_sub_C _ (Nat.succ_ne_zero n)

/-- The radical field expressed in the reciprocal base coordinate. -/
abbrev KummerInfinityField (c : Kˣ) (b R n : ℕ) :=
  AdjoinRoot (kummerInfinityPolynomial c b R n)

/-- The monic equation makes the inverted field finite-dimensional. -/
instance kummerInfinityField_finiteDimensional (c : Kˣ) (b R n : ℕ) :
    FiniteDimensional (FractionRing K[X]) (KummerInfinityField c b R n) :=
  (kummerInfinityPolynomial_monic c b R n).finite_adjoinRoot

/-- The polynomial base embeds through its fraction field. -/
instance kummerInfinityField_torsionFree (c : Kˣ) (b R n : ℕ) :
    Module.IsTorsionFree K[X] (KummerInfinityField c b R n) :=
  Module.IsTorsionFree.trans (FractionRing K[X])

/-- Coordinate inversion preserves the covering degree. -/
theorem kummerInfinityField_finrank (c : Kˣ) (b R n : ℕ) :
    Module.finrank (FractionRing K[X]) (KummerInfinityField c b R n) = n + 1 := by
  have hi := (kummerInfinityPolynomial_irreducible c b R n).out
  calc
    _ = (AdjoinRoot.powerBasis hi.ne_zero).dim := (AdjoinRoot.powerBasis hi.ne_zero).finrank
    _ = n + 1 := by
      rw [AdjoinRoot.powerBasis_dim, kummerInfinityPolynomial_eq, natDegree_X_pow_sub_C]

/-- The original and inverted radical fields are isomorphic over the constants. -/
def kummerInfinityFieldEquiv (c : Kˣ) (b R n : ℕ) :
    KummerBranchField c b R n ≃ₐ[K] KummerInfinityField c b R n :=
  AdjoinRoot.mapAlgEquiv (kummerCoordinateInversion K)
    (kummerBranchFieldPolynomial c b R n) (kummerInfinityPolynomial c b R n)
    (Associated.refl _)

/-- The field isomorphism preserves the named radical. -/
theorem kummerInfinityFieldEquiv_root (c : Kˣ) (b R n : ℕ) :
    kummerInfinityFieldEquiv c b R n
      (AdjoinRoot.root (kummerBranchFieldPolynomial c b R n)) =
        AdjoinRoot.root (kummerInfinityPolynomial c b R n) := by
  simp only [kummerInfinityFieldEquiv, AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_root]

/-- On the rational subfield, the isomorphism acts by coordinate inversion. -/
theorem kummerInfinityFieldEquiv_algebraMap (c : Kˣ) (b R n : ℕ)
    (x : FractionRing K[X]) :
    kummerInfinityFieldEquiv c b R n (algebraMap (FractionRing K[X]) (KummerBranchField c b R n) x) =
      algebraMap (FractionRing K[X]) (KummerInfinityField c b R n) (kummerCoordinateInversion K x) := by
  simp only [kummerInfinityFieldEquiv, AdjoinRoot.coe_mapAlgEquiv,
    AdjoinRoot.algebraMap_eq, AdjoinRoot.map_of]
  rfl

/-- The old base coordinate becomes the reciprocal of the new coordinate. -/
theorem kummerInfinityFieldEquiv_coordinate (c : Kˣ) (b R n : ℕ) :
    kummerInfinityFieldEquiv c b R n (algebraMap K[X] (KummerBranchField c b R n) X) =
      (algebraMap K[X] (KummerInfinityField c b R n) X)⁻¹ := by
  rw [IsScalarTower.algebraMap_apply K[X] (FractionRing K[X]) (KummerBranchField c b R n),
    kummerInfinityFieldEquiv_algebraMap, kummerCoordinateInversion_X, map_inv₀,
    ← IsScalarTower.algebraMap_apply K[X] (FractionRing K[X]) (KummerInfinityField c b R n)]

/-- The radical remains nonzero in the inverted field. -/
theorem kummerInfinityField_root_ne_zero (c : Kˣ) (b R n : ℕ) :
    AdjoinRoot.root (kummerInfinityPolynomial c b R n) ≠ 0 := by
  rw [← kummerInfinityFieldEquiv_root c b R n]
  exact (map_ne_zero_iff _ (kummerInfinityFieldEquiv c b R n).injective).mpr
    (kummerBranchField_root_ne_zero c b R n)

/-- The radical retains its defining equation in the inverted coordinate. -/
theorem kummerInfinityField_root_pow (c : Kˣ) (b R n : ℕ) :
    AdjoinRoot.root (kummerInfinityPolynomial c b R n) ^ (n + 1) =
      algebraMap (FractionRing K[X]) (KummerInfinityField c b R n)
        (kummerCoordinateInversion K
          (algebraMap K[X] (FractionRing K[X]) (kummerBranch c b R))) := by
  have h := congrArg (kummerInfinityFieldEquiv c b R n)
    (kummerBranchField_root_pow c b R n)
  rwa [map_pow, kummerInfinityFieldEquiv_root, kummerInfinityFieldEquiv_algebraMap] at h

/-- Inverting the base coordinate preserves the Galois extension. -/
theorem squareKummerInfinity_isGalois (p : ℕ) [Fact p.Prime] (s : ℕ)
    (c : (SquareConstantField p s)ˣ) (b R : ℕ) :
    IsGalois (FractionRing (SquareConstantField p s)[X])
      (KummerInfinityField c b R (p ^ (s + 1))) := by
  letI := squareKummer_isGalois p s c b R
  apply IsGalois.of_equiv_equiv
    (f := (kummerCoordinateInversion (SquareConstantField p s)).toRingEquiv)
    (g := (kummerInfinityFieldEquiv c b R (p ^ (s + 1))).toRingEquiv)
  ext x
  exact (kummerInfinityFieldEquiv_algebraMap c b R (p ^ (s + 1)) x).symm

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
