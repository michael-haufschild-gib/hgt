import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerNormalization

/-!
# Square-degree Kummer fields over extended constants

The roots of unity in the original square field remain primitive in every
constant extension. The literal radical field therefore retains its degree
and cyclic Galois action, and its polynomial normalization is finite free.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
    (E : Type*) [Field E] [Algebra (SquareConstantField p s) E]
local notation "K" => SquareConstantField p s
local notation "Q" => p ^ (s + 1)
local notation "F" => FractionRing E[X]

/-- Primitive roots of the covering degree survive extension of constants. -/
theorem squareKummerExtension_primitiveRoots : (primitiveRoots (Q + 1) E).Nonempty := by
  obtain ⟨ζ, hζ⟩ := squareConstantField_primitiveRoots p s
  exact ⟨algebraMap K E ζ, (mem_primitiveRoots (Nat.succ_pos _)).mpr
    (((mem_primitiveRoots (Nat.succ_pos _)).mp hζ).map_of_injective
      (algebraMap K E).injective)⟩

private theorem rationalPrimitiveRoots : (primitiveRoots (Q + 1) F).Nonempty := by
  obtain ⟨ζ, hζ⟩ := squareKummerExtension_primitiveRoots p s E
  exact ⟨algebraMap E F ζ, (mem_primitiveRoots (Nat.succ_pos _)).mpr
    (((mem_primitiveRoots (Nat.succ_pos _)).mp hζ).map_of_injective
      (algebraMap E F).injective)⟩

/-- The same radical equation over any extension of the square constants. -/
abbrev SquareKummerExtensionField (c : Eˣ) (b R : ℕ) := KummerBranchField c b R Q

variable (c : Eˣ) (b R : ℕ)
local notation "L" => SquareKummerExtensionField p s E c b R

/-- The monic radical equation gives a finite extension of the rational base. -/
instance squareKummerExtension_finiteDimensional : FiniteDimensional F L :=
  (monic_X_pow_sub_C _ (Nat.succ_ne_zero Q)).finite_adjoinRoot

omit [Fact p.Prime] [Algebra (SquareConstantField p s) E] in
/-- The simple branch at zero keeps the exact degree unchanged. -/
theorem squareKummerExtension_finrank : Module.finrank F L = Q + 1 :=
  kummerBranchField_finrank c b R Q

/-- One radical generates the full splitting field over the enlarged rational base. -/
theorem squareKummerExtension_isSplittingField :
    IsSplittingField F L (X ^ (Q + 1) - C (algebraMap E[X] F (kummerBranch c b R))) :=
  isSplittingField_AdjoinRoot_X_pow_sub_C (rationalPrimitiveRoots p s E)
    (kummerBranch_fraction_irreducible c b R Q)

/-- The explicit fixed-degree radical extension remains Galois. -/
theorem squareKummerExtension_isGalois : IsGalois F L := by
  letI := squareKummerExtension_isSplittingField p s E c b R
  exact isGalois_of_isSplittingField_X_pow_sub_C (rationalPrimitiveRoots p s E)
    (kummerBranch_fraction_irreducible c b R Q) _

/-- Every relative automorphism multiplies the radical by a constant root of unity. -/
def squareKummerExtensionAutEquiv : rootsOfUnity (Q + 1) E ≃* (L ≃ₐ[F] L) :=
  (rootsOfUnityEquivOfPrimitiveRoots (algebraMap E F).injective
    (squareKummerExtension_primitiveRoots p s E)).trans
    (autAdjoinRootXPowSubCEquiv (rationalPrimitiveRoots p s E)
      (kummerBranch_fraction_irreducible c b R Q))

/-- The roots-of-unity equivalence has the prescribed action on the actual radical. -/
theorem squareKummerExtensionAutEquiv_root (ζ : rootsOfUnity (Q + 1) E) :
    squareKummerExtensionAutEquiv p s E c b R ζ
      (AdjoinRoot.root (kummerBranchFieldPolynomial c b R Q)) =
        algebraMap E L (ζ : Eˣ) * AdjoinRoot.root (kummerBranchFieldPolynomial c b R Q) := by
  change autAdjoinRootXPowSubC (Q + 1)
    (algebraMap E[X] F (kummerBranch c b R)) _ _ = _
  erw [autAdjoinRootXPowSubC_root, Algebra.smul_def]
  change algebraMap F L
      ((rootsOfUnityEquivOfPrimitiveRoots (algebraMap E F).injective
        (squareKummerExtension_primitiveRoots p s E) ζ : Fˣ) : F) *
        AdjoinRoot.root (kummerBranchFieldPolynomial c b R Q) = _
  rw [val_rootsOfUnityEquivOfPrimitiveRoots_apply_coe,
    ← IsScalarTower.algebraMap_apply E F L]

/-- The actual integral closure of the enlarged polynomial ring. -/
abbrev SquareKummerExtensionNormalization := integralClosure E[X] L
local notation "B" => SquareKummerExtensionNormalization p s E c b R

/-- Separability makes the normalization Dedekind. -/
instance squareKummerExtensionNormalization_dedekind : IsDedekindDomain B := by
  letI := squareKummerExtension_isGalois p s E c b R
  infer_instance

/-- The normalization is a finite module over the polynomial ring. -/
instance squareKummerExtensionNormalization_finite : Module.Finite E[X] B := by
  letI := squareKummerExtension_isGalois p s E c b R
  exact IsIntegralClosure.finite E[X] F L _

/-- The finite normalization is free over the polynomial PID. -/
instance squareKummerExtensionNormalization_free : Module.Free E[X] B := by
  letI := squareKummerExtension_isGalois p s E c b R
  exact IsIntegralClosure.module_free E[X] F L _

/-- The fraction field of the normalization is the constructed radical field. -/
instance squareKummerExtensionNormalization_fractionRing : IsFractionRing B L :=
  IsIntegralClosure.isFractionRing_of_finite_extension E[X] F L _

/-- The module rank equals the unchanged covering degree. -/
theorem squareKummerExtensionNormalization_finrank : Module.finrank E[X] B = Q + 1 := by
  letI := squareKummerExtension_isGalois p s E c b R
  rw [IsIntegralClosure.rank E[X] F L]
  exact squareKummerExtension_finrank p s E c b R

/-- The canonical radical belongs to the actual normalization. -/
def squareKummerExtensionIntegralRoot : B :=
  ⟨AdjoinRoot.root (kummerBranchFieldPolynomial c b R Q),
    kummerBranchField_root_integral c b R Q⟩

omit [Fact p.Prime] [Algebra (SquareConstantField p s) E] in
/-- The integral radical satisfies its defining power equation. -/
theorem squareKummerExtensionIntegralRoot_pow :
    squareKummerExtensionIntegralRoot p s E c b R ^ (Q + 1) =
      algebraMap E[X] B (kummerBranch c b R) := by
  apply Subtype.ext
  exact (kummerBranchField_root_pow c b R Q).trans
    (IsScalarTower.algebraMap_apply _ _ _ _).symm

omit [Fact p.Prime] [Algebra (SquareConstantField p s) E] in
/-- The integral radical is nonzero. -/
theorem squareKummerExtensionIntegralRoot_ne_zero :
    squareKummerExtensionIntegralRoot p s E c b R ≠ 0 := by
  intro h
  exact kummerBranchField_root_ne_zero c b R Q (congrArg Subtype.val h)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
