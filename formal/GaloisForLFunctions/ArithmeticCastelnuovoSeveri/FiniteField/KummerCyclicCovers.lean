import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerBranchIrreducibility
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Finite.Extension

/-!
# Cyclic Kummer covers over square finite fields

Over the field with `Q²` elements, every simple-branch equation
`z^(Q+1)=c y(1-y^(b+1))^R` defines a cyclic Galois extension of the rational
function field of degree `Q+1`. Its automorphisms are exactly multiplication
of `z` by the `(Q+1)`-st roots of unity in the constant field.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open Polynomial

private theorem finiteField_primitiveRoots_of_dvd (K : Type*) [Field K] [Finite K]
    {n : ℕ} (hn : 0 < n) (hd : n ∣ Nat.card K - 1) : (primitiveRoots n K).Nonempty := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hprim : IsPrimitiveRoot (g : K) (Nat.card Kˣ) := by
    rw [← hg]
    exact IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.orderOf g)
  obtain ⟨d, hd⟩ := hd
  have hfactor : Nat.card Kˣ = d * n := by rw [Nat.card_units, hd, Nat.mul_comm]
  exact ⟨(g : K) ^ d, (mem_primitiveRoots hn).mpr (hprim.pow Nat.card_pos hfactor)⟩

variable (p : ℕ) [Fact p.Prime]

/-- A concrete finite field of square order, with `Q=p^(s+1)`. -/
abbrev SquareConstantField (s : ℕ) := FiniteField.Extension (ZMod p) p (2 * (s + 1))

/-- The constant field has exactly `p^(2(s+1))` elements. -/
theorem squareConstantField_card (s : ℕ) :
    Nat.card (SquareConstantField p s) = p ^ (2 * (s + 1)) := by
  rw [SquareConstantField, FiniteField.natCard_extension, Nat.card_zmod]

/-- The degree `Q+1` divides the order of the multiplicative group. -/
theorem squareConstantField_degree_dvd (s : ℕ) :
    p ^ (s + 1) + 1 ∣ Nat.card (SquareConstantField p s) - 1 := by
  rw [squareConstantField_card]
  refine ⟨p ^ (s + 1) - 1, ?_⟩
  rw [Nat.mul_comm 2 (s + 1), pow_mul, pow_two]
  have hpos := Nat.one_le_pow (s + 1) p (Fact.out : p.Prime).pos
  have hsub := Nat.sub_add_cancel hpos
  have he : (p ^ (s + 1) + 1) * (p ^ (s + 1) - 1) + 1 =
      p ^ (s + 1) * p ^ (s + 1) := by nlinarith only [hsub]
  omega

/-- All primitive roots needed for the cyclic covering lie in the stated finite field. -/
theorem squareConstantField_primitiveRoots (s : ℕ) :
    (primitiveRoots (p ^ (s + 1) + 1) (SquareConstantField p s)).Nonempty :=
  finiteField_primitiveRoots_of_dvd _ (Nat.succ_pos _) (squareConstantField_degree_dvd p s)

private theorem squareRationalField_primitiveRoots (s : ℕ) :
    (primitiveRoots (p ^ (s + 1) + 1) (FractionRing (SquareConstantField p s)[X])).Nonempty := by
  obtain ⟨ζ, hζ⟩ := squareConstantField_primitiveRoots p s
  let f := algebraMap (SquareConstantField p s) (FractionRing (SquareConstantField p s)[X])
  exact ⟨f ζ, (mem_primitiveRoots (Nat.succ_pos _)).mpr
    (((mem_primitiveRoots (Nat.succ_pos _)).mp hζ).map_of_injective f.injective)⟩

/-- The literal radical field for a simple-branch equation over the square finite field. -/
abbrev SquareKummerField (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ) :=
  KummerBranchField c b R (p ^ (s + 1))

/-- The constructed radical field is already the splitting field. -/
theorem squareKummer_isSplittingField (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ) :
    IsSplittingField (FractionRing (SquareConstantField p s)[X]) (SquareKummerField p s c b R)
      (X ^ (p ^ (s + 1) + 1) - C
        (algebraMap (SquareConstantField p s)[X] (FractionRing (SquareConstantField p s)[X])
          (kummerBranch c b R))) :=
  isSplittingField_AdjoinRoot_X_pow_sub_C (squareRationalField_primitiveRoots p s)
    (kummerBranch_fraction_irreducible c b R (p ^ (s + 1)))

/-- The Kummer extension is Galois, with no assumed splitting or separability premise. -/
theorem squareKummer_isGalois (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ) :
    IsGalois (FractionRing (SquareConstantField p s)[X]) (SquareKummerField p s c b R) := by
  letI := squareKummer_isSplittingField p s c b R
  exact isGalois_of_isSplittingField_X_pow_sub_C (squareRationalField_primitiveRoots p s)
    (kummerBranch_fraction_irreducible c b R (p ^ (s + 1))) _

/-- Its relative Galois group is cyclic. -/
theorem squareKummer_isCyclic (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ) :
    IsCyclic (SquareKummerField p s c b R ≃ₐ[FractionRing (SquareConstantField p s)[X]]
      SquareKummerField p s c b R) := by
  letI := squareKummer_isSplittingField p s c b R
  exact isCyclic_of_isSplittingField_X_pow_sub_C (squareRationalField_primitiveRoots p s)
    (kummerBranch_fraction_irreducible c b R (p ^ (s + 1))) _

/-- Every relative automorphism comes from a root of unity in the constant field. -/
def squareKummerAutEquiv (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ) :
    rootsOfUnity (p ^ (s + 1) + 1) (SquareConstantField p s) ≃*
      (SquareKummerField p s c b R ≃ₐ[FractionRing (SquareConstantField p s)[X]]
        SquareKummerField p s c b R) :=
  (rootsOfUnityEquivOfPrimitiveRoots
    (algebraMap (SquareConstantField p s) (FractionRing (SquareConstantField p s)[X])).injective
    (squareConstantField_primitiveRoots p s)).trans
    (autAdjoinRootXPowSubCEquiv (squareRationalField_primitiveRoots p s)
      (kummerBranch_fraction_irreducible c b R (p ^ (s + 1))))

/-- The roots-of-unity description acts on the generator by scalar multiplication. -/
theorem squareKummerAutEquiv_root (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)
    (ζ : rootsOfUnity (p ^ (s + 1) + 1) (SquareConstantField p s)) :
    squareKummerAutEquiv p s c b R ζ
      (AdjoinRoot.root (kummerBranchFieldPolynomial c b R (p ^ (s + 1)))) =
    algebraMap (FractionRing (SquareConstantField p s)[X]) (SquareKummerField p s c b R)
      (algebraMap (SquareConstantField p s) (FractionRing (SquareConstantField p s)[X])
        (ζ : (SquareConstantField p s)ˣ)) *
      AdjoinRoot.root (kummerBranchFieldPolynomial c b R (p ^ (s + 1))) := by
  change autAdjoinRootXPowSubC (p ^ (s + 1) + 1)
    (algebraMap (SquareConstantField p s)[X] (FractionRing (SquareConstantField p s)[X])
      (kummerBranch c b R)) _ _ = _
  erw [autAdjoinRootXPowSubC_root, Algebra.smul_def]
  rfl

/-- The radical extension is finite-dimensional by its monic defining equation. -/
instance squareKummer_finiteDimensional (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ) :
    FiniteDimensional (FractionRing (SquareConstantField p s)[X])
      (SquareKummerField p s c b R) :=
  (monic_X_pow_sub_C _ (Nat.succ_ne_zero (p ^ (s + 1)))).finite_adjoinRoot

/-- The number of relative automorphisms is exactly the covering degree. -/
theorem squareKummer_card_aut (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ) :
    Nat.card (SquareKummerField p s c b R ≃ₐ[FractionRing (SquareConstantField p s)[X]]
      SquareKummerField p s c b R) = p ^ (s + 1) + 1 := by
  letI := squareKummer_isGalois p s c b R
  rw [IsGalois.card_aut_eq_finrank]
  exact kummerBranchField_finrank c b R (p ^ (s + 1))

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
