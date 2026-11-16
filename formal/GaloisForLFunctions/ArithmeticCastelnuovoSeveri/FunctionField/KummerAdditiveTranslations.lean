import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerCoordinateHom
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerFieldHomExt
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.FiniteField.FrobeniusFixedCardinality

/-!
# Translations of additive Kummer models

Every constant fixed by the `p^(d+1)`-power map translates the rational
coordinate of `z^(n+1)=c(y-y^(p^(d+1)))` and fixes its radical.
These substitutions give a faithful action of the additive fixed field
on the actual function field, with no restriction on the covering degree.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial RenormalizedIntersectionArithmeticCounts
variable (p : ℕ) [Fact p.Prime] {K : Type*} [Field K] [CharP K p]
  (c : Kˣ) (d n : ℕ)
local notation "q" => p ^ (d + 1)
local notation "L" => KummerBranchField c (q - 2) 1 n
local notation "F" => frobeniusFixedSubfield p K (d + 1)
local notation "y" => algebraMap K[X] L X
local notation "z" => AdjoinRoot.root (kummerBranchFieldPolynomial c (q - 2) 1 n)
local notation "φ" => algebraMap K L

local instance additiveKummerCharP : CharP L p :=
  charP_of_injective_algebraMap (algebraMap K L).injective p

omit [CharP K p] in
private theorem additiveKummer_factor (x : L) :
    x * (1 - x ^ (q - 2 + 1)) = x - x ^ q := by
  have hq : 2 ≤ q := Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt
  rw [mul_sub, mul_one, ← pow_succ', show q - 2 + 1 + 1 = q by omega]

omit [CharP K p] in
private theorem additiveKummer_root : z ^ (n + 1) = φ c * (y - y ^ q) := by
  have h := kummerBranchField_root_pow c (q - 2) 1 n
  rw [← IsScalarTower.algebraMap_apply, kummerBranch, map_mul, map_mul,
    map_pow, map_sub, map_one, map_pow] at h
  have hc : algebraMap K[X] L (C (c : K)) = φ c :=
    (IsScalarTower.algebraMap_apply K K[X] L c).symm
  rw [hc, pow_one, mul_assoc, additiveKummer_factor] at h
  exact h

private theorem additiveKummer_transcendental (a : F) :
    Transcendental K (y + φ a.val) := by
  intro h
  have hy := h.isIntegral.sub (show IsIntegral K (φ a.val) from isIntegral_algebraMap)
  rw [add_sub_cancel_right] at hy
  exact kummerBranchField_coordinate_transcendental c (q - 2) 1 n hy.isAlgebraic

private theorem additiveKummer_translated_equation (a : F) :
    z ^ (n + 1) = φ c * (y + φ a.val) * (1 - (y + φ a.val) ^ (q - 2 + 1)) ^ 1 := by
  rw [pow_one, mul_assoc, additiveKummer_factor, add_pow_char_pow, ← map_pow φ a.val q,
    (show a.val ^ q = a.val from a.property)]
  have he : y + φ a.val - (y ^ q + φ a.val) = y - y ^ q := by ring
  rw [he]
  exact additiveKummer_root p c d n

/-- Translation by a fixed constant preserves the additive Kummer equation. -/
def kummerAdditiveTranslationHom (a : F) : L →ₐ[K] L :=
  kummerBranchFieldHomOfCoordinates c (q - 2) 1 n (y + φ a.val) z
    (additiveKummer_transcendental p c d n a) (additiveKummer_translated_equation p c d n a)

/-- The rational coordinate is translated by the chosen constant. -/
theorem kummerAdditiveTranslationHom_coordinate (a : F) :
    kummerAdditiveTranslationHom p c d n a y = y + φ a.val :=
  kummerBranchFieldHomOfCoordinates_coordinate _ _ _ _ _ _ _ _

/-- Additive translations fix the radical generator. -/
theorem kummerAdditiveTranslationHom_root (a : F) :
    kummerAdditiveTranslationHom p c d n a z = z :=
  kummerBranchFieldHomOfCoordinates_root _ _ _ _ _ _ _ _

/-- Subtracting the translation constant recovers the original coordinate. -/
theorem kummerAdditiveTranslationHom_surjective (a : F) :
    Function.Surjective (kummerAdditiveTranslationHom p c d n a) := by
  let f := kummerAdditiveTranslationHom p c d n a
  have hy : y ∈ f.fieldRange := by
    have h := f.fieldRange.sub_mem (show f y ∈ f.fieldRange from ⟨y, rfl⟩)
      (f.fieldRange.algebraMap_mem a.val)
    change kummerAdditiveTranslationHom p c d n a y - φ a.val ∈ f.fieldRange at h
    rw [kummerAdditiveTranslationHom_coordinate, add_sub_cancel_right] at h
    exact h
  have hz : z ∈ f.fieldRange := ⟨z, kummerAdditiveTranslationHom_root p c d n a⟩
  have htop := kummerBranchField_eq_top_of_coordinate_root_mem c (q - 2) 1 n f.fieldRange hy hz
  intro x
  have hx : x ∈ f.fieldRange := by rw [htop]; trivial
  exact hx

/-- Every fixed constant induces an automorphism of the additive Kummer function field. -/
def kummerAdditiveTranslationAut (a : F) : L ≃ₐ[K] L :=
  AlgEquiv.ofBijective (kummerAdditiveTranslationHom p c d n a)
    ⟨(kummerAdditiveTranslationHom p c d n a).injective,
      kummerAdditiveTranslationHom_surjective p c d n a⟩

/-- Substituting two translations adds their parameters. -/
theorem kummerAdditiveTranslationHom_comp (a b : F) :
    (kummerAdditiveTranslationHom p c d n a).comp (kummerAdditiveTranslationHom p c d n b) =
      kummerAdditiveTranslationHom p c d n (a + b) := by
  apply kummerBranchField_algHom_ext c (q - 2) 1 n
  · change kummerAdditiveTranslationHom p c d n a
      (kummerAdditiveTranslationHom p c d n b y) = kummerAdditiveTranslationHom p c d n (a + b) y
    rw [kummerAdditiveTranslationHom_coordinate, map_add, AlgHom.commutes,
      kummerAdditiveTranslationHom_coordinate, kummerAdditiveTranslationHom_coordinate]
    change y + φ a.val + φ b.val = y + φ (a.val + b.val)
    rw [map_add, add_assoc]
  · change kummerAdditiveTranslationHom p c d n a
      (kummerAdditiveTranslationHom p c d n b z) = kummerAdditiveTranslationHom p c d n (a + b) z
    rw [kummerAdditiveTranslationHom_root, kummerAdditiveTranslationHom_root,
      kummerAdditiveTranslationHom_root]

/-- Zero translation induces the identity automorphism. -/
theorem kummerAdditiveTranslationAut_zero : kummerAdditiveTranslationAut p c d n 0 = 1 := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply kummerBranchField_algHom_ext c (q - 2) 1 n
  · change kummerAdditiveTranslationHom p c d n 0 y = y
    rw [kummerAdditiveTranslationHom_coordinate]
    change y + φ 0 = y
    rw [map_zero, add_zero]
  · exact kummerAdditiveTranslationHom_root p c d n 0

/-- Addition of parameters agrees with multiplication of field automorphisms. -/
theorem kummerAdditiveTranslationAut_add (a b : F) :
    kummerAdditiveTranslationAut p c d n (a + b) =
      kummerAdditiveTranslationAut p c d n a * kummerAdditiveTranslationAut p c d n b := by
  apply AlgEquiv.coe_toAlgHom_injective
  exact (kummerAdditiveTranslationHom_comp p c d n a b).symm

/-- The translated rational coordinate determines the parameter uniquely. -/
theorem kummerAdditiveTranslationAut_injective :
    Function.Injective (kummerAdditiveTranslationAut p c d n) := by
  intro a b h
  have hy := congrArg (fun σ : L ≃ₐ[K] L => σ y) h
  change kummerAdditiveTranslationHom p c d n a y = kummerAdditiveTranslationHom p c d n b y at hy
  rw [kummerAdditiveTranslationHom_coordinate, kummerAdditiveTranslationHom_coordinate] at hy
  exact Subtype.ext ((algebraMap K L).injective (add_left_cancel hy))

/-- The additive Frobenius fixed field embeds into the actual automorphism group. -/
def kummerAdditiveTranslationAutHom : Multiplicative F →* (L ≃ₐ[K] L) where
  toFun a := kummerAdditiveTranslationAut p c d n a.toAdd
  map_one' := kummerAdditiveTranslationAut_zero p c d n
  map_mul' a b := kummerAdditiveTranslationAut_add p c d n a.toAdd b.toAdd

/-- The additive fixed-field action is faithful. -/
theorem kummerAdditiveTranslationAutHom_injective :
    Function.Injective (kummerAdditiveTranslationAutHom p c d n) := by
  intro a b h
  exact kummerAdditiveTranslationAut_injective p c d n h

/-- The subgroup of translations has precisely as many elements as the fixed constant field. -/
theorem kummerAdditiveTranslationAutHom_range_card :
    Nat.card (kummerAdditiveTranslationAutHom p c d n).range = Nat.card F := by
  change Nat.card (Set.range (kummerAdditiveTranslationAutHom p c d n)) = Nat.card F
  rw [← Nat.card_congr (Equiv.ofInjective _ (kummerAdditiveTranslationAutHom_injective p c d n))]
  rfl

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
