import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianTangentPlaces
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianInfinityAction
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianKummerInvariants

/-!
# Rational-place orbits of Hermitian translations

The transported affine places are distinct from infinity. Translation
acts on them by left multiplication of its parameters, so the action
is simply transitive on the affine rational places.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "K" => SquareConstantField p s
local notation "H" => HermitianKummerField p s
local notation "v" => hermitianKummerRadicalCoordinate p s
local notation "HK" => HermitianAffinePoint p s K
local notation "HP" => RationalConstantFieldPlaces K H
local notation "F" => hermitianTranslationFieldAutHom p s
local notation "point" => hermitianPointRationalPlace p s

/-- Every transported affine rational place differs from infinity. -/
theorem hermitianPointRationalPlace_ne_infinity (P : HK) :
    point P ≠ hermitianInfinityRationalPlace p s := by
  have hsmall : v - algebraMap K H P.val.1 ∈ (point P).val.val := by
    change hermitianPointValuation p s P (v - algebraMap K H P.val.1) ≤ 1
    rw [hermitianPointValuation_radical_sub, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hconst := (point P).val.property.2 P.val.1
  have hv : v - algebraMap K H P.val.1 + algebraMap K H P.val.1 ∈ (point P).val.val :=
    add_mem hsmall hconst
  have he : v - algebraMap K H P.val.1 + algebraMap K H P.val.1 = v := by ring
  rw [he] at hv
  intro h
  rw [h] at hv
  exact hermitianInfinity_radical_notMem p s hv

/-- Affine rational parameters together with infinity enumerate candidate rational places. -/
def hermitianRationalPlaceMap : HK ⊕ PUnit.{1} → HP :=
  Sum.elim point (fun _ => hermitianInfinityRationalPlace p s)

/-- The affine parameters and infinity give distinct actual rational places. -/
theorem hermitianRationalPlaceMap_injective :
    Function.Injective (hermitianRationalPlaceMap p s) := by
  intro x y h
  cases x with
  | inl P =>
    cases y with
    | inl U => exact congrArg Sum.inl (hermitianPointRationalPlace_injective p s h)
    | inr _ => exact (hermitianPointRationalPlace_ne_infinity p s P h).elim
  | inr _ =>
    cases y with
    | inl U => exact (hermitianPointRationalPlace_ne_infinity p s U h.symm).elim
    | inr _ => rfl

/-- Translation of actual affine places agrees with multiplication of rational parameters. -/
theorem hermitianPointRationalPlace_equivariant (U P : HK) :
    F U • point P = point (U * P) := by
  change F U • (F P • hermitianOriginRationalPlace p s) =
    F (U * P) • hermitianOriginRationalPlace p s
  rw [map_mul, mul_smul]

/-- No nonidentity translation fixes an affine rational place. -/
theorem hermitianTranslation_fixes_affine_iff (U P : HK) :
    F U • point P = point P ↔ U = 1 := by
  rw [hermitianPointRationalPlace_equivariant]
  constructor
  · intro h
    have he := hermitianPointRationalPlace_injective p s h
    exact mul_right_cancel (he.trans (one_mul P).symm)
  · intro h
    rw [h, one_mul]

/-- A unique rational translation carries any transported affine place to any other. -/
theorem hermitianTranslation_affine_existsUnique (P T : HK) :
    ∃! U : HK, F U • point P = point T := by
  refine ⟨T * P⁻¹, ?_, ?_⟩
  · change F (T * P⁻¹) • point P = point T
    rw [hermitianPointRationalPlace_equivariant, mul_assoc, inv_mul_cancel, mul_one]
  · intro U h
    rw [hermitianPointRationalPlace_equivariant] at h
    have he := hermitianPointRationalPlace_injective p s h
    calc
      U = U * (P * P⁻¹) := by rw [mul_inv_cancel, mul_one]
      _ = (U * P) * P⁻¹ := (mul_assoc _ _ _).symm
      _ = T * P⁻¹ := congrArg (fun A => A * P⁻¹) he

/-- The affine points and infinity account for every actual rational valuation place. -/
theorem hermitianRationalPlaceMap_bijective :
    Function.Bijective (hermitianRationalPlaceMap p s) := by
  letI : Finite HK := Nat.finite_of_card_ne_zero (by
    rw [hermitianTranslationGroup_card]
    exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))
  letI : Finite HP := Nat.finite_of_card_ne_zero (by
    rw [hermitianKummerRationalPlaces_card]
    exact Nat.succ_ne_zero _)
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨hermitianRationalPlaceMap_injective p s, ?_⟩
  rw [Nat.card_sum, hermitianTranslationGroup_card, Nat.card_unique (α := PUnit.{1}),
    hermitianKummerRationalPlaces_card]

/-- Rational Hermitian places are exactly affine rational points together with infinity. -/
def hermitianRationalPlaceEquiv : (HK ⊕ PUnit.{1}) ≃ HP :=
  Equiv.ofBijective (hermitianRationalPlaceMap p s) (hermitianRationalPlaceMap_bijective p s)

/-- Every actual rational Hermitian place is a transported affine point or infinity. -/
theorem hermitianRationalPlace_cases (W : HP) :
    (∃ P : HK, point P = W) ∨ W = hermitianInfinityRationalPlace p s := by
  obtain ⟨T, hT⟩ := (hermitianRationalPlaceMap_bijective p s).surjective W
  cases T with
  | inl P => exact Or.inl ⟨P, hT⟩
  | inr _ => exact Or.inr hT.symm

/-- A translation fixes a rational place exactly when it is the identity or the place is infinity. -/
theorem hermitianTranslation_fixedPlace_iff (U : HK) (W : HP) :
    F U • W = W ↔ U = 1 ∨ W = hermitianInfinityRationalPlace p s := by
  constructor
  · intro h
    rcases hermitianRationalPlace_cases p s W with ⟨P, rfl⟩ | hW
    · exact Or.inl ((hermitianTranslation_fixes_affine_iff p s U P).mp h)
    · exact Or.inr hW
  · rintro (rfl | rfl)
    · rw [map_one, one_smul]
    · exact hermitianTranslation_fixes_infinity p s U

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
