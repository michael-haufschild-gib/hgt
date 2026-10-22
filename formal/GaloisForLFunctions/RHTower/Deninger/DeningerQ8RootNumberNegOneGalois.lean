import GaloisForLFunctions.RHTower.Deninger.DeningerQ8RootNumberNegOneAutomorphisms
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# Normality of the legacy quaternionic radical field

This leaf proves normality of the literal degree-eight field historically labelled
`RootNumberNegOne`.  The input is not an assumed Galois action: it
constructs eight distinct `ℚ`-algebra automorphisms, indexed by the eight
elements of `QuaternionGroup 2`, from the concrete `I` and `J` radical lifts.
The finite automorphism bound and the already-proved degree then force
`IsGalois ℚ K`.

The next leaf packages the candidate enumeration as a group isomorphism
`Gal(K/ℚ) ≃* QuaternionGroup 2`.  Neither leaf establishes an Artin root number;
the authenticated root-number-minus-one witness is a different Serre field.
-/

namespace RHTower

noncomputable section

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField
local notation "K3" => deningerQ8RootNumberNegOneTopField

noncomputable local instance q8FiniteDimensionalK1K2 : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_secondQuadratic_irreducible.ne_zero).basis

noncomputable local instance q8FiniteDimensionalK2K3 : FiniteDimensional K2 K3 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_thirdQuadratic_irreducible.ne_zero).basis

noncomputable local instance q8FiniteDimensionalRatK2 : FiniteDimensional ℚ K2 :=
  FiniteDimensional.trans ℚ K1 K2

noncomputable local instance q8FiniteDimensionalRatK3 : FiniteDimensional ℚ K3 :=
  FiniteDimensional.trans ℚ K2 K3

theorem q8C_bijective : Function.Bijective q8C := by
  constructor
  · intro a b hab
    have h := congrArg (fun f : K3 →+* K3 => f a = f b) q8C_sq_eq_id
    simpa [RingHom.comp_apply, hab] using h
  · intro w
    refine ⟨q8C w, ?_⟩
    have h := congrArg (fun f : K3 →+* K3 => f w) q8C_sq_eq_id
    simpa [RingHom.comp_apply] using h

noncomputable def q8CEquiv : K3 ≃+* K3 := RingEquiv.ofBijective q8C q8C_bijective

noncomputable def q8IAlgEquiv : K3 ≃ₐ[ℚ] K3 where
  __ := q8IEquiv
  commutes' q := q8I_rat q

noncomputable def q8JAlgEquiv : K3 ≃ₐ[ℚ] K3 where
  __ := q8JEquiv
  commutes' q := q8J_rat q

noncomputable def q8CAlgEquiv : K3 ≃ₐ[ℚ] K3 where
  __ := q8CEquiv
  commutes' q := q8C_rat q

theorem q8IAlgEquiv_apply (w : K3) : q8IAlgEquiv w = q8I w := rfl
theorem q8JAlgEquiv_apply (w : K3) : q8JAlgEquiv w = q8J w := rfl
theorem q8CAlgEquiv_apply (w : K3) : q8CAlgEquiv w = q8C w := rfl

theorem q8IAlgEquiv_sq_eq_q8CAlgEquiv : q8IAlgEquiv ^ 2 = q8CAlgEquiv := by
  ext w
  change q8I (q8I w) = q8C w
  exact congrArg (fun f : K3 →+* K3 => f w) q8I_sq_eq_q8C

theorem q8CAlgEquiv_sq_eq_one : q8CAlgEquiv ^ 2 = 1 := by
  ext w
  change q8C (q8C w) = w
  have h := congrArg (fun f : K3 →+* K3 => f w) q8C_sq_eq_id
  simpa [RingHom.comp_apply] using h

theorem q8IAlgEquiv_fourth_eq_one : q8IAlgEquiv ^ 4 = 1 := by
  calc
    q8IAlgEquiv ^ 4 = q8IAlgEquiv ^ 2 * q8IAlgEquiv ^ 2 := by
      rw [show 4 = 2 + 2 by norm_num, pow_add]
    _ = q8CAlgEquiv * q8CAlgEquiv := by
      rw [q8IAlgEquiv_sq_eq_q8CAlgEquiv]
    _ = q8CAlgEquiv ^ 2 := by rw [pow_two]
    _ = 1 := q8CAlgEquiv_sq_eq_one

theorem q8IAlgEquiv_sq_ne_one : q8IAlgEquiv ^ 2 ≠ 1 := by
  intro h
  letI : CharZero K3 :=
    charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
  have hroot := congrArg
    (fun f : K3 ≃ₐ[ℚ] K3 => f deningerQ8RootNumberNegOneTopRoot) h
  change q8I (q8I deningerQ8RootNumberNegOneTopRoot) =
    deningerQ8RootNumberNegOneTopRoot at hroot
  rw [q8I_root, q8I_candidate] at hroot
  apply q8TopRoot_ne_zero
  have hsum : deningerQ8RootNumberNegOneTopRoot +
      deningerQ8RootNumberNegOneTopRoot = 0 :=
    neg_eq_iff_add_eq_zero.mp hroot
  have htwice : (2 : K3) * deningerQ8RootNumberNegOneTopRoot = 0 := by
    rw [two_mul]
    exact hsum
  exact (mul_eq_zero.mp htwice).resolve_left (by norm_num)

theorem q8_orderOf_I : orderOf q8IAlgEquiv = 4 := by
  change orderOf q8IAlgEquiv = 2 ^ 2
  apply orderOf_eq_prime_pow
  · simpa using q8IAlgEquiv_sq_ne_one
  · simpa using q8IAlgEquiv_fourth_eq_one

noncomputable def q8IAlgPow (i : ZMod 4) : K3 ≃ₐ[ℚ] K3 := q8IAlgEquiv ^ i.val

theorem q8IAlgPow_injective : Function.Injective q8IAlgPow := by
  intro i j hij
  have hpow : q8IAlgEquiv ^ i.val = q8IAlgEquiv ^ j.val := hij
  have hmod : i.val % 4 = j.val % 4 := by
    have h := (pow_eq_pow_iff_modEq.mp hpow)
    simpa [Nat.ModEq, q8_orderOf_I] using h
  apply ZMod.val_injective 4
  rw [← Nat.mod_eq_of_lt (ZMod.val_lt i), ← Nat.mod_eq_of_lt (ZMod.val_lt j)]
  exact hmod

theorem q8IAlgEquiv_topY :
    q8IAlgEquiv deningerQ8RootNumberNegOneTopY =
      deningerQ8RootNumberNegOneTopY := by
  exact q8I_topY

theorem q8IAlgPow_topY (i : ZMod 4) :
    q8IAlgPow i deningerQ8RootNumberNegOneTopY =
      deningerQ8RootNumberNegOneTopY := by
  unfold q8IAlgPow
  induction i.val with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, AlgEquiv.mul_apply, q8IAlgEquiv_topY, ih]

/-- The eight explicit `Q₈`-labelled automorphisms of the literal field. -/
noncomputable def q8AutCandidate : QuaternionGroup 2 → Gal(K3/ℚ)
  | .a i => q8IAlgPow i
  | .xa i => (q8IAlgPow i).trans q8JAlgEquiv

theorem q8AutCandidate_injective : Function.Injective q8AutCandidate := by
  intro g h hgh
  rcases g with i | i <;> rcases h with j | j
  · change q8IAlgPow i = q8IAlgPow j at hgh
    exact congrArg QuaternionGroup.a (q8IAlgPow_injective hgh)
  · exfalso
    have htop := congrArg
      (fun f : Gal(K3/ℚ) => f deningerQ8RootNumberNegOneTopY) hgh
    change q8IAlgPow i deningerQ8RootNumberNegOneTopY =
      q8JAlgEquiv (q8IAlgPow j deningerQ8RootNumberNegOneTopY) at htop
    rw [q8IAlgPow_topY, q8IAlgPow_topY, q8JAlgEquiv_apply, q8J_topY] at htop
    apply q8TopY_ne_zero
    have hsum : deningerQ8RootNumberNegOneTopY +
        deningerQ8RootNumberNegOneTopY = 0 :=
      eq_neg_iff_add_eq_zero.mp htop
    have htwice : (2 : K3) * deningerQ8RootNumberNegOneTopY = 0 := by
      rw [two_mul]
      exact hsum
    exact (mul_eq_zero.mp htwice).resolve_left (by
      letI : CharZero K3 :=
        charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
      norm_num)
  · exfalso
    have htop := congrArg
      (fun f : Gal(K3/ℚ) => f deningerQ8RootNumberNegOneTopY) hgh
    change q8JAlgEquiv (q8IAlgPow i deningerQ8RootNumberNegOneTopY) =
      q8IAlgPow j deningerQ8RootNumberNegOneTopY at htop
    rw [q8IAlgPow_topY, q8IAlgPow_topY, q8JAlgEquiv_apply, q8J_topY] at htop
    apply q8TopY_ne_zero
    have hsum : deningerQ8RootNumberNegOneTopY +
        deningerQ8RootNumberNegOneTopY = 0 :=
      neg_eq_iff_add_eq_zero.mp htop
    have htwice : (2 : K3) * deningerQ8RootNumberNegOneTopY = 0 := by
      rw [two_mul]
      exact hsum
    exact (mul_eq_zero.mp htwice).resolve_left (by
      letI : CharZero K3 :=
        charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
      norm_num)
  · apply congrArg QuaternionGroup.xa
    apply q8IAlgPow_injective
    apply AlgEquiv.ext
    intro w
    apply q8JAlgEquiv.injective
    have hw := congrArg (fun f : Gal(K3/ℚ) => f w) hgh
    change q8JAlgEquiv (q8IAlgPow i w) = q8JAlgEquiv (q8IAlgPow j w) at hw
    exact hw

theorem q8Aut_card_eq_eight : Fintype.card Gal(K3/ℚ) = 8 := by
  apply Nat.le_antisymm
  · calc
      Fintype.card Gal(K3/ℚ) ≤ Module.finrank ℚ K3 := AlgEquiv.card_le
      _ = 8 := deningerQ8RootNumberNegOneTopField_finrank_over_rat
  · have hle := Fintype.card_le_of_injective _ q8AutCandidate_injective
    rw [QuaternionGroup.card] at hle
    norm_num at hle ⊢
    exact hle

theorem q8Aut_natCard_eq_eight : Nat.card Gal(K3/ℚ) = 8 := by
  rw [Nat.card_eq_fintype_card]
  exact q8Aut_card_eq_eight

/-- The literal degree-eight radical field is Galois over `ℚ`. -/
theorem deningerQ8RootNumberNegOne_isGalois : IsGalois ℚ K3 := by
  apply IsGalois.of_card_aut_eq_finrank
  rw [q8Aut_natCard_eq_eight, deningerQ8RootNumberNegOneTopField_finrank_over_rat]

end

end RHTower
