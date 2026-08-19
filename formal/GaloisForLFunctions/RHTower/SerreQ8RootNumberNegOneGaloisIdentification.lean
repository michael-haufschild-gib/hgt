import GaloisForLFunctions.RHTower.SerreQ8RootNumberNegOneGalois
import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# Exact Q8 identification of Serre's radical field

The preceding leaf proves that Serre's radical field is Galois by counting
eight explicit automorphisms.  This leaf proves the stronger statement that
their multiplication table is the actual `QuaternionGroup 2` table, hence
identifies the field's `ℚ`-Galois group with `Q₈`.

No root-number calculation is made here.  The global Artin epsilon-factor
calculation remains a separate analytic-arithmetic input.
-/

namespace RHTower

noncomputable section

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField
local notation "K3" => SerreQ8TopField

noncomputable local instance serreQ8IdFiniteDimensionalK1K2 : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_secondQuadratic_irreducible.ne_zero).basis

noncomputable local instance serreQ8IdFiniteDimensionalK2K3 : FiniteDimensional K2 K3 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      serreQ8_thirdQuadratic_irreducible.ne_zero).basis

noncomputable local instance serreQ8IdFiniteDimensionalRatK2 : FiniteDimensional ℚ K2 :=
  FiniteDimensional.trans ℚ K1 K2

noncomputable local instance serreQ8IdFiniteDimensionalRatK3 : FiniteDimensional ℚ K3 :=
  FiniteDimensional.trans ℚ K2 K3

theorem serreQ8IAlgPow_add (i j : ZMod 4) :
    serreQ8IAlgPow (i + j) = serreQ8IAlgPow i * serreQ8IAlgPow j := by
  unfold serreQ8IAlgPow
  rw [← pow_add]
  apply pow_eq_pow_iff_modEq.mpr
  rw [serreQ8_orderOf_I, ZMod.val_add]
  exact Nat.mod_modEq _ _

theorem serreQ8JAlgEquiv_sq_eq_serreQ8CAlgEquiv : serreQ8JAlgEquiv ^ 2 = serreQ8CAlgEquiv := by
  ext w
  change serreQ8J (serreQ8J w) = serreQ8C w
  exact congrArg (fun f : K3 →+* K3 => f w) serreQ8J_sq_eq_C

theorem serreQ8IAlgEquiv_mul_serreQ8JAlgEquiv :
    serreQ8IAlgEquiv * serreQ8JAlgEquiv = serreQ8CAlgEquiv * (serreQ8JAlgEquiv * serreQ8IAlgEquiv) := by
  ext w
  change serreQ8I (serreQ8J w) = serreQ8C (serreQ8J (serreQ8I w))
  exact congrArg (fun f : K3 →+* K3 => f w)
    serreQ8I_comp_J_eq_C_comp_J_comp_I

theorem serreQ8CAlgEquiv_commutes_J :
    serreQ8CAlgEquiv * serreQ8JAlgEquiv = serreQ8JAlgEquiv * serreQ8CAlgEquiv := by
  calc
    serreQ8CAlgEquiv * serreQ8JAlgEquiv = serreQ8JAlgEquiv ^ 2 * serreQ8JAlgEquiv := by
      rw [serreQ8JAlgEquiv_sq_eq_serreQ8CAlgEquiv]
    _ = serreQ8JAlgEquiv * (serreQ8JAlgEquiv ^ 2) := by
      rw [pow_two, mul_assoc]
    _ = serreQ8JAlgEquiv * serreQ8CAlgEquiv := by
      rw [serreQ8JAlgEquiv_sq_eq_serreQ8CAlgEquiv]

theorem serreQ8IAlgEquiv_mul_serreQ8JAlgEquiv_eq_serreQ8JAlgEquiv_mul_Icube :
    serreQ8IAlgEquiv * serreQ8JAlgEquiv = serreQ8JAlgEquiv * serreQ8IAlgEquiv ^ 3 := by
  calc
    serreQ8IAlgEquiv * serreQ8JAlgEquiv = serreQ8CAlgEquiv * (serreQ8JAlgEquiv * serreQ8IAlgEquiv) :=
      serreQ8IAlgEquiv_mul_serreQ8JAlgEquiv
    _ = (serreQ8CAlgEquiv * serreQ8JAlgEquiv) * serreQ8IAlgEquiv := by rw [mul_assoc]
    _ = (serreQ8JAlgEquiv * serreQ8CAlgEquiv) * serreQ8IAlgEquiv := by
      rw [serreQ8CAlgEquiv_commutes_J]
    _ = serreQ8JAlgEquiv * (serreQ8CAlgEquiv * serreQ8IAlgEquiv) := by rw [mul_assoc]
    _ = serreQ8JAlgEquiv * (serreQ8IAlgEquiv ^ 2 * serreQ8IAlgEquiv) := by
      rw [serreQ8IAlgEquiv_sq_eq_serreQ8CAlgEquiv]
    _ = serreQ8JAlgEquiv * serreQ8IAlgEquiv ^ 3 := by rfl

theorem serreQ8Ipow_nat_mul_J (n : ℕ) :
    serreQ8IAlgEquiv ^ n * serreQ8JAlgEquiv = serreQ8JAlgEquiv * serreQ8IAlgEquiv ^ (3 * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        serreQ8IAlgEquiv ^ (Nat.succ n) * serreQ8JAlgEquiv =
            (serreQ8IAlgEquiv ^ n * serreQ8IAlgEquiv) * serreQ8JAlgEquiv := by rw [pow_succ]
        _ = serreQ8IAlgEquiv ^ n * (serreQ8IAlgEquiv * serreQ8JAlgEquiv) := by rw [mul_assoc]
        _ = serreQ8IAlgEquiv ^ n * (serreQ8JAlgEquiv * serreQ8IAlgEquiv ^ 3) := by
          rw [serreQ8IAlgEquiv_mul_serreQ8JAlgEquiv_eq_serreQ8JAlgEquiv_mul_Icube]
        _ = (serreQ8IAlgEquiv ^ n * serreQ8JAlgEquiv) * serreQ8IAlgEquiv ^ 3 := by rw [mul_assoc]
        _ = (serreQ8JAlgEquiv * serreQ8IAlgEquiv ^ (3 * n)) * serreQ8IAlgEquiv ^ 3 := by rw [ih]
        _ = serreQ8JAlgEquiv * (serreQ8IAlgEquiv ^ (3 * n) * serreQ8IAlgEquiv ^ 3) := by rw [mul_assoc]
        _ = serreQ8JAlgEquiv * serreQ8IAlgEquiv ^ (3 * Nat.succ n) := by
          rw [← pow_add]
          congr 2

private theorem serreQ8_three_mul_val_mod_eq_neg_val (i : ZMod 4) :
    3 * i.val ≡ (-i).val [MOD 4] := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  have hthree : (3 : ZMod 4) = -1 := by
    apply eq_neg_iff_add_eq_zero.mpr
    change (4 : ZMod 4) = 0
    exact ZMod.natCast_self 4
  calc
    ((3 * i.val : ℕ) : ZMod 4) = (3 : ZMod 4) * (i.val : ZMod 4) := by norm_num
    _ = (3 : ZMod 4) * i := by simp
    _ = (-1 : ZMod 4) * i := by rw [hthree]
    _ = -i := by ring
    _ = ((-i).val : ZMod 4) := by simp

theorem serreQ8IAlgPow_mul_J (i : ZMod 4) :
    serreQ8IAlgPow i * serreQ8JAlgEquiv = serreQ8JAlgEquiv * serreQ8IAlgPow (-i) := by
  unfold serreQ8IAlgPow
  rw [serreQ8Ipow_nat_mul_J]
  congr 1
  apply pow_eq_pow_iff_modEq.mpr
  rw [serreQ8_orderOf_I]
  exact serreQ8_three_mul_val_mod_eq_neg_val i

theorem serreQ8IAlgPow_two_eq_C : serreQ8IAlgPow (2 : ZMod 4) = serreQ8CAlgEquiv := by
  unfold serreQ8IAlgPow
  have htwo : (2 : ZMod 4).val = 2 := ZMod.val_cast_of_lt (by norm_num)
  rw [htwo]
  exact serreQ8IAlgEquiv_sq_eq_serreQ8CAlgEquiv

theorem serreQ8AutCandidate_a (i : ZMod 4) :
    serreQ8AutCandidate (QuaternionGroup.a i) = serreQ8IAlgPow i := rfl

theorem serreQ8AutCandidate_xa (i : ZMod 4) :
    serreQ8AutCandidate (QuaternionGroup.xa i) = serreQ8JAlgEquiv * serreQ8IAlgPow i := by
  ext w
  rfl

noncomputable def serreQ8AutCandidateHom : QuaternionGroup 2 →* Gal(K3/ℚ) where
  toFun := serreQ8AutCandidate
  map_one' := by
    change serreQ8IAlgPow (0 : ZMod 4) = 1
    unfold serreQ8IAlgPow
    simp
  map_mul' := by
    rintro (i | i) (j | j)
    · change serreQ8IAlgPow (i + j) = serreQ8IAlgPow i * serreQ8IAlgPow j
      exact serreQ8IAlgPow_add i j
    · change serreQ8JAlgEquiv * serreQ8IAlgPow (j - i) =
        serreQ8IAlgPow i * (serreQ8JAlgEquiv * serreQ8IAlgPow j)
      calc
        serreQ8JAlgEquiv * serreQ8IAlgPow (j - i) =
            serreQ8JAlgEquiv * (serreQ8IAlgPow (-i) * serreQ8IAlgPow j) := by
              rw [show j - i = -i + j by ring, serreQ8IAlgPow_add]
        _ = (serreQ8JAlgEquiv * serreQ8IAlgPow (-i)) * serreQ8IAlgPow j := by rw [mul_assoc]
        _ = (serreQ8IAlgPow i * serreQ8JAlgEquiv) * serreQ8IAlgPow j := by
              rw [serreQ8IAlgPow_mul_J]
        _ = serreQ8IAlgPow i * (serreQ8JAlgEquiv * serreQ8IAlgPow j) := by rw [mul_assoc]
    · change serreQ8JAlgEquiv * serreQ8IAlgPow (i + j) =
        (serreQ8JAlgEquiv * serreQ8IAlgPow i) * serreQ8IAlgPow j
      rw [serreQ8IAlgPow_add, mul_assoc]
    · change serreQ8IAlgPow ((2 : ZMod 4) + j - i) =
        (serreQ8JAlgEquiv * serreQ8IAlgPow i) * (serreQ8JAlgEquiv * serreQ8IAlgPow j)
      symm
      calc
        (serreQ8JAlgEquiv * serreQ8IAlgPow i) * (serreQ8JAlgEquiv * serreQ8IAlgPow j) =
            serreQ8JAlgEquiv * ((serreQ8IAlgPow i * serreQ8JAlgEquiv) * serreQ8IAlgPow j) := by
              simp only [mul_assoc]
        _ = serreQ8JAlgEquiv * ((serreQ8JAlgEquiv * serreQ8IAlgPow (-i)) * serreQ8IAlgPow j) := by
              rw [serreQ8IAlgPow_mul_J]
        _ = (serreQ8JAlgEquiv * serreQ8JAlgEquiv) *
            (serreQ8IAlgPow (-i) * serreQ8IAlgPow j) := by
              simp only [mul_assoc]
        _ = serreQ8CAlgEquiv * (serreQ8IAlgPow (-i) * serreQ8IAlgPow j) := by
              rw [← pow_two, serreQ8JAlgEquiv_sq_eq_serreQ8CAlgEquiv]
        _ = serreQ8IAlgPow (2 : ZMod 4) *
            (serreQ8IAlgPow (-i) * serreQ8IAlgPow j) := by
              rw [serreQ8IAlgPow_two_eq_C]
        _ = (serreQ8IAlgPow (2 : ZMod 4) * serreQ8IAlgPow (-i)) * serreQ8IAlgPow j := by
              rw [mul_assoc]
        _ = serreQ8IAlgPow ((2 : ZMod 4) + (-i)) * serreQ8IAlgPow j := by
              rw [← serreQ8IAlgPow_add]
        _ = serreQ8IAlgPow (((2 : ZMod 4) + (-i)) + j) := by
              rw [← serreQ8IAlgPow_add]
        _ = serreQ8IAlgPow ((2 : ZMod 4) + j - i) := by
              congr 1
              ring

theorem serreQ8AutCandidateHom_bijective : Function.Bijective serreQ8AutCandidateHom := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨serreQ8AutCandidate_injective, ?_⟩
  rw [QuaternionGroup.card, serreQ8Aut_card_eq_eight]

/-- The actual `ℚ`-Galois group of the documented field is the quaternion group `Q₈`. -/
noncomputable def serreQ8_galoisEquivQ8 :
    Gal(K3/ℚ) ≃* QuaternionGroup 2 :=
  (MulEquiv.ofBijective serreQ8AutCandidateHom serreQ8AutCandidateHom_bijective).symm

end

end RHTower
