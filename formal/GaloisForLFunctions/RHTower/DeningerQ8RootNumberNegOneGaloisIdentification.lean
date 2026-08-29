import GaloisForLFunctions.RHTower.DeningerQ8RootNumberNegOneGalois
import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# Exact Q8 identification of the legacy radical field

The preceding leaf proves that the literal radical field is Galois by counting
eight explicit automorphisms.  This leaf proves the stronger statement that
their multiplication table is the actual `QuaternionGroup 2` table, hence
identifies the field's `ℚ`-Galois group with `Q₈`.

No root-number claim is made here: its historical `RootNumberNegOne` filename
is not an arithmetic certificate.  The global Artin epsilon-factor calculation
for this literal field is a separate analytic-arithmetic input.
-/

namespace RHTower

noncomputable section

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField
local notation "K3" => deningerQ8RootNumberNegOneTopField

noncomputable local instance q8IdFiniteDimensionalK1K2 : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_secondQuadratic_irreducible.ne_zero).basis

noncomputable local instance q8IdFiniteDimensionalK2K3 : FiniteDimensional K2 K3 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_thirdQuadratic_irreducible.ne_zero).basis

noncomputable local instance q8IdFiniteDimensionalRatK2 : FiniteDimensional ℚ K2 :=
  FiniteDimensional.trans ℚ K1 K2

noncomputable local instance q8IdFiniteDimensionalRatK3 : FiniteDimensional ℚ K3 :=
  FiniteDimensional.trans ℚ K2 K3

theorem q8IAlgPow_add (i j : ZMod 4) :
    q8IAlgPow (i + j) = q8IAlgPow i * q8IAlgPow j := by
  unfold q8IAlgPow
  rw [← pow_add]
  apply pow_eq_pow_iff_modEq.mpr
  rw [q8_orderOf_I, ZMod.val_add]
  exact Nat.mod_modEq _ _

theorem q8JAlgEquiv_sq_eq_q8CAlgEquiv : q8JAlgEquiv ^ 2 = q8CAlgEquiv := by
  ext w
  change q8J (q8J w) = q8C w
  exact congrArg (fun f : K3 →+* K3 => f w) q8J_sq_eq_q8C

theorem q8IAlgEquiv_mul_q8JAlgEquiv :
    q8IAlgEquiv * q8JAlgEquiv = q8CAlgEquiv * (q8JAlgEquiv * q8IAlgEquiv) := by
  ext w
  change q8I (q8J w) = q8C (q8J (q8I w))
  exact congrArg (fun f : K3 →+* K3 => f w)
    q8I_comp_q8J_eq_q8C_comp_q8J_comp_q8I

theorem q8CAlgEquiv_commutes_J :
    q8CAlgEquiv * q8JAlgEquiv = q8JAlgEquiv * q8CAlgEquiv := by
  calc
    q8CAlgEquiv * q8JAlgEquiv = q8JAlgEquiv ^ 2 * q8JAlgEquiv := by
      rw [q8JAlgEquiv_sq_eq_q8CAlgEquiv]
    _ = q8JAlgEquiv * (q8JAlgEquiv ^ 2) := by
      rw [pow_two, mul_assoc]
    _ = q8JAlgEquiv * q8CAlgEquiv := by
      rw [q8JAlgEquiv_sq_eq_q8CAlgEquiv]

theorem q8IAlgEquiv_mul_q8JAlgEquiv_eq_q8JAlgEquiv_mul_Icube :
    q8IAlgEquiv * q8JAlgEquiv = q8JAlgEquiv * q8IAlgEquiv ^ 3 := by
  calc
    q8IAlgEquiv * q8JAlgEquiv = q8CAlgEquiv * (q8JAlgEquiv * q8IAlgEquiv) :=
      q8IAlgEquiv_mul_q8JAlgEquiv
    _ = (q8CAlgEquiv * q8JAlgEquiv) * q8IAlgEquiv := by rw [mul_assoc]
    _ = (q8JAlgEquiv * q8CAlgEquiv) * q8IAlgEquiv := by
      rw [q8CAlgEquiv_commutes_J]
    _ = q8JAlgEquiv * (q8CAlgEquiv * q8IAlgEquiv) := by rw [mul_assoc]
    _ = q8JAlgEquiv * (q8IAlgEquiv ^ 2 * q8IAlgEquiv) := by
      rw [q8IAlgEquiv_sq_eq_q8CAlgEquiv]
    _ = q8JAlgEquiv * q8IAlgEquiv ^ 3 := by rfl

theorem q8Ipow_nat_mul_J (n : ℕ) :
    q8IAlgEquiv ^ n * q8JAlgEquiv = q8JAlgEquiv * q8IAlgEquiv ^ (3 * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        q8IAlgEquiv ^ (Nat.succ n) * q8JAlgEquiv =
            (q8IAlgEquiv ^ n * q8IAlgEquiv) * q8JAlgEquiv := by rw [pow_succ]
        _ = q8IAlgEquiv ^ n * (q8IAlgEquiv * q8JAlgEquiv) := by rw [mul_assoc]
        _ = q8IAlgEquiv ^ n * (q8JAlgEquiv * q8IAlgEquiv ^ 3) := by
          rw [q8IAlgEquiv_mul_q8JAlgEquiv_eq_q8JAlgEquiv_mul_Icube]
        _ = (q8IAlgEquiv ^ n * q8JAlgEquiv) * q8IAlgEquiv ^ 3 := by rw [mul_assoc]
        _ = (q8JAlgEquiv * q8IAlgEquiv ^ (3 * n)) * q8IAlgEquiv ^ 3 := by rw [ih]
        _ = q8JAlgEquiv * (q8IAlgEquiv ^ (3 * n) * q8IAlgEquiv ^ 3) := by rw [mul_assoc]
        _ = q8JAlgEquiv * q8IAlgEquiv ^ (3 * Nat.succ n) := by
          rw [← pow_add]
          congr 2

private theorem q8_three_mul_val_mod_eq_neg_val (i : ZMod 4) :
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

theorem q8IAlgPow_mul_J (i : ZMod 4) :
    q8IAlgPow i * q8JAlgEquiv = q8JAlgEquiv * q8IAlgPow (-i) := by
  unfold q8IAlgPow
  rw [q8Ipow_nat_mul_J]
  congr 1
  apply pow_eq_pow_iff_modEq.mpr
  rw [q8_orderOf_I]
  exact q8_three_mul_val_mod_eq_neg_val i

theorem q8IAlgPow_two_eq_C : q8IAlgPow (2 : ZMod 4) = q8CAlgEquiv := by
  unfold q8IAlgPow
  have htwo : (2 : ZMod 4).val = 2 := ZMod.val_cast_of_lt (by norm_num)
  rw [htwo]
  exact q8IAlgEquiv_sq_eq_q8CAlgEquiv

theorem q8AutCandidate_a (i : ZMod 4) :
    q8AutCandidate (QuaternionGroup.a i) = q8IAlgPow i := rfl

theorem q8AutCandidate_xa (i : ZMod 4) :
    q8AutCandidate (QuaternionGroup.xa i) = q8JAlgEquiv * q8IAlgPow i := by
  ext w
  rfl

noncomputable def q8AutCandidateHom : QuaternionGroup 2 →* Gal(K3/ℚ) where
  toFun := q8AutCandidate
  map_one' := by
    change q8IAlgPow (0 : ZMod 4) = 1
    unfold q8IAlgPow
    simp
  map_mul' := by
    rintro (i | i) (j | j)
    · change q8IAlgPow (i + j) = q8IAlgPow i * q8IAlgPow j
      exact q8IAlgPow_add i j
    · change q8JAlgEquiv * q8IAlgPow (j - i) =
        q8IAlgPow i * (q8JAlgEquiv * q8IAlgPow j)
      calc
        q8JAlgEquiv * q8IAlgPow (j - i) =
            q8JAlgEquiv * (q8IAlgPow (-i) * q8IAlgPow j) := by
              rw [show j - i = -i + j by ring, q8IAlgPow_add]
        _ = (q8JAlgEquiv * q8IAlgPow (-i)) * q8IAlgPow j := by rw [mul_assoc]
        _ = (q8IAlgPow i * q8JAlgEquiv) * q8IAlgPow j := by
              rw [q8IAlgPow_mul_J]
        _ = q8IAlgPow i * (q8JAlgEquiv * q8IAlgPow j) := by rw [mul_assoc]
    · change q8JAlgEquiv * q8IAlgPow (i + j) =
        (q8JAlgEquiv * q8IAlgPow i) * q8IAlgPow j
      rw [q8IAlgPow_add, mul_assoc]
    · change q8IAlgPow ((2 : ZMod 4) + j - i) =
        (q8JAlgEquiv * q8IAlgPow i) * (q8JAlgEquiv * q8IAlgPow j)
      symm
      calc
        (q8JAlgEquiv * q8IAlgPow i) * (q8JAlgEquiv * q8IAlgPow j) =
            q8JAlgEquiv * ((q8IAlgPow i * q8JAlgEquiv) * q8IAlgPow j) := by
              simp only [mul_assoc]
        _ = q8JAlgEquiv * ((q8JAlgEquiv * q8IAlgPow (-i)) * q8IAlgPow j) := by
              rw [q8IAlgPow_mul_J]
        _ = (q8JAlgEquiv * q8JAlgEquiv) *
            (q8IAlgPow (-i) * q8IAlgPow j) := by
              simp only [mul_assoc]
        _ = q8CAlgEquiv * (q8IAlgPow (-i) * q8IAlgPow j) := by
              rw [← pow_two, q8JAlgEquiv_sq_eq_q8CAlgEquiv]
        _ = q8IAlgPow (2 : ZMod 4) *
            (q8IAlgPow (-i) * q8IAlgPow j) := by
              rw [q8IAlgPow_two_eq_C]
        _ = (q8IAlgPow (2 : ZMod 4) * q8IAlgPow (-i)) * q8IAlgPow j := by
              rw [mul_assoc]
        _ = q8IAlgPow ((2 : ZMod 4) + (-i)) * q8IAlgPow j := by
              rw [← q8IAlgPow_add]
        _ = q8IAlgPow (((2 : ZMod 4) + (-i)) + j) := by
              rw [← q8IAlgPow_add]
        _ = q8IAlgPow ((2 : ZMod 4) + j - i) := by
              congr 1
              ring

theorem q8AutCandidateHom_bijective : Function.Bijective q8AutCandidateHom := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨q8AutCandidate_injective, ?_⟩
  rw [QuaternionGroup.card, q8Aut_card_eq_eight]

/-- The actual `ℚ`-Galois group of the documented field is the quaternion group `Q₈`. -/
noncomputable def deningerQ8RootNumberNegOne_galoisEquivQ8 :
    Gal(K3/ℚ) ≃* QuaternionGroup 2 :=
  (MulEquiv.ofBijective q8AutCandidateHom q8AutCandidateHom_bijective).symm

end

end RHTower
