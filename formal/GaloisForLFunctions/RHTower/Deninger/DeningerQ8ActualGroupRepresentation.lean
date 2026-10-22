import GaloisForLFunctions.RHTower.Deninger.DeningerQ8SymplecticGeneratorRealization
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.Tactic

/-!
# The actual `QuaternionGroup 2` representation behind Deninger's transition matrices

The earlier generator calculation established the quaternion relations for two
matrices.  This file upgrades it to a literal complex-linear representation of
mathlib's `QuaternionGroup 2`, with its full group-action law and symplectic
invariance.  Thus the finite representation-theoretic part of Deninger's
quaternionic Artin input is no longer only a presentation calculation.

It deliberately does not assert an arithmetic realization as a number-field
Galois group or its Artin root number: those are independent arithmetic
statements in the cited no-go theorem.
-/

namespace RHTower

open QuaternionGroup

noncomputable section

abbrev Q8Carrier := ℂ × ℂ

/-- The cyclic order-four part of the standard two-dimensional `Q₈` action. -/
def q8Ipow (i : ZMod 4) (v : Q8Carrier) : Q8Carrier :=
  (Complex.I ^ i.val * v.1, (-Complex.I) ^ i.val * v.2)

private theorem I_pow_four : (Complex.I : ℂ) ^ 4 = 1 := by
  norm_num [pow_succ, Complex.I_mul_I]

private theorem neg_I_pow_four : (-Complex.I : ℂ) ^ 4 = 1 := by
  norm_num [pow_succ, Complex.I_mul_I]

private theorem I_pow_add_val (i j : ZMod 4) :
    Complex.I ^ (i + j).val = Complex.I ^ (i.val + j.val) := by
  rw [ZMod.val_add]
  apply pow_eq_pow_of_modEq (n := 4)
  · simp [Nat.ModEq]
  · exact I_pow_four

private theorem neg_I_pow_add_val (i j : ZMod 4) :
    (-Complex.I) ^ (i + j).val = (-Complex.I) ^ (i.val + j.val) := by
  rw [ZMod.val_add]
  apply pow_eq_pow_of_modEq (n := 4)
  · simp [Nat.ModEq]
  · exact neg_I_pow_four

theorem q8Ipow_add (i j : ZMod 4) (v : Q8Carrier) :
    q8Ipow (i + j) v = q8Ipow i (q8Ipow j v) := by
  ext <;> simp only [q8Ipow]
  · rw [I_pow_add_val, pow_add]
    ring
  · rw [neg_I_pow_add_val, pow_add]
    ring

private theorem three_eq_neg_one_zmod : (3 : ZMod 4) = -1 := by
  apply eq_neg_iff_add_eq_zero.mpr
  change (4 : ZMod 4) = 0
  exact ZMod.natCast_self 4

private theorem three_mul_val_mod_eq_neg_val (i : ZMod 4) :
    3 * i.val ≡ (-i).val [MOD 4] := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  calc
    ((3 * i.val : ℕ) : ZMod 4) = (3 : ZMod 4) * (i.val : ZMod 4) := by norm_num
    _ = (3 : ZMod 4) * i := by simp
    _ = (-1 : ZMod 4) * i := by rw [three_eq_neg_one_zmod]
    _ = -i := by ring
    _ = ((-i).val : ZMod 4) := by simp

private theorem val_mod_eq_three_mul_neg_val (i : ZMod 4) :
    i.val ≡ 3 * (-i).val [MOD 4] := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  calc
    (i.val : ZMod 4) = i := by simp
    _ = (-1 : ZMod 4) * (-i) := by ring
    _ = (3 : ZMod 4) * (-i) := by rw [three_eq_neg_one_zmod]
    _ = (3 : ZMod 4) * ((-i).val : ZMod 4) := by simp
    _ = ((3 * (-i).val : ℕ) : ZMod 4) := by norm_num

private theorem neg_I_eq_I_pow_three : (-Complex.I : ℂ) = Complex.I ^ 3 := by
  norm_num [pow_succ, Complex.I_mul_I]

private theorem neg_I_pow_val_eq_I_pow_neg_val (i : ZMod 4) :
    (-Complex.I : ℂ) ^ i.val = Complex.I ^ (-i).val := by
  rw [neg_I_eq_I_pow_three, ← pow_mul]
  apply pow_eq_pow_of_modEq (n := 4)
  · exact three_mul_val_mod_eq_neg_val i
  · exact I_pow_four

private theorem I_pow_val_eq_neg_I_pow_neg_val (i : ZMod 4) :
    Complex.I ^ i.val = (-Complex.I : ℂ) ^ (-i).val := by
  rw [neg_I_eq_I_pow_three, ← pow_mul]
  apply pow_eq_pow_of_modEq (n := 4)
  · exact val_mod_eq_three_mul_neg_val i
  · exact I_pow_four

theorem q8Ipow_apply_K (i : ZMod 4) (v : Q8Carrier) :
    q8Ipow i (deningerQuaternionTransitionK v) =
      deningerQuaternionTransitionK (q8Ipow (-i) v) := by
  rcases v with ⟨x, y⟩
  apply Prod.ext
  · change Complex.I ^ i.val * -y = -((-Complex.I) ^ (-i).val * y)
    rw [I_pow_val_eq_neg_I_pow_neg_val]
    ring
  · change (-Complex.I) ^ i.val * x = Complex.I ^ (-i).val * x
    rw [neg_I_pow_val_eq_I_pow_neg_val]

/-- The standard action of mathlib's actual quaternion group, with `xa 0`
acting by the transition `K`. -/
def deningerQ8GroupAction : QuaternionGroup 2 → Q8Carrier → Q8Carrier
  | .a i => q8Ipow i
  | .xa i => fun v => deningerQuaternionTransitionK (q8Ipow i v)

theorem q8Ipow_two_apply (v : Q8Carrier) :
    q8Ipow (2 : ZMod 4) v = -v := by
  rcases v with ⟨x, y⟩
  have htwo : (2 : ZMod 4).val = 2 := ZMod.val_cast_of_lt (by norm_num)
  ext <;> simp [q8Ipow, htwo, pow_succ, Complex.I_mul_I]

theorem q8Ipow_two_add (i : ZMod 4) (v : Q8Carrier) :
    q8Ipow ((2 : ZMod 4) + i) v = -q8Ipow i v := by
  rw [q8Ipow_add]
  exact q8Ipow_two_apply _

theorem deningerQ8GroupAction_one (v : Q8Carrier) :
    deningerQ8GroupAction (1 : QuaternionGroup 2) v = v := by
  change q8Ipow (0 : ZMod 4) v = v
  rcases v with ⟨x, y⟩
  have hzero : (0 : ZMod 4).val = 0 := by simp
  simp [q8Ipow, hzero]

/-- The action law for all eight quaternion-group elements. -/
theorem deningerQ8GroupAction_mul (g h : QuaternionGroup 2) (v : Q8Carrier) :
    deningerQ8GroupAction (g * h) v =
      deningerQ8GroupAction g (deningerQ8GroupAction h v) := by
  rcases g with i | i <;> rcases h with j | j
  · exact q8Ipow_add i j v
  · change deningerQuaternionTransitionK (q8Ipow (j - i) v) =
      q8Ipow i (deningerQuaternionTransitionK (q8Ipow j v))
    rw [q8Ipow_apply_K, ← q8Ipow_add]
    congr 2
    ring
  · change deningerQuaternionTransitionK (q8Ipow (i + j) v) =
      deningerQuaternionTransitionK (q8Ipow i (q8Ipow j v))
    rw [q8Ipow_add]
  · change q8Ipow ((2 : ZMod 4) + j - i) v =
      deningerQuaternionTransitionK (q8Ipow i
        (deningerQuaternionTransitionK (q8Ipow j v)))
    rw [q8Ipow_apply_K, ← q8Ipow_add, deningerQuaternionTransitionK_sq]
    have hindex : (2 : ZMod 4) + j - i = 2 + (-i + j) := by ring
    rw [hindex]
    exact q8Ipow_two_add (-i + j) v

def q8IpowLinear (i : ZMod 4) : Q8Carrier →ₗ[ℂ] Q8Carrier where
  toFun := q8Ipow i
  map_add' v w := by
    rcases v with ⟨x, y⟩
    rcases w with ⟨u, z⟩
    ext <;> simp [q8Ipow]
    all_goals ring
  map_smul' a v := by
    rcases v with ⟨x, y⟩
    ext <;> simp [q8Ipow]
    all_goals ring

def deningerQuaternionTransitionKLinear : Q8Carrier →ₗ[ℂ] Q8Carrier where
  toFun := deningerQuaternionTransitionK
  map_add' v w := by
    rcases v with ⟨x, y⟩
    rcases w with ⟨u, z⟩
    ext <;> simp [deningerQuaternionTransitionK]
    all_goals ring
  map_smul' a v := by
    rcases v with ⟨x, y⟩
    ext <;> simp [deningerQuaternionTransitionK]

def deningerQ8RepresentationLinear (g : QuaternionGroup 2) : Module.End ℂ Q8Carrier :=
  match g with
  | .a i => q8IpowLinear i
  | .xa i => deningerQuaternionTransitionKLinear.comp (q8IpowLinear i)

theorem deningerQ8RepresentationLinear_apply (g : QuaternionGroup 2) (v : Q8Carrier) :
    deningerQ8RepresentationLinear g v = deningerQ8GroupAction g v := by
  rcases g with i | i <;> rfl

/-- The explicit two-dimensional complex representation of the actual group
`QuaternionGroup 2`. -/
def deningerQ8Representation : QuaternionGroup 2 →* Module.End ℂ Q8Carrier where
  toFun := deningerQ8RepresentationLinear
  map_one' := by
    apply LinearMap.ext
    intro v
    change deningerQ8GroupAction (1 : QuaternionGroup 2) v = v
    exact deningerQ8GroupAction_one v
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    rw [Module.End.mul_apply, deningerQ8RepresentationLinear_apply,
      deningerQ8RepresentationLinear_apply, deningerQ8RepresentationLinear_apply]
    exact deningerQ8GroupAction_mul g h v

private theorem I_pow_mul_neg_I_pow (n : ℕ) :
    Complex.I ^ n * (-Complex.I) ^ n = 1 := by
  rw [← mul_pow]
  have h : Complex.I * -Complex.I = (1 : ℂ) := by
    calc
      Complex.I * -Complex.I = -(Complex.I * Complex.I) := by ring
      _ = 1 := by rw [Complex.I_mul_I]; norm_num
  rw [h, one_pow]

theorem q8Ipow_preserves_symplectic (i : ZMod 4) (p q : Q8Carrier) :
    deningerQ8TransitionSymplectic (q8Ipow i p) (q8Ipow i q) =
      deningerQ8TransitionSymplectic p q := by
  rcases p with ⟨x, y⟩
  rcases q with ⟨u, v⟩
  simp only [q8Ipow, deningerQ8TransitionSymplectic_apply]
  have hcoeff : Complex.I ^ i.val * (-Complex.I) ^ i.val = (1 : ℂ) :=
    I_pow_mul_neg_I_pow i.val
  calc
    Complex.I ^ i.val * x * ((-Complex.I) ^ i.val * v) -
        (-Complex.I) ^ i.val * y * (Complex.I ^ i.val * u) =
        (Complex.I ^ i.val * (-Complex.I) ^ i.val) * (x * v - y * u) := by ring
    _ = x * v - y * u := by rw [hcoeff, one_mul]

/-- Every group element preserves the standard nondegenerate alternating form. -/
theorem deningerQ8Representation_preserves_symplectic
    (g : QuaternionGroup 2) (p q : Q8Carrier) :
    deningerQ8TransitionSymplectic (deningerQ8Representation g p)
      (deningerQ8Representation g q) = deningerQ8TransitionSymplectic p q := by
  rcases g with i | i
  · exact q8Ipow_preserves_symplectic i p q
  · change deningerQ8TransitionSymplectic
      (deningerQuaternionTransitionK (q8Ipow i p))
      (deningerQuaternionTransitionK (q8Ipow i q)) = _
    rw [deningerQuaternionTransitionK_preserves_symplectic,
      q8Ipow_preserves_symplectic]

theorem deningerQ8Representation_a_one_apply (v : Q8Carrier) :
    deningerQ8Representation (QuaternionGroup.a 1) v =
      deningerQuaternionTransitionI v := by
  change deningerQ8RepresentationLinear (QuaternionGroup.a 1) v = _
  rw [deningerQ8RepresentationLinear_apply]
  rcases v with ⟨x, y⟩
  have hone : (1 : ZMod 4).val = 1 := ZMod.val_cast_of_lt (by norm_num)
  ext <;> simp [deningerQ8GroupAction, q8Ipow, hone, deningerQuaternionTransitionI]

theorem deningerQ8Representation_xa_zero_apply (v : Q8Carrier) :
    deningerQ8Representation (QuaternionGroup.xa 0) v =
      deningerQuaternionTransitionK v := by
  change deningerQ8RepresentationLinear (QuaternionGroup.xa 0) v = _
  rw [deningerQ8RepresentationLinear_apply]
  rcases v with ⟨x, y⟩
  simp [deningerQ8GroupAction, q8Ipow, deningerQuaternionTransitionK]

theorem deningerQ8Representation_central_apply (v : Q8Carrier) :
    deningerQ8Representation (QuaternionGroup.a 2) v = -v := by
  change deningerQ8RepresentationLinear (QuaternionGroup.a 2) v = _
  rw [deningerQ8RepresentationLinear_apply]
  exact q8Ipow_two_apply v

end

end RHTower
