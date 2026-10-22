import GaloisForLFunctions.RHTower.Deninger.DeningerKummerGroupNorm
import Mathlib.GroupTheory.DivisibleHull

/-!
# The Kummer space `𝒢 ⊗ ℚ` and its height norm

The Kummer group is torsion-free, so it embeds in its divisible hull, which is a `ℚ`-vector
space: this is `𝒢 ⊗ ℚ`.  The Weil height extends to it by `‖m/s‖ = ‖m‖/s`, and the extension is a
genuine norm which is homogeneous for the rational scalars.

* `deningerKummerGroup_isMulTorsionFree` : the Kummer group is torsion-free.
* `deningerKummerSpace` : the `ℚ`-vector space `𝒢 ⊗ ℚ`.
* `deningerKummerSpaceNorm` : the extended height, an `AddGroupNorm`.
* `deningerKummerSpaceNorm_qsmul` : rational homogeneity.
-/

namespace RHTower

open NumberField

section TorsionFree

variable {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]

omit [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F] in
/-- **The Kummer group has no torsion.**  A class of finite order is represented by a unit whose
power is torsion, hence which is itself torsion, hence which is the identity class. -/
theorem deningerKummerGroup_eq_one_of_isOfFinOrder {x : deningerKummerGroup F}
    (hfin : IsOfFinOrder x) : x = 1 := by
  induction x using QuotientGroup.induction_on with
  | H u =>
    obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
    have hmk : ((u ^ n : Fˣ) : deningerKummerGroup F) = (u : deningerKummerGroup F) ^ n :=
      map_pow (QuotientGroup.mk' (CommGroup.torsion Fˣ)) u n
    have h1 : ((u ^ n : Fˣ) : deningerKummerGroup F) = 1 := by
      rw [hmk]
      exact hpow
    obtain ⟨m, hm, hm2⟩ :=
      isOfFinOrder_iff_pow_eq_one.mp
        ((CommGroup.mem_torsion _).mp ((QuotientGroup.eq_one_iff _).mp h1))
    refine (QuotientGroup.eq_one_iff u).mpr ((CommGroup.mem_torsion u).mpr ?_)
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    rw [pow_mul, hm2]

instance deningerKummerGroup_isMulTorsionFree :
    IsMulTorsionFree (deningerKummerGroup F) where
  pow_left_injective {n} hn a b hab := by
    have hab' : a ^ n = b ^ n := hab
    have h : (a * b⁻¹) ^ n = 1 := by
      rw [mul_pow, inv_pow, hab', mul_inv_cancel]
    have h1 : a * b⁻¹ = 1 :=
      deningerKummerGroup_eq_one_of_isOfFinOrder
        (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn, h⟩)
    exact mul_inv_eq_one.mp h1

/-- The Kummer group written additively. -/
abbrev deningerKummerAdd (F : Type*) [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F] : Type _ :=
  Additive (deningerKummerGroup F)

instance deningerKummerAdd_isAddTorsionFree : IsAddTorsionFree (deningerKummerAdd F) where
  nsmul_right_injective {_n} hn _a _b hab :=
    IsMulTorsionFree.pow_left_injective (M := deningerKummerGroup F) hn hab

end TorsionFree

section KummerNormPow

variable {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]

/-- **The Kummer norm is homogeneous under powers.** -/
theorem deningerKummerNorm_pow (x : deningerKummerGroup F) (n : ℕ) :
    deningerKummerNorm (x ^ n) = n * deningerKummerNorm x := by
  induction x using QuotientGroup.induction_on with
  | H u =>
    have hmk : ((u ^ n : Fˣ) : deningerKummerGroup F) = (u : deningerKummerGroup F) ^ n :=
      map_pow (QuotientGroup.mk' (CommGroup.torsion Fˣ)) u n
    rw [← hmk, deningerKummerNorm_mk, deningerKummerNorm_mk, Units.val_pow_eq_pow_val,
      deningerAbsHeight_pow]

/-- The height as a function on the additive Kummer group. -/
noncomputable def deningerKummerAddNorm (a : deningerKummerAdd F) : ℝ :=
  deningerKummerNorm (Additive.toMul a)

theorem deningerKummerAddNorm_nsmul (a : deningerKummerAdd F) (n : ℕ) :
    deningerKummerAddNorm (n • a) = n * deningerKummerAddNorm a :=
  deningerKummerNorm_pow (Additive.toMul a) n

@[simp] theorem deningerKummerAddNorm_zero :
    deningerKummerAddNorm (0 : deningerKummerAdd F) = 0 :=
  (deningerKummerNorm (F := F)).map_one'

theorem deningerKummerAddNorm_add_le (a b : deningerKummerAdd F) :
    deningerKummerAddNorm (a + b) ≤ deningerKummerAddNorm a + deningerKummerAddNorm b :=
  map_mul_le_add (deningerKummerNorm (F := F)) (Additive.toMul a) (Additive.toMul b)

theorem deningerKummerAddNorm_neg (a : deningerKummerAdd F) :
    deningerKummerAddNorm (-a) = deningerKummerAddNorm a :=
  map_inv_eq_map (deningerKummerNorm (F := F)) (Additive.toMul a)

theorem deningerKummerAddNorm_eq_zero {a : deningerKummerAdd F}
    (ha : deningerKummerAddNorm a = 0) : a = 0 :=
  (deningerKummerNorm (F := F)).eq_one_of_map_eq_zero' _ ha

/-- **The Kummer norm is homogeneous under integer powers.** -/
theorem deningerKummerNorm_zpow (x : deningerKummerGroup F) (k : ℤ) :
    deningerKummerNorm (x ^ k) = (k.natAbs : ℝ) * deningerKummerNorm x := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [zpow_natCast, deningerKummerNorm_pow, Int.natAbs_natCast]
  · rw [zpow_neg, zpow_natCast, map_inv_eq_map, deningerKummerNorm_pow, Int.natAbs_neg,
      Int.natAbs_natCast]

theorem deningerKummerAddNorm_zsmul (a : deningerKummerAdd F) (k : ℤ) :
    deningerKummerAddNorm (k • a) = (k.natAbs : ℝ) * deningerKummerAddNorm a :=
  deningerKummerNorm_zpow (Additive.toMul a) k

end KummerNormPow

section KummerSpace

variable {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]

/-- **The Kummer space** `𝒢 ⊗ ℚ`: the divisible hull of the Kummer group, a `ℚ`-vector space. -/
abbrev deningerKummerSpace (F : Type*) [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F] : Type _ :=
  DivisibleHull (deningerKummerAdd F)

/-- The height on the Kummer space: `‖m/s‖ = ‖m‖/s`. -/
noncomputable def deningerKummerSpaceNormFun (x : deningerKummerSpace F) : ℝ :=
  DivisibleHull.liftOn x (fun m s => deningerKummerAddNorm m / (s : ℕ)) <| by
    intro m m' s s' h
    have hsm : (s' : ℕ) • m = (s : ℕ) • m' :=
      DivisibleHull.mk_eq_mk_iff_smul_eq_smul.mp h
    have hval := congrArg deningerKummerAddNorm hsm
    rw [deningerKummerAddNorm_nsmul, deningerKummerAddNorm_nsmul] at hval
    have hs : ((s : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr s.ne_zero
    have hs' : ((s' : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr s'.ne_zero
    field_simp
    linarith [hval]

@[simp] theorem deningerKummerSpaceNormFun_mk (m : deningerKummerAdd F) (s : ℕ+) :
    deningerKummerSpaceNormFun (DivisibleHull.mk m s) = deningerKummerAddNorm m / (s : ℕ) := rfl

theorem deningerKummerSpaceNormFun_add_le (x y : deningerKummerSpace F) :
    deningerKummerSpaceNormFun (x + y)
      ≤ deningerKummerSpaceNormFun x + deningerKummerSpaceNormFun y := by
  induction x using DivisibleHull.ind with
  | mk m s =>
    induction y using DivisibleHull.ind with
    | mk m' s' =>
      have hs : (0 : ℝ) < ((s : ℕ) : ℝ) := by exact_mod_cast s.pos
      have hs' : (0 : ℝ) < ((s' : ℕ) : ℝ) := by exact_mod_cast s'.pos
      rw [DivisibleHull.mk_add_mk, deningerKummerSpaceNormFun_mk,
        deningerKummerSpaceNormFun_mk, deningerKummerSpaceNormFun_mk]
      have hle := deningerKummerAddNorm_add_le ((s' : ℕ) • m) ((s : ℕ) • m')
      rw [deningerKummerAddNorm_nsmul, deningerKummerAddNorm_nsmul] at hle
      have hss : ((((s * s' : ℕ+)) : ℕ) : ℝ) = ((s : ℕ) : ℝ) * ((s' : ℕ) : ℝ) := by
        push_cast
        ring
      rw [hss, div_add_div _ _ (ne_of_gt hs) (ne_of_gt hs'),
        div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < ((s : ℕ) : ℝ) * ((s' : ℕ) : ℝ))]
      linarith [hle]

theorem deningerKummerSpaceNormFun_neg (x : deningerKummerSpace F) :
    deningerKummerSpaceNormFun (-x) = deningerKummerSpaceNormFun x := by
  induction x using DivisibleHull.ind with
  | mk m s =>
    rw [DivisibleHull.neg_mk, deningerKummerSpaceNormFun_mk, deningerKummerSpaceNormFun_mk,
      deningerKummerAddNorm_neg]

theorem deningerKummerSpaceNormFun_eq_zero {x : deningerKummerSpace F}
    (hx : deningerKummerSpaceNormFun x = 0) : x = 0 := by
  induction x using DivisibleHull.ind with
  | mk m s =>
    rw [deningerKummerSpaceNormFun_mk] at hx
    have hs : ((s : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr s.ne_zero
    have hm : deningerKummerAddNorm m = 0 := by
      rw [div_eq_zero_iff] at hx
      exact hx.resolve_right hs
    rw [deningerKummerAddNorm_eq_zero hm, DivisibleHull.mk_zero]

@[simp] theorem deningerKummerSpaceNormFun_zero :
    deningerKummerSpaceNormFun (0 : deningerKummerSpace F) = 0 := by
  rw [← DivisibleHull.mk_zero (M := deningerKummerAdd F) 1, deningerKummerSpaceNormFun_mk,
    deningerKummerAddNorm_zero, zero_div]

/-- **The height is a norm on the Kummer space.** -/
noncomputable def deningerKummerSpaceNorm : AddGroupNorm (deningerKummerSpace F) where
  toFun := deningerKummerSpaceNormFun
  map_zero' := deningerKummerSpaceNormFun_zero
  add_le' := deningerKummerSpaceNormFun_add_le
  neg' := deningerKummerSpaceNormFun_neg
  eq_zero_of_map_eq_zero' _ := deningerKummerSpaceNormFun_eq_zero

@[simp] theorem deningerKummerSpaceNorm_mk (m : deningerKummerAdd F) (s : ℕ+) :
    deningerKummerSpaceNorm (DivisibleHull.mk m s) = deningerKummerAddNorm m / (s : ℕ) := rfl

/-- **Rational homogeneity of the Kummer norm.** -/
theorem deningerKummerSpaceNorm_qsmul (q : ℚ) (x : deningerKummerSpace F) :
    deningerKummerSpaceNorm (q • x) = |q| * deningerKummerSpaceNorm x := by
  induction x using DivisibleHull.ind with
  | mk m s =>
    have hs : (0 : ℝ) < ((s : ℕ) : ℝ) := by exact_mod_cast s.pos
    have hdpos : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.den_pos
    rw [DivisibleHull.qsmul_mk, deningerKummerSpaceNorm_mk, deningerKummerSpaceNorm_mk,
      deningerKummerAddNorm_zsmul]
    have hq : ((|q| : ℚ) : ℝ) = (q.num.natAbs : ℝ) / (q.den : ℝ) := by
      rw [Rat.cast_abs, Rat.cast_def, abs_div, abs_of_pos hdpos]
      congr 1
      have hcast : ((q.num.natAbs : ℕ) : ℝ) = |(q.num : ℝ)| := by
        rw [← Int.cast_natCast, ← Int.abs_eq_natAbs, Int.cast_abs]
      rw [hcast]
    rw [hq]
    simp only [PNat.mul_coe]
    push_cast
    field_simp
    rfl

end KummerSpace

end RHTower
