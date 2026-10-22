import GaloisForLFunctions.RHTower.Deninger.DeningerKummerL2Inner
import GaloisForLFunctions.RHTower.Deninger.DeningerKummerSpace

/-!
# The `L²` inner product on the Kummer space `𝒢 ⊗ ℚ`

The form on the Kummer group is biadditive, so it is homogeneous under powers, and therefore
extends to the divisible hull by `⟨m/s, m'/s'⟩ = ⟨m, m'⟩/(s·s')`.  Well-definedness is exactly the
homogeneity in both arguments.

* `deningerKummerL2Inner_pow_left` : homogeneity in the first argument.
* `deningerKummerAddL2Inner` : the form written additively.
* `deningerSpaceL2Inner` : the extension to `𝒢 ⊗ ℚ`.
-/

namespace RHTower

open NumberField

section Homogeneity

variable {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]

/-- The form vanishes at the identity. -/
theorem deningerKummerL2Inner_one_left (y : deningerKummerGroup F) :
    deningerKummerL2Inner 1 y = 0 := by
  have h := deningerKummerL2Inner_mul_left (1 : deningerKummerGroup F) 1 y
  rw [mul_one] at h
  linarith

/-- **Homogeneity of the form under powers.** -/
theorem deningerKummerL2Inner_pow_left (x y : deningerKummerGroup F) (n : ℕ) :
    deningerKummerL2Inner (x ^ n) y = n * deningerKummerL2Inner x y := by
  induction n with
  | zero =>
    rw [pow_zero, deningerKummerL2Inner_one_left]
    simp
  | succ n ih =>
    rw [pow_succ, deningerKummerL2Inner_mul_left, ih]
    push_cast
    ring

/-- The form on the Kummer group written additively. -/
noncomputable def deningerKummerAddL2Inner (a b : deningerKummerAdd F) : ℝ :=
  deningerKummerL2Inner (Additive.toMul a) (Additive.toMul b)

theorem deningerKummerAddL2Inner_comm (a b : deningerKummerAdd F) :
    deningerKummerAddL2Inner a b = deningerKummerAddL2Inner b a :=
  deningerKummerL2Inner_comm _ _

theorem deningerKummerAddL2Inner_nsmul_left (a b : deningerKummerAdd F) (n : ℕ) :
    deningerKummerAddL2Inner (n • a) b = n * deningerKummerAddL2Inner a b :=
  deningerKummerL2Inner_pow_left (Additive.toMul a) (Additive.toMul b) n

theorem deningerKummerAddL2Inner_nsmul_right (a b : deningerKummerAdd F) (n : ℕ) :
    deningerKummerAddL2Inner a (n • b) = n * deningerKummerAddL2Inner a b := by
  rw [deningerKummerAddL2Inner_comm, deningerKummerAddL2Inner_nsmul_left,
    deningerKummerAddL2Inner_comm]

end Homogeneity

section SpaceInner

variable {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]

/-- **The `L²` inner product on the Kummer space** `𝒢 ⊗ ℚ`. -/
noncomputable def deningerSpaceL2Inner (x y : deningerKummerSpace F) : ℝ :=
  DivisibleHull.liftOn₂ x y
    (fun m s m' s' => deningerKummerAddL2Inner m m' / (((s : ℕ) : ℝ) * ((s' : ℕ) : ℝ))) <| by
    intro m n m' n' s t s' t' hms hnt
    have hm : (s' : ℕ) • m = (s : ℕ) • m' :=
      DivisibleHull.mk_eq_mk_iff_smul_eq_smul.mp hms
    have hn : (t' : ℕ) • n = (t : ℕ) • n' :=
      DivisibleHull.mk_eq_mk_iff_smul_eq_smul.mp hnt
    have hkey : deningerKummerAddL2Inner ((s' : ℕ) • m) ((t' : ℕ) • n)
        = deningerKummerAddL2Inner ((s : ℕ) • m') ((t : ℕ) • n') := by
      rw [hm, hn]
    rw [deningerKummerAddL2Inner_nsmul_left, deningerKummerAddL2Inner_nsmul_right,
      deningerKummerAddL2Inner_nsmul_left, deningerKummerAddL2Inner_nsmul_right] at hkey
    have hs : ((s : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr s.ne_zero
    have ht : ((t : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr t.ne_zero
    have hs' : ((s' : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr s'.ne_zero
    have ht' : ((t' : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr t'.ne_zero
    field_simp
    nlinarith [hkey]

@[simp] theorem deningerSpaceL2Inner_mk (m m' : deningerKummerAdd F) (s s' : ℕ+) :
    deningerSpaceL2Inner (DivisibleHull.mk m s) (DivisibleHull.mk m' s')
      = deningerKummerAddL2Inner m m' / (((s : ℕ) : ℝ) * ((s' : ℕ) : ℝ)) := rfl

theorem deningerSpaceL2Inner_comm (x y : deningerKummerSpace F) :
    deningerSpaceL2Inner x y = deningerSpaceL2Inner y x := by
  induction x using DivisibleHull.ind with
  | mk m s =>
    induction y using DivisibleHull.ind with
    | mk m' s' =>
      rw [deningerSpaceL2Inner_mk, deningerSpaceL2Inner_mk, deningerKummerAddL2Inner_comm,
        mul_comm (((s : ℕ) : ℝ))]

end SpaceInner

end RHTower
