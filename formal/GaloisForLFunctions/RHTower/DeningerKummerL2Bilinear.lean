import GaloisForLFunctions.RHTower.DeningerKummerL2Definite

/-!
# `ℚ`-bilinearity of the `L²` form on the Kummer space

The form is additive and homogeneous under integer powers, hence under rational scalars on the
divisible hull: scaling by `q` scales the numerator by `q.num` and the denominator by `q.den`.
This makes it a `ℚ`-bilinear form on `𝒢 ⊗ ℚ` with values in `ℝ`.

* `deningerKummerL2Inner_zpow_left` : homogeneity under integer powers.
* `deningerSpaceL2Inner_qsmul_left` : homogeneity under rational scalars.
* `deningerSpaceL2Form` : the bundled `ℚ`-bilinear form.
-/

namespace RHTower

open NumberField

section IntegerHomogeneity

variable {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]

/-- The form negates under inversion. -/
theorem deningerKummerL2Inner_inv_left (x y : deningerKummerGroup F) :
    deningerKummerL2Inner x⁻¹ y = -deningerKummerL2Inner x y := by
  have h := deningerKummerL2Inner_mul_left x x⁻¹ y
  rw [mul_inv_cancel, deningerKummerL2Inner_one_left] at h
  linarith

/-- **Homogeneity under integer powers.** -/
theorem deningerKummerL2Inner_zpow_left (x y : deningerKummerGroup F) (k : ℤ) :
    deningerKummerL2Inner (x ^ k) y = k * deningerKummerL2Inner x y := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [zpow_natCast, deningerKummerL2Inner_pow_left]
    push_cast
    ring
  · rw [zpow_neg, zpow_natCast, deningerKummerL2Inner_inv_left,
      deningerKummerL2Inner_pow_left]
    push_cast
    ring

theorem deningerKummerAddL2Inner_zsmul_left (a b : deningerKummerAdd F) (k : ℤ) :
    deningerKummerAddL2Inner (k • a) b = k * deningerKummerAddL2Inner a b :=
  deningerKummerL2Inner_zpow_left (Additive.toMul a) (Additive.toMul b) k

end IntegerHomogeneity

section RationalHomogeneity

variable {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]

/-- **Homogeneity of the form under rational scalars.** -/
theorem deningerSpaceL2Inner_qsmul_left (q : ℚ) (x y : deningerKummerSpace F) :
    deningerSpaceL2Inner (q • x) y = (q : ℝ) * deningerSpaceL2Inner x y := by
  induction x using DivisibleHull.ind with
  | mk m s =>
    induction y using DivisibleHull.ind with
    | mk m' s' =>
      have hs : (0 : ℝ) < ((s : ℕ) : ℝ) := by exact_mod_cast s.pos
      have hs' : (0 : ℝ) < ((s' : ℕ) : ℝ) := by exact_mod_cast s'.pos
      have hd : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.den_pos
      rw [DivisibleHull.qsmul_mk, deningerSpaceL2Inner_mk, deningerSpaceL2Inner_mk,
        deningerKummerAddL2Inner_zsmul_left]
      simp only [PNat.mul_coe]
      rw [Rat.cast_def]
      push_cast
      field_simp
      rfl

/-- **The bundled `ℚ`-bilinear `L²` form on the Kummer space.** -/
noncomputable def deningerSpaceL2Form :
    deningerKummerSpace F →ₗ[ℚ] deningerKummerSpace F →ₗ[ℚ] ℝ where
  toFun x :=
    { toFun := fun y => deningerSpaceL2Inner x y
      map_add' := deningerSpaceL2Inner_add_right x
      map_smul' := fun q y => by
        rw [deningerSpaceL2Inner_comm, deningerSpaceL2Inner_qsmul_left,
          deningerSpaceL2Inner_comm y x]
        rfl }
  map_add' x x' := by
    ext y
    exact deningerSpaceL2Inner_add_left x x' y
  map_smul' q x := by
    ext y
    show deningerSpaceL2Inner (q • x) y = (q : ℝ) * deningerSpaceL2Inner x y
    exact deningerSpaceL2Inner_qsmul_left q x y

@[simp] theorem deningerSpaceL2Form_apply (x y : deningerKummerSpace F) :
    deningerSpaceL2Form x y = deningerSpaceL2Inner x y := rfl

end RationalHomogeneity

end RHTower
