import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.Group.Units.Hom

/-!
# Pointed multiplicative maps into a group with zero

Two elementary facts used to pass between characters and pointed multiplicative maps in a setting
where no addition is available.

* For commutative groups with zero, pointed multiplicative maps `G → H` are exactly the
  homomorphisms `Gˣ → Hˣ`, by extension by zero.
* If every element of a commutative group with zero `K` is a ratio `ι f / ι s` of elements of a
  monoid with zero `D` embedded in it, then a pointed multiplicative map `P : D → L` which vanishes
  only at `0` extends uniquely to `K`, by `ι f / ι s ↦ P f / P s`.
-/

namespace HTGeometry

universe u

section ExtendByZero

variable {G H : Type*} [CommGroupWithZero G] [CommGroupWithZero H]

open Classical in
/-- Extension by zero of a homomorphism of unit groups. -/
noncomputable def gwzExtendByZero (χ : Gˣ →* Hˣ) : G →*₀ H where
  toFun a := if h : a = 0 then 0 else (χ (Units.mk0 a h) : H)
  map_zero' := dif_pos rfl
  map_one' := by
    rw [dif_neg (one_ne_zero (α := G))]
    have : Units.mk0 (1 : G) one_ne_zero = 1 := Units.ext rfl
    rw [this, map_one, Units.val_one]
  map_mul' a b := by
    by_cases ha : a = 0
    · subst ha; simp
    by_cases hb : b = 0
    · subst hb; simp
    rw [dif_neg ha, dif_neg hb, dif_neg (mul_ne_zero ha hb)]
    have hmk : Units.mk0 (a * b) (mul_ne_zero ha hb) = Units.mk0 a ha * Units.mk0 b hb :=
      Units.ext rfl
    rw [hmk, map_mul, Units.val_mul]

open Classical in
@[simp] theorem gwzExtendByZero_apply_ne_zero (χ : Gˣ →* Hˣ) {a : G} (h : a ≠ 0) :
    gwzExtendByZero χ a = (χ (Units.mk0 a h) : H) := dif_neg h

/-- **Pointed multiplicative maps of commutative groups with zero are the homomorphisms of their
unit groups.** -/
noncomputable def gwzPointedEquivChar : (G →*₀ H) ≃ (Gˣ →* Hˣ) where
  toFun P :=
    { toFun := fun u => Units.mk0 (P (u : G)) (by
        intro hc
        have h1 : P ((u : G) * ((u⁻¹ : Gˣ) : G)) = 1 := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
        rw [map_mul, hc, zero_mul] at h1
        exact zero_ne_one h1)
      map_one' := Units.ext (by
        show P ((1 : Gˣ) : G) = 1
        rw [Units.val_one, map_one])
      map_mul' := fun a b => Units.ext (by
        show P ((a * b : Gˣ) : G) = P (a : G) * P (b : G)
        rw [Units.val_mul, map_mul]) }
  invFun χ := gwzExtendByZero χ
  left_inv P := by
    refine MonoidWithZeroHom.ext fun a => ?_
    by_cases ha : a = 0
    · subst ha
      rw [map_zero, map_zero]
    · rw [gwzExtendByZero_apply_ne_zero _ ha]
      rfl
  right_inv χ := by
    refine MonoidHom.ext fun u => Units.ext ?_
    have hu : (u : G) ≠ 0 := u.ne_zero
    show gwzExtendByZero χ (u : G) = ((χ u : Hˣ) : H)
    rw [gwzExtendByZero_apply_ne_zero _ hu,
      show Units.mk0 (u : G) hu = u from Units.ext rfl]

end ExtendByZero

section RatioExtend

variable {D K L : Type*} [CommMonoidWithZero D] [NoZeroDivisors D]
variable [CommGroupWithZero K] [CommGroupWithZero L]
variable (ι : D →*₀ K) (hι : Function.Injective ι)
variable (hratio : ∀ t : K, ∃ fs : D × D, fs.2 ≠ 0 ∧ t * ι fs.2 = ι fs.1)
variable (P : D →*₀ L) (hP : ∀ d : D, d ≠ 0 → P d ≠ 0)

omit [NoZeroDivisors D] in
include hι in
theorem gwz_map_ne_zero {d : D} (hd : d ≠ 0) : ι d ≠ 0 := fun hc =>
  hd (hι (by rw [hc, map_zero]))

omit [NoZeroDivisors D] in
include ι in
theorem gwz_one_ne_zero : (1 : D) ≠ 0 := fun h => by
  have hc := congrArg ι h
  rw [map_one, map_zero] at hc
  exact one_ne_zero hc

omit [NoZeroDivisors D] in
include hι hP in
/-- The ratio `P f / P s` does not depend on the chosen representation. -/
theorem gwzRatio_well_defined (t : K) (f s f' s' : D) (hs : s ≠ 0) (hs' : s' ≠ 0)
    (h : t * ι s = ι f) (h' : t * ι s' = ι f') :
    P f * (P s)⁻¹ = P f' * (P s')⁻¹ := by
  have hcross : ι (f * s') = ι (f' * s) := by
    rw [map_mul, map_mul, ← h, ← h']
    exact mul_right_comm t (ι s) (ι s')
  have hDeq : f * s' = f' * s := hι hcross
  have hPeq : P f * P s' = P f' * P s := by
    rw [← map_mul, ← map_mul, hDeq]
  have hPs : P s ≠ 0 := hP s hs
  have hPs' : P s' ≠ 0 := hP s' hs'
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff hPs hPs']
  exact hPeq

open Classical in
/-- The extension of `P` to `K` along the ratio presentation. -/
noncomputable def gwzRatioExtendFun (t : K) : L :=
  P (hratio t).choose.1 * (P (hratio t).choose.2)⁻¹

omit [NoZeroDivisors D] in
include hι hP in
theorem gwzRatioExtendFun_spec (t : K) (f s : D) (hs : s ≠ 0) (h : t * ι s = ι f) :
    gwzRatioExtendFun ι hratio P t = P f * (P s)⁻¹ := by
  obtain ⟨hs0, hspec⟩ := (hratio t).choose_spec
  exact gwzRatio_well_defined ι hι P hP t _ _ f s hs0 hs hspec h

include hι hP in
/-- **The unique pointed multiplicative extension.** -/
noncomputable def gwzRatioExtend : K →*₀ L where
  toFun := gwzRatioExtendFun ι hratio P
  map_zero' := by
    rw [gwzRatioExtendFun_spec ι hι hratio P hP 0 0 1 (gwz_one_ne_zero ι) (by simp), map_zero,
      zero_mul]
  map_one' := by
    rw [gwzRatioExtendFun_spec ι hι hratio P hP 1 1 1 (gwz_one_ne_zero ι) (by simp), map_one,
      inv_one, mul_one]
  map_mul' t t' := by
    obtain ⟨⟨f, s⟩, hs, hspec⟩ := hratio t
    obtain ⟨⟨f', s'⟩, hs', hspec'⟩ := hratio t'
    have hmul : t * t' * ι (s * s') = ι (f * f') := by
      rw [map_mul, map_mul, ← hspec, ← hspec']
      exact mul_mul_mul_comm t t' (ι s) (ι s')
    rw [gwzRatioExtendFun_spec ι hι hratio P hP (t * t') (f * f') (s * s')
        (mul_ne_zero hs hs') hmul,
      gwzRatioExtendFun_spec ι hι hratio P hP t f s hs hspec,
      gwzRatioExtendFun_spec ι hι hratio P hP t' f' s' hs' hspec',
      map_mul, map_mul, mul_inv]
    exact mul_mul_mul_comm (P f) (P f') (P s)⁻¹ (P s')⁻¹

include hι hP in
@[simp] theorem gwzRatioExtend_comp (d : D) : gwzRatioExtend ι hι hratio P hP (ι d) = P d := by
  show gwzRatioExtendFun ι hratio P (ι d) = P d
  rw [gwzRatioExtendFun_spec ι hι hratio P hP (ι d) d 1 (gwz_one_ne_zero ι) (by simp), map_one,
    inv_one, mul_one]

include hι hP in
/-- The extension is unique. -/
theorem gwzRatioExtend_unique (F : K →*₀ L) (hF : ∀ d : D, F (ι d) = P d) :
    F = gwzRatioExtend ι hι hratio P hP := by
  refine MonoidWithZeroHom.ext fun t => ?_
  obtain ⟨⟨f, s⟩, hs, hspec⟩ := hratio t
  have hPs : P s ≠ 0 := hP s hs
  have hFt : F t * P s = P f := by
    rw [← hF s, ← hF f, ← map_mul, hspec]
  show F t = gwzRatioExtendFun ι hratio P t
  rw [gwzRatioExtendFun_spec ι hι hratio P hP t f s hs hspec,
    ← div_eq_mul_inv, eq_div_iff hPs]
  exact hFt

end RatioExtend

end HTGeometry
