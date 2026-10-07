import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Data.Rat.Cast.Order

/-!
# Positive-rational Steinberg relations have only a first-order quotient

For a multiplicative character of the nonzero rationals into a commutative ring where two
is invertible, positive complementary Steinberg relations force every product
`(χ q - 1) * (χ r - 1)` with positive rational `q,r` to vanish.

The proof uses finite ring identities. Scaled complementary relations first make every
natural generator unipotent. Factoring the relations at a rational and its square then
makes each natural augmentation generator square-zero; multiplicativity kills all mixed
products. Numerators and denominators finish the rational case. No global nilpotence,
Noetherian assumption, analytic logarithm, or convergence argument is used.
-/

namespace GaloisForLFunctions.HTGeometry.PositiveRationalSteinberg
variable {A : Type*} [CommRing A]

private theorem power_of_square_eq (x y : A) (h : x ^ 2 = x * y) (n : ℕ) :
    x ^ (n + 1) = x * y ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      x ^ (n + 1 + 1) = (x * y ^ n) * x := by rw [pow_succ, ih]
      _ = x ^ 2 * y ^ n := by ring
      _ = x * y ^ (n + 1) := by rw [h]; ring

variable (f : ℕ →* A)
variable (hrel : ∀ a b : ℕ, 0 < a → 0 < b →
  (f (a + b) - f a) * (f (a + b) - f b) = 0)

include hrel

private theorem natural_unipotent (n : ℕ) (hn : 0 < n) : (f n - 1) ^ n = 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n; simp
    have hn : 0 < n := by omega
    have hs := hrel n 1 hn (by omega)
    rw [map_one] at hs
    have he : (f (n + 1) - 1) ^ 2 = (f (n + 1) - 1) * (f n - 1) := by
      linear_combination hs
    rw [power_of_square_eq _ _ he, ih hn, mul_zero]

private theorem natural_square_zero (h2 : IsUnit (2 : A))
    (hunit : ∀ n : ℕ, 0 < n → IsUnit (f n)) (n : ℕ) (hn : 0 < n) :
    (f n - 1) ^ 2 = 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n; simp
    have hn : 0 < n := by omega
    have hprev := ih hn
    have hnext := hrel n 1 hn (by omega)
    rw [map_one] at hnext
    by_cases hn1 : n = 1
    · subst n; simpa [pow_two] using hnext
    have hnm : 0 < n - 1 := by omega
    have hbase := hrel (n - 1) 1 hnm (by omega)
    rw [show n - 1 + 1 = n by omega, map_one] at hbase
    have hsq := hrel 1 ((n - 1) * (n + 1)) (by omega) (Nat.mul_pos hnm (by omega))
    have harg : 1 + (n - 1) * (n + 1) = n * n := by
      have he : n - 1 + 1 = n := by omega
      nlinarith
    rw [harg, map_one, map_mul, map_mul] at hsq
    have hfactor : (f n + 1) * f (n - 1) *
        ((f n - 1) * (f n - f (n + 1))) = 0 := by
      linear_combination hsq - (f n + 1) * f n * hbase
    have hnil : IsNilpotent (f n - 1) := ⟨n, natural_unipotent f hrel n hn⟩
    have hplus : IsUnit (f n + 1) := by
      convert hnil.isUnit_add_right_of_commute h2 (Commute.all _ _) using 1; ring
    have hcancel := ((hplus.mul (hunit _ hnm)).mul_right_inj).mp
      (show (f n + 1) * f (n - 1) *
        ((f n - 1) * (f n - f (n + 1))) = (f n + 1) * f (n - 1) * 0 by
          simpa only [mul_zero] using hfactor)
    linear_combination hnext - hcancel + hprev

private theorem natural_products_zero (h2 : IsUnit (2 : A))
    (hunit : ∀ n : ℕ, 0 < n → IsUnit (f n))
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    (f n - 1) * (f m - 1) = 0 := by
  have hx := natural_square_zero f hrel h2 hunit n hn
  have hy := natural_square_zero f hrel h2 hunit m hm
  have hxy := natural_square_zero f hrel h2 hunit (n * m) (Nat.mul_pos hn hm)
  rw [map_mul] at hxy
  apply h2.mul_right_inj.mp
  change 2 * ((f n - 1) * (f m - 1)) = 2 * 0
  linear_combination hxy - (f m ^ 2) * hx - (2 * f n - 1) * hy

end GaloisForLFunctions.HTGeometry.PositiveRationalSteinberg

namespace GaloisForLFunctions.HTGeometry.PositiveRationalSteinberg
variable {A : Type*} [CommRing A]

private noncomputable def naturalCharacter (χ : ℚˣ →* A) : ℕ →* A where
  toFun n := if hn : n = 0 then 0 else χ (Units.mk0 (n : ℚ) (by exact_mod_cast hn))
  map_one' := by simp
  map_mul' n m := by
    by_cases hn : n = 0
    · subst n; simp
    by_cases hm : m = 0
    · subst m; simp
    simp only [dif_neg hn, dif_neg hm, dif_neg (Nat.mul_ne_zero hn hm)]
    rw [← map_mul]
    congr 1
    apply Units.ext
    simp

private theorem naturalCharacter_pos (χ : ℚˣ →* A) (n : ℕ) (hn : 0 < n) :
    naturalCharacter χ n = χ (Units.mk0 (n : ℚ) (by exact_mod_cast hn.ne')) := by
  simp [naturalCharacter, hn.ne']

private theorem positive_unit_image (χ : ℚˣ →* A) (q : ℚˣ) : IsUnit (χ q) :=
  (Group.isUnit q).map χ

private theorem naturalCharacter_relation (χ : ℚˣ →* A)
    (hSt : ∀ x y : ℚˣ, 0 < (x : ℚ) → 0 < (y : ℚ) → (x : ℚ) + (y : ℚ) = 1 →
      (χ x - 1) * (χ y - 1) = 0)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (naturalCharacter χ (a + b) - naturalCharacter χ a) *
      (naturalCharacter χ (a + b) - naturalCharacter χ b) = 0 := by
  let u : ℚˣ := Units.mk0 (a : ℚ) (by exact_mod_cast ha.ne')
  let v : ℚˣ := Units.mk0 (b : ℚ) (by exact_mod_cast hb.ne')
  let w : ℚˣ := Units.mk0 ((a + b : ℕ) : ℚ) (by exact_mod_cast (Nat.add_pos_left ha b).ne')
  have hwpos : 0 < (w : ℚ) := by dsimp [w]; exact_mod_cast (Nat.add_pos_left ha b)
  have hupos : 0 < (u : ℚ) := by dsimp [u]; exact_mod_cast ha
  have hvpos : 0 < (v : ℚ) := by dsimp [v]; exact_mod_cast hb
  have hxy : ((u / w : ℚˣ) : ℚ) + ((v / w : ℚˣ) : ℚ) = 1 := by
    change (a : ℚ) / (a + b : ℕ) + (b : ℚ) / (a + b : ℕ) = 1
    rw [← add_div]
    push_cast
    exact div_self (ne_of_gt (by positivity : (0 : ℚ) < a + b))
  have hs := hSt (u / w) (v / w) (div_pos hupos hwpos) (div_pos hvpos hwpos) hxy
  have hu : χ (u / w) * χ w = χ u := by rw [← map_mul]; simp
  have hv : χ (v / w) * χ w = χ v := by rw [← map_mul]; simp
  rw [naturalCharacter_pos χ (a + b) (Nat.add_pos_left ha b),
    naturalCharacter_pos χ a ha, naturalCharacter_pos χ b hb]
  change (χ w - χ u) * (χ w - χ v) = 0
  calc
    (χ w - χ u) * (χ w - χ v) = χ w ^ 2 * ((χ (u / w) - 1) * (χ (v / w) - 1)) := by
      rw [← hu, ← hv]; ring
    _ = 0 := by rw [hs, mul_zero]

private theorem rational_unit_as_natural_ratio (q : ℚˣ) (hq : 0 < (q : ℚ)) :
    ∃ n m : ℕ, 0 < n ∧ 0 < m ∧ (q : ℚ) * m = n := by
  refine ⟨(q : ℚ).num.natAbs, (q : ℚ).den, ?_, (q : ℚ).pos, ?_⟩
  · exact Int.natAbs_pos.mpr (Rat.num_pos.mpr hq).ne'
  · rw [Rat.mul_den_eq_num, ← Int.cast_natCast, Int.natAbs_of_nonneg (Rat.num_pos.mpr hq).le]

/-- Positive-rational Steinberg relations kill every pair of augmentation generators when two
is invertible. This conclusion requires no finiteness or completion hypothesis. -/
theorem positive_products_zero (χ : ℚˣ →* A) (h2 : IsUnit (2 : A))
    (hSt : ∀ x y : ℚˣ, 0 < (x : ℚ) → 0 < (y : ℚ) → (x : ℚ) + (y : ℚ) = 1 →
      (χ x - 1) * (χ y - 1) = 0)
    (q r : ℚˣ) (hq : 0 < (q : ℚ)) (hr : 0 < (r : ℚ)) :
    (χ q - 1) * (χ r - 1) = 0 := by
  obtain ⟨n, m, hn, hm, hqnm⟩ := rational_unit_as_natural_ratio q hq
  obtain ⟨p, t, hp, ht, hrpt⟩ := rational_unit_as_natural_ratio r hr
  let f := naturalCharacter χ
  have hunit (k : ℕ) (hk : 0 < k) : IsUnit (f k) := by
    rw [show f k = χ (Units.mk0 (k : ℚ) (by exact_mod_cast hk.ne')) from naturalCharacter_pos χ k hk]
    exact positive_unit_image χ _
  have hprod := natural_products_zero f (naturalCharacter_relation χ hSt) h2 hunit
  have hqmul : χ q * f m = f n := by
    rw [show f m = _ from naturalCharacter_pos χ m hm,
      show f n = _ from naturalCharacter_pos χ n hn, ← map_mul]
    congr 1
    apply Units.ext
    exact hqnm
  have hrmul : χ r * f t = f p := by
    rw [show f t = _ from naturalCharacter_pos χ t ht,
      show f p = _ from naturalCharacter_pos χ p hp, ← map_mul]
    congr 1
    apply Units.ext
    exact hrpt
  apply ((hunit m hm).mul (hunit t ht)).mul_left_inj.mp
  change ((χ q - 1) * (χ r - 1)) * (f m * f t) = 0 * (f m * f t)
  have hnp := hprod n p hn hp
  have hnt := hprod n t hn ht
  have hmp := hprod m p hm hp
  have hmt := hprod m t hm ht
  calc
    ((χ q - 1) * (χ r - 1)) * (f m * f t) =
        (χ q * f m - f m) * (χ r * f t - f t) := by ring
    _ = (f n - f m) * (f p - f t) := by rw [hqmul, hrmul]
    _ = 0 * (f m * f t) := by linear_combination hnp - hnt - hmp + hmt

end GaloisForLFunctions.HTGeometry.PositiveRationalSteinberg
