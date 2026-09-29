import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Rat.Floor

/-!
# `ℤ[√2]` is norm-Euclidean

For `x, y ∈ ℤ[√2]`, `y ≠ 0`, let `n = N(y) = y·ȳ` and round the two coordinates of `x·ȳ / n` to
the nearest integers. This gives `q` with remainder `r = x − yq` satisfying

```text
N(r)·N(y) = N(x·ȳ − n·q) = n²·(e₁² − 2e₂²),   |e₁|, |e₂| ≤ ½,
```

so `|N(r)| ≤ |N(y)|/2 < |N(y)|`. With the Euclidean function `|N|` this makes `ℤ[√2]` a Euclidean
domain, hence a principal ideal domain with unique factorization.
-/

namespace RHTower.SqrtTwo

open Zsqrtd

/-- `2` is not a square in `ℤ`. -/
theorem two_ne_mul_self (n : ℤ) : (2 : ℤ) ≠ n * n := by
  intro h
  rcases lt_trichotomy n 0 with hn | hn | hn
  · rcases le_or_gt n (-2) with h2 | h2
    · nlinarith
    · have : n = -1 := by omega
      subst this; norm_num at h
  · subst hn; norm_num at h
  · rcases le_or_gt 2 n with h2 | h2
    · nlinarith
    · have : n = 1 := by omega
      subst this; norm_num at h

theorem norm_eq_zero_iff (a : ℤ√2) : a.norm = 0 ↔ a = 0 :=
  Zsqrtd.norm_eq_zero two_ne_mul_self a

theorem norm_ne_zero {a : ℤ√2} (ha : a ≠ 0) : a.norm ≠ 0 :=
  fun h => ha ((norm_eq_zero_iff a).mp h)

instance : Div (ℤ√2) :=
  ⟨fun x y =>
    ⟨round (((x * star y).re : ℚ) / (y.norm : ℚ)), round (((x * star y).im : ℚ) / (y.norm : ℚ))⟩⟩

theorem div_def (x y : ℤ√2) :
    x / y = ⟨round (((x * star y).re : ℚ) / (y.norm : ℚ)),
      round (((x * star y).im : ℚ) / (y.norm : ℚ))⟩ := rfl

instance : Mod (ℤ√2) := ⟨fun x y => x - y * (x / y)⟩

theorem mod_def (x y : ℤ√2) : x % y = x - y * (x / y) := rfl

/-- The rounding estimate: the norm of `x·ȳ − N(y)·(x/y)` is at most `N(y)²/2`. -/
theorem two_mul_abs_norm_sub_le (x y : ℤ√2) :
    2 * |(x * star y - (y.norm : ℤ√2) * (x / y)).norm| ≤ y.norm * y.norm := by
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  have h0 : y.norm ≠ 0 := norm_ne_zero hy0
  have hq : x / y = ⟨round (((x * star y).re : ℚ) / (y.norm : ℚ)),
      round (((x * star y).im : ℚ) / (y.norm : ℚ))⟩ := div_def x y
  set c := x * star y with hc
  set n : ℤ := y.norm with hn
  set m₁ : ℤ := round ((c.re : ℚ) / (n : ℚ)) with hm₁
  set m₂ : ℤ := round ((c.im : ℚ) / (n : ℚ)) with hm₂
  have hsub : c - (n : ℤ√2) * (x / y) = ⟨c.re - n * m₁, c.im - n * m₂⟩ := by
    rw [hq]; ext <;> simp
  rw [hsub, Zsqrtd.norm_def]
  have hb₁ : |(c.re : ℚ) / n - m₁| ≤ 1 / 2 := abs_sub_round _
  have hb₂ : |(c.im : ℚ) / n - m₂| ≤ 1 / 2 := abs_sub_round _
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast h0
  set e₁ : ℚ := (c.re : ℚ) / n - m₁ with he₁
  set e₂ : ℚ := (c.im : ℚ) / n - m₂ with he₂
  have hs₁ : e₁ ^ 2 ≤ 1 / 4 := by nlinarith [abs_le.mp hb₁]
  have hs₂ : e₂ ^ 2 ≤ 1 / 4 := by nlinarith [abs_le.mp hb₂]
  have hr₁ : ((c.re - n * m₁ : ℤ) : ℚ) = n * e₁ := by
    rw [he₁]; push_cast; field_simp
  have hr₂ : ((c.im - n * m₂ : ℤ) : ℚ) = n * e₂ := by
    rw [he₂]; push_cast; field_simp
  have hn2 : 0 ≤ (n : ℚ) * n := mul_self_nonneg _
  have h1 := mul_le_mul_of_nonneg_left hs₁ hn2
  have h2 := mul_le_mul_of_nonneg_left hs₂ hn2
  have h3 : 0 ≤ (n : ℚ) * n * e₁ ^ 2 := mul_nonneg hn2 (sq_nonneg _)
  have h4 : 0 ≤ (n : ℚ) * n * e₂ ^ 2 := mul_nonneg hn2 (sq_nonneg _)
  have key : (2 : ℚ) * |(n * e₁) * (n * e₁) - 2 * (n * e₂) * (n * e₂)| ≤ n * n := by
    have habs : |(n * e₁) * (n * e₁) - 2 * (n * e₂) * (n * e₂)| ≤ (n : ℚ) * n / 2 := by
      rw [abs_le]; constructor <;> nlinarith
    linarith
  rw [← hr₁, ← hr₂] at key
  exact_mod_cast key

theorem natAbs_norm_mod_lt (x : ℤ√2) {y : ℤ√2} (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs := by
  have h0 := norm_ne_zero hy
  have hkey := two_mul_abs_norm_sub_le x y
  have hmul : x % y * star y = x * star y - (y.norm : ℤ√2) * (x / y) := by
    rw [mod_def, Zsqrtd.norm_eq_mul_conj]; ring
  have hN : (x % y * star y).norm = (x % y).norm * y.norm := by
    rw [Zsqrtd.norm_mul, Zsqrtd.norm_conj]
  rw [← hmul, hN, abs_mul] at hkey
  have hpos : 0 < |y.norm| := abs_pos.mpr h0
  have hyy : y.norm * y.norm = |y.norm| * |y.norm| := (abs_mul_abs_self _).symm
  rw [hyy] at hkey
  have h2 : 2 * |(x % y).norm| ≤ |y.norm| := by nlinarith [abs_nonneg (x % y).norm]
  zify
  linarith [abs_nonneg (x % y).norm]

theorem natAbs_norm_le_natAbs_norm_mul (a : ℤ√2) {b : ℤ√2} (hb : b ≠ 0) :
    a.norm.natAbs ≤ (a * b).norm.natAbs := by
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  have : 1 ≤ b.norm.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr (norm_ne_zero hb))
  exact Nat.le_mul_of_pos_right _ this

/-- `ℤ[√2]` is a Euclidean domain for the absolute norm. -/
instance instEuclideanDomain : EuclideanDomain (ℤ√2) :=
  { Zsqrtd.commRing, Zsqrtd.nontrivial with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := fun x => by simp [div_def]; rfl
    quotient_mul_add_remainder_eq := fun x y => by rw [mod_def]; ring
    r := fun a b => a.norm.natAbs < b.norm.natAbs
    r_wellFounded := (measure fun a : ℤ√2 => a.norm.natAbs).wf
    remainder_lt := fun x y hy => natAbs_norm_mod_lt x hy
    mul_left_not_lt := fun a b hb => not_lt_of_ge (natAbs_norm_le_natAbs_norm_mul a hb) }

end RHTower.SqrtTwo
