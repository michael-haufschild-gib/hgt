import GaloisForLFunctions.RHTower.SqrtTwoNormEuclidean
import Mathlib.NumberTheory.Zsqrtd.ToReal
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Units and inert primes of `ℤ[√2]`

* The real embedding `emb a = a.re + a.im·√2` and its conjugate satisfy
  `emb a · emb ā = N(a)`.
* **Positive units.** Every unit `ε` with `emb ε > 0` is a power `u^k`, `k ∈ ℤ`, of
  `u = 1 + √2`. Proof: scale `ε` by a power of `u` into `[1, 1+√2)`. There the coordinates
  `(a, b)` satisfy `0 ≤ a, b ≤ 1` and `a² − 2b² = ±1`, which leaves only `1` and `u` itself.
* **Inert primes.** A rational prime `p ≡ 3, 5 (mod 8)` stays prime in `ℤ[√2]`. A proper factor
  would have norm `±p`, forcing `2` to be a square modulo `p`.
-/

namespace RHTower.SqrtTwo

open Zsqrtd

/-- The real embedding `a ↦ a.re + a.im·√2`. -/
noncomputable def emb : ℤ√2 →+* ℝ := Zsqrtd.toReal (by norm_num : (0 : ℤ) ≤ 2)

theorem emb_apply (a : ℤ√2) : emb a = a.re + a.im * Real.sqrt 2 := by
  simp [emb, Zsqrtd.toReal]

theorem emb_star (a : ℤ√2) : emb (star a) = a.re - a.im * Real.sqrt 2 := by
  rw [emb_apply]; simp; ring

theorem sqrt_two_sq : Real.sqrt 2 * Real.sqrt 2 = 2 :=
  Real.mul_self_sqrt (by norm_num)

theorem emb_mul_emb_star (a : ℤ√2) : emb a * emb (star a) = (a.norm : ℝ) := by
  rw [emb_apply, emb_star, Zsqrtd.norm_def]
  push_cast
  have h := sqrt_two_sq
  linear_combination (-(a.im : ℝ) * a.im) * h

theorem one_lt_sqrt_two : (1 : ℝ) < Real.sqrt 2 := by
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem sqrt_two_lt_three_halves : Real.sqrt 2 < 3 / 2 := by
  rw [show (3 / 2 : ℝ) = Real.sqrt (9 / 4) by
    rw [show (9 / 4 : ℝ) = (3 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- The fundamental unit `u = 1 + √2`. -/
def fundUnit : ℤ√2 := ⟨1, 1⟩

theorem norm_fundUnit : fundUnit.norm = -1 := by
  simp [fundUnit, Zsqrtd.norm_def]

theorem isUnit_fundUnit : IsUnit fundUnit :=
  Zsqrtd.norm_eq_one_iff.mp (by rw [norm_fundUnit]; rfl)

theorem emb_fundUnit : emb fundUnit = 1 + Real.sqrt 2 := by
  simp [emb_apply, fundUnit]

/-- A unit whose real embedding lies in `[1, 1+√2)` is `1`. -/
theorem eq_one_of_isUnit_of_mem_Ico {η : ℤ√2} (hη : IsUnit η) (h1 : 1 ≤ emb η)
    (h2 : emb η < 1 + Real.sqrt 2) : η = 1 := by
  have hN : η.norm.natAbs = 1 := Zsqrtd.norm_eq_one_iff.mpr hη
  have hN' : η.norm = 1 ∨ η.norm = -1 := by omega
  set a := η.re with ha
  set b := η.im with hb
  set s := Real.sqrt 2 with hs
  have hs2 := sqrt_two_sq
  have hs1 := one_lt_sqrt_two
  have hs3 := sqrt_two_lt_three_halves
  have hx : emb η = a + b * s := emb_apply η
  have hy : emb (star η) = a - b * s := emb_star η
  have hxy : emb η * emb (star η) = (η.norm : ℝ) := emb_mul_emb_star η
  -- `|emb η̄| ≤ 1`
  have hyabs : |emb (star η)| ≤ 1 := by
    have hnorm : |(η.norm : ℝ)| = 1 := by
      rcases hN' with h | h <;> rw [h] <;> norm_num
    have hpos : 0 < emb η := by linarith
    rw [← hxy, abs_mul, abs_of_pos hpos] at hnorm
    have : |emb (star η)| = 1 / emb η := by field_simp; linarith
    rw [this, div_le_one hpos]; exact h1
  have hy1 := abs_le.mp hyabs
  -- coordinate bounds
  have ha0 : (0 : ℝ) ≤ a := by nlinarith
  have ha1 : (a : ℝ) < 2 := by nlinarith
  have hb0 : (0 : ℝ) ≤ b * s := by nlinarith
  have hbs : (b : ℝ) * s < 2 := by nlinarith
  have hb0' : (0 : ℝ) ≤ b := by
    by_contra hneg
    rw [not_le] at hneg
    nlinarith
  have hb1 : (b : ℝ) < 2 := by nlinarith
  have ha0z : 0 ≤ a := by exact_mod_cast ha0
  have ha1z : a ≤ 1 := by
    have h' : a < 2 := by exact_mod_cast ha1
    omega
  have hb0z : 0 ≤ b := by exact_mod_cast hb0'
  have hb1z : b ≤ 1 := by
    have h' : b < 2 := by exact_mod_cast hb1
    omega
  have hnorm_ab : η.norm = a * a - 2 * b * b := by rw [Zsqrtd.norm_def]
  interval_cases a <;> interval_cases b
  · -- a = 0, b = 0: norm 0
    rw [hnorm_ab] at hN'; omega
  · rw [hnorm_ab] at hN'; omega
  · -- a = 1, b = 0
    ext <;> simp [← ha, ← hb]
  · -- a = 1, b = 1: η = u, excluded by `h2`
    exfalso; rw [hx] at h2; push_cast at h2; linarith

/-- The fundamental unit as an element of the unit group. -/
noncomputable def fundUnitU : (ℤ√2)ˣ := isUnit_fundUnit.unit

/-- The real embedding on units. -/
noncomputable def embU : (ℤ√2)ˣ →* ℝˣ := Units.map (emb : ℤ√2 →* ℝ)

theorem val_embU (V : (ℤ√2)ˣ) : ((embU V : ℝˣ) : ℝ) = emb (V : ℤ√2) := Units.coe_map _ V

theorem emb_zpow_fundUnitU (k : ℤ) :
    emb ((fundUnitU ^ k : (ℤ√2)ˣ) : ℤ√2) = (1 + Real.sqrt 2) ^ k := by
  rw [← val_embU, map_zpow, Units.val_zpow_eq_zpow_val, val_embU]
  simp [fundUnitU, emb_fundUnit]

/-- **Positive units are powers of `1 + √2`.** -/
theorem exists_zpow_eq_of_emb_pos (V : (ℤ√2)ˣ) (hpos : 0 < emb (V : ℤ√2)) :
    ∃ k : ℤ, V = fundUnitU ^ k := by
  set r : ℝ := 1 + Real.sqrt 2 with hr
  have hs1 := one_lt_sqrt_two
  have hr1 : 1 < r := by rw [hr]; linarith
  have hr0 : 0 < r := by linarith
  set x : ℝ := emb (V : ℤ√2) with hx
  -- `r ^ n ≥ n` for natural `n`
  have hpow_ge : ∀ n : ℕ, (n : ℝ) ≤ r ^ n := by
    intro n
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ Real.sqrt 2 by linarith) n
    rw [← hr] at h
    nlinarith
  have hbdd : ∃ b : ℤ, ∀ z : ℤ, r ^ z ≤ x → z ≤ b := by
    refine ⟨⌈x⌉₊, fun z hz => ?_⟩
    rcases le_or_gt z 0 with hz0 | hz0
    · have : (0 : ℤ) ≤ (⌈x⌉₊ : ℤ) := Int.natCast_nonneg _
      omega
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, z = n := ⟨z.toNat, (Int.toNat_of_nonneg hz0.le).symm⟩
      rw [zpow_natCast] at hz
      have h1 : (n : ℝ) ≤ x := (hpow_ge n).trans hz
      have h2 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
      have : (n : ℝ) ≤ (⌈x⌉₊ : ℝ) := h1.trans h2
      exact_mod_cast this
  have hne : ∃ z : ℤ, r ^ z ≤ x := by
    set n : ℕ := ⌈1 / x⌉₊ + 1 with hn
    refine ⟨-(n : ℤ), ?_⟩
    rw [zpow_neg, zpow_natCast]
    have hn1 : (1 / x) < (n : ℝ) := by
      rw [hn]; push_cast; linarith [Nat.le_ceil (1 / x)]
    have hnpos : (0 : ℝ) < n := by rw [hn]; positivity
    have hrn : (n : ℝ) ≤ r ^ n := hpow_ge n
    have hrnpos : 0 < r ^ n := pow_pos hr0 n
    rw [inv_le_comm₀ hrnpos hpos]
    have : 1 / x ≤ r ^ n := (hn1.le).trans hrn
    rwa [one_div] at this
  obtain ⟨k, hk, hkmax⟩ := Int.exists_greatest_of_bdd hbdd hne
  refine ⟨k, ?_⟩
  set η : (ℤ√2)ˣ := V * fundUnitU ^ (-k) with hη
  have hembη : emb (η : ℤ√2) = x * r ^ (-k) := by
    rw [hη, Units.val_mul, map_mul, emb_zpow_fundUnitU]
  have hrk : 0 < r ^ k := zpow_pos hr0 k
  have hlow : 1 ≤ emb (η : ℤ√2) := by
    rw [hembη, zpow_neg, ← div_eq_mul_inv, le_div_iff₀ hrk, one_mul]; exact hk
  have hhigh : emb (η : ℤ√2) < 1 + Real.sqrt 2 := by
    have hk1 : ¬ r ^ (k + 1) ≤ x := fun h => by have := hkmax (k + 1) h; omega
    rw [not_le, zpow_add_one₀ hr0.ne'] at hk1
    rw [hembη, zpow_neg, ← div_eq_mul_inv, div_lt_iff₀ hrk, ← hr]
    linarith
  have h1 : (η : ℤ√2) = 1 := eq_one_of_isUnit_of_mem_Ico η.isUnit hlow hhigh
  have h1' : η = 1 := Units.ext h1
  rw [hη] at h1'
  calc V = V * fundUnitU ^ (-k) * fundUnitU ^ k := by
        rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
    _ = fundUnitU ^ k := by rw [h1', one_mul]

/-- **Inert primes.** A rational prime `p ≡ 3, 5 (mod 8)` is irreducible in `ℤ[√2]`. -/
theorem irreducible_natCast_of_mod_eight {p : ℕ} [hp : Fact p.Prime]
    (h8 : p % 8 = 3 ∨ p % 8 = 5) : Irreducible (p : ℤ√2) := by
  have hp1 : 1 < p := hp.out.one_lt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  refine Irreducible.mk ?_ ?_
  · intro hu
    have h := Zsqrtd.norm_eq_one_iff.mpr hu
    rw [Zsqrtd.norm_natCast] at h
    have : (p * p : ℕ) = 1 := by
      exact_mod_cast (Int.natAbs_mul (p : ℤ) p ▸ h)
    nlinarith
  · intro a b hab
    have hN : a.norm.natAbs * b.norm.natAbs = p ^ 2 := by
      have := congrArg (fun z : ℤ√2 => z.norm.natAbs) hab
      simp only [Zsqrtd.norm_mul, Int.natAbs_mul, Zsqrtd.norm_natCast, Int.natAbs_natCast] at this
      rw [← this]; ring
    have hdvd : a.norm.natAbs ∣ p ^ 2 := ⟨_, hN.symm⟩
    obtain ⟨i, hi, hia⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
    interval_cases i
    · left; exact Zsqrtd.norm_eq_one_iff.mp (by simpa using hia)
    · exfalso
      rw [pow_one] at hia
      -- `a.re² − 2 a.im² = ±p`
      have hnorm : (p : ℤ) ∣ a.re * a.re - 2 * a.im * a.im := by
        rw [← Zsqrtd.norm_def]
        have h' : (p : ℤ) ∣ ((a.norm.natAbs : ℕ) : ℤ) := by rw [hia]
        exact Int.dvd_natAbs.mp h'
      have hz : ((a.re * a.re - 2 * a.im * a.im : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hnorm
      push_cast at hz
      by_cases him : ((a.im : ℤ) : ZMod p) = 0
      · rw [him] at hz
        have hre : ((a.re : ℤ) : ZMod p) = 0 := by
          have : ((a.re : ℤ) : ZMod p) * (a.re : ℤ) = 0 := by linear_combination hz
          exact mul_self_eq_zero.mp this
        obtain ⟨r, hr⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hre
        obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp him
        have hsq : ((p : ℤ) * p) ∣ a.re * a.re - 2 * a.im * a.im :=
          ⟨r * r - 2 * t * t, by rw [hr, ht]; ring⟩
        rw [← Zsqrtd.norm_def] at hsq
        have := Int.natAbs_dvd_natAbs.mpr hsq
        rw [Int.natAbs_mul, Int.natAbs_natCast, hia] at this
        have := Nat.le_of_dvd hp.out.pos this
        nlinarith
      · have hsq : IsSquare (2 : ZMod p) := by
          refine ⟨((a.re : ℤ) : ZMod p) / ((a.im : ℤ) : ZMod p), ?_⟩
          field_simp
          linear_combination -hz
        have := (ZMod.exists_sq_eq_two_iff hp2).mp hsq
        omega
    · right
      have hb1 : b.norm.natAbs = 1 := by
        rw [hia] at hN
        have hp2pos : 0 < p ^ 2 := by positivity
        have := Nat.eq_of_mul_eq_mul_left hp2pos (hN.trans (mul_one _).symm)
        exact this
      exact Zsqrtd.norm_eq_one_iff.mp hb1

/-- Inert rational primes are prime elements of `ℤ[√2]`. -/
theorem prime_natCast_of_mod_eight {p : ℕ} [Fact p.Prime] (h8 : p % 8 = 3 ∨ p % 8 = 5) :
    Prime (p : ℤ√2) :=
  (irreducible_natCast_of_mod_eight h8).prime

end RHTower.SqrtTwo
