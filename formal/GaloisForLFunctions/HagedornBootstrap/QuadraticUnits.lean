import GaloisForLFunctions.HagedornBootstrap.LetterCounting
import GaloisForLFunctions.CompactHyperbolicSurfaces.WallCrossing
import GaloisForLFunctions.RHTower.SqrtTwoUnitsAndInertPrimes
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# The Hagedorn and bootstrap constants are logarithms of quadratic units

Two constants of the weakly coupled and of the bootstrap side of holography are regulators of
real quadratic orders.

* **Free Hagedorn temperature.** `e^{β₀/2} = 2 + √3` is the fundamental unit of `ℤ[√3]`.
  Its powers are the Pell numbers: `e^{nβ₀/2} = xₙ + yₙ√3`, `cosh(nβ₀/2) = xₙ`,
  `sinh(nβ₀/2) = yₙ√3`, and `β₀/2 = arcosh 2`. A pair `(x, y) ∈ ℕ²` solves `x² − 3y² = 1`
  exactly when `x + y√3` is a Boltzmann weight `e^{nβ₀/2} = y_H^{-n}` at the free Hagedorn point.
* **Bootstrap tip.** The slit tip of the modular bootstrap is `x* = arsinh(1)/π`, and
  `arsinh 1 = log(1 + √2)` is the logarithm of the fundamental unit of `ℤ[√2]`; the positive units
  of `ℤ[√2]` are exactly the numbers `e^{kπx*}`, `k ∈ ℤ`.
-/

noncomputable section

open Real

namespace GaloisForLFunctions.HagedornBootstrap

/-! ### `ℤ[√3]` and the free Hagedorn point -/

private theorem a12 : 1 < 2 := by norm_num

theorem pell_xn_succ_three (n : ℕ) :
    (Pell.xn a12 (n + 1) : ℝ) = 2 * Pell.xn a12 n + 3 * Pell.yn a12 n := by
  have h : Pell.xn a12 (n + 1) = Pell.xn a12 n * 2 + 3 * Pell.yn a12 n := Pell.xn_succ a12 n
  rw [h]; push_cast; ring

theorem pell_yn_succ_three (n : ℕ) :
    (Pell.yn a12 (n + 1) : ℝ) = Pell.xn a12 n + 2 * Pell.yn a12 n := by
  rw [Pell.yn_succ]; push_cast; ring

/-- `(2 + √3)ⁿ = xₙ + yₙ√3`. -/
theorem two_add_sqrt_three_pow (n : ℕ) :
    (2 + √3) ^ n = Pell.xn a12 n + Pell.yn a12 n * √3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, pell_xn_succ_three, pell_yn_succ_three]
    linear_combination (Pell.yn a12 n : ℝ) * sqrt_three_sq

/-- `y_Hⁿ = (2 − √3)ⁿ = xₙ − yₙ√3`. -/
theorem hagedornY_pow (n : ℕ) :
    hagedornY ^ n = Pell.xn a12 n - Pell.yn a12 n * √3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, pell_xn_succ_three, pell_yn_succ_three]
    unfold hagedornY
    linear_combination (Pell.yn a12 n : ℝ) * sqrt_three_sq

/-- The Boltzmann weights `e^{nβ₀/2}` at the free Hagedorn temperature are `xₙ + yₙ√3`. -/
theorem exp_nat_mul_hagedornBeta_half (n : ℕ) :
    Real.exp (n * (hagedornBeta / 2)) = Pell.xn a12 n + Pell.yn a12 n * √3 := by
  rw [Real.exp_nat_mul, hagedornBeta_eq,
    show 2 * Real.log (2 + √3) / 2 = Real.log (2 + √3) by ring,
    Real.exp_log (by positivity), two_add_sqrt_three_pow]

theorem exp_neg_nat_mul_hagedornBeta_half (n : ℕ) :
    Real.exp (-(n * (hagedornBeta / 2))) = hagedornY ^ n := by
  rw [Real.exp_neg, ← Real.exp_neg, show -(↑n * (hagedornBeta / 2)) = n * (-(hagedornBeta / 2))
    by ring, Real.exp_nat_mul, exp_neg_hagedornBeta_half]

/-- `cosh(nβ₀/2) = xₙ`: the Pell `x`-coordinates are hyperbolic cosines at the Hagedorn point. -/
theorem cosh_nat_mul_hagedornBeta_half (n : ℕ) :
    Real.cosh (n * (hagedornBeta / 2)) = Pell.xn a12 n := by
  rw [Real.cosh_eq, exp_nat_mul_hagedornBeta_half, exp_neg_nat_mul_hagedornBeta_half,
    hagedornY_pow]
  ring

/-- `sinh(nβ₀/2) = yₙ√3`. -/
theorem sinh_nat_mul_hagedornBeta_half (n : ℕ) :
    Real.sinh (n * (hagedornBeta / 2)) = Pell.yn a12 n * √3 := by
  rw [Real.sinh_eq, exp_nat_mul_hagedornBeta_half, exp_neg_nat_mul_hagedornBeta_half,
    hagedornY_pow]
  ring

/-- `β₀/2 = arcosh 2`. -/
theorem arcosh_two : Real.arcosh 2 = hagedornBeta / 2 := by
  have h := cosh_nat_mul_hagedornBeta_half 1
  rw [Pell.xn_one] at h
  push_cast at h
  rw [one_mul] at h
  have hc := Real.arcosh_cosh (show 0 ≤ hagedornBeta / 2 by linarith [hagedornBeta_pos])
  rwa [h] at hc

/-- Integer points of `x + y√3` are determined by their real value. -/
theorem nat_eq_of_add_mul_sqrt_three_eq {x y x' y' : ℕ}
    (h : (x : ℝ) + y * √3 = x' + y' * √3) : x = x' ∧ y = y' := by
  have hirr : Irrational (√3) := by
    simpa using Nat.Prime.irrational_sqrt (p := 3) (by norm_num)
  have hy : y = y' := by
    by_contra hne
    have hne' : ((y : ℝ) - y') ≠ 0 := by
      intro h0; apply hne; exact_mod_cast (sub_eq_zero.mp h0)
    apply hirr
    refine ⟨((x' : ℚ) - x) / ((y : ℚ) - y'), ?_⟩
    push_cast
    field_simp
    linarith
  subst hy
  refine ⟨?_, rfl⟩
  have : (x : ℝ) = x' := by linarith
  exact_mod_cast this

/-- **Pell solutions are Hagedorn Boltzmann weights.** `x² = 1 + 3y²` in `ℕ` exactly when
`x + y√3 = e^{nβ₀/2}` for some `n`, the inverse `n`-th power of the free Hagedorn point. -/
theorem pell_three_iff_exp_hagedorn {x y : ℕ} :
    x * x = 1 + 3 * y * y ↔ ∃ n : ℕ, (x : ℝ) + y * √3 = Real.exp (n * (hagedornBeta / 2)) := by
  constructor
  · intro h
    obtain ⟨n, hx, hy⟩ := GaloisForLFunctions.CompactHyperbolicSurfaces.pell_three h
    exact ⟨n, by rw [exp_nat_mul_hagedornBeta_half, hx, hy]⟩
  · rintro ⟨n, hn⟩
    rw [exp_nat_mul_hagedornBeta_half] at hn
    obtain ⟨rfl, rfl⟩ := nat_eq_of_add_mul_sqrt_three_eq hn
    have h : Pell.xn a12 n * Pell.xn a12 n - 3 * Pell.yn a12 n * Pell.yn a12 n = 1 :=
      Pell.pell_eq a12 n
    omega

/-! ### `ℤ[√2]` and the bootstrap tip -/

open RHTower.SqrtTwo

/-- `arsinh 1 = log(1 + √2)`, the logarithm of the fundamental unit of `ℤ[√2]`. -/
theorem arsinh_one_eq_log_fundUnit : Real.arsinh 1 = Real.log (emb fundUnit) := by
  rw [emb_fundUnit, Real.arsinh]
  norm_num

/-- `cosh(arsinh 1) = √2`: the tip's partner value on the edge. -/
theorem cosh_arsinh_one : Real.cosh (Real.arsinh 1) = √2 := by
  rw [Real.cosh_arsinh]; norm_num

/-- The units of `ℤ[√2]` are the exponentials of integer multiples of `arsinh 1`. -/
theorem emb_zpow_fundUnitU_eq_exp (k : ℤ) :
    emb ((fundUnitU ^ k : (ℤ√2)ˣ) : ℤ√2) = Real.exp (k * Real.arsinh 1) := by
  have hpos : 0 < 1 + √2 := by positivity
  rw [emb_zpow_fundUnitU, arsinh_one_eq_log_fundUnit, emb_fundUnit, mul_comm,
    ← Real.rpow_def_of_pos hpos, Real.rpow_intCast]

/-- **Positive units of `ℤ[√2]` are `e^{k·arsinh 1}`.** -/
theorem exists_exp_eq_of_emb_pos (V : (ℤ√2)ˣ) (hpos : 0 < emb (V : ℤ√2)) :
    ∃ k : ℤ, emb (V : ℤ√2) = Real.exp (k * Real.arsinh 1) := by
  obtain ⟨k, rfl⟩ := exists_zpow_eq_of_emb_pos V hpos
  exact ⟨k, emb_zpow_fundUnitU_eq_exp k⟩

end GaloisForLFunctions.HagedornBootstrap
