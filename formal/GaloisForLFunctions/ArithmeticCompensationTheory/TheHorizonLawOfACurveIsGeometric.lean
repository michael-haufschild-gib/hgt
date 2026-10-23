import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Basic

/-!
# The horizon law of a curve is geometric

Over `F_q[T]` the reciprocal zeta function is a polynomial and the damped receiver collapses to a
constant (`ArithmeticContinuationAndCriticalEnergy.fqCenteredPrefix_eq`): the cancellation is
degenerate. A curve of genus `g` over `F_q` is the first non-degenerate calibration. Its degree-`n`
prime-power count is the point count

`N(n) = qⁿ + 1 − Re Σ_{i<2g} αᵢⁿ`,

with Frobenius eigenvalues `αᵢ`. This file builds the comb of such a model from the point counts
alone — the comb weight of degree `n` is `N(n) q^{−n/2}`, the analogue of `Λ(m) m^{−1/2}` — and
proves the comb laws, for every eigenvalue configuration of modulus at most `λ√q`:

* `abs_curveCombMass_sub_geometricMass_le`: the comb mass up to degree `D` is the geometric mass
  `Σ_{n ≤ D} q^{n/2}` up to `D + 2g Σ_{n ≤ D} λⁿ`;
* `abs_curveCombMass_sub_geometricMass_le_of_weil`: on the Weil circle, `λ = 1`, the error is at
  most `(2g + 1) D`;
* `abs_curveCombTail_sub_le_of_weil`: the **horizon law is geometric**: the fraction of the comb
  mass at depth at least `k` below the horizon `D` is `q^{−k/2}` up to `16(2g + 1)(D + 1)/q^{D/2}`.

So what replaces the exponential horizon law `e^{−u/2}` is its exact discretization at
`u = k log q`, and the error of the law is square-root small, `O(g D q^{−D/2})`, because the
eigenvalues lie on the circle `|α| = √q`; with eigenvalues of modulus `λ√q` the error grows like
`λ^D`. The rate of the horizon law is the width of the zero set. The bound `|αᵢ| ≤ √q` is Weil's
theorem for curves; here it is the defining property of the model class, and nothing is claimed
about point counts of actual curves.
-/

open Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticCompensationTheory

variable {m : ℕ}

/-- The degree-`n` point count of a curve model with Frobenius eigenvalues `α`:
`N(n) = qⁿ + 1 − Re Σᵢ αᵢⁿ`. -/
def curvePointCount (q : ℕ) (α : Fin m → ℂ) (n : ℕ) : ℝ :=
  (q : ℝ) ^ n + 1 - (∑ i, α i ^ n).re

/-- The comb mass of the curve model up to the degree horizon `D`: `Σ_{1 ≤ n ≤ D} N(n) q^{−n/2}`. -/
def curveCombMass (q : ℕ) (α : Fin m → ℂ) (D : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 D, curvePointCount q α n / Real.sqrt q ^ n

/-- The geometric mass `Σ_{1 ≤ n ≤ D} q^{n/2}`. -/
def geometricMass (q : ℕ) (D : ℕ) : ℝ := ∑ n ∈ Icc 1 D, Real.sqrt q ^ n

/-- The comb tail of the curve model: the fraction of the mass at depth at least `k` below `D`. -/
def curveCombTail (q : ℕ) (α : Fin m → ℂ) (D k : ℕ) : ℝ :=
  curveCombMass q α (D - k) / curveCombMass q α D

/-- **The comb mass of a curve model.** With all eigenvalues of modulus at most `λ√q`, the comb mass
is the geometric mass up to `D + m Σ_{n ≤ D} λⁿ`. -/
theorem abs_curveCombMass_sub_geometricMass_le {q : ℕ} (hq : 1 ≤ q) {α : Fin m → ℂ} {lam : ℝ}
    (hlam : 0 ≤ lam) (hα : ∀ i, ‖α i‖ ≤ lam * Real.sqrt q) (D : ℕ) :
    |curveCombMass q α D - geometricMass q D| ≤ D + m * ∑ n ∈ Icc 1 D, lam ^ n := by
  set s := Real.sqrt q
  have hs1 : 1 ≤ s := Real.le_sqrt_of_sq_le (by norm_num; exact_mod_cast hq)
  have hs0 : 0 < s := by linarith
  have hterm : ∀ n ∈ Icc 1 D, |curvePointCount q α n / s ^ n - s ^ n| ≤ 1 + m * lam ^ n := by
    intro n _
    have hsn : 0 < s ^ n := pow_pos hs0 n
    have hqn : (q : ℝ) ^ n = s ^ n * s ^ n := by
      rw [← mul_pow, Real.mul_self_sqrt (Nat.cast_nonneg q)]
    have he : curvePointCount q α n / s ^ n - s ^ n = (1 - (∑ i, α i ^ n).re) / s ^ n := by
      rw [curvePointCount, hqn]; field_simp; ring
    have hsum : |(∑ i, α i ^ n).re| ≤ m * (lam ^ n * s ^ n) := by
      refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
      calc ∑ i, ‖α i ^ n‖ ≤ ∑ _i : Fin m, lam ^ n * s ^ n := by
            refine sum_le_sum fun i _ => ?_
            rw [norm_pow, ← mul_pow]
            exact pow_le_pow_left₀ (norm_nonneg _) (hα i) n
        _ = m * (lam ^ n * s ^ n) := by simp
    have hone : 1 / s ^ n ≤ 1 := by rw [div_le_one hsn]; exact one_le_pow₀ hs1
    rw [he, abs_div, abs_of_pos hsn]
    calc |1 - (∑ i, α i ^ n).re| / s ^ n ≤ (1 + m * (lam ^ n * s ^ n)) / s ^ n := by
          refine div_le_div_of_nonneg_right ((abs_sub _ _).trans ?_) hsn.le
          rw [abs_one]; linarith
      _ = 1 / s ^ n + m * lam ^ n := by field_simp
      _ ≤ 1 + m * lam ^ n := by linarith
  calc |curveCombMass q α D - geometricMass q D|
      = |∑ n ∈ Icc 1 D, (curvePointCount q α n / s ^ n - s ^ n)| := by
        rw [curveCombMass, geometricMass, ← sum_sub_distrib]
    _ ≤ ∑ n ∈ Icc 1 D, (1 + m * lam ^ n) := (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
    _ = D + m * ∑ n ∈ Icc 1 D, lam ^ n := by
        rw [sum_add_distrib, ← mul_sum]; simp

/-- **On the Weil circle** the comb mass is the geometric mass up to `(m + 1) D`. -/
theorem abs_curveCombMass_sub_geometricMass_le_of_weil {q : ℕ} (hq : 1 ≤ q) {α : Fin m → ℂ}
    (hα : ∀ i, ‖α i‖ ≤ Real.sqrt q) (D : ℕ) :
    |curveCombMass q α D - geometricMass q D| ≤ (m + 1) * D := by
  have h := abs_curveCombMass_sub_geometricMass_le hq zero_le_one (lam := 1)
    (fun i => by rw [one_mul]; exact hα i) D
  simp only [one_pow, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one] at h
  linarith

/-- The geometric mass is `s(sᴰ − 1)/(s − 1)`, `s = √q`. -/
theorem geometricMass_mul {q : ℕ} (D : ℕ) :
    geometricMass q D * (Real.sqrt q - 1) = Real.sqrt q * (Real.sqrt q ^ D - 1) := by
  induction D with
  | zero => simp [geometricMass]
  | succ D ih =>
      rw [geometricMass, sum_Icc_succ_top (by omega), ← geometricMass, add_mul, ih]
      ring

/-- **The horizon law of a curve is geometric.** On the Weil circle, for `q ≥ 4`, every depth
`k ≤ D` carries the fraction `q^{−k/2}` of the comb mass up to `16(m + 1)(D + 1)/q^{D/2}`, once
`q^{D/2} ≥ 4(m + 1)(D + 1)`, which holds for all large `D`. -/
theorem abs_curveCombTail_sub_le_of_weil {q : ℕ} (hq : 4 ≤ q) {α : Fin m → ℂ}
    (hα : ∀ i, ‖α i‖ ≤ Real.sqrt q) {D k : ℕ} (hk : k ≤ D)
    (hD : 4 * ((m : ℝ) + 1) * ((D : ℝ) + 1) ≤ Real.sqrt q ^ D) :
    |curveCombTail q α D k - (Real.sqrt q ^ k)⁻¹| ≤
      16 * ((m : ℝ) + 1) * ((D : ℝ) + 1) / Real.sqrt q ^ D := by
  set s := Real.sqrt q
  have hs2 : 2 ≤ s := Real.le_sqrt_of_sq_le (by norm_num; exact_mod_cast hq)
  have hs0 : 0 < s := by linarith
  have hs1 : 0 < s - 1 := by linarith
  set c : ℝ := ((m : ℝ) + 1)
  have hc : 0 < c := by positivity
  set X := s ^ D
  have hX : 0 < X := pow_pos hs0 D
  have hsk : 0 < s ^ k := pow_pos hs0 k
  -- the geometric masses: `G(D) = s(X − 1)/(s − 1)`, `G(D − k) = s(X/s^k − 1)/(s − 1)`
  have hGD : geometricMass q D = s * (X - 1) / (s - 1) := by
    rw [eq_div_iff hs1.ne']; exact geometricMass_mul D
  have hXk : s ^ (D - k) = X / s ^ k := by
    rw [eq_div_iff hsk.ne', ← pow_add, Nat.sub_add_cancel hk]
  have hGDk : geometricMass q (D - k) = s * (X / s ^ k - 1) / (s - 1) := by
    rw [eq_div_iff hs1.ne', ← hXk]; exact geometricMass_mul (D - k)
  have hE1 := abs_curveCombMass_sub_geometricMass_le_of_weil (by omega) hα D
  have hE2 := abs_curveCombMass_sub_geometricMass_le_of_weil (by omega) hα (D - k)
  have hDk : ((D - k : ℕ) : ℝ) ≤ D := by exact_mod_cast Nat.sub_le D k
  set S := curveCombMass q α D
  set Sk := curveCombMass q α (D - k)
  -- `G(D) ≥ X/2` and the errors are at most `c (D + 1)`
  have hX4 : 4 ≤ X := by
    have h1 : (4 : ℝ) ≤ 4 * c * ((D : ℝ) + 1) := by
      have : (1 : ℝ) ≤ c := by simp only [c]; linarith [Nat.cast_nonneg (α := ℝ) m]
      have : (1 : ℝ) ≤ (D : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) D]
      nlinarith
    linarith
  have hGlow : X / 2 ≤ geometricMass q D := by
    rw [hGD, le_div_iff₀ hs1]
    nlinarith
  have hcD : c * ((D : ℝ) + 1) ≤ X / 4 := by
    have : 4 * c * ((D : ℝ) + 1) ≤ X := hD
    linarith
  have hSlow : X / 4 ≤ S := by
    have := (abs_le.mp hE1).1
    have : c * D ≤ c * ((D : ℝ) + 1) := by nlinarith
    linarith
  have hS0 : 0 < S := by linarith
  -- the exact geometric ratio `G(D − k) = G(D)/s^k − (1 − s^{−k}) s/(s − 1)`
  have hratio : geometricMass q (D - k) = geometricMass q D / s ^ k -
      (1 - (s ^ k)⁻¹) * (s / (s - 1)) := by
    rw [hGDk, hGD]; field_simp; ring
  have hsk1 : (s ^ k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  have hsk0 : 0 ≤ (s ^ k)⁻¹ := (inv_pos.mpr hsk).le
  have hss : s / (s - 1) ≤ 2 := by rw [div_le_iff₀ hs1]; linarith
  have hss0 : 0 ≤ s / (s - 1) := by positivity
  -- `Sk − S/s^k` is small
  have hnum : |Sk - S * (s ^ k)⁻¹| ≤ 2 * c * ((D : ℝ) + 1) + 2 := by
    have e : Sk - S * (s ^ k)⁻¹ = (Sk - geometricMass q (D - k)) -
        (S - geometricMass q D) * (s ^ k)⁻¹ - (1 - (s ^ k)⁻¹) * (s / (s - 1)) := by
      rw [hratio]; ring
    rw [e]
    have h1 : |(S - geometricMass q D) * (s ^ k)⁻¹| ≤ c * D := by
      rw [abs_mul, abs_of_nonneg hsk0]
      calc |S - geometricMass q D| * (s ^ k)⁻¹ ≤ c * D * 1 :=
            mul_le_mul hE1 hsk1 hsk0 (by positivity)
        _ = c * D := mul_one _
    have h2 : |(1 - (s ^ k)⁻¹) * (s / (s - 1))| ≤ 2 := by
      rw [abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg hss0]
      nlinarith
    have h3 : |Sk - geometricMass q (D - k)| ≤ c * D :=
      hE2.trans (mul_le_mul_of_nonneg_left hDk hc.le)
    calc |(Sk - geometricMass q (D - k)) - (S - geometricMass q D) * (s ^ k)⁻¹ -
          (1 - (s ^ k)⁻¹) * (s / (s - 1))|
        ≤ |Sk - geometricMass q (D - k)| + |(S - geometricMass q D) * (s ^ k)⁻¹| +
          |(1 - (s ^ k)⁻¹) * (s / (s - 1))| := by
          refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _)) le_rfl)
      _ ≤ c * D + c * D + 2 := by linarith
      _ ≤ 2 * c * ((D : ℝ) + 1) + 2 := by nlinarith
  have hfin : |Sk / S - (s ^ k)⁻¹| ≤ (2 * c * ((D : ℝ) + 1) + 2) / (X / 4) := by
    rw [show Sk / S - (s ^ k)⁻¹ = (Sk - S * (s ^ k)⁻¹) / S by field_simp, abs_div,
      abs_of_pos hS0]
    exact div_le_div₀ (by positivity) hnum (by positivity) hSlow
  calc |curveCombTail q α D k - (s ^ k)⁻¹| = |Sk / S - (s ^ k)⁻¹| := rfl
    _ ≤ (2 * c * ((D : ℝ) + 1) + 2) / (X / 4) := hfin
    _ ≤ 16 * c * ((D : ℝ) + 1) / X := by
        rw [div_div_eq_mul_div, div_le_div_iff_of_pos_right hX]
        have : (1 : ℝ) ≤ c * ((D : ℝ) + 1) := by
          have h1 : (1 : ℝ) ≤ c := by simp only [c]; linarith [Nat.cast_nonneg (α := ℝ) m]
          have h2 : (1 : ℝ) ≤ (D : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) D]
          nlinarith
        nlinarith

end GaloisForLFunctions.ArithmeticCompensationTheory
