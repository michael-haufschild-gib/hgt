import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.LocallyIntegrable

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

* `curveCombEnergy_ge`, `exists_curveCombEnergy_ge`: the **comb of a curve is uniformly coercive**:
  for all large `D` and *every* test, `‖C_D F‖² ≥ (q^D/12) ∫F²`. The comb shifts by the bounded
  operator `τ_{log q}` and the geometric weights invert it,
  `q^{D/2} F(· + D log q) = G(·) − q^{−1/2} G(· − log q) + F` for the geometric comb `G`; over the
  integers the comb shifts continuously and its resolvent `(1 + 2∂)^{−1}` has no such bound.

So what replaces the exponential horizon law `e^{−u/2}` is its exact discretization at
`u = k log q`, and the error of the law is square-root small, `O(g D q^{−D/2})`, because the
eigenvalues lie on the circle `|α| = √q`; with eigenvalues of modulus `λ√q` the error grows like
`λ^D`. The rate of the horizon law is the width of the zero set. The bound `|αᵢ| ≤ √q` is Weil's
theorem for curves; here it is the defining property of the model class, and nothing is claimed
about point counts of actual curves.
-/

open Finset Filter Topology MeasureTheory

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

/-! ## The comb of a curve is uniformly coercive -/

/-- The comb weight at degree `n`, `N(n) q^{−n/2}`. -/
def curveCombWeight (q : ℕ) (α : Fin m → ℂ) (n : ℕ) : ℝ :=
  curvePointCount q α n / Real.sqrt q ^ n

/-- The comb of the curve model on a test: `C_D F(x) = Σ_{1≤n≤D} N(n) q^{−n/2} F(x + n log q)`, the
analogue of `Σ_p w_p F(x + log p)`. -/
def curveComb (q : ℕ) (α : Fin m → ℂ) (F : ℝ → ℝ) (D : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 D, curveCombWeight q α n * F (x + n * Real.log q)

/-- The raw comb energy `‖C_D F‖²`. -/
def curveCombEnergy (q : ℕ) (α : Fin m → ℂ) (F : ℝ → ℝ) (D : ℕ) : ℝ :=
  ∫ x, curveComb q α F D x ^ 2

/-- On the Weil circle each comb weight is `q^{n/2}` up to `m + 1`. -/
theorem abs_curveCombWeight_sub_le {q : ℕ} (hq : 1 ≤ q) {α : Fin m → ℂ}
    (hα : ∀ i, ‖α i‖ ≤ Real.sqrt q) (n : ℕ) :
    |curveCombWeight q α n - Real.sqrt q ^ n| ≤ m + 1 := by
  set s := Real.sqrt q
  have hs1 : 1 ≤ s := Real.le_sqrt_of_sq_le (by norm_num; exact_mod_cast hq)
  have hsn : 0 < s ^ n := pow_pos (by linarith) n
  have hqn : (q : ℝ) ^ n = s ^ n * s ^ n := by
    rw [← mul_pow, Real.mul_self_sqrt (Nat.cast_nonneg q)]
  have he : curveCombWeight q α n - s ^ n = (1 - (∑ i, α i ^ n).re) / s ^ n := by
    rw [curveCombWeight, curvePointCount, hqn]; field_simp; ring
  have hsum : |(∑ i, α i ^ n).re| ≤ m * s ^ n := by
    refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
    calc ∑ i, ‖α i ^ n‖ ≤ ∑ _i : Fin m, s ^ n := by
          refine sum_le_sum fun i _ => ?_
          rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hα i) n
      _ = m * s ^ n := by simp
  rw [he, abs_div, abs_of_pos hsn, div_le_iff₀ hsn]
  have h1 : |1 - (∑ i, α i ^ n).re| ≤ 1 + m * s ^ n := by
    refine (abs_sub _ _).trans ?_; rw [abs_one]; linarith
  have h2 : 1 ≤ s ^ n := one_le_pow₀ hs1
  nlinarith

/-- **The comb of a curve is uniformly coercive.** On the Weil circle, for every continuous
compactly supported test and every horizon `D`,
`‖C_D F‖² ≥ ((q^D − 3)/(6(1 + 1/q)) − D²(m + 1)²) ∫F²`. -/
theorem curveCombEnergy_ge {q : ℕ} (hq : 2 ≤ q) {α : Fin m → ℂ}
    (hα : ∀ i, ‖α i‖ ≤ Real.sqrt q) {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (D : ℕ) :
    (((q : ℝ) ^ D - 3) / (6 * (1 + 1 / (q : ℝ))) - (D : ℝ) ^ 2 * ((m : ℝ) + 1) ^ 2) *
      ∫ x, F x ^ 2 ≤ curveCombEnergy q α F D := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  set s := Real.sqrt q
  have hs1 : 1 ≤ s := Real.le_sqrt_of_sq_le (by norm_num; exact_mod_cast (show 1 ≤ q by omega))
  have hs0 : 0 < s := by linarith
  have hss : s * s = q := Real.mul_self_sqrt hq0.le
  set L := Real.log q
  set I := ∫ x, F x ^ 2
  have hI0 : 0 ≤ I := integral_nonneg fun x => sq_nonneg _
  -- translates of `F` and of `F²` are integrable
  have htr : ∀ c : ℝ, Continuous fun x => F (x + c) := fun c =>
    hF.comp (continuous_id.add continuous_const)
  have hsqi : ∀ c : ℝ, Integrable fun x => F (x + c) ^ 2 := by
    intro c
    have hcs : HasCompactSupport fun x => F (x + c) := hFc.comp_homeomorph (Homeomorph.addRight c)
    have hcs2 : HasCompactSupport fun x => F (x + c) ^ 2 :=
      hcs.comp_left (g := fun y : ℝ => y ^ 2) (zero_pow two_ne_zero)
    exact ((htr c).pow 2).integrable_of_hasCompactSupport hcs2
  have hsqint : ∀ c : ℝ, ∫ x, F (x + c) ^ 2 = I := fun c =>
    integral_add_right_eq_self (fun x => F x ^ 2) c
  -- a finite combination of translates has square at most `(Σ a²)(Σ F²)`, hence is integrable
  have hcomb : ∀ a : ℕ → ℝ, Integrable fun x => (∑ n ∈ Icc 1 D, a n * F (x + n * L)) ^ 2 := by
    intro a
    have hdom : Integrable fun x => (∑ n ∈ Icc 1 D, a n ^ 2) *
        ∑ n ∈ Icc 1 D, F (x + n * L) ^ 2 :=
      (integrable_finsetSum (Icc 1 D) fun (n : ℕ) _ => hsqi ((n : ℝ) * L)).const_mul _
    refine hdom.mono' ?_ (Eventually.of_forall fun x => ?_)
    · exact ((continuous_finsetSum _ fun n _ => continuous_const.mul (htr _)).pow 2)
        |>.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  -- the geometric comb `G₀ = Σ sⁿ F(· + nL)` and the error comb `G₁`
  set G₀ : ℝ → ℝ := fun x => ∑ n ∈ Icc 1 D, s ^ n * F (x + n * L)
  set G₁ : ℝ → ℝ := fun x => ∑ n ∈ Icc 1 D, (curveCombWeight q α n - s ^ n) * F (x + n * L)
  have hG : ∀ x, curveComb q α F D x = G₀ x + G₁ x := fun x => by
    simp only [curveComb, G₀, G₁, ← sum_add_distrib]
    exact sum_congr rfl fun n _ => by ring
  have hG₀i : Integrable fun x => G₀ x ^ 2 := hcomb _
  have hG₁i : Integrable fun x => G₁ x ^ 2 := hcomb _
  have hGi : Integrable fun x => curveComb q α F D x ^ 2 := hcomb _
  -- the inversion `s^D F(x + DL) = G₀(x) − G₀(x − L)/s + F(x)`
  have hinv : ∀ x, s ^ D * F (x + D * L) = G₀ x - G₀ (x - L) / s + F x := by
    intro x
    rcases Nat.eq_zero_or_pos D with rfl | hD
    · simp [G₀]
    have hshift : G₀ (x - L) / s = F x + ∑ n ∈ Icc 1 (D - 1), s ^ n * F (x + n * L) := by
      simp only [G₀]
      rw [sum_div]
      have hre : ∀ n ∈ Icc 1 D, s ^ n * F (x - L + n * L) / s =
          s ^ (n - 1) * F (x + ((n - 1 : ℕ) : ℝ) * L) := by
        intro n hn
        have hn1 := (mem_Icc.mp hn).1
        rw [show x - L + n * L = x + ((n - 1 : ℕ) : ℝ) * L by push_cast [hn1]; ring]
        rw [show s ^ n = s ^ (n - 1) * s by rw [← pow_succ, Nat.sub_add_cancel hn1]]
        field_simp
      rw [sum_congr rfl hre]
      have hD1 : Icc 1 D = insert 1 (Icc 2 D) := by
        ext k; simp only [mem_Icc, mem_insert]; omega
      rw [hD1, sum_insert (by simp)]
      simp only [Nat.sub_self, pow_zero, one_mul, Nat.cast_zero, zero_mul, add_zero]
      congr 1
      refine sum_nbij' (fun n => n - 1) (fun n => n + 1) ?_ ?_ ?_ ?_ ?_
      · intro n hn; simp only [mem_Icc] at hn ⊢; omega
      · intro n hn; simp only [mem_Icc] at hn ⊢; omega
      · intro n hn; simp only [mem_Icc] at hn; omega
      · intro n hn; simp only [mem_Icc] at hn; omega
      · intro n hn; rfl
    have htop : G₀ x = ∑ n ∈ Icc 1 (D - 1), s ^ n * F (x + n * L) + s ^ D * F (x + D * L) := by
      simp only [G₀]
      rw [show Icc 1 D = insert D (Icc 1 (D - 1)) by
        ext k; simp only [mem_Icc, mem_insert]; omega, sum_insert (by simp; omega)]
      ring
    rw [hshift, htop]; ring
  -- integrate the squared inversion
  have hlow₀ : (s ^ D) ^ 2 * I ≤ 3 * (1 + 1 / (q : ℝ)) * (∫ x, G₀ x ^ 2) + 3 * I := by
    have hpt : ∀ x, (s ^ D * F (x + D * L)) ^ 2 ≤
        3 * (G₀ x ^ 2 + G₀ (x - L) ^ 2 / (q : ℝ) + F x ^ 2) := by
      intro x
      rw [hinv x]
      have : G₀ (x - L) ^ 2 / (q : ℝ) = (G₀ (x - L) / s) ^ 2 := by
        rw [div_pow, sq s, hss]
      rw [this]
      nlinarith [sq_nonneg (G₀ x - G₀ (x - L) / s), sq_nonneg (G₀ x - F x),
        sq_nonneg (G₀ (x - L) / s + F x)]
    have hshi : Integrable fun x => G₀ (x - L) ^ 2 := by
      simpa [sub_eq_add_neg] using hG₀i.comp_add_right (-L)
    have hFi : Integrable fun x => F x ^ 2 := by simpa using hsqi 0
    have h12 : Integrable fun x => G₀ x ^ 2 + G₀ (x - L) ^ 2 / (q : ℝ) :=
      hG₀i.add (hshi.div_const (q : ℝ))
    have h123 : Integrable fun x => G₀ x ^ 2 + G₀ (x - L) ^ 2 / (q : ℝ) + F x ^ 2 := h12.add hFi
    have hlhs : Integrable fun x => (s ^ D) ^ 2 * F (x + D * L) ^ 2 :=
      (hsqi (D * L)).const_mul _
    have hint : ∫ x, (s ^ D) ^ 2 * F (x + D * L) ^ 2 ≤
        ∫ x, 3 * (G₀ x ^ 2 + G₀ (x - L) ^ 2 / (q : ℝ) + F x ^ 2) :=
      integral_mono hlhs (h123.const_mul 3) fun x => by
        simp only; rw [← mul_pow]; exact hpt x
    rw [integral_const_mul, integral_const_mul, integral_add h12 hFi,
      integral_add hG₀i (hshi.div_const _), integral_div, hsqint] at hint
    have hsh : ∫ x, G₀ (x - L) ^ 2 = ∫ x, G₀ x ^ 2 := by
      simpa [sub_eq_add_neg] using integral_add_right_eq_self (fun x => G₀ x ^ 2) (-L)
    rw [hsh] at hint
    calc (s ^ D) ^ 2 * I ≤ 3 * ((∫ x, G₀ x ^ 2) + (∫ x, G₀ x ^ 2) / q + I) := hint
      _ = 3 * (1 + 1 / (q : ℝ)) * (∫ x, G₀ x ^ 2) + 3 * I := by ring
  -- the error comb is small: `‖G₁‖² ≤ D²(m + 1)² ∫F²`
  have hG₁ : ∫ x, G₁ x ^ 2 ≤ (D : ℝ) ^ 2 * ((m : ℝ) + 1) ^ 2 * I := by
    have hcs : ∀ x, G₁ x ^ 2 ≤ ((D : ℝ) * ((m : ℝ) + 1) ^ 2) * ∑ n ∈ Icc 1 D, F (x + n * L) ^ 2 := by
      intro x
      refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans
        (mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun _ _ => sq_nonneg _))
      calc ∑ n ∈ Icc 1 D, (curveCombWeight q α n - s ^ n) ^ 2
          ≤ ∑ _n ∈ Icc 1 D, ((m : ℝ) + 1) ^ 2 := sum_le_sum fun n _ => by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _)
              (abs_curveCombWeight_sub_le (by omega) hα n) 2
        _ = (D : ℝ) * ((m : ℝ) + 1) ^ 2 := by simp
    have hsumF : Integrable fun x => ∑ n ∈ Icc 1 D, F (x + n * L) ^ 2 :=
      integrable_finsetSum (Icc 1 D) fun (n : ℕ) _ => hsqi ((n : ℝ) * L)
    have hint : ∫ x, G₁ x ^ 2 ≤ ∫ x, ((D : ℝ) * ((m : ℝ) + 1) ^ 2) *
        ∑ n ∈ Icc 1 D, F (x + n * L) ^ 2 :=
      integral_mono hG₁i (hsumF.const_mul _) hcs
    rw [integral_const_mul, integral_finsetSum (Icc 1 D)
      fun (n : ℕ) _ => hsqi ((n : ℝ) * L)] at hint
    simp only [hsqint, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at hint
    calc ∫ x, G₁ x ^ 2 ≤ (D : ℝ) * ((m : ℝ) + 1) ^ 2 * ((D : ℝ) * I) := hint
      _ = (D : ℝ) ^ 2 * ((m : ℝ) + 1) ^ 2 * I := by ring
  -- `‖C_D F‖² ≥ ‖G₀‖²/2 − ‖G₁‖²`
  have hsplit : (∫ x, G₀ x ^ 2) / 2 - ∫ x, G₁ x ^ 2 ≤ curveCombEnergy q α F D := by
    have hpt : ∀ x, G₀ x ^ 2 / 2 - G₁ x ^ 2 ≤ curveComb q α F D x ^ 2 := fun x => by
      rw [hG x]; nlinarith [sq_nonneg (G₀ x + 2 * G₁ x)]
    have hdi : Integrable fun x => G₀ x ^ 2 / 2 - G₁ x ^ 2 := (hG₀i.div_const 2).sub hG₁i
    have h : ∫ x, (G₀ x ^ 2 / 2 - G₁ x ^ 2) ≤ ∫ x, curveComb q α F D x ^ 2 :=
      integral_mono hdi hGi hpt
    rwa [integral_sub (hG₀i.div_const 2) hG₁i, integral_div] at h
  have hsD : (s ^ D) ^ 2 = (q : ℝ) ^ D := by rw [← pow_mul, mul_comm, pow_mul, sq, hss]
  have hc : 0 < 6 * (1 + 1 / (q : ℝ)) := by positivity
  have hG₀low : ((q : ℝ) ^ D - 3) / (3 * (1 + 1 / (q : ℝ))) * I ≤ ∫ x, G₀ x ^ 2 := by
    rw [hsD] at hlow₀
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith
  calc (((q : ℝ) ^ D - 3) / (6 * (1 + 1 / (q : ℝ))) - (D : ℝ) ^ 2 * ((m : ℝ) + 1) ^ 2) * I
      = ((q : ℝ) ^ D - 3) / (3 * (1 + 1 / (q : ℝ))) * I / 2 -
          (D : ℝ) ^ 2 * ((m : ℝ) + 1) ^ 2 * I := by field_simp; ring
    _ ≤ (∫ x, G₀ x ^ 2) / 2 - ∫ x, G₁ x ^ 2 := by linarith
    _ ≤ curveCombEnergy q α F D := hsplit

/-- **Uniform coercivity at large horizons.** On the Weil circle there is `D₀` such that for every
`D ≥ D₀` and every continuous compactly supported test, `‖C_D F‖² ≥ (q^D/12) ∫F²`. -/
theorem exists_curveCombEnergy_ge {q : ℕ} (hq : 2 ≤ q) {α : Fin m → ℂ}
    (hα : ∀ i, ‖α i‖ ≤ Real.sqrt q) :
    ∃ D₀ : ℕ, ∀ D, D₀ ≤ D → ∀ F : ℝ → ℝ, Continuous F → HasCompactSupport F →
      (q : ℝ) ^ D / 12 * ∫ x, F x ^ 2 ≤ curveCombEnergy q α F D := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  -- `D²/q^D → 0` and `3/q^D → 0`
  have h1 := (tendsto_pow_const_div_const_pow_of_one_lt 2 hq1).const_mul (((m : ℝ) + 1) ^ 2)
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : (0 : ℝ) ≤ 1 / q)
    ((div_lt_one (by linarith)).mpr hq1)).const_mul 3
  rw [mul_zero] at h1 h2
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.mp ((h1.eventually (eventually_le_nhds
    (by norm_num : (0 : ℝ) < 1 / 72))).and (h2.eventually (eventually_le_nhds
    (by norm_num : (0 : ℝ) < 1 / 8))))
  refine ⟨D₀, fun D hD F hF hFc => ?_⟩
  obtain ⟨hD1, hD2⟩ := hD₀ D hD
  have hqD : 0 < (q : ℝ) ^ D := by positivity
  have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun x => sq_nonneg _
  refine le_trans (mul_le_mul_of_nonneg_right ?_ hI0) (curveCombEnergy_ge hq hα hF hFc D)
  -- `(q^D − 3)/(6(1 + 1/q)) − D²(m+1)² ≥ q^D/12`
  have hm2 : ((m : ℝ) + 1) ^ 2 * ((D : ℝ) ^ 2 / (q : ℝ) ^ D) ≤ 1 / 72 := hD1
  have h3 : 3 * (1 / (q : ℝ)) ^ D ≤ 1 / 8 := hD2
  have hDm : (D : ℝ) ^ 2 * ((m : ℝ) + 1) ^ 2 ≤ (q : ℝ) ^ D / 72 := by
    rw [← mul_div_assoc, div_le_iff₀ hqD] at hm2
    linarith
  have h3' : 3 ≤ (q : ℝ) ^ D / 8 := by
    rw [one_div_pow, mul_one_div, div_le_iff₀ hqD] at h3; linarith
  have hqq : 1 + 1 / (q : ℝ) ≤ 3 / 2 := by
    have : 1 / (q : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hq2
    linarith
  have hc : 0 < 6 * (1 + 1 / (q : ℝ)) := by positivity
  have hfrac : ((q : ℝ) ^ D - 3) / 9 ≤ ((q : ℝ) ^ D - 3) / (6 * (1 + 1 / (q : ℝ))) :=
    div_le_div_of_nonneg_left (by linarith) hc (by linarith)
  linarith

end GaloisForLFunctions.ArithmeticCompensationTheory
