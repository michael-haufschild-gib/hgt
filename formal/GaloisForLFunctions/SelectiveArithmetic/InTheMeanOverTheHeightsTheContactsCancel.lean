import GaloisForLFunctions.SelectiveArithmetic.APoleAtTheHeightFailsBeyondTheTrivialAperture
import GaloisForLFunctions.SelectiveArithmetic.EveryVisibleWeightIsBoundedByTheMass

/-!
# In the mean over the heights the contacts cancel

At the height `t` the primes enter the symbol of a system through the **contact polynomial**
`D_N(t) = Σ_{2 ≤ n ≤ N} Λ(n) n^{−1/2} cos(t log n)`, `N = e^{2a}`. Its size is at most
`Σ Λ(n) n^{−1/2} ≈ 2e^{a}`, and the Schur price of the sizes is `e^{a}`. This module shows that
these sizes are attained at aligned heights only: mean values are a source that buys every rung
in the mean.

* **The mean square of a cosine polynomial** (`integral_sq_sum_cos_le`): for nonnegative
  coefficients on frequencies that are `1/X`-separated together with their sums,
  `∫_A^B (Σ c(n) cos(t log n))² dt ≤ (B − A) Σ c(n)² + 2X (Σ c(n))²`. The diagonal has the length
  of the interval; an off-diagonal pair is an integral of two cosines of frequencies at least
  `1/X`.
* **The mean square of the contact polynomial** (`integral_contactPoly_sq_le`,
  `integral_contactPoly_window_sq_le`): `∫_A^B D_N² ≤ (B − A) Σ Λ(n)²/n + 4N (Σ Λ(n)/√n)²`. On the
  window of aperture `a`, if `4 e^{4a} (2 + 2a)⁴ ≤ T`, the mean square over the heights `[T, 2T]`
  is at most `2a (2 + 2a)² + 1`: polylogarithmic in the window, against the mass `log T`, at every
  aperture up to about `¼ log T`.
* **A height where the primes are quiet on an interval and half of a positive sum survives**
  (`exists_height_contactPoly_small`, `abs_contactPoly_le_of_grid`): the two mean values are
  combined by maximising `G − λ B` over the window, and a grid of shifts with the Lipschitz
  constant `Σ Λ(n) n^{−1/2} log n` controls the contact polynomial on an interval of heights.
-/

open Filter Topology MeasureTheory
open Zeta23
open scoped ArithmeticFunction.vonMangoldt Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SelectiveArithmetic

open AbsoluteGeometryOfSpecZ BiScaleUncertainty

/-! ### The mean square of a cosine polynomial -/

/-- `|∫_A^B cos(tθ) dt| ≤ 2/|θ|`. -/
theorem abs_integral_cos_mul_le {θ : ℝ} (hθ : θ ≠ 0) (A B : ℝ) :
    |∫ t in A..B, Real.cos (t * θ)| ≤ 2 / |θ| := by
  have h : ∫ t in A..B, Real.cos (t * θ) = θ⁻¹ • ∫ y in A * θ..B * θ, Real.cos y :=
    intervalIntegral.integral_comp_mul_right (fun y => Real.cos y) hθ
  rw [h, integral_cos, smul_eq_mul, abs_mul, abs_inv, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right
    (abs_le.mpr ⟨by linarith [Real.neg_one_le_sin (B * θ), Real.sin_le_one (A * θ)],
      by linarith [Real.sin_le_one (B * θ), Real.neg_one_le_sin (A * θ)]⟩) (abs_nonneg θ)

/-- Two cosines whose frequencies have difference and sum at least `1/X` have an integral of
absolute value at most `2X` over any interval. -/
theorem abs_integral_cos_mul_cos_le {α β X : ℝ} (hX : 0 < X) (h1 : 1 / X ≤ |α - β|)
    (h2 : 1 / X ≤ |α + β|) (A B : ℝ) :
    |∫ t in A..B, Real.cos (t * α) * Real.cos (t * β)| ≤ 2 * X := by
  have hXi : 0 < 1 / X := one_div_pos.mpr hX
  have hb : ∀ θ : ℝ, 1 / X ≤ |θ| → |∫ t in A..B, Real.cos (t * θ)| ≤ 2 * X := fun θ h => by
    have hθ : θ ≠ 0 := fun h0 => by
      rw [h0, abs_zero] at h
      linarith
    refine (abs_integral_cos_mul_le hθ A B).trans ?_
    rw [div_le_iff₀ (abs_pos.mpr hθ)]
    have h3 := mul_le_mul_of_nonneg_left h hX.le
    rw [mul_one_div_cancel hX.ne'] at h3
    linarith
  have e : (fun t : ℝ => Real.cos (t * α) * Real.cos (t * β)) =
      fun t : ℝ => 1 / 2 * Real.cos (t * (α - β)) + 1 / 2 * Real.cos (t * (α + β)) := by
    funext t
    rw [mul_sub, mul_add, Real.cos_sub, Real.cos_add]
    ring
  rw [e, intervalIntegral.integral_add
      ((by fun_prop : Continuous fun t : ℝ =>
        1 / 2 * Real.cos (t * (α - β))).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun t : ℝ =>
        1 / 2 * Real.cos (t * (α + β))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have h3 := abs_le.mp (hb _ h1)
  have h4 := abs_le.mp (hb _ h2)
  rw [abs_le]
  constructor <;> linarith

/-- **The mean square of a cosine polynomial.** For nonnegative coefficients on integers whose
logarithms are `1/X`-separated, together with their sums:
`∫_A^B (Σ c(n) cos(t log n))² dt ≤ (B − A) Σ c(n)² + 2X (Σ c(n))²`. -/
theorem integral_sq_sum_cos_le {s : Finset ℕ} {X : ℝ} (hX : 0 < X) (c : ℕ → ℝ)
    (hc : ∀ n ∈ s, 0 ≤ c n)
    (hsep : ∀ m ∈ s, ∀ n ∈ s, m ≠ n → 1 / X ≤ |Real.log m - Real.log n| ∧
      1 / X ≤ |Real.log m + Real.log n|) {A B : ℝ} (hAB : A ≤ B) :
    ∫ t in A..B, (∑ n ∈ s, c n * Real.cos (t * Real.log n)) ^ 2 ≤
      (B - A) * ∑ n ∈ s, c n ^ 2 + 2 * X * (∑ n ∈ s, c n) ^ 2 := by
  have hexp : (fun t : ℝ => (∑ n ∈ s, c n * Real.cos (t * Real.log n)) ^ 2) =
      fun t : ℝ => ∑ m ∈ s, ∑ n ∈ s,
        c m * c n * (Real.cos (t * Real.log m) * Real.cos (t * Real.log n)) := by
    funext t
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => by ring
  have hcont : ∀ m n : ℕ, Continuous fun t : ℝ =>
      c m * c n * (Real.cos (t * Real.log m) * Real.cos (t * Real.log n)) := fun m n => by
    fun_prop
  -- one row: the diagonal term is at most the length, every other term at most `2X`
  have hterm : ∀ m ∈ s, ∫ t in A..B, ∑ n ∈ s,
        c m * c n * (Real.cos (t * Real.log m) * Real.cos (t * Real.log n)) ≤
      (B - A) * c m ^ 2 + 2 * X * (c m * ∑ n ∈ s, c n) := by
    intro m hm
    rw [intervalIntegral.integral_finsetSum fun n _ => (hcont m n).intervalIntegrable _ _]
    have hn : ∀ n ∈ s, ∫ t in A..B,
          c m * c n * (Real.cos (t * Real.log m) * Real.cos (t * Real.log n)) ≤
        (if n = m then (B - A) * c m ^ 2 else 0) + 2 * X * (c m * c n) := by
      intro n hn
      rw [intervalIntegral.integral_const_mul]
      have hcc : 0 ≤ c m * c n := mul_nonneg (hc m hm) (hc n hn)
      by_cases hmn : n = m
      · rw [if_pos hmn, hmn]
        have hI : ∫ t in A..B, Real.cos (t * Real.log m) * Real.cos (t * Real.log m) ≤
            B - A := by
          have h := intervalIntegral.integral_mono_on (μ := volume) hAB
            ((by fun_prop : Continuous fun t : ℝ =>
              Real.cos (t * Real.log m) * Real.cos (t * Real.log m)).intervalIntegrable A B)
            (intervalIntegrable_const (c := (1 : ℝ)))
            fun t _ => by nlinarith [Real.cos_sq_le_one (t * Real.log m)]
          rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h
          exact h
        have hcm : 0 ≤ c m * c m := mul_nonneg (hc m hm) (hc m hm)
        nlinarith [mul_le_mul_of_nonneg_left hI hcm, mul_nonneg hX.le hcm]
      · rw [if_neg hmn, zero_add]
        have hsp := hsep m hm n hn (Ne.symm hmn)
        have hI := (abs_le.mp (abs_integral_cos_mul_cos_le hX hsp.1 hsp.2 A B)).2
        nlinarith [mul_le_mul_of_nonneg_left hI hcc]
    refine (Finset.sum_le_sum hn).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' s m fun _ => (B - A) * c m ^ 2, if_pos hm,
      ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hexp, intervalIntegral.integral_finsetSum fun m _ =>
    (continuous_finsetSum _ fun n _ => hcont m n).intervalIntegrable _ _]
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-! ### The contact polynomial of the primes -/

/-- The contact polynomial of the primes on a window:
`D_N(u) = Σ_{2 ≤ n ≤ N} Λ(n) n^{−1/2} cos(u log n)`. -/
def contactPoly (N : ℕ) (u : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N, (Λ n : ℝ) / Real.sqrt n * Real.cos (u * Real.log n)

/-- `Σ_{2 ≤ n ≤ N} Λ(n) n^{−1/2}`. -/
def contactMass (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 2 N, (Λ n : ℝ) / Real.sqrt n

/-- `Σ_{2 ≤ n ≤ N} Λ(n)²/n`. -/
def contactEnergy (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 2 N, ((Λ n : ℝ) / Real.sqrt n) ^ 2

/-- `Σ_{2 ≤ n ≤ N} Λ(n) n^{−1/2} log n`. -/
def contactSlope (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N, (Λ n : ℝ) / Real.sqrt n * Real.log n

theorem contactCoeff_nonneg (n : ℕ) : 0 ≤ (Λ n : ℝ) / Real.sqrt n :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

theorem contactMass_nonneg (N : ℕ) : 0 ≤ contactMass N :=
  Finset.sum_nonneg fun n _ => contactCoeff_nonneg n

theorem contactEnergy_nonneg (N : ℕ) : 0 ≤ contactEnergy N :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem contactSlope_nonneg (N : ℕ) : 0 ≤ contactSlope N :=
  Finset.sum_nonneg fun n hn => mul_nonneg (contactCoeff_nonneg n)
    (Real.log_nonneg (by exact_mod_cast (by have := (Finset.mem_Icc.mp hn).1; omega : 1 ≤ n)))

theorem continuous_contactPoly (N : ℕ) : Continuous (contactPoly N) := by
  show Continuous fun u : ℝ =>
    ∑ n ∈ Finset.Icc 2 N, (Λ n : ℝ) / Real.sqrt n * Real.cos (u * Real.log n)
  exact continuous_finsetSum _ fun n _ => by fun_prop

theorem abs_contactPoly_le (N : ℕ) (u : ℝ) : |contactPoly N u| ≤ contactMass N := by
  unfold contactPoly contactMass
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [abs_mul, abs_of_nonneg (contactCoeff_nonneg n)]
  exact mul_le_of_le_one_right (contactCoeff_nonneg n) (Real.abs_cos_le_one _)

/-- The contact polynomial is Lipschitz in the height with the constant
`Σ Λ(n) n^{−1/2} log n`. -/
theorem abs_contactPoly_sub_le (N : ℕ) (u v : ℝ) :
    |contactPoly N u - contactPoly N v| ≤ contactSlope N * |u - v| := by
  unfold contactPoly contactSlope
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (by have := (Finset.mem_Icc.mp hn).1; omega : 1 ≤ n)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
  rw [← mul_sub, abs_mul, abs_of_nonneg (contactCoeff_nonneg n)]
  have h := Real.abs_cos_sub_cos_le (u * Real.log n) (v * Real.log n)
  rw [← sub_mul, abs_mul, abs_of_nonneg hlog] at h
  calc (Λ n : ℝ) / Real.sqrt n * |Real.cos (u * Real.log n) - Real.cos (v * Real.log n)|
      ≤ (Λ n : ℝ) / Real.sqrt n * (|u - v| * Real.log n) :=
        mul_le_mul_of_nonneg_left h (contactCoeff_nonneg n)
    _ = (Λ n : ℝ) / Real.sqrt n * Real.log n * |u - v| := by ring

/-- **The mean square of the contact polynomial**:
`∫_A^B D_N² ≤ (B − A) Σ Λ(n)²/n + 4N (Σ Λ(n)/√n)²`. -/
theorem integral_contactPoly_sq_le {N : ℕ} (hN : 1 ≤ N) {A B : ℝ} (hAB : A ≤ B) :
    ∫ t in A..B, contactPoly N t ^ 2 ≤
      (B - A) * contactEnergy N + 4 * N * contactMass N ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsep : ∀ m ∈ Finset.Icc 2 N, ∀ n ∈ Finset.Icc 2 N, m ≠ n →
      1 / (2 * (N : ℝ)) ≤ |Real.log m - Real.log n| ∧
        1 / (2 * (N : ℝ)) ≤ |Real.log m + Real.log n| := by
    intro m hm n hn hmn
    rw [Finset.mem_Icc] at hm hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn.2
    have h1 : 1 / (2 * (N : ℝ)) ≤ 1 / (2 * (n : ℝ)) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    refine ⟨h1.trans (abs_log_sub_log_ge (by omega) (by omega) hmn), ?_⟩
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm.1
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlm : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) hm2
    have hln : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
    have h2 : 1 / (2 * (N : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    exact h2.trans (le_abs.mpr (Or.inl (by linarith)))
  have h := integral_sq_sum_cos_le (X := 2 * (N : ℝ)) (mul_pos two_pos hN0)
    (fun n => (Λ n : ℝ) / Real.sqrt n) (fun n _ => contactCoeff_nonneg n) hsep hAB
  unfold contactPoly contactEnergy contactMass
  refine h.trans (le_of_eq ?_)
  ring

/-- The mean square of the contact polynomial over a window of heights, with a shift. -/
theorem integral_contactPoly_shift_sq_le {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hT : 0 ≤ T) (s : ℝ) :
    ∫ t in T..2 * T, contactPoly N (t + s) ^ 2 ≤
      T * contactEnergy N + 4 * N * contactMass N ^ 2 := by
  have h : ∫ t in T..2 * T, contactPoly N (t + s) ^ 2 =
      ∫ u in T + s..2 * T + s, contactPoly N u ^ 2 :=
    intervalIntegral.integral_comp_add_right (fun u => contactPoly N u ^ 2) s
  rw [h]
  refine (integral_contactPoly_sq_le hN (by linarith)).trans (le_of_eq ?_)
  ring

/-! ### The sizes on a window -/

theorem cast_le_exp_of_mem {a : ℝ} {n : ℕ} (hn : n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊) :
    (n : ℝ) ≤ Real.exp (2 * a) :=
  (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans (Nat.floor_le (Real.exp_pos _).le)

/-- Mertens' bound on the window, from the second integer on. -/
theorem sum_vonMangoldt_div_window_le' {a : ℝ} (ha : 0 ≤ a) :
    ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, (Λ n : ℝ) / n ≤ (2 + 2 * a) ^ 2 :=
  (Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => by
    rw [Finset.mem_Icc] at hn ⊢
    omega) fun n _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Nat.cast_nonneg n)).trans (sum_vonMangoldt_div_window_le ha)

/-- `Λ(n)/√n ≤ e^{a} Λ(n)/n` for `n ≤ e^{2a}`. -/
theorem contactCoeff_le {a : ℝ} {n : ℕ} (hn0 : (0 : ℝ) < n) (hn : (n : ℝ) ≤ Real.exp (2 * a)) :
    (Λ n : ℝ) / Real.sqrt n ≤ Real.exp a * ((Λ n : ℝ) / n) := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  have hE2 : Real.exp a ^ 2 = Real.exp (2 * a) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hsE : Real.sqrt n ≤ Real.exp a :=
    Real.sqrt_le_iff.mpr ⟨(Real.exp_pos a).le, by rw [hE2]; exact hn⟩
  have e1 : (Λ n : ℝ) / Real.sqrt n = (Λ n : ℝ) / n * Real.sqrt n := by
    rw [div_mul_eq_mul_div, div_eq_div_iff hs.ne' hn0.ne', mul_assoc, hss]
  rw [e1, mul_comm (Real.exp a)]
  exact mul_le_mul_of_nonneg_left hsE
    (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hn0.le)

/-- The mass of the contacts on the window of aperture `a` is at most `e^{a} (2 + 2a)²`. -/
theorem contactMass_le {a : ℝ} (ha : 0 ≤ a) :
    contactMass ⌊Real.exp (2 * a)⌋₊ ≤ Real.exp a * (2 + 2 * a) ^ 2 := by
  unfold contactMass
  calc ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, (Λ n : ℝ) / Real.sqrt n
      ≤ ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, Real.exp a * ((Λ n : ℝ) / n) :=
        Finset.sum_le_sum fun n hn => by
          have hn2 := (Finset.mem_Icc.mp hn).1
          have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
          exact contactCoeff_le hn0 (cast_le_exp_of_mem hn)
    _ = Real.exp a * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, (Λ n : ℝ) / n :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp a * (2 + 2 * a) ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_vonMangoldt_div_window_le' ha) (Real.exp_pos _).le

/-- The energy of the contacts on the window of aperture `a` is at most `2a (2 + 2a)²`. -/
theorem contactEnergy_le {a : ℝ} (ha : 0 ≤ a) :
    contactEnergy ⌊Real.exp (2 * a)⌋₊ ≤ 2 * a * (2 + 2 * a) ^ 2 := by
  unfold contactEnergy
  calc ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, ((Λ n : ℝ) / Real.sqrt n) ^ 2
      ≤ ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, 2 * a * ((Λ n : ℝ) / n) :=
        Finset.sum_le_sum fun n hn => by
          have hn2 := (Finset.mem_Icc.mp hn).1
          have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
          have hlog : Real.log n ≤ 2 * a :=
            (Real.log_le_log hn0 (cast_le_exp_of_mem hn)).trans_eq (Real.log_exp _)
          have hΛ : (Λ n : ℝ) ≤ 2 * a := ArithmeticFunction.vonMangoldt_le_log.trans hlog
          rw [div_pow, Real.sq_sqrt hn0.le, sq, mul_div_assoc]
          exact mul_le_mul_of_nonneg_right hΛ
            (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hn0.le)
    _ = 2 * a * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, (Λ n : ℝ) / n :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * a * (2 + 2 * a) ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_vonMangoldt_div_window_le' ha) (by linarith)

/-- The slope of the contact polynomial on the window of aperture `a` is at most
`2a e^{a} (2 + 2a)²`. -/
theorem contactSlope_le {a : ℝ} (ha : 0 ≤ a) :
    contactSlope ⌊Real.exp (2 * a)⌋₊ ≤ 2 * a * (Real.exp a * (2 + 2 * a) ^ 2) := by
  unfold contactSlope
  calc ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, (Λ n : ℝ) / Real.sqrt n * Real.log n
      ≤ ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, 2 * a * ((Λ n : ℝ) / Real.sqrt n) :=
        Finset.sum_le_sum fun n hn => by
          have hn2 := (Finset.mem_Icc.mp hn).1
          have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
          have hlog : Real.log n ≤ 2 * a :=
            (Real.log_le_log hn0 (cast_le_exp_of_mem hn)).trans_eq (Real.log_exp _)
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right hlog (contactCoeff_nonneg n)
    _ = 2 * a * contactMass ⌊Real.exp (2 * a)⌋₊ := (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * a * (Real.exp a * (2 + 2 * a) ^ 2) :=
        mul_le_mul_of_nonneg_left (contactMass_le ha) (by linarith)

/-- The off-diagonal budget of the window: `4N (Σ Λ(n)/√n)² ≤ 4 e^{4a} (2 + 2a)⁴`. -/
theorem four_mul_window_mass_sq_le {a : ℝ} (ha : 0 ≤ a) :
    4 * (⌊Real.exp (2 * a)⌋₊ : ℝ) * contactMass ⌊Real.exp (2 * a)⌋₊ ^ 2 ≤
      4 * Real.exp (4 * a) * (2 + 2 * a) ^ 4 := by
  have hNle : ((⌊Real.exp (2 * a)⌋₊ : ℕ) : ℝ) ≤ Real.exp (2 * a) :=
    Nat.floor_le (Real.exp_pos _).le
  have hP2 : contactMass ⌊Real.exp (2 * a)⌋₊ ^ 2 ≤ (Real.exp a * (2 + 2 * a) ^ 2) ^ 2 :=
    pow_le_pow_left₀ (contactMass_nonneg _) (contactMass_le ha) 2
  have h := mul_le_mul hNle hP2 (sq_nonneg _) (Real.exp_pos _).le
  have e : Real.exp (2 * a) * (Real.exp a * (2 + 2 * a) ^ 2) ^ 2 =
      Real.exp (4 * a) * (2 + 2 * a) ^ 4 := by
    have h1 : Real.exp (4 * a) = Real.exp (2 * a) * (Real.exp a * Real.exp a) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [h1]
    ring
  linarith

/-- **In the mean over the heights the contacts of the primes cancel.** On the window of aperture
`a`, if `4 e^{4a} (2 + 2a)⁴ ≤ T`, the mean square of the contact polynomial over the heights
`[T, 2T]` is at most `2a (2 + 2a)² + 1`. -/
theorem integral_contactPoly_window_sq_le {a : ℝ} (ha : 0 ≤ a) {T : ℝ}
    (hT : 4 * Real.exp (4 * a) * (2 + 2 * a) ^ 4 ≤ T) :
    ∫ t in T..2 * T, contactPoly ⌊Real.exp (2 * a)⌋₊ t ^ 2 ≤
      T * (2 * a * (2 + 2 * a) ^ 2 + 1) := by
  have hT0 : 0 ≤ T := le_trans (by positivity) hT
  have hN : 1 ≤ ⌊Real.exp (2 * a)⌋₊ :=
    Nat.le_floor (by rw [Nat.cast_one]; exact Real.one_le_exp (by linarith))
  have h1 := integral_contactPoly_sq_le hN (by linarith : T ≤ 2 * T)
  have h2 := four_mul_window_mass_sq_le ha
  have h3 := mul_le_mul_of_nonneg_left (contactEnergy_le ha) hT0
  linarith

/-! ### A height where the primes are quiet and half of a positive sum survives -/

/-- **A common height for two means.** If the mean of `G` over `[T, 2T]` is at least
`(½ − 1/T) S` and the mean of `B` at most `K`, then at some height
`G − λ B ≥ (½ − 1/T) S − λ K`: the maximum of `G − λ B` is at least its mean. -/
theorem exists_height_of_means {G B : ℝ → ℝ} (hG : Continuous G) (hB : Continuous B)
    {T S K lam : ℝ} (hT : 0 < T) (hGm : (T / 2 - 1) * S ≤ ∫ t in T..2 * T, G t)
    (hBm : ∫ t in T..2 * T, B t ≤ T * K) (hlam : 0 ≤ lam) :
    ∃ t ∈ Set.Icc T (2 * T), (1 / 2 - 1 / T) * S - lam * K ≤ G t - lam * B t := by
  have hlB : Continuous fun t => lam * B t := continuous_const.mul hB
  have hΦ : Continuous fun t => G t - lam * B t := hG.sub hlB
  have hTle : T ≤ 2 * T := by linarith
  obtain ⟨t₀, ht₀, hmax⟩ := (isCompact_Icc (a := T) (b := 2 * T)).exists_isMaxOn
    ⟨T, Set.left_mem_Icc.mpr hTle⟩ hΦ.continuousOn
  refine ⟨t₀, ht₀, ?_⟩
  have hup : ∫ t in T..2 * T, (G t - lam * B t) ≤ T * (G t₀ - lam * B t₀) := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hTle
      (hΦ.intervalIntegrable T (2 * T))
      (intervalIntegrable_const (c := G t₀ - lam * B t₀))
      fun t ht => isMaxOn_iff.mp hmax t ht
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    exact h.trans (le_of_eq (by ring))
  have hsplit : ∫ t in T..2 * T, (G t - lam * B t) =
      (∫ t in T..2 * T, G t) - lam * ∫ t in T..2 * T, B t := by
    rw [intervalIntegral.integral_sub (hG.intervalIntegrable _ _)
      (hlB.intervalIntegrable _ _), intervalIntegral.integral_const_mul]
  rw [hsplit] at hup
  have h1 : lam * ∫ t in T..2 * T, B t ≤ lam * (T * K) := mul_le_mul_of_nonneg_left hBm hlam
  have hfin : (T / 2 - 1) * S - lam * (T * K) ≤ T * (G t₀ - lam * B t₀) := by linarith
  have e : T * ((1 / 2 - 1 / T) * S - lam * K) = (T / 2 - 1) * S - lam * (T * K) := by
    have hTT : T * (1 / T) = 1 := mul_one_div_cancel hT.ne'
    linear_combination (-S) * hTT
  exact le_of_mul_le_mul_left (by rw [e]; exact hfin) hT

/-- **A height where the primes are quiet on a grid and half of a positive sum survives.** Let
`4N (Σ Λ(n)/√n)² ≤ T`, `T ≥ 2`, and let `r ≥ 0` on the window with positive sum. For every grid of
`2M + 1` shifts and every `0 < ε ≤ 1` there is a height `t ∈ [T, 2T]` with
`Σ r(n) cos²(t log n) ≥ (½ − 1/T − ε) Σ r(n)` and
`D_N(t + (k − M) h)² ≤ 2 (2M + 1)(Σ Λ(n)²/n + 1)/ε` at every point of the grid. -/
theorem exists_height_contactPoly_small {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hT : 2 ≤ T) (M : ℕ)
    (h : ℝ) (r : ℕ → ℝ) (hr : ∀ n ∈ Finset.Icc 2 N, 0 ≤ r n)
    (hpos : 0 < ∑ n ∈ Finset.Icc 2 N, r n) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsmall : 4 * N * contactMass N ^ 2 ≤ T) :
    ∃ t ∈ Set.Icc T (2 * T),
      (1 / 2 - 1 / T - ε) * ∑ n ∈ Finset.Icc 2 N, r n ≤
          ∑ n ∈ Finset.Icc 2 N, r n * Real.cos (t * Real.log n) ^ 2 ∧
      ∀ k ∈ Finset.range (2 * M + 1),
        contactPoly N (t + ((k : ℝ) - M) * h) ^ 2 ≤
          2 * ((2 * (M : ℝ) + 1) * (contactEnergy N + 1)) / ε := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ∑ n ∈ Finset.Icc 2 N, r n := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (2 * (M : ℝ) + 1) * (contactEnergy N + 1) := ⟨_, rfl⟩
  rw [← hR] at hpos ⊢
  rw [← hK]
  have hQ0 := contactEnergy_nonneg N
  have hK0 : 0 < K := by
    rw [hK]
    positivity
  have hT0 : 0 < T := by linarith
  have hshift : ∀ c : ℝ, Continuous fun t : ℝ => contactPoly N (t + c) ^ 2 := fun c => by
    have := continuous_contactPoly N
    fun_prop
  have hGc : Continuous fun t : ℝ =>
      ∑ n ∈ Finset.Icc 2 N, r n * Real.cos (t * Real.log n) ^ 2 :=
    continuous_finsetSum _ fun n _ => by fun_prop
  have hBc : Continuous fun t : ℝ =>
      ∑ k ∈ Finset.range (2 * M + 1), contactPoly N (t + ((k : ℝ) - M) * h) ^ 2 :=
    continuous_finsetSum _ fun k _ => hshift _
  have hGm : (T / 2 - 1) * R ≤
      ∫ t in T..2 * T, ∑ n ∈ Finset.Icc 2 N, r n * Real.cos (t * Real.log n) ^ 2 := by
    rw [hR]
    exact integral_sum_cos_sq_ge (Finset.Icc 2 N) r hr
      (fun n hn => (Finset.mem_Icc.mp hn).1) T
  have hBm : ∫ t in T..2 * T,
        ∑ k ∈ Finset.range (2 * M + 1), contactPoly N (t + ((k : ℝ) - M) * h) ^ 2 ≤
      T * K := by
    rw [intervalIntegral.integral_finsetSum fun k _ => (hshift _).intervalIntegrable _ _]
    calc ∑ k ∈ Finset.range (2 * M + 1),
          ∫ t in T..2 * T, contactPoly N (t + ((k : ℝ) - M) * h) ^ 2
        ≤ ∑ _k ∈ Finset.range (2 * M + 1), (T * contactEnergy N + T) :=
          Finset.sum_le_sum fun k _ =>
            (integral_contactPoly_shift_sq_le hN hT0.le _).trans (by linarith)
      _ = T * K := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hK]
          push_cast
          ring
  have hlam : 0 ≤ ε * R / K := by positivity
  obtain ⟨t, ht, hsel⟩ := exists_height_of_means hGc hBc hT0 hGm hBm hlam
  obtain ⟨Bd, hBd⟩ : ∃ Bd : ℝ, Bd =
      ∑ k ∈ Finset.range (2 * M + 1), contactPoly N (t + ((k : ℝ) - M) * h) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Gt, hGt⟩ : ∃ Gt : ℝ, Gt =
      ∑ n ∈ Finset.Icc 2 N, r n * Real.cos (t * Real.log n) ^ 2 := ⟨_, rfl⟩
  have hlamK : ε * R / K * K = ε * R := div_mul_cancel₀ _ hK0.ne'
  have hsel' : (1 / 2 - 1 / T) * R - ε * R ≤ Gt - ε * R / K * Bd := by
    rw [hGt, hBd, ← hlamK]
    exact hsel
  have hBd0 : 0 ≤ Bd := by
    rw [hBd]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hGle : Gt ≤ R := by
    rw [hGt, hR]
    exact Finset.sum_le_sum fun n hn =>
      mul_le_of_le_one_right (hr n hn) (Real.cos_sq_le_one _)
  have hTinv : 1 / T ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hT
  have hlB := mul_nonneg hlam hBd0
  refine ⟨t, ht, ?_, fun k hk => ?_⟩
  · rw [← hGt]
    linarith
  · have hk' := Finset.single_le_sum
      (f := fun k : ℕ => contactPoly N (t + ((k : ℝ) - M) * h) ^ 2)
      (fun _ _ => sq_nonneg _) hk
    have hkB : contactPoly N (t + ((k : ℝ) - M) * h) ^ 2 ≤ Bd := by
      rw [hBd]
      exact hk'
    refine hkB.trans ?_
    have h3 : 1 / T * R ≤ 1 / 2 * R := mul_le_mul_of_nonneg_right hTinv hpos.le
    have h4 : ε * R ≤ 1 * R := mul_le_mul_of_nonneg_right hε1 hpos.le
    have h2 : ε * R / K * Bd ≤ 2 * R := by linarith
    have h6 := mul_le_mul_of_nonneg_right h2 hK0.le
    have e : ε * R / K * Bd * K = R * (Bd * ε) := by
      rw [mul_right_comm, hlamK]
      ring
    rw [e] at h6
    rw [le_div_iff₀ hε]
    exact le_of_mul_le_mul_left (by linarith) hpos

/-- **From a grid to an interval of heights.** If the contact polynomial is at most `b` at the
points `t + (k − M) h`, `0 ≤ k ≤ 2M`, then it is at most `b + h Σ Λ(n) n^{−1/2} log n` at every
`t + s` with `|s| ≤ M h`. -/
theorem abs_contactPoly_le_of_grid {N M : ℕ} {t h b : ℝ} (hh : 0 < h)
    (hgrid : ∀ k ∈ Finset.range (2 * M + 1), |contactPoly N (t + ((k : ℝ) - M) * h)| ≤ b)
    {s : ℝ} (hs : |s| ≤ M * h) :
    |contactPoly N (t + s)| ≤ b + contactSlope N * h := by
  have hs' := abs_le.mp hs
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (s + M * h) / h := ⟨_, rfl⟩
  have hyh : y * h = s + M * h := by rw [hy, div_mul_cancel₀ _ hh.ne']
  have hy0 : 0 ≤ y := nonneg_of_mul_nonneg_left (by rw [hyh]; linarith) hh
  have hyM : y ≤ 2 * M := le_of_mul_le_mul_right (by rw [hyh]; linarith) hh
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌊y⌋₊ := ⟨_, rfl⟩
  have hk1 : (k : ℝ) ≤ y := by
    rw [hk]
    exact Nat.floor_le hy0
  have hk2 : y < k + 1 := by
    rw [hk]
    exact Nat.lt_floor_add_one y
  have hkM : k ≤ 2 * M := by
    have : (k : ℝ) ≤ 2 * M := hk1.trans hyM
    exact_mod_cast this
  have hg := hgrid k (Finset.mem_range.mpr (by omega))
  have hd : |(t + s) - (t + ((k : ℝ) - M) * h)| ≤ h := by
    have e : (t + s) - (t + ((k : ℝ) - M) * h) = (y - k) * h := by
      linear_combination (-1 : ℝ) * hyh
    rw [e, abs_of_nonneg (mul_nonneg (by linarith) hh.le)]
    nlinarith [mul_le_mul_of_nonneg_right (by linarith : y - k ≤ 1) hh.le]
  have hlip := abs_contactPoly_sub_le N (t + s) (t + ((k : ℝ) - M) * h)
  have h1 := abs_sub_abs_le_abs_sub (contactPoly N (t + s))
    (contactPoly N (t + ((k : ℝ) - M) * h))
  have h2 := mul_le_mul_of_nonneg_left hd (contactSlope_nonneg N)
  linarith

end GaloisForLFunctions.SelectiveArithmetic
