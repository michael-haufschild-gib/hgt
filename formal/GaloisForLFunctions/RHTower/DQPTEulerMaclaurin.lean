import GaloisForLFunctions.RHTower.DQPTBernoulliBound

/-!
# DQPT: Euler–Maclaurin summation to arbitrary order

Supplementary Note 4 of arXiv:2511.11199 (published Supplementary Note 5), Proposition 4.5,
uses the Euler–Maclaurin formula to order `2l₃` with the Bernoulli-polynomial remainder.
Neither mathlib nor this corpus had that formula (only the second-order case,
`HTGeometry.EulerMaclaurinSecondOrder`), so it is built here.

The formula is stated for a **derivative tower** `F : ℕ → ℝ → ℝ` with `F (j+1) = (F j)'` on the
interval, which avoids any global smoothness assumption: `x ↦ x^{−β}` has such a tower on
`(0, ∞)`.

Main results:
* `dqptEMJ_zero`, `dqptEMJ_succ` — the one-cell integration-by-parts recursion;
* `dqptEMJ_one_expansion` — the order-`M` expansion of the first cell integral;
* `dqpt_euler_maclaurin_cell` — the Euler–Maclaurin identity on one unit cell;
* `dqpt_euler_maclaurin` — **Euler–Maclaurin summation to order `2m`**;
* `dqpt_abs_bernoulliFun_le` — `|B_{2k}(x)| ≤ |B_{2k}| on [0,1]`, the remainder bound input.
-/

namespace RHTower.DQPT

open Filter Topology Set MeasureTheory

noncomputable section

/-! ## Derivative towers -/

/-- `F` is a derivative tower on `s`: each `F (j+1)` is the derivative of `F j`. -/
def DqptDerivTower (F : ℕ → ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ j : ℕ, ∀ x ∈ s, HasDerivAt (F j) (F (j + 1) x) x

theorem DqptDerivTower.continuousOn {F : ℕ → ℝ → ℝ} {s : Set ℝ}
    (hF : DqptDerivTower F s) (j : ℕ) : ContinuousOn (F j) s :=
  fun x hx => ((hF j x hx).continuousAt).continuousWithinAt

theorem DqptDerivTower.mono {F : ℕ → ℝ → ℝ} {s t : Set ℝ} (hF : DqptDerivTower F s)
    (hts : t ⊆ s) : DqptDerivTower F t :=
  fun j x hx => hF j x (hts hx)

/-! ## The cell integrals -/

/-- The `k`-th Euler–Maclaurin cell integral over `[t, t+1]`. -/
def dqptEMJ (F : ℕ → ℝ → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  ∫ x in t..(t + 1), bernoulliFun k (x - t) / (k.factorial : ℝ) * F k x

theorem dqpt_uIcc_cell (t : ℝ) : Set.uIcc t (t + 1) = Set.Icc t (t + 1) :=
  Set.uIcc_of_le (by linarith)

theorem dqpt_intervalIntegrable_cell {F : ℕ → ℝ → ℝ} {t : ℝ}
    (hF : DqptDerivTower F (Set.Icc t (t + 1))) (j : ℕ) :
    IntervalIntegrable (F j) volume t (t + 1) := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [dqpt_uIcc_cell]
  exact hF.continuousOn j

/-- The antiderivative used in the cell integration by parts. -/
theorem dqpt_hasDerivAt_bernoulliQuot (k : ℕ) (t x : ℝ) :
    HasDerivAt (fun y : ℝ => bernoulliFun (k + 1) (y - t) / ((k + 1).factorial : ℝ))
      (bernoulliFun k (x - t) / (k.factorial : ℝ)) x := by
  have hbase : HasDerivAt (fun y : ℝ => bernoulliFun (k + 1) y / ((k : ℝ) + 1))
      (bernoulliFun k (x - t)) (x - t) := antideriv_bernoulliFun k (x - t)
  have hshift : HasDerivAt (fun y : ℝ => bernoulliFun (k + 1) (y - t) / ((k : ℝ) + 1))
      (bernoulliFun k (x - t)) x := by
    have h := hbase.comp_sub_const x t
    exact h
  have hdiv := hshift.div_const (k.factorial : ℝ)
  refine hdiv.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
  · have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    field_simp
  · filter_upwards with y
    have hfacsucc : (((k + 1).factorial : ℕ) : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [hfacsucc]
    have hfac : (0 : ℝ) ≠ (k.factorial : ℝ) := by
      have := Nat.factorial_pos k
      positivity
    field_simp

/-- **The base cell identity.**  `∫_t^{t+1} F₀ = (F₀(t)+F₀(t+1))/2 − J₁(t)`. -/
theorem dqptEMJ_zero {F : ℕ → ℝ → ℝ} {t : ℝ} (hF : DqptDerivTower F (Set.Icc t (t + 1))) :
    dqptEMJ F 0 t = (F 0 t + F 0 (t + 1)) / 2 - dqptEMJ F 1 t := by
  have huIcc := dqpt_uIcc_cell t
  have hu : ∀ x ∈ Set.uIcc t (t + 1), HasDerivAt (F 0) (F 1 x) x := by
    intro x hx
    rw [huIcc] at hx
    exact hF 0 x hx
  have hv : ∀ x ∈ Set.uIcc t (t + 1),
      HasDerivAt (fun y : ℝ => bernoulliFun 1 (y - t) / ((1 : ℕ).factorial : ℝ))
        (bernoulliFun 0 (x - t) / ((0 : ℕ).factorial : ℝ)) x := by
    intro x _
    exact dqpt_hasDerivAt_bernoulliQuot 0 t x
  have hu' : IntervalIntegrable (F 1) volume t (t + 1) := dqpt_intervalIntegrable_cell hF 1
  have hv' : IntervalIntegrable
      (fun x : ℝ => bernoulliFun 0 (x - t) / ((0 : ℕ).factorial : ℝ)) volume t (t + 1) := by
    refine ContinuousOn.intervalIntegrable ?_
    fun_prop
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hlhs : ∫ x in t..(t + 1), F 0 x
        * (bernoulliFun 0 (x - t) / ((0 : ℕ).factorial : ℝ)) = dqptEMJ F 0 t := by
    rw [dqptEMJ]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp [Nat.factorial]
  have hrhs : ∫ x in t..(t + 1), F 1 x
        * (bernoulliFun 1 (x - t) / ((1 : ℕ).factorial : ℝ)) = dqptEMJ F 1 t := by
    rw [dqptEMJ]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    ring
  rw [hlhs, hrhs] at key
  rw [key]
  have hb1 : bernoulliFun 1 ((t + 1) - t) = 1 / 2 := by
    have : (t + 1) - t = 1 := by ring
    rw [this, bernoulliFun_one]
    norm_num
  have hb0 : bernoulliFun 1 (t - t) = -(1 / 2) := by
    have : t - t = 0 := by ring
    rw [this, bernoulliFun_one]
    norm_num
  rw [hb1, hb0]
  simp [Nat.factorial]
  ring

/-- **The cell recursion.**  For `k ≥ 1`,
`J_k(t) = B_{k+1}/(k+1)!·(F_k(t+1) − F_k(t)) − J_{k+1}(t)`. -/
theorem dqptEMJ_succ {F : ℕ → ℝ → ℝ} {t : ℝ} (hF : DqptDerivTower F (Set.Icc t (t + 1)))
    {k : ℕ} (hk : 1 ≤ k) :
    dqptEMJ F k t
      = ((bernoulli (k + 1) : ℚ) : ℝ) / (((k + 1).factorial : ℕ) : ℝ)
          * (F k (t + 1) - F k t) - dqptEMJ F (k + 1) t := by
  have huIcc := dqpt_uIcc_cell t
  have hu : ∀ x ∈ Set.uIcc t (t + 1), HasDerivAt (F k) (F (k + 1) x) x := by
    intro x hx
    rw [huIcc] at hx
    exact hF k x hx
  have hv : ∀ x ∈ Set.uIcc t (t + 1),
      HasDerivAt (fun y : ℝ => bernoulliFun (k + 1) (y - t) / (((k + 1).factorial : ℕ) : ℝ))
        (bernoulliFun k (x - t) / ((k.factorial : ℕ) : ℝ)) x := by
    intro x _
    exact dqpt_hasDerivAt_bernoulliQuot k t x
  have hu' : IntervalIntegrable (F (k + 1)) volume t (t + 1) :=
    dqpt_intervalIntegrable_cell hF (k + 1)
  have hv' : IntervalIntegrable
      (fun x : ℝ => bernoulliFun k (x - t) / ((k.factorial : ℕ) : ℝ)) volume t (t + 1) := by
    refine ContinuousOn.intervalIntegrable ?_
    fun_prop
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hlhs : ∫ x in t..(t + 1), F k x
        * (bernoulliFun k (x - t) / ((k.factorial : ℕ) : ℝ)) = dqptEMJ F k t := by
    rw [dqptEMJ]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    ring
  have hrhs : ∫ x in t..(t + 1), F (k + 1) x
        * (bernoulliFun (k + 1) (x - t) / (((k + 1).factorial : ℕ) : ℝ))
      = dqptEMJ F (k + 1) t := by
    rw [dqptEMJ]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    ring
  rw [hlhs, hrhs] at key
  rw [key]
  have hne : k + 1 ≠ 1 := by omega
  have hb1 : bernoulliFun (k + 1) ((t + 1) - t) = ((bernoulli (k + 1) : ℚ) : ℝ) := by
    have harg : (t + 1) - t = 1 := by ring
    rw [harg, bernoulliFun_endpoints_eq_of_ne_one hne, bernoulliFun_eval_zero]
  have hb0 : bernoulliFun (k + 1) (t - t) = ((bernoulli (k + 1) : ℚ) : ℝ) := by
    have harg : t - t = 0 := by ring
    rw [harg, bernoulliFun_eval_zero]
  rw [hb1, hb0]
  ring

end

end RHTower.DQPT

namespace RHTower.DQPT

open Filter Topology Set MeasureTheory

noncomputable section

/-! ## The order-`M` expansion of the first cell integral -/

theorem dqptEMJ_one_expansion {F : ℕ → ℝ → ℝ} {t : ℝ}
    (hF : DqptDerivTower F (Set.Icc t (t + 1))) (M : ℕ) :
    dqptEMJ F 1 t
      = ∑ k ∈ Finset.Icc 1 M, (-1 : ℝ) ^ (k + 1)
            * (((bernoulli (k + 1) : ℚ) : ℝ) / (((k + 1).factorial : ℕ) : ℝ))
            * (F k (t + 1) - F k t)
        + (-1 : ℝ) ^ M * dqptEMJ F (M + 1) t := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1)]
      have hrec := dqptEMJ_succ hF (by omega : 1 ≤ M + 1)
      have hsign1 : (-1 : ℝ) ^ (M + 1 + 1) = (-1 : ℝ) ^ M := by
        rw [pow_succ, pow_succ]
        ring
      have hsign2 : (-1 : ℝ) ^ (M + 1) = -((-1 : ℝ) ^ M) := by
        rw [pow_succ]
        ring
      rw [ih, hrec, hsign1, hsign2]
      ring

/-! ## The odd reindexing -/

theorem dqpt_odd_reindex {g : ℕ → ℝ} (hzero : ∀ j : ℕ, 1 ≤ j → g (2 * j) = 0) (m : ℕ) :
    ∑ k ∈ Finset.Icc 1 (2 * m + 1), g k = ∑ r ∈ Finset.range (m + 1), g (2 * r + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hstep : 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 := by ring
      have hz : g (2 * m + 1 + 1) = 0 := by
        have hrw : 2 * m + 1 + 1 = 2 * (m + 1) := by ring
        rw [hrw]
        exact hzero (m + 1) (by omega)
      rw [hstep, Finset.sum_Icc_succ_top (by omega : 1 ≤ 2 * m + 1 + 1 + 1),
        Finset.sum_Icc_succ_top (by omega : 1 ≤ 2 * m + 1 + 1), ih, hz]
      conv_rhs => rw [Finset.sum_range_succ]
      have hidx : 2 * m + 1 + 1 + 1 = 2 * (m + 1) + 1 := by ring
      rw [hidx]
      ring

/-! ## Euler–Maclaurin on one cell -/

theorem dqpt_euler_maclaurin_cell {F : ℕ → ℝ → ℝ} {t : ℝ}
    (hF : DqptDerivTower F (Set.Icc t (t + 1))) (m : ℕ) :
    (∫ x in t..(t + 1), F 0 x)
      = (F 0 t + F 0 (t + 1)) / 2
        - ∑ r ∈ Finset.range (m + 1),
            ((bernoulli (2 * r + 2) : ℚ) : ℝ) / (((2 * r + 2).factorial : ℕ) : ℝ)
              * (F (2 * r + 1) (t + 1) - F (2 * r + 1) t)
        + dqptEMJ F (2 * m + 2) t := by
  have hzero0 : dqptEMJ F 0 t = ∫ x in t..(t + 1), F 0 x := by
    rw [dqptEMJ]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp [Nat.factorial]
  have hbase := dqptEMJ_zero hF
  have hexp := dqptEMJ_one_expansion hF (2 * m + 1)
  set g : ℕ → ℝ := fun k => (-1 : ℝ) ^ (k + 1)
      * (((bernoulli (k + 1) : ℚ) : ℝ) / (((k + 1).factorial : ℕ) : ℝ))
      * (F k (t + 1) - F k t) with hg
  have hgzero : ∀ j : ℕ, 1 ≤ j → g (2 * j) = 0 := by
    intro j hj
    have hodd : Odd (2 * j + 1) := ⟨j, by ring⟩
    have hb : bernoulli (2 * j + 1) = 0 := bernoulli_eq_zero_of_odd hodd (by omega)
    rw [hg]
    simp only
    rw [hb]
    simp
  have hreindex := dqpt_odd_reindex hgzero m
  have hgodd : ∀ r : ℕ, g (2 * r + 1)
      = ((bernoulli (2 * r + 2) : ℚ) : ℝ) / (((2 * r + 2).factorial : ℕ) : ℝ)
          * (F (2 * r + 1) (t + 1) - F (2 * r + 1) t) := by
    intro r
    rw [hg]
    simp only
    have hs : (-1 : ℝ) ^ (2 * r + 1 + 1) = 1 := by
      have : 2 * r + 1 + 1 = 2 * (r + 1) := by ring
      rw [this, pow_mul]
      norm_num
    rw [hs, one_mul]
  have hsum : ∑ k ∈ Finset.Icc 1 (2 * m + 1), g k
      = ∑ r ∈ Finset.range (m + 1),
          ((bernoulli (2 * r + 2) : ℚ) : ℝ) / (((2 * r + 2).factorial : ℕ) : ℝ)
            * (F (2 * r + 1) (t + 1) - F (2 * r + 1) t) := by
    rw [hreindex]
    exact Finset.sum_congr rfl (fun r _ => hgodd r)
  have hsign : (-1 : ℝ) ^ (2 * m + 1) = -1 := by
    rw [pow_succ, pow_mul]
    norm_num
  rw [← hzero0, hbase, hexp, hsum, hsign]
  have hidx : 2 * m + 1 + 1 = 2 * m + 2 := by ring
  rw [hidx]
  ring

end

end RHTower.DQPT

namespace RHTower.DQPT

open Filter Topology Set MeasureTheory

noncomputable section

/-! ## Euler–Maclaurin summation over `N` cells -/

theorem dqpt_intervalIntegrable_run {F : ℕ → ℝ → ℝ} {a : ℝ} {N : ℕ}
    (hF : DqptDerivTower F (Set.Icc a (a + N))) :
    IntervalIntegrable (F 0) volume a (a + N) := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le (by have : (0:ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N; linarith :
    a ≤ a + (N : ℝ))]
  exact hF.continuousOn 0

/-- **Euler–Maclaurin summation to order `2m+2`.** -/
theorem dqpt_euler_maclaurin {F : ℕ → ℝ → ℝ} {a : ℝ} (m : ℕ) :
    ∀ N : ℕ, DqptDerivTower F (Set.Icc a (a + N)) →
      ∑ n ∈ Finset.range (N + 1), F 0 (a + n)
        = (∫ x in a..(a + (N : ℝ)), F 0 x) + (F 0 a + F 0 (a + N)) / 2
          + ∑ r ∈ Finset.range (m + 1),
              ((bernoulli (2 * r + 2) : ℚ) : ℝ) / (((2 * r + 2).factorial : ℕ) : ℝ)
                * (F (2 * r + 1) (a + N) - F (2 * r + 1) a)
          - ∑ n ∈ Finset.range N, dqptEMJ F (2 * m + 2) (a + n) := by
  intro N
  induction N with
  | zero =>
      intro _
      simp
  | succ N ih =>
      intro hF
      have hcastN : ((N : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
        push_cast; linarith
      have hsub1 : DqptDerivTower F (Set.Icc a (a + (N : ℝ))) := by
        refine hF.mono ?_
        refine Set.Icc_subset_Icc (le_refl a) ?_
        push_cast
        linarith
      have hsub2 : DqptDerivTower F (Set.Icc (a + (N : ℝ)) ((a + (N : ℝ)) + 1)) := by
        refine hF.mono ?_
        refine Set.Icc_subset_Icc ?_ ?_
        · have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
          linarith
        · push_cast
          linarith
      have hcell := dqpt_euler_maclaurin_cell hsub2 m
      have hIH := ih hsub1
      have hend : a + ((N + 1 : ℕ) : ℝ) = (a + (N : ℝ)) + 1 := by push_cast; ring
      have hint1 : IntervalIntegrable (F 0) volume a (a + (N : ℝ)) :=
        dqpt_intervalIntegrable_run hsub1
      have hint2 : IntervalIntegrable (F 0) volume (a + (N : ℝ)) ((a + (N : ℝ)) + 1) := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [Set.uIcc_of_le (by linarith : a + (N : ℝ) ≤ (a + (N : ℝ)) + 1)]
        exact hsub2.continuousOn 0
      have hadd := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
      rw [Finset.sum_range_succ, hIH, Finset.sum_range_succ (f := fun n : ℕ =>
        dqptEMJ F (2 * m + 2) (a + n)) (n := N), hend, ← hadd, hcell]
      have hsumsplit : ∑ r ∈ Finset.range (m + 1),
            ((bernoulli (2 * r + 2) : ℚ) : ℝ) / (((2 * r + 2).factorial : ℕ) : ℝ)
              * (F (2 * r + 1) ((a + (N : ℝ)) + 1) - F (2 * r + 1) a)
          = ∑ r ∈ Finset.range (m + 1),
              ((bernoulli (2 * r + 2) : ℚ) : ℝ) / (((2 * r + 2).factorial : ℕ) : ℝ)
                * (F (2 * r + 1) (a + (N : ℝ)) - F (2 * r + 1) a)
            + ∑ r ∈ Finset.range (m + 1),
              ((bernoulli (2 * r + 2) : ℚ) : ℝ) / (((2 * r + 2).factorial : ℕ) : ℝ)
                * (F (2 * r + 1) ((a + (N : ℝ)) + 1) - F (2 * r + 1) (a + (N : ℝ))) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun r _ => by ring)
      rw [hsumsplit]
      ring

/-! ## The Bernoulli-polynomial bound on `[0,1]` -/

/-- `|B_{2k}(x)| ≤ |B_{2k}|` for `x ∈ [0,1]`: the input to the Euler–Maclaurin remainder bound. -/
theorem dqpt_abs_bernoulliFun_le {k : ℕ} (hk : k ≠ 0) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |bernoulliFun (2 * k) x| ≤ |((bernoulli (2 * k) : ℚ) : ℝ)| := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hfac : (0 : ℝ) < (((2 * k).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hsum := hasSum_one_div_nat_pow_mul_cos hk hx
  set C : ℝ := (-1 : ℝ) ^ (k + 1) * (2 * Real.pi) ^ (2 * k) / 2 / (((2 * k).factorial : ℕ) : ℝ)
    with hC
  have hsum' : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ (2 * k) * Real.cos (2 * Real.pi * n * x))
      (C * bernoulliFun (2 * k) x) := hsum
  have hzsum : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ (2 * k)) (dqptZetaEven k) :=
    (dqpt_summable_zetaEven hk).hasSum
  have hbnd : ∀ n : ℕ, ‖1 / (n : ℝ) ^ (2 * k) * Real.cos (2 * Real.pi * n * x)‖
      ≤ 1 / (n : ℝ) ^ (2 * k) := by
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ) ^ (2 * k))]
    have hcos : |Real.cos (2 * Real.pi * n * x)| ≤ 1 := Real.abs_cos_le_one _
    nlinarith [hcos, (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ) ^ (2 * k))]
  have hnorm : ‖C * bernoulliFun (2 * k) x‖ ≤ dqptZetaEven k := by
    rw [← hsum'.tsum_eq]
    exact tsum_of_norm_bounded hzsum hbnd
  have hCabs : |C| = (2 * Real.pi) ^ (2 * k) / (2 * (((2 * k).factorial : ℕ) : ℝ)) := by
    rw [hC, abs_div, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * Real.pi) ^ (2 * k)),
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ)),
      abs_of_nonneg (le_of_lt hfac)]
    field_simp
  have hCpos : 0 < |C| := by
    rw [hCabs]
    positivity
  have hkey : |C| * |bernoulliFun (2 * k) x| ≤ dqptZetaEven k := by
    rw [← abs_mul]
    exact hnorm
  have hidentity := dqpt_abs_bernoulli_eq hk
  rw [hidentity]
  rw [← le_div_iff₀' hCpos] at hkey
  refine hkey.trans (le_of_eq ?_)
  rw [hCabs]
  field_simp

end

end RHTower.DQPT
