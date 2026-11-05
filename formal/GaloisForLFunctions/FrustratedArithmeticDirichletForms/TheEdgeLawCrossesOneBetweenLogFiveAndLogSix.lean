import GaloisForLFunctions.FrustratedArithmeticDirichletForms.SoftEntryInEveryStageFibre

/-!
# The edge law of `ζ` crosses one between `log 5` and `log 6`

The edge-law constant `E_c(λ) = Σ_n |λ(n)|/(√n Ω(2c − log n))` (`SoftEntryInEveryStageFibre`) is the
size cost of the acting prime powers on `[−c, c]`; size-only certificates die once it reaches one
(`not_edgeLaw_of_one_le`). This module locates the crossing for `ζ`'s weights `Λ`.

* **Monotonicity** (`edgeLawConstant_mono`): `E_c(λ)` is nondecreasing in `c` — slivers widen, the
  Lévy tail `Ω` shrinks, and new powers enter at cost zero.
* **Two-sided tail at a sliver** (`levyTail_sliver_ge`, `levyTail_sliver_le`): at `δ = log(m/n)`,
  `2s ≤ Ω(δ) ≤ 2s + (2/5)s⁵/(1 − s⁴)` with `s = √(n/m)`.
* **The crossing** (`edgeLaw_threshold`): `E_c(Λ) < 1` for `2c ≤ log 5` and `E_c(Λ) ≥ 1` for
  `2c ≥ log 6`. At `2c = log 5` the bound is `E ≤ √5((3/8)log 2 + (1/6)log 3) < 0.9930`; at
  `2c = log 6` the primes `2, 3, 5` alone give `E ≥ √6((10/41)log 2 + (5/32)log 3 + (11/160)log 5) > 1.077`.

The review places the end of size payment at `log 5`, measured with the one-edge law
`|f⋆f(−ℓ)|Ω(2c − ℓ) ≤ 𝒥`. Paying each lag at both edges halves that cost, and the crossing moves into
`(log 5, log 6]`: from `log 6` on every size-only edge certificate for `ζ` fails
(`edgeLaw_fails_from_log_six`).

* **The exact threshold** (`exists_edgeLaw_threshold`). Each edge cost is continuous in the window,
  across its entry (`continuous_edgeCost`: `Ω → ∞` at the entry), and `E_c(Λ)` is strictly increasing
  once `2` acts (`Ω` strictly decreasing). So there is a unique `c* ∈ (½log 5, ½log 6]` with
  `E_{c*}(Λ) = 1`, and `E_c(Λ) < 1` exactly for `c < c*`.
-/

open MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.FrustratedArithmeticDirichletForms

open _root_.RHTower _root_.Zeta23

/-! ### Monotonicity in the window -/

theorem edgeCost_mono {c c' : ℝ} (hcc : c ≤ c') (lam : ℕ → ℝ) (n : ℕ) :
    edgeCost c lam n ≤ edgeCost c' lam n := by
  unfold edgeCost
  by_cases h : 2 ≤ n ∧ Real.log n < 2 * c
  · have h' : 2 ≤ n ∧ Real.log n < 2 * c' := ⟨h.1, by linarith [h.2]⟩
    rw [if_pos h, if_pos h']
    have hδ : 0 < 2 * c - Real.log n := by linarith [h.2]
    have hδ' : 0 < 2 * c' - Real.log n := by linarith [h.2]
    have hle : ∫ x in Ioi (2 * c' - Real.log n), archLevyDensity x ≤
        ∫ x in Ioi (2 * c - Real.log n), archLevyDensity x :=
      setIntegral_mono_set (WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi hδ)
        (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx =>
          (archLevyDensity_pos (lt_trans hδ hx)).le)
        (Ioi_subset_Ioi (by linarith)).eventuallyLE
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
    exact div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hsq (levyTail_pos hδ'))
      (mul_le_mul_of_nonneg_left hle hsq.le)
  · rw [if_neg h]
    exact edgeCost_nonneg c' lam n

/-- **The edge-law constant is nondecreasing in the window.** -/
theorem edgeLawConstant_mono {c c' : ℝ} (hcc : c ≤ c') (lam : ℕ → ℝ) :
    edgeLawConstant c lam ≤ edgeLawConstant c' lam := by
  unfold edgeLawConstant
  calc ∑ n ∈ Finset.range (⌊Real.exp (2 * c)⌋₊ + 1), edgeCost c lam n
      ≤ ∑ n ∈ Finset.range (⌊Real.exp (2 * c)⌋₊ + 1), edgeCost c' lam n :=
        Finset.sum_le_sum fun n _ => edgeCost_mono hcc lam n
    _ ≤ ∑ n ∈ Finset.range (⌊Real.exp (2 * c')⌋₊ + 1), edgeCost c' lam n :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr (Nat.add_le_add_right
            (Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith))) 1))
          fun n _ _ => edgeCost_nonneg c' lam n

/-! ### The Lévy tail at a sliver `log(m/n)` -/

theorem exp_half_log {x : ℝ} (hx : 0 < x) : Real.exp (Real.log x / 2) = Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
  congr 1
  ring

theorem exp_neg_half_sliver {n m : ℝ} (hn : 0 < n) (hm : 0 < m) :
    Real.exp (-(Real.log m - Real.log n) / 2) = Real.sqrt n / Real.sqrt m := by
  rw [show -(Real.log m - Real.log n) / 2 = Real.log n / 2 - Real.log m / 2 by ring, Real.exp_sub,
    exp_half_log hn, exp_half_log hm]

/-- `Ω(log(m/n)) ≥ 2√(n/m)`. -/
theorem levyTail_sliver_ge {n m : ℝ} (hn : 0 < n) (hnm : n < m) :
    2 * (Real.sqrt n / Real.sqrt m) ≤ ∫ x in Ioi (Real.log m - Real.log n), archLevyDensity x := by
  have h := SignedWindowCriticality.PrimeThreeEntry.two_mul_exp_le_levyTail
    (sub_pos.mpr (Real.log_lt_log hn hnm))
  rwa [exp_neg_half_sliver hn (hn.trans hnm)] at h

/-- `Ω(log(m/n)) ≤ 2s + (2/5)s⁵/(1 − s⁴)`, `s = √(n/m)`. -/
theorem levyTail_sliver_le {n m : ℝ} (hn : 0 < n) (hnm : n < m) :
    ∫ x in Ioi (Real.log m - Real.log n), archLevyDensity x ≤
      2 * (Real.sqrt n / Real.sqrt m) + (2 / 5) * (Real.sqrt n / Real.sqrt m) ^ 5 /
        (1 - (Real.sqrt n / Real.sqrt m) ^ 4) := by
  have hL : 0 < Real.log m - Real.log n := sub_pos.mpr (Real.log_lt_log hn hnm)
  have h := SignedWindowCriticality.PrimeThreeEntry.levyTail_le_exp hL
  have hs : Real.exp (-(1 / 2) * (Real.log m - Real.log n)) = Real.sqrt n / Real.sqrt m := by
    rw [← exp_neg_half_sliver hn (hn.trans hnm)]
    congr 1
    ring
  rw [show -(5 / 2) * (Real.log m - Real.log n) =
      ((5 : ℕ) : ℝ) * (-(1 / 2) * (Real.log m - Real.log n)) by push_cast; ring,
    show -2 * (Real.log m - Real.log n) =
      ((4 : ℕ) : ℝ) * (-(1 / 2) * (Real.log m - Real.log n)) by push_cast; ring,
    Real.exp_nat_mul, Real.exp_nat_mul, hs] at h
  exact h

/-! ### Edge costs at a window `2c = log m` -/

theorem edgeCost_eq_of_window {c m : ℝ} (hc : 2 * c = Real.log m) (lam : ℕ → ℝ) {n : ℕ}
    (hn : 2 ≤ n) (hnm : (n : ℝ) < m) :
    edgeCost c lam n =
      |lam n| / (Real.sqrt n * ∫ x in Ioi (Real.log m - Real.log n), archLevyDensity x) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  unfold edgeCost
  rw [if_pos ⟨hn, by rw [hc]; exact Real.log_lt_log hn0 hnm⟩, hc]

/-- Upper bound from `Ω ≥ 2√(n/m)`: `edgeCost ≤ |λ(n)|√m/(2n)`. -/
theorem edgeCost_le_of_window {c m : ℝ} (hc : 2 * c = Real.log m) (lam : ℕ → ℝ) {n : ℕ}
    (hn : 2 ≤ n) (hnm : (n : ℝ) < m) :
    edgeCost c lam n ≤ |lam n| * Real.sqrt m / (2 * n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm : 0 < m := hn0.trans hnm
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hΩ := levyTail_sliver_ge hn0 hnm
  have hsn2 : Real.sqrt n * (2 * (Real.sqrt n / Real.sqrt m)) = 2 * n / Real.sqrt m := by
    rw [show Real.sqrt n * (2 * (Real.sqrt n / Real.sqrt m)) =
      2 * (Real.sqrt n * Real.sqrt n) / Real.sqrt m by ring, Real.mul_self_sqrt hn0.le]
  rw [edgeCost_eq_of_window hc lam hn hnm]
  calc |lam n| / (Real.sqrt n * ∫ x in Ioi (Real.log m - Real.log n), archLevyDensity x)
      ≤ |lam n| / (Real.sqrt n * (2 * (Real.sqrt n / Real.sqrt m))) :=
        div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hsn (mul_pos two_pos (div_pos hsn hsm)))
          (mul_le_mul_of_nonneg_left hΩ hsn.le)
    _ = |lam n| * Real.sqrt m / (2 * n) := by rw [hsn2, div_div_eq_mul_div]

/-- Lower bound from the upper tail bound: `edgeCost ≥ |λ(n)|√m/(nK)`,
`K = 2 + (2/5)(n/m)²/(1 − (n/m)²)`. -/
theorem edgeCost_ge_of_window {c m : ℝ} (hc : 2 * c = Real.log m) (lam : ℕ → ℝ) {n : ℕ}
    (hn : 2 ≤ n) (hnm : (n : ℝ) < m) :
    |lam n| * Real.sqrt m /
        (n * (2 + (2 / 5) * ((n : ℝ) / m) ^ 2 / (1 - ((n : ℝ) / m) ^ 2))) ≤
      edgeCost c lam n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm : 0 < m := hn0.trans hnm
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hU := levyTail_sliver_le hn0 hnm
  have hΩpos := levyTail_pos (sub_pos.mpr (Real.log_lt_log hn0 hnm))
  have hs2 : (Real.sqrt n / Real.sqrt m) ^ 2 = n / m := by
    rw [div_pow, Real.sq_sqrt hn0.le, Real.sq_sqrt hm.le]
  have hq : (n : ℝ) / m < 1 := (div_lt_one hm).mpr hnm
  have hq0 : 0 < (n : ℝ) / m := div_pos hn0 hm
  have hd : 0 < 1 - ((n : ℝ) / m) ^ 2 := by nlinarith
  have hK0 : 0 < 2 + (2 / 5) * ((n : ℝ) / m) ^ 2 / (1 - ((n : ℝ) / m) ^ 2) := by positivity
  have hUK : 2 * (Real.sqrt n / Real.sqrt m) + (2 / 5) * (Real.sqrt n / Real.sqrt m) ^ 5 /
      (1 - (Real.sqrt n / Real.sqrt m) ^ 4) = (Real.sqrt n / Real.sqrt m) *
        (2 + (2 / 5) * ((n : ℝ) / m) ^ 2 / (1 - ((n : ℝ) / m) ^ 2)) := by
    rw [show (Real.sqrt n / Real.sqrt m) ^ 5 =
        (Real.sqrt n / Real.sqrt m) * ((Real.sqrt n / Real.sqrt m) ^ 2) ^ 2 by ring,
      show (Real.sqrt n / Real.sqrt m) ^ 4 = ((Real.sqrt n / Real.sqrt m) ^ 2) ^ 2 by ring, hs2]
    ring
  have hsnK : Real.sqrt n * ((Real.sqrt n / Real.sqrt m) *
      (2 + (2 / 5) * ((n : ℝ) / m) ^ 2 / (1 - ((n : ℝ) / m) ^ 2))) =
        n * (2 + (2 / 5) * ((n : ℝ) / m) ^ 2 / (1 - ((n : ℝ) / m) ^ 2)) / Real.sqrt m := by
    rw [show Real.sqrt n * ((Real.sqrt n / Real.sqrt m) *
        (2 + (2 / 5) * ((n : ℝ) / m) ^ 2 / (1 - ((n : ℝ) / m) ^ 2))) =
        (Real.sqrt n * Real.sqrt n) * (2 + (2 / 5) * ((n : ℝ) / m) ^ 2 /
          (1 - ((n : ℝ) / m) ^ 2)) / Real.sqrt m by ring, Real.mul_self_sqrt hn0.le]
  rw [edgeCost_eq_of_window hc lam hn hnm]
  calc |lam n| * Real.sqrt m /
        (n * (2 + (2 / 5) * ((n : ℝ) / m) ^ 2 / (1 - ((n : ℝ) / m) ^ 2)))
      = |lam n| / (Real.sqrt n * ((Real.sqrt n / Real.sqrt m) *
          (2 + (2 / 5) * ((n : ℝ) / m) ^ 2 / (1 - ((n : ℝ) / m) ^ 2)))) := by
        rw [hsnK, div_div_eq_mul_div]
    _ ≤ |lam n| / (Real.sqrt n * ∫ x in Ioi (Real.log m - Real.log n), archLevyDensity x) :=
        div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hsn hΩpos)
          (mul_le_mul_of_nonneg_left (hU.trans_eq hUK) hsn.le)

/-! ### The weights of `ζ` and the constants -/

theorem vonMangoldt_two_real : (ArithmeticFunction.vonMangoldt 2 : ℝ) = Real.log 2 := by
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]; norm_num

theorem vonMangoldt_three_real : (ArithmeticFunction.vonMangoldt 3 : ℝ) = Real.log 3 := by
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]; norm_num

theorem vonMangoldt_four_real : (ArithmeticFunction.vonMangoldt 4 : ℝ) = Real.log 2 := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num

theorem vonMangoldt_five_real : (ArithmeticFunction.vonMangoldt 5 : ℝ) = Real.log 5 := by
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_five]; norm_num

/-- `log x ≤ x/e`, from `log y ≤ y − 1` at `y = x/e`. -/
theorem log_le_div_exp_one {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / Real.exp 1 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < x / Real.exp 1 by positivity)
  rw [Real.log_div hx.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
  linarith

/-- `log x ≥ 2 − e/x`, from `log y ≤ y − 1` at `y = e/x`. -/
theorem two_sub_exp_one_div_le_log {x : ℝ} (hx : 0 < x) : 2 - Real.exp 1 / x ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (show 0 < Real.exp 1 / x by positivity)
  rw [Real.log_div (Real.exp_pos 1).ne' hx.ne', Real.log_exp] at h
  linarith

/-! ### The crossing -/

/-- **Below `log 5` the edge cost of `ζ` is less than one**: at `2c = log 5`,
`E_c(Λ) ≤ √5((3/8)log 2 + (1/6)log 3) < 1`. -/
theorem edgeLawConstant_vonMangoldt_lt_one {c : ℝ} (hc : 2 * c = Real.log 5) :
    edgeLawConstant c (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) < 1 := by
  have hfl : ⌊Real.exp (2 * c)⌋₊ + 1 = 6 := by
    rw [hc, Real.exp_log (by norm_num)]
    norm_num [Nat.floor_ofNat]
  unfold edgeLawConstant
  rw [hfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have e0 : edgeCost c (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) 0 = 0 := by
    unfold edgeCost; simp
  have e1 : edgeCost c (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) 1 = 0 := by
    unfold edgeCost; simp
  have e5 : edgeCost c (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) 5 = 0 := by
    unfold edgeCost; rw [hc]; simp
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have b2 := edgeCost_le_of_window hc (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    (n := 2) le_rfl (by norm_num)
  have b3 := edgeCost_le_of_window hc (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    (n := 3) (by norm_num) (by norm_num)
  have b4 := edgeCost_le_of_window hc (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    (n := 4) (by norm_num) (by norm_num)
  simp only [vonMangoldt_two_real, vonMangoldt_three_real, vonMangoldt_four_real,
    abs_of_pos hl2, abs_of_pos hl3, Nat.cast_ofNat] at b2 b3 b4
  rw [e0, e1, e5]
  have hs5 : Real.sqrt 5 ≤ 2.237 := by
    have h := Real.sqrt_le_sqrt (show (5 : ℝ) ≤ 2.237 ^ 2 by norm_num)
    rwa [Real.sqrt_sq (by norm_num)] at h
  have he := Real.exp_one_gt_d9
  have hl3e := log_le_div_exp_one (show (0 : ℝ) < 3 by norm_num)
  have h3e : 3 / Real.exp 1 ≤ 3 / 2.7182818283 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) he.le
  have hl2u := Real.log_two_lt_d9
  have hT : (3 / 8) * Real.log 2 + (1 / 6) * Real.log 3 ≤ 0.4438703 := by
    norm_num at h3e hl2u ⊢
    linarith
  have hkey := mul_le_mul hs5 hT (by positivity) (by norm_num)
  norm_num at hkey
  nlinarith

/-- **From `log 6` on the edge cost of `ζ` is at least one**: at `2c = log 6` the primes `2, 3, 5`
give `E_c(Λ) ≥ √6((10/41)log 2 + (5/32)log 3 + (11/160)log 5) > 1`. -/
theorem one_le_edgeLawConstant_vonMangoldt_at_log_six {c : ℝ} (hc : 2 * c = Real.log 6) :
    1 ≤ edgeLawConstant c (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) := by
  have hfl : ⌊Real.exp (2 * c)⌋₊ + 1 = 7 := by
    rw [hc, Real.exp_log (by norm_num)]
    norm_num [Nat.floor_ofNat]
  unfold edgeLawConstant
  rw [hfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h0 := edgeCost_nonneg c (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) 0
  have h1 := edgeCost_nonneg c (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) 1
  have h4 := edgeCost_nonneg c (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) 4
  have h6 := edgeCost_nonneg c (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) 6
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hl5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have b2 := edgeCost_ge_of_window hc (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    (n := 2) le_rfl (by norm_num)
  have b3 := edgeCost_ge_of_window hc (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    (n := 3) (by norm_num) (by norm_num)
  have b5 := edgeCost_ge_of_window hc (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    (n := 5) (by norm_num) (by norm_num)
  simp only [vonMangoldt_two_real, vonMangoldt_three_real, vonMangoldt_five_real,
    abs_of_pos hl2, abs_of_pos hl3, abs_of_pos hl5, Nat.cast_ofNat] at b2 b3 b5
  norm_num at b2 b3 b5
  have hs6 : 2.449 ≤ Real.sqrt 6 := by
    have h := Real.sqrt_le_sqrt (show (2.449 : ℝ) ^ 2 ≤ 6 by norm_num)
    rwa [Real.sqrt_sq (by norm_num)] at h
  have he := Real.exp_one_lt_d9
  have hl3e := two_sub_exp_one_div_le_log (show (0 : ℝ) < 3 by norm_num)
  have hl5e := two_sub_exp_one_div_le_log (show (0 : ℝ) < 5 by norm_num)
  have hl2l := Real.log_two_gt_d9
  have hS : 0.4401 ≤ (10 / 41) * Real.log 2 + (5 / 32) * Real.log 3 + (11 / 160) * Real.log 5 := by
    norm_num at hl2l ⊢
    linarith
  have hkey := mul_le_mul hs6 hS (by norm_num) (Real.sqrt_nonneg 6)
  norm_num at hkey
  nlinarith

/-- **The edge law of `ζ` crosses one between `log 5` and `log 6`.** -/
theorem edgeLaw_threshold :
    (∀ c : ℝ, 2 * c ≤ Real.log 5 →
      edgeLawConstant c (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) < 1) ∧
    ∀ c : ℝ, Real.log 6 ≤ 2 * c →
      1 ≤ edgeLawConstant c (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) :=
  ⟨fun c hc => (edgeLawConstant_mono (show c ≤ Real.log 5 / 2 by linarith) _).trans_lt
      (edgeLawConstant_vonMangoldt_lt_one (by ring)),
    fun c hc => (one_le_edgeLawConstant_vonMangoldt_at_log_six
      (show 2 * (Real.log 6 / 2) = Real.log 6 by ring)).trans
        (edgeLawConstant_mono (show Real.log 6 / 2 ≤ c by linarith) _)⟩

/-- From `log 6` on, size cannot pay `ζ`'s primes: on every window with `2c ≥ log 6` a real test has
`H(f) < E_c(Λ)𝒥(f)`. -/
theorem edgeLaw_fails_from_log_six {c : ℝ} (hc : Real.log 6 ≤ 2 * c) :
    ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ tsupport (fun u => (f u : ℂ)) ⊆ Icc (-c) c ∧
      (weilFullFunctional (fun _ => 0)
          (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re <
        edgeLawConstant c (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) * levyEnergy f :=
  not_edgeLaw_of_one_le (by linarith [Real.log_pos (show (1 : ℝ) < 6 by norm_num)])
    (edgeLaw_threshold.2 c hc)

/-! ### Continuity and the exact threshold -/

/-- The Lévy tail is continuous on `(0, ∞)`: it is the elementary antiderivative
`archLevyAntideriv`. -/
theorem continuousOn_levyTail :
    ContinuousOn (fun δ => ∫ x in Ioi δ, archLevyDensity x) (Ioi 0) := fun _ hδ =>
  (WeilLevyPoleGauss.hasDerivAt_archLevyAntideriv hδ).continuousAt.continuousWithinAt.congr
    (fun _ hy => WeilLevyCoshCrossover.integral_archLevyDensity_Ioi hy)
    (WeilLevyCoshCrossover.integral_archLevyDensity_Ioi hδ)

/-- The Lévy tail is strictly decreasing on `(0, ∞)` (`Ω′ = −ω < 0`). -/
theorem strictAntiOn_levyTail :
    StrictAntiOn (fun δ => ∫ x in Ioi δ, archLevyDensity x) (Ioi 0) := by
  have h : StrictAntiOn WeilLevyPoleGauss.archLevyAntideriv (Ioi 0) :=
    strictAntiOn_of_deriv_neg (convex_Ioi 0)
      (fun _ hδ => (WeilLevyPoleGauss.hasDerivAt_archLevyAntideriv hδ).continuousAt.continuousWithinAt)
      (fun x hx => by
        rw [interior_Ioi] at hx
        rw [(WeilLevyPoleGauss.hasDerivAt_archLevyAntideriv hx).deriv]
        linarith [archLevyDensity_pos (show (0 : ℝ) < x from hx)])
  intro a ha b hb hab
  show (∫ x in Ioi b, archLevyDensity x) < ∫ x in Ioi a, archLevyDensity x
  rw [WeilLevyCoshCrossover.integral_archLevyDensity_Ioi ha,
    WeilLevyCoshCrossover.integral_archLevyDensity_Ioi hb]
  exact h ha hb hab

/-- The Lévy tail blows up at the entry: `Ω(δ) → ∞` as `δ ↓ 0`. -/
theorem tendsto_levyTail_atTop :
    Tendsto (fun δ => ∫ x in Ioi δ, archLevyDensity x) (𝓝[>] 0) atTop := by
  have hL : Tendsto (fun δ : ℝ => Real.exp (-1 / 2) / 2 * Real.log δ⁻¹) (𝓝[>] 0) atTop :=
    (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero).const_mul_atTop (by positivity)
  refine tendsto_atTop_mono' _ ?_ hL
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hδ
  have h := SignedWindowCriticality.PrimeThreeEntry.levyTail_ge_log hδ.1 hδ.2.le
  rwa [one_div] at h

/-- The edge gate `G(δ) = 1/Ω(δ)` for `δ > 0`, `0` otherwise: the edge cost per unit weight. -/
def edgeGate (δ : ℝ) : ℝ := if 0 < δ then (∫ x in Ioi δ, archLevyDensity x)⁻¹ else 0

/-- **The edge gate is continuous**, also at `δ = 0`: an entering power costs nothing. -/
theorem continuous_edgeGate : Continuous edgeGate := by
  refine continuous_iff_continuousAt.mpr fun δ => ?_
  rcases lt_trichotomy δ 0 with h | h | h
  · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [Iio_mem_nhds h] with y hy
    show (0 : ℝ) = if 0 < y then _ else 0
    rw [if_neg (not_lt.mpr (le_of_lt hy))]
  · subst h
    have h0 : edgeGate 0 = 0 := if_neg (lt_irrefl 0)
    show Tendsto edgeGate (𝓝 0) (𝓝 (edgeGate 0))
    rw [h0]
    have hA : Tendsto edgeGate (𝓝[≤] (0 : ℝ)) (𝓝 0) := by
      refine (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≤] 0) (𝓝 0)).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      show (0 : ℝ) = if 0 < y then _ else 0
      rw [if_neg (not_lt.mpr (show y ≤ 0 from hy))]
    have hB : Tendsto edgeGate (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine tendsto_levyTail_atTop.inv_tendsto_atTop.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      show (∫ x in Ioi y, archLevyDensity x)⁻¹ = if 0 < y then _ else 0
      rw [if_pos (show (0 : ℝ) < y from hy)]
    have hAB := hA.sup hB
    rwa [nhdsLE_sup_nhdsGT] at hAB
  · refine ((continuousOn_levyTail.continuousAt (Ioi_mem_nhds h)).inv₀
      (levyTail_pos h).ne').congr ?_
    filter_upwards [Ioi_mem_nhds h] with y hy
    show (∫ x in Ioi y, archLevyDensity x)⁻¹ = if 0 < y then _ else 0
    rw [if_pos (show (0 : ℝ) < y from hy)]

theorem edgeCost_eq_gate (lam : ℕ → ℝ) {n : ℕ} (hn : 2 ≤ n) (c : ℝ) :
    edgeCost c lam n = |lam n| / Real.sqrt n * edgeGate (2 * c - Real.log n) := by
  unfold edgeCost edgeGate
  by_cases h : Real.log n < 2 * c
  · rw [if_pos ⟨hn, h⟩, if_pos (by linarith)]
    ring
  · rw [if_neg (fun h' => h h'.2), if_neg (by linarith), mul_zero]

/-- **Each edge cost is continuous in the window**, across its entry. -/
theorem continuous_edgeCost (lam : ℕ → ℝ) (n : ℕ) : Continuous fun c => edgeCost c lam n := by
  by_cases hn : 2 ≤ n
  · simp_rw [edgeCost_eq_gate lam hn]
    exact continuous_const.mul
      (continuous_edgeGate.comp (by fun_prop : Continuous fun c : ℝ => 2 * c - Real.log n))
  · have e : (fun c => edgeCost c lam n) = fun _ => 0 := by
      funext c
      unfold edgeCost
      rw [if_neg (fun h => hn h.1)]
    rw [e]
    exact continuous_const

/-- Past the window's reach the edge costs vanish, so any longer range of summation gives `E_c`. -/
theorem edgeLawConstant_eq_sum {c : ℝ} (lam : ℕ → ℝ) {N : ℕ}
    (hN : ⌊Real.exp (2 * c)⌋₊ + 1 ≤ N) :
    edgeLawConstant c lam = ∑ n ∈ Finset.range N, edgeCost c lam n := by
  unfold edgeLawConstant
  refine Finset.sum_subset (Finset.range_subset_range.mpr hN) fun n _ hn' => ?_
  rw [Finset.mem_range, not_lt] at hn'
  unfold edgeCost
  rw [if_neg]
  rintro ⟨h2, hlt⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlt' : Real.exp (2 * c) < n := by
    have := Nat.lt_floor_add_one (Real.exp (2 * c))
    have h' : ((⌊Real.exp (2 * c)⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn'
    push_cast at h'
    linarith
  have := (Real.lt_log_iff_exp_lt hn0).mpr hlt'
  linarith

/-- **`E_c(Λ)` is strictly increasing once the prime `2` acts.** -/
theorem strictMonoOn_edgeLawConstant_vonMangoldt :
    StrictMonoOn (fun c => edgeLawConstant c (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)))
      (Ioi (Real.log 2 / 2)) := by
  intro c hc c' hc' hcc
  simp only [mem_Ioi] at hc hc'
  show edgeLawConstant c (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) <
    edgeLawConstant c' (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
  have hNc : ⌊Real.exp (2 * c)⌋₊ + 1 ≤ ⌊Real.exp (2 * c')⌋₊ + 1 :=
    Nat.add_le_add_right (Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith))) 1
  rw [edgeLawConstant_eq_sum _ hNc, edgeLawConstant_eq_sum _ le_rfl]
  have h2mem : 2 ∈ Finset.range (⌊Real.exp (2 * c')⌋₊ + 1) := by
    rw [Finset.mem_range, Nat.lt_succ_iff]
    refine Nat.le_floor ?_
    have : Real.exp (Real.log 2) ≤ Real.exp (2 * c') := Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_log (by norm_num)] at this
    exact_mod_cast this
  refine Finset.sum_lt_sum (fun n _ => edgeCost_mono hcc.le _ n) ⟨2, h2mem, ?_⟩
  have hδ : 0 < 2 * c - Real.log 2 := by linarith
  have hδ' : 0 < 2 * c' - Real.log 2 := by linarith
  have hlt : (∫ x in Ioi (2 * c' - Real.log 2), archLevyDensity x) <
      ∫ x in Ioi (2 * c - Real.log 2), archLevyDensity x :=
    strictAntiOn_levyTail hδ hδ' (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsq : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [edgeCost_eq_gate _ le_rfl, edgeCost_eq_gate _ le_rfl]
  simp only [vonMangoldt_two_real, abs_of_pos hl2, Nat.cast_ofNat, edgeGate, if_pos hδ, if_pos hδ']
  exact mul_lt_mul_of_pos_left ((inv_lt_inv₀ (levyTail_pos hδ) (levyTail_pos hδ')).mpr hlt)
    (div_pos hl2 hsq)

/-- **The exact threshold of the edge law of `ζ`.** There is a unique window `c*` with
`E_{c*}(Λ) = 1`; it lies in `(½log 5, ½log 6]`, and `E_c(Λ) < 1` exactly for `c < c*`. -/
theorem exists_edgeLaw_threshold :
    ∃ cs : ℝ, Real.log 5 / 2 < cs ∧ cs ≤ Real.log 6 / 2 ∧
      edgeLawConstant cs (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) = 1 ∧
      ∀ c : ℝ, edgeLawConstant c (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) < 1 ↔ c < cs := by
  have h56 : Real.log 5 < Real.log 6 := Real.log_lt_log (by norm_num) (by norm_num)
  have h25 : Real.log 2 < Real.log 5 := Real.log_lt_log (by norm_num) (by norm_num)
  have hab : Real.log 5 / 2 ≤ Real.log 6 / 2 := by linarith
  have hEa : edgeLawConstant (Real.log 5 / 2) (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) < 1 :=
    edgeLawConstant_vonMangoldt_lt_one (by ring)
  have hEb : 1 ≤ edgeLawConstant (Real.log 6 / 2) (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) :=
    one_le_edgeLawConstant_vonMangoldt_at_log_six (by ring)
  have hcont : ContinuousOn (fun c => edgeLawConstant c (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)))
      (Icc (Real.log 5 / 2) (Real.log 6 / 2)) := by
    refine ContinuousOn.congr (f := fun c => ∑ n ∈ Finset.range 7,
      edgeCost c (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) n)
      (continuous_finsetSum _ fun n _ => continuous_edgeCost _ n).continuousOn fun c hc => ?_
    refine edgeLawConstant_eq_sum _ ?_
    have h6 : Real.exp (2 * c) ≤ 6 := by
      calc Real.exp (2 * c) ≤ Real.exp (Real.log 6) := Real.exp_le_exp.mpr (by linarith [hc.2])
        _ = 6 := Real.exp_log (by norm_num)
    have := Nat.floor_le_floor h6
    rw [Nat.floor_ofNat] at this
    omega
  obtain ⟨cs, hcs, hEcs⟩ := intermediate_value_Icc hab hcont ⟨hEa.le, hEb⟩
  have hEcs' : edgeLawConstant cs (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) = 1 := hEcs
  have hacs : Real.log 5 / 2 < cs := lt_of_le_of_ne hcs.1 fun h => by
    rw [← h] at hEcs'
    linarith
  refine ⟨cs, hacs, hcs.2, hEcs', fun c => ⟨fun hc => ?_, fun hc => ?_⟩⟩
  · by_contra h
    push Not at h
    have := edgeLawConstant_mono h (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    linarith
  · by_cases hca : c ≤ Real.log 5 / 2
    · exact (edgeLawConstant_mono hca _).trans_lt hEa
    · push Not at hca
      have h' : edgeLawConstant c (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) <
          edgeLawConstant cs (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) :=
        strictMonoOn_edgeLawConstant_vonMangoldt (show c ∈ Ioi (Real.log 2 / 2) by
          simp only [mem_Ioi]; linarith) (show cs ∈ Ioi (Real.log 2 / 2) by
          simp only [mem_Ioi]; linarith) hc
      linarith

end GaloisForLFunctions.FrustratedArithmeticDirichletForms
