import GaloisForLFunctions.RHTower.RiemannKernelModulatedWindowTests
import GaloisForLFunctions.RHTower.WeilFullConeDyadicRigidity

/-!
# Weil-cone rigidity on lacunary sets of ratio `3/2`

**Theorem** (`eq_vonMangoldt_of_weilPositiveFull_of_threeHalves_lacunary`, unconditional). Let `lam`
be full-cone Weil-positive (`WeilPositiveFull`). Suppose `lam m = Λ(m)` for every `m ≥ 2` outside a
set `n 0 < n 1 < ⋯` with `n 0 ≥ 2` and `3 n i ≤ 2 n (i+1)`. Then `lam = Λ`. The deviations on the set
are arbitrary a priori: any sign, any size up to the universal box `|lam(m)| ≤ √m(log m + C₀)`.

This extends `eq_vonMangoldt_of_weilPositiveFull_of_lacunary` (ratio `3`) and
`eq_vonMangoldt_of_weilPositiveFull_of_powers_two` (the powers of `2`) to every lacunary sequence of
ratio `3/2`.

**The test.** The window tests of `RiemannKernelModulatedWindowTests` with `L = 163/100`,
`η = 3/1000` (so `L + η` stays inside the zero-free window `|t| ≤ 10.26` of `Ξ`) and modulation
frequency `a = log n_j`. The deviation `v = (Λ − lam)/√m` then satisfies
`Σ_m v(m)[2B(η log m)W(log m) + σ(B(η(log m + a))W(log m + a) + B(η(log m − a))W(log m − a))] ≥ 0`
for `σ = ±1`, where `W(z) = L sin(πu)/(πu(1 − u²))`, `u = 2Lz`, and `|B| ≤ B(0)`.

**The contraction.** Put `M = sup_i |v(n_i)|/(12 + log n_i)` (finite by the box). With the cubic
majorants `|W(z)| ≤ L c/|z|³` (`abs_W_le_cube_*`) and the log-gaps `log n_i − log n_j ≥ (2/5)(i − j)`,
positivity at the atom `n_j` with `σ = −sign v(n_j)` gives `|v(n_j)| ≤ (97/100) M (12 + log n_j)`
(`threeHalves_atom_le`). Taking the supremum gives `M = 0`.

**Reach.** The resolution comes from the zero-free window of `Ξ`, not from the width of `K = Φ⋆Φ̃`.
On the full zero-free window `|t| < 14.13` the same contraction reaches ratio `4/3`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace RHTower

noncomputable section

/-! ## Tails, box and lacunary facts -/


/-- Telescoping cube tail: `Σ_{m ≥ a} 1/m³ ≤ 1/(2(a−1)a)`. -/
theorem tsum_inv_nat_add_cube_le (a : ℕ) (ha : 2 ≤ a) :
    Summable (fun i : ℕ => 1 / ((i + a : ℕ) : ℝ) ^ 3) ∧
      ∑' i : ℕ, 1 / ((i + a : ℕ) : ℝ) ^ 3 ≤ 1 / (2 * ((a : ℝ) - 1) * a) := by
  have ha1 : (1 : ℝ) < a := by exact_mod_cast (by omega : 1 < a)
  set T : ℕ → ℝ := fun i => 1 / (2 * (((i + a : ℕ) : ℝ) - 1) * ((i + a : ℕ) : ℝ)) with hT
  have hstep : ∀ i : ℕ, 1 / ((i + a : ℕ) : ℝ) ^ 3 ≤ T i - T (i + 1) := by
    intro i
    simp only [hT]
    set m : ℝ := ((i + a : ℕ) : ℝ) with hm
    have hm' : ((i + 1 + a : ℕ) : ℝ) = m + 1 := by rw [hm]; push_cast; ring
    rw [hm']
    have hm1 : 1 < m := by rw [hm]; push_cast; have : (0:ℝ) ≤ i := Nat.cast_nonneg i; linarith
    rw [show m + 1 - 1 = m by ring]
    have hm0 : 0 < m - 1 := by linarith
    have hmp : 0 < m := by linarith
    have e : 1 / (2 * (m - 1) * m) - 1 / (2 * m * (m + 1)) = 1 / ((m - 1) * m * (m + 1)) := by
      field_simp; ring
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hnn : ∀ i : ℕ, 0 ≤ 1 / ((i + a : ℕ) : ℝ) ^ 3 := fun i => by positivity
  have hpart : ∀ N : ℕ, ∑ i ∈ Finset.range N, 1 / ((i + a : ℕ) : ℝ) ^ 3 ≤ T 0 := by
    intro N
    have htel : ∑ i ∈ Finset.range N, (T i - T (i + 1)) = T 0 - T N :=
      Finset.sum_range_sub' T N
    have hTN : 0 ≤ T N := by
      simp only [hT]
      have : (1 : ℝ) < ((N + a : ℕ) : ℝ) := by push_cast; have := Nat.cast_nonneg (α := ℝ) N; linarith
      have : 0 < ((N + a : ℕ) : ℝ) - 1 := by linarith
      positivity
    calc ∑ i ∈ Finset.range N, 1 / ((i + a : ℕ) : ℝ) ^ 3
        ≤ ∑ i ∈ Finset.range N, (T i - T (i + 1)) := Finset.sum_le_sum fun i _ => hstep i
      _ = T 0 - T N := htel
      _ ≤ T 0 := by linarith
  have hs : Summable (fun i : ℕ => 1 / ((i + a : ℕ) : ℝ) ^ 3) :=
    summable_of_sum_range_le hnn hpart
  refine ⟨hs, (Real.tsum_le_of_sum_range_le hnn hpart).trans (le_of_eq ?_)⟩
  simp only [hT]; push_cast; ring_nf

/-- Telescoping square tail: `Σ_{m ≥ a} 1/m² ≤ 1/(a−1)`. -/
theorem tsum_inv_nat_add_sq_le (a : ℕ) (ha : 2 ≤ a) :
    Summable (fun i : ℕ => 1 / ((i + a : ℕ) : ℝ) ^ 2) ∧
      ∑' i : ℕ, 1 / ((i + a : ℕ) : ℝ) ^ 2 ≤ 1 / ((a : ℝ) - 1) := by
  have ha1 : (1 : ℝ) < a := by exact_mod_cast (by omega : 1 < a)
  set T : ℕ → ℝ := fun i => 1 / (((i + a : ℕ) : ℝ) - 1) with hT
  have hstep : ∀ i : ℕ, 1 / ((i + a : ℕ) : ℝ) ^ 2 ≤ T i - T (i + 1) := by
    intro i
    simp only [hT]
    set m : ℝ := ((i + a : ℕ) : ℝ) with hm
    have hm' : ((i + 1 + a : ℕ) : ℝ) = m + 1 := by rw [hm]; push_cast; ring
    rw [hm']
    have hm1 : 1 < m := by rw [hm]; push_cast; have : (0:ℝ) ≤ i := Nat.cast_nonneg i; linarith
    rw [show m + 1 - 1 = m by ring, div_sub_div _ _ (by linarith) (by linarith),
      div_le_div_iff₀ (by positivity) (by nlinarith)]
    nlinarith
  have hnn : ∀ i : ℕ, 0 ≤ 1 / ((i + a : ℕ) : ℝ) ^ 2 := fun i => by positivity
  have hpart : ∀ N : ℕ, ∑ i ∈ Finset.range N, 1 / ((i + a : ℕ) : ℝ) ^ 2 ≤ T 0 := by
    intro N
    have htel : ∑ i ∈ Finset.range N, (T i - T (i + 1)) = T 0 - T N :=
      Finset.sum_range_sub' T N
    have hTN : 0 ≤ T N := by
      simp only [hT]
      have : (1 : ℝ) < ((N + a : ℕ) : ℝ) := by push_cast; have := Nat.cast_nonneg (α := ℝ) N; linarith
      have : 0 < ((N + a : ℕ) : ℝ) - 1 := by linarith
      positivity
    calc ∑ i ∈ Finset.range N, 1 / ((i + a : ℕ) : ℝ) ^ 2
        ≤ ∑ i ∈ Finset.range N, (T i - T (i + 1)) := Finset.sum_le_sum fun i _ => hstep i
      _ = T 0 - T N := htel
      _ ≤ T 0 := by linarith
  have hs : Summable (fun i : ℕ => 1 / ((i + a : ℕ) : ℝ) ^ 2) :=
    summable_of_sum_range_le hnn hpart
  refine ⟨hs, (Real.tsum_le_of_sum_range_le hnn hpart).trans (le_of_eq ?_)⟩
  simp only [hT]; push_cast; ring_nf



/-- **The universal box in logarithmic form.** -/
theorem exists_abs_normDeficit_le_log {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m : ℕ, |normDeficit lam m| ≤ B * (1 + |Real.log m|) := by
  obtain ⟨C₀, hC₀⟩ := abs_le_of_weilPositive (weilPositive_of_weilPositiveFull hW)
  refine ⟨2 + |C₀|, by positivity, fun m => ?_⟩
  by_cases hm : 2 ≤ m
  · have hsq1 : 1 ≤ Real.sqrt m := by
      rw [Real.one_le_sqrt]; exact_mod_cast (by omega : 1 ≤ m)
    have hsq0 : 0 < Real.sqrt m := by linarith
    have hlog0 := Real.log_natCast_nonneg m
    have hΛ := ArithmeticFunction.vonMangoldt_le_log (n := m)
    have hΛ0 : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt m := ArithmeticFunction.vonMangoldt_nonneg
    have hl := hC₀ m hm
    simp only [normDeficit, if_pos hm]
    rw [abs_div, abs_of_pos hsq0, div_le_iff₀ hsq0, abs_of_nonneg hlog0]
    have h1 : |(ArithmeticFunction.vonMangoldt m : ℝ) - lam m| ≤
        Real.log m + Real.sqrt m * (Real.log m + C₀) := by
      calc _ ≤ |(ArithmeticFunction.vonMangoldt m : ℝ)| + |lam m| := abs_sub _ _
        _ ≤ _ := by rw [abs_of_nonneg hΛ0]; linarith
    have h2 : Real.log m ≤ Real.log m * Real.sqrt m := le_mul_of_one_le_right hlog0 hsq1
    have h3 : C₀ ≤ |C₀| := le_abs_self C₀
    have h4 : Real.sqrt m * C₀ ≤ Real.sqrt m * |C₀| := mul_le_mul_of_nonneg_left h3 hsq0.le
    have h5 : 0 ≤ Real.sqrt m * |C₀| * Real.log m := by positivity
    have h6 : 0 ≤ Real.sqrt m * |C₀| := by positivity
    nlinarith
  · simp only [normDeficit, if_neg hm, abs_zero]; positivity

/-! ## Three-halves lacunary sequences -/

theorem threeHalves_pow_mul_le {n : ℕ → ℕ} (hs : ∀ i, 3 * n i ≤ 2 * n (i + 1)) (i k : ℕ) :
    (3 / 2 : ℝ) ^ k * (n i : ℝ) ≤ n (i + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := hs (i + k)
    have h' : (3 : ℝ) * n (i + k) ≤ 2 * n (i + k + 1) := by exact_mod_cast h
    rw [pow_succ, show i + (k + 1) = i + k + 1 by ring]
    nlinarith

theorem two_le_threeHalvesLacunary {n : ℕ → ℕ} (h0 : 2 ≤ n 0) (hs : ∀ i, 3 * n i ≤ 2 * n (i + 1)) (i : ℕ) :
    2 ≤ n i := by
  have h := threeHalves_pow_mul_le hs 0 i
  rw [zero_add] at h
  have h1 : (1 : ℝ) ≤ (3 / 2) ^ i := one_le_pow₀ (by norm_num)
  have h2 : (2 : ℝ) ≤ n 0 := by exact_mod_cast h0
  have : (2 : ℝ) ≤ n i := by nlinarith
  exact_mod_cast this

theorem two_fifths_le_log_three_halves : (2 / 5 : ℝ) ≤ Real.log (3 / 2) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_bound' (x := 2 / 5) (by norm_num) (by norm_num) (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at this
  linarith

theorem log_threeHalvesLacunary_add_sub_ge {n : ℕ → ℕ} (h0 : 2 ≤ n 0) (hs : ∀ i, 3 * n i ≤ 2 * n (i + 1))
    (i k : ℕ) : (k : ℝ) * (2 / 5) ≤ Real.log (n (i + k)) - Real.log (n i) := by
  have hpos : (0 : ℝ) < n i := by
    have := two_le_threeHalvesLacunary h0 hs i; exact_mod_cast (by omega : 0 < n i)
  have h := threeHalves_pow_mul_le hs i k
  have hl := Real.log_le_log (by positivity) h
  rw [Real.log_mul (by positivity) hpos.ne', Real.log_pow] at hl
  have := two_fifths_le_log_three_halves
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

theorem log_threeHalvesLacunary_ge {n : ℕ → ℕ} (h0 : 2 ≤ n 0) (hs : ∀ i, 3 * n i ≤ 2 * n (i + 1)) (i : ℕ) :
    6931 / 10000 + (i : ℝ) * (2 / 5) ≤ Real.log (n i) := by
  have h := log_threeHalvesLacunary_add_sub_ge h0 hs 0 i
  rw [zero_add] at h
  have h2 : Real.log 2 ≤ Real.log (n 0) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast h0)
  have := Real.log_two_gt_d9
  linarith

theorem threeHalvesLacunary_strictMono {n : ℕ → ℕ} (h0 : 2 ≤ n 0) (hs : ∀ i, 3 * n i ≤ 2 * n (i + 1)) :
    StrictMono n := by
  refine strictMono_nat_of_lt_succ fun i => ?_
  have := hs i; have := two_le_threeHalvesLacunary h0 hs i; omega


/-! ## Cubic majorants of the window transform at `L = 163/100` -/

theorem abs_cosSqWindowTransform_le_cube {y₀ c : ℝ} (hy₀ : 1 < 163 / 50 * y₀)
    (hc : 1 ≤ c * (π * (163 / 50) ^ 3 * (1 - 1 / (163 / 50 * y₀) ^ 2))) {y : ℝ} (hy : y₀ ≤ |y|) :
    |cosSqWindowTransform (163 / 100) y| ≤ 163 / 100 * c / |y| ^ 3 := by
  have hL : (0 : ℝ) < 163 / 100 := by norm_num
  have hy0 : 0 < y₀ := by nlinarith
  have hyp : 0 < |y| := by linarith
  have hu : 1 < |2 * (163 / 100) * y| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2 * (163 / 100))]; nlinarith
  refine (abs_cosSqWindowTransform_le hL hu).trans ?_
  set u := 2 * (163 / 100 : ℝ) * y with hu_def
  have hau : |u| = 163 / 50 * |y| := by
    rw [hu_def, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2 * (163 / 100))]; ring
  have husq : u ^ 2 = (163 / 50) ^ 2 * |y| ^ 2 := by
    rw [← sq_abs, hau]; ring
  have hπ := Real.pi_pos
  have hc0 : 0 < c := by
    by_contra h; push Not at h
    have h1 : 0 ≤ π * (163 / 50) ^ 3 * (1 - 1 / (163 / 50 * y₀) ^ 2) := by
      have : 1 / (163 / 50 * y₀) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith
      have : 0 ≤ 1 - 1 / (163 / 50 * y₀) ^ 2 := by linarith
      positivity
    nlinarith
  have hk : 1 / (163 / 50 * |y|) ^ 2 ≤ 1 / (163 / 50 * y₀) ^ 2 := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) 2
  have hden : π * |u| * (u ^ 2 - 1) = π * (163 / 50) ^ 3 * (1 - 1 / (163 / 50 * |y|) ^ 2) * |y| ^ 3 := by
    rw [hau, husq]; field_simp
  have hpos1 : 0 < 1 - 1 / (163 / 50 * |y|) ^ 2 := by
    have : 1 / (163 / 50 * |y|) ^ 2 < 1 := by
      rw [div_lt_one (by positivity)]; nlinarith
    linarith
  rw [hden, div_le_div_iff₀ (by positivity) (by positivity)]
  have hmono : c * (π * (163 / 50) ^ 3 * (1 - 1 / (163 / 50 * y₀) ^ 2)) ≤
      c * (π * (163 / 50) ^ 3 * (1 - 1 / (163 / 50 * |y|) ^ 2)) := by
    apply mul_le_mul_of_nonneg_left _ hc0.le
    apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hy3 : 0 < |y| ^ 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (hc.trans hmono) hy3.le]

theorem abs_W_le_cube_one {y : ℝ} (hy : 2 / 5 ≤ |y|) :
    |cosSqWindowTransform (163 / 100) y| ≤ 163 / 100 * (224 / 10000) / |y| ^ 3 := by
  refine abs_cosSqWindowTransform_le_cube (by norm_num) ?_ hy
  have := Real.pi_gt_d6
  norm_num; nlinarith

theorem abs_W_le_cube_two {y : ℝ} (hy : 4 / 5 ≤ |y|) :
    |cosSqWindowTransform (163 / 100) y| ≤ 163 / 100 * (108 / 10000) / |y| ^ 3 := by
  refine abs_cosSqWindowTransform_le_cube (by norm_num) ?_ hy
  have := Real.pi_gt_d6
  norm_num; nlinarith

theorem abs_W_le_cube_base {y : ℝ} (hy : 6931 / 10000 ≤ |y|) :
    |cosSqWindowTransform (163 / 100) y| ≤ 163 / 100 * (115 / 10000) / |y| ^ 3 := by
  refine abs_cosSqWindowTransform_le_cube (by norm_num) ?_ hy
  have := Real.pi_gt_d6
  norm_num; nlinarith

theorem abs_W_le_cube_shift {y : ℝ} (hy : 6 / 5 ≤ |y|) :
    |cosSqWindowTransform (163 / 100) y| ≤ 163 / 100 * (99 / 10000) / |y| ^ 3 := by
  refine abs_cosSqWindowTransform_le_cube (by norm_num) ?_ hy
  have := Real.pi_gt_d6
  norm_num; nlinarith

/-! ## Majorant sequences -/

/-- Neighbour majorant at lattice distance `k + 1`. -/
def nbrMaj (k : ℕ) : ℝ :=
  (if k = 0 then 224 / 10000 else 108 / 10000) *
    (125 / 8 / ((k + 1 : ℕ) : ℝ) ^ 3 + 25 / 48 / ((k + 1 : ℕ) : ℝ) ^ 2)

/-- Base majorant for the `i`-th atom. -/
def baseMaj (i : ℕ) : ℝ :=
  115 / 10000 * (if i = 0 then 31769 / 10000 else if i = 1 then 8354 / 10000 else
    125 / 8 / ((i + 1 : ℕ) : ℝ) ^ 3 + 25 / 48 / ((i + 1 : ℕ) : ℝ) ^ 2)

/-- Shift majorant for the `i`-th atom. -/
def shiftMaj (i : ℕ) : ℝ :=
  99 / 10000 * (125 / 8 / ((i + 3 : ℕ) : ℝ) ^ 3 + 25 / 48 / ((i + 3 : ℕ) : ℝ) ^ 2)

theorem nbrMaj_nonneg (k : ℕ) : 0 ≤ nbrMaj k := by
  unfold nbrMaj; split_ifs <;> positivity

theorem baseMaj_nonneg (i : ℕ) : 0 ≤ baseMaj i := by
  unfold baseMaj; split_ifs <;> positivity

theorem shiftMaj_nonneg (i : ℕ) : 0 ≤ shiftMaj i := by
  unfold shiftMaj; positivity

theorem summable_cube_sq_tail (a : ℕ) (ha : 2 ≤ a) (c : ℝ) :
    Summable (fun i : ℕ => c * (125 / 8 / ((i + a : ℕ) : ℝ) ^ 3 + 25 / 48 / ((i + a : ℕ) : ℝ) ^ 2)) ∧
      ∑' i : ℕ, (125 / 8 / ((i + a : ℕ) : ℝ) ^ 3 + 25 / 48 / ((i + a : ℕ) : ℝ) ^ 2) ≤
        125 / 8 * (1 / (2 * ((a : ℝ) - 1) * a)) + 25 / 48 * (1 / ((a : ℝ) - 1)) := by
  obtain ⟨h3s, h3⟩ := tsum_inv_nat_add_cube_le a ha
  obtain ⟨h2s, h2⟩ := tsum_inv_nat_add_sq_le a ha
  have e3 : (fun i : ℕ => 125 / 8 / ((i + a : ℕ) : ℝ) ^ 3) =
      fun i : ℕ => 125 / 8 * (1 / ((i + a : ℕ) : ℝ) ^ 3) := by funext i; ring
  have e2 : (fun i : ℕ => 25 / 48 / ((i + a : ℕ) : ℝ) ^ 2) =
      fun i : ℕ => 25 / 48 * (1 / ((i + a : ℕ) : ℝ) ^ 2) := by funext i; ring
  have hs3 : Summable fun i : ℕ => 125 / 8 / ((i + a : ℕ) : ℝ) ^ 3 := by
    rw [e3]; exact h3s.mul_left _
  have hs2 : Summable fun i : ℕ => 25 / 48 / ((i + a : ℕ) : ℝ) ^ 2 := by
    rw [e2]; exact h2s.mul_left _
  refine ⟨(hs3.add hs2).mul_left c, ?_⟩
  rw [Summable.tsum_add hs3 hs2, e3, e2, tsum_mul_left, tsum_mul_left]
  gcongr

theorem summable_nbrMaj : Summable nbrMaj := by
  rw [← summable_nat_add_iff 1]
  obtain ⟨hs, -⟩ := summable_cube_sq_tail 2 le_rfl (108 / 10000)
  refine hs.congr fun i => ?_
  unfold nbrMaj
  rw [if_neg (by omega)]

theorem tsum_nbrMaj_le : ∑' k, nbrMaj k ≤ 4095 / 10000 := by
  rw [Summable.tsum_eq_zero_add summable_nbrMaj]
  obtain ⟨hs, ht⟩ := summable_cube_sq_tail 2 le_rfl (108 / 10000)
  have e : ∑' i, nbrMaj (i + 1) = 108 / 10000 *
      ∑' i : ℕ, (125 / 8 / ((i + 2 : ℕ) : ℝ) ^ 3 + 25 / 48 / ((i + 2 : ℕ) : ℝ) ^ 2) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun i => ?_
    unfold nbrMaj
    rw [if_neg (by omega)]
  rw [e]
  have h0 : nbrMaj 0 = 224 / 10000 * (125 / 8 + 25 / 48) := by
    unfold nbrMaj; norm_num
  rw [h0]
  have hnum : 125 / 8 * (1 / (2 * (((2 : ℕ) : ℝ) - 1) * ((2 : ℕ) : ℝ))) +
      25 / 48 * (1 / (((2 : ℕ) : ℝ) - 1)) = 425 / 96 := by norm_num
  rw [hnum] at ht
  nlinarith

theorem summable_baseMaj : Summable baseMaj := by
  rw [← summable_nat_add_iff 2]
  obtain ⟨hs, -⟩ := summable_cube_sq_tail 3 (by norm_num) (115 / 10000)
  refine hs.congr fun i => ?_
  unfold baseMaj
  rw [if_neg (by omega), if_neg (by omega)]

theorem tsum_baseMaj_le : ∑' i, baseMaj i ≤ 642 / 10000 := by
  rw [← summable_baseMaj.sum_add_tsum_nat_add 2]
  obtain ⟨hs, ht⟩ := summable_cube_sq_tail 3 (by norm_num) (115 / 10000)
  have e : ∑' i, baseMaj (i + 2) = 115 / 10000 *
      ∑' i : ℕ, (125 / 8 / ((i + 3 : ℕ) : ℝ) ^ 3 + 25 / 48 / ((i + 3 : ℕ) : ℝ) ^ 2) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun i => ?_
    unfold baseMaj
    rw [if_neg (by omega), if_neg (by omega)]
  rw [e]
  have hnum : 125 / 8 * (1 / (2 * (((3 : ℕ) : ℝ) - 1) * ((3 : ℕ) : ℝ))) +
      25 / 48 * (1 / (((3 : ℕ) : ℝ) - 1)) = 25 / 16 := by norm_num
  rw [hnum] at ht
  have hb0 : baseMaj 0 = 115 / 10000 * (31769 / 10000) := by unfold baseMaj; norm_num
  have hb1 : baseMaj 1 = 115 / 10000 * (8354 / 10000) := by unfold baseMaj; norm_num
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hb0, hb1]
  nlinarith

theorem summable_shiftMaj : Summable shiftMaj := by
  obtain ⟨hs, -⟩ := summable_cube_sq_tail 3 (by norm_num) (99 / 10000)
  exact hs

theorem tsum_shiftMaj_le : ∑' i, shiftMaj i ≤ 155 / 10000 := by
  obtain ⟨-, ht⟩ := summable_cube_sq_tail 3 (by norm_num) (99 / 10000)
  have hnum : 125 / 8 * (1 / (2 * (((3 : ℕ) : ℝ) - 1) * ((3 : ℕ) : ℝ))) +
      25 / 48 * (1 / (((3 : ℕ) : ℝ) - 1)) = 25 / 16 := by norm_num
  rw [hnum] at ht
  unfold shiftMaj
  rw [tsum_mul_left]
  nlinarith

/-! ## Pointwise majorants -/

theorem inv_cube_add_inv_sq_anti {x ℓ : ℝ} (hℓ : 0 < ℓ) (h : ℓ ≤ x) :
    1 / x ^ 3 + 1 / (12 * x ^ 2) ≤ 1 / ℓ ^ 3 + 1 / (12 * ℓ ^ 2) := by
  have hx : 0 < x := lt_of_lt_of_le hℓ h
  have h3 : 1 / x ^ 3 ≤ 1 / ℓ ^ 3 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hℓ.le h 3)
  have h2 : 1 / (12 * x ^ 2) ≤ 1 / (12 * ℓ ^ 2) :=
    one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hℓ.le h 2) (by norm_num))
  linarith

theorem weight_mul_cube_eq {x c : ℝ} (hx : 0 < x) :
    (1 + x / 12) * (c / x ^ 3) = c * (1 / x ^ 3 + 1 / (12 * x ^ 2)) := by
  field_simp

theorem cube_sq_at_nat_mul {k : ℕ} :
    1 / ((2 / 5 : ℝ) * ((k + 1 : ℕ) : ℝ)) ^ 3 + 1 / (12 * ((2 / 5 : ℝ) * ((k + 1 : ℕ) : ℝ)) ^ 2) =
      125 / 8 / ((k + 1 : ℕ) : ℝ) ^ 3 + 25 / 48 / ((k + 1 : ℕ) : ℝ) ^ 2 := by
  have : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  field_simp; ring

/-- Base majorant. -/
theorem base_term_le {i : ℕ} {li lj : ℝ} (hli : 6931 / 10000 + (i : ℝ) * (2 / 5) ≤ li)
    (hlj : 0 ≤ lj) :
    (12 + li) * |cosSqWindowTransform (163 / 100) li| ≤ 163 / 100 * (12 + lj) * baseMaj i := by
  have hli0 : 0 < li := by have := Nat.cast_nonneg (α := ℝ) i; linarith
  have hW := abs_W_le_cube_base (y := li) (by rw [abs_of_pos hli0]; have := Nat.cast_nonneg (α := ℝ) i; linarith)
  rw [abs_of_pos hli0] at hW
  have hwt : 12 + li ≤ (12 + lj) * (1 + li / 12) := by nlinarith
  have hc : (1 + li / 12) * (115 / 10000 / li ^ 3) = 115 / 10000 * (1 / li ^ 3 + 1 / (12 * li ^ 2)) :=
    weight_mul_cube_eq hli0
  have hkey : 1 / li ^ 3 + 1 / (12 * li ^ 2) ≤ baseMaj i / (115 / 10000) := by
    unfold baseMaj
    rw [mul_div_cancel_left₀ _ (by norm_num)]
    split_ifs with h0 h1
    · subst h0
      refine (inv_cube_add_inv_sq_anti (ℓ := 6931 / 10000) (by norm_num)
        (by simpa using hli)).trans ?_
      norm_num
    · subst h1
      refine (inv_cube_add_inv_sq_anti (ℓ := 10931 / 10000) (by norm_num) (show (10931 / 10000 : ℝ) ≤ li by
        push_cast at hli; linarith)).trans ?_
      norm_num
    · have hi2 : (2 : ℝ) ≤ i := by exact_mod_cast (by omega : 2 ≤ i)
      have hlow : (2 / 5 : ℝ) * ((i + 1 : ℕ) : ℝ) ≤ li := by push_cast; nlinarith
      refine (inv_cube_add_inv_sq_anti (by positivity) hlow).trans (le_of_eq ?_)
      exact cube_sq_at_nat_mul
  have hW0 : 0 ≤ |cosSqWindowTransform (163 / 100) li| := abs_nonneg _
  calc (12 + li) * |cosSqWindowTransform (163 / 100) li|
      ≤ ((12 + lj) * (1 + li / 12)) * (163 / 100 * (115 / 10000) / li ^ 3) :=
        mul_le_mul hwt hW hW0 (by positivity)
    _ = 163 / 100 * (12 + lj) * ((1 + li / 12) * (115 / 10000 / li ^ 3)) := by ring
    _ = 163 / 100 * (12 + lj) * (115 / 10000 * (1 / li ^ 3 + 1 / (12 * li ^ 2))) := by rw [hc]
    _ ≤ 163 / 100 * (12 + lj) * (115 / 10000 * (baseMaj i / (115 / 10000))) := by gcongr
    _ = 163 / 100 * (12 + lj) * baseMaj i := by field_simp

/-- Shift majorant. -/
theorem shift_term_le {i : ℕ} {li lj : ℝ} (hli : 6931 / 10000 + (i : ℝ) * (2 / 5) ≤ li)
    (hlj : 6931 / 10000 ≤ lj) :
    (12 + li) * |cosSqWindowTransform (163 / 100) (li + lj)| ≤
      163 / 100 * (12 + lj) * shiftMaj i := by
  have hi0 := Nat.cast_nonneg (α := ℝ) i
  set μ := li + lj with hμ
  have hμ0 : 0 < μ := by linarith
  have hμlow : (2 / 5 : ℝ) * ((i + 3 : ℕ) : ℝ) ≤ μ := by push_cast; linarith
  have hW := abs_W_le_cube_shift (y := μ) (by rw [abs_of_pos hμ0]; linarith)
  rw [abs_of_pos hμ0] at hW
  have hwt : 12 + li ≤ (12 + lj) * (1 + μ / 12) := by nlinarith
  have hc : (1 + μ / 12) * (99 / 10000 / μ ^ 3) = 99 / 10000 * (1 / μ ^ 3 + 1 / (12 * μ ^ 2)) :=
    weight_mul_cube_eq hμ0
  have hkey : 1 / μ ^ 3 + 1 / (12 * μ ^ 2) ≤
      125 / 8 / ((i + 3 : ℕ) : ℝ) ^ 3 + 25 / 48 / ((i + 3 : ℕ) : ℝ) ^ 2 := by
    refine (inv_cube_add_inv_sq_anti (by positivity) hμlow).trans (le_of_eq ?_)
    have : (0 : ℝ) < ((i + 3 : ℕ) : ℝ) := by positivity
    field_simp; ring
  have hW0 : 0 ≤ |cosSqWindowTransform (163 / 100) μ| := abs_nonneg _
  calc (12 + li) * |cosSqWindowTransform (163 / 100) μ|
      ≤ ((12 + lj) * (1 + μ / 12)) * (163 / 100 * (99 / 10000) / μ ^ 3) :=
        mul_le_mul hwt hW hW0 (by positivity)
    _ = 163 / 100 * (12 + lj) * ((1 + μ / 12) * (99 / 10000 / μ ^ 3)) := by ring
    _ = 163 / 100 * (12 + lj) * (99 / 10000 * (1 / μ ^ 3 + 1 / (12 * μ ^ 2))) := by rw [hc]
    _ ≤ 163 / 100 * (12 + lj) * (99 / 10000 * (125 / 8 / ((i + 3 : ℕ) : ℝ) ^ 3 +
          25 / 48 / ((i + 3 : ℕ) : ℝ) ^ 2)) := by gcongr
    _ = 163 / 100 * (12 + lj) * shiftMaj i := by rw [shiftMaj]

/-- Neighbour majorant. -/
theorem nbr_term_le {k : ℕ} {li lj : ℝ} (hD : (2 / 5 : ℝ) * ((k + 1 : ℕ) : ℝ) ≤ |li - lj|)
    (hlj : 0 ≤ lj) :
    (12 + li) * |cosSqWindowTransform (163 / 100) (li - lj)| ≤
      163 / 100 * (12 + lj) * nbrMaj k := by
  set D := |li - lj| with hDdef
  have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith
  have hD0 : 0 < D := by nlinarith
  have hwt : 12 + li ≤ (12 + lj) * (1 + D / 12) := by
    have : li ≤ lj + D := by
      have := le_abs_self (li - lj); rw [← hDdef] at this; linarith
    nlinarith
  set c : ℝ := if k = 0 then 224 / 10000 else 108 / 10000 with hcdef
  have hW : |cosSqWindowTransform (163 / 100) (li - lj)| ≤ 163 / 100 * c / D ^ 3 := by
    rw [hcdef]
    split_ifs with h0
    · exact abs_W_le_cube_one (by rw [← hDdef]; subst h0; simpa using hD)
    · have hk2 : (2 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ k + 1)
      exact abs_W_le_cube_two (by rw [← hDdef]; nlinarith)
  have hc : (1 + D / 12) * (c / D ^ 3) = c * (1 / D ^ 3 + 1 / (12 * D ^ 2)) :=
    weight_mul_cube_eq hD0
  have hkey : 1 / D ^ 3 + 1 / (12 * D ^ 2) ≤
      125 / 8 / ((k + 1 : ℕ) : ℝ) ^ 3 + 25 / 48 / ((k + 1 : ℕ) : ℝ) ^ 2 :=
    (inv_cube_add_inv_sq_anti (by positivity) hD).trans (le_of_eq cube_sq_at_nat_mul)
  have hc0 : 0 ≤ c := by rw [hcdef]; split_ifs <;> norm_num
  have hW0 : 0 ≤ |cosSqWindowTransform (163 / 100) (li - lj)| := abs_nonneg _
  calc (12 + li) * |cosSqWindowTransform (163 / 100) (li - lj)|
      ≤ ((12 + lj) * (1 + D / 12)) * (163 / 100 * c / D ^ 3) :=
        mul_le_mul hwt hW hW0 (by positivity)
    _ = 163 / 100 * (12 + lj) * ((1 + D / 12) * (c / D ^ 3)) := by ring
    _ = 163 / 100 * (12 + lj) * (c * (1 / D ^ 3 + 1 / (12 * D ^ 2))) := by rw [hc]
    _ ≤ 163 / 100 * (12 + lj) * (c * (125 / 8 / ((k + 1 : ℕ) : ℝ) ^ 3 +
          25 / 48 / ((k + 1 : ℕ) : ℝ) ^ 2)) := by gcongr
    _ = 163 / 100 * (12 + lj) * nbrMaj k := by rw [nbrMaj]

/-! ## The super-value at the atoms -/

theorem abs_modSuperValue_le {L η a σ : ℝ} (hσ : σ ^ 2 = 1) (y : ℝ) :
    |modSuperValue L η a σ y| ≤ bumpCos 0 * (2 * |cosSqWindowTransform L y| +
      |cosSqWindowTransform L (y + a)| + |cosSqWindowTransform L (y - a)|) := by
  have hσa : |σ| = 1 := by
    have := sq_abs σ; rw [hσ] at this
    nlinarith [abs_nonneg σ, sq_nonneg (|σ| - 1)]
  have hB := fun x => abs_bumpCos_le x
  unfold modSuperValue
  rw [hσ]
  have e : ∀ x w : ℝ, |bumpCos x * w| ≤ bumpCos 0 * |w| := fun x w => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _)
  calc |(1 + 1) * (bumpCos (η * y) * cosSqWindowTransform L y) +
        σ * (bumpCos (η * (y + a)) * cosSqWindowTransform L (y + a) +
          bumpCos (η * (y - a)) * cosSqWindowTransform L (y - a))|
      ≤ 2 * |bumpCos (η * y) * cosSqWindowTransform L y| +
        |σ| * (|bumpCos (η * (y + a)) * cosSqWindowTransform L (y + a)| +
          |bumpCos (η * (y - a)) * cosSqWindowTransform L (y - a)|) := by
        refine (abs_add_le _ _).trans (add_le_add (le_of_eq ?_) ?_)
        · rw [abs_mul, show |(1 + 1 : ℝ)| = 2 by norm_num]
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
    _ ≤ 2 * (bumpCos 0 * |cosSqWindowTransform L y|) +
        1 * (bumpCos 0 * |cosSqWindowTransform L (y + a)| +
          bumpCos 0 * |cosSqWindowTransform L (y - a)|) := by
        rw [hσa]; gcongr <;> exact e _ _
    _ = _ := by ring

theorem modSuperValue_diag_le {L η σ v : ℝ} (hL : 0 < L) (hσ : σ ^ 2 = 1)
    (hσv : σ * v = -|v|) (a : ℝ) :
    v * modSuperValue L η a σ a + |v| * bumpCos 0 * L ≤
      |v| * (bumpCos 0 * (2 * |cosSqWindowTransform L a| + |cosSqWindowTransform L (a + a)|)) := by
  have hB := fun x => abs_bumpCos_le x
  unfold modSuperValue
  rw [hσ, sub_self, mul_zero, cosSqWindowTransform_zero hL]
  have e1 : v * ((1 + 1) * (bumpCos (η * a) * cosSqWindowTransform L a) +
      σ * (bumpCos (η * (a + a)) * cosSqWindowTransform L (a + a) + bumpCos 0 * L)) +
      |v| * bumpCos 0 * L = 2 * (v * (bumpCos (η * a) * cosSqWindowTransform L a)) +
        (σ * v) * (bumpCos (η * (a + a)) * cosSqWindowTransform L (a + a)) := by
    rw [show (σ * v) = σ * v from rfl]
    have : σ * v * (bumpCos 0 * L) = -|v| * bumpCos 0 * L := by rw [hσv]; ring
    linear_combination this
  rw [e1, hσv]
  have h1 : v * (bumpCos (η * a) * cosSqWindowTransform L a) ≤
      |v| * (bumpCos 0 * |cosSqWindowTransform L a|) := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hB _) (abs_nonneg _)) (abs_nonneg _)
  have h2 : -|v| * (bumpCos (η * (a + a)) * cosSqWindowTransform L (a + a)) ≤
      |v| * (bumpCos 0 * |cosSqWindowTransform L (a + a)|) := by
    have : |-|v| * (bumpCos (η * (a + a)) * cosSqWindowTransform L (a + a))| ≤
        |v| * (bumpCos 0 * |cosSqWindowTransform L (a + a)|) := by
      rw [abs_mul, abs_neg, abs_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hB _) (abs_nonneg _)) (abs_nonneg _)
    exact (le_abs_self _).trans this
  nlinarith

/-! ## The contraction at one atom -/

theorem log_threeHalvesLacunary_dist_ge {n : ℕ → ℕ} (h0 : 2 ≤ n 0)
    (hs : ∀ i, 3 * n i ≤ 2 * n (i + 1)) {i j : ℕ} (hij : i ≠ j) :
    (2 / 5 : ℝ) * ((Nat.dist i j - 1 + 1 : ℕ) : ℝ) ≤ |Real.log (n i) - Real.log (n j)| := by
  rcases lt_or_gt_of_ne hij with h | h
  · have hd : Nat.dist i j = j - i := Nat.dist_eq_sub_of_le h.le
    have := log_threeHalvesLacunary_add_sub_ge h0 hs i (j - i)
    rw [show i + (j - i) = j by omega] at this
    rw [abs_sub_comm, abs_of_nonneg (by have := Nat.cast_nonneg (α := ℝ) (j - i); nlinarith), hd,
      show j - i - 1 + 1 = j - i by omega]
    linarith
  · have hd : Nat.dist i j = i - j := Nat.dist_eq_sub_of_le_right h.le
    have := log_threeHalvesLacunary_add_sub_ge h0 hs j (i - j)
    rw [show j + (i - j) = i by omega] at this
    rw [abs_of_nonneg (by have := Nat.cast_nonneg (α := ℝ) (i - j); nlinarith), hd,
      show i - j - 1 + 1 = i - j by omega]
    linarith

/-- The neighbour majorant, reflected. -/
def nbrRefl (j i : ℕ) : ℝ :=
  (if j < i then nbrMaj (i - j - 1) else 0) + (if i < j then nbrMaj (j - i - 1) else 0)

theorem nbrRefl_eq {i j : ℕ} (hij : i ≠ j) : nbrRefl j i = nbrMaj (Nat.dist i j - 1) := by
  unfold nbrRefl
  rcases lt_or_gt_of_ne hij with h | h
  · rw [if_neg (by omega), if_pos h, zero_add, Nat.dist_eq_sub_of_le h.le]
  · rw [if_pos h, if_neg (by omega), add_zero, Nat.dist_eq_sub_of_le_right h.le]

theorem nbrRefl_self (j : ℕ) : nbrRefl j j = 0 := by
  unfold nbrRefl; simp

theorem nbrRefl_nonneg (j i : ℕ) : 0 ≤ nbrRefl j i := by
  unfold nbrRefl
  have := nbrMaj_nonneg (i - j - 1); have := nbrMaj_nonneg (j - i - 1)
  split_ifs <;> linarith

/-- **The key inequality at one atom of a three-halves lacunary set.** -/
theorem threeHalves_atom_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {n : ℕ → ℕ} (h0 : 2 ≤ n 0)
    (hs : ∀ i, 3 * n i ≤ 2 * n (i + 1))
    (hsupp : ∀ m, 2 ≤ m → (∀ i, m ≠ n i) → lam m = ArithmeticFunction.vonMangoldt m)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i, |normDeficit lam (n i)| ≤ M * (12 + Real.log (n i))) (j : ℕ) :
    |normDeficit lam (n j)| ≤ 97 / 100 * M * (12 + Real.log (n j)) := by
  obtain ⟨Bx, -, hBx⟩ := exists_abs_normDeficit_le_log hW
  set v := normDeficit lam with hvdef
  have hinj : Function.Injective n := (threeHalvesLacunary_strictMono h0 hs).injective
  set l : ℕ → ℝ := fun i => Real.log (n i) with hl
  have hlow : ∀ i : ℕ, 6931 / 10000 + (i : ℝ) * (2 / 5) ≤ l i := log_threeHalvesLacunary_ge h0 hs
  have hl0 : ∀ i, 0 ≤ l i := fun i => by
    have := hlow i; have := Nat.cast_nonneg (α := ℝ) i; linarith
  have hlj : 6931 / 10000 ≤ l j := by
    have := hlow j; have := Nat.cast_nonneg (α := ℝ) j; linarith
  have hvz : ∀ m, m ∉ Set.range n → v m = 0 := by
    intro m hm
    rw [hvdef]; simp only [normDeficit]
    split_ifs with h2
    · rw [hsupp m h2 (fun i hi => hm ⟨i, hi.symm⟩), sub_self, zero_div]
    · rfl
  -- the summability input
  have hZ : Summable fun m : ℕ => |v m| * ((1 + |Real.log m|) ^ 3)⁻¹ := by
    have hz : ∀ m ∉ Set.range n, |v m| * ((1 + |Real.log m|) ^ 3)⁻¹ = 0 := fun m hm => by
      rw [hvz m hm, abs_zero, zero_mul]
    rw [← hinj.summable_iff hz]
    have hg : Summable fun i : ℕ => 75 * M * (1 / ((i + 1 : ℕ) : ℝ) ^ 2) := by
      have := (summable_nat_add_iff 1).mpr ((Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two)
      exact (this.mul_left (75 * M)).congr fun i => by push_cast; ring
    refine Summable.of_nonneg_of_le (fun i => by simp only [Function.comp]; positivity)
      (fun i => ?_) hg
    simp only [Function.comp]
    have hli := hl0 i
    rw [abs_of_nonneg (Real.log_natCast_nonneg _)]
    change |v (n i)| * ((1 + l i) ^ 3)⁻¹ ≤ _
    have hvi := hM i
    change |v (n i)| ≤ M * (12 + l i) at hvi
    have h1 : 0 < 1 + l i := by linarith
    have hlo : (2 / 5 : ℝ) * ((i + 1 : ℕ) : ℝ) ≤ 1 + l i := by
      have := hlow i; push_cast; linarith
    have hi1 : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    have hk : M * (12 + l i) ≤ 12 * M * (1 + l i) := by nlinarith
    have hsq : (2 / 5 : ℝ) ^ 2 * ((i + 1 : ℕ) : ℝ) ^ 2 ≤ (1 + l i) ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hlo 2
    have hfin : 12 * M * (1 + l i) ≤ 75 * M * (1 / ((i + 1 : ℕ) : ℝ) ^ 2) * (1 + l i) ^ 3 := by
      have e : 75 * M * (1 / ((i + 1 : ℕ) : ℝ) ^ 2) * (1 + l i) ^ 3 =
          12 * M * (1 + l i) * ((1 + l i) ^ 2 / ((2 / 5 : ℝ) ^ 2 * ((i + 1 : ℕ) : ℝ) ^ 2)) := by
        field_simp; ring
      rw [e]
      have : 1 ≤ (1 + l i) ^ 2 / ((2 / 5 : ℝ) ^ 2 * ((i + 1 : ℕ) : ℝ) ^ 2) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      nlinarith [mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 12 * M * (1 + l i))]
    linarith
  -- the sign and the positivity
  set σ : ℝ := if 0 ≤ v (n j) then -1 else 1 with hσdef
  have hσ2 : σ ^ 2 = 1 := by rw [hσdef]; split_ifs <;> norm_num
  have hσv : σ * v (n j) = -|v (n j)| := by
    rw [hσdef]; split_ifs with h
    · rw [abs_of_nonneg h]; ring
    · rw [abs_of_neg (not_le.mp h)]; ring
  have hpos := superposed_deviation_nonneg hW hBx hZ (L := 163 / 100) (η := 3 / 1000)
    (by norm_num) (by norm_num) (by norm_num) (l j) σ
  set Sv : ℝ → ℝ := modSuperValue (163 / 100) (3 / 1000) (l j) σ with hSv
  set W : ℝ → ℝ := cosSqWindowTransform (163 / 100) with hWdef
  set B₀ := bumpCos 0 with hB₀
  have hB₀pos : 0 < B₀ := bumpCos_zero_pos
  -- reindexing
  have hsupport : Function.support (fun m => v m * Sv (Real.log m)) ⊆ Set.range n := by
    intro m hm; by_contra hc; exact hm (by simp only; rw [hvz m hc, zero_mul])
  have hreindex : ∑' i, v (n i) * Sv (l i) = ∑' m, v m * Sv (Real.log m) :=
    hinj.tsum_eq (f := fun m => v m * Sv (Real.log m)) hsupport
  -- the majorant
  set β : ℕ → ℝ := fun i => M * B₀ * (163 / 100) * (12 + l j) *
    (2 * baseMaj i + shiftMaj i + nbrRefl j i) with hβ
  obtain ⟨hRs, hRt⟩ := sum_shift_reflect_le nbrMaj_nonneg summable_nbrMaj j
  have hRs' : Summable (nbrRefl j) := hRs
  have hRt' : ∑' i, nbrRefl j i ≤ 2 * ∑' k, nbrMaj k := hRt
  have hβs : Summable β := by
    rw [hβ]
    exact ((((summable_baseMaj.mul_left 2).add summable_shiftMaj).add hRs').mul_left _)
  have hβt : ∑' i, β i ≤ M * B₀ * (163 / 100) * (12 + l j) * (9629 / 10000) := by
    rw [hβ, tsum_mul_left, Summable.tsum_add ((summable_baseMaj.mul_left 2).add summable_shiftMaj) hRs',
      Summable.tsum_add (summable_baseMaj.mul_left 2) summable_shiftMaj, tsum_mul_left]
    have := tsum_baseMaj_le; have := tsum_shiftMaj_le; have := tsum_nbrMaj_le
    have hc : 0 ≤ M * B₀ * (163 / 100) * (12 + l j) := by have := hl0 j; positivity
    refine mul_le_mul_of_nonneg_left ?_ hc
    linarith
  -- the pointwise bound
  set A : ℕ → ℝ := fun i => if i = j then |v (n j)| * B₀ * (163 / 100) else 0 with hA
  have hW3 : ∀ i, (12 + l i) * (2 * |W (l i)| + |W (l i + l j)|) ≤
      163 / 100 * (12 + l j) * (2 * baseMaj i + shiftMaj i) := by
    intro i
    have h1 := base_term_le (hlow i) (hl0 j)
    have h2 := shift_term_le (hlow i) hlj
    nlinarith
  have hle : ∀ i, v (n i) * Sv (l i) + A i ≤ β i := by
    intro i
    have hMi := hM i
    change |v (n i)| ≤ M * (12 + l i) at hMi
    have hli := hl0 i
    by_cases hij : i = j
    · subst hij
      simp only [hA, if_pos rfl, hβ, nbrRefl_self, add_zero]
      have hd := modSuperValue_diag_le (L := 163 / 100) (η := 3 / 1000) (by norm_num) hσ2 hσv (l i)
      have hw := hW3 i
      have hWn : 0 ≤ 2 * |W (l i)| + |W (l i + l i)| := by positivity
      calc v (n i) * Sv (l i) + |v (n i)| * B₀ * (163 / 100)
          ≤ |v (n i)| * (B₀ * (2 * |W (l i)| + |W (l i + l i)|)) := hd
        _ ≤ (M * (12 + l i)) * (B₀ * (2 * |W (l i)| + |W (l i + l i)|)) :=
          mul_le_mul_of_nonneg_right hMi (by positivity)
        _ = M * B₀ * ((12 + l i) * (2 * |W (l i)| + |W (l i + l i)|)) := by ring
        _ ≤ M * B₀ * (163 / 100 * (12 + l i) * (2 * baseMaj i + shiftMaj i)) :=
          mul_le_mul_of_nonneg_left hw (by positivity)
        _ = _ := by ring
    · simp only [hA, if_neg hij, add_zero, hβ]
      have hS := abs_modSuperValue_le (L := 163 / 100) (η := 3 / 1000) (a := l j) hσ2 (l i)
      have hn := nbr_term_le (k := Nat.dist i j - 1) (log_threeHalvesLacunary_dist_ge h0 hs hij)
        (hl0 j)
      rw [← nbrRefl_eq hij] at hn
      have hw := hW3 i
      have hWn : 0 ≤ 2 * |W (l i)| + |W (l i + l j)| + |W (l i - l j)| := by positivity
      calc v (n i) * Sv (l i) ≤ |v (n i)| * |Sv (l i)| := by rw [← abs_mul]; exact le_abs_self _
        _ ≤ (M * (12 + l i)) * (B₀ * (2 * |W (l i)| + |W (l i + l j)| + |W (l i - l j)|)) :=
          mul_le_mul hMi hS (abs_nonneg _) (by positivity)
        _ = M * B₀ * ((12 + l i) * (2 * |W (l i)| + |W (l i + l j)|) +
              (12 + l i) * |W (l i - l j)|) := by ring
        _ ≤ M * B₀ * (163 / 100 * (12 + l j) * (2 * baseMaj i + shiftMaj i) +
              163 / 100 * (12 + l j) * nbrRefl j i) :=
          mul_le_mul_of_nonneg_left (add_le_add hw hn) (by positivity)
        _ = _ := by ring
  -- summability of the pairing
  have hAs : Summable A := by
    rw [hA]; exact summable_of_ne_finset_zero (s := {j}) fun i hi => by
      rw [Finset.mem_singleton] at hi; rw [if_neg hi]
  have hAt : ∑' i, A i = |v (n j)| * B₀ * (163 / 100) := by rw [hA, tsum_ite_eq]
  have hvS : Summable fun i => v (n i) * Sv (l i) := by
    refine Summable.of_norm_bounded (hβs.add hAs) fun i => ?_
    rw [Real.norm_eq_abs]
    have hMi := hM i
    change |v (n i)| ≤ M * (12 + l i) at hMi
    have hS := abs_modSuperValue_le (L := 163 / 100) (η := 3 / 1000) (a := l j) hσ2 (l i)
    have hli := hl0 i
    have h1 := hle i
    have hAi : 0 ≤ A i := by simp only [hA]; split_ifs <;> positivity
    by_cases hij : i = j
    · subst hij
      have hWz : |W (l i - l i)| = 163 / 100 := by
        rw [sub_self, hWdef, cosSqWindowTransform_zero (by norm_num)]; norm_num
      have hAi' : A i = |v (n i)| * B₀ * (163 / 100) := by simp only [hA, if_pos rfl]
      have hw := hW3 i
      have hβi : β i = M * B₀ * (163 / 100) * (12 + l i) * (2 * baseMaj i + shiftMaj i) := by
        simp only [hβ, nbrRefl_self, add_zero]
      calc |v (n i) * Sv (l i)| = |v (n i)| * |Sv (l i)| := abs_mul _ _
        _ ≤ |v (n i)| * (B₀ * (2 * |W (l i)| + |W (l i + l i)| + |W (l i - l i)|)) :=
          mul_le_mul_of_nonneg_left hS (abs_nonneg _)
        _ = |v (n i)| * (B₀ * (2 * |W (l i)| + |W (l i + l i)|)) + A i := by rw [hWz, hAi']; ring
        _ ≤ M * (12 + l i) * (B₀ * (2 * |W (l i)| + |W (l i + l i)|)) + A i := by
          gcongr
        _ = M * B₀ * ((12 + l i) * (2 * |W (l i)| + |W (l i + l i)|)) + A i := by ring
        _ ≤ M * B₀ * (163 / 100 * (12 + l i) * (2 * baseMaj i + shiftMaj i)) + A i := by
          gcongr
        _ = β i + A i := by rw [hβi]; ring
    · have hAi0 : A i = 0 := by simp only [hA, if_neg hij]
      have hn := nbr_term_le (k := Nat.dist i j - 1) (log_threeHalvesLacunary_dist_ge h0 hs hij)
        (hl0 j)
      rw [← nbrRefl_eq hij] at hn
      have hw := hW3 i
      rw [hAi0, add_zero]
      calc |v (n i) * Sv (l i)| = |v (n i)| * |Sv (l i)| := abs_mul _ _
        _ ≤ (M * (12 + l i)) * (B₀ * (2 * |W (l i)| + |W (l i + l j)| + |W (l i - l j)|)) :=
          mul_le_mul hMi hS (abs_nonneg _) (by positivity)
        _ = M * B₀ * ((12 + l i) * (2 * |W (l i)| + |W (l i + l j)|) +
              (12 + l i) * |W (l i - l j)|) := by ring
        _ ≤ M * B₀ * (163 / 100 * (12 + l j) * (2 * baseMaj i + shiftMaj i) +
              163 / 100 * (12 + l j) * nbrRefl j i) :=
          mul_le_mul_of_nonneg_left (add_le_add hw hn) (by positivity)
        _ = β i := by simp only [hβ]; ring
  have hsum := (hvS.add hAs).tsum_le_tsum hle hβs
  rw [hvS.tsum_add hAs, hAt, hreindex] at hsum
  have hB0L : 0 < B₀ * (163 / 100) := by positivity
  have hpos' : 0 ≤ ∑' m, v m * Sv (Real.log m) := hpos
  have hfinal : |v (n j)| * (B₀ * (163 / 100)) ≤
      (97 / 100 * M * (12 + l j)) * (B₀ * (163 / 100)) := by
    have := hl0 j
    have hc : 0 ≤ M * B₀ * (163 / 100) * (12 + l j) := by positivity
    nlinarith
  exact le_of_mul_le_mul_right hfinal hB0L

/-- **Three-halves lacunary rigidity.** A full-cone Weil-positive system that agrees with `Λ` off a
set `n 0 < n 1 < ⋯` with `n 0 ≥ 2` and `3 n i ≤ 2 n (i+1)` is `Λ`. The deviations on the set are
arbitrary a priori. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_threeHalves_lacunary {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {n : ℕ → ℕ} (h0 : 2 ≤ n 0) (hs : ∀ i, 3 * n i ≤ 2 * n (i + 1))
    (hsupp : ∀ m, 2 ≤ m → (∀ i, m ≠ n i) → lam m = ArithmeticFunction.vonMangoldt m) :
    ∀ m, 2 ≤ m → lam m = ArithmeticFunction.vonMangoldt m := by
  obtain ⟨Bx, hBx0, hBx⟩ := exists_abs_normDeficit_le_log hW
  have hw : ∀ i, 0 < 12 + Real.log (n i) := fun i => by
    have := Real.log_natCast_nonneg (n i); linarith
  set r : ℕ → ℝ := fun i => |normDeficit lam (n i)| / (12 + Real.log (n i)) with hr
  have hr0 : ∀ i, 0 ≤ r i := fun i => div_nonneg (abs_nonneg _) (hw i).le
  have hrB : ∀ i, r i ≤ Bx := fun i => by
    simp only [hr]; rw [div_le_iff₀ (hw i)]
    have h := hBx (n i)
    rw [abs_of_nonneg (Real.log_natCast_nonneg _)] at h
    have := Real.log_natCast_nonneg (n i)
    nlinarith
  have hbdd : BddAbove (Set.range r) := ⟨Bx, by rintro _ ⟨i, rfl⟩; exact hrB i⟩
  set M := ⨆ i, r i with hMdef
  have hM0 : 0 ≤ M := le_trans (hr0 0) (le_ciSup hbdd 0)
  have hM : ∀ i, |normDeficit lam (n i)| ≤ M * (12 + Real.log (n i)) := fun i => by
    have := le_ciSup hbdd i
    simp only [hr] at this
    rwa [div_le_iff₀ (hw i)] at this
  have hrle : ∀ j, r j ≤ 97 / 100 * M := by
    intro j
    have h := threeHalves_atom_le hW h0 hs hsupp hM0 hM j
    simp only [hr]
    rw [div_le_iff₀ (hw j)]
    linarith
  have hMle : M ≤ 97 / 100 * M := ciSup_le hrle
  have hMz : M = 0 := by linarith
  intro m hm
  by_cases hmr : ∃ i, m = n i
  · obtain ⟨i, rfl⟩ := hmr
    have h := hM i
    rw [hMz, zero_mul] at h
    have hv : normDeficit lam (n i) = 0 := abs_nonpos_iff.mp h
    simp only [normDeficit, if_pos hm] at hv
    have hsq : Real.sqrt (n i : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n i))).ne'
    rw [div_eq_zero_iff, sub_eq_zero] at hv
    rcases hv with hv | hv
    · exact hv.symm
    · exact absurd hv hsq
  · exact hsupp m hm fun i hi => hmr ⟨i, hi⟩

end

end RHTower
