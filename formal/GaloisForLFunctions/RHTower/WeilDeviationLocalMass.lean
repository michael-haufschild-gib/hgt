import GaloisForLFunctions.RHTower.WeilLittleODeviationHarmonicConvergence

/-!
# Local harmonic mass of Weil deviations

A sequence `d` has *local mass at most `M`* (`LocalMassBounded d M`) if every unit harmonic window
carries `Σ_{|log n − Z| ≤ ½} |d(n)|/n ≤ M`, `Z ≥ 1`.

* **Local mass gives the notch bounds** (`notchBounded_of_localMassBounded`). Covering by unit windows
  gives `Σ_{n≤N} |d|/n ≪ M log N`, `Σ_{n≤N} |d|/√n ≪ M √N`, `Σ_{n>N} |d| n^{−3/2} ≪ M N^{−1/2}`
  and `Σ |d| n^{−σ} < ∞` for `σ > 1`. So `d` is notch-bounded at level `5M + 1`.
* **Size `C(1 + Λ)`** (`localMassBounded_of_abs_le`), by the square-root Chebyshev bound.
* **Nonnegative Weil-positive weights** (`exists_localMassBounded_of_nonneg`). If `lam ≥ 0` is
  full-cone Weil-positive, then `d = lam − Λ` has bounded local mass, with no size hypothesis. The
  harmonic windows of `d` are `O(L^{−2})`. Integrating the windows of `lam = d + Λ` over
  `[Z − 2, Z + 2]` dominates `Φ(1)` times the local mass of `lam`, since `lam ≥ 0`.
-/

noncomputable section

open MeasureTheory Set Filter Topology RHTower

namespace RHTower.WeilAbscissa

open RHTower.PrimeSmallDeviation

/-- **Local mass at most `M`**: `Σ_{|log n − Z| ≤ ½} |d(n)|/n ≤ M` for every `Z ≥ 1`. -/
def LocalMassBounded (d : ℕ → ℝ) (M : ℝ) : Prop :=
  ∀ Z : ℝ, 1 ≤ Z → ∀ N₁ : ℕ,
    ∑ n ∈ Finset.range N₁, |d n| / n * (if |Real.log n - Z| ≤ 1 / 2 then 1 else 0) ≤ M

theorem localWindow_nonneg (d : ℕ → ℝ) (Z : ℝ) (n : ℕ) :
    0 ≤ |d n| / n * (if |Real.log n - Z| ≤ 1 / 2 then 1 else 0) :=
  mul_nonneg (div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) (by split_ifs <;> norm_num)

/-- The local mass bound holds on every finite set of indices. -/
theorem LocalMassBounded.sum_finset_le {d : ℕ → ℝ} {M : ℝ} (h : LocalMassBounded d M) {Z : ℝ}
    (hZ : 1 ≤ Z) (S : Finset ℕ) :
    ∑ n ∈ S, |d n| / n * (if |Real.log n - Z| ≤ 1 / 2 then 1 else 0) ≤ M := by
  have hsub : S ⊆ Finset.range (S.sup id + 1) := fun n hn =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => localWindow_nonneg d Z n).trans
    (h Z hZ _)

/-- Domination by a sum adds the local masses. -/
theorem LocalMassBounded.of_abs_le_add {d d₁ d₂ : ℕ → ℝ} {M₁ M₂ : ℝ}
    (h₁ : LocalMassBounded d₁ M₁) (h₂ : LocalMassBounded d₂ M₂)
    (hle : ∀ n, |d n| ≤ |d₁ n| + |d₂ n|) : LocalMassBounded d (M₁ + M₂) := by
  intro Z hZ N₁
  have h := add_le_add (h₁ Z hZ N₁) (h₂ Z hZ N₁)
  rw [← Finset.sum_add_distrib] at h
  refine le_trans (Finset.sum_le_sum fun n _ => ?_) h
  have hw : 0 ≤ (if |Real.log n - Z| ≤ 1 / 2 then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have hn := Nat.cast_nonneg (α := ℝ) n
  calc |d n| / n * (if |Real.log n - Z| ≤ 1 / 2 then 1 else 0)
      ≤ (|d₁ n| + |d₂ n|) / n * (if |Real.log n - Z| ≤ 1 / 2 then 1 else 0) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hle n) hn) hw
    _ = _ := by ring

/-! ## Windows -/

/-- **Covering a weighted sum by windows.** If every index with `f(n) ≠ 0` lies in a window
`|log n − Z_k| ≤ ½`, `k ∈ K`, on which `w(n) ≤ W_k`, then `Σ_S f w ≤ Σ_K W_k Σ_S f 1_{window k}`. -/
theorem sum_mul_le_windows {f w : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (S K : Finset ℕ) (Z W : ℕ → ℝ)
    (hW0 : ∀ k ∈ K, 0 ≤ W k)
    (hcov : ∀ n ∈ S, f n ≠ 0 → ∃ k ∈ K, |Real.log n - Z k| ≤ 1 / 2 ∧ w n ≤ W k) :
    ∑ n ∈ S, f n * w n ≤
      ∑ k ∈ K, W k * ∑ n ∈ S, f n * (if |Real.log n - Z k| ≤ 1 / 2 then 1 else 0) := by
  have hpt : ∀ n ∈ S, f n * w n ≤
      ∑ k ∈ K, W k * (f n * (if |Real.log n - Z k| ≤ 1 / 2 then 1 else 0)) := by
    intro n hn
    have hnn : ∀ k ∈ K, 0 ≤ W k * (f n * (if |Real.log n - Z k| ≤ 1 / 2 then 1 else 0)) :=
      fun k hk => mul_nonneg (hW0 k hk) (mul_nonneg (hf n) (by split_ifs <;> norm_num))
    by_cases h0 : f n = 0
    · calc f n * w n = 0 := by rw [h0, zero_mul]
        _ ≤ _ := Finset.sum_nonneg hnn
    obtain ⟨k, hk, hwin, hwk⟩ := hcov n hn h0
    calc f n * w n ≤ f n * W k := mul_le_mul_of_nonneg_left hwk (hf n)
      _ = W k * (f n * (if |Real.log n - Z k| ≤ 1 / 2 then 1 else 0)) := by
          rw [if_pos hwin]; ring
      _ ≤ _ := Finset.single_le_sum hnn hk
  calc ∑ n ∈ S, f n * w n
      ≤ ∑ n ∈ S, ∑ k ∈ K, W k * (f n * (if |Real.log n - Z k| ≤ 1 / 2 then 1 else 0)) :=
        Finset.sum_le_sum hpt
    _ = ∑ k ∈ K, ∑ n ∈ S, W k * (f n * (if |Real.log n - Z k| ≤ 1 / 2 then 1 else 0)) :=
        Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm

/-- The window `j = ⌊log n + ½⌋` of `n ≥ 2`: `j ≥ 1` and `|log n − j| ≤ ½`. -/
theorem window_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ ⌊Real.log n + 1 / 2⌋₊ ∧ |Real.log n - (⌊Real.log n + 1 / 2⌋₊ : ℝ)| ≤ 1 / 2 := by
  have hlog2 : 1 / 2 ≤ Real.log n := by
    have h2 : Real.log 2 ≤ Real.log n :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have := Real.log_two_gt_d9
    linarith
  have h0 : 0 ≤ Real.log n + 1 / 2 := by linarith
  have hf := Nat.floor_le h0
  have hf' := Nat.lt_floor_add_one (Real.log n + 1 / 2)
  refine ⟨Nat.le_floor (by push_cast; linarith), abs_le.mpr ⟨by linarith, by linarith⟩⟩

theorem exp_neg_half_le : Real.exp (-(1 / 2)) ≤ 2 / 3 := by
  have h := Real.add_one_le_exp (1 / 2 : ℝ)
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  linarith

/-- `Σ_{j≤J} r^j ≤ r^{J+1}/(r − 1)` for `r > 1`. -/
theorem sum_range_pow_le_of_one_lt {r : ℝ} (hr : 1 < r) (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), r ^ j ≤ r ^ (J + 1) / (r - 1) := by
  rw [geom_sum_eq hr.ne', div_le_div_iff_of_pos_right (by linarith)]
  linarith

/-- `Σ_{k<K} r^k ≤ 1/(1 − r)` for `0 ≤ r < 1`. -/
theorem sum_range_pow_le_of_lt_one {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (K : ℕ) :
    ∑ k ∈ Finset.range K, r ^ k ≤ 1 / (1 - r) := by
  have e : (r ^ K - 1) / (r - 1) = (1 - r ^ K) / (1 - r) := by
    rw [← neg_sub (r ^ K) 1, ← neg_sub r 1, neg_div_neg_eq]
  rw [geom_sum_eq hr.ne, e]
  exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hr0 K]) (by linarith)

/-! ## Local mass gives the notch bounds -/

/-- **Bounded local mass gives notch-boundedness.** -/
theorem notchBounded_of_localMassBounded {d : ℕ → ℝ} (hd0 : d 0 = 0) (hd1 : d 1 = 0) {M : ℝ}
    (hM : 0 ≤ M) (h : LocalMassBounded d M) : NotchBounded d (5 * M) := by
  set f : ℕ → ℝ := fun n => |d n| / n with hfdef
  have hf0 : ∀ n, 0 ≤ f n := fun n => div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
  have hfz : ∀ n, f n ≠ 0 → 2 ≤ n := by
    intro n hn
    by_contra h2
    interval_cases n <;> simp [hfdef, hd0, hd1] at hn
  have hlocS : ∀ (S : Finset ℕ) {Z : ℝ}, 1 ≤ Z →
      ∑ n ∈ S, f n * (if |Real.log n - Z| ≤ 1 / 2 then 1 else 0) ≤ M := fun S Z hZ =>
    h.sum_finset_le hZ S
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have he : Real.exp (-(1 / 2)) ≤ 2 / 3 := exp_neg_half_le
  have hr1 : 1 < Real.exp (1 / 2) := Real.one_lt_exp_iff.mpr (by norm_num)
  have hr32 : 3 / 2 ≤ Real.exp (1 / 2) := by have := Real.add_one_le_exp (1 / 2 : ℝ); linarith
  refine ⟨⟨0, le_rfl, fun N hN => ?_⟩, ⟨0, le_rfl, fun N hN => ?_⟩, ⟨2, fun N hN2 hN M' => ?_⟩,
    fun σ hσ => ?_⟩
  · -- harmonic sums
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    set J : ℕ := ⌊Real.log N + 1 / 2⌋₊ with hJ
    have hcov : ∀ n ∈ Finset.range (N + 1), f n ≠ 0 → ∃ k ∈ Finset.Icc 1 J,
        |Real.log n - (k : ℝ)| ≤ 1 / 2 ∧ (1 : ℝ) ≤ 1 := by
      intro n hn hfn
      have h2 := hfz n hfn
      obtain ⟨hj1, hwin⟩ := window_of_two_le h2
      refine ⟨⌊Real.log n + 1 / 2⌋₊, Finset.mem_Icc.mpr ⟨hj1, ?_⟩, hwin, le_rfl⟩
      refine Nat.floor_le_floor ?_
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      have := Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) hnN
      linarith
    have hcover := sum_mul_le_windows (w := fun _ => (1 : ℝ)) hf0 (Finset.range (N + 1))
      (Finset.Icc 1 J) (fun k => (k : ℝ)) (fun _ => 1) (fun _ _ => zero_le_one) hcov
    have hbound : ∑ k ∈ Finset.Icc 1 J, (1 : ℝ) * ∑ n ∈ Finset.range (N + 1),
        f n * (if |Real.log n - (k : ℝ)| ≤ 1 / 2 then 1 else 0) ≤ J * M := by
      calc _ ≤ ∑ k ∈ Finset.Icc 1 J, M := Finset.sum_le_sum fun k hk => by
            rw [one_mul]
            exact hlocS _ (by exact_mod_cast (Finset.mem_Icc.mp hk).1)
        _ = J * M := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
    have hJle : (J : ℝ) ≤ Real.log N + 1 / 2 := Nat.floor_le (by linarith)
    have e : ∑ n ∈ Finset.range (N + 1), |d n| / n = ∑ n ∈ Finset.range (N + 1), f n * 1 :=
      Finset.sum_congr rfl fun n _ => by rw [mul_one]
    rw [e]
    have hJM : (J : ℝ) * M ≤ (Real.log N + 1 / 2) * M := mul_le_mul_of_nonneg_right hJle hM
    nlinarith [mul_nonneg hM hlogN]
  · -- square-root sums
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    set J : ℕ := ⌊Real.log N + 1 / 2⌋₊ with hJ
    set r : ℝ := Real.exp (1 / 2) with hr
    have hW : ∀ k : ℕ, Real.exp (((k : ℝ) + 1 / 2) / 2) = Real.exp (1 / 4) * r ^ k := by
      intro k
      rw [hr, ← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
    have hcov : ∀ n ∈ Finset.range (N + 1), f n ≠ 0 → ∃ k ∈ Finset.Icc 1 J,
        |Real.log n - (k : ℝ)| ≤ 1 / 2 ∧ Real.sqrt n ≤ Real.exp (((k : ℝ) + 1 / 2) / 2) := by
      intro n hn hfn
      have h2 := hfz n hfn
      obtain ⟨hj1, hwin⟩ := window_of_two_le h2
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      refine ⟨⌊Real.log n + 1 / 2⌋₊, Finset.mem_Icc.mpr ⟨hj1, ?_⟩, hwin, ?_⟩
      · refine Nat.floor_le_floor ?_
        have hnN : (n : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
        have := Real.log_le_log hn0 hnN
        linarith
      · rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0]
        exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp hwin).2])
    have hcover := sum_mul_le_windows (w := fun n => Real.sqrt n) hf0 (Finset.range (N + 1))
      (Finset.Icc 1 J) (fun k => (k : ℝ)) (fun k => Real.exp (((k : ℝ) + 1 / 2) / 2))
      (fun _ _ => (Real.exp_pos _).le) hcov
    have hbound : ∑ k ∈ Finset.Icc 1 J, Real.exp (((k : ℝ) + 1 / 2) / 2) *
        ∑ n ∈ Finset.range (N + 1), f n * (if |Real.log n - (k : ℝ)| ≤ 1 / 2 then 1 else 0) ≤
        M * (Real.exp (1 / 4) * (r ^ (J + 1) / (r - 1))) := by
      calc _ ≤ ∑ k ∈ Finset.Icc 1 J, Real.exp (((k : ℝ) + 1 / 2) / 2) * M :=
            Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left
              (hlocS _ (by exact_mod_cast (Finset.mem_Icc.mp hk).1)) (Real.exp_pos _).le
        _ ≤ ∑ k ∈ Finset.range (J + 1), Real.exp (((k : ℝ) + 1 / 2) / 2) * M :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (fun k hk => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hk).2))
              fun k _ _ => mul_nonneg (Real.exp_pos _).le hM
        _ = M * (Real.exp (1 / 4) * ∑ k ∈ Finset.range (J + 1), r ^ k) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => by rw [hW]; ring
        _ ≤ M * (Real.exp (1 / 4) * (r ^ (J + 1) / (r - 1))) := by
            gcongr
            exact sum_range_pow_le_of_one_lt hr1 J
    -- `r^(J+1) ≤ e^{3/4} √N`
    have hJle : (J : ℝ) ≤ Real.log N + 1 / 2 := Nat.floor_le (by
      have := Real.log_natCast_nonneg N; linarith)
    have hrJ : r ^ (J + 1) ≤ Real.exp (3 / 4) * Real.sqrt N := by
      rw [hr, ← Real.exp_nat_mul, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hN0, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by push_cast; linarith)
    have he34 : Real.exp (1 / 4) * Real.exp (3 / 4) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    have hex : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    have hfin : M * (Real.exp (1 / 4) * (r ^ (J + 1) / (r - 1))) ≤ M * (6 * Real.sqrt N) := by
      refine mul_le_mul_of_nonneg_left ?_ hM
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]
      have h1 : Real.exp (1 / 4) * r ^ (J + 1) ≤ Real.exp (1 / 4) * (Real.exp (3 / 4) * Real.sqrt N) :=
        mul_le_mul_of_nonneg_left hrJ (Real.exp_pos _).le
      have hsq := Real.sqrt_nonneg (N : ℝ)
      nlinarith
    have e : ∑ n ∈ Finset.range (N + 1), |d n| / Real.sqrt n =
        ∑ n ∈ Finset.range (N + 1), f n * Real.sqrt n := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [hfdef, hd0]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hs := Real.sqrt_pos.mpr hn0
      have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
      simp only [hfdef]
      field_simp
      rw [Real.sq_sqrt hn0.le]
    rw [e]
    have hsq := Real.sqrt_nonneg (N : ℝ)
    nlinarith [mul_nonneg hM hsq]
  · -- the tail `Σ_{N<n≤M'} |d| n^{−3/2}`
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    set K' : ℕ := ⌊Real.log M' - Real.log N⌋₊ + 1 with hK'
    set q : ℝ := Real.exp (-(1 / 2)) with hq
    have hq0 : 0 ≤ q := (Real.exp_pos _).le
    have hcov : ∀ n ∈ Finset.Ioc N M', f n ≠ 0 → ∃ k ∈ Finset.range K',
        |Real.log n - (Real.log N + k + 1 / 2)| ≤ 1 / 2 ∧
          (Real.sqrt n)⁻¹ ≤ (Real.sqrt N)⁻¹ * q ^ k := by
      intro n hn _
      obtain ⟨hNn, hnM⟩ := Finset.mem_Ioc.mp hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hlt : Real.log N < Real.log n := Real.log_lt_log hN0 (by exact_mod_cast hNn)
      have hle : Real.log n ≤ Real.log M' := Real.log_le_log hn0 (by exact_mod_cast hnM)
      set k : ℕ := ⌊Real.log n - Real.log N⌋₊ with hk
      have hk1 := Nat.floor_le (show 0 ≤ Real.log n - Real.log N by linarith)
      have hk2 := Nat.lt_floor_add_one (Real.log n - Real.log N)
      refine ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_le_floor (by linarith))),
        abs_le.mpr ⟨by linarith, by linarith⟩, ?_⟩
      rw [hq, ← Real.exp_nat_mul, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0,
        Real.rpow_def_of_pos hN0, ← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    have hcover := sum_mul_le_windows (w := fun n => (Real.sqrt n)⁻¹) hf0 (Finset.Ioc N M')
      (Finset.range K') (fun k => Real.log N + k + 1 / 2) (fun k => (Real.sqrt N)⁻¹ * q ^ k)
      (fun _ _ => mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (pow_nonneg hq0 _)) hcov
    have hbound : ∑ k ∈ Finset.range K', (Real.sqrt N)⁻¹ * q ^ k *
        ∑ n ∈ Finset.Ioc N M', f n *
          (if |Real.log n - (Real.log N + k + 1 / 2)| ≤ 1 / 2 then 1 else 0) ≤
        (Real.sqrt N)⁻¹ * M * 3 := by
      calc _ ≤ ∑ k ∈ Finset.range K', (Real.sqrt N)⁻¹ * q ^ k * M :=
            Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
              (hlocS _ (by
                have h2 : Real.log 2 ≤ Real.log N :=
                  Real.log_le_log (by norm_num) (by exact_mod_cast hN2)
                have := Real.log_two_gt_d9
                have hk0 := Nat.cast_nonneg (α := ℝ) k
                linarith))
              (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (pow_nonneg hq0 _))
        _ = (Real.sqrt N)⁻¹ * M * ∑ k ∈ Finset.range K', q ^ k := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        _ ≤ (Real.sqrt N)⁻¹ * M * 3 := by
            refine mul_le_mul_of_nonneg_left ?_
              (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) hM)
            refine (sum_range_pow_le_of_lt_one hq0 (by linarith) K').trans ?_
            rw [div_le_iff₀ (by linarith)]
            linarith
    have e : ∑ n ∈ Finset.Ioc N M', |d n| * (n : ℝ) ^ (-(1 + 1 / 2 : ℝ)) =
        ∑ n ∈ Finset.Ioc N M', f n * (Real.sqrt n)⁻¹ := by
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn0 : (0 : ℝ) < n := by
        exact_mod_cast (show 0 < n by have := (Finset.mem_Ioc.mp hn).1; omega)
      rw [rpow_neg_one_add_half_eq_inv hn0, mul_inv]
      simp only [hfdef]
      rw [div_eq_mul_inv]; ring
    rw [e]
    have hCT := two_le_vonMangoldtThreeHalvesTail
    have hi0 : 0 ≤ (Real.sqrt N)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    have : (Real.sqrt N)⁻¹ * M * 3 ≤ 5 * M * (vonMangoldtThreeHalvesTail * (Real.sqrt N)⁻¹) := by
      nlinarith [mul_nonneg hi0 hM]
    linarith
  · -- summability for `σ > 1`
    set q : ℝ := Real.exp (-(σ - 1)) with hq
    have hq0 : 0 ≤ q := (Real.exp_pos _).le
    have hq1 : q < 1 := by
      have := Real.exp_lt_exp.mpr (show -(σ - 1) < 0 by linarith)
      rwa [Real.exp_zero] at this
    set B : ℝ := M * Real.exp ((σ - 1) / 2) * (1 / (1 - q)) with hB
    refine summable_of_sum_range_le (c := B) (fun n => by positivity) fun N => ?_
    set J : ℕ := ⌊Real.log N + 1 / 2⌋₊ with hJ
    have hcov : ∀ n ∈ Finset.range N, f n ≠ 0 → ∃ k ∈ Finset.Icc 1 J,
        |Real.log n - (k : ℝ)| ≤ 1 / 2 ∧
          (n : ℝ) ^ (1 - σ) ≤ Real.exp ((σ - 1) / 2) * q ^ k := by
      intro n hn hfn
      have h2 := hfz n hfn
      obtain ⟨hj1, hwin⟩ := window_of_two_le h2
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      refine ⟨⌊Real.log n + 1 / 2⌋₊, Finset.mem_Icc.mpr ⟨hj1, ?_⟩, hwin, ?_⟩
      · refine Nat.floor_le_floor ?_
        have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.mp hn).le
        have := Real.log_le_log hn0 hnN
        linarith
      · rw [Real.rpow_def_of_pos hn0, hq, ← Real.exp_nat_mul, ← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have hw := (abs_le.mp hwin).1
        nlinarith
    have hcover := sum_mul_le_windows (w := fun n => (n : ℝ) ^ (1 - σ)) hf0 (Finset.range N)
      (Finset.Icc 1 J) (fun k => (k : ℝ)) (fun k => Real.exp ((σ - 1) / 2) * q ^ k)
      (fun _ _ => mul_nonneg (Real.exp_pos _).le (pow_nonneg hq0 _)) hcov
    have hbound : ∑ k ∈ Finset.Icc 1 J, Real.exp ((σ - 1) / 2) * q ^ k *
        ∑ n ∈ Finset.range N, f n * (if |Real.log n - (k : ℝ)| ≤ 1 / 2 then 1 else 0) ≤ B := by
      calc _ ≤ ∑ k ∈ Finset.Icc 1 J, Real.exp ((σ - 1) / 2) * q ^ k * M :=
            Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left
              (hlocS _ (by exact_mod_cast (Finset.mem_Icc.mp hk).1))
              (mul_nonneg (Real.exp_pos _).le (pow_nonneg hq0 _))
        _ ≤ ∑ k ∈ Finset.range (J + 1), Real.exp ((σ - 1) / 2) * q ^ k * M :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (fun k hk => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hk).2))
              fun k _ _ => mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hq0 _)) hM
        _ = M * Real.exp ((σ - 1) / 2) * ∑ k ∈ Finset.range (J + 1), q ^ k := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        _ ≤ B := mul_le_mul_of_nonneg_left (sum_range_pow_le_of_lt_one hq0 hq1 _)
            (mul_nonneg hM (Real.exp_pos _).le)
    have e : ∑ n ∈ Finset.range N, |d n| * (n : ℝ) ^ (-σ) =
        ∑ n ∈ Finset.range N, f n * (n : ℝ) ^ (1 - σ) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [hfdef, hd0]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      simp only [hfdef]
      rw [Real.rpow_sub hn0, Real.rpow_one, Real.rpow_neg hn0.le]
      field_simp
    rw [e]
    exact hcover.trans hbound

/-- Notch-boundedness is monotone in the level. -/
theorem _root_.RHTower.PrimeSmallDeviation.NotchBounded.mono_level {d : ℕ → ℝ} {η η' : ℝ} (h : NotchBounded d η) (hη : η ≤ η') :
    NotchBounded d η' := by
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨?_, ?_, ?_, h.summable⟩
  · obtain ⟨A, hA, hb⟩ := h.harm
    refine ⟨A, hA, fun N hN => (hb N hN).trans ?_⟩
    have : 0 ≤ Real.log N + (Real.log 4 + 4) := by
      have := Real.log_natCast_nonneg N; linarith
    nlinarith
  · obtain ⟨A, hA, hb⟩ := h.sqrt
    refine ⟨A, hA, fun N hN => (hb N hN).trans ?_⟩
    have : 0 ≤ (2 * Real.log 4 + 16) * Real.sqrt N := by positivity
    nlinarith
  · obtain ⟨P₀, hb⟩ := h.tail
    refine ⟨P₀, fun N h1 h2 M => (hb N h1 h2 M).trans ?_⟩
    have : 0 ≤ vonMangoldtThreeHalvesTail * (Real.sqrt N)⁻¹ :=
      mul_nonneg vonMangoldtThreeHalvesTail_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
    nlinarith

/-- Notch-boundedness is unchanged by a finite modification. -/
theorem _root_.RHTower.PrimeSmallDeviation.NotchBounded.of_eq_of_ge {d d' : ℕ → ℝ} {η : ℝ} (h : NotchBounded d' η) {n₀ : ℕ}
    (heq : ∀ n, n₀ ≤ n → d n = d' n) : NotchBounded d η := by
  have hpt : ∀ (w : ℕ → ℝ), (∀ n, 0 ≤ w n) → ∀ n, |d n| * w n ≤
      |d' n| * w n + (if n < n₀ then |d n| * w n else 0) := by
    intro w hw n
    by_cases hn : n < n₀
    · rw [if_pos hn]; have := mul_nonneg (abs_nonneg (d' n)) (hw n); linarith
    · rw [if_neg hn, heq n (not_lt.mp hn)]; linarith
  have hhead : ∀ (w : ℕ → ℝ), (∀ n, 0 ≤ w n) → ∀ N,
      ∑ n ∈ Finset.range (N + 1), (if n < n₀ then |d n| * w n else 0) ≤
        ∑ n ∈ Finset.range n₀, |d n| * w n := by
    intro w hw N
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ =>
      mul_nonneg (abs_nonneg _) (hw n)
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hn).2
  refine ⟨?_, ?_, ?_, fun σ hσ => ?_⟩
  · obtain ⟨A, hA, hb⟩ := h.harm
    refine ⟨A + ∑ n ∈ Finset.range n₀, |d n| * (n : ℝ)⁻¹,
      add_nonneg hA (Finset.sum_nonneg fun n _ => by positivity), fun N hN => ?_⟩
    have h1 := Finset.sum_le_sum fun n (_ : n ∈ Finset.range (N + 1)) =>
      hpt (fun n => (n : ℝ)⁻¹) (fun n => by positivity) n
    rw [Finset.sum_add_distrib] at h1
    have h2 := hhead (fun n => (n : ℝ)⁻¹) (fun n => by positivity) N
    have h3 := hb N hN
    simp only [div_eq_mul_inv] at h3 ⊢
    linarith
  · obtain ⟨A, hA, hb⟩ := h.sqrt
    refine ⟨A + ∑ n ∈ Finset.range n₀, |d n| * (Real.sqrt n)⁻¹,
      add_nonneg hA (Finset.sum_nonneg fun n _ => by positivity), fun N hN => ?_⟩
    have h1 := Finset.sum_le_sum fun n (_ : n ∈ Finset.range (N + 1)) =>
      hpt (fun n => (Real.sqrt n)⁻¹) (fun n => by positivity) n
    rw [Finset.sum_add_distrib] at h1
    have h2 := hhead (fun n => (Real.sqrt n)⁻¹) (fun n => by positivity) N
    have h3 := hb N hN
    simp only [div_eq_mul_inv] at h3 ⊢
    linarith
  · obtain ⟨P₀, hb⟩ := h.tail
    refine ⟨max P₀ n₀, fun N hN h1 M => ?_⟩
    refine le_of_eq_of_le (Finset.sum_congr rfl fun n hn => ?_) (hb N ((le_max_left _ _).trans hN) h1 M)
    rw [heq n ((le_max_right _ _).trans (hN.trans (Finset.mem_Ioc.mp hn).1.le))]
  · have hs := h.summable σ hσ
    have hfin : Summable fun n : ℕ => if n < n₀ then |d n| * (n : ℝ) ^ (-σ) else 0 :=
      summable_of_ne_finset_zero (s := Finset.range n₀) fun n hn => by
        rw [if_neg (fun h => hn (Finset.mem_range.mpr h))]
    refine (hs.add hfin).of_nonneg_of_le (fun n => by positivity) fun n => ?_
    exact hpt (fun n => (n : ℝ) ^ (-σ)) (fun n => by positivity) n

/-- **Local mass tending to zero**: for every `η > 0`, all far unit windows carry
`Σ_{|log n − Z| ≤ ½} |d(n)|/n ≤ η`. -/
def LocalMassTendsZero (d : ℕ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ Z₀ : ℝ, ∀ Z, Z₀ ≤ Z → ∀ N₁ : ℕ,
    ∑ n ∈ Finset.range N₁, |d n| / n * (if |Real.log n - Z| ≤ 1 / 2 then 1 else 0) ≤ η

/-- **Local mass tending to zero gives notch-smallness.** -/
theorem notchSmall_of_localMassTendsZero {d : ℕ → ℝ} (hd0 : d 0 = 0) (hd1 : d 1 = 0)
    (h : LocalMassTendsZero d) : NotchSmall d := by
  have key : ∀ η : ℝ, 0 < η → NotchBounded d η := by
    intro η hη
    obtain ⟨Z₀, hZ₀⟩ := h (η / 5) (by positivity)
    set n₀ : ℕ := ⌈Real.exp (max Z₀ 1 + 1)⌉₊ with hn₀
    set d' : ℕ → ℝ := fun n => if n < n₀ then 0 else d n with hd'
    have hd'0 : d' 0 = 0 := by simp only [hd']; split_ifs <;> simp [hd0]
    have hd'1 : d' 1 = 0 := by simp only [hd']; split_ifs <;> simp [hd1]
    have hloc : LocalMassBounded d' (η / 5) := by
      intro Z hZ N₁
      rcases le_or_gt Z₀ Z with hZZ | hZZ
      · refine le_trans (Finset.sum_le_sum fun n _ => ?_) (hZ₀ Z hZZ N₁)
        have hw : 0 ≤ (if |Real.log n - Z| ≤ 1 / 2 then (1 : ℝ) else 0) := by
          split_ifs <;> norm_num
        refine mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)) hw
        simp only [hd']; split_ifs <;> simp
      · refine le_trans (le_of_eq (Finset.sum_eq_zero fun n _ => ?_)) (by positivity)
        by_cases hw : |Real.log n - Z| ≤ 1 / 2
        · have hlt : n < n₀ := by
            have hn1 : 1 ≤ n := by
              by_contra hn
              have : n = 0 := by omega
              rw [this, Nat.cast_zero, Real.log_zero] at hw
              have := (abs_le.mp hw).1
              linarith
            have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
            have hlog : Real.log n < max Z₀ 1 + 1 := by
              have := (abs_le.mp hw).2
              have := le_max_left Z₀ 1
              linarith
            have : (n : ℝ) < Real.exp (max Z₀ 1 + 1) := by
              rw [← Real.exp_log hn0]; exact Real.exp_lt_exp.mpr hlog
            exact_mod_cast this.trans_le (Nat.le_ceil _)
          simp [hd', hlt]
        · rw [if_neg hw, mul_zero]
    have hnb := notchBounded_of_localMassBounded hd'0 hd'1 (by positivity) hloc
    have e : 5 * (η / 5) = η := by ring
    rw [e] at hnb
    exact hnb.of_eq_of_ge (n₀ := n₀) fun n hn => by
      simp only [hd']; rw [if_neg (not_lt.mpr hn)]
  exact ⟨fun η hη => (key η hη).harm, fun η hη => (key η hη).sqrt,
    fun η hη => (key η hη).tail, (key 1 one_pos).summable⟩

/-! ## Deviations of size `C(1 + Λ)` -/

/-- **Local mass of a deviation of size `C(1 + Λ)`**: at most `C (2 log 4 + 18) e^{1/2}`, by the
square-root Chebyshev bound. -/
theorem localMassBounded_of_abs_le {d : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ n, |d n| ≤ C * (1 + ArithmeticFunction.vonMangoldt n)) :
    LocalMassBounded d (C * ((2 * Real.log 4 + 18) * Real.exp (1 / 2))) := by
  intro Z hZ N₁
  set K : ℕ := ⌊Real.exp (Z + 1 / 2)⌋₊ with hK
  set c : ℝ := Real.exp (-((Z - 1 / 2) / 2)) with hc
  have hc0 : 0 ≤ c := (Real.exp_pos _).le
  set g : ℕ → ℝ := fun n => (1 + (ArithmeticFunction.vonMangoldt n : ℝ)) * (Real.sqrt n)⁻¹
    with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => by
    have := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    simp only [hg]; positivity
  have hpt : ∀ n ∈ Finset.range N₁, |d n| / n * (if |Real.log n - Z| ≤ 1 / 2 then 1 else 0) ≤
      C * c * (g n * (if n ≤ K then 1 else 0)) := by
    intro n _
    split_ifs with h1 h2 h2
    · rw [mul_one, mul_one]
      have hlow : Z - 1 / 2 ≤ Real.log n := by linarith [(abs_le.mp h1).1]
      have hn1 : 1 ≤ n := by
        by_contra hn
        have : n = 0 := by omega
        rw [this, Nat.cast_zero, Real.log_zero] at hlow
        linarith
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hsq : Real.exp ((Z - 1 / 2) / 2) ≤ Real.sqrt n := by
        rw [Real.le_sqrt (by positivity) hn0.le, ← Real.exp_log hn0, ← Real.exp_nat_mul]
        exact Real.exp_le_exp.mpr (by push_cast; linarith)
      have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
      have hinv : (n : ℝ)⁻¹ ≤ c * (Real.sqrt n)⁻¹ := by
        have hnn : (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt hn0.le).symm
        rw [hc, Real.exp_neg, ← mul_inv]
        calc (n : ℝ)⁻¹ = (Real.sqrt n * Real.sqrt n)⁻¹ := by rw [← hnn]
          _ ≤ (Real.exp ((Z - 1 / 2) / 2) * Real.sqrt n)⁻¹ :=
              inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_right hsq hs0.le)
      have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      rw [div_eq_mul_inv]
      calc |d n| * (n : ℝ)⁻¹
          ≤ (C * (1 + ArithmeticFunction.vonMangoldt n)) * (c * (Real.sqrt n)⁻¹) :=
            mul_le_mul (hd n) hinv (inv_nonneg.mpr hn0.le) (mul_nonneg hC (by linarith))
        _ = C * c * g n := by simp only [hg]; ring
    · exfalso
      have hup : Real.log n ≤ Z + 1 / 2 := by linarith [(abs_le.mp h1).2]
      have hn1 : 1 ≤ n := by
        by_contra hn
        have : n = 0 := by omega
        have hlow : Z - 1 / 2 ≤ Real.log n := by linarith [(abs_le.mp h1).1]
        rw [this, Nat.cast_zero, Real.log_zero] at hlow
        linarith
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      exact h2 (Nat.le_floor (by rw [← Real.exp_log hn0]; exact Real.exp_le_exp.mpr hup))
    · rw [mul_zero, mul_one]
      exact mul_nonneg (mul_nonneg hC hc0) (hg0 n)
    · rw [mul_zero, mul_zero, mul_zero]
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum]
  have hsub : ∑ n ∈ Finset.range N₁, g n * (if n ≤ K then 1 else 0) ≤
      ∑ n ∈ Finset.range (K + 1), g n := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N₁) (fun n => n ≤ K)]
    have h2 : ∑ n ∈ (Finset.range N₁).filter (fun n => ¬ n ≤ K),
        g n * (if n ≤ K then 1 else 0) = 0 :=
      Finset.sum_eq_zero fun n hn => by rw [if_neg (Finset.mem_filter.mp hn).2, mul_zero]
    rw [h2, add_zero]
    calc ∑ n ∈ (Finset.range N₁).filter (fun n => n ≤ K), g n * (if n ≤ K then 1 else 0)
        = ∑ n ∈ (Finset.range N₁).filter (fun n => n ≤ K), g n :=
          Finset.sum_congr rfl fun n hn => by rw [if_pos (Finset.mem_filter.mp hn).2, mul_one]
      _ ≤ ∑ n ∈ Finset.range (K + 1), g n :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun n hn => Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hn).2; omega))
            fun n _ _ => hg0 n
  have hK1 : 1 ≤ K := Nat.le_floor (by
    push_cast
    have : (1 : ℝ) ≤ Real.exp (Z + 1 / 2) := Real.one_le_exp (by linarith)
    exact this)
  have hgsum : ∑ n ∈ Finset.range (K + 1), g n ≤ (2 * Real.log 4 + 18) * Real.sqrt K := by
    have e : ∑ n ∈ Finset.range (K + 1), g n = ∑ n ∈ Finset.range (K + 1), (Real.sqrt n)⁻¹ +
        ∑ n ∈ Finset.range (K + 1), (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun n _ => by simp only [hg]; rw [div_eq_mul_inv]; ring
    rw [e]
    have h1 := sum_range_inv_sqrt_le_two_mul_sqrt K
    have h2 := sum_range_vonMangoldt_div_sqrt_le hK1
    linarith
  have hsqK : Real.sqrt K ≤ Real.exp ((Z + 1 / 2) / 2) := by
    rw [Real.sqrt_le_left (by positivity), ← Real.exp_nat_mul]
    push_cast
    rw [show (2 : ℝ) * ((Z + 1 / 2) / 2) = Z + 1 / 2 by ring]
    exact Nat.floor_le (by positivity)
  have hlog4 := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
  have hce : c * Real.exp ((Z + 1 / 2) / 2) = Real.exp (1 / 2) := by
    rw [hc, ← Real.exp_add]; congr 1; ring
  calc C * c * ∑ n ∈ Finset.range N₁, g n * (if n ≤ K then 1 else 0)
      ≤ C * c * ((2 * Real.log 4 + 18) * Real.sqrt K) :=
        mul_le_mul_of_nonneg_left (hsub.trans hgsum) (mul_nonneg hC hc0)
    _ ≤ C * c * ((2 * Real.log 4 + 18) * Real.exp ((Z + 1 / 2) / 2)) := by gcongr
    _ = C * ((2 * Real.log 4 + 18) * Real.exp (1 / 2)) := by rw [← hce]; ring

/-! ## Nonnegative Weil-positive weights -/

theorem profilePrimitive_mono {φ : ℝ → ℝ} (hφc : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x) {y y' : ℝ}
    (h : y' ≤ y) : WeilOneSided.profilePrimitive φ y' ≤ WeilOneSided.profilePrimitive φ y := by
  unfold WeilOneSided.profilePrimitive
  rw [← intervalIntegral.integral_add_adjacent_intervals (hφc.intervalIntegrable (μ := volume) (-1) y')
    (hφc.intervalIntegrable y' y)]
  have := intervalIntegral.integral_nonneg (μ := volume) h (fun x _ => hφ0 x)
  linarith

/-- **Nonnegative Weil-positive weights have bounded local mass.** If `lam` is full-cone
Weil-positive and `lam(n) ≥ 0` for `n ≥ 2`, then `d = lam − Λ` has bounded local mass. -/
theorem exists_localMassBounded_of_nonneg {lam : ℕ → ℝ} (hW : RHTower.WeilPositiveFull lam)
    (hnn : ∀ n, 2 ≤ n → 0 ≤ lam n) :
    ∃ M : ℝ, 0 ≤ M ∧ LocalMassBounded (WeilOneSided.coneDeviation lam) M := by
  obtain ⟨φ, Cw, L₁, hφc, hφ0, hφs, hI, hL₁, hCw0, hwin⟩ :=
    WeilOneSided.exists_profile_window_le_inv_sq
  set I := WeilOneSided.profilePrimitive φ 1 with hIdef
  set d := WeilOneSided.coneDeviation lam with hddef
  -- a bound for the profile
  obtain ⟨Φ₀, hΦ₀⟩ := (isCompact_Icc (a := (-1 / 2 : ℝ)) (b := 1 / 2)).exists_bound_of_continuousOn
    hφc.continuousOn
  set Φm : ℝ := max Φ₀ 0 with hΦm
  have hΦm0 : 0 ≤ Φm := le_max_right _ _
  have hφle : ∀ x, φ x ≤ Φm := fun x => by
    by_cases hx : |x| ≤ 1 / 2
    · have := hΦ₀ x ⟨by linarith [(abs_le.mp hx).1], (abs_le.mp hx).2⟩
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_max_left _ _))
    · rw [hφs x (not_le.mp hx)]; exact hΦm0
  -- the local mass of `Λ`
  set MΛ : ℝ := (2 * Real.log 4 + 18) * Real.exp (1 / 2) with hMΛ
  have hlog4 := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
  have hMΛ0 : 0 ≤ MΛ := by positivity
  have hΛloc : LocalMassBounded (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) MΛ := by
    have h := localMassBounded_of_abs_le (d := fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (C := 1) zero_le_one fun n => by
        have := ArithmeticFunction.vonMangoldt_nonneg (n := n)
        rw [abs_of_nonneg this]; linarith
    rwa [one_mul] at h
  -- `g = d + Λ` is `lam` on `n ≥ 2` and `0` below
  set g : ℕ → ℝ := fun n => d n + ArithmeticFunction.vonMangoldt n with hgdef
  have hg0 : ∀ n, 0 ≤ g n := fun n => by
    simp only [hgdef, hddef, WeilOneSided.coneDeviation]
    split_ifs with h2
    · linarith [hnn n h2]
    · interval_cases n <;> simp
  have hdg : ∀ n, |d n| ≤ |g n| + |(ArithmeticFunction.vonMangoldt n : ℝ)| := fun n => by
    have : d n = g n - ArithmeticFunction.vonMangoldt n := by simp only [hgdef]; ring
    rw [this]; exact abs_sub _ _
  -- local mass of `g` at large `Z`
  set Mbig : ℝ := 4 * (Cw + Φm * MΛ) / I with hMbig
  have hbig : ∀ Z : ℝ, L₁ + 2 ≤ Z → ∀ N₁ : ℕ,
      ∑ n ∈ Finset.range N₁, |g n| / n * (if |Real.log n - Z| ≤ 1 / 2 then 1 else 0) ≤ Mbig := by
    intro Z hZ N₁
    set X := Z - 2 with hX
    set X' := Z + 2 with hX'
    set N₂ : ℕ := max N₁ ⌈Real.exp (X' + 1)⌉₊ with hN₂
    have hmono : ∑ n ∈ Finset.range N₁, |g n| / n * (if |Real.log n - Z| ≤ 1 / 2 then 1 else 0) ≤
        ∑ n ∈ Finset.range N₂, |g n| / n * (if |Real.log n - Z| ≤ 1 / 2 then 1 else 0) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (le_max_left _ _))
        fun n _ _ => localWindow_nonneg g Z n
    -- termwise domination by the primitive difference
    have hterm : ∀ n, I * (|g n| / n * (if |Real.log n - Z| ≤ 1 / 2 then 1 else 0)) ≤
        g n / n * (WeilOneSided.profilePrimitive φ (Real.log n - X) -
          WeilOneSided.profilePrimitive φ (Real.log n - X')) := by
      intro n
      rw [abs_of_nonneg (hg0 n)]
      have hgn : 0 ≤ g n / n := div_nonneg (hg0 n) (Nat.cast_nonneg _)
      split_ifs with h1
      · have e1 : WeilOneSided.profilePrimitive φ (Real.log n - X) = I :=
          WeilOneSided.profilePrimitive_eq_one hφc hφs (by linarith [(abs_le.mp h1).1])
        have e2 : WeilOneSided.profilePrimitive φ (Real.log n - X') = 0 :=
          WeilOneSided.profilePrimitive_eq_zero hφs (by linarith [(abs_le.mp h1).2])
        rw [e1, e2]; ring_nf; exact le_rfl
      · rw [mul_zero, mul_zero]
        exact mul_nonneg hgn (sub_nonneg.mpr (profilePrimitive_mono hφc hφ0 (by linarith)))
    have hsum : I * ∑ n ∈ Finset.range N₂, |g n| / n *
        (if |Real.log n - Z| ≤ 1 / 2 then 1 else 0) ≤
        ∫ L in X..X', ∑ n ∈ Finset.range N₂, g n * φ (Real.log n - L) / n := by
      rw [WeilOneSided.integral_windowSum_eq hφc g N₂ X X', Finset.mul_sum]
      exact Finset.sum_le_sum fun n _ => hterm n
    -- the windows of `g` are bounded on `[X, X']`
    have hwinb : ∀ L ∈ Set.uIoc X X',
        ‖∑ n ∈ Finset.range N₂, g n * φ (Real.log n - L) / n‖ ≤ Cw + Φm * MΛ := by
      intro L hL
      rw [Set.uIoc_of_le (by linarith)] at hL
      have hL1 : L₁ ≤ L := by linarith [hL.1]
      have hLone : 1 ≤ L := hL₁.trans hL1
      have hsplit : ∑ n ∈ Finset.range N₂, g n * φ (Real.log n - L) / n =
          ∑ n ∈ Finset.range N₂, d n * φ (Real.log n - L) / n +
            ∑ n ∈ Finset.range N₂, (ArithmeticFunction.vonMangoldt n : ℝ) *
              φ (Real.log n - L) / n := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun n _ => by simp only [hgdef]; ring
      have hd := hwin lam hW L hL1 N₂ (by
        refine le_trans (Real.exp_le_exp.mpr (show L + 1 ≤ X' + 1 by linarith [hL.2])) ?_
        exact le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right N₁ _))
      have hdC : Cw * (L ^ 2)⁻¹ ≤ Cw := by
        have : (L ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
        nlinarith
      have hΛw : ∑ n ∈ Finset.range N₂, (ArithmeticFunction.vonMangoldt n : ℝ) *
          φ (Real.log n - L) / n ≤ Φm * MΛ := by
        have h := hΛloc L hLone N₂
        calc _ ≤ ∑ n ∈ Finset.range N₂, Φm * (|(ArithmeticFunction.vonMangoldt n : ℝ)| / n *
              (if |Real.log n - L| ≤ 1 / 2 then 1 else 0)) := by
              refine Finset.sum_le_sum fun n _ => ?_
              have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
              have hn := Nat.cast_nonneg (α := ℝ) n
              rw [abs_of_nonneg hΛ]
              split_ifs with h1
              · rw [mul_one, mul_div_right_comm, mul_comm Φm]
                exact mul_le_mul_of_nonneg_left (hφle _) (div_nonneg hΛ hn)
              · rw [hφs _ (not_le.mp h1)]; simp
          _ = Φm * ∑ n ∈ Finset.range N₂, |(ArithmeticFunction.vonMangoldt n : ℝ)| / n *
              (if |Real.log n - L| ≤ 1 / 2 then 1 else 0) := by rw [Finset.mul_sum]
          _ ≤ Φm * MΛ := mul_le_mul_of_nonneg_left h hΦm0
      have hgw : 0 ≤ ∑ n ∈ Finset.range N₂, g n * φ (Real.log n - L) / n :=
        Finset.sum_nonneg fun n _ =>
          div_nonneg (mul_nonneg (hg0 n) (hφ0 _)) (Nat.cast_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hgw, hsplit]
      linarith [(abs_le.mp hd).2]
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const hwinb
    rw [Real.norm_eq_abs, show |X' - X| = 4 by rw [hX, hX']; norm_num] at hint
    have hle := (le_abs_self _).trans hint
    have hfin : I * ∑ n ∈ Finset.range N₂, |g n| / n *
        (if |Real.log n - Z| ≤ 1 / 2 then 1 else 0) ≤ I * Mbig := by
      rw [hMbig, mul_div_assoc', mul_div_cancel_left₀ _ hI.ne']
      linarith
    exact hmono.trans (le_of_mul_le_mul_left hfin hI)
  -- local mass of `g` at small `Z`
  set N₀ : ℕ := ⌈Real.exp (L₁ + 3)⌉₊ with hN₀
  set H : ℝ := ∑ n ∈ Finset.range N₀, |g n| / n with hH
  have hH0 : 0 ≤ H := Finset.sum_nonneg fun n _ => div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
  have hsmall : ∀ Z : ℝ, Z ≤ L₁ + 2 → ∀ N₁ : ℕ,
      ∑ n ∈ Finset.range N₁, |g n| / n * (if |Real.log n - Z| ≤ 1 / 2 then 1 else 0) ≤ H := by
    intro Z hZ N₁
    calc _ ≤ ∑ n ∈ Finset.range N₀, |g n| / n * (if |Real.log n - Z| ≤ 1 / 2 then 1 else 0) := by
          rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N₁) (fun n => n < N₀)]
          have h2 : ∑ n ∈ (Finset.range N₁).filter (fun n => ¬ n < N₀),
              |g n| / n * (if |Real.log n - Z| ≤ 1 / 2 then 1 else 0) = 0 := by
            refine Finset.sum_eq_zero fun n hn => ?_
            have hnN : N₀ ≤ n := not_lt.mp (Finset.mem_filter.mp hn).2
            have hn0 : (0 : ℝ) < n := by
              have : 1 ≤ N₀ := Nat.one_le_iff_ne_zero.mpr (by
                rw [hN₀]; exact (Nat.ceil_pos.mpr (Real.exp_pos _)).ne')
              exact_mod_cast (show 0 < n by omega)
            have hlog : L₁ + 3 ≤ Real.log n := by
              rw [Real.le_log_iff_exp_le hn0]
              exact (Nat.le_ceil _).trans (by exact_mod_cast hnN)
            rw [if_neg (by rw [abs_le]; push Not; intro; linarith), mul_zero]
          rw [h2, add_zero]
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (fun n hn => Finset.mem_range.mpr (Finset.mem_filter.mp hn).2)
            fun n _ _ => localWindow_nonneg g Z n
      _ ≤ H := Finset.sum_le_sum fun n _ => by
          have h0 : 0 ≤ |g n| / n := div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
          split_ifs <;> simp [h0]
  have hgloc : LocalMassBounded g (max Mbig H) := fun Z _ N₁ => by
    rcases le_or_gt Z (L₁ + 2) with h | h
    · exact (hsmall Z h N₁).trans (le_max_right _ _)
    · exact (hbig Z h.le N₁).trans (le_max_left _ _)
  exact ⟨max Mbig H + MΛ, add_nonneg (hH0.trans (le_max_right _ _)) hMΛ0,
    LocalMassBounded.of_abs_le_add hgloc hΛloc hdg⟩

end RHTower.WeilAbscissa
