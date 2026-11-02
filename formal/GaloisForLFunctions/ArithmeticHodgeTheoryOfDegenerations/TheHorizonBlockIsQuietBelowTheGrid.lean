import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheHorizonLayerReadsWeilSummands
import GaloisForLFunctions.RHTower.Sieve.KuzminLandau

/-!
# The horizon block is quiet below the grid

The Dirichlet polynomial of a horizon block, `D_x(τ) = Σ_{Ne^{−A} ≤ n ≤ N} h(log(n/N)) n^{−1/2} n^{iτ}`,
has phase increments `(τ/2π) log(1 + 1/n) ≤ τ/(2π N e^{−A})`. Below the atom grid,
`|τ| ≤ N e^{−A}`, they stay in `[τ/(2πN), ½]`, so the Kuzmin–Landau inequality bounds every partial
sum of `n^{iτ}` by `4πN/|τ|`. The weights `h(log(n/N))/√n` vary by `O(N^{−3/2})` per step and vanish
at the horizon, so summation by parts gives

* **Decay** (`norm_horizonDirichlet_le_div`): `|D_x(τ)| ≤ C √N/|τ|` for `0 < |τ| ≤ N e^{−A}`;
* **Size** (`norm_horizonDirichlet_le`): `|D_x(τ)| ≤ C √N` for all `τ`;
* **Domination** (`horizonDirichlet_sq_div_le`): `|D_x(τ)|²/N ≤ C/(1 + τ²)` below the grid,
  uniformly in `N`.

Below the grid the horizon block is a smooth test seen at the density `log n`; the only large
values of its Dirichlet polynomial sit at the aliasing frequencies `|τ| ≳ N e^{−A}`.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis

/-- **Summation by parts.** If every partial sum of `e` has norm at most `B`, the weighted sum is
at most `B` times the last weight plus the total variation. -/
theorem norm_sum_mul_le_of_partial (a : ℕ → ℝ) (e : ℕ → ℂ) (M : ℕ) {B : ℝ}
    (hB : ∀ k ≤ M, ‖∑ m ∈ range (k + 1), e m‖ ≤ B) :
    ‖∑ m ∈ range (M + 1), (a m : ℂ) * e m‖ ≤ B * (|a M| + ∑ m ∈ range M, |a (m + 1) - a m|) := by
  have hBnn : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _))
  have h := Finset.sum_range_by_parts (fun m => (a m : ℂ)) e (M + 1)
  simp only [smul_eq_mul, Nat.add_sub_cancel] at h
  rw [h]
  refine (norm_sub_le _ _).trans ?_
  rw [mul_add]
  refine add_le_add ?_ ?_
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB M le_rfl) (abs_nonneg _)
  · rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (sum_le_sum fun m hm => ?_)
    rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB m (by simp at hm; omega)) (abs_nonneg _)

/-- `log(1 + 1/t) ≥ 1/(t + 1)`. -/
theorem one_div_add_one_le_log {t : ℝ} (ht : 0 < t) :
    1 / (t + 1) ≤ Real.log ((t + 1) / t) := by
  have h := Real.log_le_sub_one_of_pos (show 0 < t / (t + 1) by positivity)
  rw [Real.log_div ht.ne' (by linarith)] at h
  rw [Real.log_div (by linarith) ht.ne']
  have : t / (t + 1) - 1 = -(1 / (t + 1)) := by field_simp; ring
  linarith

/-- **Kuzmin–Landau for `n^{iτ}`.** For `0 < τ ≤ π n₀` and `n₀ + k ≤ N`, the partial sum
`Σ_{m≤k} (n₀ + m)^{iτ}` has norm at most `3πN/τ + 1`. -/
theorem norm_partial_cpow_le {n₀ N k : ℕ} (hn₀ : 1 ≤ n₀) (hk : n₀ + k ≤ N) {τ : ℝ} (hτ : 0 < τ)
    (hτn : τ ≤ Real.pi * n₀) :
    ‖∑ m ∈ range (k + 1), Complex.exp (((τ * Real.log (n₀ + m) : ℝ) : ℂ) * Complex.I)‖ ≤
      3 * Real.pi * N / τ + 1 := by
  have hN0 : (0 : ℝ) < N := by have : 1 ≤ N := by omega
                               exact_mod_cast this
  set φ : ℕ → ℝ := fun m => m - τ * Real.log (n₀ + m) / (2 * Real.pi) with hφ
  have hterm : ∀ m : ℕ, Complex.exp (((τ * Real.log (n₀ + m) : ℝ) : ℂ) * Complex.I) =
      (starRingEnd ℂ) (Complex.exp (((2 * Real.pi * φ m : ℝ) : ℂ) * Complex.I)) := by
    intro m
    have key : (((2 * Real.pi * φ m : ℝ) : ℂ) * Complex.I) = (m : ℂ) * (2 * Real.pi * Complex.I) +
        (-(((τ * Real.log (n₀ + m) : ℝ) : ℂ) * Complex.I)) := by
      simp only [hφ]; push_cast; field_simp; ring
    rw [key, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, one_mul, ← Complex.exp_conj]
    congr 1
    simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_neg]
  have hconj : ∑ m ∈ range (k + 1), Complex.exp (((τ * Real.log (n₀ + m) : ℝ) : ℂ) * Complex.I) =
      (starRingEnd ℂ) (∑ m ∈ range (k + 1),
        Complex.exp (((2 * Real.pi * φ m : ℝ) : ℂ) * Complex.I)) := by
    rw [map_sum]
    exact sum_congr rfl fun m _ => hterm m
  rw [hconj, RCLike.norm_conj]
  set δ := τ / (2 * Real.pi * N) with hδ
  have hδ0 : 0 < δ := by positivity
  have hdiff : ∀ m : ℕ, φ (m + 1) - φ m =
      1 - τ / (2 * Real.pi) * Real.log (((n₀ + m : ℝ) + 1) / (n₀ + m)) := by
    intro m
    have h1 : (0 : ℝ) < n₀ + m := by positivity
    simp only [hφ]
    push_cast
    rw [Real.log_div (by linarith) h1.ne', show ((n₀ : ℝ) + (m + 1)) = (n₀ + m) + 1 by ring]
    field_simp
    ring
  have hlog_le : ∀ m : ℕ, Real.log (((n₀ + m : ℝ) + 1) / (n₀ + m)) ≤ 1 / (n₀ + m) := by
    intro m
    have h1 : (0 : ℝ) < n₀ + m := by positivity
    have := Real.log_le_sub_one_of_pos (show 0 < ((n₀ + m : ℝ) + 1) / (n₀ + m) by positivity)
    rw [show ((n₀ + m : ℝ) + 1) / (n₀ + m) - 1 = 1 / (n₀ + m) by field_simp; ring] at this
    exact this
  have hn₀R : (1 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  refine (RHTower.Sieve.kuzminLandau_band φ k hδ0 (fun m hm => ?_) (fun m hm => ?_)
    (fun m hm => ?_)).trans ?_
  · -- lower band: increments are at least `½ ≥ δ`
    rw [hdiff]
    have h1 : (0 : ℝ) < n₀ + m := by positivity
    have hle := hlog_le m
    have : τ / (2 * Real.pi) * Real.log (((n₀ + m : ℝ) + 1) / (n₀ + m)) ≤ 1 / 2 := by
      calc τ / (2 * Real.pi) * Real.log (((n₀ + m : ℝ) + 1) / (n₀ + m))
          ≤ τ / (2 * Real.pi) * (1 / (n₀ + m)) :=
            mul_le_mul_of_nonneg_left hle (by positivity)
        _ ≤ τ / (2 * Real.pi) * (1 / n₀) := by
            gcongr
            · exact_mod_cast Nat.le_add_right n₀ m
        _ ≤ 1 / 2 := by
            rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith [Real.pi_pos]
    have hδle : δ ≤ 1 / 2 := by
      rw [hδ, div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (n₀ : ℝ) ≤ N := by exact_mod_cast (show n₀ ≤ N by omega)
      nlinarith [Real.pi_pos]
    linarith
  · -- upper band: increments are at most `1 − τ/(2πN)`
    rw [hdiff]
    have h1 : (0 : ℝ) < n₀ + m := by positivity
    have hge := one_div_add_one_le_log h1
    have hmN : (n₀ + m : ℝ) + 1 ≤ N := by
      have : n₀ + m + 1 ≤ N := by omega
      exact_mod_cast this
    have : δ ≤ τ / (2 * Real.pi) * Real.log (((n₀ + m : ℝ) + 1) / (n₀ + m)) := by
      calc δ = τ / (2 * Real.pi) * (1 / N) := by rw [hδ]; field_simp
        _ ≤ τ / (2 * Real.pi) * (1 / ((n₀ + m : ℝ) + 1)) := by
            gcongr
        _ ≤ _ := mul_le_mul_of_nonneg_left hge (by positivity)
    linarith
  · -- monotone increments
    rw [hdiff, hdiff]
    have h1 : (0 : ℝ) < n₀ + m := by positivity
    have h2 : Real.log (((n₀ + (m + 1 : ℕ) : ℝ) + 1) / (n₀ + (m + 1 : ℕ))) ≤
        Real.log (((n₀ + m : ℝ) + 1) / (n₀ + m)) := by
      push_cast
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff₀ (by positivity) h1]
      nlinarith
    have : 0 ≤ τ / (2 * Real.pi) := by positivity
    nlinarith
  · have : 3 / (2 * δ) = 3 * Real.pi * N / τ := by rw [hδ]; field_simp
    rw [this]

/-! ### The horizon block -/

section Horizon

variable {h : ℝ → ℝ} {A Bh L : ℝ}

/-- The first index of the window `[N e^{−A}, N]`. -/
def windowStart (A : ℝ) (N : ℕ) : ℕ := ⌈(N : ℝ) * Real.exp (-A)⌉₊

theorem one_le_windowStart {N : ℕ} (hN : 1 ≤ N) (A : ℝ) : 1 ≤ windowStart A N := by
  unfold windowStart
  rw [Nat.one_le_ceil_iff]
  have : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

theorem windowStart_le {N : ℕ} (hA : 0 ≤ A) : windowStart A N ≤ N := by
  unfold windowStart
  rw [Nat.ceil_le]
  have h1 : Real.exp (-A) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

theorem le_windowStart (A : ℝ) (N : ℕ) : (N : ℝ) * Real.exp (-A) ≤ windowStart A N :=
  Nat.le_ceil _

theorem horizon_zero_at_zero (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    (hL : ∀ u v, |h u - h v| ≤ L * |u - v|) : h 0 = 0 := by
  have hε : ∀ ε : ℝ, 0 < ε → |h 0| ≤ L * ε := fun ε hε => by
    have h1 := hL 0 ε
    rw [hsupp ε (fun hm => by linarith [hm.2]), sub_zero, zero_sub, abs_neg, abs_of_pos hε] at h1
    exact h1
  have : |h 0| ≤ 0 := by
    by_contra hc
    push Not at hc
    rcases le_or_gt L 0 with hL0 | hL0
    · have := hε 1 one_pos; nlinarith
    · have := hε (|h 0| / (2 * L)) (by positivity)
      rw [mul_div_assoc', mul_comm L, mul_div_mul_right _ _ hL0.ne'] at this
      linarith
  exact abs_nonpos_iff.mp this

theorem horizonWeights_eq_zero_of_lt (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {N n : ℕ}
    (hn : 1 ≤ n) (hnA : n < windowStart A N) : horizonWeights h N n = 0 := by
  unfold horizonWeights
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlt : (n : ℝ) < N * Real.exp (-A) := by
    by_contra hc
    push Not at hc
    exact absurd (Nat.ceil_le.mpr hc) (by unfold windowStart at hnA; omega)
  have hN0 : (0 : ℝ) < N := by
    by_contra hc; push Not at hc
    have : (N : ℝ) * Real.exp (-A) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (Real.exp_pos _).le
    linarith
  have hlog : Real.log n - Real.log N < -A := by
    rw [← Real.log_div hn0.ne' hN0.ne', Real.log_lt_iff_lt_exp (by positivity),
      div_lt_iff₀ hN0, mul_comm]
    exact hlt
  rw [hsupp _ (fun hm => by linarith [hm.1]), zero_div]

/-- The Dirichlet polynomial of a horizon block lives on its window. -/
theorem dirichletPoly_horizon_eq_range (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A)
    {N : ℕ} (hN : 1 ≤ N) (τ : ℝ) :
    dirichletPoly N (horizonWeights h N) τ =
      ∑ m ∈ range (N - windowStart A N + 1), (horizonWeights h N (windowStart A N + m) : ℂ) *
        Complex.exp (((τ * Real.log (windowStart A N + m) : ℝ) : ℂ) * Complex.I) := by
  set n₀ := windowStart A N with hn₀
  have h1 := one_le_windowStart hN A
  have h2 : n₀ ≤ N := windowStart_le hA
  unfold dirichletPoly
  have hsplit : Icc 1 N = Ico 1 n₀ ∪ Ico n₀ (N + 1) := by
    ext n; simp only [mem_Icc, mem_union, mem_Ico]; omega
  rw [hsplit, sum_union (disjoint_left.mpr fun n ha hb => by
    simp only [mem_Ico] at ha hb; omega)]
  rw [sum_eq_zero (fun n hn => by
    simp only [mem_Ico] at hn
    rw [horizonWeights_eq_zero_of_lt hsupp hn.1 hn.2, Complex.ofReal_zero, zero_mul]), zero_add,
    sum_Ico_eq_sum_range, show N + 1 - n₀ = N - n₀ + 1 by omega]
  refine sum_congr rfl fun m _ => ?_
  push_cast
  ring_nf

/-- The total variation of the window weights is `O(N^{−1/2})`. -/
theorem variation_horizonWeights_le (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A)
    (hB : ∀ y, |h y| ≤ Bh) (hL : ∀ u v, |h u - h v| ≤ L * |u - v|) {N : ℕ} (hN : 1 ≤ N) :
    |horizonWeights h N (windowStart A N + (N - windowStart A N))| +
      ∑ m ∈ range (N - windowStart A N), |horizonWeights h N (windowStart A N + (m + 1)) -
        horizonWeights h N (windowStart A N + m)| ≤
      (L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2)) / Real.sqrt N := by
  set n₀ := windowStart A N with hn₀
  have h1 := one_le_windowStart hN A
  have h2 : n₀ ≤ N := windowStart_le hA
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hn₀0 : (0 : ℝ) < n₀ := by exact_mod_cast h1
  have hL0 : 0 ≤ L := by
    have := hL 1 0
    norm_num at this
    linarith [abs_nonneg (h 1 - h 0)]
  have hB0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  -- the last weight vanishes
  have hlast : horizonWeights h N (n₀ + (N - n₀)) = 0 := by
    rw [show n₀ + (N - n₀) = N by omega, horizonWeights, sub_self,
      horizon_zero_at_zero hsupp hL, zero_div]
  rw [hlast, abs_zero, zero_add]
  -- each step: a Lipschitz part and a telescoping part
  have hstep : ∀ m : ℕ, |horizonWeights h N (n₀ + (m + 1)) - horizonWeights h N (n₀ + m)| ≤
      L / ((n₀ : ℝ) * Real.sqrt n₀) +
        Bh * ((Real.sqrt (n₀ + m))⁻¹ - (Real.sqrt (n₀ + m + 1))⁻¹) := by
    intro m
    have ht : (0 : ℝ) < n₀ + m := by positivity
    set t : ℝ := n₀ + m
    unfold horizonWeights
    push_cast
    rw [show (n₀ : ℝ) + (m + 1) = t + 1 by simp only [t]; ring, show (n₀ : ℝ) + m = t from rfl]
    have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    have hs1 : 0 < Real.sqrt (t + 1) := Real.sqrt_pos.mpr (by linarith)
    have hsle : Real.sqrt t ≤ Real.sqrt (t + 1) := Real.sqrt_le_sqrt (by linarith)
    set a := h (Real.log (t + 1) - Real.log N)
    set b := h (Real.log t - Real.log N)
    have hab : |a - b| ≤ L / t := by
      have := hL (Real.log (t + 1) - Real.log N) (Real.log t - Real.log N)
      rw [show Real.log (t + 1) - Real.log N - (Real.log t - Real.log N) =
        Real.log ((t + 1) / t) by rw [Real.log_div (by linarith) ht.ne']; ring] at this
      have hlog0 : 0 ≤ Real.log ((t + 1) / t) := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
      have hlog : Real.log ((t + 1) / t) ≤ 1 / t := by
        have := Real.log_le_sub_one_of_pos (show 0 < (t + 1) / t by positivity)
        rwa [show (t + 1) / t - 1 = 1 / t by field_simp; ring] at this
      rw [abs_of_nonneg hlog0] at this
      calc |a - b| ≤ L * Real.log ((t + 1) / t) := this
        _ ≤ L * (1 / t) := mul_le_mul_of_nonneg_left hlog hL0
        _ = L / t := by ring
    have hdecomp : a / Real.sqrt (t + 1) - b / Real.sqrt t =
        (a - b) / Real.sqrt (t + 1) + b * ((Real.sqrt (t + 1))⁻¹ - (Real.sqrt t)⁻¹) := by
      field_simp; ring
    rw [hdecomp]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_div, abs_of_pos hs1]
      have hn₀t : (n₀ : ℝ) ≤ t := by simp only [t]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      have hsn : Real.sqrt n₀ ≤ Real.sqrt (t + 1) := Real.sqrt_le_sqrt (by linarith)
      have hsn0 : 0 < Real.sqrt n₀ := Real.sqrt_pos.mpr hn₀0
      calc |a - b| / Real.sqrt (t + 1) ≤ (L / t) / Real.sqrt n₀ :=
            div_le_div₀ (by positivity) hab hsn0 hsn
        _ ≤ (L / n₀) / Real.sqrt n₀ := by
            gcongr
        _ = L / ((n₀ : ℝ) * Real.sqrt n₀) := by rw [div_div]
    · rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr (inv_anti₀ hs0 hsle)), neg_sub]
      exact mul_le_mul_of_nonneg_right (hB _) (sub_nonneg.mpr (inv_anti₀ hs0 hsle))
  refine (sum_le_sum fun m _ => hstep m).trans ?_
  rw [sum_add_distrib, sum_const, card_range, ← mul_sum]
  have htel : ∑ m ∈ range (N - n₀), ((Real.sqrt ((n₀ : ℝ) + m))⁻¹ -
      (Real.sqrt ((n₀ : ℝ) + m + 1))⁻¹) ≤ (Real.sqrt n₀)⁻¹ := by
    have := Finset.sum_range_sub' (fun m : ℕ => (Real.sqrt ((n₀ : ℝ) + m))⁻¹) (N - n₀)
    simp only [Nat.cast_add, Nat.cast_one, ← add_assoc, Nat.cast_zero, add_zero] at this
    rw [this]
    have : 0 ≤ (Real.sqrt ((n₀ : ℝ) + (N - n₀ : ℕ)))⁻¹ := by positivity
    linarith
  have hn₀ge : (N : ℝ) * Real.exp (-A) ≤ n₀ := le_windowStart A N
  have hsq : Real.sqrt N * Real.exp (-A / 2) ≤ Real.sqrt n₀ := by
    rw [show Real.exp (-A / 2) = Real.sqrt (Real.exp (-A)) by
      rw [← Real.exp_half], ← Real.sqrt_mul hN0.le]
    exact Real.sqrt_le_sqrt hn₀ge
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hsn0 : 0 < Real.sqrt n₀ := Real.sqrt_pos.mpr hn₀0
  have hexpA : Real.exp (A / 2) * Real.exp (-A / 2) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  -- first part: `(N − n₀) L/(n₀^{3/2}) ≤ L e^{3A/2}/√N`
  have hpart1 : ((N - n₀ : ℕ) : ℝ) * (L / ((n₀ : ℝ) * Real.sqrt n₀)) ≤
      L * Real.exp (3 / 2 * A) / Real.sqrt N := by
    have hcard : ((N - n₀ : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N n₀
    have hprod : (N : ℝ) * Real.exp (-A) * (Real.sqrt N * Real.exp (-A / 2)) ≤
        (n₀ : ℝ) * Real.sqrt n₀ := mul_le_mul hn₀ge hsq (by positivity) (by positivity)
    have hkey : (N : ℝ) * Real.exp (-A) * (Real.sqrt N * Real.exp (-A / 2)) =
        N * Real.sqrt N * Real.exp (-(3 / 2 * A)) := by
      rw [show -(3 / 2 * A) = -A + -A / 2 by ring, Real.exp_add]; ring
    rw [hkey] at hprod
    calc ((N - n₀ : ℕ) : ℝ) * (L / ((n₀ : ℝ) * Real.sqrt n₀))
        ≤ N * (L / (N * Real.sqrt N * Real.exp (-(3 / 2 * A)))) := by
          gcongr
    _ = L * Real.exp (3 / 2 * A) / Real.sqrt N := by
          rw [Real.exp_neg]
          field_simp
  -- second part: `Bh/√n₀ ≤ Bh e^{A/2}/√N`
  have hpart2 : Bh * (Real.sqrt n₀)⁻¹ ≤ Bh * Real.exp (A / 2) / Real.sqrt N := by
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hB0
    rw [inv_le_comm₀ hsn0 (by positivity), inv_div, div_eq_mul_inv, ← Real.exp_neg,
      show -(A / 2) = -A / 2 by ring]
    exact hsq
  rw [nsmul_eq_mul, add_div]
  have := mul_le_mul_of_nonneg_left htel hB0
  linarith [hpart1, hpart2]

/-- For real weights, `D_x(−τ) = conj D_x(τ)`. -/
theorem dirichletPoly_neg_real (N : ℕ) (x : ℕ → ℝ) (τ : ℝ) :
    dirichletPoly N x (((-τ : ℝ) : ℂ)) = (starRingEnd ℂ) (dirichletPoly N x τ) := by
  unfold dirichletPoly
  rw [map_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- The window constant `C_v = L e^{3A/2} + B e^{A/2}`. -/
def windowConst (A Bh L : ℝ) : ℝ := L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2)

theorem norm_horizonDirichlet_le_div_pos (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    (hA : 0 ≤ A) (hB : ∀ y, |h y| ≤ Bh) (hL : ∀ u v, |h u - h v| ≤ L * |u - v|) {N : ℕ}
    (hN : 1 ≤ N) {τ : ℝ} (hτ0 : 0 < τ) (hτN : τ ≤ N * Real.exp (-A)) :
    ‖dirichletPoly N (horizonWeights h N) τ‖ ≤
      4 * Real.pi * windowConst A Bh L * Real.sqrt N / τ := by
  set n₀ := windowStart A N with hn₀
  have h1 := one_le_windowStart hN A
  have h2 : n₀ ≤ N := windowStart_le hA
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hτn₀ : τ ≤ Real.pi * n₀ := by
    have := le_windowStart A N
    nlinarith [Real.pi_gt_three, (Nat.cast_nonneg n₀ : (0 : ℝ) ≤ n₀)]
  have hτN' : τ ≤ N := by
    have : Real.exp (-A) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith
  rw [dirichletPoly_horizon_eq_range hsupp hA hN]
  have hpart := norm_sum_mul_le_of_partial (fun m => horizonWeights h N (n₀ + m))
    (fun m => Complex.exp (((τ * Real.log (n₀ + m) : ℝ) : ℂ) * Complex.I)) (N - n₀)
    (B := 3 * Real.pi * N / τ + 1) fun k hk =>
      norm_partial_cpow_le h1 (by omega) hτ0 hτn₀
  have hvar := variation_horizonWeights_le hsupp hA hB hL hN
  have hBle : 3 * Real.pi * N / τ + 1 ≤ 4 * Real.pi * N / τ := by
    have : 1 ≤ Real.pi * N / τ := by
      rw [le_div_iff₀ hτ0, one_mul]; nlinarith [Real.pi_gt_three]
    have h3 : 3 * Real.pi * N / τ + Real.pi * N / τ = 4 * Real.pi * N / τ := by ring
    linarith
  have hBnn : 0 ≤ 3 * Real.pi * N / τ + 1 := by positivity
  have hvar0 : 0 ≤ |horizonWeights h N (n₀ + (N - n₀))| + ∑ m ∈ range (N - n₀),
      |horizonWeights h N (n₀ + (m + 1)) - horizonWeights h N (n₀ + m)| := by positivity
  refine hpart.trans ?_
  calc (3 * Real.pi * N / τ + 1) * (|horizonWeights h N (n₀ + (N - n₀))| +
        ∑ m ∈ range (N - n₀), |horizonWeights h N (n₀ + (m + 1)) - horizonWeights h N (n₀ + m)|)
      ≤ (4 * Real.pi * N / τ) * (windowConst A Bh L / Real.sqrt N) :=
        mul_le_mul hBle hvar hvar0 (by positivity)
    _ = 4 * Real.pi * windowConst A Bh L * Real.sqrt N / τ := by
        rw [show 4 * Real.pi * N / τ * (windowConst A Bh L / Real.sqrt N) =
          4 * Real.pi * windowConst A Bh L * ((N : ℝ) / Real.sqrt N) / τ by ring, Real.div_sqrt]

/-- **Decay below the grid**: `|D_x(τ)| ≤ 4π C_v √N/|τ|` for `0 < |τ| ≤ N e^{−A}`. -/
theorem norm_horizonDirichlet_le_div (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    (hA : 0 ≤ A) (hB : ∀ y, |h y| ≤ Bh) (hL : ∀ u v, |h u - h v| ≤ L * |u - v|) {N : ℕ}
    (hN : 1 ≤ N) {τ : ℝ} (hτ0 : 0 < |τ|) (hτN : |τ| ≤ N * Real.exp (-A)) :
    ‖dirichletPoly N (horizonWeights h N) τ‖ ≤
      4 * Real.pi * windowConst A Bh L * Real.sqrt N / |τ| := by
  rcases lt_or_gt_of_ne (abs_pos.mp hτ0) with hneg | hpos
  · have h' := norm_horizonDirichlet_le_div_pos hsupp hA hB hL hN (τ := -τ) (by linarith)
      (by rw [abs_of_neg hneg] at hτN; exact hτN)
    rw [show ((-τ : ℝ) : ℂ) = (((-τ : ℝ) : ℝ) : ℂ) from rfl, dirichletPoly_neg_real,
      RCLike.norm_conj] at h'
    rwa [abs_of_neg hneg]
  · rw [abs_of_pos hpos] at hτN ⊢
    exact norm_horizonDirichlet_le_div_pos hsupp hA hB hL hN hpos hτN

/-- **Size**: `|D_x(τ)| ≤ B e^{A/2} √N` for every real `τ`. -/
theorem norm_horizonDirichlet_le (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A)
    (hB : ∀ y, |h y| ≤ Bh) {N : ℕ} (hN : 1 ≤ N) (τ : ℝ) :
    ‖dirichletPoly N (horizonWeights h N) τ‖ ≤ Bh * Real.exp (A / 2) * Real.sqrt N := by
  set n₀ := windowStart A N with hn₀
  have h1 := one_le_windowStart hN A
  have h2 : n₀ ≤ N := windowStart_le hA
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hn₀0 : (0 : ℝ) < n₀ := by exact_mod_cast h1
  have hB0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  rw [dirichletPoly_horizon_eq_range hsupp hA hN]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ m ∈ range (N - n₀ + 1),
      ‖(horizonWeights h N (n₀ + m) : ℂ) *
        Complex.exp (((τ * Real.log (n₀ + m) : ℝ) : ℂ) * Complex.I)‖ ≤ Bh / Real.sqrt n₀ := by
    intro m _
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      horizonWeights, abs_div, abs_of_pos (Real.sqrt_pos.mpr (by positivity))]
    exact div_le_div₀ hB0 (hB _) (Real.sqrt_pos.mpr hn₀0)
      (Real.sqrt_le_sqrt (by push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]))
  refine (sum_le_sum hterm).trans ?_
  rw [sum_const, card_range, nsmul_eq_mul]
  have hcard : ((N - n₀ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast (show N - n₀ + 1 ≤ N by omega)
  have hsq : Real.sqrt N * Real.exp (-A / 2) ≤ Real.sqrt n₀ := by
    rw [show Real.exp (-A / 2) = Real.sqrt (Real.exp (-A)) by
      rw [← Real.exp_half], ← Real.sqrt_mul hN0.le]
    exact Real.sqrt_le_sqrt (le_windowStart A N)
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hdiv : Bh / Real.sqrt n₀ ≤ Bh * Real.exp (A / 2) / Real.sqrt N := by
    rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hn₀0) hsN]
    have : Real.sqrt N ≤ Real.exp (A / 2) * Real.sqrt n₀ := by
      calc Real.sqrt N = Real.sqrt N * Real.exp (-A / 2) * Real.exp (A / 2) := by
            rw [mul_assoc, ← Real.exp_add]; ring_nf; rw [Real.exp_zero, mul_one]
        _ ≤ Real.sqrt n₀ * Real.exp (A / 2) := by gcongr
        _ = _ := by ring
    nlinarith
  calc ((N - n₀ + 1 : ℕ) : ℝ) * (Bh / Real.sqrt n₀) ≤ N * (Bh * Real.exp (A / 2) / Real.sqrt N) :=
        mul_le_mul hcard hdiv (by positivity) (by positivity)
    _ = Bh * Real.exp (A / 2) * Real.sqrt N := by
        rw [show (N : ℝ) * (Bh * Real.exp (A / 2) / Real.sqrt N) =
          Bh * Real.exp (A / 2) * ((N : ℝ) / Real.sqrt N) by ring, Real.div_sqrt]

/-- **Domination below the grid**: `|D_x(τ)|²/N ≤ C/(1 + τ²)` for `|τ| ≤ N e^{−A}`, with
`C = 2(B²e^A + 16π² C_v²)`. -/
theorem horizonDirichlet_sq_div_le (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A)
    (hB : ∀ y, |h y| ≤ Bh) (hL : ∀ u v, |h u - h v| ≤ L * |u - v|) {N : ℕ} (hN : 1 ≤ N)
    {τ : ℝ} (hτN : |τ| ≤ N * Real.exp (-A)) :
    ‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N ≤
      2 * (Bh ^ 2 * Real.exp A + 16 * Real.pi ^ 2 * windowConst A Bh L ^ 2) / (1 + τ ^ 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0.le
  have hB0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  have hexp : Real.exp (A / 2) ^ 2 = Real.exp A := by rw [← Real.exp_nat_mul]; ring_nf
  have hpos : 0 < 1 + τ ^ 2 := by positivity
  rw [div_le_div_iff₀ hN0 hpos]
  rcases le_or_gt |τ| 1 with hτ1 | hτ1
  · have hD := norm_horizonDirichlet_le hsupp hA hB hN τ
    have hD2 : ‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 ≤ Bh ^ 2 * Real.exp A * N := by
      calc ‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2
          ≤ (Bh * Real.exp (A / 2) * Real.sqrt N) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hD 2
        _ = Bh ^ 2 * Real.exp A * N := by rw [mul_pow, mul_pow, hexp, hs]
    have hτ2 : τ ^ 2 ≤ 1 := by nlinarith [abs_nonneg τ, sq_abs τ]
    have hW : 0 ≤ 16 * Real.pi ^ 2 * windowConst A Bh L ^ 2 := by positivity
    nlinarith [sq_nonneg τ]
  · have hD := norm_horizonDirichlet_le_div hsupp hA hB hL hN (by linarith) hτN
    have hτ0 : 0 < |τ| := by linarith
    have hD2 : ‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 * τ ^ 2 ≤
        16 * Real.pi ^ 2 * windowConst A Bh L ^ 2 * N := by
      have h2 := pow_le_pow_left₀ (norm_nonneg _) hD 2
      rw [div_pow, mul_pow, mul_pow, mul_pow, hs, sq_abs] at h2
      have hτsq : 0 < τ ^ 2 := by nlinarith [sq_abs τ]
      rw [le_div_iff₀ hτsq] at h2
      nlinarith
    have hτ2 : 1 ≤ τ ^ 2 := by nlinarith [sq_abs τ]
    have hBe : 0 ≤ Bh ^ 2 * Real.exp A := by positivity
    nlinarith [sq_nonneg τ, norm_nonneg (dirichletPoly N (horizonWeights h N) τ)]

end Horizon

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
