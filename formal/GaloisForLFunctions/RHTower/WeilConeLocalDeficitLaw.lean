import GaloisForLFunctions.RHTower.WeilConeSingularDeficitCounting

/-!
# The local deficit law of the Weil cone

Let `lam` be full-cone Weil-positive.  The singular deficit law bounds `lam − Λ` by the deficit
count over `(0, T]`.  This file shows that one long window anywhere on the line suffices.

**Theorem** (`abs_sub_vonMangoldt_mul_rpow_le_of_localDeficit`).  Fix `σ > 1` and `E ≥ 0`.
Suppose that for every `η > 0` and `L₀` there are `T` and `L ≥ L₀` with `T − L ≥ 8`,
`log(T + 2L) ≤ ηL`, and at most `(E + η)·2L` deficit weight (`D(T − 2L, T + 2L]`) on ordinates
in `(T − 2L, T + 2L]`.  Then `|lam(m) − Λ(m)| m^{−σ} ≤ 4πE` for every `m ≥ 2`.

**Corollaries.**
* `eq_vonMangoldt_of_localDeficit`: if windows of length `L` with `log T = o(L)` carry `o(L)`
  deficit weight, then `lam = Λ` on `n ≥ 2`, and RH holds (`riemannHypothesis_of_localDeficit`).
* `eq_vonMangoldt_of_deficitFree_windows`: deficit-free windows of length `L` with `log T = o(L)`
  force `lam = Λ`.

So a producer other than `Λ` has deficits of positive density in every window of length
`≥ C log T`, uniformly in the height: its deficit set cannot switch off on long stretches.

**Proof.**
* Bohr coefficients can be read off one long window (`abs_le_four_mul_of_logCosSeries_window`):
  for `f(t) = Σ a_n cos(t log n)` with `Σ|a_n| < ∞`, the window integral of `f(t)cos(t log m)` over
  `[s, s + L]` is `(a_m/2)L` up to `L·κ_m(L)`, with `κ_m(L) → 0` independently of `s` (each
  oscillating term has window integral at most `min(L, 2/|δ|)`; Tannery).  If `f ≥ −ε` on the
  window, then `|a_m| ≤ 4·mean(ε) + o(1)` as in the Cesàro envelope bound.
* For `t` within `L` of `T`, deficit copies outside `(T − 2L, T + 2L]` are at distance `≥ L`, so
  they contribute at most `(2σ/(L − 1)) Re ξ'/ξ(L + it) = O(σ log(T + 2L)/L)`; the copies inside
  contribute at most `πD(T − 2L, T + 2L]` to the window integral.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate NNReal ENNReal
open Zeta23

noncomputable section

namespace RHTower

/-! ## Bohr coefficients from one long window -/

/-- `min(1, 2/(L|δ|))`: the decay of the window mean of `cos(δt)` over a window of length `L`. -/
def windowDecay (L δ : ℝ) : ℝ := min 1 (2 / (L * |δ|))

theorem windowDecay_nonneg {L : ℝ} (hL : 0 ≤ L) (δ : ℝ) : 0 ≤ windowDecay L δ :=
  le_min zero_le_one (div_nonneg zero_le_two (mul_nonneg hL (abs_nonneg δ)))

theorem windowDecay_le_one (L δ : ℝ) : windowDecay L δ ≤ 1 := min_le_left _ _

theorem tendsto_windowDecay {δ : ℝ} (hδ : δ ≠ 0) :
    Tendsto (fun L => windowDecay L δ) atTop (𝓝 0) := by
  have h : Tendsto (fun L : ℝ => 2 / (L * |δ|)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_id.atTop_mul_const (abs_pos.mpr hδ))
  have := (tendsto_const_nhds (x := (1 : ℝ))).min h
  rwa [min_eq_right zero_le_one] at this

/-- `|∫_s^{s+L} cos(δt) dt| ≤ L · min(1, 2/(L|δ|))` for `δ ≠ 0`. -/
theorem abs_integral_cos_window_le {δ L : ℝ} (hδ : δ ≠ 0) (hL : 0 < L) (s : ℝ) :
    |∫ t in s..s + L, Real.cos (δ * t)| ≤ L * windowDecay L δ := by
  have h1 : |∫ t in s..s + L, Real.cos (δ * t)| ≤ L := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := s + L)
      (f := fun t => Real.cos (δ * t)) (C := 1)
      (fun t _ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
    rw [Real.norm_eq_abs, show s + L - s = L by ring, abs_of_pos hL, one_mul] at h
    exact h
  have h2 : |∫ t in s..s + L, Real.cos (δ * t)| ≤ 2 / |δ| := by
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hδ, integral_cos,
      smul_eq_mul, abs_mul, abs_inv]
    have hs : |Real.sin (δ * (s + L)) - Real.sin (δ * s)| ≤ 2 := by
      have := abs_sub (Real.sin (δ * (s + L))) (Real.sin (δ * s))
      linarith [Real.abs_sin_le_one (δ * (s + L)), Real.abs_sin_le_one (δ * s)]
    calc |δ|⁻¹ * |Real.sin (δ * (s + L)) - Real.sin (δ * s)| ≤ |δ|⁻¹ * 2 :=
          mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (abs_nonneg δ))
      _ = 2 / |δ| := by ring
  have hδ0 : 0 < |δ| := abs_pos.mpr hδ
  rw [windowDecay, mul_min_of_nonneg _ _ hL.le, mul_one]
  refine le_min h1 ?_
  rwa [show L * (2 / (L * |δ|)) = 2 / |δ| by field_simp]

theorem hasSum_integral_window_logCosSeriesProdTerm {a : ℕ → ℝ} (ha : Summable fun n => |a n|)
    (m : ℕ) (s L : ℝ) :
    HasSum (fun n => ∫ t in s..s + L, logCosSeriesProdTerm a m n t)
      (∫ t in s..s + L, logCosSeries a t * Real.cos (t * Real.log m)) := by
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun n _ => |a n|)
    (fun n => (by unfold logCosSeriesProdTerm; fun_prop : Continuous _).aestronglyMeasurable)
    (fun n => Eventually.of_forall fun t _ => by
      rw [Real.norm_eq_abs]; exact abs_logCosSeriesProdTerm_le a m n t)
    (Eventually.of_forall fun t _ => ha)
    (by simp) ?_
  refine Eventually.of_forall fun t _ => ?_
  rw [logCosSeries_mul_cos_eq]
  refine (Summable.of_norm_bounded ha fun n => ?_).hasSum
  rw [Real.norm_eq_abs]; exact abs_logCosSeriesProdTerm_le a m n t

theorem integral_window_logCosSeriesProdTerm (a : ℕ → ℝ) (m n : ℕ) (s L : ℝ) :
    ∫ t in s..s + L, logCosSeriesProdTerm a m n t =
      a n / 2 * ((∫ t in s..s + L, Real.cos ((Real.log n + Real.log m) * t)) +
        ∫ t in s..s + L, Real.cos ((Real.log n - Real.log m) * t)) := by
  unfold logCosSeriesProdTerm
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add]
  · exact (by fun_prop : Continuous _).intervalIntegrable _ _
  · exact (by fun_prop : Continuous _).intervalIntegrable _ _

/-- The window error `Σ_n (|a_n|/2)(κ_L(log n + log m) + [n ≠ m] κ_L(log n − log m))`. -/
def bohrWindowError (a : ℕ → ℝ) (m : ℕ) (L : ℝ) : ℝ :=
  ∑' n, |a n| / 2 * (windowDecay L (Real.log n + Real.log m) +
    if n = m then 0 else windowDecay L (Real.log n - Real.log m))

theorem log_add_log_nat_ne_zero {n m : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m) :
    Real.log n + Real.log m ≠ 0 := by
  have h1 : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have h2 : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  linarith

theorem log_sub_log_nat_ne_zero {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≠ m) :
    Real.log n - Real.log m ≠ 0 := by
  intro h
  have heq : Real.log (n : ℝ) = Real.log m := by linarith
  have := Real.log_injOn_pos (Set.mem_Ioi.mpr (by exact_mod_cast hn))
    (Set.mem_Ioi.mpr (by exact_mod_cast hm)) heq
  exact hnm (by exact_mod_cast this)

theorem bohrWindowTerm_le {a : ℕ → ℝ} (m n : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    ‖|a n| / 2 * (windowDecay L (Real.log n + Real.log m) +
      if n = m then 0 else windowDecay L (Real.log n - Real.log m))‖ ≤ |a n| := by
  have h1 := windowDecay_nonneg hL (Real.log n + Real.log m)
  have h2 := windowDecay_le_one L (Real.log n + Real.log m)
  have h3 : 0 ≤ (if n = m then 0 else windowDecay L (Real.log n - Real.log m)) := by
    split_ifs
    · exact le_rfl
    · exact windowDecay_nonneg hL _
  have h4 : (if n = m then 0 else windowDecay L (Real.log n - Real.log m)) ≤ 1 := by
    split_ifs
    · exact zero_le_one
    · exact windowDecay_le_one L _
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (by linarith))]
  nlinarith [abs_nonneg (a n)]

theorem tendsto_bohrWindowError {a : ℕ → ℝ} (ha : Summable fun n => |a n|) (ha0 : a 0 = 0)
    (ha1 : a 1 = 0) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (bohrWindowError a m) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (bound := fun n => |a n|) ha
    (f := fun L n => |a n| / 2 * (windowDecay L (Real.log n + Real.log m) +
      if n = m then 0 else windowDecay L (Real.log n - Real.log m))) (g := fun _ => (0 : ℝ))
    (fun n => ?_) ((eventually_ge_atTop 0).mono fun L hL n => bohrWindowTerm_le m n hL)
  · rw [tsum_zero] at h
    exact h
  rcases (show n ≤ 1 ∨ 2 ≤ n by omega) with hn | hn
  · have : a n = 0 := by
      interval_cases n
      · exact ha0
      · exact ha1
    simp [this]
  · have h1 := tendsto_windowDecay (log_add_log_nat_ne_zero hn hm)
    by_cases hnm : n = m
    · simp only [hnm, if_true, add_zero]
      have := h1.const_mul (|a n| / 2)
      rw [mul_zero] at this
      rwa [hnm] at this
    · simp only [hnm, if_false]
      have h2 := tendsto_windowDecay (log_sub_log_nat_ne_zero (by omega) hm hnm)
      have := (h1.add h2).const_mul (|a n| / 2)
      rwa [add_zero, mul_zero] at this

/-- **One window gives every Bohr coefficient.**  For `m ≥ 1`,
`|∫_s^{s+L} f(t) cos(t log m) dt − [m ≥ 2](a_m/2)L| ≤ L κ_m(L)`. -/
theorem abs_window_logCosSeries_mul_cos_sub_le {a : ℕ → ℝ} (ha : Summable fun n => |a n|)
    (ha0 : a 0 = 0) (ha1 : a 1 = 0) {m : ℕ} (hm : 1 ≤ m) {L : ℝ} (hL : 0 < L) (s : ℝ) :
    |(∫ t in s..s + L, logCosSeries a t * Real.cos (t * Real.log m)) -
      (if 2 ≤ m then a m / 2 else 0) * L| ≤ L * bohrWindowError a m L := by
  classical
  set c : ℕ → ℝ := fun n => if n = m then (if 2 ≤ m then a m / 2 else 0) * L else 0 with hcdef
  have hc : HasSum c ((if 2 ≤ m then a m / 2 else 0) * L) := hasSum_ite_eq m _
  have hS := (hasSum_integral_window_logCosSeriesProdTerm ha m s L).sub hc
  set B : ℕ → ℝ := fun n => L * (|a n| / 2 * (windowDecay L (Real.log n + Real.log m) +
    if n = m then 0 else windowDecay L (Real.log n - Real.log m))) with hBdef
  have hBs : Summable B := by
    refine (ha.mul_left L).of_nonneg_of_le (fun n => ?_) fun n => ?_
    · have := bohrWindowTerm_le (a := a) m n hL.le
      exact mul_nonneg hL.le ((norm_nonneg _).trans_eq (Real.norm_of_nonneg
        (by
          have h1 := windowDecay_nonneg hL.le (Real.log n + Real.log m)
          have h3 : 0 ≤ (if n = m then 0 else windowDecay L (Real.log n - Real.log m)) := by
            split_ifs
            · exact le_rfl
            · exact windowDecay_nonneg hL.le _
          positivity)))
    · have := bohrWindowTerm_le (a := a) m n hL.le
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans this) hL.le
  have hb : ∀ n, |(∫ t in s..s + L, logCosSeriesProdTerm a m n t) - c n| ≤ B n := by
    intro n
    rw [integral_window_logCosSeriesProdTerm]
    rcases (show n ≤ 1 ∨ 2 ≤ n by omega) with hn | hn
    · have han : a n = 0 := by
        interval_cases n
        · exact ha0
        · exact ha1
      have hcn : c n = 0 := by
        simp only [hcdef]
        split_ifs with h1 h2
        · omega
        · exact zero_mul L
        · rfl
      rw [han, hcn]
      simp [hBdef, han]
    · have hp := log_add_log_nat_ne_zero hn hm
      have hJ1 := abs_integral_cos_window_le hp hL s
      by_cases hnm : n = m
      · subst hnm
        have hcn : c n = a n / 2 * L := by simp [hcdef, hn]
        have hz : Real.log (n : ℝ) - Real.log n = 0 := sub_self _
        rw [hcn, hz]
        simp only [zero_mul, Real.cos_zero, intervalIntegral.integral_const, smul_eq_mul,
          mul_one, show s + L - s = L by ring]
        have e : a n / 2 * ((∫ t in s..s + L, Real.cos ((Real.log n + Real.log n) * t)) + L) -
            a n / 2 * L = a n / 2 * ∫ t in s..s + L, Real.cos ((Real.log n + Real.log n) * t) := by
          ring
        rw [e, abs_mul, abs_div, abs_two]
        simp only [hBdef, if_true, add_zero]
        calc |a n| / 2 * |∫ t in s..s + L, Real.cos ((Real.log n + Real.log n) * t)|
            ≤ |a n| / 2 * (L * windowDecay L (Real.log n + Real.log n)) :=
              mul_le_mul_of_nonneg_left hJ1 (by positivity)
          _ = _ := by ring
      · have hcn : c n = 0 := by simp [hcdef, hnm]
        have hJ2 := abs_integral_cos_window_le (log_sub_log_nat_ne_zero (by omega) hm hnm) hL s
        rw [hcn, sub_zero, abs_mul, abs_div, abs_two]
        simp only [hBdef, hnm, if_false]
        calc |a n| / 2 * |(∫ t in s..s + L, Real.cos ((Real.log n + Real.log m) * t)) +
              ∫ t in s..s + L, Real.cos ((Real.log n - Real.log m) * t)|
            ≤ |a n| / 2 * (L * windowDecay L (Real.log n + Real.log m) +
                L * windowDecay L (Real.log n - Real.log m)) :=
              mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hJ1 hJ2))
                (by positivity)
          _ = _ := by ring
  have hsabs : Summable fun n => ‖(∫ t in s..s + L, logCosSeriesProdTerm a m n t) - c n‖ :=
    hBs.of_nonneg_of_le (fun n => norm_nonneg _) fun n => by rw [Real.norm_eq_abs]; exact hb n
  calc |(∫ t in s..s + L, logCosSeries a t * Real.cos (t * Real.log m)) -
        (if 2 ≤ m then a m / 2 else 0) * L|
      = ‖∑' n, ((∫ t in s..s + L, logCosSeriesProdTerm a m n t) - c n)‖ := by
        rw [hS.tsum_eq, Real.norm_eq_abs]
    _ ≤ ∑' n, ‖(∫ t in s..s + L, logCosSeriesProdTerm a m n t) - c n‖ :=
        norm_tsum_le_tsum_norm hsabs
    _ ≤ ∑' n, B n := hsabs.tsum_le_tsum (fun n => by rw [Real.norm_eq_abs]; exact hb n) hBs
    _ = L * bohrWindowError a m L := by rw [hBdef, tsum_mul_left, bohrWindowError]

/-- **Bohr envelope bound on long windows.**  Let `f(t) = Σ a_n cos(t log n)` with
`Σ|a_n| < ∞` and `a_0 = a_1 = 0`, and `ε ≥ 0` continuous.  If for every `η > 0` there are windows
`[s, s + L]` of arbitrarily large length on which `f ≥ −ε` and `∫ ε ≤ (E + η)L`, then
`|a_m| ≤ 4E` for every `m ≥ 2`. -/
theorem abs_le_four_mul_of_logCosSeries_window {a : ℕ → ℝ} (ha : Summable fun n => |a n|)
    (ha0 : a 0 = 0) (ha1 : a 1 = 0) {ε : ℝ → ℝ} (hε0 : ∀ t, 0 ≤ ε t) (hεc : Continuous ε)
    {E : ℝ}
    (hwin : ∀ η > 0, ∀ L₀ : ℝ, ∃ s L : ℝ, L₀ ≤ L ∧ 0 < L ∧ (∫ t in s..s + L, ε t) ≤ (E + η) * L ∧
      ∀ t ∈ Icc s (s + L), -ε t ≤ logCosSeries a t) {m : ℕ} (hm : 2 ≤ m) : |a m| ≤ 4 * E := by
  refine le_of_forall_pos_lt_add fun η hη => ?_
  have hm1 := tendsto_bohrWindowError ha ha0 ha1 (m := m) (by omega)
  have h11 := tendsto_bohrWindowError ha ha0 ha1 (m := 1) le_rfl
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp
    ((hm1.add h11).eventually (gt_mem_nhds (show (0 : ℝ) + 0 < η / 4 by linarith)))
  obtain ⟨s, L, hLL, hL0, hint, hf⟩ := hwin (η / 8) (by positivity) L₁
  have hErr := hL₁ L hLL
  have hA := abs_window_logCosSeries_mul_cos_sub_le ha ha0 ha1 (m := m) (by omega) hL0 s
  have hB := abs_window_logCosSeries_mul_cos_sub_le ha ha0 ha1 (m := 1) le_rfl hL0 s
  simp only [Nat.cast_one, Real.log_one, mul_zero, Real.cos_zero, mul_one,
    show ¬ (2 ≤ 1) by omega, if_false, zero_mul, sub_zero] at hB
  rw [if_pos hm] at hA
  have hcont := continuous_logCosSeries ha
  have hsL : s ≤ s + L := by linarith
  have hint1 : IntervalIntegrable (fun t => logCosSeries a t * Real.cos (t * Real.log m))
      volume s (s + L) := (hcont.mul (by fun_prop)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (logCosSeries a) volume s (s + L) := hcont.intervalIntegrable _ _
  have hint3 : IntervalIntegrable ε volume s (s + L) := hεc.intervalIntegrable _ _
  have hpt : ∀ t ∈ Icc s (s + L),
      |logCosSeries a t * Real.cos (t * Real.log m)| ≤ logCosSeries a t + 2 * ε t := by
    intro t ht
    have h1 := hf t ht
    have h2 := hε0 t
    rw [abs_mul]
    have h3 := Real.abs_cos_le_one (t * Real.log m)
    have h4 : |logCosSeries a t| ≤ logCosSeries a t + 2 * ε t := by
      rcases le_or_gt 0 (logCosSeries a t) with h | h
      · rw [abs_of_nonneg h]; linarith
      · rw [abs_of_neg h]; linarith
    calc |logCosSeries a t| * |Real.cos (t * Real.log m)| ≤ |logCosSeries a t| * 1 :=
          mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
      _ ≤ _ := by linarith
  have hI : |∫ t in s..s + L, logCosSeries a t * Real.cos (t * Real.log m)| ≤
      (∫ t in s..s + L, logCosSeries a t) + 2 * ∫ t in s..s + L, ε t := by
    calc |∫ t in s..s + L, logCosSeries a t * Real.cos (t * Real.log m)|
        ≤ ∫ t in s..s + L, |logCosSeries a t * Real.cos (t * Real.log m)| :=
          intervalIntegral.abs_integral_le_integral_abs hsL
      _ ≤ ∫ t in s..s + L, (logCosSeries a t + 2 * ε t) :=
          intervalIntegral.integral_mono_on hsL hint1.abs (hint2.add (hint3.const_mul 2)) hpt
      _ = (∫ t in s..s + L, logCosSeries a t) + 2 * ∫ t in s..s + L, ε t := by
          rw [intervalIntegral.integral_add hint2 (hint3.const_mul 2),
            intervalIntegral.integral_const_mul]
  have hF : (∫ t in s..s + L, logCosSeries a t) ≤ L * bohrWindowError a 1 L :=
    (le_abs_self _).trans hB
  have hmain : |a m| / 2 * L ≤
      L * bohrWindowError a m L + L * bohrWindowError a 1 L + 2 * ((E + η / 8) * L) := by
    have h1 : |a m / 2 * L| ≤ |∫ t in s..s + L, logCosSeries a t * Real.cos (t * Real.log m)| +
        L * bohrWindowError a m L := by
      have := abs_sub_abs_le_abs_sub (a m / 2 * L)
        (∫ t in s..s + L, logCosSeries a t * Real.cos (t * Real.log m))
      rw [abs_sub_comm] at this
      linarith
    rw [abs_mul, abs_div, abs_two, abs_of_pos hL0] at h1
    linarith
  have hdiv : |a m| / 2 ≤ bohrWindowError a m L + bohrWindowError a 1 L + 2 * (E + η / 8) := by
    have h := hmain
    rw [show L * bohrWindowError a m L + L * bohrWindowError a 1 L + 2 * ((E + η / 8) * L) =
      (bohrWindowError a m L + bohrWindowError a 1 L + 2 * (E + η / 8)) * L by ring] at h
    exact le_of_mul_le_mul_right h hL0
  linarith

end RHTower

namespace RHTower.WeilSpectral

open WeilHerglotz

/-! ## Deficits in a window -/

/-- The deficit weight of a copy with ordinate in `(a, b]`, and `0` otherwise. -/
def windowDeficitWeight {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (a b : ℝ) (q : XiZeroCopy) : ℝ :=
  if a < ((q.1 : ℂ)).im ∧ ((q.1 : ℂ)).im ≤ b then deficitWeight hW q else 0

/-- **The window deficit count** `D(a, b] = Σ_{a < γ_q ≤ b} d_q`. -/
def windowDeficitCount {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (a b : ℝ) : ℝ :=
  ∑' q, windowDeficitWeight hW a b q

theorem windowDeficitWeight_nonneg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (a b : ℝ)
    (q : XiZeroCopy) : 0 ≤ windowDeficitWeight hW a b q := by
  unfold windowDeficitWeight
  split_ifs
  · exact deficitWeight_nonneg hW q
  · exact le_rfl

theorem windowDeficitWeight_le_one {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (a b : ℝ)
    (q : XiZeroCopy) : windowDeficitWeight hW a b q ≤ 1 := by
  unfold windowDeficitWeight
  split_ifs
  · exact deficitWeight_le_one hW q
  · exact zero_le_one

/-- **Splitting off a window.**  For `a + H ≤ t ≤ b − H`,
`ε_σ(t) ≤ Σ_q d_q 1_{(a,b]}(γ_q) A_q^σ(t) + (2σ/(H − 1)) Σ_q A_q^H(t)`. -/
theorem deficitEnvelope_le_localWindow {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {σ H a b t : ℝ}
    (hσ : 1 < σ) (hH : 1 < H) (htH : a + H ≤ t) (htb : t ≤ b - H) :
    deficitEnvelope hW σ t ≤ ∑' q, windowDeficitWeight hW a b q * copyPoisson σ t q +
      2 * σ / (H - 1) * ∑' q, copyPoisson H t q := by
  have hk : 0 ≤ 2 * σ / (H - 1) := div_nonneg (by linarith) (by linarith)
  have hs1 := summable_deficit_mul_copyPoisson hσ t (windowDeficitWeight_nonneg hW a b)
    (windowDeficitWeight_le_one hW a b)
  have hs2 := (summable_copyPoisson hH t).mul_left (2 * σ / (H - 1))
  rw [← tsum_mul_left, ← hs1.tsum_add hs2]
  refine (summable_deficit_mul_copyPoisson hσ t (deficitWeight_nonneg hW)
    (deficitWeight_le_one hW)).tsum_le_tsum (fun q => ?_) (hs1.add hs2)
  have hA := (copyPoisson_pos hσ.le t q).le
  have hAH := (copyPoisson_pos hH.le t q).le
  by_cases hw : a < ((q.1 : ℂ)).im ∧ ((q.1 : ℂ)).im ≤ b
  · rw [windowDeficitWeight, if_pos hw]
    have := mul_nonneg hk hAH
    linarith
  · rw [windowDeficitWeight, if_neg hw, zero_mul, zero_add]
    have hfar : H ≤ |t - ((q.1 : ℂ)).im| := by
      rcases not_and_or.mp hw with h | h
      · push Not at h
        rw [abs_of_nonneg (by linarith)]
        linarith
      · push Not at h
        rw [abs_of_neg (by linarith)]
        linarith
    calc deficitWeight hW q * copyPoisson σ t q ≤ 1 * copyPoisson σ t q :=
          mul_le_mul_of_nonneg_right (deficitWeight_le_one hW q) hA
      _ ≤ _ := by rw [one_mul]; exact copyPoisson_le_shift hσ.le hH q hfar

/-- The window part has total mass at most `πD(a, b]` on every interval. -/
theorem integral_localWindow_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {σ : ℝ} (hσ : 1 < σ)
    (a b c d : ℝ) :
    ∫ t in c..d, ∑' q, windowDeficitWeight hW a b q * copyPoisson σ t q ≤
      π * windowDeficitCount hW a b := by
  have hfin := finite_xiZeroCopy_band ((a + b) / 2) (div_nonneg (abs_nonneg (b - a)) zero_le_two)
  set S := hfin.toFinset
  have hzero : ∀ q ∉ S, windowDeficitWeight hW a b q = 0 := by
    intro q hq
    rw [windowDeficitWeight, if_neg]
    intro h
    apply hq
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, abs_le]
    have := le_abs_self (b - a)
    constructor <;> linarith [h.1, h.2]
  have hsum : ∀ t, ∑' q, windowDeficitWeight hW a b q * copyPoisson σ t q =
      ∑ q ∈ S, windowDeficitWeight hW a b q * copyPoisson σ t q :=
    fun t => tsum_eq_sum fun q hq => by rw [hzero q hq, zero_mul]
  have hD : windowDeficitCount hW a b = ∑ q ∈ S, windowDeficitWeight hW a b q :=
    tsum_eq_sum fun q hq => hzero q hq
  simp_rw [hsum]
  rw [intervalIntegral.integral_finsetSum
    (f := fun q t => windowDeficitWeight hW a b q * copyPoisson σ t q)
    fun q _ => ((continuous_copyPoisson hσ.le q).const_mul _).intervalIntegrable _ _,
    hD, Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ => ?_
  rw [intervalIntegral.integral_const_mul, mul_comm π]
  exact mul_le_mul_of_nonneg_left (integral_copyPoisson_le_pi hσ.le q c d)
    (windowDeficitWeight_nonneg hW a b q)

/-- **The window counting bound.**  For `L > 1`, `σ ≤ L` and `T − L ≥ 8`,
`∫_{T−L}^{T+L} ε_σ ≤ πD(T − 2L, T + 2L] + 2L (2σ/(L − 1)) (½ log(T + 2L) + C_σ)`. -/
theorem integral_deficitEnvelope_localWindow_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {σ T L : ℝ} (hσ : 1 < σ) (hL : 1 < L) (hσL : σ ≤ L) (h8 : 8 ≤ T - L) :
    ∫ t in (T - L)..(T + L), deficitEnvelope hW σ t ≤
      π * windowDeficitCount hW (T - 2 * L) (T + 2 * L) +
        2 * L * (2 * σ / (L - 1) * (Real.log (T + 2 * L) / 2 + envelopeConst σ)) := by
  set B := Real.log (T + 2 * L) / 2 + envelopeConst σ with hB
  have hk : 0 ≤ 2 * σ / (L - 1) := div_nonneg (by linarith) (by linarith)
  have hcε := continuous_deficitEnvelope hW hσ
  have hW1 : Continuous fun t => ∑' q, windowDeficitWeight hW (T - 2 * L) (T + 2 * L) q *
      copyPoisson σ t q :=
    continuous_weighted_copyPoisson hσ (windowDeficitWeight_nonneg hW _ _)
      (windowDeficitWeight_le_one hW _ _)
  have hP1 : Continuous fun t => ∑' q, copyPoisson L t q :=
    continuous_tsum_copyPoisson (by linarith)
  have hle : T - L ≤ T + L := by linarith
  have hPL : ∀ t ∈ Icc (T - L) (T + L), ∑' q, copyPoisson L t q ≤ B := fun t ht => by
    rw [← re_logDeriv_xi_eq_tsum_copyPoisson (by linarith) t]
    exact re_logDeriv_xi_le_log hσ hσL (by linarith) (by linarith [ht.1]) (by linarith [ht.2])
  have hmidP : ∫ t in (T - L)..(T + L), ∑' q, copyPoisson L t q ≤ 2 * L * B := by
    calc _ ≤ ∫ _ in (T - L)..(T + L), B :=
          intervalIntegral.integral_mono_on hle (hP1.intervalIntegrable _ _)
            intervalIntegrable_const hPL
      _ = 2 * L * B := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  calc ∫ t in (T - L)..(T + L), deficitEnvelope hW σ t
      ≤ ∫ t in (T - L)..(T + L), (∑' q, windowDeficitWeight hW (T - 2 * L) (T + 2 * L) q *
          copyPoisson σ t q + 2 * σ / (L - 1) * ∑' q, copyPoisson L t q) :=
        intervalIntegral.integral_mono_on hle (hcε.intervalIntegrable _ _)
          ((hW1.add (hP1.const_mul _)).intervalIntegrable _ _)
          fun t ht => deficitEnvelope_le_localWindow hW hσ hL (by linarith [ht.1])
            (by linarith [ht.2])
    _ = (∫ t in (T - L)..(T + L), ∑' q, windowDeficitWeight hW (T - 2 * L) (T + 2 * L) q *
          copyPoisson σ t q) + 2 * σ / (L - 1) * ∫ t in (T - L)..(T + L), ∑' q,
            copyPoisson L t q := by
        rw [intervalIntegral.integral_add (hW1.intervalIntegrable _ _)
          ((hP1.const_mul _).intervalIntegrable _ _), intervalIntegral.integral_const_mul]
    _ ≤ π * windowDeficitCount hW (T - 2 * L) (T + 2 * L) + 2 * σ / (L - 1) * (2 * L * B) :=
        add_le_add (integral_localWindow_le hW hσ _ _ _ _) (mul_le_mul_of_nonneg_left hmidP hk)
    _ = _ := by ring

/-! ## The local deficit law -/

/-- **The local deficit law at abscissa `σ`.**  If for every `η > 0` there are windows
`(T − 2L, T + 2L]` with `L` arbitrarily large, `T − L ≥ 8`, `log(T + 2L) ≤ ηL`, and deficit weight
at most `(E + η)·2L`, then `|lam(m) − Λ(m)| m^{−σ} ≤ 4πE` for every `m ≥ 2`. -/
theorem abs_sub_vonMangoldt_mul_rpow_le_of_localDeficit {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {σ : ℝ} (hσ : 1 < σ) {E : ℝ}
    (hloc : ∀ η > 0, ∀ L₀ : ℝ, ∃ T L : ℝ, L₀ ≤ L ∧ 8 ≤ T - L ∧
      Real.log (T + 2 * L) ≤ η * L ∧
      windowDeficitCount hW (T - 2 * L) (T + 2 * L) ≤ (E + η) * (2 * L)) {m : ℕ} (hm : 2 ≤ m) :
    |lam m - ArithmeticFunction.vonMangoldt m| * (m : ℝ) ^ (-σ) ≤ 4 * (π * E) := by
  rw [← abs_deviationCoeff hm]
  refine abs_le_four_mul_of_logCosSeries_window (summable_abs_deviationCoeff hW hσ)
    (by simp [deviationCoeff]) (by simp [deviationCoeff]) (deficitEnvelope_nonneg hW hσ)
    (continuous_deficitEnvelope hW hσ) (fun η hη L₀ => ?_) hm
  set C := envelopeConst σ with hC
  have hC0 : 0 ≤ C := by
    have h2 : 0 ≤ 1 / σ := by positivity
    have h3 : 0 ≤ 1 / (σ - 1) := one_div_nonneg.mpr (by linarith)
    have h4 := vonMangoldtMajorant_nonneg σ
    rw [hC, envelopeConst]
    linarith
  set η' : ℝ := η / (8 * σ + 2 * π) with hη'
  have hden : 0 < 8 * σ + 2 * π := by positivity
  have hη'0 : 0 < η' := div_pos hη hden
  have hη'1 : 2 * σ * η' ≤ η / 4 := by
    rw [hη', mul_div_assoc', div_le_div_iff₀ hden (by norm_num)]
    nlinarith [Real.pi_pos]
  have hη'2 : π * η' ≤ η / 2 := by
    rw [hη', mul_div_assoc', div_le_div_iff₀ hden (by norm_num)]
    nlinarith [Real.pi_pos]
  set L₁ : ℝ := max (max L₀ (σ + 2)) (8 * σ * C / η + 2) with hL₁
  obtain ⟨T, L, hLL, h8, hlog, hD⟩ := hloc η' hη'0 L₁
  have hL2 : σ + 2 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hLL)
  have hL3 : 8 * σ * C / η + 2 ≤ L := (le_max_right _ _).trans hLL
  have hL0 : L₀ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hLL)
  have hL1 : 1 < L := by linarith
  have hLpos : 0 < L := by linarith
  refine ⟨T - L, 2 * L, by linarith, by linarith, ?_, fun t _ => neg_deficitEnvelope_le hW hσ t⟩
  have hI := integral_deficitEnvelope_localWindow_le hW hσ hL1 (by linarith) h8
  rw [show T - L + 2 * L = T + L by ring]
  -- the tail term is at most `(η/2)·2L`
  have hLm1 : 0 < L - 1 := by linarith
  have htail : 2 * σ / (L - 1) * (Real.log (T + 2 * L) / 2 + C) ≤ η / 2 := by
    have hB : Real.log (T + 2 * L) / 2 + C ≤ η' * L / 2 + C := by linarith
    have hfrac : L / (L - 1) ≤ 2 := by rw [div_le_iff₀ hLm1]; linarith
    have hCL : 2 * σ * C / (L - 1) ≤ η / 4 := by
      rw [div_le_iff₀ hLm1]
      have : 8 * σ * C / η ≤ L - 2 := by linarith
      rw [div_le_iff₀ hη] at this
      nlinarith
    calc 2 * σ / (L - 1) * (Real.log (T + 2 * L) / 2 + C)
        ≤ 2 * σ / (L - 1) * (η' * L / 2 + C) :=
          mul_le_mul_of_nonneg_left hB (div_nonneg (by linarith) hLm1.le)
      _ = σ * η' * (L / (L - 1)) + 2 * σ * C / (L - 1) := by field_simp
      _ ≤ σ * η' * 2 + η / 4 := by
          gcongr
      _ ≤ η / 2 := by linarith
  have hDπ : π * windowDeficitCount hW (T - 2 * L) (T + 2 * L) ≤ (π * E + η / 2) * (2 * L) := by
    calc π * windowDeficitCount hW (T - 2 * L) (T + 2 * L) ≤ π * ((E + η') * (2 * L)) :=
          mul_le_mul_of_nonneg_left hD Real.pi_pos.le
      _ = (π * E + π * η') * (2 * L) := by ring
      _ ≤ (π * E + η / 2) * (2 * L) := by gcongr
  calc ∫ t in (T - L)..(T + L), deficitEnvelope hW σ t
      ≤ π * windowDeficitCount hW (T - 2 * L) (T + 2 * L) +
          2 * L * (2 * σ / (L - 1) * (Real.log (T + 2 * L) / 2 + envelopeConst σ)) := hI
    _ ≤ (π * E + η / 2) * (2 * L) + 2 * L * (η / 2) :=
        add_le_add hDπ (mul_le_mul_of_nonneg_left htail (by linarith))
    _ = (π * E + η) * (2 * L) := by ring

/-- **The local deficit law.**  If for every `η > 0` some window `(T − 2L, T + 2L]` with
`T − L ≥ 8` and `log(T + 2L) ≤ ηL` carries deficit weight at most `ηL`, then `lam = Λ` on
`n ≥ 2`. -/
theorem eq_vonMangoldt_of_localDeficit {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hloc : ∀ η > 0, ∃ T L : ℝ, 0 < L ∧ 8 ≤ T - L ∧ Real.log (T + 2 * L) ≤ η * L ∧
      windowDeficitCount hW (T - 2 * L) (T + 2 * L) ≤ η * L) :
    ∀ m : ℕ, 2 ≤ m → lam m = ArithmeticFunction.vonMangoldt m := by
  intro m hm
  have hlog8 : 2 ≤ Real.log 8 := by
    have h := Real.log_two_gt_d9
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast
    linarith
  have h := abs_sub_vonMangoldt_mul_rpow_le_of_localDeficit hW (σ := 2) (by norm_num) (E := 0)
    (fun η hη L₀ => ?_) hm
  · have hpos : (0 : ℝ) < (m : ℝ) ^ (-(2 : ℝ)) :=
      Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < m)) _
    have h0 : |lam m - ArithmeticFunction.vonMangoldt m| * (m : ℝ) ^ (-(2 : ℝ)) ≤ 0 := by
      simpa using h
    have := mul_nonneg (abs_nonneg (lam m - ArithmeticFunction.vonMangoldt m)) hpos.le
    have habs : |lam m - ArithmeticFunction.vonMangoldt m| = 0 := by nlinarith
    rw [abs_eq_zero, sub_eq_zero] at habs
    exact habs
  · set η₁ : ℝ := min η (2 / (|L₀| + 1)) with hη₁
    have hη₁0 : 0 < η₁ := lt_min hη (by positivity)
    obtain ⟨T, L, hL0, h8, hlog, hD⟩ := hloc η₁ hη₁0
    have hlogpos : 2 ≤ Real.log (T + 2 * L) :=
      hlog8.trans (Real.log_le_log (by norm_num) (by linarith))
    have hLbig : |L₀| + 1 ≤ L := by
      have h1 : 2 ≤ η₁ * L := hlogpos.trans hlog
      have h2 : η₁ ≤ 2 / (|L₀| + 1) := min_le_right _ _
      have h3 : 2 ≤ 2 / (|L₀| + 1) * L := h1.trans (mul_le_mul_of_nonneg_right h2 hL0.le)
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at h3
      linarith
    refine ⟨T, L, by linarith [le_abs_self L₀], h8, hlog.trans ?_, ?_⟩
    · exact mul_le_mul_of_nonneg_right (min_le_left _ _) (by linarith [abs_nonneg L₀])
    · have hL0 : 0 ≤ L := by linarith [abs_nonneg L₀]
      calc windowDeficitCount hW (T - 2 * L) (T + 2 * L) ≤ η₁ * L := hD
        _ ≤ η * L := mul_le_mul_of_nonneg_right (min_le_left _ _) hL0
        _ ≤ (0 + η) * (2 * L) := by nlinarith

/-- Under the local deficit law's hypothesis, RH holds. -/
theorem riemannHypothesis_of_localDeficit {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hloc : ∀ η > 0, ∃ T L : ℝ, 0 < L ∧ 8 ≤ T - L ∧ Real.log (T + 2 * L) ≤ η * L ∧
      windowDeficitCount hW (T - 2 * L) (T + 2 * L) ≤ η * L) : RiemannHypothesis :=
  riemannHypothesis_of_weilPositiveFull_of_ge hW fun n hn =>
    (eq_vonMangoldt_of_localDeficit hW hloc n hn).ge

/-- **Deficit-free windows.**  If for every `η > 0` some window `(T − 2L, T + 2L]` with
`T − L ≥ 8` and `log(T + 2L) ≤ ηL` contains no deficit (every zero there is critical and carries
its full multiplicity), then `lam = Λ` on `n ≥ 2`. -/
theorem eq_vonMangoldt_of_deficitFree_windows {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hfree : ∀ η > 0, ∃ T L : ℝ, 0 < L ∧ 8 ≤ T - L ∧ Real.log (T + 2 * L) ≤ η * L ∧
      ∀ q : XiZeroCopy, T - 2 * L < ((q.1 : ℂ)).im → ((q.1 : ℂ)).im ≤ T + 2 * L →
        deficitWeight hW q = 0) :
    ∀ m : ℕ, 2 ≤ m → lam m = ArithmeticFunction.vonMangoldt m := by
  refine eq_vonMangoldt_of_localDeficit hW fun η hη => ?_
  obtain ⟨T, L, hL, h8, hlog, hq⟩ := hfree η hη
  refine ⟨T, L, hL, h8, hlog, ?_⟩
  have h0 : windowDeficitCount hW (T - 2 * L) (T + 2 * L) = 0 := by
    refine (tsum_congr fun q => ?_).trans tsum_zero
    unfold windowDeficitWeight
    split_ifs with h
    · exact hq q h.1 h.2
    · rfl
  rw [h0]
  positivity

end RHTower.WeilSpectral

end
