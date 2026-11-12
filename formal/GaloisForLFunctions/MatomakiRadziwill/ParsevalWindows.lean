import GaloisForLFunctions.MatomakiRadziwill.LadderMeanSquare
import GaloisForLFunctions.RHTower.Sieve.LogWindowPlancherel
import GaloisForLFunctions.RHTower.Sieve.LogWindowCount
import GaloisForLFunctions.RHTower.Sieve.GallagherRange
import GaloisForLFunctions.RHTower.Sieve.SupportMeanSquare

/-!
# Logarithmic windows from the Dirichlet-polynomial mean square

For `P(w) = Σ_{n ∈ s} a_n n^{2πiw}` with `0 ∉ s`, `n ≤ M`, energy `E = Σ |a_n|²`, and `W ≥ 1`:

* **frequency tail** (`setIntegral_tail_le`): on the dyadic shells `2^k W < |w| ≤ 2^{k+1} W` the window
  kernel is `≤ (π 2^k W)^{-2}` and the mean value theorem bounds `∫|P|²`, so
  `∫_{|w| > W} |K_δ(w)|² |P(w)|² ≤ E (4/W + M/W²)`;
* **windows** (`integral_normSq_logWindowSum_le_split`): with Plancherel,
  `∫_ℝ |Σ_{e^u < n ≤ e^{u+δ}} a_n|² du ≤ δ² ∫_{|w| ≤ W} |P|² + E (4/W + M/W²)`;
* **raw coefficients** (`integral_normSq_logWindowSum_le_coefA`): for `|f| ≤ 1` on `s = (X, 4X]`, a
  window of `f` is `e^u` times the window of `f(n)/n` up to `#window · δ`, so
  `∫_ℝ |window of f|² ≤ 32X² ∫_ℝ |window of f(n)/n|² + 2((4X(e^δ − 1) + 1)δ)² (log 4 + δ)`.
-/

open Finset MeasureTheory Set Filter Topology RHTower.Sieve

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- The dyadic frequency shell `2^k W < |w| ≤ 2^{k+1} W`. -/
def freqShell (W : ℝ) (k : ℕ) : Set ℝ :=
  (fun w : ℝ => |w|) ⁻¹' Set.Ioc (2 ^ k * W) (2 ^ (k + 1) * W)

theorem mem_freqShell {W w : ℝ} {k : ℕ} :
    w ∈ freqShell W k ↔ 2 ^ k * W < |w| ∧ |w| ≤ 2 ^ (k + 1) * W := Iff.rfl

theorem measurableSet_freqShell (W : ℝ) (k : ℕ) : MeasurableSet (freqShell W k) :=
  continuous_abs.measurable measurableSet_Ioc

theorem iUnion_freqShell {W : ℝ} (hW : 0 < W) : (⋃ k, freqShell W k) = {w : ℝ | W < |w|} := by
  classical
  ext w
  simp only [Set.mem_iUnion, mem_freqShell, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, h1, -⟩
    have : W ≤ 2 ^ k * W := le_mul_of_one_le_left hW.le (one_le_pow₀ (by norm_num))
    linarith
  · intro hw
    have hex : ∃ k : ℕ, |w| ≤ 2 ^ (k + 1) * W := by
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (|w| / W) (by norm_num : (1 : ℝ) < 2)
      refine ⟨k, ?_⟩
      have h1 : |w| < 2 ^ k * W := by rwa [div_lt_iff₀ hW] at hk
      have h2 : (2 : ℝ) ^ k ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ k)
      nlinarith
    refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, pow_zero, one_mul]; exact hw
    · obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
      have hmin := Nat.find_min hex (show k < Nat.find hex by omega)
      rw [hk]
      push Not at hmin
      exact hmin

theorem pairwise_disjoint_freqShell {W : ℝ} (hW : 0 < W) :
    Pairwise (Function.onFun Disjoint (freqShell W)) := by
  intro i j hij
  wlog h : i < j generalizing i j
  · exact (this hij.symm (lt_of_le_of_ne (not_lt.mp h) hij.symm)).symm
  show Disjoint (freqShell W i) (freqShell W j)
  rw [Set.disjoint_left]
  intro w hi hj
  rw [mem_freqShell] at hi hj
  have h2 : (2 : ℝ) ^ (i + 1) ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) h
  have := mul_le_mul_of_nonneg_right h2 hW.le
  linarith [hi.2, hj.1]

/-- **One frequency shell.** -/
theorem setIntegral_freqShell_le (a : ℕ → ℂ) {s : Finset ℕ} (hs0 : (0 : ℕ) ∉ s) {M : ℕ}
    (hsM : ∀ n ∈ s, n ≤ M) {δ W : ℝ} (hδ : 0 ≤ δ) (hW : 1 ≤ W) (k : ℕ) :
    (∫ w in freqShell W k, ‖logWindowKernel δ w‖ ^ 2 * ‖logPoly a s w‖ ^ 2)
      ≤ (∑ n ∈ s, ‖a n‖ ^ 2) * (5 / (Real.pi * W) / 2 ^ k
        + 5 * Real.exp 1 * M / (2 * Real.pi ^ 2 * W ^ 2) / (2 ^ k) ^ 2) := by
  have hW0 : 0 < W := by linarith
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hpi := Real.pi_pos
  set c : ℝ := 1 / (Real.pi * (2 ^ k * W)) ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hpt : ∀ w ∈ freqShell W k, ‖logWindowKernel δ w‖ ^ 2 * ‖logPoly a s w‖ ^ 2
      ≤ c * ‖logPoly a s w‖ ^ 2 := by
    intro w hw
    rw [mem_freqShell] at hw
    have hw0 : w ≠ 0 := by
      intro h
      rw [h, abs_zero] at hw
      linarith [mul_pos h2k hW0, hw.1]
    have hK := normSq_logWindowKernel_le_inv_sq δ hw0
    have hK' : 1 / (Real.pi * w) ^ 2 ≤ c := by
      rw [hc]
      apply one_div_le_one_div_of_le (by positivity)
      have : (2 ^ k * W) ^ 2 ≤ w ^ 2 := by
        rw [← sq_abs w]; exact pow_le_pow_left₀ (by positivity) hw.1.le 2
      have hπ2 : (0 : ℝ) ≤ Real.pi ^ 2 := by positivity
      calc (Real.pi * (2 ^ k * W)) ^ 2 = Real.pi ^ 2 * (2 ^ k * W) ^ 2 := by ring
        _ ≤ Real.pi ^ 2 * w ^ 2 := mul_le_mul_of_nonneg_left this hπ2
        _ = (Real.pi * w) ^ 2 := by ring
    exact mul_le_mul_of_nonneg_right (le_trans hK hK') (sq_nonneg _)
  have hint1 := (integrable_normSq_logWindowKernel_mul_logPoly a s hδ).integrableOn
    (s := freqShell W k)
  have hsub : freqShell W k ⊆ Icc (-(2 ^ (k + 1) * W)) (2 ^ (k + 1) * W) := by
    intro w hw
    rw [mem_freqShell] at hw
    exact abs_le.mp hw.2
  have hIcc : IntegrableOn (fun w => ‖logPoly a s w‖ ^ 2)
      (Icc (-(2 ^ (k + 1) * W)) (2 ^ (k + 1) * W)) :=
    ((continuous_logPoly a s).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hint2 : IntegrableOn (fun w => c * ‖logPoly a s w‖ ^ 2) (freqShell W k) :=
    (hIcc.mono_set hsub).const_mul c
  have h1 := setIntegral_mono_on hint1 hint2 (measurableSet_freqShell W k) hpt
  rw [integral_const_mul] at h1
  have h2 : (∫ w in freqShell W k, ‖logPoly a s w‖ ^ 2)
      ≤ ∫ w in Icc (-(2 ^ (k + 1) * W)) (2 ^ (k + 1) * W), ‖logPoly a s w‖ ^ 2 :=
    setIntegral_mono_set hIcc (ae_of_all _ fun w => sq_nonneg _) hsub.eventuallyLE
  have hW' : 1 ≤ 2 ^ (k + 1) * W := by
    have : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
    nlinarith
  have h3 := integral_Icc_normSq_logPoly_le_energy a hs0 hsM hW'
  calc (∫ w in freqShell W k, ‖logWindowKernel δ w‖ ^ 2 * ‖logPoly a s w‖ ^ 2)
      ≤ c * ∫ w in freqShell W k, ‖logPoly a s w‖ ^ 2 := h1
    _ ≤ c * ((5 * Real.pi / 2 * (2 ^ (k + 1) * W) + 5 * Real.exp 1 / 2 * (M : ℝ))
          * (∑ n ∈ s, ‖a n‖ ^ 2)) := mul_le_mul_of_nonneg_left (le_trans h2 h3) hc0
    _ = _ := by rw [hc]; field_simp; ring

/-- **The frequency tail.** -/
theorem setIntegral_tail_le (a : ℕ → ℂ) {s : Finset ℕ} (hs0 : (0 : ℕ) ∉ s) {M : ℕ}
    (hsM : ∀ n ∈ s, n ≤ M) {δ W : ℝ} (hδ : 0 ≤ δ) (hW : 1 ≤ W) :
    (∫ w in {w : ℝ | W < |w|}, ‖logWindowKernel δ w‖ ^ 2 * ‖logPoly a s w‖ ^ 2)
      ≤ (∑ n ∈ s, ‖a n‖ ^ 2) * (4 / W + M / W ^ 2) := by
  have hW0 : 0 < W := by linarith
  rw [← iUnion_freqShell hW0]
  have hfi := (integrable_normSq_logWindowKernel_mul_logPoly a s hδ).integrableOn
    (s := ⋃ k, freqShell W k)
  have hsum := hasSum_integral_iUnion (measurableSet_freqShell W)
    (pairwise_disjoint_freqShell hW0) hfi
  set E := ∑ n ∈ s, ‖a n‖ ^ 2 with hE
  set A := 5 / (Real.pi * W) with hA
  set B := 5 * Real.exp 1 * M / (2 * Real.pi ^ 2 * W ^ 2) with hB
  have hg : HasSum (fun k : ℕ => E * (A / 2 ^ k + B / (2 ^ k) ^ 2)) (E * (2 * A + 4 / 3 * B)) := by
    have h1 : HasSum (fun k : ℕ => ((1 : ℝ) / 2) ^ k) 2 := hasSum_geometric_two
    have h2 : HasSum (fun k : ℕ => ((1 : ℝ) / 4) ^ k) (4 / 3) := by
      have := hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)
      convert this using 1; norm_num
    have h3 := ((h1.mul_left A).add (h2.mul_left B)).mul_left E
    have hfun : (fun k : ℕ => E * (A * ((1 : ℝ) / 2) ^ k + B * ((1 : ℝ) / 4) ^ k))
        = fun k : ℕ => E * (A / 2 ^ k + B / (2 ^ k) ^ 2) := by
      funext k
      have h4 : ((2 : ℝ) ^ k) ^ 2 = 4 ^ k := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [one_div_pow, one_div_pow, ← h4]
      ring
    have hval : E * (A * 2 + B * (4 / 3)) = E * (2 * A + 4 / 3 * B) := by ring
    rw [hfun, hval] at h3
    exact h3
  refine le_trans (hasSum_le (fun k => setIntegral_freqShell_le a hs0 hsM hδ hW k) hsum hg) ?_
  have hE0 : 0 ≤ E := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hE0
  have hpi := Real.pi_gt_three
  have hpi' := Real.pi_gt_d2
  have he := Real.exp_one_lt_d9
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have h1 : 2 * A ≤ 4 / W := by
    have hπ : 10 / Real.pi ≤ 4 := by rw [div_le_iff₀ Real.pi_pos]; linarith
    have e1 : 2 * A = 10 / Real.pi * (1 / W) := by rw [hA]; field_simp; ring
    have e2 : 4 / W = 4 * (1 / W) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right hπ (by positivity)
  have h2 : 4 / 3 * B ≤ M / W ^ 2 := by
    have hπ2 : 10 * Real.exp 1 / (3 * Real.pi ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have e1 : 4 / 3 * B = 10 * Real.exp 1 / (3 * Real.pi ^ 2) * (M / W ^ 2) := by
      rw [hB]; field_simp; ring
    rw [e1]
    have : 0 ≤ (M : ℝ) / W ^ 2 := by positivity
    nlinarith
  linarith

/-- **Window mean square against the Dirichlet-polynomial mean square.** -/
theorem integral_normSq_logWindowSum_le_split (a : ℕ → ℂ) {s : Finset ℕ} (hs0 : (0 : ℕ) ∉ s)
    {M : ℕ} (hsM : ∀ n ∈ s, n ≤ M) {δ W : ℝ} (hδ : 0 ≤ δ) (hW : 1 ≤ W) :
    (∫ u : ℝ, ‖logWindowSum a s δ u‖ ^ 2)
      ≤ δ ^ 2 * (∫ w in Icc (-W) W, ‖logPoly a s w‖ ^ 2)
        + (∑ n ∈ s, ‖a n‖ ^ 2) * (4 / W + M / W ^ 2) := by
  rw [integral_normSq_logWindowSum_eq a s hδ]
  have hg := integrable_normSq_logWindowKernel_mul_logPoly a s hδ
  rw [← integral_add_compl (measurableSet_Icc (a := -W) (b := W)) hg]
  have hcompl : (Icc (-W) W)ᶜ = {w : ℝ | W < |w|} := by
    ext w
    rw [Set.mem_compl_iff, Set.mem_Icc, Set.mem_setOf_eq, lt_abs]
    constructor
    · intro h
      by_contra hc
      push Not at hc
      exact h ⟨by linarith [hc.2], hc.1⟩
    · rintro (h | h) ⟨h1, h2⟩
      · linarith
      · linarith
  rw [hcompl]
  have hin : (∫ w in Icc (-W) W, ‖logWindowKernel δ w‖ ^ 2 * ‖logPoly a s w‖ ^ 2)
      ≤ δ ^ 2 * ∫ w in Icc (-W) W, ‖logPoly a s w‖ ^ 2 := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on hg.integrableOn
      ((((continuous_logPoly a s).norm.pow 2).continuousOn.integrableOn_compact
        isCompact_Icc).const_mul _) measurableSet_Icc fun w _ => ?_
    exact mul_le_mul_of_nonneg_right (normSq_logWindowKernel_le_sq δ w) (sq_nonneg _)
  have htail := setIntegral_tail_le a hs0 hsM hδ hW
  linarith

/-- **A window of `f` against the window of `f(n)/n`.** -/
theorem normSq_logWindowSum_le_coefA {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {X : ℕ} (hX : 1 ≤ X)
    {δ : ℝ} (hδ : 0 ≤ δ) (u : ℝ) :
    ‖logWindowSum f (Finset.Ioc X (4 * X)) δ u‖ ^ 2
      ≤ 2 * (4 * (X : ℝ)) ^ 2 * ‖logWindowSum (coefA f) (Finset.Ioc X (4 * X)) δ u‖ ^ 2
        + 2 * ((4 * X * (Real.exp δ - 1) + 1) * δ) ^ 2
          * (Icc (Real.log X - δ) (Real.log (4 * X))).indicator (fun _ => (1 : ℝ)) u := by
  classical
  rw [logWindowSum_eq_filter, logWindowSum_eq_filter]
  set F := (Finset.Ioc X (4 * X)).filter (fun n : ℕ => u < Real.log n ∧ Real.log n ≤ u + δ)
    with hF
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hB0 : 0 ≤ 4 * (X : ℝ) * (Real.exp δ - 1) + 1 := by
    have : 0 ≤ Real.exp δ - 1 := by linarith [Real.one_le_exp hδ]
    positivity
  rcases F.eq_empty_or_nonempty with hFe | ⟨n₀, hn₀⟩
  · rw [hFe]
    simp only [sum_empty, norm_zero]
    have hi : 0 ≤ (Icc (Real.log X - δ) (Real.log (4 * X))).indicator (fun _ => (1 : ℝ)) u :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) u
    have : 0 ≤ 2 * ((4 * X * (Real.exp δ - 1) + 1) * δ) ^ 2
        * (Icc (Real.log X - δ) (Real.log (4 * X))).indicator (fun _ => (1 : ℝ)) u :=
      mul_nonneg (by positivity) hi
    nlinarith
  -- the window meets `(X, 4X]`, so `log X − δ ≤ u ≤ log 4X`
  have hmemF : ∀ n ∈ F, X < n ∧ n ≤ 4 * X ∧ Real.exp u < n ∧ (n : ℝ) ≤ Real.exp (u + δ) := by
    intro n hn
    rw [hF, Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    refine ⟨h1, h2, ?_, ?_⟩
    · rwa [← Real.lt_log_iff_exp_lt hn0]
    · rwa [← Real.log_le_iff_le_exp hn0]
  obtain ⟨h1, h2, h3, h4⟩ := hmemF n₀ hn₀
  have hn₀0 : (0 : ℝ) < n₀ := lt_of_lt_of_le (Real.exp_pos u) h3.le
  have hind : (Icc (Real.log X - δ) (Real.log (4 * X))).indicator (fun _ => (1 : ℝ)) u = 1 := by
    refine Set.indicator_of_mem ?_ _
    have hl1 : Real.log X ≤ Real.log n₀ :=
      Real.log_le_log hX0 (by exact_mod_cast h1.le)
    have hl2 : Real.log n₀ ≤ Real.log (4 * X) :=
      Real.log_le_log hn₀0 (by exact_mod_cast h2)
    have hl3 : Real.log n₀ ≤ u + δ := by
      rw [Real.log_le_iff_le_exp hn₀0]; exact h4
    have hl4 : u < Real.log n₀ := by rw [Real.lt_log_iff_exp_lt hn₀0]; exact h3
    exact ⟨by linarith, by linarith⟩
  rw [hind, mul_one]
  have heu : Real.exp u ≤ 4 * X := by
    have : ((n₀ : ℕ) : ℝ) ≤ ((4 * X : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at this
    linarith
  -- the count of the window
  have hcard : (F.card : ℝ) ≤ 4 * X * (Real.exp δ - 1) + 1 := by
    have hsub : F ⊆ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp (u + δ)⌋₊ := by
      intro n hn
      obtain ⟨-, -, hn3, hn4⟩ := hmemF n hn
      rw [Finset.mem_Ioc]
      exact ⟨Nat.floor_lt (Real.exp_pos u).le |>.mpr hn3, Nat.le_floor hn4⟩
    have hc := card_Ioc_floor_le (X := ⌊Real.exp u⌋₊) (y := Real.exp (u + δ))
      (le_trans (Nat.floor_le (Real.exp_pos u).le) (Real.exp_le_exp.mpr (by linarith)))
    have hfl : Real.exp u - 1 ≤ (⌊Real.exp u⌋₊ : ℝ) := (Nat.sub_one_lt_floor _).le
    have hexp : Real.exp (u + δ) = Real.exp u * Real.exp δ := Real.exp_add u δ
    have h5 : (F.card : ℝ) ≤ Real.exp u * (Real.exp δ - 1) + 1 := by
      have : (F.card : ℝ) ≤ ((Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp (u + δ)⌋₊).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      nlinarith
    have h6 : Real.exp u * (Real.exp δ - 1) ≤ 4 * X * (Real.exp δ - 1) :=
      mul_le_mul_of_nonneg_right heu (by linarith [Real.one_le_exp hδ])
    linarith
  -- each term moves by at most `δ`
  have hdecomp : ∑ n ∈ F, f n
      = (Real.exp u : ℂ) * ∑ n ∈ F, coefA f n + ∑ n ∈ F, f n * (1 - Real.exp u / n) := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℂ) ≠ 0 := by
      have := (hmemF n hn).1; exact_mod_cast (show n ≠ 0 by omega)
    rw [coefA]
    field_simp
    ring
  have hterm : ∀ n ∈ F, ‖f n * (1 - Real.exp u / n)‖ ≤ δ := by
    intro n hn
    obtain ⟨-, -, hn3, hn4⟩ := hmemF n hn
    have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (Real.exp_pos u) hn3.le
    have hq1 : Real.exp u / n ≤ 1 := by rw [div_le_one hn0]; exact hn3.le
    have hq2 : Real.exp (-δ) ≤ Real.exp u / n := by
      rw [le_div_iff₀ hn0, Real.exp_neg, ← div_eq_inv_mul, div_le_iff₀ (Real.exp_pos δ),
        ← Real.exp_add]
      exact hn4
    have hq3 : 1 - δ ≤ Real.exp (-δ) := by linarith [Real.add_one_le_exp (-δ)]
    have hc : ((1 : ℂ) - Real.exp u / n) = ((1 - Real.exp u / n : ℝ) : ℂ) := by push_cast; ring
    rw [norm_mul, hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    calc ‖f n‖ * (1 - Real.exp u / n) ≤ 1 * (1 - Real.exp u / n) :=
          mul_le_mul_of_nonneg_right (hf n) (by linarith)
      _ ≤ δ := by linarith
  have herr : ‖∑ n ∈ F, f n * (1 - Real.exp u / n)‖ ≤ (4 * X * (Real.exp δ - 1) + 1) * δ := by
    calc ‖∑ n ∈ F, f n * (1 - Real.exp u / n)‖ ≤ ∑ n ∈ F, ‖f n * (1 - Real.exp u / n)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _n ∈ F, δ := sum_le_sum hterm
      _ = F.card * δ := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hδ
  have hmain : ‖∑ n ∈ F, f n‖
      ≤ 4 * X * ‖∑ n ∈ F, coefA f n‖ + (4 * X * (Real.exp δ - 1) + 1) * δ := by
    rw [hdecomp]
    refine le_trans (norm_add_le _ _) (add_le_add ?_ herr)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos u)]
    exact mul_le_mul_of_nonneg_right heu (norm_nonneg _)
  have h0 : 0 ≤ ‖∑ n ∈ F, f n‖ := norm_nonneg _
  have hc0 : 0 ≤ ‖∑ n ∈ F, coefA f n‖ := norm_nonneg _
  nlinarith [sq_nonneg (4 * X * ‖∑ n ∈ F, coefA f n‖ - (4 * X * (Real.exp δ - 1) + 1) * δ)]

/-- **Raw windows against the `f(n)/n` windows, integrated.** -/
theorem integral_normSq_logWindowSum_le_coefA {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {X : ℕ}
    (hX : 1 ≤ X) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫ u : ℝ, ‖logWindowSum f (Finset.Ioc X (4 * X)) δ u‖ ^ 2)
      ≤ 2 * (4 * (X : ℝ)) ^ 2 * (∫ u : ℝ, ‖logWindowSum (coefA f) (Finset.Ioc X (4 * X)) δ u‖ ^ 2)
        + 2 * ((4 * X * (Real.exp δ - 1) + 1) * δ) ^ 2 * (Real.log 4 + δ) := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hint1 := integrable_normSq_logWindowSum f (Finset.Ioc X (4 * X)) δ
  have hint2 := integrable_normSq_logWindowSum (coefA f) (Finset.Ioc X (4 * X)) δ
  have hind : Integrable ((Icc (Real.log X - δ) (Real.log (4 * X))).indicator
      (fun _ => (1 : ℝ))) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hmono := integral_mono hint1 ((hint2.const_mul (2 * (4 * (X : ℝ)) ^ 2)).add
    (hind.const_mul (2 * ((4 * X * (Real.exp δ - 1) + 1) * δ) ^ 2)))
    (fun u => normSq_logWindowSum_le_coefA hf hX hδ u)
  simp only [Pi.add_apply] at hmono
  rw [integral_add (hint2.const_mul _) (hind.const_mul _), integral_const_mul,
    integral_const_mul, integral_indicator_const _ measurableSet_Icc] at hmono
  have hlen : Real.log X - δ ≤ Real.log (4 * X) := by
    have : Real.log X ≤ Real.log (4 * X) := Real.log_le_log hX0 (by linarith)
    linarith
  rw [Real.volume_real_Icc_of_le hlen, smul_eq_mul, mul_one] at hmono
  have hl4 : Real.log (4 * X) - (Real.log X - δ) = Real.log 4 + δ := by
    rw [Real.log_mul (by norm_num) hX0.ne']; ring
  rw [hl4] at hmono
  exact hmono

end

end GaloisForLFunctions.MatomakiRadziwill
