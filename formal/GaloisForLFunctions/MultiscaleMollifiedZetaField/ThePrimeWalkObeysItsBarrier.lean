import GaloisForLFunctions.MultiscaleMollifiedZetaField.SelbergsCentralLimitTheorem

/-!
# The prime walk obeys its barrier

The Gaussian rate of the prime walk `S_j(t) = Σ_{p ≤ y_j} p^{−1/2} cos(t log p)`, with mass
`W_j = Σ_{p ≤ y_j} 1/p`, and the barrier estimates it gives.

* **The sharp rate on the model.** `E e^{b Re X_p} = I₀(b) ≤ e^{b²/4}`
  (`integral_exp_phase_le_sharp`), the true variance proxy `½` of a phase; hence
  `E e^{bS} ≤ e^{b²W/4}` and `P(S ≥ λ) ≤ e^{−λ²/W}`, the exact Gaussian exponent of variance `W/2`.
* **The sharp rate on heights.** For `K W ≤ λ²`, `λ ≥ 1`, the heights of `[T, 2T]` with
  `|S(t)| ≥ λ` have measure `≤ T · 2e²K²e^{−K} + 2Y^{4K}` (`volume_primeField_ge_le`), through the
  Steinhaus transfer of the `2K`-th moment.
* **The barrier.** At the doubly exponential cuts `y_j = ⌈exp(exp j)⌉`, with `K_j = ⌈4 log(j+2)⌉`,
  the heights crossing `√(K_j W_j)` at some scale `j₀ ≤ j ≤ J` have proportion `≤ 256/j₀` up to the
  transfer error (`volume_barrier_crossing_le`), uniformly in `T`.

The walk is compared with its model only at scales `y_J^{4K_J} ≤ T^{1−}`: the barrier lives
below the window, where the phases are independent.
-/

noncomputable section

open Complex Set MeasureTheory Filter ArithmeticFunction ProbabilityTheory Topology
open RHTower RHTower.SteinhausModel

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-! ### Moments of a phase -/

/-- The moment `∫_0^1 cos(2πx)^k dx`. -/
def cosMoment (k : ℕ) : ℝ := ∫ x in (0 : ℝ)..1, Real.cos (2 * Real.pi * x) ^ k

/-- A moment of the phase is a moment of the cosine. -/
theorem integral_phase_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∫ ω, phase p ω ^ k ∂steinhausMeasure = cosMoment k := by
  have hmap : steinhausMeasure.map (fun ω : Omega => ω p) = volume.restrict (Icc (0 : ℝ) 1) :=
    Measure.infinitePi_map_eval _ p
  have hm : Measurable fun ω : Omega => ω p := measurable_pi_apply p
  have h1 : ∫ ω, phase p ω ^ k ∂steinhausMeasure =
      ∫ ω, (fun x : ℝ => Real.cos (2 * Real.pi * x) ^ k) (ω p) ∂steinhausMeasure := by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only
    rw [phase_eq_cos hp]
  have h2 := integral_map (μ := steinhausMeasure) hm.aemeasurable
    (f := fun x : ℝ => Real.cos (2 * Real.pi * x) ^ k) (by fun_prop)
  rw [h1, ← h2, hmap, cosMoment, intervalIntegral.integral_of_le zero_le_one,
    integral_Icc_eq_integral_Ioc]

/-- The recursion of the cosine moments. -/
theorem cosMoment_add_two (k : ℕ) :
    cosMoment (k + 2) = ((k : ℝ) + 1) / ((k : ℝ) + 2) * cosMoment k := by
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  have hsub : ∀ n : ℕ, cosMoment n = (2 * Real.pi)⁻¹ * ∫ y in (0 : ℝ)..(2 * Real.pi), Real.cos y ^ n := by
    intro n
    unfold cosMoment
    have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
      (fun y : ℝ => Real.cos y ^ n) hπ
    simpa using h
  rw [hsub, hsub, integral_cos_pow]
  simp only [Real.sin_zero, Real.sin_two_pi, mul_zero, sub_self, zero_div, zero_add]
  ring

theorem cosMoment_zero : cosMoment 0 = 1 := by
  simp [cosMoment]

theorem cosMoment_one : cosMoment 1 = 0 := by
  have h := integral_phase_eq_zero (p := 2) Nat.prime_two
  have h2 := integral_phase_pow (p := 2) Nat.prime_two 1
  simp only [pow_one] at h2
  rw [← h2, h]

/-- Odd moments vanish. -/
theorem cosMoment_odd (j : ℕ) : cosMoment (2 * j + 1) = 0 := by
  induction j with
  | zero => simpa using cosMoment_one
  | succ j ih =>
    rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, cosMoment_add_two, ih, mul_zero]

/-- Even moments are dominated by the moments of the Gaussian of variance `½`. -/
theorem cosMoment_even_le (j : ℕ) :
    cosMoment (2 * j) * ((j.factorial : ℝ) * 4 ^ j) ≤ ((2 * j).factorial : ℝ) := by
  induction j with
  | zero => simp [cosMoment_zero]
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, cosMoment_add_two, Nat.factorial_succ j,
      Nat.factorial_succ (2 * j + 1), Nat.factorial_succ (2 * j), pow_succ]
    push_cast
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hd : (2 * (j : ℝ) + 2) ≠ 0 := by positivity
    have e : (2 * (j : ℝ) + 1) / (2 * (j : ℝ) + 2) * cosMoment (2 * j) *
        (((j : ℝ) + 1) * (j.factorial : ℝ) * (4 ^ j * 4)) =
        (2 * (2 * (j : ℝ) + 1)) * (cosMoment (2 * j) * ((j.factorial : ℝ) * 4 ^ j)) := by
      field_simp
      ring
    rw [e]
    have h2 : (0 : ℝ) ≤ ((2 * j).factorial : ℝ) := Nat.cast_nonneg _
    calc (2 * (2 * (j : ℝ) + 1)) * (cosMoment (2 * j) * ((j.factorial : ℝ) * 4 ^ j))
        ≤ (2 * (2 * (j : ℝ) + 1)) * ((2 * j).factorial : ℝ) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
      _ ≤ _ := by
          have h3 : 0 ≤ (j : ℝ) * ((2 * (j : ℝ) + 1) * ((2 * j).factorial : ℝ)) := by positivity
          nlinarith

/-- **The sharp moment generating function of a phase**: `I₀(b) ≤ exp(b²/4)`. -/
theorem integral_exp_phase_le_sharp {p : ℕ} (hp : p.Prime) (b : ℝ) :
    ∫ ω, Real.exp (b * phase p ω) ∂steinhausMeasure ≤ Real.exp (b ^ 2 / 4) := by
  -- expand the exponential
  have hpt : ∀ (k : ℕ) (ω : Omega), ‖(b * phase p ω) ^ k / (k.factorial : ℝ)‖ ≤
      |b| ^ k / (k.factorial : ℝ) := by
    intro k ω
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_mul, Nat.abs_cast]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_of_le_one_right (abs_nonneg b) (abs_phase_le p ω)) k
  have hterm : ∀ k : ℕ, Integrable (fun ω => (b * phase p ω) ^ k / (k.factorial : ℝ))
      steinhausMeasure := by
    intro k
    exact Integrable.of_bound
      (((((measurable_phase p).const_mul b).pow_const k).div_const _).aestronglyMeasurable)
      (|b| ^ k / (k.factorial : ℝ)) (Eventually.of_forall (hpt k))
  have hsum : Summable fun k : ℕ => ∫ ω, ‖(b * phase p ω) ^ k / (k.factorial : ℝ)‖ ∂steinhausMeasure := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun ω => norm_nonneg _) (fun k => ?_)
      (Real.summable_pow_div_factorial |b|)
    refine (integral_mono_of_nonneg (Eventually.of_forall fun ω => norm_nonneg _)
      (integrable_const (|b| ^ k / (k.factorial : ℝ))) (Eventually.of_forall (hpt k))).trans ?_
    simp
  have hhas := hasSum_integral_of_summable_integral_norm hterm hsum
  have hexp : ∀ ω, ∑' k : ℕ, (b * phase p ω) ^ k / (k.factorial : ℝ) = Real.exp (b * phase p ω) := by
    intro ω
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  simp_rw [hexp] at hhas
  have hval : ∀ k : ℕ, ∫ ω, (b * phase p ω) ^ k / (k.factorial : ℝ) ∂steinhausMeasure =
      b ^ k * cosMoment k / (k.factorial : ℝ) := by
    intro k
    simp_rw [mul_pow]
    rw [integral_div, integral_const_mul, integral_phase_pow hp]
  simp_rw [hval] at hhas
  -- the even partial sums stay below `exp(b²/4)`
  have hpart : ∀ N : ℕ, ∑ k ∈ Finset.range (2 * N), b ^ k * cosMoment k / (k.factorial : ℝ) ≤
      Real.exp (b ^ 2 / 4) := by
    intro N
    have hsplit : ∑ k ∈ Finset.range (2 * N), b ^ k * cosMoment k / (k.factorial : ℝ) =
        ∑ j ∈ Finset.range N, b ^ (2 * j) * cosMoment (2 * j) / ((2 * j).factorial : ℝ) := by
      induction N with
      | zero => simp
      | succ N ih =>
        rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
          ih, Finset.sum_range_succ, cosMoment_odd]
        simp
    rw [hsplit]
    refine le_trans (Finset.sum_le_sum fun j _ => ?_)
      (Real.sum_le_exp_of_nonneg (show 0 ≤ b ^ 2 / 4 by positivity) N)
    have hfac : (0 : ℝ) < ((2 * j).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hjf : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have h4 : (0 : ℝ) < 4 ^ j := by positivity
    have h := cosMoment_even_le j
    have hb : 0 ≤ b ^ (2 * j) := by
      rw [pow_mul]
      positivity
    have e : (b ^ 2 / 4) ^ j / (j.factorial : ℝ) = b ^ (2 * j) * (1 / ((j.factorial : ℝ) * 4 ^ j)) := by
      rw [div_pow, pow_mul]
      field_simp
    rw [e, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hb
    rw [div_le_div_iff₀ hfac (by positivity), one_mul]
    exact h
  have hlim := hhas.tendsto_sum_nat.comp (tendsto_id.const_mul_atTop' (show 0 < 2 by norm_num))
  exact le_of_tendsto hlim (Eventually.of_forall fun N => by
    simpa using hpart N)

/-- The sharp moment generating function of the model. -/
theorem integral_exp_modelField_le_sharp {w : ℕ → ℝ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (b : ℝ) :
    ∫ ω, Real.exp (b * modelField w P ω) ∂steinhausMeasure ≤
      Real.exp (b ^ 2 * (∑ p ∈ P, w p ^ 2) / 4) := by
  have hexp : (fun ω => Real.exp (b * modelField w P ω)) =
      fun ω => ∏ p ∈ P, (fun (p : ℕ) (x : ℝ) => Real.exp (b * w p * x)) p (phase p ω) := by
    funext ω
    rw [modelField_eq_sum_phase, Finset.mul_sum, Real.exp_sum]
    exact Finset.prod_congr rfl fun p _ => by ring_nf
  rw [hexp, integral_prod_phase_eq hP (fun (p : ℕ) (x : ℝ) => Real.exp (b * w p * x))
    (fun p => by fun_prop)]
  have hsum : b ^ 2 * (∑ p ∈ P, w p ^ 2) / 4 = ∑ p ∈ P, (b * w p) ^ 2 / 4 := by
    rw [Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hsum, Real.exp_sum]
  refine Finset.prod_le_prod (fun p _ => integral_nonneg fun ω => (Real.exp_pos _).le)
    fun p hp => ?_
  exact integral_exp_phase_le_sharp (hP p hp) (b * w p)

/-- **The Gaussian tail of the model**: `P(S ≥ λ) ≤ exp(−λ²/W)`. -/
theorem measureReal_modelField_ge_le {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) {lam : ℝ} (hlam : 0 < lam) (hW : 0 < ∑ p ∈ P, w p ^ 2) :
    steinhausMeasure.real {ω | lam ≤ modelField w P ω} ≤
      Real.exp (-(lam ^ 2 / ∑ p ∈ P, w p ^ 2)) := by
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = ∑ p ∈ P, w p ^ 2 := ⟨_, rfl⟩
  rw [← hWdef] at hW ⊢
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 2 * lam / W := ⟨_, rfl⟩
  have hb0 : 0 < b := by
    rw [hb]
    positivity
  have hm : Measurable fun ω => Real.exp (b * modelField w P ω) :=
    Real.measurable_exp.comp ((measurable_modelField w P).const_mul b)
  have hI : Integrable (fun ω => Real.exp (b * modelField w P ω)) steinhausMeasure := by
    refine Integrable.of_bound hm.aestronglyMeasurable (Real.exp (|b| * ∑ p ∈ P, w p))
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    refine Real.exp_le_exp.mpr ?_
    calc b * modelField w P ω ≤ |b * modelField w P ω| := le_abs_self _
      _ = |b| * |modelField w P ω| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (abs_modelField_le hw P ω) (abs_nonneg b)
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := steinhausMeasure)
    (Eventually.of_forall fun ω => (Real.exp_pos (b * modelField w P ω)).le) hI (Real.exp (b * lam))
  have hsub : {ω | lam ≤ modelField w P ω} ⊆
      {ω | Real.exp (b * lam) ≤ Real.exp (b * modelField w P ω)} := by
    intro ω hω
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω hb0.le)
  have hmono : steinhausMeasure.real {ω | lam ≤ modelField w P ω} ≤
      steinhausMeasure.real {ω | Real.exp (b * lam) ≤ Real.exp (b * modelField w P ω)} :=
    measureReal_mono hsub
  have hmgf := integral_exp_modelField_le_sharp (w := w) hP b
  rw [← hWdef] at hmgf
  have h1 : Real.exp (b * lam) * steinhausMeasure.real {ω | lam ≤ modelField w P ω} ≤
      Real.exp (b ^ 2 * W / 4) :=
    (mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le).trans (hmark.trans hmgf)
  have e : b ^ 2 * W / 4 - b * lam = -(lam ^ 2 / W) := by
    rw [hb]
    field_simp
    ring
  rw [← e, Real.exp_sub, le_div_iff₀ (Real.exp_pos _), mul_comm]
  exact h1

/-! ### High moments on the model -/

/-- **Even moments with the sharp variance proxy.** -/
theorem integral_modelField_even_pow_le_sharp {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (K : ℕ) {l : ℝ} (hl : 0 < l) :
    ∫ ω, modelField w P ω ^ (2 * K) ∂steinhausMeasure ≤
      ((2 * K).factorial : ℝ) * (l ^ (2 * K))⁻¹ * (2 * Real.exp (l ^ 2 * (∑ p ∈ P, w p ^ 2) / 4)) := by
  have hbd : ∀ b : ℝ, Integrable (fun ω => Real.exp (b * modelField w P ω)) steinhausMeasure := by
    intro b
    refine Integrable.of_bound
      (Real.measurable_exp.comp ((measurable_modelField w P).const_mul b)).aestronglyMeasurable
      (Real.exp (|b| * ∑ p ∈ P, w p)) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    refine Real.exp_le_exp.mpr ?_
    calc b * modelField w P ω ≤ |b * modelField w P ω| := le_abs_self _
      _ = |b| * |modelField w P ω| := abs_mul _ _
      _ ≤ |b| * ∑ p ∈ P, w p := mul_le_mul_of_nonneg_left (abs_modelField_le hw P ω) (abs_nonneg b)
  have hfac : (0 : ℝ) < ((2 * K).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hpt : ∀ ω, modelField w P ω ^ (2 * K) ≤
      ((2 * K).factorial : ℝ) * (l ^ (2 * K))⁻¹ *
        (Real.exp (l * modelField w P ω) + Real.exp (-l * modelField w P ω)) := by
    intro ω
    set s := modelField w P ω with hs
    have h1 := Real.pow_div_factorial_le_exp (x := l * |s|) (by positivity) (2 * K)
    have h2 : Real.exp (l * |s|) ≤ Real.exp (l * s) + Real.exp (-l * s) := by
      rcases le_total 0 s with h | h
      · rw [abs_of_nonneg h]
        linarith [Real.exp_pos (-l * s)]
      · rw [abs_of_nonpos h]
        have : l * -s = -l * s := by ring
        rw [this]
        linarith [Real.exp_pos (l * s)]
    have h3 : s ^ (2 * K) = |s| ^ (2 * K) := by
      rw [pow_mul, pow_mul, sq_abs]
    rw [mul_pow, div_le_iff₀ hfac] at h1
    have hlp : 0 < l ^ (2 * K) := by positivity
    have h4 : |s| ^ (2 * K) ≤ Real.exp (l * |s|) * ((2 * K).factorial : ℝ) * (l ^ (2 * K))⁻¹ := by
      rw [le_mul_inv_iff₀ hlp, mul_comm]
      exact h1
    rw [h3]
    refine h4.trans ?_
    have h5 : 0 ≤ ((2 * K).factorial : ℝ) * (l ^ (2 * K))⁻¹ := by positivity
    calc Real.exp (l * |s|) * ((2 * K).factorial : ℝ) * (l ^ (2 * K))⁻¹
        = ((2 * K).factorial : ℝ) * (l ^ (2 * K))⁻¹ * Real.exp (l * |s|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 h5
  have hI : Integrable (fun ω => Real.exp (l * modelField w P ω) +
      Real.exp (-l * modelField w P ω)) steinhausMeasure := (hbd l).add (hbd (-l))
  have hle := integral_mono (integrable_modelField_pow hw P (2 * K)) (hI.const_mul _) hpt
  rw [integral_const_mul, integral_add (hbd l) (hbd (-l))] at hle
  refine hle.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have h1 := integral_exp_modelField_le_sharp (w := w) hP l
  have h2 := integral_exp_modelField_le_sharp (w := w) hP (-l)
  rw [neg_sq] at h2
  linarith

/-- Stirling's upper bound in the form `K! ≤ e K (K/e)^K`. -/
theorem factorial_le_stirling {K : ℕ} (hK : 1 ≤ K) :
    (K.factorial : ℝ) ≤ Real.exp 1 * K * ((K : ℝ) / Real.exp 1) ^ K := by
  induction K, hK using Nat.le_induction with
  | base =>
    simp only [Nat.factorial_one, Nat.cast_one, mul_one, pow_one]
    rw [mul_one_div_cancel (Real.exp_pos 1).ne']
  | succ K hK ih =>
    have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
    have he : 0 < Real.exp 1 := Real.exp_pos 1
    rw [Nat.factorial_succ]
    push_cast
    -- `e ≤ (1 + 1/K)^{K+1}`
    have hz : Real.exp (1 / ((K : ℝ) + 1)) ≤ ((K : ℝ) + 1) / K := by
      have h1 := Real.add_one_le_exp (-(1 / ((K : ℝ) + 1)))
      have h2 : 0 < -(1 / ((K : ℝ) + 1)) + 1 := by
        have : (1 : ℝ) / ((K : ℝ) + 1) < 1 := by
          rw [div_lt_one (by positivity)]
          linarith
        linarith
      rw [Real.exp_neg] at h1
      have h3 : -(1 / ((K : ℝ) + 1)) + 1 = K / ((K : ℝ) + 1) := by
        field_simp
        ring
      rw [h3] at h1 h2
      have h4 := inv_anti₀ h2 h1
      rwa [inv_inv, inv_div] at h4
    have hpow : Real.exp 1 ≤ (((K : ℝ) + 1) / K) ^ (K + 1) := by
      have h1 : Real.exp (1 / ((K : ℝ) + 1)) ^ (K + 1) = Real.exp 1 := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        field_simp
      rw [← h1]
      exact pow_le_pow_left₀ (Real.exp_pos _).le hz _
    have hkey : (K : ℝ) * ((K : ℝ) / Real.exp 1) ^ K ≤ (((K : ℝ) + 1) / Real.exp 1) ^ (K + 1) := by
      have e1 : (((K : ℝ) + 1) / Real.exp 1) ^ (K + 1) =
          (((K : ℝ) + 1) / K) ^ (K + 1) * ((K : ℝ) / Real.exp 1) ^ (K + 1) := by
        rw [← mul_pow]
        congr 1
        field_simp
      rw [e1, pow_succ ((K : ℝ) / Real.exp 1) K]
      have h0 : 0 ≤ ((K : ℝ) / Real.exp 1) ^ K := by positivity
      have h2 : (K : ℝ) = Real.exp 1 * ((K : ℝ) / Real.exp 1) := by field_simp
      calc (K : ℝ) * ((K : ℝ) / Real.exp 1) ^ K
          = Real.exp 1 * (((K : ℝ) / Real.exp 1) ^ K * ((K : ℝ) / Real.exp 1)) := by
            nth_rewrite 1 [h2]
            ring
        _ ≤ (((K : ℝ) + 1) / K) ^ (K + 1) * (((K : ℝ) / Real.exp 1) ^ K * ((K : ℝ) / Real.exp 1)) :=
            mul_le_mul_of_nonneg_right hpow (by positivity)
    calc ((K : ℝ) + 1) * (K.factorial : ℝ)
        ≤ ((K : ℝ) + 1) * (Real.exp 1 * K * ((K : ℝ) / Real.exp 1) ^ K) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
      _ = Real.exp 1 * ((K : ℝ) + 1) * ((K : ℝ) * ((K : ℝ) / Real.exp 1) ^ K) := by ring
      _ ≤ Real.exp 1 * ((K : ℝ) + 1) * (((K : ℝ) + 1) / Real.exp 1) ^ (K + 1) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)

/-- `(2K)! ≤ e² K² (4K²/e²)^K`. -/
theorem two_mul_factorial_le {K : ℕ} (hK : 1 ≤ K) :
    ((2 * K).factorial : ℝ) ≤
      Real.exp 2 * (K : ℝ) ^ 2 * (4 * (K : ℝ) ^ 2 / Real.exp 2) ^ K := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hch := Nat.choose_mul_factorial_mul_factorial (show K ≤ 2 * K by omega)
  rw [show 2 * K - K = K by omega] at hch
  have hc : (((2 * K).choose K : ℕ) : ℝ) ≤ 4 ^ K := by
    have h := Nat.choose_le_two_pow (2 * K) K
    have h2 : ((2 : ℕ) ^ (2 * K) : ℕ) = 4 ^ K := by
      rw [pow_mul]
      norm_num
    rw [h2] at h
    exact_mod_cast h
  have hS := factorial_le_stirling hK
  have hfac0 : (0 : ℝ) ≤ (K.factorial : ℝ) := Nat.cast_nonneg _
  have heq : ((2 * K).factorial : ℝ) = (((2 * K).choose K : ℕ) : ℝ) * (K.factorial : ℝ) ^ 2 := by
    rw [← hch]
    push_cast
    ring
  rw [heq]
  have hsq : (K.factorial : ℝ) ^ 2 ≤ (Real.exp 1 * K * ((K : ℝ) / Real.exp 1) ^ K) ^ 2 :=
    pow_le_pow_left₀ hfac0 hS 2
  have he2 : Real.exp 2 = Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul]
    norm_num
  calc (((2 * K).choose K : ℕ) : ℝ) * (K.factorial : ℝ) ^ 2
      ≤ 4 ^ K * (Real.exp 1 * K * ((K : ℝ) / Real.exp 1) ^ K) ^ 2 :=
        mul_le_mul hc hsq (by positivity) (by positivity)
    _ = _ := by
        have h3 : (4 * (K : ℝ) ^ 2 / Real.exp 1 ^ 2) ^ K = 4 ^ K * (((K : ℝ) / Real.exp 1) ^ K) ^ 2 := by
          rw [show 4 * (K : ℝ) ^ 2 / Real.exp 1 ^ 2 = 4 * ((K : ℝ) / Real.exp 1) ^ 2 by
            rw [div_pow]
            ring, mul_pow, ← pow_mul, ← pow_mul, mul_comm K 2]
        rw [he2, h3]
        ring

/-- The arithmetic of the moment tail at order `K`, level `λ² ≥ K W`. -/
theorem moment_tail_le {K : ℕ} {W lam : ℝ} (hK : 1 ≤ K) (hW : 0 < W) (hlam : 0 < lam)
    (hKle : (K : ℝ) * W ≤ lam ^ 2) :
    ((2 * K).factorial : ℝ) * (W / (4 * K)) ^ K * (2 * Real.exp K) / lam ^ (2 * K) ≤
      2 * Real.exp 2 * (K : ℝ) ^ 2 * Real.exp (-(K : ℝ)) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have h2 := two_mul_factorial_le hK
  have hratio : W / (4 * K) / lam ^ 2 ≤ 1 / (4 * (K : ℝ) ^ 2) := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hpow : (W / (4 * K)) ^ K / lam ^ (2 * K) ≤ (1 / (4 * (K : ℝ) ^ 2)) ^ K := by
    rw [pow_mul, ← div_pow]
    exact pow_le_pow_left₀ (by positivity) hratio K
  have heK : Real.exp K * Real.exp (-(K : ℝ)) = 1 := by
    rw [← Real.exp_add]
    simp
  have he2 : Real.exp 2 ^ K = Real.exp (K : ℝ) * Real.exp (K : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  calc ((2 * K).factorial : ℝ) * (W / (4 * K)) ^ K * (2 * Real.exp K) / lam ^ (2 * K)
      = ((2 * K).factorial : ℝ) * ((W / (4 * K)) ^ K / lam ^ (2 * K)) * (2 * Real.exp K) := by
        ring
    _ ≤ (Real.exp 2 * (K : ℝ) ^ 2 * (4 * (K : ℝ) ^ 2 / Real.exp 2) ^ K) *
          (1 / (4 * (K : ℝ) ^ 2)) ^ K * (2 * Real.exp K) := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul h2 hpow (by positivity) (by positivity)) (by positivity)
    _ = 2 * Real.exp 2 * (K : ℝ) ^ 2 * Real.exp (-(K : ℝ)) := by
        have e : (4 * (K : ℝ) ^ 2 / Real.exp 2) ^ K * (1 / (4 * (K : ℝ) ^ 2)) ^ K =
            (Real.exp (K : ℝ) * Real.exp (K : ℝ))⁻¹ := by
          rw [← mul_pow, ← he2, ← inv_pow]
          congr 1
          field_simp
        have e2 : (Real.exp (K : ℝ) * Real.exp (K : ℝ))⁻¹ * Real.exp K = Real.exp (-(K : ℝ)) := by
          rw [Real.exp_neg]
          have := Real.exp_pos (K : ℝ)
          field_simp
        calc _ = 2 * Real.exp 2 * (K : ℝ) ^ 2 *
              (((4 * (K : ℝ) ^ 2 / Real.exp 2) ^ K * (1 / (4 * (K : ℝ) ^ 2)) ^ K) * Real.exp K) := by
              ring
          _ = _ := by rw [e, e2]

/-! ### The tail on heights -/

theorem continuous_primeField_pow (P : Finset ℕ) (j : ℕ) :
    Continuous fun t => primeField halfWeight P t ^ j :=
  (continuous_primeField halfWeight P).pow j

/-- **The Gaussian rate on heights.** For `K W ≤ λ²` and `λ ≥ 1`, the heights of `[T, 2T]` with
`|Σ_{p ≤ Y} p^{−1/2} cos(t log p)| ≥ λ` have measure at most `T 2e²K²e^{−K} + 2Y^{4K}`. -/
theorem volume_primeField_ge_le {T lam : ℝ} {Y K : ℕ} (hT : 0 < T) (hY1 : 1 ≤ Y) (hK : 1 ≤ K)
    (hW : 0 < Sieve.mertensS Y) (hKle : (K : ℝ) * Sieve.mertensS Y ≤ lam ^ 2) (hlam : 1 ≤ lam) :
    volume {t | t ∈ Icc T (2 * T) ∧ lam ≤ |primeField halfWeight (primesUpTo Y) t|} ≤
      ENNReal.ofReal (T * (2 * Real.exp 2 * (K : ℝ) ^ 2 * Real.exp (-(K : ℝ))) +
        2 * (Y : ℝ) ^ (4 * K)) := by
  have hlam0 : 0 < lam := by linarith
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = Sieve.mertensS Y := ⟨_, rfl⟩
  rw [← hWdef] at hW hKle
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, F = primeField halfWeight (primesUpTo Y) := ⟨_, rfl⟩
  rw [← hF]
  have hFc : Continuous fun t => F t ^ (2 * K) := hF ▸ continuous_primeField_pow _ _
  have hf0 : ∀ t, 0 ≤ F t ^ (2 * K) := fun t => by
    rw [pow_mul]
    positivity
  -- the moment on the model
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = Real.sqrt (4 * K / W) := ⟨_, rfl⟩
  have hl0 : 0 < l := by
    rw [hl]
    exact Real.sqrt_pos.mpr (by positivity)
  have hl2 : l ^ 2 = 4 * K / W := by
    rw [hl, Real.sq_sqrt (by positivity)]
  have hM := integral_modelField_even_pow_le_sharp (w := halfWeight) (P := primesUpTo Y)
    halfWeight_nonneg (fun p hp => prime_of_mem_primesUpTo hp) K hl0
  rw [sum_halfWeight_sq, ← hWdef, hl2] at hM
  have e1 : 4 * (K : ℝ) / W * W / 4 = K := by
    field_simp
  rw [e1] at hM
  have e2 : (l ^ (2 * K))⁻¹ = (W / (4 * K)) ^ K := by
    rw [pow_mul, hl2, ← inv_pow, inv_div]
  rw [e2] at hM
  -- the transfer
  have hP0 : ∀ p ∈ primesUpTo Y, p ≠ 0 := fun p hp => (prime_of_mem_primesUpTo hp).ne_zero
  have htrans := abs_mean_primeField_pow_sub_model_le halfWeight_nonneg hP0 hY1
    (fun p hp => le_of_mem_primesUpTo hp) hT (2 * K)
  rw [← hF] at htrans
  have hA : (∑ p ∈ primesUpTo Y, halfWeight p) * Y ≤ (Y : ℝ) ^ 2 := by
    rw [sq]
    exact mul_le_mul_of_nonneg_right (sum_halfWeight_le Y) (Nat.cast_nonneg _)
  have hA0 : 0 ≤ (∑ p ∈ primesUpTo Y, halfWeight p) * Y :=
    mul_nonneg (Finset.sum_nonneg fun p _ => halfWeight_nonneg p) (Nat.cast_nonneg _)
  have hA2 : ((∑ p ∈ primesUpTo Y, halfWeight p) * Y) ^ (2 * K) ≤ (Y : ℝ) ^ (4 * K) := by
    calc ((∑ p ∈ primesUpTo Y, halfWeight p) * Y) ^ (2 * K) ≤ ((Y : ℝ) ^ 2) ^ (2 * K) :=
          pow_le_pow_left₀ hA0 hA _
      _ = (Y : ℝ) ^ (4 * K) := by
          rw [← pow_mul]
          congr 1
          ring
  have hupper := (abs_le.mp htrans).2
  have hdiv : 2 * ((∑ p ∈ primesUpTo Y, halfWeight p) * Y) ^ (2 * K) / T ≤
      2 * (Y : ℝ) ^ (4 * K) / T := div_le_div_of_nonneg_right (by linarith) hT.le
  have hmean : T⁻¹ * ∫ t in T..(T + T), F t ^ (2 * K) ≤
      ((2 * K).factorial : ℝ) * (W / (4 * K)) ^ K * (2 * Real.exp K) +
        2 * (Y : ℝ) ^ (4 * K) / T := by
    linarith
  have hint : ∫ t in T..(2 * T), F t ^ (2 * K) ≤
      T * (((2 * K).factorial : ℝ) * (W / (4 * K)) ^ K * (2 * Real.exp K)) +
        2 * (Y : ℝ) ^ (4 * K) := by
    have h := mul_le_mul_of_nonneg_left hmean hT.le
    rw [← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul, mul_add,
      mul_div_cancel₀ _ hT.ne'] at h
    have e3 : 2 * T = T + T := two_mul T
    rw [e3]
    exact h
  have hc : 0 < lam ^ (2 * K) := by positivity
  have hV := volume_Icc_setOf_le_le_of_integral (show T ≤ 2 * T by linarith) hc hf0 hFc hint
  have hsub : {t | t ∈ Icc T (2 * T) ∧ lam ≤ |F t|} ⊆
      {t | t ∈ Icc T (2 * T) ∧ lam ^ (2 * K) ≤ F t ^ (2 * K)} := by
    rintro t ⟨ht, hle⟩
    refine ⟨ht, ?_⟩
    have h1 := pow_le_pow_left₀ hlam0.le hle (2 * K)
    rwa [pow_mul |F t|, sq_abs, ← pow_mul] at h1
  refine (measure_mono hsub).trans (hV.trans (ENNReal.ofReal_le_ofReal ?_))
  have hc1 : 1 ≤ lam ^ (2 * K) := one_le_pow₀ hlam
  have hY0 : 0 ≤ (Y : ℝ) ^ (4 * K) := by positivity
  have htail := moment_tail_le hK hW hlam0 hKle
  rw [add_div, mul_div_assoc]
  refine add_le_add (mul_le_mul_of_nonneg_left htail hT.le) ?_
  exact div_le_self (by positivity) hc1

/-! ### The barrier -/

/-- The doubly exponential cuts `y_j = ⌈exp(exp j)⌉`: each step adds reciprocal mass `≈ 1`. -/
def scaleCut (j : ℕ) : ℕ := ⌈Real.exp (Real.exp j)⌉₊

/-- The moment order `K_j = ⌈4 log(j + 2)⌉` at scale `j`. -/
def scaleOrder (j : ℕ) : ℕ := ⌈4 * Real.log ((j : ℝ) + 2)⌉₊

/-- The reciprocal mass of the walk at scale `j`. -/
def walkMass (j : ℕ) : ℝ := Sieve.mertensS (scaleCut j)

/-- The walk at scale `j`. -/
def primeWalkAt (j : ℕ) (t : ℝ) : ℝ := primeField halfWeight (primesUpTo (scaleCut j)) t

/-- The barrier `√(K_j W_j)` at scale `j`: the envelope `√(4 W_j log j)` of the walk. -/
def barrierLevel (j : ℕ) : ℝ := Real.sqrt ((scaleOrder j : ℝ) * walkMass j)

theorem two_le_scaleCut (j : ℕ) : 2 ≤ scaleCut j := by
  have h1 : (1 : ℝ) ≤ Real.exp j := Real.one_le_exp (Nat.cast_nonneg j)
  have h2 : (2 : ℝ) ≤ Real.exp (Real.exp j) := by
    have := Real.add_one_le_exp (Real.exp (j : ℝ))
    linarith
  have h3 := Nat.le_ceil (Real.exp (Real.exp (j : ℝ)))
  unfold scaleCut
  exact_mod_cast h2.trans h3

theorem half_le_walkMass (j : ℕ) : 1 / 2 ≤ walkMass j := by
  unfold walkMass
  rw [← sum_primesUpTo_inv]
  have hmem : 2 ∈ primesUpTo (scaleCut j) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by norm_num, two_le_scaleCut j⟩, Nat.prime_two⟩
  have h := Finset.single_le_sum (f := fun p : ℕ => 1 / (p : ℝ))
    (fun p _ => by positivity) hmem
  simpa using h

theorem three_le_scaleOrder (j : ℕ) : 3 ≤ scaleOrder j := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h1 : Real.log 2 ≤ Real.log ((j : ℝ) + 2) := Real.log_le_log (by norm_num) (by linarith)
  have h2 := Real.log_two_gt_d9
  have h3 : ((2 : ℕ) : ℝ) < 4 * Real.log ((j : ℝ) + 2) := by
    push_cast
    linarith
  exact Nat.lt_ceil.mpr h3

theorem one_le_barrierLevel (j : ℕ) : 1 ≤ barrierLevel j := by
  refine Real.one_le_sqrt.mpr ?_
  have h1 : (3 : ℝ) ≤ scaleOrder j := by exact_mod_cast three_le_scaleOrder j
  have h2 := half_le_walkMass j
  nlinarith

theorem barrierLevel_sq (j : ℕ) : barrierLevel j ^ 2 = (scaleOrder j : ℝ) * walkMass j := by
  unfold barrierLevel
  refine Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) ?_)
  have := half_le_walkMass j
  linarith

/-- `K² e^{−K} ≤ 16 e^{−K/2}`. -/
theorem sq_mul_exp_neg_le {K : ℝ} (hK : 0 ≤ K) : K ^ 2 * Real.exp (-K) ≤ 16 * Real.exp (-(K / 2)) := by
  have h1 : K / 4 ≤ Real.exp (K / 4) := by
    have := Real.add_one_le_exp (K / 4)
    linarith
  have h2 : (K / 4) ^ 2 ≤ Real.exp (K / 4) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  have h3 : Real.exp (K / 4) ^ 2 = Real.exp (K / 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h3] at h2
  have e : Real.exp (-(K / 2)) = Real.exp (K / 2) * Real.exp (-K) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [e]
  have hpos := Real.exp_pos (-K)
  nlinarith

theorem exp_neg_half_scaleOrder_le (j : ℕ) :
    Real.exp (-((scaleOrder j : ℝ) / 2)) ≤ 1 / ((j : ℝ) + 2) ^ 2 := by
  have hj : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  have h1 : 4 * Real.log ((j : ℝ) + 2) ≤ scaleOrder j := Nat.le_ceil _
  have e : 1 / ((j : ℝ) + 2) ^ 2 = Real.exp (-(2 * Real.log ((j : ℝ) + 2))) := by
    rw [Real.exp_neg, mul_comm, Real.exp_mul, Real.exp_log hj, one_div]
    norm_num
  rw [e]
  exact Real.exp_le_exp.mpr (by linarith)

/-- Telescoping for the barrier series. -/
theorem sum_Icc_inv_sq_le (j₀ J : ℕ) :
    ∑ j ∈ Finset.Icc j₀ J, 1 / ((j : ℝ) + 2) ^ 2 ≤ 1 / ((j₀ : ℝ) + 1) := by
  have hkey : ∀ n : ℕ, ∑ j ∈ Finset.Icc j₀ (j₀ + n), 1 / ((j : ℝ) + 2) ^ 2 ≤
      1 / ((j₀ : ℝ) + 1) - 1 / (((j₀ + n : ℕ) : ℝ) + 2) := by
    intro n
    induction n with
    | zero =>
      simp only [add_zero, Finset.Icc_self, Finset.sum_singleton]
      have hj : (0 : ℝ) ≤ j₀ := Nat.cast_nonneg j₀
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    | succ n ih =>
      rw [show j₀ + (n + 1) = (j₀ + n) + 1 by ring, Finset.sum_Icc_succ_top (by omega)]
      push_cast at ih ⊢
      have hj : (0 : ℝ) ≤ (j₀ : ℝ) + n := by positivity
      have hstep : 1 / ((j₀ : ℝ) + n + 1 + 2) ^ 2 ≤
          1 / ((j₀ : ℝ) + n + 2) - 1 / ((j₀ : ℝ) + n + 1 + 2) := by
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith
      linarith
  have h0 : (0 : ℝ) ≤ 1 / ((j₀ : ℝ) + 1) := by positivity
  rcases le_or_gt j₀ J with h | h
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
    have h1 := hkey n
    have h2 : (0 : ℝ) ≤ 1 / (((j₀ + n : ℕ) : ℝ) + 2) := by positivity
    linarith
  · rw [Finset.Icc_eq_empty (by omega)]
    simpa using h0

/-- **The barrier.** The heights of `[T, 2T]` where the prime walk crosses its envelope
`√(K_j W_j) ≈ √(4 W_j log j)` at some scale `j₀ ≤ j ≤ J` have measure at most
`256 T/j₀ + Σ_j 2 y_j^{4K_j}`, uniformly in `T`. -/
theorem volume_barrier_crossing_le {T : ℝ} (hT : 0 < T) {j₀ : ℕ} (hj₀ : 1 ≤ j₀) (J : ℕ) :
    volume {t | t ∈ Icc T (2 * T) ∧ ∃ j ∈ Finset.Icc j₀ J, barrierLevel j ≤ |primeWalkAt j t|} ≤
      ENNReal.ofReal (T * (256 / (j₀ : ℝ)) +
        ∑ j ∈ Finset.Icc j₀ J, 2 * (scaleCut j : ℝ) ^ (4 * scaleOrder j)) := by
  have hsub : {t | t ∈ Icc T (2 * T) ∧ ∃ j ∈ Finset.Icc j₀ J, barrierLevel j ≤ |primeWalkAt j t|} ⊆
      ⋃ j ∈ Finset.Icc j₀ J, {t | t ∈ Icc T (2 * T) ∧
        barrierLevel j ≤ |primeField halfWeight (primesUpTo (scaleCut j)) t|} := by
    rintro t ⟨ht, j, hj, hle⟩
    exact mem_iUnion₂.mpr ⟨j, hj, ht, hle⟩
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hone : ∀ j ∈ Finset.Icc j₀ J, volume {t | t ∈ Icc T (2 * T) ∧
      barrierLevel j ≤ |primeField halfWeight (primesUpTo (scaleCut j)) t|} ≤
      ENNReal.ofReal (T * (256 * (1 / ((j : ℝ) + 2) ^ 2)) + 2 * (scaleCut j : ℝ) ^ (4 * scaleOrder j)) := by
    intro j _
    have hK3 := three_le_scaleOrder j
    have hW := half_le_walkMass j
    have hV := volume_primeField_ge_le (T := T) (lam := barrierLevel j) (Y := scaleCut j)
      (K := scaleOrder j) hT (by have := two_le_scaleCut j; omega) (by omega)
      (by
        unfold walkMass at hW
        linarith)
      (by
        rw [barrierLevel_sq]
        exact le_rfl)
      (one_le_barrierLevel j)
    refine hV.trans (ENNReal.ofReal_le_ofReal ?_)
    refine add_le_add (mul_le_mul_of_nonneg_left ?_ hT.le) le_rfl
    have hK0 : (0 : ℝ) ≤ scaleOrder j := Nat.cast_nonneg _
    have h1 := sq_mul_exp_neg_le hK0
    have h2 := exp_neg_half_scaleOrder_le j
    have he2 : Real.exp 2 ≤ 8 := by
      have h3 : Real.exp 2 = Real.exp 1 ^ 2 := by
        rw [← Real.exp_nat_mul]
        norm_num
      have h4 := Real.exp_one_lt_d9
      have h5 := Real.exp_pos 1
      rw [h3]
      nlinarith
    have he0 := Real.exp_pos 2
    have hnn : 0 ≤ (scaleOrder j : ℝ) ^ 2 * Real.exp (-(scaleOrder j : ℝ)) := by positivity
    have hinv : 0 ≤ 1 / ((j : ℝ) + 2) ^ 2 := by positivity
    calc 2 * Real.exp 2 * (scaleOrder j : ℝ) ^ 2 * Real.exp (-(scaleOrder j : ℝ))
        = 2 * Real.exp 2 * ((scaleOrder j : ℝ) ^ 2 * Real.exp (-(scaleOrder j : ℝ))) := by ring
      _ ≤ 2 * 8 * (16 * (1 / ((j : ℝ) + 2) ^ 2)) := by
          refine mul_le_mul (by linarith) (h1.trans ?_) hnn (by norm_num)
          exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = _ := by ring
  refine (Finset.sum_le_sum hone).trans ?_
  have hnn : ∀ j ∈ Finset.Icc j₀ J, 0 ≤ T * (256 * (1 / ((j : ℝ) + 2) ^ 2)) +
      2 * (scaleCut j : ℝ) ^ (4 * scaleOrder j) := fun j _ => by positivity
  rw [← ENNReal.ofReal_sum_of_nonneg hnn]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  refine add_le_add (mul_le_mul_of_nonneg_left ?_ hT.le) le_rfl
  have hj0 : (0 : ℝ) < j₀ := by exact_mod_cast hj₀
  have h1 := sum_Icc_inv_sq_le j₀ J
  have h2 : 1 / ((j₀ : ℝ) + 1) ≤ 1 / (j₀ : ℝ) :=
    one_div_le_one_div_of_le hj0 (by linarith)
  calc 256 * ∑ j ∈ Finset.Icc j₀ J, 1 / ((j : ℝ) + 2) ^ 2 ≤ 256 * (1 / (j₀ : ℝ)) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (by norm_num)
    _ = _ := by ring

/-! ### The dyadic decomposition -/

theorem scaleCut_mono : Monotone scaleCut := by
  intro a b hab
  refine Nat.ceil_mono (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr ?_))
  exact_mod_cast hab

/-- The increment of the walk is the field of the primes in the block `(y_j, y_{j+1}]`. -/
theorem primeWalkAt_succ_sub (j : ℕ) (t : ℝ) :
    primeWalkAt (j + 1) t - primeWalkAt j t =
      primeField halfWeight (primesUpTo (scaleCut (j + 1)) \ primesUpTo (scaleCut j)) t := by
  have hsub : primesUpTo (scaleCut j) ⊆ primesUpTo (scaleCut (j + 1)) := by
    intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hp
    obtain ⟨h3, h4⟩ := Finset.mem_Icc.mp h1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨h3, h4.trans (scaleCut_mono (Nat.le_succ j))⟩, h2⟩
  unfold primeWalkAt primeField
  rw [← Finset.sum_sdiff hsub]
  ring

/-- `0 ≤ log log y_j − j ≤ e^{−j}`. -/
theorem logLog_scaleCut_sub_le (j : ℕ) :
    (j : ℝ) ≤ Real.log (Real.log (scaleCut j)) ∧
      Real.log (Real.log (scaleCut j)) ≤ j + Real.exp (-(j : ℝ)) := by
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = Real.exp (Real.exp (j : ℝ)) := ⟨_, rfl⟩
  have hy1 : 1 ≤ y := by
    rw [hy]
    exact Real.one_le_exp (Real.exp_pos _).le
  have hc1 : y ≤ scaleCut j := by
    unfold scaleCut
    rw [← hy]
    exact Nat.le_ceil y
  have hc2 : (scaleCut j : ℝ) ≤ y + 1 := by
    unfold scaleCut
    rw [← hy]
    exact (Nat.ceil_lt_add_one (by linarith)).le
  have hlogy : Real.log y = Real.exp (j : ℝ) := by rw [hy, Real.log_exp]
  have hejpos := Real.exp_pos (j : ℝ)
  have hlow : Real.exp (j : ℝ) ≤ Real.log (scaleCut j) := by
    rw [← hlogy]
    exact Real.log_le_log (by linarith) hc1
  have hup : Real.log (scaleCut j) ≤ Real.exp (j : ℝ) + Real.exp (j : ℝ) * Real.exp (-(j : ℝ)) := by
    have e : Real.exp (j : ℝ) * Real.exp (-(j : ℝ)) = 1 := by
      rw [← Real.exp_add]
      simp
    rw [e]
    have h1 := Real.log_le_log (by linarith [hc1, hy1] : 0 < (scaleCut j : ℝ)) hc2
    have h2 : Real.log (y + 1) ≤ Real.log y + 1 := by
      have h3 : Real.log (y + 1) ≤ Real.log (y * Real.exp 1) := by
        refine Real.log_le_log (by linarith) ?_
        have := Real.add_one_le_exp (1 : ℝ)
        nlinarith
      rw [Real.log_mul (by linarith) (Real.exp_pos 1).ne', Real.log_exp] at h3
      exact h3
    rw [← hlogy]
    linarith
  constructor
  · have := Real.log_le_log hejpos hlow
    rwa [Real.log_exp] at this
  · have h1 := Real.log_le_log (lt_of_lt_of_le hejpos hlow) hup
    have e : Real.exp (j : ℝ) + Real.exp (j : ℝ) * Real.exp (-(j : ℝ)) =
        Real.exp (j : ℝ) * (1 + Real.exp (-(j : ℝ))) := by ring
    rw [e, Real.log_mul hejpos.ne' (by positivity), Real.log_exp] at h1
    have h2 := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.exp (-(j : ℝ)) by positivity)
    linarith

/-- **The dyadic decomposition.** Each block `(y_j, y_{j+1}]` carries reciprocal mass
`1 + O(e^{−j})`. -/
theorem exists_abs_walkMass_succ_sub_le :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, |walkMass (j + 1) - walkMass j - 1| ≤ C * Real.exp (-(j : ℝ)) := by
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = 2 * Sieve.mertensFirstConst + 1 / 2 := ⟨_, rfl⟩
  have hC'0 : 0 ≤ C' := by
    rw [hC']
    have := Sieve.mertensFirstConst_nonneg
    linarith
  refine ⟨2 * C' + 2, by positivity, fun j => ?_⟩
  have hone : ∀ i : ℕ, |walkMass i - Real.log (Real.log (scaleCut i)) - Sieve.meisselMertensConst| ≤
      C' * Real.exp (-(i : ℝ)) := by
    intro i
    have h := Sieve.abs_mertensS_sub_logLog_sub_const_le (two_le_scaleCut i)
    unfold Sieve.logLog at h
    unfold walkMass
    rw [← hC'] at h
    refine h.trans ?_
    rw [div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ hC'0
    obtain ⟨hl, -⟩ := logLog_scaleCut_sub_le i
    have hlog0 : 0 < Real.log (scaleCut i) := by
      have h2 : (1 : ℝ) < scaleCut i := by
        have := two_le_scaleCut i
        exact_mod_cast (show 1 < scaleCut i by omega)
      exact Real.log_pos h2
    rw [Real.exp_neg]
    refine inv_anti₀ (Real.exp_pos _) ?_
    have := Real.exp_le_exp.mpr hl
    rwa [Real.exp_log hlog0] at this
  have h1 := abs_le.mp (hone j)
  have h2 := abs_le.mp (hone (j + 1))
  obtain ⟨h3, h4⟩ := logLog_scaleCut_sub_le j
  obtain ⟨h5, h6⟩ := logLog_scaleCut_sub_le (j + 1)
  have hE : Real.exp (-((j + 1 : ℕ) : ℝ)) ≤ Real.exp (-(j : ℝ)) :=
    Real.exp_le_exp.mpr (by push_cast; linarith)
  have hE0 := Real.exp_pos (-(j : ℝ))
  have hE1 := Real.exp_pos (-((j + 1 : ℕ) : ℝ))
  have hC1 : C' * Real.exp (-((j + 1 : ℕ) : ℝ)) ≤ C' * Real.exp (-(j : ℝ)) :=
    mul_le_mul_of_nonneg_left hE hC'0
  push_cast at h5 h6 hE hE1 hC1 h2
  rw [abs_le]
  constructor <;> nlinarith

end GaloisForLFunctions.MultiscaleMollifiedZetaField
