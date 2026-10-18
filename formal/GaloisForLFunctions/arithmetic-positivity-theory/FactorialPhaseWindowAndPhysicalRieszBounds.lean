import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialPhaseHarmonicLayers

/-! Uniform window coercivity, weighted bounds, and physical Riesz bounds for the factorial
correction phases.

Let `B_b = ∑_{n ∈ S} b_n Φ_{n+1}` and `S_b = ∑ ‖b_n‖²`. The harmonic expansion
`-(π²/2) B_b = ∑_k w_k H_k` (`w_1 = 1`, `∑_{k ≥ 2} |w_k| ≤ 3/4`, `∑_k |w_k| ≤ 7/4`) together with
the Montgomery–Vaughan layer bounds gives:
1. on every window of length `L = 16 K` (`K = 390/π`),
   `∫_a^{a+L} ‖B_b‖² ≥ (L / (16 π⁴)) S_b`, via the pointwise dominance
   `‖x + y‖² ≥ (1 - θ)‖x‖² - (1/θ - 1)‖y‖²` with `θ = 4/5` and weighted Cauchy–Schwarz on the
   higher layers;
2. for every dilation `r ≥ 1` and window length `ℓ ≥ 0`,
   `∫_a^{a+ℓ} ‖B_b(r v)‖² ≤ (49/(4π⁴)) (ℓ + K) S_b`;
3. `A S_b ≤ ∫_1^∞ v^{-4} ‖B_b(v)‖² dv` and `∫_1^∞ v^{-4} ‖B_b(r v)‖² dv ≤ B S_b` for `r ≥ 1`,
   by restriction to `[1, 1 + L]` and by summing unit intervals with `∑ j^{-4} ≤ 4/3`;
4. under the clock substitution `v = e^{-x}`, a finite combination `∑ c_n T_n` of literal
   correction tails has physical square mass `∫_1^∞ v^{-4} ‖B_b(v)‖² dv` with `b_n = c_n a_n`,
   hence `144 A ∑ |c_n|²/(n+1) ≤ ∫_ℝ |∑ c_n T_n|² ≤ 225 B ∑ |c_n|²/(n+1)`. -/

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-- Weighted Cauchy–Schwarz for an absolutely summable weight sequence and bounded vectors:
`‖∑' w_k z_k‖² ≤ (∑' |w_k|) (∑' |w_k| ‖z_k‖²)`. -/
theorem norm_tsum_weighted_sq_le {w : ℕ → ℝ} {z : ℕ → ℂ} (hw : Summable fun k => |w k|)
    {C : ℝ} (hz : ∀ k, ‖z k‖ ≤ C) :
    ‖∑' k, (w k : ℂ) * z k‖ ^ 2 ≤ (∑' k, |w k|) * ∑' k, |w k| * ‖z k‖ ^ 2 := by
  have hs1 : Summable fun k => |w k| * ‖z k‖ :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) (norm_nonneg _))
      (fun k => mul_le_mul_of_nonneg_left (hz k) (abs_nonneg _)) (hw.mul_right C)
  have hs2 : Summable fun k => |w k| * ‖z k‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) (sq_nonneg _))
      (fun k => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hz k) 2)
        (abs_nonneg _)) (hw.mul_right (C ^ 2))
  have hnorm : ‖∑' k, (w k : ℂ) * z k‖ ≤ ∑' k, |w k| * ‖z k‖ := by
    have he : (fun k => ‖(w k : ℂ) * z k‖) = fun k => |w k| * ‖z k‖ := by
      funext k
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine (norm_tsum_le_tsum_norm ?_).trans_eq ?_
    · rw [he]
      exact hs1
    · rw [he]
  have hcs : (∑' k, |w k| * ‖z k‖) ^ 2 ≤ (∑' k, |w k|) * ∑' k, |w k| * ‖z k‖ ^ 2 := by
    refine le_of_tendsto_of_tendsto' (hs1.hasSum.tendsto_sum_nat.pow 2)
      (hw.hasSum.tendsto_sum_nat.mul hs2.hasSum.tendsto_sum_nat) fun n => ?_
    exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range n)
      (fun k _ => abs_nonneg _) (fun k _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
      (fun k _ => le_of_eq (by ring))
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hcs

/-- Integrating the weighted Cauchy–Schwarz bound over a finite measure:
`∫ ‖∑' w_k H_k‖² ≤ (∑' |w_k|) ∑' |w_k| ∫ ‖H_k‖²` for continuous uniformly bounded layers. -/
theorem integral_norm_tsum_weighted_sq_le {μ : Measure ℝ} [IsFiniteMeasure μ]
    {H : ℕ → ℝ → ℂ} {w : ℕ → ℝ} (hw : Summable fun k => |w k|)
    (hHc : ∀ k, Continuous (H k)) {C : ℝ} (hHb : ∀ k v, ‖H k v‖ ≤ C) :
    Integrable (fun v => ‖∑' k, (w k : ℂ) * H k v‖ ^ 2) μ ∧
    (∫ v, ‖∑' k, (w k : ℂ) * H k v‖ ^ 2 ∂μ) ≤
      (∑' k, |w k|) * ∑' k, |w k| * ∫ v, ‖H k v‖ ^ 2 ∂μ := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hHb 0 0)
  have hFc : Continuous fun v => ∑' k, (w k : ℂ) * H k v := by
    refine continuous_tsum (fun k => continuous_const.mul (hHc k)) (hw.mul_right C)
      fun k v => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hHb k v) (abs_nonneg _)
  have hFb : ∀ v, ‖∑' k, (w k : ℂ) * H k v‖ ≤ (∑' k, |w k|) * C := by
    intro v
    have hs : Summable fun k => ‖(w k : ℂ) * H k v‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hHb k v) (abs_nonneg _)) (hw.mul_right C)
    refine (norm_tsum_le_tsum_norm hs).trans ?_
    rw [← tsum_mul_right]
    exact hs.tsum_le_tsum (fun k => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hHb k v) (abs_nonneg _)) (hw.mul_right C)
  have hint : Integrable (fun v => ‖∑' k, (w k : ℂ) * H k v‖ ^ 2) μ := by
    refine Integrable.of_bound ((hFc.norm.pow 2).aestronglyMeasurable)
      (((∑' k, |w k|) * C) ^ 2) (Eventually.of_forall fun v => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hFb v) 2
  refine ⟨hint, ?_⟩
  have hGi (k : ℕ) : Integrable (fun v => |w k| * ‖H k v‖ ^ 2) μ := by
    refine Integrable.of_bound ((continuous_const.mul ((hHc k).norm.pow 2)).aestronglyMeasurable)
      (|w k| * C ^ 2) (Eventually.of_forall fun v => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hHb k v) 2)
      (abs_nonneg _)
  have hGs : Summable fun k => ∫ v, ‖|w k| * ‖H k v‖ ^ 2‖ ∂μ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _)
      (fun k => ?_) (hw.mul_right (C ^ 2 * μ.real univ))
    calc (∫ v, ‖|w k| * ‖H k v‖ ^ 2‖ ∂μ) ≤ ∫ _v, |w k| * C ^ 2 ∂μ := by
          refine integral_mono (hGi k).norm (integrable_const _) fun v => ?_
          rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hHb k v) 2)
            (abs_nonneg _)
      _ = |w k| * (C ^ 2 * μ.real univ) := by
          rw [integral_const, smul_eq_mul]
          ring
  have hswap := integral_tsum_of_summable_integral_norm hGi hGs
  have hpt : ∀ v, ‖∑' k, (w k : ℂ) * H k v‖ ^ 2 ≤
      (∑' k, |w k|) * ∑' k, |w k| * ‖H k v‖ ^ 2 := fun v =>
    norm_tsum_weighted_sq_le hw (hHb · v)
  have hsumi : Integrable (fun v => ∑' k, |w k| * ‖H k v‖ ^ 2) μ := by
    refine Integrable.of_bound ?_ ((∑' k, |w k|) * C ^ 2) (Eventually.of_forall fun v => ?_)
    · refine (continuous_tsum (fun k => continuous_const.mul ((hHc k).norm.pow 2))
        (hw.mul_right (C ^ 2)) fun k v => ?_).aestronglyMeasurable
      show ‖|w k| * ‖H k v‖ ^ 2‖ ≤ |w k| * C ^ 2
      rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hHb k v) 2)
        (abs_nonneg _)
    · have hs : Summable fun k => |w k| * ‖H k v‖ ^ 2 :=
        Summable.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) (sq_nonneg _))
          (fun k => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hHb k v) 2)
            (abs_nonneg _)) (hw.mul_right (C ^ 2))
      rw [Real.norm_of_nonneg (tsum_nonneg fun k => mul_nonneg (abs_nonneg _) (sq_nonneg _)),
        ← tsum_mul_right]
      exact hs.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hHb k v) 2) (abs_nonneg _)) (hw.mul_right (C ^ 2))
  calc (∫ v, ‖∑' k, (w k : ℂ) * H k v‖ ^ 2 ∂μ) ≤
        ∫ v, (∑' k, |w k|) * ∑' k, |w k| * ‖H k v‖ ^ 2 ∂μ :=
        integral_mono hint (hsumi.const_mul _) hpt
    _ = (∑' k, |w k|) * ∑' k, |w k| * ∫ v, ‖H k v‖ ^ 2 ∂μ := by
        rw [integral_const_mul, ← hswap]
        congr 1
        refine tsum_congr fun k => ?_
        rw [integral_const_mul]

/-- Pointwise dominance: `‖x + y‖² ≥ (1 - θ)‖x‖² - (1/θ - 1)‖y‖²` for every `θ > 0`. -/
theorem norm_add_sq_ge_dominance (x y : ℂ) {θ : ℝ} (hθ : 0 < θ) :
    (1 - θ) * ‖x‖ ^ 2 - (1 / θ - 1) * ‖y‖ ^ 2 ≤ ‖x + y‖ ^ 2 := by
  have h1 : |‖x‖ - ‖y‖| ≤ ‖x + y‖ := by
    have h := abs_norm_sub_norm_le x (-y)
    rwa [norm_neg, sub_neg_eq_add] at h
  have h2 : (‖x‖ - ‖y‖) ^ 2 ≤ ‖x + y‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have key : θ * ((‖x‖ - ‖y‖) ^ 2 - ((1 - θ) * ‖x‖ ^ 2 - (1 / θ - 1) * ‖y‖ ^ 2)) =
      (θ * ‖x‖ - ‖y‖) ^ 2 := by
    field_simp
    ring
  have h3 : 0 ≤ (‖x‖ - ‖y‖) ^ 2 - ((1 - θ) * ‖x‖ ^ 2 - (1 / θ - 1) * ‖y‖ ^ 2) := by
    by_contra hneg
    push Not at hneg
    have hm := mul_neg_of_pos_of_neg hθ hneg
    rw [key] at hm
    linarith [sq_nonneg (θ * ‖x‖ - ‖y‖)]
  linarith

/-- **First-harmonic dominance in mean square.** If `F = ∑_k w_k H_k` with `w_0 = 0`, `w_1 = 1`,
`∑_{k ≥ 2} |w_k| ≤ τ`, `∫ ‖H_1‖² ≥ α`, and `∫ ‖H_k‖² ≤ β` for `k ≥ 2`, then for `0 < θ ≤ 1`,
`∫ ‖F‖² ≥ (1 - θ) α - (1/θ - 1) τ² β`. -/
theorem integral_norm_sq_ge_of_first_harmonic {μ : Measure ℝ} [IsFiniteMeasure μ]
    {H : ℕ → ℝ → ℂ} {w : ℕ → ℝ} {F : ℝ → ℂ} {C τ α β θ : ℝ}
    (hF : ∀ v, HasSum (fun k => (w k : ℂ) * H k v) (F v))
    (hw : Summable fun k => |w k|) (hw0 : w 0 = 0) (hw1 : w 1 = 1)
    (htail : ∑' k, |w (k + 2)| ≤ τ)
    (hHc : ∀ k, Continuous (H k)) (hHb : ∀ k v, ‖H k v‖ ≤ C)
    (h1 : α ≤ ∫ v, ‖H 1 v‖ ^ 2 ∂μ) (hk : ∀ k, 2 ≤ k → ∫ v, ‖H k v‖ ^ 2 ∂μ ≤ β)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    (1 - θ) * α - (1 / θ - 1) * τ ^ 2 * β ≤ ∫ v, ‖F v‖ ^ 2 ∂μ := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hHb 0 0)
  have hw2 : Summable fun k => |w (k + 2)| := (summable_nat_add_iff 2).mpr hw
  have hτ : 0 ≤ τ := (tsum_nonneg fun _ => abs_nonneg _).trans htail
  have hβ : 0 ≤ β := (integral_nonneg fun _ => sq_nonneg _).trans (hk 2 le_rfl)
  set R : ℝ → ℂ := fun v => ∑' k, (w (k + 2) : ℂ) * H (k + 2) v with hR
  have hFeq : ∀ v, F v = H 1 v + R v := by
    intro v
    have hs := (hF v).summable
    rw [← (hF v).tsum_eq, hs.tsum_eq_zero_add,
      ((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add]
    simp only [hw0, hw1, Complex.ofReal_zero, Complex.ofReal_one, zero_mul, one_mul, zero_add]
    rfl
  obtain ⟨hFi, -⟩ := integral_norm_tsum_weighted_sq_le (μ := μ) hw hHc hHb
  obtain ⟨hRi, hRle⟩ := integral_norm_tsum_weighted_sq_le (μ := μ) (H := fun k => H (k + 2))
    hw2 (fun k => hHc (k + 2)) (fun k => hHb (k + 2))
  have hFi' : Integrable (fun v => ‖F v‖ ^ 2) μ := by
    refine hFi.congr (Eventually.of_forall fun v => ?_)
    simp only [(hF v).tsum_eq]
  have hH1i : Integrable (fun v => ‖H 1 v‖ ^ 2) μ := by
    refine Integrable.of_bound ((hHc 1).norm.pow 2).aestronglyMeasurable (C ^ 2)
      (Eventually.of_forall fun v => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hHb 1 v) 2
  have hsum_le : (∑' k, |w (k + 2)| * ∫ v, ‖H (k + 2) v‖ ^ 2 ∂μ) ≤ τ * β := by
    have hs : Summable fun k => |w (k + 2)| * ∫ v, ‖H (k + 2) v‖ ^ 2 ∂μ :=
      Summable.of_nonneg_of_le
        (fun k => mul_nonneg (abs_nonneg _) (integral_nonneg fun _ => sq_nonneg _))
        (fun k => mul_le_mul_of_nonneg_left (hk (k + 2) (by omega)) (abs_nonneg _))
        (hw2.mul_right β)
    calc (∑' k, |w (k + 2)| * ∫ v, ‖H (k + 2) v‖ ^ 2 ∂μ) ≤ ∑' k, |w (k + 2)| * β :=
          hs.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left (hk (k + 2) (by omega))
            (abs_nonneg _)) (hw2.mul_right β)
      _ = (∑' k, |w (k + 2)|) * β := tsum_mul_right
      _ ≤ τ * β := mul_le_mul_of_nonneg_right htail hβ
  have hRint : (∫ v, ‖R v‖ ^ 2 ∂μ) ≤ τ ^ 2 * β := by
    refine hRle.trans ?_
    calc (∑' k, |w (k + 2)|) * (∑' k, |w (k + 2)| * ∫ v, ‖H (k + 2) v‖ ^ 2 ∂μ) ≤
          τ * (τ * β) := mul_le_mul htail hsum_le
            (tsum_nonneg fun k => mul_nonneg (abs_nonneg _)
              (integral_nonneg fun _ => sq_nonneg _)) hτ
      _ = τ ^ 2 * β := by ring
  have hpt : ∀ v, (1 - θ) * ‖H 1 v‖ ^ 2 - (1 / θ - 1) * ‖R v‖ ^ 2 ≤ ‖F v‖ ^ 2 := fun v => by
    rw [hFeq v]
    exact norm_add_sq_ge_dominance _ _ hθ
  have hmono : (∫ v, ((1 - θ) * ‖H 1 v‖ ^ 2 - (1 / θ - 1) * ‖R v‖ ^ 2) ∂μ) ≤
      ∫ v, ‖F v‖ ^ 2 ∂μ :=
    integral_mono ((hH1i.const_mul _).sub (hRi.const_mul _)) hFi' hpt
  rw [integral_sub (hH1i.const_mul _) (hRi.const_mul _), integral_const_mul,
    integral_const_mul] at hmono
  have hc1 : 0 ≤ 1 - θ := by linarith
  have hc2 : 0 ≤ 1 / θ - 1 := by
    rw [sub_nonneg, le_div_iff₀ hθ]
    linarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hc1, mul_le_mul_of_nonneg_left hRint hc2]

/-- **Harmonic triangle bound in mean square.** If `F = ∑_k w_k H_k` with `w_0 = 0`,
`∑_k |w_k| ≤ W`, and `∫ ‖H_k‖² ≤ β` for `k ≥ 1`, then `∫ ‖F‖² ≤ W² β`. -/
theorem integral_norm_sq_le_of_harmonics {μ : Measure ℝ} [IsFiniteMeasure μ]
    {H : ℕ → ℝ → ℂ} {w : ℕ → ℝ} {F : ℝ → ℂ} {C W β : ℝ}
    (hF : ∀ v, HasSum (fun k => (w k : ℂ) * H k v) (F v))
    (hw : Summable fun k => |w k|) (hw0 : w 0 = 0) (htot : ∑' k, |w k| ≤ W)
    (hHc : ∀ k, Continuous (H k)) (hHb : ∀ k v, ‖H k v‖ ≤ C)
    (hk : ∀ k, 1 ≤ k → ∫ v, ‖H k v‖ ^ 2 ∂μ ≤ β) (hβ : 0 ≤ β) :
    Integrable (fun v => ‖F v‖ ^ 2) μ ∧ (∫ v, ‖F v‖ ^ 2 ∂μ) ≤ W ^ 2 * β := by
  obtain ⟨hFi, hFle⟩ := integral_norm_tsum_weighted_sq_le (μ := μ) hw hHc hHb
  have hW : 0 ≤ W := (tsum_nonneg fun _ => abs_nonneg _).trans htot
  have he : ∀ v, ‖∑' k, (w k : ℂ) * H k v‖ ^ 2 = ‖F v‖ ^ 2 := fun v => by
    rw [(hF v).tsum_eq]
  simp only [he] at hFi hFle
  refine ⟨hFi, hFle.trans ?_⟩
  have hkb : ∀ k, |w k| * ∫ v, ‖H k v‖ ^ 2 ∂μ ≤ |w k| * β := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · simp [hw0]
    · exact mul_le_mul_of_nonneg_left (hk k hk1) (abs_nonneg _)
  have hs : Summable fun k => |w k| * ∫ v, ‖H k v‖ ^ 2 ∂μ :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (abs_nonneg _) (integral_nonneg fun _ => sq_nonneg _)) hkb
      (hw.mul_right β)
  calc (∑' k, |w k|) * (∑' k, |w k| * ∫ v, ‖H k v‖ ^ 2 ∂μ) ≤ W * (W * β) := by
        refine mul_le_mul htot ?_ (tsum_nonneg fun k => mul_nonneg (abs_nonneg _)
          (integral_nonneg fun _ => sq_nonneg _)) hW
        calc (∑' k, |w k| * ∫ v, ‖H k v‖ ^ 2 ∂μ) ≤ ∑' k, |w k| * β :=
              hs.tsum_le_tsum hkb (hw.mul_right β)
          _ = (∑' k, |w k|) * β := tsum_mul_right
          _ ≤ W * β := mul_le_mul_of_nonneg_right htot hβ
    _ = W ^ 2 * β := by ring

theorem factorialWindowLength_eq : factorialWindowLength = 16 * factorialWindowGapConstant := rfl

/-- `‖-(π²/2) z‖² = (π⁴/4) ‖z‖²`. -/
theorem norm_neg_pi_sq_half_mul_sq (z : ℂ) :
    ‖-((Real.pi ^ 2 / 2 : ℝ) : ℂ) * z‖ ^ 2 = Real.pi ^ 4 / 4 * ‖z‖ ^ 2 := by
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow]
  ring

/-- **Finite-window coercivity of the factorial phases.** For every finite complex family
`b` and every real `a`, with `L = 16 K = 6240/π`,
`∫_a^{a+L} ‖∑_{n ∈ S} b_n Φ_{n+1}(v)‖² dv ≥ (L / (16 π⁴)) ∑_{n ∈ S} ‖b_n‖²`. -/
theorem factorialPhaseCombination_window_lower (S : Finset ℕ) (b : ℕ → ℂ) (a : ℝ) :
    factorialWindowLength / (16 * Real.pi ^ 4) * ∑ n ∈ S, ‖b n‖ ^ 2 ≤
      ∫ v in a..a + factorialWindowLength, ‖factorialPhaseCombination S b v‖ ^ 2 := by
  set L := factorialWindowLength with hLdef
  set K := factorialWindowGapConstant with hKdef
  set Sb := ∑ n ∈ S, ‖b n‖ ^ 2 with hSb
  have hL : 0 < L := factorialWindowLength_pos
  have hK : 0 < K := factorialWindowGapConstant_pos
  have hSb0 : 0 ≤ Sb := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hLK : L = 16 * K := factorialWindowLength_eq
  rw [intervalIntegral.integral_of_le (by linarith)]
  have hI (k : ℕ) : (∫ v in a..a + L, ‖factorialHarmonicLayer S b k v‖ ^ 2) =
      ∫ v in Ioc a (a + L), ‖factorialHarmonicLayer S b k v‖ ^ 2 :=
    intervalIntegral.integral_of_le (by linarith)
  have h1 : (L - K) * Sb ≤ ∫ v in Ioc a (a + L), ‖factorialHarmonicLayer S b 1 v‖ ^ 2 := by
    have h := (factorialHarmonicLayer_interval_bounds S b (k := 1) le_rfl (r := 1) le_rfl a L).1
    simp only [one_mul, Nat.cast_one, div_one] at h
    rwa [hI] at h
  have hk : ∀ k, 2 ≤ k →
      ∫ v in Ioc a (a + L), ‖factorialHarmonicLayer S b k v‖ ^ 2 ≤ (L + K) * Sb := by
    intro k hk2
    have h := (factorialHarmonicLayer_interval_bounds S b (k := k) (by omega) (r := 1) le_rfl
      a L).2
    simp only [one_mul] at h
    rw [hI] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hSb0)
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have : K / k ≤ K := div_le_self hK.le hk1
    linarith
  have hdom := integral_norm_sq_ge_of_first_harmonic
    (μ := volume.restrict (Ioc a (a + L)))
    (F := fun v => -((Real.pi ^ 2 / 2 : ℝ) : ℂ) * factorialPhaseCombination S b v)
    (factorialPhaseCombination_hasSum S b) summable_abs_dyadicHarmonicWeight
    dyadicHarmonicWeight_zero dyadicHarmonicWeight_one tsum_abs_dyadicHarmonicWeight_tail_le
    (continuous_factorialHarmonicLayer S b) (norm_factorialHarmonicLayer_le S b) h1 hk
    (θ := 4 / 5) (by norm_num) (by norm_num)
  simp only [norm_neg_pi_sq_half_mul_sq, integral_const_mul] at hdom
  have hpi : 0 < Real.pi ^ 4 := by positivity
  set I := ∫ v in Ioc a (a + L), ‖factorialPhaseCombination S b v‖ ^ 2 with hIdef
  have hmain : 39 / 1024 * L * Sb ≤ Real.pi ^ 4 / 4 * I := by
    rw [hLK] at hdom ⊢
    nlinarith
  have hgoal : Real.pi ^ 4 / 4 * (L / (16 * Real.pi ^ 4) * Sb) ≤ Real.pi ^ 4 / 4 * I := by
    have he : Real.pi ^ 4 / 4 * (L / (16 * Real.pi ^ 4) * Sb) = 16 / 1024 * L * Sb := by
      field_simp
      ring
    rw [he]
    nlinarith [mul_nonneg hL.le hSb0]
  exact le_of_mul_le_mul_left hgoal (by positivity)

/-- **Dilated window upper bound.** For `r ≥ 1`, every real `a`, and `ℓ ≥ 0`,
`∫_a^{a+ℓ} ‖B_b(r v)‖² dv ≤ (49 / (4 π⁴)) (ℓ + K) ∑ ‖b_n‖²`. -/
theorem factorialPhaseCombination_dilated_window_upper (S : Finset ℕ) (b : ℕ → ℂ) {r : ℝ}
    (hr : 1 ≤ r) (a : ℝ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    IntervalIntegrable (fun v => ‖factorialPhaseCombination S b (r * v)‖ ^ 2) volume a (a + ℓ) ∧
    (∫ v in a..a + ℓ, ‖factorialPhaseCombination S b (r * v)‖ ^ 2) ≤
      49 / (4 * Real.pi ^ 4) * (ℓ + factorialWindowGapConstant) * ∑ n ∈ S, ‖b n‖ ^ 2 := by
  set K := factorialWindowGapConstant with hKdef
  set Sb := ∑ n ∈ S, ‖b n‖ ^ 2 with hSb
  have hK : 0 < K := factorialWindowGapConstant_pos
  have hSb0 : 0 ≤ Sb := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hI (k : ℕ) : (∫ v in a..a + ℓ, ‖factorialHarmonicLayer S b k (r * v)‖ ^ 2) =
      ∫ v in Ioc a (a + ℓ), ‖factorialHarmonicLayer S b k (r * v)‖ ^ 2 :=
    intervalIntegral.integral_of_le (by linarith)
  have hk : ∀ k, 1 ≤ k →
      ∫ v in Ioc a (a + ℓ), ‖factorialHarmonicLayer S b k (r * v)‖ ^ 2 ≤ (ℓ + K) * Sb := by
    intro k hk1
    have h := (factorialHarmonicLayer_interval_bounds S b hk1 hr a ℓ).2
    rw [hI] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hSb0)
    have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have : K / k ≤ K := div_le_self hK.le hk1'
    linarith
  obtain ⟨hint, hup⟩ := integral_norm_sq_le_of_harmonics
    (μ := volume.restrict (Ioc a (a + ℓ)))
    (H := fun k v => factorialHarmonicLayer S b k (r * v))
    (F := fun v => -((Real.pi ^ 2 / 2 : ℝ) : ℂ) * factorialPhaseCombination S b (r * v))
    (fun v => factorialPhaseCombination_hasSum S b (r * v)) summable_abs_dyadicHarmonicWeight
    dyadicHarmonicWeight_zero tsum_abs_dyadicHarmonicWeight_le
    (fun k => (continuous_factorialHarmonicLayer S b k).comp (continuous_const.mul continuous_id))
    (fun k v => norm_factorialHarmonicLayer_le S b k (r * v)) hk
    (mul_nonneg (by linarith) hSb0)
  simp only [norm_neg_pi_sq_half_mul_sq, integral_const_mul] at hup
  have hpi : 0 < Real.pi ^ 4 := by positivity
  refine ⟨?_, ?_⟩
  · refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr ?_
    have h2 := hint.const_mul (4 / Real.pi ^ 4)
    refine h2.congr (Eventually.of_forall fun v => ?_)
    simp only [norm_neg_pi_sq_half_mul_sq]
    field_simp
  · rw [intervalIntegral.integral_of_le (by linarith)]
    set I := ∫ v in Ioc a (a + ℓ), ‖factorialPhaseCombination S b (r * v)‖ ^ 2
    have he : 49 / (4 * Real.pi ^ 4) * (ℓ + K) * Sb =
        (4 / Real.pi ^ 4) * ((7 / 4) ^ 2 * ((ℓ + K) * Sb)) := by
      field_simp
      ring
    rw [he]
    have hI4 : I = (4 / Real.pi ^ 4) * (Real.pi ^ 4 / 4 * I) := by
      field_simp
    rw [hI4]
    exact mul_le_mul_of_nonneg_left hup (by positivity)

/-- The negative fourth power `v ^ (-4)` as a reciprocal. -/
theorem rpow_neg_four_eq (v : ℝ) (hv : 0 ≤ v) : v ^ (-4 : ℝ) = (v ^ 4)⁻¹ := by
  rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hv, Real.rpow_natCast]

theorem continuousOn_rpow_neg_four_Ioi : ContinuousOn (fun v : ℝ => v ^ (-4 : ℝ)) (Ioi 0) :=
  continuousOn_id.rpow_const fun _x hx => Or.inl (ne_of_gt hx)

/-- The weighted dilated phase energy `v ↦ v^{-4} ‖B_b(r v)‖²` is integrable on `(1, ∞)`. -/
theorem integrableOn_weighted_factorialPhaseCombination (S : Finset ℕ) (b : ℕ → ℂ) (r : ℝ) :
    IntegrableOn (fun v => v ^ (-4 : ℝ) * ‖factorialPhaseCombination S b (r * v)‖ ^ 2)
      (Ioi 1) := by
  have hw : IntegrableOn (fun v : ℝ => v ^ (-4 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  set Cb := 2 * ∑ n ∈ S, ‖b n‖ with hCb
  refine (hw.mul_const (Cb ^ 2)).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact (continuousOn_rpow_neg_four_Ioi.mono fun x (hx : (1 : ℝ) < x) =>
      show (0 : ℝ) < x from lt_trans zero_lt_one hx).mul
      (((continuous_factorialPhaseCombination S b).comp
        (continuous_const.mul continuous_id)).norm.pow 2).continuousOn
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 < v := lt_trans zero_lt_one hv
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hv0.le _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
      (norm_factorialPhaseCombination_le S b (r * v)) 2) (Real.rpow_nonneg hv0.le _)

/-- **Weighted upper bound (dilated).** For `r ≥ 1`,
`∫_1^∞ v^{-4} ‖B_b(r v)‖² dv ≤ B ∑ ‖b_n‖²` with `B = 49 (1 + K) / (3 π⁴)`. -/
theorem factorialPhaseCombination_weighted_upper (S : Finset ℕ) (b : ℕ → ℂ) {r : ℝ}
    (hr : 1 ≤ r) :
    (∫ v in Ioi 1, v ^ (-4 : ℝ) * ‖factorialPhaseCombination S b (r * v)‖ ^ 2) ≤
      factorialWeightedPhaseUpper * ∑ n ∈ S, ‖b n‖ ^ 2 := by
  set Sb := ∑ n ∈ S, ‖b n‖ ^ 2 with hSb
  have hSb0 : 0 ≤ Sb := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set g : ℝ → ℝ := fun v => v ^ (-4 : ℝ) * ‖factorialPhaseCombination S b (r * v)‖ ^ 2
    with hg
  have hint := integrableOn_weighted_factorialPhaseCombination S b r
  have hlim := intervalIntegral_tendsto_integral_Ioi (f := g) (μ := volume) 1 hint
    (b := fun M : ℕ => 1 + (M : ℝ))
    (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
  refine le_of_tendsto' hlim fun M => ?_
  have hJ0 : 0 ≤ factorialUnitIntervalUpper * Sb :=
    mul_nonneg factorialUnitIntervalUpper_pos.le hSb0
  have hpiece : ∀ j : ℕ, IntervalIntegrable g volume (1 + (j : ℝ)) (1 + ((j + 1 : ℕ) : ℝ)) ∧
      (∫ v in (1 + (j : ℝ))..(1 + ((j + 1 : ℕ) : ℝ)), g v) ≤
        (1 / ((j + 1 : ℕ) : ℝ) ^ 4) * (factorialUnitIntervalUpper * Sb) := by
    intro j
    set aj : ℝ := 1 + (j : ℝ) with haj
    have haj1 : 1 ≤ aj := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have haj0 : 0 < aj := by linarith
    have hend : (1 : ℝ) + ((j + 1 : ℕ) : ℝ) = aj + 1 := by rw [haj]; push_cast; ring
    rw [hend]
    have hgi : IntervalIntegrable g volume aj (aj + 1) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
      exact hint.mono_set fun v hv => lt_of_le_of_lt haj1 hv.1
    obtain ⟨hBi, hBle⟩ := factorialPhaseCombination_dilated_window_upper S b hr aj zero_le_one
    refine ⟨hgi, ?_⟩
    have hmono : (∫ v in aj..aj + 1, g v) ≤
        ∫ v in aj..aj + 1, aj ^ (-4 : ℝ) * ‖factorialPhaseCombination S b (r * v)‖ ^ 2 := by
      refine intervalIntegral.integral_mono_on (by linarith) hgi (hBi.const_mul _) fun v hv => ?_
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos haj0 hv.1 (by norm_num)) (sq_nonneg _)
    rw [intervalIntegral.integral_const_mul] at hmono
    have hpow : aj ^ (-4 : ℝ) = 1 / ((j + 1 : ℕ) : ℝ) ^ 4 := by
      rw [rpow_neg_four_eq aj haj0.le, haj, one_div]
      push_cast
      ring_nf
    rw [hpow] at hmono
    refine hmono.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    unfold factorialUnitIntervalUpper
    have he : 49 / (4 * Real.pi ^ 4) * (1 + factorialWindowGapConstant) * Sb =
        49 * (1 + factorialWindowGapConstant) / (4 * Real.pi ^ 4) * Sb := by ring
    rw [← he]
    exact hBle
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := g)
    (a := fun k : ℕ => 1 + (k : ℝ)) (n := M) fun k _ => (hpiece k).1
  simp only [Nat.cast_zero, add_zero] at hsum
  rw [← hsum]
  calc (∑ k ∈ Finset.range M, ∫ v in (1 + (k : ℝ))..(1 + ((k + 1 : ℕ) : ℝ)), g v) ≤
        ∑ k ∈ Finset.range M, (1 / ((k + 1 : ℕ) : ℝ) ^ 4) * (factorialUnitIntervalUpper * Sb) :=
        Finset.sum_le_sum fun k _ => (hpiece k).2
    _ = ∑ j ∈ Finset.Icc 1 M, (1 / (j : ℝ) ^ 4) * (factorialUnitIntervalUpper * Sb) := by
        rw [Finset.range_eq_Ico, Finset.sum_Ico_add'
          (fun j : ℕ => (1 / (j : ℝ) ^ 4) * (factorialUnitIntervalUpper * Sb)) 0 M 1,
          zero_add, Finset.Ico_add_one_right_eq_Icc]
    _ ≤ factorialWeightedPhaseUpper * Sb := (weighted_phase_window_transport hSb0 M).2

/-- **Weighted lower bound.** `∫_1^∞ v^{-4} ‖B_b(v)‖² dv ≥ A ∑ ‖b_n‖²`
with `A = L / (16 π⁴ (1 + L)⁴)`. -/
theorem factorialPhaseCombination_weighted_lower (S : Finset ℕ) (b : ℕ → ℂ) :
    factorialWeightedPhaseLower * ∑ n ∈ S, ‖b n‖ ^ 2 ≤
      ∫ v in Ioi 1, v ^ (-4 : ℝ) * ‖factorialPhaseCombination S b v‖ ^ 2 := by
  set L := factorialWindowLength with hL
  set Sb := ∑ n ∈ S, ‖b n‖ ^ 2 with hSb
  have hSb0 : 0 ≤ Sb := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hL0 : 0 < L := factorialWindowLength_pos
  have hint := integrableOn_weighted_factorialPhaseCombination S b 1
  simp only [one_mul] at hint
  have hset : (∫ v in Ioc 1 (1 + L), v ^ (-4 : ℝ) * ‖factorialPhaseCombination S b v‖ ^ 2) ≤
      ∫ v in Ioi 1, v ^ (-4 : ℝ) * ‖factorialPhaseCombination S b v‖ ^ 2 := by
    refine setIntegral_mono_set hint ?_ (Eventually.of_forall fun v hv => ?_)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact mul_nonneg (Real.rpow_nonneg (lt_trans zero_lt_one hv).le _) (sq_nonneg _)
    · exact hv.1
  have hwin := factorialPhaseCombination_window_lower S b 1
  rw [intervalIntegral.integral_of_le (by linarith)] at hwin
  have hBi : IntegrableOn (fun v => ‖factorialPhaseCombination S b v‖ ^ 2) (Ioc 1 (1 + L)) := by
    have h := (factorialPhaseCombination_dilated_window_upper S b le_rfl 1 hL0.le).1
    simp only [one_mul] at h
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp h
  have hlow : (1 + L) ^ (-4 : ℝ) * ∫ v in Ioc 1 (1 + L), ‖factorialPhaseCombination S b v‖ ^ 2 ≤
      ∫ v in Ioc 1 (1 + L), v ^ (-4 : ℝ) * ‖factorialPhaseCombination S b v‖ ^ 2 := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hBi.const_mul _) (hint.mono_set Ioc_subset_Ioi_self)
      measurableSet_Ioc fun v hv => ?_
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos (lt_trans zero_lt_one hv.1) hv.2 (by norm_num)) (sq_nonneg _)
  have hpow : (1 + L) ^ (-4 : ℝ) = (1 + L)⁻¹ ^ 4 := by
    rw [rpow_neg_four_eq _ (by linarith), inv_pow]
  have htr := (weighted_phase_window_transport hSb0 0).1
  rw [hpow] at hlow
  calc factorialWeightedPhaseLower * Sb =
        (1 + L)⁻¹ ^ 4 * ((L / (16 * Real.pi ^ 4)) * Sb) := htr.symm
    _ ≤ (1 + L)⁻¹ ^ 4 * ∫ v in Ioc 1 (1 + L), ‖factorialPhaseCombination S b v‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hwin (by positivity)
    _ ≤ _ := hlow.trans hset

/-- A finite combination of literal correction tails is the zero-extended clock reading of the
phase combination with coefficients `b_n = c_n a_n`. -/
theorem sum_factorialMuntzCorrectedTail_eq (S : Finset ℕ) (c : ℕ → ℂ) (x : ℝ) :
    ∑ n ∈ S, c n * (factorialMuntzCorrectedTail n x : ℂ) =
      (Iic (0 : ℝ)).indicator (fun y => (Real.exp (3 * y / 2) : ℂ) *
        factorialPhaseCombination S (fun n => c n * (factorialTailAmplitude n : ℂ))
          (Real.exp (-y))) x := by
  by_cases hx : x ≤ 0
  · rw [indicator_of_mem (show x ∈ Iic 0 from hx)]
    unfold factorialPhaseCombination
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [factorialMuntzCorrectedTail_eq_factorialPhaseProfile,
      indicator_of_mem (show x ∈ Iic 0 from hx)]
    push_cast
    ring
  · rw [indicator_of_notMem (show x ∉ Iic 0 from hx)]
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [factorialMuntzCorrectedTail_eq_factorialPhaseProfile,
      indicator_of_notMem (show x ∉ Iic 0 from hx)]
    simp

/-- **Clock change of variables.** With `b_n = c_n a_n`, the physical square mass of a tail
combination is integrable and equals `∫_1^∞ v^{-4} ‖B_b(v)‖² dv` (substitution `v = e^{-x}`). -/
theorem integral_norm_sq_sum_factorialMuntzCorrectedTail (S : Finset ℕ) (c : ℕ → ℂ) :
    Integrable (fun x => ‖∑ n ∈ S, c n * (factorialMuntzCorrectedTail n x : ℂ)‖ ^ 2) ∧
    (∫ x, ‖∑ n ∈ S, c n * (factorialMuntzCorrectedTail n x : ℂ)‖ ^ 2) =
      ∫ v in Ioi 1, v ^ (-4 : ℝ) *
        ‖factorialPhaseCombination S (fun n => c n * (factorialTailAmplitude n : ℂ)) v‖ ^ 2 := by
  set B := factorialPhaseCombination S (fun n => c n * (factorialTailAmplitude n : ℂ)) with hB
  have hBc : Continuous B := continuous_factorialPhaseCombination S _
  set Cb := 2 * ∑ n ∈ S, ‖c n * (factorialTailAmplitude n : ℂ)‖ with hCb
  have hBb : ∀ v, ‖B v‖ ≤ Cb := norm_factorialPhaseCombination_le S _
  have hpt : (fun x => ‖∑ n ∈ S, c n * (factorialMuntzCorrectedTail n x : ℂ)‖ ^ 2) =
      (Iic (0 : ℝ)).indicator (fun y => Real.exp (3 * y) * ‖B (Real.exp (-y))‖ ^ 2) := by
    funext x
    rw [sum_factorialMuntzCorrectedTail_eq]
    by_cases hx : x ≤ 0
    · rw [indicator_of_mem (show x ∈ Iic 0 from hx), indicator_of_mem (show x ∈ Iic 0 from hx),
        norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    · rw [indicator_of_notMem (show x ∉ Iic 0 from hx),
        indicator_of_notMem (show x ∉ Iic 0 from hx)]
      simp
  have hcont : Continuous fun y => Real.exp (3 * y) * ‖B (Real.exp (-y))‖ ^ 2 := by
    fun_prop
  have hon : IntegrableOn (fun y => Real.exp (3 * y) * ‖B (Real.exp (-y))‖ ^ 2) (Iic 0) := by
    refine ((integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 3) 0).mul_const (Cb ^ 2)).mono'
      hcont.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hBb _) 2)
      (Real.exp_pos _).le
  refine ⟨?_, ?_⟩
  · rw [hpt]
    exact (integrable_indicator_iff measurableSet_Iic).mpr hon
  · rw [hpt, integral_indicator measurableSet_Iic]
    have hneg : (∫ y in Iic (0 : ℝ), Real.exp (3 * y) * ‖B (Real.exp (-y))‖ ^ 2) =
        ∫ t in Ioi (0 : ℝ), Real.exp (-3 * t) * ‖B (Real.exp t)‖ ^ 2 := by
      have h := integral_comp_neg_Iic (0 : ℝ)
        (fun t => Real.exp (-3 * t) * ‖B (Real.exp t)‖ ^ 2)
      simp only [neg_zero] at h
      rw [← h]
      refine setIntegral_congr_fun measurableSet_Iic fun y _ => ?_
      simp only [neg_mul, neg_neg, mul_neg]
    rw [hneg]
    have hcv := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ)) (f := Real.exp)
      (f' := Real.exp) measurableSet_Ioi
      (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn
      (fun v => v ^ (-4 : ℝ) * ‖B v‖ ^ 2)
    rw [Real.image_exp_Ioi, Real.exp_zero] at hcv
    rw [hcv]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [abs_of_pos (Real.exp_pos t), smul_eq_mul, ← Real.exp_mul, ← mul_assoc, ← Real.exp_add]
    congr 2
    ring

/-- **Physical Riesz bounds for the factorial correction tails.** For every finite index set
`S` and complex coefficients `c`, the physical square mass of `∑_{n ∈ S} c_n T_n` is finite and
`144 A ∑ |c_n|²/(n+1) ≤ ∫_ℝ |∑ c_n T_n|² ≤ 225 B ∑ |c_n|²/(n+1)`. -/
theorem factorialTail_physical_riesz_bounds (S : Finset ℕ) (c : ℕ → ℂ) :
    Integrable (fun x => ‖∑ n ∈ S, c n * (factorialMuntzCorrectedTail n x : ℂ)‖ ^ 2) ∧
    144 * factorialWeightedPhaseLower * (∑ n ∈ S, ‖c n‖ ^ 2 / ((n + 1 : ℕ) : ℝ)) ≤
      ∫ x, ‖∑ n ∈ S, c n * (factorialMuntzCorrectedTail n x : ℂ)‖ ^ 2 ∧
    (∫ x, ‖∑ n ∈ S, c n * (factorialMuntzCorrectedTail n x : ℂ)‖ ^ 2) ≤
      225 * factorialWeightedPhaseUpper * (∑ n ∈ S, ‖c n‖ ^ 2 / ((n + 1 : ℕ) : ℝ)) := by
  obtain ⟨hint, heq⟩ := integral_norm_sq_sum_factorialMuntzCorrectedTail S c
  obtain ⟨hlo, hhi⟩ := factorialTail_riesz_coefficient_bounds S c
  have hw_lo := factorialPhaseCombination_weighted_lower S
    (fun n => c n * (factorialTailAmplitude n : ℂ))
  have hw_hi := factorialPhaseCombination_weighted_upper S
    (fun n => c n * (factorialTailAmplitude n : ℂ)) (r := 1) le_rfl
  simp only [one_mul] at hw_hi
  refine ⟨hint, ?_, ?_⟩
  · rw [heq]
    exact hlo.trans hw_lo
  · rw [heq]
    exact hw_hi.trans hhi

end

end GaloisForLFunctions.ArithmeticPositivityTheory
