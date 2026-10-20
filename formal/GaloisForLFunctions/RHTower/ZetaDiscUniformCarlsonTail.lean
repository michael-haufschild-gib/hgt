import GaloisForLFunctions.RHTower.BagchiCarlsonCenteredTailBridge
import GaloisForLFunctions.HTGeometry.HolomorphicBallMeanSq

/-!
# Disc-uniform Carlson tails of zeta in the Bagchi strip

Carlson's mean-square law makes the tail `ζ − head_M`, `head_M(s) = Σ_{n ≤ M} n^{-s}`, small at
most heights of one vertical line `Re s = σ`, `1/2 < σ < 1`.  The self-return programme for `ζ`
needs that smallness *uniformly on a disc* of the strip, at a common height.  This module supplies
it unconditionally.

Three ingredients are connected.
1. The explicit arbitrary-order Euler–Maclaurin truncation scale is uniform on `[σ₀, 1]` up to the
   factor `2^(2m+2)` (`zetaTruncationErrorScale_le_of_le`).  Hence Carlson's dyadic mean square is
   bounded uniformly on a compact abscissa interval
   (`eventually_uniform_dyadic_zetaDirichletTail_meanSquare_le`).
2. The planar holomorphic mean-square inequality, applied to the entire function
   `(s − 1)(ζ(s) − head_M(s))`, bounds the tail at every point of `closedBall c r + iτ` by its
   planar mean square on `ball c (2r) + iτ`, with the explicit pole weight
   `(1 + r/(1 − (Re c + 2r)))²` (`normSq_zetaTailFun_le_integral_ball`).
3. Tonelli and Markov in the height variable turn that planar mean square into a density bound
   for the heights at which the tail is large somewhere on the disc
   (`volume_discTailBadSet_window_le`).

**Theorem** (`eventually_eventually_volume_discTailBadSet_le`).  Let `closedBall c (2r)` lie in
`1/2 < Re s < 1` and `ε, δ > 0`.  For all large `M`, the heights `τ ∈ [0, T]` with
`sup_{z ∈ closedBall c r} |ζ(z + iτ) − head_M(z + iτ)| ≥ ε` have measure at most `δ T` for all
large `T`.  Equivalently, the complement of the disc-uniform Abel-centered return set
`abelCenteredZetaTailReturnSet M (closedBall c r) ε` has asymptotic density at most `δ`
(`eventually_eventually_volume_not_mem_abelCenteredZetaTailReturnSet_le`).
-/

open Complex Filter Topology MeasureTheory Set Metric
open GaloisForLFunctions.HTGeometry
open scoped ENNReal

noncomputable section

namespace RHTower

/-! ## 1. The truncation scale is uniform on `[σ₀, 1]` up to a factor `2^(2m+2)` -/

/-- Every term of `zetaTruncationErrorScale` at `σ ∈ [σ₀, 1]` is at most `2^(2m+2)` times the
corresponding term at `σ₀`: powers of `N ≥ 1` decrease in the exponent, and the rising-factor bases
satisfy `σ + k ≤ 2 (σ₀ + k)`. -/
theorem zetaTruncationErrorScale_le_of_le {σ₀ σ : ℝ} (hσ₀ : 0 < σ₀) (hσ : σ₀ ≤ σ)
    (hσ1 : σ ≤ 1) (m : ℕ) {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hT : 0 ≤ T) :
    zetaTruncationErrorScale σ m N T ≤
      2 ^ (2 * m + 2) * zetaTruncationErrorScale σ₀ m N T := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hσpos : 0 < σ := lt_of_lt_of_le hσ₀ hσ
  have hC : (1 : ℝ) ≤ 2 ^ (2 * m + 2) := one_le_pow₀ (by norm_num)
  have hA1 : (N : ℝ) ^ (1 - σ) / T ≤ (N : ℝ) ^ (1 - σ₀) / T :=
    div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) hT
  have hA : (N : ℝ) ^ (1 - σ) / T ≤ 2 ^ (2 * m + 2) * ((N : ℝ) ^ (1 - σ₀) / T) :=
    hA1.trans (le_mul_of_one_le_left (by positivity) hC)
  have hB1 : (N : ℝ) ^ (-σ) / 2 ≤ (N : ℝ) ^ (-σ₀) / 2 :=
    div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) (by norm_num)
  have hB : (N : ℝ) ^ (-σ) / 2 ≤ 2 ^ (2 * m + 2) * ((N : ℝ) ^ (-σ₀) / 2) :=
    hB1.trans (le_mul_of_one_le_left (by positivity) hC)
  have hterm : ∀ r ∈ Finset.range (m + 1),
      |((bernoulli (2 * r + 2) : ℚ) : ℝ)| / ((2 * r + 2).factorial : ℝ) *
        ((σ + (2 * r + 1 : ℕ) + 2) * T) ^ (2 * r + 1) * (N : ℝ) ^ (-σ - (2 * r + 1 : ℕ)) ≤
      2 ^ (2 * m + 2) * (|((bernoulli (2 * r + 2) : ℚ) : ℝ)| / ((2 * r + 2).factorial : ℝ) *
        ((σ₀ + (2 * r + 1 : ℕ) + 2) * T) ^ (2 * r + 1) *
          (N : ℝ) ^ (-σ₀ - (2 * r + 1 : ℕ))) := by
    intro r hr
    have hrm : r ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    set b : ℝ := |((bernoulli (2 * r + 2) : ℚ) : ℝ)| / ((2 * r + 2).factorial : ℝ) with hb
    have hb0 : 0 ≤ b := by positivity
    have hk : (0 : ℝ) ≤ (2 * r + 1 : ℕ) := Nat.cast_nonneg _
    have hbase : (σ + (2 * r + 1 : ℕ) + 2) * T ≤ 2 * ((σ₀ + (2 * r + 1 : ℕ) + 2) * T) := by
      nlinarith [mul_nonneg hT (show (0 : ℝ) ≤ 2 * σ₀ + (2 * r + 1 : ℕ) + 2 - σ by linarith)]
    have hpow : ((σ + (2 * r + 1 : ℕ) + 2) * T) ^ (2 * r + 1) ≤
        2 ^ (2 * r + 1) * ((σ₀ + (2 * r + 1 : ℕ) + 2) * T) ^ (2 * r + 1) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hbase _
    have hrp : (N : ℝ) ^ (-σ - (2 * r + 1 : ℕ)) ≤ (N : ℝ) ^ (-σ₀ - (2 * r + 1 : ℕ)) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have h2 : (2 : ℝ) ^ (2 * r + 1) ≤ 2 ^ (2 * m + 2) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    calc b * ((σ + (2 * r + 1 : ℕ) + 2) * T) ^ (2 * r + 1) * (N : ℝ) ^ (-σ - (2 * r + 1 : ℕ))
        ≤ b * (2 ^ (2 * r + 1) * ((σ₀ + (2 * r + 1 : ℕ) + 2) * T) ^ (2 * r + 1)) *
            (N : ℝ) ^ (-σ₀ - (2 * r + 1 : ℕ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpow hb0) hrp (by positivity) (by positivity)
      _ = 2 ^ (2 * r + 1) * (b * ((σ₀ + (2 * r + 1 : ℕ) + 2) * T) ^ (2 * r + 1) *
            (N : ℝ) ^ (-σ₀ - (2 * r + 1 : ℕ))) := by ring
      _ ≤ 2 ^ (2 * m + 2) * (b * ((σ₀ + (2 * r + 1 : ℕ) + 2) * T) ^ (2 * r + 1) *
            (N : ℝ) ^ (-σ₀ - (2 * r + 1 : ℕ))) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
  have hS := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hS
  have hL : |((bernoulli (2 * m + 2) : ℚ) : ℝ)| / ((2 * m + 2).factorial : ℝ) *
      ((σ + (2 * m + 2 : ℕ) + 2) * T) ^ (2 * m + 2) *
        ((N : ℝ) ^ (1 - σ - (2 * m + 2 : ℕ)) / (σ + (2 * m + 2 : ℕ) - 1)) ≤
      2 ^ (2 * m + 2) * (|((bernoulli (2 * m + 2) : ℚ) : ℝ)| / ((2 * m + 2).factorial : ℝ) *
        ((σ₀ + (2 * m + 2 : ℕ) + 2) * T) ^ (2 * m + 2) *
          ((N : ℝ) ^ (1 - σ₀ - (2 * m + 2 : ℕ)) / (σ₀ + (2 * m + 2 : ℕ) - 1))) := by
    set b : ℝ := |((bernoulli (2 * m + 2) : ℚ) : ℝ)| / ((2 * m + 2).factorial : ℝ) with hb
    have hb0 : 0 ≤ b := by positivity
    have hk : (2 : ℝ) ≤ (2 * m + 2 : ℕ) := by exact_mod_cast (by omega : 2 ≤ 2 * m + 2)
    have hbase : (σ + (2 * m + 2 : ℕ) + 2) * T ≤ 2 * ((σ₀ + (2 * m + 2 : ℕ) + 2) * T) := by
      nlinarith [mul_nonneg hT (show (0 : ℝ) ≤ 2 * σ₀ + (2 * m + 2 : ℕ) + 2 - σ by linarith)]
    have hpow : ((σ + (2 * m + 2 : ℕ) + 2) * T) ^ (2 * m + 2) ≤
        2 ^ (2 * m + 2) * ((σ₀ + (2 * m + 2 : ℕ) + 2) * T) ^ (2 * m + 2) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hbase _
    have hden0 : 0 < σ₀ + (2 * m + 2 : ℕ) - 1 := by linarith
    have hden1 : 0 < σ + (2 * m + 2 : ℕ) - 1 := by linarith
    have hq : (N : ℝ) ^ (1 - σ - (2 * m + 2 : ℕ)) / (σ + (2 * m + 2 : ℕ) - 1) ≤
        (N : ℝ) ^ (1 - σ₀ - (2 * m + 2 : ℕ)) / (σ₀ + (2 * m + 2 : ℕ) - 1) := by
      calc (N : ℝ) ^ (1 - σ - (2 * m + 2 : ℕ)) / (σ + (2 * m + 2 : ℕ) - 1)
          ≤ (N : ℝ) ^ (1 - σ - (2 * m + 2 : ℕ)) / (σ₀ + (2 * m + 2 : ℕ) - 1) :=
            div_le_div_of_nonneg_left (by positivity) hden0 (by linarith)
        _ ≤ _ := div_le_div_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) hden0.le
    calc b * ((σ + (2 * m + 2 : ℕ) + 2) * T) ^ (2 * m + 2) *
          ((N : ℝ) ^ (1 - σ - (2 * m + 2 : ℕ)) / (σ + (2 * m + 2 : ℕ) - 1))
        ≤ b * (2 ^ (2 * m + 2) * ((σ₀ + (2 * m + 2 : ℕ) + 2) * T) ^ (2 * m + 2)) *
          ((N : ℝ) ^ (1 - σ₀ - (2 * m + 2 : ℕ)) / (σ₀ + (2 * m + 2 : ℕ) - 1)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpow hb0) hq
            (div_nonneg (by positivity) hden1.le) (by positivity)
      _ = _ := by ring
  unfold zetaTruncationErrorScale
  rw [mul_add, mul_add, mul_add]
  linarith [hA, hB, hS, hL]

/-! ## 2. Carlson's dyadic mean square, uniformly on a compact abscissa interval -/

theorem zetaCoefficientTailMass_nonneg (M : ℕ) (σ : ℝ) : 0 ≤ zetaCoefficientTailMass M σ := by
  unfold zetaCoefficientTailMass
  exact tsum_nonneg fun n => by split_ifs <;> positivity

/-- The finite band diagonal at `σ ≥ σ₀` is dominated by the full tail mass at `σ₀`. -/
theorem zetaBandDiagonal_le_zetaCoefficientTailMass (M N : ℕ) {σ₀ σ : ℝ} (hσ₀ : 1 / 2 < σ₀)
    (hσ : σ₀ ≤ σ) : zetaBandDiagonal M N σ ≤ zetaCoefficientTailMass M σ₀ := by
  unfold zetaBandDiagonal zetaCoefficientTailMass
  calc (∑ n ∈ Finset.Icc 1 N, if n ≤ M then (0 : ℝ) else (n : ℝ) ^ (-2 * σ))
      ≤ ∑ n ∈ Finset.Icc 1 N, if n ≤ M then (0 : ℝ) else (n : ℝ) ^ (-2 * σ₀) := by
        apply Finset.sum_le_sum
        intro n hn
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
        split_ifs
        · exact le_rfl
        · exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    _ ≤ ∑' n : ℕ, if n ≤ M then (0 : ℝ) else (n : ℝ) ^ (-2 * σ₀) := by
        refine Summable.sum_le_tsum _ (fun n _ => ?_) (summable_zetaCoefficientTail M hσ₀)
        split_ifs
        · exact le_rfl
        · positivity

/-- **Uniform Carlson bound.**  On `[σ₀, σ₁] ⊂ (1/2, 1)` the dyadic mean square of
`ζ − head_M` is eventually at most `V (2 · tailMass(M, σ₀) + η)`, uniformly in the abscissa. -/
theorem eventually_uniform_dyadic_zetaDirichletTail_meanSquare_le (M : ℕ) {σ₀ σ₁ : ℝ}
    (h0 : 1 / 2 < σ₀) (h01 : σ₀ ≤ σ₁) (h1 : σ₁ < 1) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ V : ℝ in atTop, ∀ σ ∈ Icc σ₀ σ₁,
      (∫ t in V..2 * V, ‖zetaDirichletTail M σ t‖ ^ 2) ≤
        V * (2 * zetaCoefficientTailMass M σ₀ + η) := by
  have hσ₀1 : σ₀ < 1 := lt_of_le_of_lt h01 h1
  have hσ₀0 : 0 < σ₀ := by linarith
  obtain ⟨m, hE, hN⟩ := exists_zetaSuperlinearTruncation h0 hσ₀1
  set a : ℝ := σ₀ + 1 / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  set C : ℝ := 2 ^ (2 * m + 2) with hC
  have hC1 : (1 : ℝ) ≤ C := one_le_pow₀ (by norm_num)
  have hC0 : 0 < C := by positivity
  set η₁ : ℝ := min 1 (η / (4 * C ^ 2)) with hη₁
  have hη₁0 : 0 < η₁ := lt_min one_pos (by positivity)
  have hη₁1 : η₁ ≤ 1 := min_le_left _ _
  have hη₁2 : η₁ ≤ η / (4 * C ^ 2) := min_le_right _ _
  have hmse : Tendsto (fun V : ℝ =>
      416 * ((superlinearCutoff a V : ℝ) ^ (2 - 2 * σ₀) / (2 - 2 * σ₁) + 1) / V)
      atTop (𝓝 0) := by
    have h1' : Tendsto (fun V : ℝ =>
        (superlinearCutoff a V : ℝ) ^ (2 - 2 * σ₀) / V / (2 - 2 * σ₁)) atTop (𝓝 0) := by
      simpa using hN.div_const (2 - 2 * σ₁)
    have h2' : Tendsto (fun V : ℝ => 1 / V) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h3 := (h1'.add h2').const_mul 416
    rw [add_zero, mul_zero] at h3
    exact h3.congr' (Eventually.of_forall fun V => by ring)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_superlinearCutoff ha0).eventually (eventually_ge_atTop (max M 1)),
    hE.eventually (gt_mem_nhds hη₁0),
    hmse.eventually (gt_mem_nhds (half_pos hη))] with V hV1 hNV hEV hmV
  intro σ hσ
  set N : ℕ := superlinearCutoff a V with hNdef
  have hMN : M ≤ N := (le_max_left _ _).trans hNV
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hNV
  have hσ0 : 0 < σ := by linarith [hσ.1]
  have hσ1 : σ < 1 := lt_of_le_of_lt hσ.2 h1
  have hV0 : 0 < V := by linarith
  have hE0 : 0 ≤ zetaTruncationErrorScale σ m N V :=
    zetaTruncationErrorScale_nonneg hσ0 hV0.le m N
  have hEsq : 2 * zetaTruncationErrorScale σ m N V ^ 2 ≤ η / 2 := by
    have hEsmall : zetaTruncationErrorScale σ m N V ≤ C * η₁ :=
      calc zetaTruncationErrorScale σ m N V
          ≤ C * zetaTruncationErrorScale σ₀ m N V :=
            zetaTruncationErrorScale_le_of_le hσ₀0 hσ.1 hσ1.le m hN1 hV0.le
        _ ≤ C * η₁ := mul_le_mul_of_nonneg_left hEV.le hC0.le
    have h1 : zetaTruncationErrorScale σ m N V ^ 2 ≤ (C * η₁) ^ 2 :=
      pow_le_pow_left₀ hE0 hEsmall 2
    have h2 : (C * η₁) ^ 2 ≤ C ^ 2 * η₁ := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    have h3 : C ^ 2 * η₁ ≤ η / 4 := by
      calc C ^ 2 * η₁ ≤ C ^ 2 * (η / (4 * C ^ 2)) :=
            mul_le_mul_of_nonneg_left hη₁2 (by positivity)
        _ = η / 4 := by
            rw [mul_div_assoc', mul_comm (C ^ 2) η, mul_div_mul_right _ _ (by positivity)]
    linarith
  have hpt : ∀ t ∈ Icc V (2 * V), ‖zetaDirichletTail M σ t‖ ^ 2 ≤
      η / 2 + 2 * ‖zetaDirichletBand M N σ t‖ ^ 2 := by
    intro t ht
    have hdec : zetaDirichletTail M σ t =
        (riemannZeta ((σ : ℂ) + (t : ℂ) * I) - zetaDirichletHead N σ t) +
          zetaDirichletBand M N σ t := by
      rw [zetaDirichletBand_eq_sub hMN]
      unfold zetaDirichletTail
      ring
    have hnorm : ‖zetaDirichletTail M σ t‖ ≤
        zetaTruncationErrorScale σ m N V + ‖zetaDirichletBand M N σ t‖ := by
      rw [hdec]
      exact (norm_add_le _ _).trans
        (add_le_add (norm_zeta_sub_head_le_arbitraryOrder hσ0 hV1 ht hN1 m) le_rfl)
    have h0 := norm_nonneg (zetaDirichletTail M σ t)
    have hb := norm_nonneg (zetaDirichletBand M N σ t)
    nlinarith [mul_le_mul hnorm hnorm h0 (add_nonneg hE0 hb),
      sq_nonneg (zetaTruncationErrorScale σ m N V - ‖zetaDirichletBand M N σ t‖)]
  have hcontT : Continuous (fun t => ‖zetaDirichletTail M σ t‖ ^ 2) :=
    (continuous_zetaDirichletTail M hσ1.ne).norm.pow 2
  have hcontB : Continuous (fun t => ‖zetaDirichletBand M N σ t‖ ^ 2) :=
    (continuous_zetaDirichletBand M N σ).norm.pow 2
  have hint : (∫ t in V..2 * V, ‖zetaDirichletTail M σ t‖ ^ 2) ≤
      ∫ t in V..2 * V, (η / 2 + 2 * ‖zetaDirichletBand M N σ t‖ ^ 2) :=
    intervalIntegral.integral_mono_on (by linarith) (hcontT.intervalIntegrable _ _)
      ((continuous_const.add (continuous_const.mul hcontB)).intervalIntegrable _ _) hpt
  have hsplit : (∫ t in V..2 * V, (η / 2 + 2 * ‖zetaDirichletBand M N σ t‖ ^ 2)) =
      (2 * V - V) * (η / 2) + 2 * ∫ t in V..2 * V, ‖zetaDirichletBand M N σ t‖ ^ 2 := by
    have hf : IntervalIntegrable (fun _ : ℝ => η / 2) volume V (2 * V) :=
      continuous_const.intervalIntegrable _ _
    have hg : IntervalIntegrable (fun t => 2 * ‖zetaDirichletBand M N σ t‖ ^ 2) volume V (2 * V) :=
      (continuous_const.mul hcontB).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hf hg, intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, smul_eq_mul]
  have hband : (∫ t in V..2 * V, ‖zetaDirichletBand M N σ t‖ ^ 2) ≤
      V * zetaBandDiagonal M N σ + 208 * ((N : ℝ) ^ (2 - 2 * σ) / (2 - 2 * σ) + 1) := by
    have h := zetaDirichletBand_meanSquare_error_subcritical M N (lt_of_lt_of_le h0 hσ.1) hσ1
      V (2 * V)
    rw [show 2 * V - V = V by ring] at h
    linarith [(abs_le.mp h).2]
  have hdiag : zetaBandDiagonal M N σ ≤ zetaCoefficientTailMass M σ₀ :=
    zetaBandDiagonal_le_zetaCoefficientTailMass M N h0 hσ.1
  have hmse' : 208 * ((N : ℝ) ^ (2 - 2 * σ) / (2 - 2 * σ) + 1) ≤
      208 * ((N : ℝ) ^ (2 - 2 * σ₀) / (2 - 2 * σ₁) + 1) := by
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hd1 : 0 < 2 - 2 * σ₁ := by linarith
    have : (N : ℝ) ^ (2 - 2 * σ) / (2 - 2 * σ) ≤ (N : ℝ) ^ (2 - 2 * σ₀) / (2 - 2 * σ₁) :=
      calc (N : ℝ) ^ (2 - 2 * σ) / (2 - 2 * σ)
          ≤ (N : ℝ) ^ (2 - 2 * σ) / (2 - 2 * σ₁) :=
            div_le_div_of_nonneg_left (by positivity) hd1 (by linarith [hσ.2])
        _ ≤ _ := div_le_div_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_le hN1' (by linarith [hσ.1])) hd1.le
    linarith
  have hmV' : 416 * ((N : ℝ) ^ (2 - 2 * σ₀) / (2 - 2 * σ₁) + 1) ≤ V * (η / 2) := by
    have := hmV
    rw [div_lt_iff₀ hV0] at this
    linarith
  calc (∫ t in V..2 * V, ‖zetaDirichletTail M σ t‖ ^ 2)
      ≤ (2 * V - V) * (η / 2) + 2 * ∫ t in V..2 * V, ‖zetaDirichletBand M N σ t‖ ^ 2 :=
        hsplit ▸ hint
    _ ≤ (2 * V - V) * (η / 2) + 2 * (V * zetaCoefficientTailMass M σ₀ +
          208 * ((N : ℝ) ^ (2 - 2 * σ₀) / (2 - 2 * σ₁) + 1)) := by
        have := hband.trans (add_le_add (mul_le_mul_of_nonneg_left hdiag hV0.le) hmse')
        linarith
    _ ≤ V * (2 * zetaCoefficientTailMass M σ₀ + η) := by linarith [hmV']

/-- Three dyadic windows cover `[V/4, 2V]`. -/
theorem eventually_uniform_window_zetaDirichletTail_meanSquare_le (M : ℕ) {σ₀ σ₁ : ℝ}
    (h0 : 1 / 2 < σ₀) (h01 : σ₀ ≤ σ₁) (h1 : σ₁ < 1) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ V : ℝ in atTop, ∀ σ ∈ Icc σ₀ σ₁,
      (∫ t in V / 4..2 * V, ‖zetaDirichletTail M σ t‖ ^ 2) ≤
        7 * V / 4 * (2 * zetaCoefficientTailMass M σ₀ + η) := by
  obtain ⟨V₀, hV₀⟩ := eventually_atTop.mp
    (eventually_uniform_dyadic_zetaDirichletTail_meanSquare_le M h0 h01 h1 hη)
  filter_upwards [eventually_ge_atTop (4 * max V₀ 0)] with V hV
  intro σ hσ
  have h4 : V₀ ≤ V / 4 := by linarith [le_max_left V₀ 0]
  have h2 : V₀ ≤ V / 2 := by linarith [le_max_left V₀ 0, le_max_right V₀ 0]
  have h1' : V₀ ≤ V := by linarith [le_max_left V₀ 0, le_max_right V₀ 0]
  have hσ1 : σ ≠ 1 := ne_of_lt (lt_of_le_of_lt hσ.2 h1)
  have hii : ∀ a b : ℝ, IntervalIntegrable (fun t => ‖zetaDirichletTail M σ t‖ ^ 2) volume a b :=
    fun a b => ((continuous_zetaDirichletTail M hσ1).norm.pow 2).intervalIntegrable a b
  have e1 := hV₀ (V / 4) h4 σ hσ
  have e2 := hV₀ (V / 2) h2 σ hσ
  have e3 := hV₀ V h1' σ hσ
  rw [show 2 * (V / 4) = V / 2 by ring] at e1
  rw [show 2 * (V / 2) = V by ring] at e2
  rw [← intervalIntegral.integral_add_adjacent_intervals (hii (V / 4) (V / 2)) (hii (V / 2) (2 * V)),
    ← intervalIntegral.integral_add_adjacent_intervals (hii (V / 2) V) (hii V (2 * V))]
  linarith [e1, e2, e3]

/-! ## 3. The tail as a function of the complex variable, and its entire pole-weighted form -/

/-- `ζ(s) − Σ_{n ≤ M} n^{-s}` as a function of `s`. -/
def zetaTailFun (M : ℕ) (s : ℂ) : ℂ :=
  riemannZeta s - edPoly (fun _ => 1) (Finset.Icc 1 M) s

theorem zetaTailFun_eq_zetaDirichletTail (M : ℕ) (s : ℂ) :
    zetaTailFun M s = zetaDirichletTail M s.re s.im :=
  riemannZeta_sub_edPoly_one_Icc_eq_zetaDirichletTail M s

theorem zetaTailFun_add_mul_I (M : ℕ) (z : ℂ) (τ : ℝ) :
    zetaTailFun M (z + τ * I) = zetaDirichletTail M z.re (z.im + τ) :=
  riemannZeta_shift_sub_edPoly_one_Icc_eq_zetaDirichletTail M z τ

theorem differentiable_edPoly_one_Icc (M : ℕ) :
    Differentiable ℂ (edPoly (fun _ => 1) (Finset.Icc 1 M)) :=
  differentiable_edPoly _ fun _ hn => (Finset.mem_Icc.mp hn).1

theorem continuousOn_zetaTailFun (M : ℕ) : ContinuousOn (zetaTailFun M) ({1} : Set ℂ)ᶜ := by
  intro s hs
  have hs1 : s ≠ 1 := hs
  exact ((differentiableAt_riemannZeta hs1).continuousAt.sub
    ((differentiable_edPoly_one_Icc M) s).continuousAt).continuousWithinAt

theorem measurable_zetaTailFun (M : ℕ) : Measurable (zetaTailFun M) :=
  measurable_of_continuousOn_compl_singleton 1 (continuousOn_zetaTailFun M)

/-- `(s − 1) ζ(s)`, with the removable singularity at `s = 1` filled by the residue `1`. -/
def zetaPoleFilled : ℂ → ℂ :=
  Function.update (fun s : ℂ => (s - 1) * riemannZeta s) 1 1

theorem zetaPoleFilled_of_ne {s : ℂ} (hs : s ≠ 1) :
    zetaPoleFilled s = (s - 1) * riemannZeta s :=
  Function.update_of_ne hs _ _

/-- `(s − 1) ζ(s)` is entire: holomorphic off `1`, and continuous at `1` by the residue law. -/
theorem differentiable_zetaPoleFilled : Differentiable ℂ zetaPoleFilled := by
  rw [← differentiableOn_univ]
  refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff (c := (1 : ℂ))
    univ_mem).mp ⟨?_, ?_⟩
  · intro s hs
    have hs1 : s ≠ 1 := fun h => hs.2 (by rw [h]; exact mem_singleton 1)
    have hd : DifferentiableAt ℂ (fun s : ℂ => (s - 1) * riemannZeta s) s :=
      (differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs1)
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [isOpen_ne.mem_nhds hs1] with w hw
    exact zetaPoleFilled_of_ne hw
  · rw [← continuousWithinAt_compl_self]
    unfold ContinuousWithinAt
    rw [show zetaPoleFilled 1 = 1 from Function.update_self _ _ _]
    refine riemannZeta_residue_one.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (zetaPoleFilled_of_ne hw).symm

/-- The pole-weighted tail `(s − 1)(ζ(s) − head_M(s))`, entire in `s`. -/
def zetaTailPoleWeighted (M : ℕ) (s : ℂ) : ℂ :=
  zetaPoleFilled s - (s - 1) * edPoly (fun _ => 1) (Finset.Icc 1 M) s

theorem differentiable_zetaTailPoleWeighted (M : ℕ) :
    Differentiable ℂ (zetaTailPoleWeighted M) :=
  differentiable_zetaPoleFilled.sub
    ((differentiable_id.sub_const 1).mul (differentiable_edPoly_one_Icc M))

theorem zetaTailPoleWeighted_of_ne (M : ℕ) {s : ℂ} (hs : s ≠ 1) :
    zetaTailPoleWeighted M s = (s - 1) * zetaTailFun M s := by
  unfold zetaTailPoleWeighted zetaTailFun
  rw [zetaPoleFilled_of_ne hs]
  ring

theorem norm_zetaTailPoleWeighted (M : ℕ) {s : ℂ} (hs : s ≠ 1) :
    ‖zetaTailPoleWeighted M s‖ = ‖s - 1‖ * ‖zetaTailFun M s‖ := by
  rw [zetaTailPoleWeighted_of_ne M hs, norm_mul]

/-! ## 4. Sup on a disc from the planar mean square on the doubled disc -/

theorem re_le_of_mem_closedBall {c z : ℂ} {r : ℝ} (hz : z ∈ closedBall c r) :
    z.re ≤ c.re + r := by
  have h := (abs_le.mp ((Complex.abs_re_le_norm (z - c)).trans
    (mem_closedBall_iff_norm.mp hz))).2
  rw [Complex.sub_re] at h
  linarith

theorem re_lt_of_mem_ball {c z : ℂ} {r : ℝ} (hz : z ∈ ball c r) : z.re < c.re + r := by
  have h := (abs_lt.mp ((Complex.abs_re_le_norm (z - c)).trans_lt
    (mem_ball_iff_norm.mp hz))).2
  rw [Complex.sub_re] at h
  linarith

theorem re_gt_of_mem_ball {c z : ℂ} {r : ℝ} (hz : z ∈ ball c r) : c.re - r < z.re := by
  have h := (abs_lt.mp ((Complex.abs_re_le_norm (z - c)).trans_lt
    (mem_ball_iff_norm.mp hz))).1
  rw [Complex.sub_re] at h
  linarith

theorem im_sub_abs_lt_of_mem_ball {c z : ℂ} {r : ℝ} (hz : z ∈ ball c r) :
    |z.im - c.im| < r := by
  have h := (Complex.abs_im_le_norm (z - c)).trans_lt (mem_ball_iff_norm.mp hz)
  rwa [Complex.sub_im] at h

theorem one_sub_re_le_norm_sub_one (s : ℂ) : 1 - s.re ≤ ‖s - 1‖ := by
  have h := Complex.abs_re_le_norm (s - 1)
  rw [Complex.sub_re, Complex.one_re] at h
  linarith [neg_le_abs (s.re - 1)]

/-- `‖ζ − head_M‖²` is integrable on every ball left of the pole. -/
theorem integrableOn_normSq_zetaTailFun_ball (M : ℕ) {w₀ : ℂ} {ρ : ℝ} (hρ : w₀.re + ρ < 1) :
    IntegrableOn (fun w => ‖zetaTailFun M w‖ ^ 2) (ball w₀ ρ) := by
  have hcont : ContinuousOn (fun w => ‖zetaTailFun M w‖ ^ 2) (closedBall w₀ ρ) := by
    refine ((continuousOn_zetaTailFun M).mono ?_).norm.pow 2
    intro w hw h1
    have hw1 : w = 1 := Set.mem_singleton_iff.mp h1
    have := re_le_of_mem_closedBall hw
    rw [hw1, Complex.one_re] at this
    linarith
  exact (hcont.integrableOn_compact (isCompact_closedBall w₀ ρ)).mono_set ball_subset_closedBall

theorem integrableOn_normSq_zetaTailFun_shift_ball (M : ℕ) {c : ℂ} {ρ : ℝ}
    (h1 : c.re + ρ < 1) (τ : ℝ) :
    IntegrableOn (fun w => ‖zetaTailFun M (w + τ * I)‖ ^ 2) (ball c ρ) := by
  have hcont : ContinuousOn (fun w => ‖zetaTailFun M (w + τ * I)‖ ^ 2) (closedBall c ρ) := by
    refine ((continuousOn_zetaTailFun M).comp
      (continuous_id.add continuous_const).continuousOn ?_).norm.pow 2
    intro w hw h1'
    have hw1 : w + τ * I = 1 := Set.mem_singleton_iff.mp h1'
    have hre := re_le_of_mem_closedBall hw
    have h2 := congrArg Complex.re hw1
    simp at h2
    linarith
  exact (hcont.integrableOn_compact (isCompact_closedBall c ρ)).mono_set ball_subset_closedBall

/-- Translation of the planar integral along the imaginary axis. -/
theorem integral_ball_normSq_zetaTailFun_shift (M : ℕ) (c : ℂ) (ρ : ℝ) (τ : ℝ) :
    (∫ w in ball (c + τ * I) ρ, ‖zetaTailFun M w‖ ^ 2) =
      ∫ w in ball c ρ, ‖zetaTailFun M (w + τ * I)‖ ^ 2 := by
  rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball]
  calc (∫ w, (ball (c + τ * I) ρ).indicator (fun w => ‖zetaTailFun M w‖ ^ 2) w)
      = ∫ w, (ball (c + τ * I) ρ).indicator (fun w => ‖zetaTailFun M w‖ ^ 2) (w + τ * I) :=
        (MeasureTheory.integral_add_right_eq_self _ _).symm
    _ = ∫ w, (ball c ρ).indicator (fun w => ‖zetaTailFun M (w + τ * I)‖ ^ 2) w := by
        congr 1
        funext w
        by_cases hw : w ∈ ball c ρ
        · have hw' : w + τ * I ∈ ball (c + τ * I) ρ := by rwa [mem_ball, dist_add_right]
          rw [indicator_of_mem hw', indicator_of_mem hw]
        · have hw' : w + τ * I ∉ ball (c + τ * I) ρ := by rwa [mem_ball, dist_add_right]
          rw [indicator_of_notMem hw', indicator_of_notMem hw]

/-- **Pointwise control on the disc.**  For `z ∈ closedBall c r` and any height `τ`, the tail at
`z + iτ` is bounded by its planar mean square on `ball c (2r) + iτ`, with the pole weight
`(1 + r/(1 − (Re c + 2r)))²` coming from the entire function `(s − 1)(ζ(s) − head_M(s))`. -/
theorem normSq_zetaTailFun_le_integral_ball (M : ℕ) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (h1 : c.re + 2 * r < 1) {z : ℂ} (hz : z ∈ closedBall c r) (τ : ℝ) :
    ‖zetaTailFun M (z + τ * I)‖ ^ 2 ≤
      (1 + r / (1 - (c.re + 2 * r))) ^ 2 / (Real.pi * r ^ 2) *
        ∫ w in ball c (2 * r), ‖zetaTailFun M (w + τ * I)‖ ^ 2 := by
  set w₀ : ℂ := z + τ * I with hw₀
  have hw₀re : w₀.re = z.re := by simp [hw₀]
  have hzre : z.re ≤ c.re + r := re_le_of_mem_closedBall hz
  set L : ℝ := 1 - (c.re + 2 * r) with hL
  have hL0 : 0 < L := by rw [hL]; linarith
  have hw₀1 : w₀ ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hw₀re, Complex.one_re] at this
    linarith
  set A : ℝ := ‖w₀ - 1‖ with hA
  have hAL : L ≤ A := by
    have := one_sub_re_le_norm_sub_one w₀
    rw [hw₀re] at this
    rw [hL, hA]
    linarith
  have hA0 : 0 < A := lt_of_lt_of_le hL0 hAL
  have hmvi := normSq_value_mul_area_le_integral_ball (zetaTailPoleWeighted M)
    (differentiable_zetaTailPoleWeighted M) w₀ hr
  have hpt : ∀ w ∈ ball w₀ r,
      ‖zetaTailPoleWeighted M w‖ ^ 2 ≤ (A + r) ^ 2 * ‖zetaTailFun M w‖ ^ 2 := by
    intro w hw
    have hwre : w.re < c.re + 2 * r := by
      have := re_lt_of_mem_ball hw
      rw [hw₀re] at this
      linarith
    have hw1 : w ≠ 1 := by
      intro h
      rw [h, Complex.one_re] at hwre
      linarith
    rw [norm_zetaTailPoleWeighted M hw1, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply pow_le_pow_left₀ (norm_nonneg _)
    calc ‖w - 1‖ = ‖(w - w₀) + (w₀ - 1)‖ := by ring_nf
      _ ≤ ‖w - w₀‖ + ‖w₀ - 1‖ := norm_add_le _ _
      _ ≤ A + r := by
          have := mem_ball_iff_norm.mp hw
          rw [hA]
          linarith
  have hρ : w₀.re + r < 1 := by rw [hw₀re]; linarith
  have hiF : IntegrableOn (fun w => ‖zetaTailFun M w‖ ^ 2) (ball w₀ r) :=
    integrableOn_normSq_zetaTailFun_ball M hρ
  have hiΦ : IntegrableOn (fun w => ‖zetaTailPoleWeighted M w‖ ^ 2) (ball w₀ r) :=
    (((differentiable_zetaTailPoleWeighted M).continuous.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall w₀ r)).mono_set ball_subset_closedBall
  have hint1 : (∫ w in ball w₀ r, ‖zetaTailPoleWeighted M w‖ ^ 2) ≤
      (A + r) ^ 2 * ∫ w in ball w₀ r, ‖zetaTailFun M w‖ ^ 2 := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on hiΦ (Integrable.const_mul hiF _) measurableSet_ball hpt
  have hball : ball w₀ r ⊆ ball (c + τ * I) (2 * r) := by
    intro w hw
    rw [mem_ball] at hw ⊢
    have hd : dist w₀ (c + τ * I) ≤ r := by
      rw [hw₀, dist_add_right]
      exact mem_closedBall.mp hz
    calc dist w (c + τ * I) ≤ dist w w₀ + dist w₀ (c + τ * I) := dist_triangle _ _ _
      _ < r + r := by linarith
      _ = 2 * r := by ring
  have hcre : (c + τ * I).re = c.re := by simp
  have hiF2 : IntegrableOn (fun w => ‖zetaTailFun M w‖ ^ 2) (ball (c + τ * I) (2 * r)) :=
    integrableOn_normSq_zetaTailFun_ball M (by rw [hcre]; exact h1)
  have hint2 : (∫ w in ball w₀ r, ‖zetaTailFun M w‖ ^ 2) ≤
      ∫ w in ball (c + τ * I) (2 * r), ‖zetaTailFun M w‖ ^ 2 :=
    setIntegral_mono_set hiF2 (Eventually.of_forall fun w => by
      show (0 : ℝ) ≤ ‖zetaTailFun M w‖ ^ 2
      positivity) (Eventually.of_forall hball)
  rw [integral_ball_normSq_zetaTailFun_shift M c (2 * r) τ] at hint2
  set J : ℝ := (∫ w in ball c (2 * r), ‖zetaTailFun M (w + τ * I)‖ ^ 2) with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun w => by positivity
  set X : ℝ := ‖zetaTailFun M w₀‖ ^ 2 with hX
  have hAr : A + r ≤ A * (1 + r / L) := by
    have h1' : r ≤ A * r / L := by
      rw [le_div_iff₀ hL0]
      nlinarith
    calc A + r ≤ A + A * r / L := by linarith
      _ = A * (1 + r / L) := by ring
  have hAr2 : (A + r) ^ 2 ≤ A ^ 2 * (1 + r / L) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hAr 2
  have hkey : Real.pi * r ^ 2 * (A ^ 2 * X) ≤ A ^ 2 * ((1 + r / L) ^ 2 * J) := by
    have e1 : ‖zetaTailPoleWeighted M w₀‖ ^ 2 = A ^ 2 * X := by
      rw [norm_zetaTailPoleWeighted M hw₀1, mul_pow]
    rw [e1] at hmvi
    calc Real.pi * r ^ 2 * (A ^ 2 * X)
        ≤ ∫ w in ball w₀ r, ‖zetaTailPoleWeighted M w‖ ^ 2 := hmvi
      _ ≤ (A + r) ^ 2 * ∫ w in ball w₀ r, ‖zetaTailFun M w‖ ^ 2 := hint1
      _ ≤ (A + r) ^ 2 * J := mul_le_mul_of_nonneg_left hint2 (by positivity)
      _ ≤ A ^ 2 * (1 + r / L) ^ 2 * J := mul_le_mul_of_nonneg_right hAr2 hJ0
      _ = A ^ 2 * ((1 + r / L) ^ 2 * J) := by ring
  have hkey2 : Real.pi * r ^ 2 * X ≤ (1 + r / L) ^ 2 * J := by
    have hA2 : 0 < A ^ 2 := by positivity
    rw [show Real.pi * r ^ 2 * (A ^ 2 * X) = A ^ 2 * (Real.pi * r ^ 2 * X) by ring] at hkey
    exact le_of_mul_le_mul_left hkey hA2
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith [hkey2]

/-! ## 5. Planar tail energy on the translated doubled disc -/

/-- Planar mean square of `ζ − head_M` on `ball c (2r) + iτ`, as a function of the height. -/
def discTailEnergy (M : ℕ) (c : ℂ) (r : ℝ) (τ : ℝ) : ℝ≥0∞ :=
  ∫⁻ w in ball c (2 * r), ENNReal.ofReal (‖zetaTailFun M (w + τ * I)‖ ^ 2)

/-- Heights at which the tail is at least `ε` somewhere on `closedBall c r + iτ`. -/
def discTailBadSet (M : ℕ) (c : ℂ) (r ε : ℝ) : Set ℝ :=
  {τ : ℝ | ∃ z ∈ closedBall c r, ε ≤ ‖zetaTailFun M (z + τ * I)‖}

theorem measurable_shiftedTailEnergyIntegrand (M : ℕ) :
    Measurable (fun p : ℝ × ℂ => ENNReal.ofReal (‖zetaTailFun M (p.2 + p.1 * I)‖ ^ 2)) := by
  have hm : Measurable (fun p : ℝ × ℂ => p.2 + (p.1 : ℂ) * I) :=
    (continuous_snd.add ((Complex.continuous_ofReal.comp continuous_fst).mul
      continuous_const)).measurable
  exact (((measurable_zetaTailFun M).comp hm).norm.pow_const 2).ennreal_ofReal

theorem measurable_discTailEnergy (M : ℕ) (c : ℂ) (r : ℝ) :
    Measurable (discTailEnergy M c r) :=
  (measurable_shiftedTailEnergyIntegrand M).lintegral_prod_right'

/-- The bad heights are those of large planar energy. -/
theorem discTailBadSet_subset_energy_ge (M : ℕ) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (h1 : c.re + 2 * r < 1) {ε : ℝ} (hε : 0 < ε) :
    discTailBadSet M c r ε ⊆
      {τ : ℝ | ENNReal.ofReal (ε ^ 2 * (Real.pi * r ^ 2) /
        (1 + r / (1 - (c.re + 2 * r))) ^ 2) ≤ discTailEnergy M c r τ} := by
  rintro τ ⟨z, hz, hε'⟩
  have hL : 0 < 1 - (c.re + 2 * r) := by linarith
  have hK : 0 < (1 + r / (1 - (c.re + 2 * r))) ^ 2 := by positivity
  have hmvi := normSq_zetaTailFun_le_integral_ball M hr h1 hz τ
  have hX : ε ^ 2 ≤ ‖zetaTailFun M (z + τ * I)‖ ^ 2 := pow_le_pow_left₀ hε.le hε' 2
  have hJ : ε ^ 2 * (Real.pi * r ^ 2) / (1 + r / (1 - (c.re + 2 * r))) ^ 2 ≤
      ∫ w in ball c (2 * r), ‖zetaTailFun M (w + τ * I)‖ ^ 2 := by
    rw [div_le_iff₀ hK]
    have h := hX.trans hmvi
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at h
    linarith [h]
  show ENNReal.ofReal _ ≤ discTailEnergy M c r τ
  unfold discTailEnergy
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_normSq_zetaTailFun_shift_ball M h1 τ)
    (Eventually.of_forall fun w => by
      show (0 : ℝ) ≤ ‖zetaTailFun M (w + τ * I)‖ ^ 2
      positivity)]
  exact ENNReal.ofReal_le_ofReal hJ

/-! ## 6. Tonelli and Markov on a dyadic window of heights -/

/-- Vertical window integral of the shifted tail at one point `w` of the doubled disc, bounded by
the uniform window bound at the abscissa `Re w`. -/
theorem lintegral_window_shiftedTail_le (M : ℕ) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (h1 : c.re + 2 * r < 1) {V B : ℝ} (hV : 4 * (|c.im| + 2 * r) ≤ V)
    (hB : ∀ σ ∈ Icc (c.re - 2 * r) (c.re + 2 * r),
      (∫ t in V / 4..2 * V, ‖zetaDirichletTail M σ t‖ ^ 2) ≤ B)
    {w : ℂ} (hw : w ∈ ball c (2 * r)) :
    (∫⁻ τ in Icc (V / 2) V, ENNReal.ofReal (‖zetaTailFun M (w + τ * I)‖ ^ 2)) ≤
      ENNReal.ofReal B := by
  have hK0 : 0 ≤ |c.im| + 2 * r := by positivity
  have hV0 : 0 ≤ V := by linarith
  have hwre : w.re ∈ Icc (c.re - 2 * r) (c.re + 2 * r) :=
    ⟨(re_gt_of_mem_ball hw).le, (re_lt_of_mem_ball hw).le⟩
  have hwim : |w.im| ≤ |c.im| + 2 * r := by
    have h := im_sub_abs_lt_of_mem_ball hw
    have h2 := abs_sub_abs_le_abs_sub w.im c.im
    linarith
  have hne : w.re ≠ 1 := ne_of_lt (by linarith [re_lt_of_mem_ball hw])
  set g : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (‖zetaDirichletTail M w.re t‖ ^ 2) with hg
  have hshift : ∀ τ : ℝ, ENNReal.ofReal (‖zetaTailFun M (w + τ * I)‖ ^ 2) = g (τ + w.im) := by
    intro τ
    rw [zetaTailFun_add_mul_I, add_comm]
  have htrans : (∫⁻ τ in Icc (V / 2) V, g (τ + w.im)) =
      ∫⁻ t in Icc (V / 2 + w.im) (V + w.im), g t := by
    rw [← lintegral_indicator measurableSet_Icc, ← lintegral_indicator measurableSet_Icc]
    calc (∫⁻ τ, (Icc (V / 2) V).indicator (fun τ => g (τ + w.im)) τ)
        = ∫⁻ τ, (Icc (V / 2 + w.im) (V + w.im)).indicator g (τ + w.im) := by
          congr 1
          funext τ
          by_cases hτ : τ ∈ Icc (V / 2) V
          · have hτ' : τ + w.im ∈ Icc (V / 2 + w.im) (V + w.im) :=
              ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
            rw [indicator_of_mem hτ, indicator_of_mem hτ']
          · have hτ' : τ + w.im ∉ Icc (V / 2 + w.im) (V + w.im) := by
              intro h
              exact hτ ⟨by linarith [h.1], by linarith [h.2]⟩
            rw [indicator_of_notMem hτ, indicator_of_notMem hτ']
      _ = ∫⁻ t, (Icc (V / 2 + w.im) (V + w.im)).indicator g t :=
          lintegral_add_right_eq_self _ _
  simp_rw [hshift]
  rw [htrans]
  have hsub : Icc (V / 2 + w.im) (V + w.im) ⊆ Icc (V / 4) (2 * V) := by
    intro t ht
    have ha := abs_le.mp hwim
    constructor <;> linarith [ht.1, ht.2, ha.1, ha.2]
  have hint : IntegrableOn (fun t => ‖zetaDirichletTail M w.re t‖ ^ 2) (Icc (V / 4) (2 * V)) :=
    ((continuous_zetaDirichletTail M hne).norm.pow 2).continuousOn.integrableOn_compact
      isCompact_Icc
  calc (∫⁻ t in Icc (V / 2 + w.im) (V + w.im), g t)
      ≤ ∫⁻ t in Icc (V / 4) (2 * V), g t := lintegral_mono_set hsub
    _ = ENNReal.ofReal (∫ t in Icc (V / 4) (2 * V), ‖zetaDirichletTail M w.re t‖ ^ 2) :=
        (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun t => by
          show (0 : ℝ) ≤ ‖zetaDirichletTail M w.re t‖ ^ 2
          positivity)).symm
    _ = ENNReal.ofReal (∫ t in V / 4..2 * V, ‖zetaDirichletTail M w.re t‖ ^ 2) := by
        rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]
    _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (hB w.re hwre)

/-- **Markov bound on a dyadic window.**  If the window mean squares on `[V/4, 2V]` are at most
`B` for every abscissa of the doubled disc, the bad heights in `[V/2, V]` have measure at most
`4 K B / ε²`, `K = (1 + r/(1 − (Re c + 2r)))²`. -/
theorem volume_discTailBadSet_window_le (M : ℕ) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (h1 : c.re + 2 * r < 1) {ε : ℝ} (hε : 0 < ε) {V B : ℝ} (hV : 4 * (|c.im| + 2 * r) ≤ V)
    (hB0 : 0 ≤ B)
    (hB : ∀ σ ∈ Icc (c.re - 2 * r) (c.re + 2 * r),
      (∫ t in V / 4..2 * V, ‖zetaDirichletTail M σ t‖ ^ 2) ≤ B) :
    volume (discTailBadSet M c r ε ∩ Icc (V / 2) V) ≤
      ENNReal.ofReal (4 * (1 + r / (1 - (c.re + 2 * r))) ^ 2 / ε ^ 2 * B) := by
  set K : ℝ := (1 + r / (1 - (c.re + 2 * r))) ^ 2 with hK
  have hL : 0 < 1 - (c.re + 2 * r) := by linarith
  have hK0 : 0 < K := by positivity
  set a : ℝ := ε ^ 2 * (Real.pi * r ^ 2) / K with ha
  have ha0 : 0 < a := by positivity
  have hmarkov : volume ({τ : ℝ | ENNReal.ofReal a ≤ discTailEnergy M c r τ} ∩ Icc (V / 2) V) ≤
      (∫⁻ τ in Icc (V / 2) V, discTailEnergy M c r τ) / ENNReal.ofReal a := by
    rw [← Measure.restrict_apply' measurableSet_Icc,
      ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr ha0).ne')
        (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact mul_meas_ge_le_lintegral₀ (measurable_discTailEnergy M c r).aemeasurable _
  have hton : (∫⁻ τ in Icc (V / 2) V, discTailEnergy M c r τ) =
      ∫⁻ w in ball c (2 * r), ∫⁻ τ in Icc (V / 2) V,
        ENNReal.ofReal (‖zetaTailFun M (w + τ * I)‖ ^ 2) := by
    unfold discTailEnergy
    exact lintegral_lintegral_swap (measurable_shiftedTailEnergyIntegrand M).aemeasurable
  have hinner : (∫⁻ w in ball c (2 * r), ∫⁻ τ in Icc (V / 2) V,
      ENNReal.ofReal (‖zetaTailFun M (w + τ * I)‖ ^ 2)) ≤
      ENNReal.ofReal B * volume (ball c (2 * r)) := by
    calc (∫⁻ w in ball c (2 * r), ∫⁻ τ in Icc (V / 2) V,
          ENNReal.ofReal (‖zetaTailFun M (w + τ * I)‖ ^ 2))
        ≤ ∫⁻ w in ball c (2 * r), ENNReal.ofReal B :=
          setLIntegral_mono' measurableSet_ball fun w hw =>
            lintegral_window_shiftedTail_le M hr h1 hV hB hw
      _ = ENNReal.ofReal B * volume (ball c (2 * r)) := setLIntegral_const _ _
  have hvol : volume (ball c (2 * r)) = ENNReal.ofReal (Real.pi * (2 * r) ^ 2) := by
    rw [Complex.volume_ball, ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow (by positivity),
      mul_comm, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
  calc volume (discTailBadSet M c r ε ∩ Icc (V / 2) V)
      ≤ volume ({τ : ℝ | ENNReal.ofReal a ≤ discTailEnergy M c r τ} ∩ Icc (V / 2) V) :=
        measure_mono (inter_subset_inter_left _ (discTailBadSet_subset_energy_ge M hr h1 hε))
    _ ≤ (∫⁻ τ in Icc (V / 2) V, discTailEnergy M c r τ) / ENNReal.ofReal a := hmarkov
    _ ≤ ENNReal.ofReal B * ENNReal.ofReal (Real.pi * (2 * r) ^ 2) / ENNReal.ofReal a := by
        rw [hton, ← hvol]
        exact ENNReal.div_le_div_right hinner _
    _ = ENNReal.ofReal (4 * K / ε ^ 2 * B) := by
        rw [← ENNReal.ofReal_mul hB0, ← ENNReal.ofReal_div_of_pos ha0]
        congr 1
        rw [ha]
        field_simp
        ring

/-! ## 7. Window density bounds give prefix density bounds -/

/-- If `S ∩ [V/2, V]` eventually has measure `≤ β V`, then `S ∩ [0, T]` eventually has measure
`≤ (2β + κ) T` for every `κ > 0`. -/
theorem eventually_volume_inter_Icc_le_of_dyadic_window {S : Set ℝ} {β : ℝ} (hβ : 0 ≤ β)
    (hwin : ∀ᶠ V : ℝ in atTop, volume (S ∩ Icc (V / 2) V) ≤ ENNReal.ofReal (β * V))
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ T : ℝ in atTop, volume (S ∩ Icc 0 T) ≤ ENNReal.ofReal ((2 * β + κ) * T) := by
  have hstep : ∀ q : ℕ, ∀ᶠ V : ℝ in atTop,
      volume (S ∩ Icc 0 V) ≤ ENNReal.ofReal (V / 2 ^ q + 2 * β * V) := by
    intro q
    induction q with
    | zero =>
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with V hV
      calc volume (S ∩ Icc 0 V) ≤ volume (Icc 0 V) := measure_mono inter_subset_right
        _ = ENNReal.ofReal V := by rw [Real.volume_Icc, sub_zero]
        _ ≤ ENNReal.ofReal (V / 2 ^ 0 + 2 * β * V) := by
          apply ENNReal.ofReal_le_ofReal
          rw [pow_zero, div_one]
          nlinarith [mul_nonneg hβ hV]
    | succ q ih =>
      obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp ih
      filter_upwards [hwin, eventually_ge_atTop (2 * max W₀ 0)] with V hV hVbig
      have hW : W₀ ≤ V / 2 := by linarith [le_max_left W₀ 0]
      have hV0 : 0 ≤ V := by linarith [le_max_right W₀ 0]
      have hsplit : S ∩ Icc 0 V ⊆ S ∩ Icc 0 (V / 2) ∪ S ∩ Icc (V / 2) V := by
        rw [← inter_union_distrib_left]
        refine inter_subset_inter_right _ fun x hx => ?_
        rcases le_total x (V / 2) with h | h
        · exact Or.inl ⟨hx.1, h⟩
        · exact Or.inr ⟨h, hx.2⟩
      calc volume (S ∩ Icc 0 V)
          ≤ volume (S ∩ Icc 0 (V / 2)) + volume (S ∩ Icc (V / 2) V) :=
            (measure_mono hsplit).trans (measure_union_le _ _)
        _ ≤ ENNReal.ofReal (V / 2 / 2 ^ q + 2 * β * (V / 2)) + ENNReal.ofReal (β * V) :=
            add_le_add (hW₀ _ hW) hV
        _ = ENNReal.ofReal (V / 2 / 2 ^ q + 2 * β * (V / 2) + β * V) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        _ ≤ ENNReal.ofReal (V / 2 ^ (q + 1) + 2 * β * V) := by
            apply ENNReal.ofReal_le_ofReal
            rw [pow_succ, show V / 2 / 2 ^ q = V / (2 ^ q * 2) by rw [div_div, mul_comm]]
            linarith
  obtain ⟨q, hq⟩ := exists_pow_lt_of_lt_one hκ (show (1 / 2 : ℝ) < 1 by norm_num)
  filter_upwards [hstep q, eventually_ge_atTop (0 : ℝ)] with T hT hT0
  refine hT.trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 : T / 2 ^ q ≤ κ * T := by
    rw [div_eq_mul_one_div, one_div, ← inv_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (by rw [inv_eq_one_div]; exact hq.le) hT0
  linarith

/-! ## 8. The disc-uniform Carlson tail law -/

/-- **Disc-uniform Carlson tail law.**  Let `closedBall c (2r)` lie in `1/2 < Re s < 1`.  For all
large `M`, the heights `τ ∈ [0, T]` at which `|ζ(z + iτ) − head_M(z + iτ)| ≥ ε` for some
`z ∈ closedBall c r` have measure at most `δ T` for all large `T`. -/
theorem eventually_eventually_volume_discTailBadSet_le {c : ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < c.re - 2 * r) (h1 : c.re + 2 * r < 1) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ M : ℕ in atTop, ∀ᶠ T : ℝ in atTop,
      volume (discTailBadSet M c r ε ∩ Icc 0 T) ≤ ENNReal.ofReal (δ * T) := by
  set K : ℝ := (1 + r / (1 - (c.re + 2 * r))) ^ 2 with hK
  have hL : 0 < 1 - (c.re + 2 * r) := by linarith
  have hK0 : 0 < K := by positivity
  set η : ℝ := δ * ε ^ 2 / (56 * K) with hη
  have hη0 : 0 < η := by positivity
  filter_upwards [(tendsto_zetaCoefficientTailMass h0).eventually (gt_mem_nhds (half_pos hη0))]
    with M hM
  have hτ0 := zetaCoefficientTailMass_nonneg M (c.re - 2 * r)
  set β : ℝ := 7 * K / ε ^ 2 * (2 * zetaCoefficientTailMass M (c.re - 2 * r) + η) with hβ
  have hβ0 : 0 ≤ β := mul_nonneg (by positivity) (by linarith)
  have hβle : β ≤ δ / 4 := by
    have h2 : 2 * zetaCoefficientTailMass M (c.re - 2 * r) + η ≤ 2 * η := by linarith
    calc β ≤ 7 * K / ε ^ 2 * (2 * η) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = δ / 4 := by
          rw [hη]
          field_simp
          ring
  have hwin : ∀ᶠ V : ℝ in atTop,
      volume (discTailBadSet M c r ε ∩ Icc (V / 2) V) ≤ ENNReal.ofReal (β * V) := by
    filter_upwards [eventually_uniform_window_zetaDirichletTail_meanSquare_le M h0
      (by linarith) h1 hη0, eventually_ge_atTop (4 * (|c.im| + 2 * r)),
      eventually_ge_atTop (0 : ℝ)] with V hVwin hV4 hV0
    have hB0 : 0 ≤ 7 * V / 4 * (2 * zetaCoefficientTailMass M (c.re - 2 * r) + η) :=
      mul_nonneg (by positivity) (by linarith)
    refine (volume_discTailBadSet_window_le M hr h1 hε hV4 hB0 hVwin).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [hβ]
    ring
  filter_upwards [eventually_volume_inter_Icc_le_of_dyadic_window hβ0 hwin (half_pos hδ),
    eventually_ge_atTop (0 : ℝ)] with T hT hT0
  refine hT.trans (ENNReal.ofReal_le_ofReal ?_)
  have := mul_le_mul_of_nonneg_right (show 2 * β + δ / 2 ≤ δ by linarith) hT0
  linarith

/-- **Disc-uniform Abel-centered return heights have density one.**  For all large `M` the
complement of `abelCenteredZetaTailReturnSet M (closedBall c r) ε` has asymptotic density at
most `δ`: the fractional-part term is uniformly `O(M^{-Re c + 2r})` on the disc, and the shifted
Carlson tail is controlled by `eventually_eventually_volume_discTailBadSet_le`. -/
theorem eventually_eventually_volume_not_mem_abelCenteredZetaTailReturnSet_le {c : ℂ} {r : ℝ}
    (hr : 0 < r) (h0 : 1 / 2 < c.re - 2 * r) (h1 : c.re + 2 * r < 1) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) :
    ∀ᶠ M : ℕ in atTop, ∀ᶠ T : ℝ in atTop,
      volume ({τ : ℝ | τ ∉ abelCenteredZetaTailReturnSet M (closedBall c r) ε} ∩ Icc 0 T) ≤
        ENNReal.ofReal (δ * T) := by
  have hσ₀ : 0 < c.re - 2 * r := by linarith
  have hdecay : Tendsto (fun M : ℕ => (‖c‖ + r) * ((M : ℝ) ^ (-(c.re - 2 * r)) / (c.re - 2 * r)))
      atTop (𝓝 0) := by
    have h0' : Tendsto (fun M : ℕ => (M : ℝ) ^ (-(c.re - 2 * r))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hσ₀).comp tendsto_natCast_atTop_atTop
    simpa using (h0'.div_const (c.re - 2 * r)).const_mul (‖c‖ + r)
  filter_upwards [eventually_eventually_volume_discTailBadSet_le hr h0 h1 (half_pos hε) hδ,
    eventually_ge_atTop 1, hdecay.eventually (gt_mem_nhds (half_pos hε))] with M hM hM1 hMfr
  refine hM.mono fun T hT => le_trans (measure_mono (inter_subset_inter_left _ ?_)) hT
  intro τ hτ
  simp only [abelCenteredZetaTailReturnSet, mem_setOf_eq, not_forall, not_lt] at hτ
  obtain ⟨z, hz, hzε⟩ := hτ
  refine ⟨z, hz, ?_⟩
  have hzre : c.re - r ≤ z.re := re_ge_of_mem_closedBall hz
  have hz0 : 0 < z.re := by linarith
  have hz1 : z ≠ 1 := by
    intro h
    have := re_le_of_mem_closedBall hz
    rw [h, Complex.one_re] at this
    linarith
  have hfr : ‖abelCenteredZetaTail M z τ - zetaDirichletTail M z.re (z.im + τ)‖ ≤
      ‖z‖ * ((M : ℝ) ^ (-z.re) / z.re) :=
    norm_abelCenteredZetaTail_sub_shiftedTail_le hM1 hz0 hz1 τ
  have hfr2 : ‖z‖ * ((M : ℝ) ^ (-z.re) / z.re) ≤
      (‖c‖ + r) * ((M : ℝ) ^ (-(c.re - 2 * r)) / (c.re - 2 * r)) := by
    have hM1' : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    apply mul_le_mul _ _ (by positivity) (by positivity)
    · calc ‖z‖ = ‖(z - c) + c‖ := by ring_nf
        _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
        _ ≤ ‖c‖ + r := by linarith [mem_closedBall_iff_norm.mp hz]
    · calc (M : ℝ) ^ (-z.re) / z.re ≤ (M : ℝ) ^ (-(c.re - 2 * r)) / z.re :=
            div_le_div_of_nonneg_right
              (Real.rpow_le_rpow_of_exponent_le hM1' (by linarith)) hz0.le
        _ ≤ (M : ℝ) ^ (-(c.re - 2 * r)) / (c.re - 2 * r) :=
            div_le_div_of_nonneg_left (by positivity) hσ₀ (by linarith)
  rw [zetaTailFun_add_mul_I]
  have := norm_sub_norm_le (abelCenteredZetaTail M z τ) (zetaDirichletTail M z.re (z.im + τ))
  linarith

end RHTower
