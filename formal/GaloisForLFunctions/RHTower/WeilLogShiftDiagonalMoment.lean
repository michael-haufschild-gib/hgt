import GaloisForLFunctions.RHTower.WeilTailPanelPositiveCompletion
import GaloisForLFunctions.RHTower.WeilFullConeSummableExcessRigidity

/-!
# A moving log-shift probe exposes the summable majorant boundary

For summable normalized deviation, the probe with window `k` and shift
`log (k + 2)` tends to minus four times the signed Riemann-kernel moment.
Thus eventual nonnegativity of this single probe per window excludes every
strict coefficient majorant with summable excess. No full Weil positivity or
Riemann hypothesis enters the limit or the rigidity statement.
-/

open Complex MeasureTheory Filter Topology Set Zeta23
open RHTower.WeilExcess

noncomputable section

namespace RHTower

/-- One moving member of the countable log-shift panel, valid for every `k ≥ 1`. -/
def weilLogShiftDiagonalProbe (lam : ℕ → ℝ) (k : ℕ) : ℝ :=
  (weilFullFunctional lam (EF.weilTest
    (logShiftRiemannDifference k (Real.log (k + 2 : ℕ)))
    (logShiftRiemannDifference k (Real.log (k + 2 : ℕ))))).re

private theorem diagonal_index_bound {k : ℕ} (hk : 1 ≤ k) :
    ((k + 2 : ℕ) : ℝ) ≤ Real.exp (2 * (k : ℝ)) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h := Real.add_one_le_exp (2 * (k : ℝ))
  push_cast
  linarith only [hkR, h]

private def diagonalPair (k : ℕ) (y : ℝ) : ℝ :=
  4 * truncatedRiemannAutocorr k y -
    2 * truncatedRiemannAutocorr k (y + Real.log (k + 2 : ℕ)) -
    2 * truncatedRiemannAutocorr k (y - Real.log (k + 2 : ℕ))

private theorem diagonalPair_abs_le (k : ℕ) (y : ℝ) :
    |diagonalPair k y| ≤ 4 * riemannAutocorr 0 := by
  have h := norm_logShiftRiemannPair_le k (Real.log (k + 2 : ℕ)) y
  rwa [logShiftRiemannPair_eq, Complex.norm_real, Real.norm_eq_abs] at h

private theorem tendsto_diagonalPair (y : ℝ) :
    Tendsto (fun k : ℕ => diagonalPair k y) atTop (𝓝 (4 * riemannAutocorr y)) := by
  have hlog : Tendsto (fun k : ℕ => Real.log (k + 2 : ℕ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
  have hplus : Tendsto (fun k : ℕ => |y + Real.log (k + 2 : ℕ)|) atTop atTop := by
    refine tendsto_atTop.mpr fun b => ?_
    filter_upwards [hlog.eventually_ge_atTop (|y| + b)] with k hk
    linarith only [hk, neg_abs_le y, le_abs_self (y + Real.log (k + 2 : ℕ))]
  have hminus : Tendsto (fun k : ℕ => |y - Real.log (k + 2 : ℕ)|) atTop atTop := by
    refine tendsto_atTop.mpr fun b => ?_
    filter_upwards [hlog.eventually_ge_atTop (|y| + b)] with k hk
    linarith only [hk, le_abs_self y, neg_abs_le (y - Real.log (k + 2 : ℕ))]
  have hvanish (z : ℕ → ℝ) (hz : Tendsto (fun k => |z k|) atTop atTop) :
      Tendsto (fun k : ℕ => truncatedRiemannAutocorr k (z k)) atTop (𝓝 0) := by
    obtain ⟨C, hC0, hC⟩ := exists_riemannAutocorr_le
    refine squeeze_zero' (Eventually.of_forall fun k => truncatedRiemannAutocorr_nonneg _ _)
      (Eventually.of_forall fun k =>
        (truncatedRiemannAutocorr_le_riemannAutocorr _ _).trans (hC _)) ?_
    have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (hz.const_mul_atTop (by norm_num : (0 : ℝ) < 2))).const_mul C
    simpa only [Function.comp_def, mul_zero] using h
  have h0 := ((tendsto_truncatedRiemannAutocorr y).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 4
  have h1 := (hvanish _ hplus).const_mul 2
  have h2 := (hvanish _ hminus).const_mul 2
  simpa only [diagonalPair, Function.comp_def, mul_zero, sub_zero] using (h0.sub h1).sub h2

private theorem tendsto_diagonal_zeroSide :
    Tendsto (fun k : ℕ => (zetaZeroConfig.W
      (logShiftRiemannDifference k (Real.log (k + 2 : ℕ)))
      (logShiftRiemannDifference k (Real.log (k + 2 : ℕ)))).re) atTop (𝓝 0) := by
  let E : ℝ → ℝ := fun L => (5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2
  have hE0 (L : ℝ) : 0 ≤ E L :=
    mul_nonneg (mul_nonneg (by norm_num) zetaInvSqSum_nonneg) (sq_nonneg _)
  have hE : Tendsto (fun k : ℕ => Real.exp (2 * (k : ℝ)) * E k) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨L, hL⟩ := exists_exp_mul_nearRadicalEnergy_le (ε := ε / 2) (by positivity)
    refine ⟨⌈L⌉₊, fun k hk => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hE0 _))]
    have hLk : L ≤ (k : ℝ) := (Nat.le_ceil L).trans (by exact_mod_cast hk)
    exact (hL k hLk).trans_lt (by linarith)
  have hbound : ∀ᶠ k : ℕ in atTop,
      ‖(zetaZeroConfig.W (logShiftRiemannDifference k (Real.log (k + 2 : ℕ)))
        (logShiftRiemannDifference k (Real.log (k + 2 : ℕ)))).re‖ ≤
          4 * (Real.exp (2 * (k : ℝ)) * E k) := by
    obtain ⟨Λ, _, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hlog0 := Real.log_natCast_nonneg (k + 2)
    have hlog : Real.log (k + 2 : ℕ) ≤ 2 * (k : ℝ) :=
      (Real.log_le_iff_le_exp (by positivity)).mpr (diagonal_index_bound hk)
    have hfac : (1 + Real.exp (Real.log (k + 2 : ℕ) / 2)) ^ 2 ≤
        4 * Real.exp (2 * (k : ℝ)) := by
      have he1 : 1 ≤ Real.exp (k : ℝ) := Real.one_le_exp (Nat.cast_nonneg _)
      have helog : Real.exp (Real.log (k + 2 : ℕ) / 2) ≤ Real.exp (k : ℝ) :=
        Real.exp_le_exp.mpr (by linarith only [hlog])
      have hs := sq_le_sq₀ (by positivity : (0 : ℝ) ≤ 1 +
        Real.exp (Real.log (k + 2 : ℕ) / 2)) (by positivity : (0 : ℝ) ≤ 2 * Real.exp (k : ℝ))
      have hsq := hs.mpr (by linarith only [he1, helog])
      have heq : Real.exp (2 * (k : ℝ)) = Real.exp (k : ℝ) ^ 2 := by
        rw [show 2 * (k : ℝ) = (k : ℝ) + k by ring, Real.exp_add, pow_two]
      rw [heq]
      nlinarith only [hsq]
    calc _ ≤ ‖zetaZeroConfig.W (logShiftRiemannDifference k (Real.log (k + 2 : ℕ)))
          (logShiftRiemannDifference k (Real.log (k + 2 : ℕ)))‖ := by
          rw [Real.norm_eq_abs]
          exact Complex.abs_re_le_norm _
      _ ≤ (1 + Real.exp (Real.log (k + 2 : ℕ) / 2)) ^ 2 * E k :=
        norm_W_logShiftRiemannDifference_le k hlog0 hΛ
      _ ≤ (4 * Real.exp (2 * (k : ℝ))) * E k := mul_le_mul_of_nonneg_right hfac (hE0 _)
      _ = _ := by ring
  exact squeeze_zero_norm' hbound (by simpa only [mul_zero] using hE.const_mul 4)

/-- Exact signed moment read by one escaping log-shift probe per integer window. -/
theorem tendsto_weilLogShiftDiagonalProbe {lam : ℕ → ℝ}
    (hs : Summable fun n => |weilDeviation lam n|) :
    Tendsto (weilLogShiftDiagonalProbe lam) atTop
      (𝓝 (-4 * ∑' n : ℕ, weilDeviation lam n * riemannAutocorr (Real.log n))) := by
  have hsum : Tendsto (fun k : ℕ => ∑' n : ℕ, weilDeviation lam n * diagonalPair k (Real.log n))
      atTop (𝓝 (∑' n : ℕ, weilDeviation lam n * (4 * riemannAutocorr (Real.log n)))) := by
    refine tendsto_tsum_of_dominated_convergence (hs.mul_right (4 * riemannAutocorr 0))
      (fun n => (tendsto_diagonalPair _).const_mul _) (Eventually.of_forall fun k n => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (diagonalPair_abs_le k _) (abs_nonneg _)
  have hformula (k : ℕ) : weilLogShiftDiagonalProbe lam k =
      (zetaZeroConfig.W (logShiftRiemannDifference k (Real.log (k + 2 : ℕ)))
        (logShiftRiemannDifference k (Real.log (k + 2 : ℕ)))).re -
          ∑' n : ℕ, weilDeviation lam n * diagonalPair k (Real.log n) := by
    let f := logShiftRiemannDifference k (Real.log (k + 2 : ℕ))
    have hfc : HasCompactSupport f := hasCompactSupport_logShiftRiemannDifference _ _
    have hgc := EF.weilTest_hasCompactSupport hfc hfc
    have hterms := summable_primeAtoms (weilDeviation lam) hgc
    change (weilFullFunctional lam (EF.weilTest f f)).re = _
    rw [weilFullFunctional_eq_sub lam hgc, ← weilFullFunctional_vonMangoldt,
      ← zeta_W_eq_weilFullFunctional (contDiff_logShiftRiemannDifference _ _) hfc, Complex.sub_re]
    congr 1
    change (∑' n : ℕ, ((weilDeviation lam n : ℝ) : ℂ) *
      (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n))).re = _
    rw [Complex.re_tsum hterms]
    refine tsum_congr fun n => ?_
    rw [show EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n) =
      ((diagonalPair k (Real.log n) : ℝ) : ℂ) from logShiftRiemannPair_eq _ _ _,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have hmoment : (∑' n : ℕ, weilDeviation lam n * (4 * riemannAutocorr (Real.log n))) =
      4 * ∑' n : ℕ, weilDeviation lam n * riemannAutocorr (Real.log n) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by ring
  have h := tendsto_diagonal_zeroSide.sub hsum
  rw [hmoment, zero_sub, ← neg_mul] at h
  exact h.congr fun k => (hformula k).symm

/-- Eventual positivity of the diagonal probes forces a nonpositive signed kernel moment. -/
theorem weilLogShiftDiagonal_moment_nonpos {lam : ℕ → ℝ}
    (hs : Summable fun n => |weilDeviation lam n|)
    (hpos : ∀ᶠ k : ℕ in atTop, 0 ≤ weilLogShiftDiagonalProbe lam k) :
    (∑' n : ℕ, weilDeviation lam n * riemannAutocorr (Real.log n)) ≤ 0 := by
  have h := ge_of_tendsto (tendsto_weilLogShiftDiagonalProbe hs) hpos
  linarith only [h]

/-- A summable coefficient majorant is identified by eventual nonnegativity of only
the single diagonal probe in each window. -/
theorem eq_vonMangoldt_of_eventually_diagonal_nonneg_of_summable_excess {lam : ℕ → ℝ}
    (hge : ∀ n : ℕ, 2 ≤ n → (ArithmeticFunction.vonMangoldt n : ℝ) ≤ lam n)
    (hexc : Summable fun n => max (lam n - (ArithmeticFunction.vonMangoldt n : ℝ)) 0 /
      Real.sqrt n)
    (hpos : ∀ᶠ k : ℕ in atTop, 0 ≤ weilLogShiftDiagonalProbe lam k) :
    ∀ n : ℕ, 2 ≤ n → lam n = (ArithmeticFunction.vonMangoldt n : ℝ) := by
  have ha (n : ℕ) : 0 ≤ weilDeviation lam n := by
    unfold weilDeviation
    split_ifs with hn
    · exact div_nonneg (sub_nonneg.mpr (hge n hn)) (Real.sqrt_nonneg _)
    · exact le_rfl
  have hs : Summable fun n => |weilDeviation lam n| := by
    refine (summable_deviationExcess hexc).congr fun n => ?_
    rw [deviationExcess, max_eq_left (ha n), abs_of_nonneg (ha n)]
  have hm := weilLogShiftDiagonal_moment_nonpos hs hpos
  have hsm : Summable fun n => weilDeviation lam n * riemannAutocorr (Real.log n) := by
    refine (hs.mul_right (riemannAutocorr 0)).of_norm_bounded fun n => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (riemannAutocorr_nonneg _)]
    exact mul_le_mul_of_nonneg_left (riemannAutocorr_le_zero _) (abs_nonneg _)
  intro n hn
  have hzero : weilDeviation lam n * riemannAutocorr (Real.log n) = 0 := by
    apply le_antisymm
    · exact (hsm.le_tsum n fun j _ => mul_nonneg (ha j) (riemannAutocorr_nonneg _)).trans hm
    · exact mul_nonneg (ha n) (riemannAutocorr_nonneg _)
  have han : weilDeviation lam n = 0 :=
    (mul_eq_zero.mp hzero).resolve_right (riemannAutocorr_pos _).ne'
  rw [weilDeviation, if_pos hn] at han
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr
    (by exact_mod_cast (show 0 < n by omega))).ne'
  exact sub_eq_zero.mp ((div_eq_zero_iff.mp han).resolve_right hsqrt)

/-- Countable log-shift positivity is sufficient for order rigidity from above
inside the summable-excess sector. -/
theorem weilLogShiftSummableMajorants_subset_exact :
    {lam : ℕ → ℝ |
      (∀ n : ℕ, 2 ≤ n → (ArithmeticFunction.vonMangoldt n : ℝ) ≤ lam n) ∧
      (Summable fun n => max (lam n - (ArithmeticFunction.vonMangoldt n : ℝ)) 0 / Real.sqrt n) ∧
      WeilLogShiftTestsPositive lam} ⊆
    {lam | ∀ n : ℕ, 2 ≤ n → lam n = (ArithmeticFunction.vonMangoldt n : ℝ)} := by
  rintro lam ⟨hge, hexc, hpos⟩
  apply eq_vonMangoldt_of_eventually_diagonal_nonneg_of_summable_excess hge hexc
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact hpos k (k + 2) (by omega) (diagonal_index_bound hk)

/-- Strict majorants satisfying every countable log-shift test exist, but necessarily
pay infinite total normalized excess. The prescribed excess at `2` is arbitrary. -/
theorem exists_weilLogShift_majorant_infinite_excess (t : ℝ) :
    ∃ lam : ℕ → ℝ,
      WeilLogShiftTestsPositive lam ∧
      (∀ n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) ≤ lam n) ∧
      lam 2 = (ArithmeticFunction.vonMangoldt 2 : ℝ) + Real.exp t * Real.sqrt 2 ∧
      ¬ Summable (fun n => max (lam n - (ArithmeticFunction.vonMangoldt n : ℝ)) 0 /
        Real.sqrt n) := by
  let seed : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) +
    if n = 2 then Real.exp t * Real.sqrt 2 else 0
  obtain ⟨lam, hpos, hhead, hle⟩ := exists_weilLogShiftTestsPositive_prescribed_head seed
  have hge (n : ℕ) : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ lam n := by
    have hseed : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ seed n := by
      dsimp only [seed]
      split_ifs
      · exact le_add_of_nonneg_right (by positivity)
      · exact le_add_of_nonneg_right le_rfl
    exact hseed.trans (hle n)
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by
    have h := Real.add_one_le_exp (2 : ℝ)
    linarith only [h]
  have hv : lam 2 = (ArithmeticFunction.vonMangoldt 2 : ℝ) + Real.exp t * Real.sqrt 2 :=
    hhead 2 h2
  refine ⟨lam, hpos, hge, hv, ?_⟩
  intro hs
  have heq := weilLogShiftSummableMajorants_subset_exact ⟨fun n _ => hge n, hs, hpos⟩
    2 (by norm_num)
  have hd : 0 < Real.exp t * Real.sqrt 2 := by positivity
  linarith only [heq, hv, hd]

end RHTower

end
