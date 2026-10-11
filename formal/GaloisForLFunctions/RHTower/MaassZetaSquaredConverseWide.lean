import GaloisForLFunctions.RHTower.MaassZetaSquaredConverse

/-!
# The `ζ²` converse theorem at abscissa `3/2`

The converse theorems of `MaassZetaSquaredConverse` assume that `G(s) = Σ g_n n^{−s}` converges
absolutely on `Re s > 1`.  Here absolute convergence is assumed only on `Re s > 3/2`, together with
boundedness of `Λ̂(s) = s²(s−1)²Γ_ℝ(s)²G(s)` on `−3/4 ≤ Re s ≤ 7/4`.

The theta relation `Θ(y) − ε y^{−1}Θ(1/y) = ¼[(b − a log y)/y − ε(b + a log y)]` is proved by the
same two-line Mellin argument as `MaassThetaRelation.kTheta_relation_sign`, now on the lines
`Re s = 7/4` and `Re s = −3/4`.  Both lie in the strip `−1 < Re s < 2` where the Gamma corrections
are holomorphic; the Cauchy estimate for `γ₁` uses circles of radius `1/4`.

* `coeff_eq_zero_of_odd_functional_equation_wide`: `Λ̂(1 − s) = −Λ̂(s)` forces `G = 0`.
* `coeff_eq_divisorCount_of_functional_equation_wide`: `Λ̂(1 − s) = Λ̂(s)` and `g₁ = 1` force
  `G = ζ²`.
-/

open Complex Set Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.MaassZetaSquaredConverseWide

open MaassThetaMellin MaassGammaCorrections MaassThetaRelation MaassBesselSeries BesselKZero
  MaassConverseLevelOne MaassConstantTermWronskian MaassLevelOneCuspVanishing
  MaassZetaSquaredConverse GaloisForLFunctions.RHTower.SelbergMaassMean

variable {g : ℕ → ℂ}

/-! ## Growth and the Mellin transform of `Θ` -/

/-- Absolute convergence beyond `3/2` gives `‖g_{n+1}‖ ≤ M (n + 1)²`. -/
theorem exists_norm_le_sq_wide
    (hsum : ∀ σ : ℝ, 3 / 2 < σ → Summable fun n : ℕ => ‖g n‖ * (n : ℝ) ^ (-σ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ‖g (n + 1)‖ ≤ M * ((n : ℝ) + 1) ^ 2 := by
  have hs := hsum 2 (by norm_num)
  have hnn : ∀ n : ℕ, 0 ≤ ‖g n‖ * (n : ℝ) ^ (-(2 : ℝ)) := fun n => by positivity
  refine ⟨∑' n : ℕ, ‖g n‖ * (n : ℝ) ^ (-(2 : ℝ)), tsum_nonneg hnn, fun n => ?_⟩
  have hle := hs.le_tsum (n + 1) (fun j _ => hnn j)
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hrp : ((n + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)) * ((n : ℝ) + 1) ^ 2 = 1 := by
    rw [show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg hpos.le,
      ← Real.rpow_natCast]
    push_cast
    rw [inv_mul_cancel₀ (by positivity)]
  calc ‖g (n + 1)‖ = ‖g (n + 1)‖ * ((n + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)) * ((n : ℝ) + 1) ^ 2 := by
        rw [mul_assoc, hrp, mul_one]
    _ ≤ (∑' n : ℕ, ‖g n‖ * (n : ℝ) ^ (-(2 : ℝ))) * ((n : ℝ) + 1) ^ 2 :=
        mul_le_mul_of_nonneg_right hle (by positivity)

theorem polyGrowth_of_summable_wide
    (hsum : ∀ σ : ℝ, 3 / 2 < σ → Summable fun n : ℕ => ‖g n‖ * (n : ℝ) ^ (-σ)) : PolyGrowth g := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_le_sq_wide hsum
  refine ⟨max M ‖g 0‖, le_max_of_le_right (norm_nonneg _), 2, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h := hM m
    have h1 : ((m : ℝ) + 1) ^ 2 ≤ (((m + 1 : ℕ) : ℝ) + 1) ^ 2 := by
      push_cast; nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    calc ‖g (m + 1)‖ ≤ M * ((m : ℝ) + 1) ^ 2 := h
      _ ≤ max M ‖g 0‖ * (((m + 1 : ℕ) : ℝ) + 1) ^ 2 :=
          mul_le_mul (le_max_left _ _) h1 (by positivity) (le_max_of_le_left hM0)

/-- `Θ` is continuous on `(0, ∞)` as soon as `‖g_{n+1}‖ ≤ M (n + 1)²`. -/
theorem continuousOn_kTheta_of_bound {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ n : ℕ, ‖g (n + 1)‖ ≤ M * ((n : ℝ) + 1) ^ 2) :
    ContinuousOn (kTheta g) (Ioi 0) := by
  intro y₀ hy₀
  have hy₀' : (0 : ℝ) < y₀ := hy₀
  have hr : 0 < Real.pi * y₀ := by positivity
  set K : ℝ := Real.exp (Real.pi * y₀) * kMoment 0 (Real.pi * y₀) with hK
  have hK0 : 0 ≤ K := by have := kMoment_nonneg 0 (Real.pi * y₀); positivity
  have hu : Summable fun n : ℕ => M * K * (((n + 1 : ℕ) : ℝ) ^ 2 *
      Real.exp (-(Real.pi * y₀) * ((n + 1 : ℕ) : ℝ))) :=
    ((summable_nat_add_iff 1).mpr (Real.summable_pow_mul_exp_neg_nat_mul 2 hr)).mul_left _
  have hcont : ContinuousOn (kTheta g) (Ioi (y₀ / 2)) := by
    refine continuousOn_tsum (fun n => ?_) hu (fun n y hy => ?_)
    · have hc : ContinuousOn (fun y : ℝ => kMoment 0 (2 * Real.pi * (n + 1) * y)) (Ioi (y₀ / 2)) :=
        (continuousOn_kMoment 0).comp (by fun_prop) (fun y hy => by
          have : (0 : ℝ) < y := lt_trans (by positivity) hy
          show 0 < 2 * Real.pi * (n + 1) * y
          positivity)
      exact continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hc)
    · have hy' : y₀ / 2 < y := hy
      have hle : Real.pi * y₀ ≤ 2 * Real.pi * (n + 1) * y := by
        have : y₀ ≤ 2 * ((n : ℝ) + 1) * y := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
        nlinarith [Real.pi_pos]
      have hKb := kMoment_le_exp_mul 0 hr hle
      have hexp : Real.exp (-(2 * Real.pi * (n + 1) * y - Real.pi * y₀)) ≤
          Real.exp (Real.pi * y₀) * Real.exp (-(Real.pi * y₀) * ((n + 1 : ℕ) : ℝ)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        push_cast
        nlinarith [Real.pi_pos]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (kMoment_nonneg _ _)]
      have hn := hM n
      calc ‖g (n + 1)‖ * kMoment 0 (2 * Real.pi * (n + 1) * y)
          ≤ (M * ((n : ℝ) + 1) ^ 2) * (Real.exp (Real.pi * y₀) *
              Real.exp (-(Real.pi * y₀) * ((n + 1 : ℕ) : ℝ)) * kMoment 0 (Real.pi * y₀)) := by
            refine mul_le_mul hn (hKb.trans ?_) (kMoment_nonneg _ _) (by positivity)
            exact mul_le_mul_of_nonneg_right hexp (kMoment_nonneg _ _)
        _ = M * K * (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-(Real.pi * y₀) * ((n + 1 : ℕ) : ℝ))) := by
            rw [hK]; push_cast; ring
  exact hcont.continuousWithinAt (by simp; linarith) |>.mono_of_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by linarith)))

theorem continuousOn_kTheta_wide
    (hsum : ∀ σ : ℝ, 3 / 2 < σ → Summable fun n : ℕ => ‖g n‖ * (n : ℝ) ^ (-σ)) :
    ContinuousOn (kTheta g) (Ioi 0) := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_le_sq_wide hsum
  exact continuousOn_kTheta_of_bound hM0 hM

/-- The Mellin transform of `Θ` on `Re s > 3/2`. -/
theorem hasMellin_kTheta_wide
    (hsum : ∀ σ : ℝ, 3 / 2 < σ → Summable fun n : ℕ => ‖g n‖ * (n : ℝ) ^ (-σ))
    {s : ℂ} (hs : 3 / 2 < s.re) :
    HasMellin (kTheta g) s ((1 / 4 : ℂ) * Complex.Gammaℝ s ^ 2 * LSeries g s) := by
  have hs0 : 0 < s.re := by linarith
  set F : ℕ → ℝ → ℂ := fun n y =>
    (y : ℂ) ^ (s - 1) • (g (n + 1) * (kMoment 0 (2 * Real.pi * (n + 1) * y) : ℂ)) with hFdef
  have hT := fun n => kTheta_term_hasMellin (g := g) n hs0
  have hFi : ∀ n, Integrable (F n) (volume.restrict (Ioi 0)) := fun n => (hT n).1
  have hFnorm : ∀ n, ∫ y in Ioi (0 : ℝ), ‖F n y‖ = ‖g (n + 1)‖ *
      ((2 * Real.pi * (n + 1)) ^ (-s.re) * (2 ^ (s.re - 2) * Real.Gamma (s.re / 2) ^ 2)) := by
    intro n
    have hc : (0 : ℝ) < 2 * Real.pi * (n + 1) := by positivity
    have hpt : ∀ y ∈ Ioi (0 : ℝ), ‖F n y‖ =
        ‖g (n + 1)‖ * (y ^ (s.re - 1) * kMoment 0 (2 * Real.pi * (n + 1) * y)) := by
      intro y hy
      have hy0 : (0 : ℝ) < y := hy
      simp only [hFdef, smul_eq_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (kMoment_nonneg _ _), sub_re, one_re]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
      integral_norm_kTerm hc hs0]
  have hFs : Summable fun n => ∫ y in Ioi (0 : ℝ), ‖F n y‖ := by
    simp_rw [hFnorm]
    have hs' : Summable fun n : ℕ => ‖g (n + 1)‖ * ((n + 1 : ℕ) : ℝ) ^ (-s.re) :=
      (summable_nat_add_iff 1).mpr (hsum s.re hs)
    refine (hs'.mul_right ((2 * Real.pi) ^ (-s.re) *
      (2 ^ (s.re - 2) * Real.Gamma (s.re / 2) ^ 2))).congr fun n => ?_
    rw [Real.mul_rpow (x := 2 * Real.pi) (y := (n : ℝ) + 1) (by positivity) (by positivity)]
    push_cast
    ring
  have hHS := hasSum_integral_of_summable_integral_norm hFi hFs
  have hsumF : ∀ y : ℝ, ∑' n, F n y = (y : ℂ) ^ (s - 1) • kTheta g y := by
    intro y
    simp only [hFdef, kTheta, smul_eq_mul]
    rw [tsum_mul_left]
  have hconv : MellinConvergent (kTheta g) s := by
    unfold MellinConvergent
    refine ⟨?_, ?_⟩
    · have hc : ContinuousOn (fun y : ℝ => (y : ℂ) ^ (s - 1) • kTheta g y) (Ioi 0) := by
        intro y hy
        have hy0 : (0 : ℝ) < y := hy
        exact ((Complex.continuousAt_ofReal_cpow_const y (s - 1) (Or.inr hy0.ne')).continuousWithinAt).smul
          (continuousOn_kTheta_wide hsum y hy)
      exact hc.aestronglyMeasurable measurableSet_Ioi
    · rw [HasFiniteIntegral]
      calc ∫⁻ y in Ioi (0 : ℝ), ‖(y : ℂ) ^ (s - 1) • kTheta g y‖ₑ
          = ∫⁻ y in Ioi (0 : ℝ), ‖∑' n, F n y‖ₑ := by simp_rw [hsumF]
        _ ≤ ∫⁻ y in Ioi (0 : ℝ), ∑' n, ‖F n y‖ₑ := lintegral_mono fun y => enorm_tsum_le_tsum_enorm
        _ = ∑' n, ∫⁻ y in Ioi (0 : ℝ), ‖F n y‖ₑ :=
            lintegral_tsum fun n => (hFi n).aestronglyMeasurable.enorm
        _ < ⊤ := by
            have hfin : ∀ n, ∫⁻ y in Ioi (0 : ℝ), ‖F n y‖ₑ =
                ENNReal.ofReal (∫ y in Ioi (0 : ℝ), ‖F n y‖) := by
              intro n
              rw [ofReal_integral_eq_lintegral_ofReal (hFi n).norm
                (Eventually.of_forall fun y => norm_nonneg _)]
              congr 1
              funext y
              rw [ofReal_norm]
            simp_rw [hfin]
            rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg fun y => norm_nonneg _) hFs]
            exact ENNReal.ofReal_lt_top
  refine ⟨hconv, ?_⟩
  have hval : mellin (kTheta g) s = ∑' n, ∫ y in Ioi (0 : ℝ), F n y := by
    rw [mellin, hHS.tsum_eq]
    exact setIntegral_congr_fun measurableSet_Ioi fun y _ => (hsumF y).symm
  rw [hval]
  have hterm : ∀ n, ∫ y in Ioi (0 : ℝ), F n y = ((2 : ℂ) ^ (s - 2) * Complex.Gamma (s / 2) ^ 2 *
      (2 * Real.pi : ℂ) ^ (-s)) * LSeries.term g s (n + 1) := by
    intro n
    have h := (hT n).2
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n)]
    simp only [mellin] at h
    rw [show (fun y : ℝ => F n y) = fun y : ℝ =>
      (y : ℂ) ^ (s - 1) • (g (n + 1) * (kMoment 0 (2 * Real.pi * (n + 1) * y) : ℂ)) from rfl, h]
    have hc : ((2 * Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ) ^ (-s) =
        ((2 * Real.pi : ℝ) : ℂ) ^ (-s) * ((n + 1 : ℕ) : ℂ) ^ (-s) := by
      rw [show (2 * Real.pi * ((n : ℝ) + 1)) = (2 * Real.pi) * ((n + 1 : ℕ) : ℝ) by push_cast; ring,
        Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
        Complex.ofReal_natCast]
    rw [hc, Complex.cpow_neg ((n + 1 : ℕ) : ℂ) s, div_eq_mul_inv]
    push_cast
    ring
  simp_rw [hterm]
  have hLs : LSeriesSummable g s := by
    rw [LSeriesSummable]
    refine (hsum s.re hs).of_norm_bounded (fun n => ?_)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [LSeries.term_zero, norm_zero]
      exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg 0) _)
    · rw [LSeries.norm_term_eq, if_neg (by omega), Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  have hshift : LSeries g s = ∑' n : ℕ, LSeries.term g s (n + 1) := by
    rw [LSeries, hLs.tsum_eq_zero_add, LSeries.term_zero, zero_add]
  have hconst : (2 : ℂ) ^ (s - 2) * Complex.Gamma (s / 2) ^ 2 * (2 * Real.pi : ℂ) ^ (-s) =
      (1 / 4 : ℂ) * Complex.Gammaℝ s ^ 2 := by
    rw [Complex.Gammaℝ_def]
    have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
    have h2π : (2 * Real.pi : ℂ) ^ (-s) = (2 : ℂ) ^ (-s) * (Real.pi : ℂ) ^ (-s) := by
      rw [show (2 * Real.pi : ℂ) = ((2 : ℝ) : ℂ) * ((Real.pi : ℝ) : ℂ) by push_cast; ring,
        Complex.mul_cpow_ofReal_nonneg (by norm_num) hpi]
      push_cast; ring
    have hpow : ((Real.pi : ℂ) ^ (-s / 2)) ^ 2 = (Real.pi : ℂ) ^ (-s) := by
      rw [sq, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
      ring_nf
    have h22 : (2 : ℂ) ^ (s - 2) * (2 : ℂ) ^ (-s) = 1 / 4 := by
      rw [← Complex.cpow_add _ _ (by norm_num), show s - 2 + -s = ((-2 : ℤ) : ℂ) by push_cast; ring,
        Complex.cpow_intCast]
      norm_num
    rw [h2π, mul_pow, hpow]
    linear_combination (Complex.Gamma (s / 2) ^ 2 * (Real.pi : ℂ) ^ (-s)) * h22
  rw [tsum_mul_left, ← hshift, hconst]


/-! ## The Gamma corrections on `−3/4 ≤ Re s ≤ 7/4` -/

/-- `‖γ₁(s)‖ ≤ K/(1 + t²)` for `−3/4 ≤ Re s ≤ 7/4`, `|Im s| ≥ 2` (Cauchy estimate on circles of
radius `1/4`). -/
theorem exists_bound_gam1_wide :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, -3 / 4 ≤ s.re → s.re ≤ 7 / 4 → 2 ≤ |s.im| →
      ‖gam1 s‖ ≤ K / (1 + s.im ^ 2) := by
  obtain ⟨K, hK, hb⟩ := exists_bound_gam0
  refine ⟨8 * K, by positivity, fun s h1 h2 ht => ?_⟩
  have hpos : 0 < 1 + s.im ^ 2 := by positivity
  have hcirc : ∀ w ∈ Metric.closedBall s (1 / 4),
      -1 ≤ w.re ∧ w.re ≤ 2 ∧ |s.im| - 1 / 4 ≤ |w.im| := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    have hre := (abs_le.mp ((Complex.abs_re_le_norm (w - s)).trans hw))
    have him := (Complex.abs_im_le_norm (w - s)).trans hw
    simp only [sub_re, sub_im] at hre him
    refine ⟨by linarith [hre.1], by linarith [hre.2], ?_⟩
    have := abs_sub_abs_le_abs_sub s.im w.im
    rw [abs_sub_comm] at him
    linarith
  have hdiff : DiffContOnCl ℂ gam0 (Metric.ball s (1 / 4)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball s (by norm_num)]
    intro w hw
    refine (differentiableAt_gam0 fun m h => ?_).differentiableWithinAt
    have := (hcirc w hw).2.2
    rw [h] at this
    simp at this
    linarith
  have hbd : ∀ w ∈ Metric.sphere s (1 / 4), ‖gam0 w‖ ≤ 2 * K / (1 + s.im ^ 2) := by
    intro w hw
    have hw' := hcirc w (Metric.sphere_subset_closedBall hw)
    have hwt : 1 ≤ |w.im| := by linarith [hw'.2.2]
    refine (hb w hw'.1 hw'.2.1 hwt).trans ?_
    rw [div_le_div_iff₀ (by positivity) hpos]
    have hsq : (|s.im| - 1 / 4) ^ 2 ≤ w.im ^ 2 := by
      rw [← sq_abs w.im]
      exact pow_le_pow_left₀ (by linarith) hw'.2.2 2
    have h78 : (7 / 8) * |s.im| ≤ |s.im| - 1 / 4 := by linarith
    have h4964 : (49 / 64) * s.im ^ 2 ≤ (|s.im| - 1 / 4) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) h78 2
      rw [mul_pow, sq_abs] at this
      linarith
    have hfin : 1 + s.im ^ 2 ≤ 2 * (1 + w.im ^ 2) := by nlinarith
    nlinarith
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num) hdiff hbd
  rw [gam1]
  refine this.trans (le_of_eq ?_)
  field_simp
  ring

theorem verticalStrip_wide_subset_wideStrip : verticalStrip (-3 / 4) (7 / 4) ⊆ wideStrip := by
  intro s hs
  rw [mem_verticalStrip] at hs
  constructor <;> linarith [hs.1, hs.2]

/-- Decay of `E` on `−3/4 ≤ Re s ≤ 7/4`. -/
theorem exists_decay_eFun_wide {Λh : ℂ → ℂ} {ε : ℂ} (hΛ : Differentiable ℂ Λh) (hsym : ∀ s, Λh (1 - s) = ε * Λh s)
    (hε : ε * ε = 1) (hbd : ∃ B : ℝ, ∀ s : ℂ, -3 / 4 ≤ s.re → s.re ≤ 7 / 4 → ‖Λh s‖ ≤ B) :
    ∃ C : ℝ, ∀ s ∈ verticalStrip (-3 / 4) (7 / 4), ‖eFun Λh ε s‖ ≤ C / (1 + s.im ^ 2) := by
  have hεn : ‖ε‖ = 1 := by
    have h := congrArg norm hε
    rw [norm_mul, norm_one] at h
    nlinarith [norm_nonneg ε]
  obtain ⟨B, hB⟩ := hbd
  obtain ⟨K₀, hK₀, hb₀⟩ := exists_bound_gam0
  obtain ⟨K₁, hK₁, hb₁⟩ := exists_bound_gam1_wide
  -- the compact part
  set Kc : Set ℂ := (Icc (-3 / 4 : ℝ) (7 / 4)) ×ℂ (Icc (-2 : ℝ) 2) with hKc
  have hKcc : IsCompact Kc := isCompact_Icc.reProdIm isCompact_Icc
  have hKsub : Kc ⊆ wideStrip := by
    intro s hs
    rw [hKc, Complex.mem_reProdIm] at hs
    constructor <;> linarith [hs.1.1, hs.1.2]
  obtain ⟨M, hM⟩ := hKcc.exists_bound_of_continuousOn
    ((differentiableOn_eFun hΛ).continuousOn.mono hKsub)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by norm_num) (by norm_num))
  have hM0 : 0 ≤ M := by
    have := hM (0 : ℂ) (by rw [hKc, Complex.mem_reProdIm]; simp; norm_num)
    exact (norm_nonneg _).trans this
  refine ⟨5 * M + (B + 2 * ‖cA0 Λh ε‖ * K₀ + 2 * ‖cA1 Λh ε‖ * (K₀ + K₁)), fun s hs => ?_⟩
  rw [mem_verticalStrip] at hs
  have hpos : 0 < 1 + s.im ^ 2 := by positivity
  rcases le_or_gt |s.im| 2 with ht | ht
  · -- compact part
    have hsK : s ∈ Kc := by
      rw [hKc, Complex.mem_reProdIm]
      exact ⟨⟨hs.1, hs.2⟩, abs_le.mp ht⟩
    have h1 := hM s hsK
    rw [le_div_iff₀ hpos]
    have hle : 1 + s.im ^ 2 ≤ 5 := by
      have := sq_abs s.im
      nlinarith [abs_nonneg s.im]
    have hrest : 0 ≤ B + 2 * ‖cA0 Λh ε‖ * K₀ + 2 * ‖cA1 Λh ε‖ * (K₀ + K₁) := by positivity
    nlinarith [norm_nonneg (eFun Λh ε s)]
  · -- the tail: `E = Λ/4 − P`
    have h0 : s ≠ 0 := by intro h; rw [h] at ht; simp at ht; linarith
    have h1 : s ≠ 1 := by intro h; rw [h] at ht; simp at ht; linarith
    have hw : s ∈ wideStrip := verticalStrip_wide_subset_wideStrip (by rw [mem_verticalStrip]; exact hs)
    rw [eFun_eq_sub hΛ hsym hε h0 h1 hw]
    have ht1 : 1 ≤ |s.im| := by linarith
    have ht2 : 2 ≤ |s.im| := ht.le
    -- `‖Λ/(4s²(s−1)²)‖ ≤ B/(1+t²)`
    have hden : 1 + s.im ^ 2 ≤ ‖4 * s ^ 2 * (s - 1) ^ 2‖ := by
      rw [norm_mul, norm_mul, norm_pow, norm_pow, show ‖(4 : ℂ)‖ = 4 by norm_num]
      have a1 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
      have a2 : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
      simp only [sub_im, one_im, sub_zero] at a2
      have hsq : s.im ^ 2 = |s.im| ^ 2 := (sq_abs _).symm
      have hx2 : 4 ≤ |s.im| ^ 2 := by nlinarith
      have : 1 + |s.im| ^ 2 ≤ 4 * |s.im| ^ 2 * |s.im| ^ 2 := by nlinarith
      calc 1 + s.im ^ 2 = 1 + |s.im| ^ 2 := by rw [hsq]
        _ ≤ 4 * |s.im| ^ 2 * |s.im| ^ 2 := this
        _ ≤ 4 * ‖s‖ ^ 2 * ‖s - 1‖ ^ 2 := by gcongr
    have hΛq : ‖Λh s / (4 * s ^ 2 * (s - 1) ^ 2)‖ ≤ B / (1 + s.im ^ 2) := by
      rw [norm_div]
      exact div_le_div₀ hB0 (hB s hs.1 hs.2) hpos hden
    -- the corrections
    have hre1 : -3 / 4 ≤ (1 - s).re := by simp; linarith [hs.2]
    have hre2 : (1 - s).re ≤ 7 / 4 := by simp; linarith [hs.1]
    have him : (1 - s).im ^ 2 = s.im ^ 2 := by simp
    have habs : |(1 - s).im| = |s.im| := by simp
    have g0s := hb₀ s (by linarith [hs.1]) (by linarith [hs.2]) ht1
    have g0r := hb₀ (1 - s) (by linarith) (by linarith) (by rw [habs]; exact ht1)
    have g1s := hb₁ s hs.1 hs.2 ht2
    have g1r := hb₁ (1 - s) hre1 hre2 (by rw [habs]; exact ht2)
    rw [him] at g0r g1r
    have hP : ‖corrP Λh ε s‖ ≤
        (2 * ‖cA0 Λh ε‖ * K₀ + 2 * ‖cA1 Λh ε‖ * (K₀ + K₁)) / (1 + s.im ^ 2) := by
      unfold corrP
      have e1 : ‖gam0 s + ε * gam0 (1 - s)‖ ≤ 2 * K₀ / (1 + s.im ^ 2) := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, hεn, one_mul, mul_div_assoc, two_mul]
        exact add_le_add g0s g0r
      have e2 : ‖gam1 s + ε * gam1 (1 - s)‖ ≤ 2 * (K₀ + K₁) / (1 + s.im ^ 2) := by
        refine (norm_add_le _ _).trans ?_
        have : K₁ / (1 + s.im ^ 2) ≤ (K₀ + K₁) / (1 + s.im ^ 2) := by gcongr; linarith
        rw [norm_mul, hεn, one_mul, mul_div_assoc, two_mul]
        exact add_le_add (g1s.trans this) (g1r.trans this)
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      calc ‖cA0 Λh ε‖ * ‖gam0 s + ε * gam0 (1 - s)‖ + ‖cA1 Λh ε‖ * ‖gam1 s + ε * gam1 (1 - s)‖
          ≤ ‖cA0 Λh ε‖ * (2 * K₀ / (1 + s.im ^ 2)) +
              ‖cA1 Λh ε‖ * (2 * (K₀ + K₁) / (1 + s.im ^ 2)) := by
            gcongr
        _ = _ := by field_simp
    refine (norm_sub_le _ _).trans ?_
    calc ‖Λh s / (4 * s ^ 2 * (s - 1) ^ 2)‖ + ‖corrP Λh ε s‖
        ≤ B / (1 + s.im ^ 2) +
            (2 * ‖cA0 Λh ε‖ * K₀ + 2 * ‖cA1 Λh ε‖ * (K₀ + K₁)) / (1 + s.im ^ 2) :=
          add_le_add hΛq hP
      _ ≤ (5 * M + (B + 2 * ‖cA0 Λh ε‖ * K₀ + 2 * ‖cA1 Λh ε‖ * (K₀ + K₁))) / (1 + s.im ^ 2) := by
          rw [← add_div]
          apply div_le_div_of_nonneg_right _ hpos.le
          linarith



/-! ## The corrections on the lines `Re s = 7/4` and `Re s = −3/4` -/

theorem hasMellin_corrRight_wide {Λh : ℂ → ℂ} {ε : ℂ} {s : ℂ} (hs : s.re = 7 / 4) :
    HasMellin (corrRight Λh ε) s (corrP Λh ε s) := by
  have h1s1 : -1 < (1 - s).re := by simp [hs]; norm_num
  have h1s2 : (1 - s).re < 0 := by simp [hs]; norm_num
  have hpos : 0 < s.re := by rw [hs]; norm_num
  have h := hasMellin_lin (c₀ := cA0 Λh ε) (c₁ := cA1 Λh ε) (hasMellin_eTwo hpos)
    (hasMellin_const_mul (hasMellin_dual_inv (hasMellin_eTwo_sub_one h1s1 h1s2)) ε)
    (hasMellin_log_eTwo hpos)
    (hasMellin_const_mul (hasMellin_dual_inv (hasMellin_log_eTwo_sub_one h1s1 h1s2)) ε)
  unfold corrRight corrP
  exact h

theorem hasMellin_corrLeft_wide {Λh : ℂ → ℂ} {ε : ℂ} {s : ℂ} (hs : s.re = -3 / 4) :
    HasMellin (corrLeft Λh ε) s (corrP Λh ε s) := by
  have h1 : -1 < s.re := by rw [hs]; norm_num
  have h2 : s.re < 0 := by rw [hs]; norm_num
  have hpos : 0 < (1 - s).re := by simp [hs]; norm_num
  have h := hasMellin_lin (c₀ := cA0 Λh ε) (c₁ := cA1 Λh ε) (hasMellin_eTwo_sub_one h1 h2)
    (hasMellin_const_mul (hasMellin_dual_inv (hasMellin_eTwo hpos)) ε)
    (hasMellin_log_eTwo_sub_one h1 h2)
    (hasMellin_const_mul (hasMellin_dual_inv (hasMellin_log_eTwo hpos)) ε)
  unfold corrLeft corrP
  exact h

/-! ## The theta relation -/

/-- **The theta relation with sign `ε`, at abscissa `3/2`.** -/
theorem kTheta_relation_sign_wide {Λh : ℂ → ℂ} {ε : ℂ}
    (hsum : ∀ σ : ℝ, 3 / 2 < σ → Summable fun n : ℕ => ‖g n‖ * (n : ℝ) ^ (-σ))
    (hΛ : Differentiable ℂ Λh) (hsym : ∀ s, Λh (1 - s) = ε * Λh s) (hε : ε * ε = 1)
    (heq : ∀ s : ℂ, 3 / 2 < s.re →
      Λh s = s ^ 2 * (s - 1) ^ 2 * Complex.Gammaℝ s ^ 2 * LSeries g s)
    (hbd : ∃ B : ℝ, ∀ s : ℂ, -3 / 4 ≤ s.re → s.re ≤ 7 / 4 → ‖Λh s‖ ≤ B) {y : ℝ} (hy : 0 < y) :
    kTheta g y - ε * ((y : ℂ) ^ (-1 : ℂ) * kTheta g y⁻¹) =
      (1 / 4) * ((coeffB Λh - coeffA Λh * Real.log y) / y -
        ε * (coeffB Λh + coeffA Λh * Real.log y)) := by
  obtain ⟨C, hC⟩ := exists_decay_eFun_wide hΛ hsym hε hbd
  have hE : DifferentiableOn ℂ (eFun Λh ε) (verticalStrip (-3 / 4) (7 / 4)) :=
    (differentiableOn_eFun hΛ).mono verticalStrip_wide_subset_wideStrip
  have hΛq : ∀ s : ℂ, 3 / 2 < s.re →
      (1 / 4 : ℂ) * Complex.Gammaℝ s ^ 2 * LSeries g s = Λh s / (4 * s ^ 2 * (s - 1) ^ 2) := by
    intro s hs
    have h0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
    have h1 : s - 1 ≠ 0 := by intro h; rw [sub_eq_zero] at h; rw [h] at hs; norm_num at hs
    rw [heq s hs]
    field_simp
  have hR : ∀ s : ℂ, s.re = 7 / 4 →
      HasMellin (fun t => kTheta g t - corrRight Λh ε t) s (eFun Λh ε s) := by
    intro s hs
    have hs1 : 3 / 2 < s.re := by rw [hs]; norm_num
    have h0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
    have h1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
    have hw : s ∈ wideStrip := ⟨by rw [hs]; norm_num, by rw [hs]; norm_num⟩
    have hK := hasMellin_kTheta_wide hsum hs1
    have hP := hasMellin_corrRight_wide (Λh := Λh) (ε := ε) hs
    have hsub := hasMellin_sub hK.1 hP.1
    refine ⟨hsub.1, ?_⟩
    rw [hsub.2, hK.2, hP.2, hΛq s hs1, eFun_eq_sub hΛ hsym hε h0 h1 hw]
  have hL : ∀ s : ℂ, s.re = -3 / 4 →
      HasMellin (fun t => ε * ((t : ℂ) ^ (-1 : ℂ) * kTheta g t⁻¹) - corrLeft Λh ε t) s
        (eFun Λh ε s) := by
    intro s hs
    have hs1 : 3 / 2 < (1 - s).re := by simp [hs]; norm_num
    have h0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
    have h1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
    have hw : s ∈ wideStrip := ⟨by rw [hs]; norm_num, by rw [hs]; norm_num⟩
    have hK := hasMellin_const_mul (hasMellin_dual_inv (hasMellin_kTheta_wide hsum hs1)) ε
    have hP := hasMellin_corrLeft_wide (Λh := Λh) (ε := ε) hs
    have hsub := hasMellin_sub hK.1 hP.1
    refine ⟨hsub.1, ?_⟩
    rw [hsub.2, hK.2, hP.2, hΛq (1 - s) hs1, hsym, eFun_eq_sub hΛ hsym hε h0 h1 hw,
      show (1 - s - 1) ^ 2 = s ^ 2 by ring, show (1 - s) ^ 2 = (s - 1) ^ 2 by ring]
    have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
    field_simp
    linear_combination (Λh s) * hε
  have hc := continuousAt_corr (Λh := Λh) (ε := ε) hy
  have hkc : ContinuousAt (kTheta g) y :=
    (continuousOn_kTheta_wide hsum).continuousAt (Ioi_mem_nhds hy)
  have hkci : ContinuousAt (fun t : ℝ => kTheta g t⁻¹) y :=
    ((continuousOn_kTheta_wide hsum).continuousAt (Ioi_mem_nhds (inv_pos.mpr hy))).comp
      (continuousAt_inv₀ hy.ne')
  have hcp : ContinuousAt (fun t : ℝ => (t : ℂ) ^ (-1 : ℂ)) y :=
    Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hy.ne')
  have heng := MaassThetaMellin.eq_of_hasMellin_two_lines (by norm_num) hE hC hR hL hy
    (hkc.sub hc.1) ((continuousAt_const.mul (hcp.mul hkci)).sub hc.2)
  rw [← corrRight_sub_corrLeft hε]
  linear_combination heng

/-- The axis relation `u(i/y) = ε u(iy)` at abscissa `3/2`. -/
theorem maassFun_axis_sign_wide
    (hsum : ∀ σ : ℝ, 3 / 2 < σ → Summable fun n : ℕ => ‖g n‖ * (n : ℝ) ^ (-σ))
    {Λh : ℂ → ℂ} {ε : ℂ} (hΛ : Differentiable ℂ Λh) (hsym : ∀ s, Λh (1 - s) = ε * Λh s)
    (hε : ε * ε = 1)
    (heq : ∀ s : ℂ, 3 / 2 < s.re →
      Λh s = s ^ 2 * (s - 1) ^ 2 * Complex.Gammaℝ s ^ 2 * LSeries g s)
    (hbd : ∃ B : ℝ, ∀ s : ℂ, -3 / 4 ≤ s.re → s.re ≤ 7 / 4 → ‖Λh s‖ ≤ B) {y : ℝ} (hy : 0 < y) :
    maassFun g (ε * coeffA Λh) (ε * coeffB Λh) (((1 / y : ℝ) : ℂ) * I) =
      ε * maassFun g (ε * coeffA Λh) (ε * coeffB Λh) ((y : ℂ) * I) := by
  have hrel := kTheta_relation_sign_wide hsum hΛ hsym hε heq hbd hy
  unfold maassFun
  rw [cosSeries_axis y, cosSeries_axis (1 / y), constTerm_axis, constTerm_axis]
  set r : ℝ := y ^ (1 / 2 : ℝ) with hr_def
  have hsq : ((1 / y) ^ (1 / 2 : ℝ) : ℝ) = r⁻¹ := by
    rw [hr_def, Real.div_rpow zero_le_one hy.le, Real.one_rpow, one_div]
  have hlog : Real.log (1 / y) = -Real.log y := by rw [one_div, Real.log_inv]
  have hr : r ^ 2 = y := by
    rw [hr_def, ← Real.rpow_natCast, ← Real.rpow_mul hy.le]; norm_num
  have hr0 : (0 : ℝ) < r := Real.rpow_pos_of_pos hy _
  have hinv : (y : ℂ) ^ (-1 : ℂ) = (y : ℂ)⁻¹ := Complex.cpow_neg_one _
  have hyc : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  have hrc : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0.ne'
  have hrc2 : (r : ℂ) ^ 2 = (y : ℂ) := by exact_mod_cast hr
  have hΘ : kTheta g (1 / y) = ε * (y : ℂ) * (kTheta g y - (1 / 4) * ((coeffB Λh - coeffA Λh *
      Real.log y) / y - ε * (coeffB Λh + coeffA Λh * Real.log y))) := by
    rw [hinv] at hrel
    rw [show (1 / y : ℝ) = y⁻¹ from one_div y]
    have hyy : (y : ℂ) * (y : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hyc
    linear_combination (-(ε * (y : ℂ))) * hrel - kTheta g y⁻¹ * (y : ℂ) * (y : ℂ)⁻¹ * hε -
      kTheta g y⁻¹ * hyy
  rw [hsq, hlog, hΘ]
  push_cast
  rw [← hrc2]
  field_simp
  ring

/-- `u(−1/z) = ε u(z)` at abscissa `3/2`. -/
theorem maassFun_invS_sign_wide
    (hsum : ∀ σ : ℝ, 3 / 2 < σ → Summable fun n : ℕ => ‖g n‖ * (n : ℝ) ^ (-σ))
    {Λh : ℂ → ℂ} {ε : ℂ} (hΛ : Differentiable ℂ Λh) (hsym : ∀ s, Λh (1 - s) = ε * Λh s)
    (hε : ε * ε = 1)
    (heq : ∀ s : ℂ, 3 / 2 < s.re →
      Λh s = s ^ 2 * (s - 1) ^ 2 * Complex.Gammaℝ s ^ 2 * LSeries g s)
    (hbd : ∃ B : ℝ, ∀ s : ℂ, -3 / 4 ≤ s.re → s.re ≤ 7 / 4 → ‖Λh s‖ ≤ B) {z : ℂ}
    (hz : 0 < z.im) :
    maassFun g (ε * coeffA Λh) (ε * coeffB Λh) (invS z) =
      ε * maassFun g (ε * coeffA Λh) (ε * coeffB Λh) z :=
  maassFun_inv_eq_smul_of_axis (polyGrowth_of_summable_wide hsum) _ _ ε
    (fun _ hy => maassFun_axis_sign_wide hsum hΛ hsym hε heq hbd hy) hz

/-! ## The converse theorems -/

/-- **An odd functional equation forces `G = 0`, at abscissa `3/2`.** -/
theorem coeff_eq_zero_of_odd_functional_equation_wide
    (hsum : ∀ σ : ℝ, 3 / 2 < σ → Summable fun n : ℕ => ‖g n‖ * (n : ℝ) ^ (-σ))
    {Λh : ℂ → ℂ} (hΛ : Differentiable ℂ Λh) (hsym : ∀ s, Λh (1 - s) = -Λh s)
    (heq : ∀ s : ℂ, 3 / 2 < s.re →
      Λh s = s ^ 2 * (s - 1) ^ 2 * Complex.Gammaℝ s ^ 2 * LSeries g s)
    (hbd : ∃ B : ℝ, ∀ s : ℂ, -3 / 4 ≤ s.re → s.re ≤ 7 / 4 → ‖Λh s‖ ≤ B) {m : ℕ} (hm : 1 ≤ m) :
    g m = 0 := by
  have hg := polyGrowth_of_summable_wide hsum
  set a := (-1 : ℂ) * coeffA Λh
  set b := (-1 : ℂ) * coeffB Λh
  have hS : ∀ z : ℂ, 0 < z.im → maassFun g a b (invS z) = -1 * maassFun g a b z :=
    fun z hz => maassFun_invS_sign_wide hsum hΛ (fun s => by rw [hsym]; ring) (by norm_num) heq hbd hz
  have hT : ∀ z : ℂ, maassFun g a b (z + 1) = maassFun g a b z := fun z => maassFun_add_one a b z
  -- `u` vanishes identically
  have hzero : ∀ z : ℂ, 0 < z.im → maassFun g a b z = 0 := by
    intro z hz
    have hz1 := upper_add_one hz
    have hS1 := invS_mem_upper hz1
    have hz2 := upper_add_one hS1
    have hS2 := invS_mem_upper hz2
    have hz3 := upper_add_one hS2
    have e1 := hS (z + 1) hz1
    have e2 := hS (invS (z + 1) + 1) hz2
    have e3 := hS (invS (invS (z + 1) + 1) + 1) hz3
    rw [invS_cube hz, hT] at e3
    rw [hT] at e2
    rw [hT] at e1
    rw [e2, e1] at e3
    linear_combination e3 / 2
  -- `W` is constant on horizontal lines
  have hy : (0 : ℝ) < 1 := one_pos
  have hline : ∀ x : ℝ, cosSeries g (point x 1) = -(constTerm a b (point x 1)) / 4 := by
    intro x
    have h := hzero (point x 1) (by rw [point_im]; exact hy)
    unfold maassFun at h
    linear_combination h / 4
  have hc : ∀ x : ℝ, constTerm a b (point x 1) = constTerm a b (point 0 1) := by
    intro x; simp [constTerm, point_im]
  have hint := integral_cosSeries_mul_cos_eq hg hm hy
  have hint0 : ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
      cosSeries g (point x 1) * (Real.cos (2 * Real.pi * m * x) : ℂ) = 0 := by
    have hcos := integral_cos_two_pi_int (k := (m : ℤ)) (by exact_mod_cast (show m ≠ 0 by omega))
    push_cast at hcos
    simp_rw [hline, hc]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, hcos]
    simp
  rw [hint0] at hint
  have hyp := yPart_pos hm hy
  have hprod : g m * (yPart (1 / 2) 0 0 m 1 : ℂ) = 0 := by linear_combination (-2 : ℂ) * hint
  rcases mul_eq_zero.mp hprod with h0 | h0
  · exact h0
  · exact absurd h0 (by exact_mod_cast hyp.ne')


/-- **A converse theorem for `ζ²` at abscissa `3/2`.**  A Dirichlet series `G = Σ g_n n^{−s}` with `g_1 = 1`,
absolutely convergent on `Re s > 3/2`, whose completion `s²(s−1)²Γ_ℝ(s)²G(s)` extends to an
entire function invariant under `s ↦ 1 − s` and bounded on `−3/4 ≤ Re s ≤ 7/4`, is `ζ²`. -/
theorem coeff_eq_divisorCount_of_functional_equation_wide
    (hsum : ∀ σ : ℝ, 3 / 2 < σ → Summable fun n : ℕ => ‖g n‖ * (n : ℝ) ^ (-σ)) (hg1 : g 1 = 1)
    {Λh : ℂ → ℂ} (hΛ : Differentiable ℂ Λh) (hsym : ∀ s, Λh (1 - s) = Λh s)
    (heq : ∀ s : ℂ, 3 / 2 < s.re →
      Λh s = s ^ 2 * (s - 1) ^ 2 * Complex.Gammaℝ s ^ 2 * LSeries g s)
    (hbd : ∃ B : ℝ, ∀ s : ℂ, -3 / 4 ≤ s.re → s.re ≤ 7 / 4 → ‖Λh s‖ ≤ B) {n : ℕ} (hn : 1 ≤ n) :
    g n = divisorCount n := by
  have hg := polyGrowth_of_summable_wide hsum
  have hd := polyGrowth_of_summable (fun σ hσ => summable_divisorCount (σ := σ) hσ)
  set aG := coeffA Λh
  set bG := coeffB Λh
  set b₀ := coeffB zetaSqCompleted
  have hSG : ∀ z : ℂ, 0 < z.im → maassFun g aG bG (invS z) = maassFun g aG bG z :=
    fun z hz => by
      simpa only [one_mul] using maassFun_invS_sign_wide (ε := 1) hsum hΛ
        (fun s => by rw [one_mul]; exact hsym s) (one_mul 1) heq hbd hz
  have hS₀ : ∀ z : ℂ, 0 < z.im → maassFun divisorCount 1 b₀ (invS z) = maassFun divisorCount 1 b₀ z := by
    intro z hz
    have h := maassFun_divisorCount_invS hz
    rwa [coeffA_zetaSqCompleted] at h
  -- the constant terms are proportional
  have hW := constTerm_wronskian_eq_zero hg hd aG bG 1 b₀ hSG hS₀
  have hb : bG = aG * b₀ := by linear_combination hW
  -- the difference is an `S`-invariant Bessel cosine series
  set h : ℕ → ℂ := fun k => g k - aG * divisorCount k with hh
  have hhp : PolyGrowth h := polyGrowth_sub_smul hg hd aG
  have hdiff : ∀ z : ℂ, 0 < z.im →
      maassFun g aG bG z - aG * maassFun divisorCount 1 b₀ z = 4 * cosSeries h z := by
    intro z hz
    rw [hh, cosSeries_sub_smul hg hd aG hz]
    simp only [maassFun, constTerm, hb]
    ring
  have hSh : ∀ z : ℂ, 0 < z.im → cosSeries h (invS z) = cosSeries h z := by
    intro z hz
    have hSz : 0 < (invS z).im := invS_mem_upper hz
    have e := hdiff (invS z) hSz
    rw [hSG z hz, hS₀ z hz, hdiff z hz] at e
    exact (mul_left_cancel₀ (by norm_num : (4 : ℂ) ≠ 0) e).symm
  have hzero : ∀ k : ℕ, 1 ≤ k → h k = 0 := fun k hk => coeff_eq_zero_of_invS hhp hSh hk
  have hc : aG = 1 := by
    have h1 := hzero 1 le_rfl
    simp only [hh, hg1, divisorCount_one, mul_one] at h1
    linear_combination -h1
  have hk := hzero n hn
  simp only [hh, hc, one_mul] at hk
  exact sub_eq_zero.mp hk

end RHTower.MaassZetaSquaredConverseWide
