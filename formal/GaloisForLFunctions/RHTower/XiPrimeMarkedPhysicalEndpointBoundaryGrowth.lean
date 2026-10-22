import GaloisForLFunctions.RHTower.XiPrimeMarkedPhysicalEndpointBoundaryNuclearObstruction
import GaloisForLFunctions.RHTower.ZetaLogDerivStripRange
import GaloisForLFunctions.RHTower.XiShiftPrimeExposure
import GaloisForLFunctions.RHTower.XiWardInteriorTraceSplit
import GaloisForLFunctions.HTGeometry.GammaProjectiveBoundary
import GaloisForLFunctions.HTGeometry.ReflectedDigammaAnomaly

/-!
# Polynomial growth of `-ξ'/ξ` on the line `Re s = 1`

On the boundary line `s = 1 + it`, `ξ = s(s - 1)/2 · Γ_ℝ(s) · ζ(s)` has no zeros, and its
logarithmic derivative splits as the archimedean part plus `ζ'/ζ`. The archimedean part equals
`1/s + 1/(s - 1) - (log π)/2 + ψ(s/2)/2`, which is `O(log |t|)` by the vertical digamma bound,
while `ζ'/ζ(1 + it) = O(log⁹ |t|)` for `|t| ≥ 9`. Combining these with continuity on the compact
range `|t| ≤ 9` gives a global polynomial bound `‖-ξ'/ξ(1 + it)‖ ≤ C (1 + |t|)^9`.

## Main results

- `logDeriv_xi_boundary_split`: for `t ≠ 0`, `ξ'/ξ(1 + it)` is the archimedean log-derivative
  plus `ζ'/ζ(1 + it)`.
- `norm_logDeriv_archFactor_boundary_le`: for `|t| ≥ 9`, the archimedean log-derivative is at
  most `(log |t|)/2 + routeKArchBoundaryConstant`.
- `norm_seamFluxCochain_boundary_le`: for `|t| ≥ 9`,
  `‖-ξ'/ξ(1 + it)‖ ≤ routeKBoundaryGrowthConstant · (1 + |t|)^9`.
- `exists_norm_seamFluxCochain_boundary_global_le`: some `C ≥ 0` gives
  `‖-ξ'/ξ(1 + it)‖ ≤ C (1 + |t|)^9` for all real `t`.

## Hypotheses

All results are unconditional; the only side conditions are `t ≠ 0` or `9 ≤ |t|` on the height.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- For `t ≠ 0`, the logarithmic derivative of `ξ` at `1 + it` is the archimedean
log-derivative of `s(s - 1)/2 · Γ_ℝ(s)` plus `ζ'/ζ(1 + it)`. -/
theorem logDeriv_xi_boundary_split {t : ℝ} (ht : t ≠ 0) :
    logDeriv xi ((1 : ℂ) + (t : ℂ) * I) =
      logDeriv archFactor ((1 : ℂ) + (t : ℂ) * I) +
        deriv riemannZeta ((1 : ℂ) + (t : ℂ) * I) /
          riemannZeta ((1 : ℂ) + (t : ℂ) * I) := by
  let s : ℂ := (1 : ℂ) + (t : ℂ) * I
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s, Complex.mul_re] at hre
  have hs1 : s ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [s, Complex.mul_im] at him
    exact ht him
  have hsre : s.re = 1 := by simp [s, Complex.mul_re]
  have hz : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by rw [hsre])
  have hG : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by rw [hsre]; norm_num)
  have haf : archFactor s ≠ 0 := archFactor_ne_zero hs0 hs1 hG
  have hlocal : xi =ᶠ[nhds s] fun z => archFactor z * riemannZeta z := by
    have h0 : {z : ℂ | z ≠ 0} ∈ nhds s := isOpen_compl_singleton.mem_nhds hs0
    have h1 : {z : ℂ | z ≠ 1} ∈ nhds s := isOpen_compl_singleton.mem_nhds hs1
    have hpos : {z : ℂ | 0 < z.re} ∈ nhds s :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show 0 < s.re by rw [hsre]; norm_num)
    filter_upwards [h0, h1, hpos] with z hz0 hz1 hzpos
    exact xi_eq_archFactor_mul_zeta hz0 hz1
      (Complex.Gammaℝ_ne_zero_of_re_pos hzpos)
  change logDeriv xi s =
    logDeriv archFactor s + deriv riemannZeta s / riemannZeta s
  rw [logDeriv_congr_of_eventuallyEq hlocal]
  rw [logDeriv_mul s haf hz
    (hasDerivAt_archFactor_of_re_pos (by rw [hsre]; norm_num)).differentiableAt
    (differentiableAt_riemannZeta hs1)]
  rw [logDeriv_apply]
  rfl

/-- For `|t| ≥ 9`, `‖ψ((1 + it)/2)‖ ≤ log |t| + digammaVerticalLogConstant`. -/
theorem norm_digamma_one_add_I_div_two_le {t : ℝ} (ht : 9 ≤ |t|) :
    ‖Complex.digamma (((1 : ℂ) + (t : ℂ) * I) / 2)‖ ≤
      Real.log |t| + GaloisForLFunctions.digammaVerticalLogConstant := by
  let T : ℝ := |t| / 2
  have hT1 : 1 ≤ T := by dsimp [T]; linarith
  have hsigT : (1 / 2 : ℝ) ≤ T := by linarith
  have hbase := GaloisForLFunctions.norm_digamma_vertical_le_log
    (σ := (1 / 2 : ℝ)) (t := T) (by norm_num) hT1 hsigT
  have hTpos : 0 < T := zero_lt_one.trans_le hT1
  have habspos : 0 < |t| := by linarith
  have hTle : T ≤ |t| := by dsimp [T]; linarith
  have hlog : Real.log T ≤ Real.log |t| := Real.log_le_log hTpos hTle
  have hnorm : ‖Complex.digamma (((1 : ℂ) + (t : ℂ) * I) / 2)‖ =
      ‖Complex.digamma (((1 / 2 : ℝ) : ℂ) + (T : ℂ) * I)‖ := by
    by_cases ht0 : 0 ≤ t
    · have harg : ((1 : ℂ) + (t : ℂ) * I) / 2 =
          (((1 / 2 : ℝ) : ℂ) + (T : ℂ) * I) := by
        apply Complex.ext <;>
          simp [T, abs_of_nonneg ht0, Complex.mul_re, Complex.mul_im]
      rw [harg]
    · have htneg : t < 0 := lt_of_not_ge ht0
      have harg : ((1 : ℂ) + (t : ℂ) * I) / 2 =
          (starRingEnd ℂ) (((1 / 2 : ℝ) : ℂ) + (T : ℂ) * I) := by
        apply Complex.ext
        · simp [T, abs_of_neg htneg, Complex.div_re, Complex.div_im,
            Complex.mul_re]
        · simp [T, abs_of_neg htneg, Complex.div_re, Complex.div_im,
            Complex.mul_im]
          ring
      rw [harg, ReflectedDigammaAnomaly.digamma_conj, norm_conj]
  rw [hnorm]
  linarith

/-- Additive constant in the boundary bound for the archimedean log-derivative. -/
def routeKArchBoundaryConstant : ℝ :=
  2 + |Real.log Real.pi| / 2 +
    GaloisForLFunctions.digammaVerticalLogConstant / 2

/-- For `|t| ≥ 9`, the archimedean log-derivative at `1 + it` is bounded by
`(log |t|)/2 + routeKArchBoundaryConstant`. -/
theorem norm_logDeriv_archFactor_boundary_le {t : ℝ} (ht : 9 ≤ |t|) :
    ‖logDeriv archFactor ((1 : ℂ) + (t : ℂ) * I)‖ ≤
      Real.log |t| / 2 + routeKArchBoundaryConstant := by
  let s : ℂ := (1 : ℂ) + (t : ℂ) * I
  have ht0 : t ≠ 0 := by
    intro h
    norm_num [h] at ht
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s, Complex.mul_re] at hre
  have hs1 : s ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [s, Complex.mul_im] at him
    exact ht0 him
  have hspos : 0 < s.re := by simp [s, Complex.mul_re]
  have hs_norm : 1 ≤ ‖s‖ := by
    have h := Complex.abs_re_le_norm s
    simpa [s, Complex.mul_re] using h
  have hsinv : ‖1 / s‖ ≤ 1 := by
    rw [norm_div, norm_one, one_div]
    exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hs_norm)).2 hs_norm
  have hsm1inv : ‖1 / (s - 1)‖ ≤ 1 := by
    have habspos : 0 < |t| := by linarith
    rw [norm_div, norm_one, one_div]
    have hnorm : ‖s - 1‖ = |t| := by
      rw [show s - 1 = (t : ℂ) * I by simp [s]]
      simp [Real.norm_eq_abs]
    rw [hnorm]
    exact (inv_le_one₀ habspos).2 (by linarith)
  have hdig := norm_digamma_one_add_I_div_two_le ht
  have hgamma : ‖GaloisForLFunctions.gammaRealLogConnection s‖ ≤
      |Real.log Real.pi| / 2 +
        (Real.log |t| + GaloisForLFunctions.digammaVerticalLogConstant) / 2 := by
    rw [GaloisForLFunctions.gammaRealLogConnection]
    calc
      ‖-(((Real.log Real.pi : ℝ) : ℂ) / 2) + Complex.digamma (s / 2) / 2‖ ≤
          ‖-(((Real.log Real.pi : ℝ) : ℂ) / 2)‖ +
            ‖Complex.digamma (s / 2) / 2‖ := norm_add_le _ _
      _ = |Real.log Real.pi| / 2 + ‖Complex.digamma (s / 2)‖ / 2 := by
        simp [Real.norm_eq_abs]
      _ ≤ _ := by
        have hdig' : ‖Complex.digamma (s / 2)‖ ≤
            Real.log |t| + GaloisForLFunctions.digammaVerticalLogConstant := by
          simpa [s] using hdig
        linarith
  rw [logDeriv_archFactor_closed hspos hs0 hs1]
  calc
    ‖1 / s + 1 / (s - 1) + GaloisForLFunctions.gammaRealLogConnection s‖ ≤
        ‖1 / s‖ + ‖1 / (s - 1)‖ +
          ‖GaloisForLFunctions.gammaRealLogConnection s‖ := by
      calc
        _ ≤ ‖1 / s + 1 / (s - 1)‖ +
            ‖GaloisForLFunctions.gammaRealLogConnection s‖ := norm_add_le _ _
        _ ≤ _ := by
          gcongr
          exact norm_add_le _ _
    _ ≤ 1 + 1 + (|Real.log Real.pi| / 2 +
        (Real.log |t| + GaloisForLFunctions.digammaVerticalLogConstant) / 2) := by
      gcongr
    _ = Real.log |t| / 2 + routeKArchBoundaryConstant := by
      rw [routeKArchBoundaryConstant]
      ring

/-- Constant in the large-height polynomial bound for `-ξ'/ξ` on `Re s = 1`. -/
def routeKBoundaryGrowthConstant : ℝ :=
  1 / 2 + routeKArchBoundaryConstant + 2240 / zetaLowerA

/-- For `|t| ≥ 9`, `‖-ξ'/ξ(1 + it)‖ ≤ routeKBoundaryGrowthConstant · (1 + |t|)^9`, from the
archimedean bound and `‖ζ'/ζ(1 + it)‖ ≤ (2240 / A) log⁹ |t|`. -/
theorem norm_seamFluxCochain_boundary_le {t : ℝ} (ht : 9 ≤ |t|) :
    ‖seamFluxCochain ((1 : ℂ) + (t : ℂ) * I)‖ ≤
      routeKBoundaryGrowthConstant * (1 + |t|) ^ (9 : ℕ) := by
  have habspos : 0 < |t| := by linarith
  have hlogpos : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hstrip : 0 ≤ zetaLowerA / Real.log |t| ^ (9 : ℕ) :=
    div_nonneg zetaLowerA_pos.le (pow_nonneg hlogpos.le 9)
  have hzeta := norm_deriv_div_riemannZeta_le
    (σ := (1 : ℝ)) (t := t) ht (by linarith) (by linarith)
  have harch := norm_logDeriv_archFactor_boundary_le ht
  have hsplit := logDeriv_xi_boundary_split
    (t := t) (by exact abs_pos.mp habspos)
  have hpow1 : 1 ≤ (1 + |t|) ^ (9 : ℕ) := by
    exact one_le_pow₀ (by linarith : 1 ≤ 1 + |t|)
  have habspow : |t| ≤ (1 + |t|) ^ (9 : ℕ) := by
    calc
      |t| ≤ 1 + |t| := by linarith
      _ ≤ (1 + |t|) ^ (9 : ℕ) := le_self_pow₀ (by linarith) (by norm_num)
  have hlogbase : Real.log |t| ≤ 1 + |t| :=
    (Real.log_le_sub_one_of_pos habspos).trans (by linarith)
  have hlogpow : Real.log |t| ≤ (1 + |t|) ^ (9 : ℕ) :=
    hlogbase.trans (le_self_pow₀ (by linarith) (by norm_num))
  have harchC : 0 ≤ routeKArchBoundaryConstant := by
    rw [routeKArchBoundaryConstant,
      GaloisForLFunctions.digammaVerticalLogConstant]
    positivity
  have hzetaC : 0 ≤ 2240 / zetaLowerA :=
    div_nonneg (by norm_num) zetaLowerA_pos.le
  have harch' :
      Real.log |t| / 2 + routeKArchBoundaryConstant ≤
        (1 / 2 + routeKArchBoundaryConstant) * (1 + |t|) ^ (9 : ℕ) := by
    nlinarith
  have hzeta' :
      2240 / zetaLowerA * Real.log |t| ^ (9 : ℕ) ≤
        (2240 / zetaLowerA) * (1 + |t|) ^ (9 : ℕ) := by
    apply mul_le_mul_of_nonneg_left _ hzetaC
    exact pow_le_pow_left₀ hlogpos.le hlogbase 9
  rw [seamFluxCochain, norm_neg, hsplit]
  calc
    ‖logDeriv archFactor ((1 : ℂ) + (t : ℂ) * I) +
        deriv riemannZeta ((1 : ℂ) + (t : ℂ) * I) /
          riemannZeta ((1 : ℂ) + (t : ℂ) * I)‖ ≤
      ‖logDeriv archFactor ((1 : ℂ) + (t : ℂ) * I)‖ +
        ‖deriv riemannZeta ((1 : ℂ) + (t : ℂ) * I) /
          riemannZeta ((1 : ℂ) + (t : ℂ) * I)‖ := norm_add_le _ _
    _ ≤ (Real.log |t| / 2 + routeKArchBoundaryConstant) +
        2240 / zetaLowerA * Real.log |t| ^ (9 : ℕ) := add_le_add harch hzeta
    _ ≤ (1 / 2 + routeKArchBoundaryConstant) * (1 + |t|) ^ (9 : ℕ) +
        (2240 / zetaLowerA) * (1 + |t|) ^ (9 : ℕ) := add_le_add harch' hzeta'
    _ = routeKBoundaryGrowthConstant * (1 + |t|) ^ (9 : ℕ) := by
      rw [routeKBoundaryGrowthConstant]
      ring

/-- Global polynomial growth on the boundary line: there is `C ≥ 0` with
`‖-ξ'/ξ(1 + it)‖ ≤ C (1 + |t|)^9` for every real `t`. -/
theorem exists_norm_seamFluxCochain_boundary_global_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖seamFluxCochain ((1 : ℂ) + (t : ℂ) * I)‖ ≤
        C * (1 + |t|) ^ (9 : ℕ) := by
  have han : ∀ t : ℝ,
      AnalyticAt ℂ seamFluxCochain ((1 : ℂ) + (t : ℂ) * I) := by
    intro t
    have hxi : AnalyticAt ℂ xi ((1 : ℂ) + (t : ℂ) * I) :=
      xi_analyticOnNhd_univ _ (Set.mem_univ _)
    have hxi0 : xi ((1 : ℂ) + (t : ℂ) * I) ≠ 0 :=
      xi_ne_zero_of_one_le_re (by simp [Complex.mul_re])
    change AnalyticAt ℂ (fun z => -logDeriv xi z)
      ((1 : ℂ) + (t : ℂ) * I)
    exact (hxi.deriv.div hxi hxi0).neg
  have hcont : Continuous (fun t : ℝ =>
      seamFluxCochain ((1 : ℂ) + (t : ℂ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have harg : ContinuousAt
        (fun u : ℝ => (1 : ℂ) + (u : ℂ) * I) t := by fun_prop
    have houter : ContinuousAt seamFluxCochain
        ((1 : ℂ) + (t : ℂ) * I) := (han t).continuousAt
    have hcomp := ContinuousAt.comp
      (f := fun u : ℝ => (1 : ℂ) + (u : ℂ) * I)
      (g := seamFluxCochain) houter harg
    simpa [Function.comp_def] using hcomp
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
  let C : ℝ := max (max C₀ routeKBoundaryGrowthConstant) 0
  have hC0 : 0 ≤ C := le_max_right _ _
  refine ⟨C, hC0, ?_⟩
  intro t
  have hpow : 1 ≤ (1 + |t|) ^ (9 : ℕ) :=
    one_le_pow₀ (by linarith [abs_nonneg t] : 1 ≤ 1 + |t|)
  by_cases ht : 9 ≤ |t|
  · have hhigh := norm_seamFluxCochain_boundary_le ht
    have hconst : routeKBoundaryGrowthConstant ≤ C :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    have hgrowth0 : 0 ≤ (1 + |t|) ^ (9 : ℕ) := le_trans zero_le_one hpow
    exact hhigh.trans (mul_le_mul_of_nonneg_right hconst hgrowth0)
  · have htmem : t ∈ Set.Icc (-9 : ℝ) 9 := by
      rw [Set.mem_Icc, ← abs_le]
      linarith
    have hlow := hC₀ t htmem
    have hC₀C : C₀ ≤ C :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    calc
      ‖seamFluxCochain ((1 : ℂ) + (t : ℂ) * I)‖ ≤ C₀ := hlow
      _ ≤ C := hC₀C
      _ ≤ C * (1 + |t|) ^ (9 : ℕ) := by nlinarith

end

end RHTower
