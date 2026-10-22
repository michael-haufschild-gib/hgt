import GaloisForLFunctions.RHTower.CCM.CCMPrimeMomentPotentialLaplace
import GaloisForLFunctions.RHTower.LaplaceNegativeRealResidue
import GaloisForLFunctions.RHTower.ZetaLogDerivZeroDistance
import GaloisForLFunctions.RHTower.XiEdgeLogDerivativeBlindness
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadCoherentQuantileGammaNoGo
import GaloisForLFunctions.RHTower.VisibleCoprimeZetaZeroJet

/-!
# Unconditional negative escape of the actual nonlinear prime discrepancy

The source potential has a negative real Laplace residue at the central
point. The negative-residue Landau theorem, retaining compact-head terms,
forces arbitrarily deep continuous excursions. Concavity in square-root
coordinates transfers them exactly to integer entries.

The first-contact minimum principle then proves that
`D_n = primeMassHalf n + (primeMassHalf n)^2/4 - psi n` is unbounded below
on every integer tail. No RH or eventual-sign premise is used. This does
not prove eventual negativity or the canonical-head Gamma--prime--polar sign.
-/

noncomputable section
open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower
namespace RHTower

private theorem central_residue :
    (-logDeriv zetaResidueUnit (1/2 : ℂ)).re = 2+gammaHardyPhaseRate 0 := by
  have hG : zetaResidueUnit (1/2 : ℂ) ≠ 0 := by
    simpa using zetaResidueUnit_ne_zero_of_ofReal_pos (u := (1/2 : ℝ)) (by norm_num)
  have hζ : riemannZeta (1/2 : ℂ) ≠ 0 := by
    intro hz
    apply hG
    rw [zetaResidueUnit, Function.update_of_ne (by norm_num : (1/2 : ℂ) ≠ 1), hz, mul_zero]
  have hu := logDeriv_zeta_eq (s := (1/2 : ℂ)) (by norm_num) hG
  have hz := logDeriv_zeta_eq_logDeriv_xi (s := (1/2 : ℂ)) (by norm_num) (by norm_num) hζ
  have hx : (logDeriv xi (1/2 : ℂ)).re = 0 := by
    simpa [logDeriv_apply] using re_logDeriv_xi_criticalLine 0
  have hΓ : (logDeriv Gammaℝ (1/2 : ℂ)).re = gammaHardyPhaseRate 0 := by
    rw [logDeriv_Gammaℝ_of_re_pos (by norm_num)]
    simp [gammaHardyPhaseRate, linePt]
  have hur := congrArg Complex.re hu
  have hzr := congrArg Complex.re hz
  norm_num [Complex.sub_re, hx, hΓ] at hur hzr
  simp only [Complex.neg_re]
  linarith

private def shiftedPotential (B t : ℝ) : ℝ :=
  (ccmPrimeMomentLogPotential t+B)*Real.exp (-t/4)

private def potentialTransform (B : ℝ) (z : ℂ) : ℂ :=
  -logDeriv zetaResidueUnit (z+1/4)/(2*(z+1/4)*(z-1/4))+B/(z+1/4)

private theorem weighted_shifted (B s t : ℝ) :
    shiftedPotential B t*Real.exp (-s*t) =
      Real.exp (-(s+1/4)*t)*ccmPrimeMomentLogPotential t +
        B*Real.exp (-(s+1/4)*t) := by
  have he : Real.exp (-t/4)*Real.exp (-s*t) = Real.exp (-(s+1/4)*t) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold shiftedPotential
  linear_combination (ccmPrimeMomentLogPotential t+B)*he

private theorem shifted_integrable (B : ℝ) {s : ℝ} (hs : 3/2 < s) :
    IntegrableOn (fun t => shiftedPotential B t*Real.exp (-s*t)) (Ioi 0) := by
  simp_rw [weighted_shifted]
  exact (integrable_ccmPrimeMomentLogPotential (by linarith)).add
    ((exp_neg_integrableOn_Ioi 0 (by linarith : 0 < s+1/4)).const_mul B)

private theorem shifted_laplace (B : ℝ) {s : ℝ} (hs : 3/2 < s) :
    ((∫ t in Ioi (0:ℝ), shiftedPotential B t*Real.exp (-s*t) : ℝ) : ℂ) =
      potentialTransform B (s : ℂ) := by
  simp_rw [weighted_shifted]
  rw [integral_add (integrable_ccmPrimeMomentLogPotential (by linarith))
      ((exp_neg_integrableOn_Ioi 0 (by linarith : 0 < s+1/4)).const_mul B),
    integral_const_mul, integral_exp_neg_mul_Ioi_real (by linarith : 0 < s+1/4)]
  push_cast
  rw [ccmPrimeMomentLogPotential_laplace (by linarith : 1 < s+1/4)]
  unfold potentialTransform
  push_cast
  ring

private theorem log_unit_analytic {z : ℂ} (hz : zetaResidueUnit z ≠ 0) :
    AnalyticAt ℂ (logDeriv zetaResidueUnit) z := by
  change AnalyticAt ℂ (fun w => deriv zetaResidueUnit w / zetaResidueUnit w) z
  exact (analyticAt_zetaResidueUnit z).deriv.div (analyticAt_zetaResidueUnit z) hz

private theorem transform_analytic (B : ℝ) {s : ℝ} (hs : 1/4 < s) :
    AnalyticAt ℂ (potentialTransform B) (s : ℂ) := by
  have hz : zetaResidueUnit ((s : ℂ)+1/4) ≠ 0 := by
    simpa using zetaResidueUnit_ne_zero_of_ofReal_pos (u := s+1/4) (by linarith)
  have hshift : AnalyticAt ℂ (fun z : ℂ => z+1/4) (s : ℂ) := by fun_prop
  have hn : ((s : ℂ)+1/4) ≠ 0 := by
    intro h; have hh := congrArg Complex.re h; norm_num at hh; linarith
  have hd : (s : ℂ)-1/4 ≠ 0 := by
    intro h; have hh := congrArg Complex.re h; norm_num at hh; linarith
  unfold potentialTransform
  have hl := (log_unit_analytic hz).comp (f := fun z : ℂ => z+1/4) hshift
  have hp : AnalyticAt ℂ (fun z : ℂ => 2*(z+1/4)*(z-1/4)) (s : ℂ) := by
    fun_prop
  have hB : AnalyticAt ℂ (fun _z : ℂ => (B : ℂ)) (s : ℂ) := analyticAt_const
  exact (hl.neg.div hp (mul_ne_zero (mul_ne_zero (by norm_num) hn) hd)).add
    (hB.div hshift hn)

private theorem residue_limit (B : ℝ) :
    Tendsto (fun s : ℝ => (s-1/4)*(potentialTransform B (s : ℂ)).re)
      (𝓝[>] (1/4 : ℝ)) (𝓝 (2+gammaHardyPhaseRate 0)) := by
  have hx : Tendsto (fun s : ℝ => s) (𝓝[>] (1/4 : ℝ)) (𝓝 (1/4 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hz : zetaResidueUnit (1/2 : ℂ) ≠ 0 := by
    simpa using zetaResidueUnit_ne_zero_of_ofReal_pos (u := (1/2 : ℝ)) (by norm_num)
  have hl : Tendsto (fun s : ℝ => (-logDeriv zetaResidueUnit ((s : ℂ)+1/4)).re)
      (𝓝[>] (1/4 : ℝ)) (𝓝 (-logDeriv zetaResidueUnit (1/2 : ℂ)).re) := by
    have hc : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] (1/4 : ℝ))
        (𝓝 ((1/4 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto (1/4 : ℝ)).mono_left nhdsWithin_le_nhds
    have hh := (log_unit_analytic hz).continuousAt.tendsto.comp
      (show Tendsto (fun s : ℝ => (s : ℂ)+1/4) (𝓝[>] (1/4 : ℝ)) (𝓝 (1/2 : ℂ)) by
        convert hc.add_const (1/4 : ℂ) using 1; norm_num)
    norm_num at hh
    exact Complex.continuous_re.continuousAt.tendsto.comp hh.neg
  have hd : Tendsto (fun s : ℝ => 2*(s+1/4))
      (𝓝[>] (1/4 : ℝ)) (𝓝 (1 : ℝ)) := by
    convert (hx.add_const (1/4 : ℝ)).const_mul 2 using 1; norm_num
  have hb : Tendsto (fun s : ℝ => (s-1/4)*B/(s+1/4))
      (𝓝[>] (1/4 : ℝ)) (𝓝 (0 : ℝ)) := by
    convert ((hx.sub_const (1/4 : ℝ)).mul_const B).div
      (hx.add_const (1/4 : ℝ)) (by norm_num) using 1
    · rfl
    · norm_num
  have hlim := (hl.div hd (by norm_num)).add hb
  simp only [div_one, add_zero, central_residue] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  change 1/4 < s at hs
  have hn : (s : ℂ)+1/4 ≠ 0 := by
    intro h; have hh := congrArg Complex.re h; norm_num at hh; linarith
  have hd : (s : ℂ)-1/4 ≠ 0 := by
    intro h; have hh := congrArg Complex.re h; norm_num at hh; linarith
  have heq : ((s : ℂ)-1/4)*potentialTransform B (s : ℂ) =
      -logDeriv zetaResidueUnit ((s : ℂ)+1/4)/(2*((s : ℂ)+1/4)) +
        ((s : ℂ)-1/4)*B/((s : ℂ)+1/4) := by
    unfold potentialTransform
    rw [mul_add, div_mul_eq_div_div, mul_div_cancel₀ _ hd]
    ring
  have hcast : ((s : ℂ)-1/4) = ((s-1/4 : ℝ) : ℂ) := by push_cast; rfl
  have hcast' : ((s : ℂ)+1/4) = ((s+1/4 : ℝ) : ℂ) := by push_cast; rfl
  have hh := congrArg Complex.re heq
  rw [hcast, hcast'] at hh
  have hden : 2*((s+1/4 : ℝ) : ℂ) = ((2*(s+1/4) : ℝ) : ℂ) := by push_cast; rfl
  rw [hden] at hh
  simp only [Complex.add_re, Complex.div_ofReal_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hh
  convert hh.symm using 1; push_cast; rfl

/-- The literal continuous prime potential escapes below every fixed level on every tail. -/
theorem ccmPrimeMomentLogPotential_negative_escape (B H : ℝ) :
    ∃ T : ℝ, max 0 H < T ∧ ccmPrimeMomentLogPotential T < -B := by
  have hn := not_eventually_nonneg_of_negative_real_laplace_residue
    (g := shiftedPotential B) (G := potentialTransform B)
    (show Continuous (shiftedPotential B) from
      (continuous_ccmPrimeMomentLogPotential.add continuous_const).mul
        (by fun_prop))
    (fun s hs => shifted_integrable B hs) (fun s hs => shifted_laplace B hs)
    (fun s hs => transform_analytic B hs)
    (κ := -(2+gammaHardyPhaseRate 0))
    (by linarith [two_gammaHardyPhaseRate_zero_add_four_neg])
    (by simpa only [neg_neg] using residue_limit B)
  by_contra! h
  apply hn
  refine ⟨max 0 H, fun T hT => ?_⟩
  unfold shiftedPotential
  exact mul_nonneg (by linarith [h T hT]) (Real.exp_pos _).le

/-- Exact concavity between arithmetic entries transfers a continuous low value to an endpoint. -/
theorem ccmPrimeMomentLogPotential_cell_lower {x : ℝ} (hx : 1 ≤ x) :
    min (ccmPrimeMomentPotential ⌊x⌋₊) (ccmPrimeMomentPotential (⌊x⌋₊+1)) ≤
      ccmPrimeMomentLogPotential (Real.log x) := by
  let n := ⌊x⌋₊
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hn : (n : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxnext : x < (n : ℝ)+1 := Nat.lt_floor_add_one x
  have ha : Real.sqrt n ≤ Real.sqrt x := Real.sqrt_le_sqrt hn
  have hb : Real.sqrt x ≤ Real.sqrt (n+1 : ℕ) :=
    Real.sqrt_le_sqrt (by push_cast; linarith)
  have hqa := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
  have hqb := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (n+1))
  have hqx := Real.sq_sqrt hx0.le
  have hm : primeMassHalf x = primeMassHalf n := by simp [primeMassHalf, n]
  have hpsi : Chebyshev.psi x = Chebyshev.psi n := by simp [Chebyshev.psi_eq_sum_Icc, n]
  have hu₀ : ccmPrimeMomentPotential n =
      Real.sqrt n*(primeMassHalf n+2)-n-Chebyshev.psi n-1 := rfl
  have hu₁ : ccmPrimeMomentPotential (n+1) =
      Real.sqrt (n+1 : ℕ)*(primeMassHalf n+2)-(n+1 : ℕ)-Chebyshev.psi n-1 := by
    have hh := ccmPrimeMomentPotential_succ_sub n
    rw [hu₀] at hh
    nlinarith only [hh, hqa, hqb]
  rw [ccmPrimeMomentLogPotential_eq_source (Real.log_nonneg hx), Real.exp_log hx0, hm, hpsi]
  change min (ccmPrimeMomentPotential n) (ccmPrimeMomentPotential (n+1)) ≤ _
  by_cases hc : 2*Real.sqrt x ≤ primeMassHalf n+2
  · apply (min_le_left _ _).trans
    rw [hu₀]
    have hh := mul_nonneg (sub_nonneg.mpr ha)
      (show 0 ≤ primeMassHalf n+2-Real.sqrt x-Real.sqrt n by linarith)
    nlinarith only [hh, hqa, hqx]
  · apply (min_le_right _ _).trans
    rw [hu₁]
    have hh := mul_nonneg (sub_nonneg.mpr hb)
      (show 0 ≤ Real.sqrt (n+1 : ℕ)+Real.sqrt x-(primeMassHalf n+2) by linarith)
    nlinarith only [hh, hqb, hqx]

/-- Unconditional negative escape of the actual integer prime-moment potential. -/
theorem ccmPrimeMomentPotential_negative_escape (B : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ccmPrimeMomentPotential n < -B := by
  obtain ⟨T, hT, hU⟩ := ccmPrimeMomentLogPotential_negative_escape B (Real.log ((N : ℝ)+1))
  have hT0 : 0 < T := (le_max_left _ _).trans_lt hT
  have hTN : Real.log ((N : ℝ)+1) < T := (le_max_right _ _).trans_lt hT
  have hx : (N : ℝ)+1 < Real.exp T := by
    have h := Real.exp_lt_exp.mpr hTN
    rwa [Real.exp_log (by positivity)] at h
  have hn : N ≤ ⌊Real.exp T⌋₊ := Nat.le_floor (by linarith)
  have hc := ccmPrimeMomentLogPotential_cell_lower (Real.one_le_exp hT0.le)
  rw [Real.log_exp] at hc
  have hmin := hc.trans_lt hU
  rcases min_lt_iff.mp hmin with hl | hr
  · exact ⟨_, hn, hl⟩
  · exact ⟨_, hn.trans (Nat.le_succ _), hr⟩

/-- The positive nonlinear square cannot keep the actual prime discrepancy above
any fixed level on any integer tail. -/
theorem ccmPrimeMomentDiscrepancy_negative_escape (B : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ccmPrimeMomentDiscrepancy n < -B := by
  by_contra! hpos
  have hl := ccmPrimeMomentPotential_lower_of_forcing_lower (-B) N hpos
  obtain ⟨n, hn, hneg⟩ := ccmPrimeMomentPotential_negative_escape
    (-min (ccmPrimeMomentPotential N) (-B-1)) N
  have hh := hl n hn
  linarith

/-- Negative actual nonlinear forcing occurs beyond every integer cutoff. -/
theorem ccmPrimeMomentDiscrepancy_negative_cofinally (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ccmPrimeMomentDiscrepancy n < 0 := by
  simpa using ccmPrimeMomentDiscrepancy_negative_escape 0 N

/-- The negative central residue survives a positive shift at critical scale.
This is an unconditional excursion theorem, not an eventual sign assertion. -/
theorem ccmPrimeMomentLogPotential_critical_negative_escape
    (c : ℝ) (hc : c < -(2+gammaHardyPhaseRate 0)) (H : ℝ) :
    ∃ T : ℝ, max 0 H < T ∧
      ccmPrimeMomentLogPotential T < -c*Real.exp (T/2) := by
  let g : ℝ → ℝ := fun t => shiftedPotential 0 t+c*Real.exp (t/4)
  let G : ℂ → ℂ := fun z => potentialTransform 0 z+(c : ℂ)/(z-1/4)
  have hw (s t : ℝ) : g t*Real.exp (-s*t) =
      shiftedPotential 0 t*Real.exp (-s*t)+c*Real.exp (-(s-1/4)*t) := by
    have he : Real.exp (t/4)*Real.exp (-s*t) = Real.exp (-(s-1/4)*t) := by
      rw [← Real.exp_add]; congr 1; ring
    dsimp [g]
    linear_combination c*he
  have hi (s : ℝ) (hs : 3/2 < s) :
      IntegrableOn (fun t => g t*Real.exp (-s*t)) (Ioi 0) := by
    simp_rw [hw]
    exact (shifted_integrable 0 hs).add
      ((exp_neg_integrableOn_Ioi 0 (by linarith : 0 < s-1/4)).const_mul c)
  have ht (s : ℝ) (hs : 3/2 < s) :
      ((∫ t in Ioi (0:ℝ), g t*Real.exp (-s*t) : ℝ) : ℂ) = G (s : ℂ) := by
    simp_rw [hw]
    rw [integral_add (shifted_integrable 0 hs)
      ((exp_neg_integrableOn_Ioi 0 (by linarith : 0 < s-1/4)).const_mul c),
      integral_const_mul, integral_exp_neg_mul_Ioi_real (by linarith : 0 < s-1/4)]
    push_cast
    rw [shifted_laplace 0 hs]
    dsimp [G]
    ring
  have ha (s : ℝ) (hs : 1/4 < s) : AnalyticAt ℂ G (s : ℂ) := by
    have hd : (s : ℂ)-1/4 ≠ 0 := by
      intro h; have hh := congrArg Complex.re h; norm_num at hh; linarith
    exact (transform_analytic 0 hs).add
      (analyticAt_const.div (by fun_prop) hd)
  have hr : Tendsto (fun s : ℝ => (s-1/4)*(G (s : ℂ)).re)
      (𝓝[>] (1/4 : ℝ)) (𝓝 (2+gammaHardyPhaseRate 0+c)) := by
    apply ((residue_limit 0).add_const c).congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    change 1/4 < s at hs
    have hn : s-1/4 ≠ 0 := by linarith
    dsimp [G]
    have he : ((c : ℂ)/((s : ℂ)-1/4)).re = c/(s-1/4) := by
      rw [show (s : ℂ)-1/4 = ((s-1/4 : ℝ) : ℂ) by push_cast; rfl]
      simp only [Complex.div_ofReal_re, Complex.ofReal_re]
    rw [he, mul_add, mul_div_cancel₀ _ hn]
  have hn := not_eventually_nonneg_of_negative_real_laplace_residue
    (g := g) (G := G)
    (show Continuous g from
      ((continuous_ccmPrimeMomentLogPotential.add continuous_const).mul
        (by fun_prop)).add (by fun_prop)) hi ht ha
    (κ := -(2+gammaHardyPhaseRate 0+c)) (by linarith)
    (by simpa only [neg_neg] using hr)
  by_contra! h
  apply hn
  refine ⟨max 0 H, fun T hT => ?_⟩
  have he : Real.exp (T/2)*Real.exp (-T/4) = Real.exp (T/4) := by
    rw [← Real.exp_add]; congr 1; ring
  have hh := mul_nonneg (show 0 ≤ ccmPrimeMomentLogPotential T+c*Real.exp (T/2) by
    linarith [h T hT]) (Real.exp_pos (-T/4)).le
  dsimp [g, shiftedPotential]
  rw [add_mul, mul_assoc, he] at hh
  simpa only [add_zero] using hh

private theorem tilted_cell_lower (c : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    min (ccmPrimeMomentPotential ⌊x⌋₊+c*Real.sqrt ⌊x⌋₊)
      (ccmPrimeMomentPotential (⌊x⌋₊+1)+c*Real.sqrt (⌊x⌋₊+1 : ℕ)) ≤
      ccmPrimeMomentLogPotential (Real.log x)+c*Real.sqrt x := by
  let n := ⌊x⌋₊
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hn : (n : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxnext : x < (n : ℝ)+1 := Nat.lt_floor_add_one x
  have ha : Real.sqrt n ≤ Real.sqrt x := Real.sqrt_le_sqrt hn
  have hb : Real.sqrt x ≤ Real.sqrt (n+1 : ℕ) :=
    Real.sqrt_le_sqrt (by push_cast; linarith)
  have hqa := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
  have hqb := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (n+1))
  have hqx := Real.sq_sqrt hx0.le
  have hm : primeMassHalf x = primeMassHalf n := by simp [primeMassHalf, n]
  have hp : Chebyshev.psi x = Chebyshev.psi n := by simp [Chebyshev.psi_eq_sum_Icc, n]
  have hu₀ : ccmPrimeMomentPotential n+c*Real.sqrt n =
      Real.sqrt n*(primeMassHalf n+2+c)-n-Chebyshev.psi n-1 := by
    unfold ccmPrimeMomentPotential; ring
  have hu₁ : ccmPrimeMomentPotential (n+1)+c*Real.sqrt (n+1 : ℕ) =
      Real.sqrt (n+1 : ℕ)*(primeMassHalf n+2+c)-(n+1 : ℕ)-Chebyshev.psi n-1 := by
    have hh := ccmPrimeMomentPotential_succ_sub n
    unfold ccmPrimeMomentPotential at hh ⊢
    nlinarith only [hh, hqa, hqb]
  rw [ccmPrimeMomentLogPotential_eq_source (Real.log_nonneg hx), Real.exp_log hx0, hm, hp]
  change min (ccmPrimeMomentPotential n+c*Real.sqrt n)
    (ccmPrimeMomentPotential (n+1)+c*Real.sqrt (n+1 : ℕ)) ≤ _
  by_cases hc : 2*Real.sqrt x ≤ primeMassHalf n+2+c
  · apply (min_le_left _ _).trans
    rw [hu₀]
    have hh := mul_nonneg (sub_nonneg.mpr ha)
      (show 0 ≤ primeMassHalf n+2+c-Real.sqrt x-Real.sqrt n by linarith)
    nlinarith only [hh, hqa, hqx]
  · apply (min_le_right _ _).trans
    rw [hu₁]
    have hh := mul_nonneg (sub_nonneg.mpr hb)
      (show 0 ≤ Real.sqrt (n+1 : ℕ)+Real.sqrt x-(primeMassHalf n+2+c) by linarith)
    nlinarith only [hh, hqb, hqx]

/-- The critical-scale negative excursions persist at literal integer cutoffs. -/
theorem ccmPrimeMomentPotential_critical_negative_escape
    (c : ℝ) (hc : c < -(2+gammaHardyPhaseRate 0)) (N : ℕ) :
    ∃ n : ℕ, max 1 N ≤ n ∧ ccmPrimeMomentPotential n < -c*Real.sqrt n := by
  obtain ⟨T,hT,hU⟩ := ccmPrimeMomentLogPotential_critical_negative_escape c hc
    (Real.log ((max 1 N : ℕ)+1))
  have hT0 : 0 < T := (le_max_left _ _).trans_lt hT
  have hTN : Real.log ((max 1 N : ℕ)+1) < T := (le_max_right _ _).trans_lt hT
  have hx : (max 1 N : ℕ)+1 < Real.exp T := by
    have hh := Real.exp_lt_exp.mpr hTN
    rwa [Real.exp_log (by positivity)] at hh
  have hn : max 1 N ≤ ⌊Real.exp T⌋₊ := Nat.le_floor (by linarith)
  have hc' := tilted_cell_lower c (Real.one_le_exp hT0.le)
  have he : Real.sqrt (Real.exp T) = Real.exp (T/2) := by
    have heq : Real.exp (T/2)^2 = Real.exp T := by
      rw [sq, ← Real.exp_add, add_halves]
    rw [← heq, Real.sqrt_sq (Real.exp_pos _).le]
  rw [Real.log_exp, he] at hc'
  have hm : min (ccmPrimeMomentPotential ⌊Real.exp T⌋₊+c*Real.sqrt ⌊Real.exp T⌋₊)
      (ccmPrimeMomentPotential (⌊Real.exp T⌋₊+1)+c*Real.sqrt (⌊Real.exp T⌋₊+1 : ℕ)) < 0 := by
    linarith
  rcases min_lt_iff.mp hm with hl | hr
  · exact ⟨_,hn,by linarith⟩
  · exact ⟨_,hn.trans (Nat.le_succ _),by linarith⟩

/-- A strictly negative critical-scale amplitude occurs on every arithmetic tail,
without an RH, zero-location or source-sign premise. -/
theorem ccmPrimeMomentPotential_critical_negative_cofinally :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ, max 1 N ≤ n ∧
      ccmPrimeMomentPotential n < -c*Real.sqrt n := by
  have hk : 0 < -(2+gammaHardyPhaseRate 0) := by
    linarith [two_gammaHardyPhaseRate_zero_add_four_neg]
  refine ⟨-(2+gammaHardyPhaseRate 0)/2, by linarith, fun N => ?_⟩
  exact ccmPrimeMomentPotential_critical_negative_escape _ (by linarith) N

end RHTower
