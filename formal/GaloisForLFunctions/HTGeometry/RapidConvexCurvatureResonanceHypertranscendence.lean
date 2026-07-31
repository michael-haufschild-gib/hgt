import GaloisForLFunctions.HTGeometry.RapidConvexCurvatureResonance
import GaloisForLFunctions.HTGeometry.LogWeibullFiniteDifference
import GaloisForLFunctions.HTGeometry.StretchedExponentialMagnitudeHypertranscendence

open Filter Finset PowerSeries MvPolynomial Polynomial Set Asymptotics Topology

namespace GaloisForLFunctions

noncomputable section

/-- The log-Weibull profile with its single degenerate initial value repaired. -/
def admissibleLogWeibullProfile (γ : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 1 / 2 else logWeibull γ n

@[simp] theorem admissibleLogWeibullProfile_zero (γ : ℝ) :
    admissibleLogWeibullProfile γ 0 = 1 / 2 := by
  simp [admissibleLogWeibullProfile]

theorem admissibleLogWeibullProfile_eq {γ : ℝ} {n : ℕ} (hn : 0 < n) :
    admissibleLogWeibullProfile γ n = logWeibull γ n := by
  simp [admissibleLogWeibullProfile, hn.ne']

theorem admissibleLogWeibullProfile_positive (γ : ℝ) (n : ℕ) :
    0 < admissibleLogWeibullProfile γ n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · rw [admissibleLogWeibullProfile_eq hn]
    exact Real.exp_pos _

theorem admissibleLogWeibullProfile_strictMono {γ : ℝ} (hγ : 1 < γ) :
    StrictMono (admissibleLogWeibullProfile γ) := by
  intro m n hmn
  rcases m.eq_zero_or_pos with rfl | hm
  · rw [admissibleLogWeibullProfile_zero,
      admissibleLogWeibullProfile_eq (Nat.zero_lt_of_lt hmn)]
    have hlog : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt hmn)))
    have hexp : 1 ≤ logWeibull γ n := by
      dsimp [logWeibull, stretchedExp]
      exact Real.one_le_exp (Real.rpow_nonneg hlog γ)
    linarith
  · rw [admissibleLogWeibullProfile_eq hm,
      admissibleLogWeibullProfile_eq (hm.trans hmn)]
    have hmlog : Real.log (m : ℝ) < Real.log (n : ℝ) :=
      Real.strictMonoOn_log
        (by simpa only [Set.mem_Ioi] using (show (0 : ℝ) < (m : ℝ) by exact_mod_cast hm))
        (by simpa only [Set.mem_Ioi] using
          (show (0 : ℝ) < (n : ℝ) by exact_mod_cast (hm.trans hmn)))
        (by exact_mod_cast hmn)
    have hpow : (Real.log (m : ℝ)) ^ γ < (Real.log (n : ℝ)) ^ γ := by
      exact Real.rpow_lt_rpow (Real.log_nonneg (by exact_mod_cast hm)) hmlog (by linarith)
    exact Real.exp_lt_exp.mpr hpow

theorem rapidIncrement_admissibleLogWeibullProfile {γ : ℝ} {n : ℕ} (hn : 0 < n) :
    rapidIncrement (admissibleLogWeibullProfile γ) n =
      logWeibullFiniteDifference γ logWeibullFirstStencil n := by
  rw [logWeibullFiniteDifference_first]
  dsimp [rapidIncrement]
  rw [admissibleLogWeibullProfile_eq hn,
    admissibleLogWeibullProfile_eq (show 0 < n + 1 by omega)]
  norm_num

theorem rapidCurvature_admissibleLogWeibullProfile {γ : ℝ} {n : ℕ} (hn : 0 < n) :
    rapidCurvature (admissibleLogWeibullProfile γ) n =
      logWeibullFiniteDifference γ logWeibullSecondStencil n := by
  rw [logWeibullFiniteDifference_second]
  dsimp [rapidCurvature]
  rw [admissibleLogWeibullProfile_eq hn,
    admissibleLogWeibullProfile_eq (show 0 < n + 1 by omega),
    admissibleLogWeibullProfile_eq (show 0 < n + 2 by omega)]
  norm_num

/-- A positive packet which dominates `log x` also dominates the card's `log (x + 2)` scale. -/
theorem tendsto_abs_div_log_add_two_atTop_of_log_isLittleO
    {f : ℝ → ℝ} (hne : ∀ᶠ x : ℝ in atTop, f x ≠ 0)
    (hlog : Real.log =o[atTop] fun x => |f x|) :
    Tendsto (fun x : ℝ => |f x| / Real.log (x + 2)) atTop atTop := by
  have habsne : ∀ᶠ x : ℝ in atTop, |f x| ≠ 0 := hne.mono fun _ hx => abs_ne_zero.mpr hx
  have hzero : Tendsto (fun x : ℝ => Real.log x / |f x|) atTop (𝓝 0) :=
    (isLittleO_iff_tendsto' (habsne.mono fun _ hx hzero => (hx hzero).elim)).mp hlog
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < Real.log x / |f x| := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), hne] with x hx hfx
    exact div_pos (Real.log_pos hx) (abs_pos.mpr hfx)
  have hzeroPos : Tendsto (fun x : ℝ => Real.log x / |f x|) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  have htop : Tendsto (fun x : ℝ => |f x| / Real.log x) atTop atTop := by
    refine hzeroPos.inv_tendsto_nhdsGT_zero.congr' ?_
    filter_upwards with x
    rw [Pi.inv_apply, inv_div]
  have hlogRatio : Tendsto (fun x : ℝ => Real.log x / Real.log (x + 2))
      atTop (𝓝 1) := by
    have hinv := (tendsto_log_add_div_log 2).inv₀ one_ne_zero
    simpa only [inv_div, inv_one] using hinv
  have hprod := htop.atTop_mul_pos zero_lt_one hlogRatio
  simpa only using hprod.congr' (by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hlogx : Real.log x ≠ 0 := (Real.log_pos hx).ne'
    have hlogx2 : Real.log (x + 2) ≠ 0 := (Real.log_pos (by linarith)).ne'
    field_simp)

theorem admissibleLogWeibullProfile_curvaturePositive
    {γ : ℝ} (hγ : 1 < γ) :
    ∀ᶠ n : ℕ in atTop, 0 < rapidCurvature (admissibleLogWeibullProfile γ) n := by
  have hcancel : ∀ k < 2, stretchedMoment logWeibullSecondStencil k = 0 := by
    intro k hk
    interval_cases k <;> simp [logWeibullSecondStencil_moments]
  have hpos := eventually_pos_logWeibullFiniteDifference hγ logWeibullSecondStencil 2
    hcancel (by rw [logWeibullSecondStencil_moments.2.2]; norm_num)
  have hnat := tendsto_natCast_atTop_atTop.eventually hpos
  filter_upwards [hnat, eventually_ge_atTop 1] with n hn hnone
  rw [rapidCurvature_admissibleLogWeibullProfile (by omega)]
  exact hn

theorem admissibleLogWeibullProfile_adjacentRatioOne
    {γ : ℝ} (hγ : 1 < γ) :
    Tendsto (fun n : ℕ =>
      admissibleLogWeibullProfile γ (n + 1) / admissibleLogWeibullProfile γ n)
      atTop (𝓝 1) := by
  have hreal := tendsto_logWeibull_fixedShift_ratio hγ (show (0 : ℝ) ≤ 1 by norm_num)
  refine (hreal.comp tendsto_natCast_atTop_atTop).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [admissibleLogWeibullProfile_eq (by omega),
    admissibleLogWeibullProfile_eq (by omega)]
  norm_num

theorem admissibleLogWeibullProfile_curvatureShiftStable
    {γ : ℝ} (hγ : 1 < γ) (r : ℕ) :
    Tendsto (fun n : ℕ =>
      rapidCurvature (admissibleLogWeibullProfile γ) (n + r) /
        rapidCurvature (admissibleLogWeibullProfile γ) n) atTop (𝓝 1) := by
  have hcancel : ∀ k < 2, stretchedMoment logWeibullSecondStencil k = 0 := by
    intro k hk
    interval_cases k <;> simp [logWeibullSecondStencil_moments]
  have hreal := tendsto_logWeibullFiniteDifference_fixedShift_ratio hγ
    logWeibullSecondStencil 2 hcancel
    (by rw [logWeibullSecondStencil_moments.2.2]; norm_num)
    r (by positivity)
  refine (hreal.comp tendsto_natCast_atTop_atTop).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [rapidCurvature_admissibleLogWeibullProfile (by omega),
    rapidCurvature_admissibleLogWeibullProfile (by omega)]
  norm_num

theorem admissibleLogWeibullProfile_curvatureOverIncrementZero
    {γ : ℝ} (hγ : 1 < γ) :
    Tendsto (fun n : ℕ =>
      rapidCurvature (admissibleLogWeibullProfile γ) n /
        rapidIncrement (admissibleLogWeibullProfile γ) n) atTop (𝓝 0) := by
  have hcancel₁ : ∀ k < 1, stretchedMoment logWeibullFirstStencil k = 0 := by
    intro k hk
    interval_cases k
    exact logWeibullFirstStencil_moments.1
  have hcancel₂ : ∀ k < 2, stretchedMoment logWeibullSecondStencil k = 0 := by
    intro k hk
    interval_cases k <;> simp [logWeibullSecondStencil_moments]
  have heq₁ := logWeibullFiniteDifference_isEquivalent hγ logWeibullFirstStencil 1
    hcancel₁ (by rw [logWeibullFirstStencil_moments.2]; norm_num)
  have heq₂ := logWeibullFiniteDifference_isEquivalent hγ logWeibullSecondStencil 2
    hcancel₂ (by rw [logWeibullSecondStencil_moments.2.2]; norm_num)
  have hlead : Tendsto (fun x : ℝ =>
      logWeibullFiniteDifferenceLeading γ logWeibullSecondStencil 2 x /
        logWeibullFiniteDifferenceLeading γ logWeibullFirstStencil 1 x)
      atTop (𝓝 0) := by
    have ht := (tendsto_log_rpow_div_id_zero (γ - 1)).const_mul γ
    simpa only [mul_zero] using ht.congr' (by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      have hx0 : x ≠ 0 := by linarith
      have hlog : 0 < Real.log x := Real.log_pos hx
      dsimp [logWeibullFiniteDifferenceLeading, logWeibullDerivativeLeading]
      rw [logWeibullFirstStencil_moments.2, logWeibullSecondStencil_moments.2.2]
      norm_num
      dsimp [logWeibull, stretchedExp]
      field_simp [pow_ne_zero _ (by linarith : γ ≠ 0), Real.exp_ne_zero,
        ne_of_gt (Real.rpow_pos_of_pos hlog _), zpow_ne_zero _ hx0]
      exact (Real.rpow_mul_natCast hlog.le (γ - 1) 2).symm)
  have hquot := heq₂.div heq₁
  have hreal : Tendsto (fun x : ℝ =>
      logWeibullFiniteDifference γ logWeibullSecondStencil x /
        logWeibullFiniteDifference γ logWeibullFirstStencil x) atTop (𝓝 0) :=
    hquot.tendsto_nhds_iff.mpr hlead
  refine (hreal.comp tendsto_natCast_atTop_atTop).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [Function.comp_apply]
  rw [rapidCurvature_admissibleLogWeibullProfile (by omega),
    rapidIncrement_admissibleLogWeibullProfile (by omega)]

theorem admissibleLogWeibullProfile_rapidlyVarying
    {γ : ℝ} (hγ : 1 < γ) :
    RapidlyVarying (admissibleLogWeibullProfile γ) := by
  intro c hc
  let c₀ : ℝ := (c + 1) / 2
  have hc₀ : 1 < c₀ := by dsimp [c₀]; linarith
  have hc₀c : c₀ < c := by dsimp [c₀]; linarith
  have hgap : 0 < c - c₀ := sub_pos.mpr hc₀c
  have hreal := (tendsto_logWeibull_mul_div_atTop hγ hc₀).comp
    tendsto_natCast_atTop_atTop
  refine tendsto_atTop_mono' atTop ?_ hreal
  have hnlarge := tendsto_natCast_atTop_atTop.eventually_gt_atTop (1 / (c - c₀))
  filter_upwards [hnlarge, eventually_ge_atTop 1] with n hnlarge hn
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hscaled : 1 < (c - c₀) * (n : ℝ) := by
    rw [div_lt_iff₀ hgap] at hnlarge
    simpa [mul_comm] using hnlarge
  have hfloor : c₀ * (n : ℝ) < (⌊c * (n : ℝ)⌋₊ : ℝ) := by
    have hfloorUpper := Nat.lt_floor_add_one (c * (n : ℝ))
    linarith
  have hfloorPos : 0 < ⌊c * (n : ℝ)⌋₊ := by
    have : (0 : ℝ) < (⌊c * (n : ℝ)⌋₊ : ℝ) :=
      (mul_pos (zero_lt_one.trans hc₀) (by positivity)).trans hfloor
    exact_mod_cast this
  have hprofileLe : logWeibull γ (c₀ * (n : ℝ)) ≤
      logWeibull γ (⌊c * (n : ℝ)⌋₊ : ℝ) := by
    dsimp [logWeibull, stretchedExp]
    apply Real.exp_le_exp.mpr
    apply Real.rpow_le_rpow
    · apply Real.log_nonneg
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ ≤ c₀ * (n : ℝ) := mul_le_mul hc₀.le hnreal (by positivity) (by positivity)
    · exact Real.log_le_log (mul_pos (zero_lt_one.trans hc₀) (by positivity)) hfloor.le
    · linarith
  have hden : 0 < logWeibull γ (n : ℝ) := Real.exp_pos _
  calc
    logWeibull γ (c₀ * (n : ℝ)) / logWeibull γ (n : ℝ) ≤
        logWeibull γ (⌊c * (n : ℝ)⌋₊ : ℝ) / logWeibull γ (n : ℝ) :=
      div_le_div_of_nonneg_right hprofileLe hden.le
    _ = admissibleLogWeibullProfile γ ⌊c * (n : ℝ)⌋₊ /
        admissibleLogWeibullProfile γ n := by
      rw [admissibleLogWeibullProfile_eq hfloorPos,
        admissibleLogWeibullProfile_eq (by omega)]

theorem admissibleLogWeibullProfile_curvatureOverLogAtTop
    {γ : ℝ} (hγ : 1 < γ) :
    Tendsto (fun n : ℕ =>
      rapidCurvature (admissibleLogWeibullProfile γ) n /
        Real.log ((n : ℝ) + 2)) atTop atTop := by
  have hcancel : ∀ k < 2, stretchedMoment logWeibullSecondStencil k = 0 := by
    intro k hk
    interval_cases k <;> simp [logWeibullSecondStencil_moments]
  have hpos := eventually_pos_logWeibullFiniteDifference hγ logWeibullSecondStencil 2
    hcancel (by rw [logWeibullSecondStencil_moments.2.2]; norm_num)
  have htop := tendsto_abs_div_log_add_two_atTop_of_log_isLittleO
    (hpos.mono fun _ hx => hx.ne')
    (log_isLittleO_abs_logWeibullFiniteDifference hγ logWeibullSecondStencil 2
      hcancel (by rw [logWeibullSecondStencil_moments.2.2]; norm_num))
  refine (htop.comp tendsto_natCast_atTop_atTop).congr' ?_
  have hnatpos := tendsto_natCast_atTop_atTop.eventually hpos
  filter_upwards [hnatpos, eventually_ge_atTop 1] with n hfn hn
  simp only [Function.comp_apply]
  rw [rapidCurvature_admissibleLogWeibullProfile (by omega), abs_of_pos hfn]

/-- Log-Weibull profiles satisfy the complete rapid-convex interface used by the resonance law. -/
theorem admissiblyRapidConvex_admissibleLogWeibullProfile
    {γ : ℝ} (hγ : 1 < γ) :
    AdmissiblyRapidConvex (admissibleLogWeibullProfile γ) where
  positive := admissibleLogWeibullProfile_positive γ
  strictMono := admissibleLogWeibullProfile_strictMono hγ
  curvaturePositive := admissibleLogWeibullProfile_curvaturePositive hγ
  adjacentRatioOne := admissibleLogWeibullProfile_adjacentRatioOne hγ
  curvatureShiftStable := admissibleLogWeibullProfile_curvatureShiftStable hγ
  curvatureOverIncrementZero := admissibleLogWeibullProfile_curvatureOverIncrementZero hγ
  rapidlyVarying := admissibleLogWeibullProfile_rapidlyVarying hγ
  curvatureOverLogAtTop := admissibleLogWeibullProfile_curvatureOverLogAtTop hγ

/-- Polynomial coefficient stencils evaluate the log-Weibull finite difference literally. -/
theorem logWeibullFiniteDifference_polynomialRealCoeffFinsupp
    (Q : Polynomial ℤ) (γ x : ℝ) :
    logWeibullFiniteDifference γ (polynomialRealCoeffFinsupp Q) x =
      ∑ j ∈ Finset.range (Q.natDegree + 1),
        (Q.coeff j : ℝ) * logWeibull γ (x + j) := by
  rw [logWeibullFiniteDifference, Finsupp.sum_of_support_subset
    (s := Finset.range (Q.natDegree + 1))]
  · apply Finset.sum_congr rfl
    intro j hj
    simp
  · intro j hj
    simp only [Finsupp.mem_support_iff, polynomialRealCoeffFinsupp_apply, ne_eq] at hj
    have hj' : Q.coeff j ≠ 0 := fun hz => hj (by simp [hz])
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Polynomial.le_natDegree_of_ne_zero hj'))
  · intro i hi
    simp

theorem polynomialShiftOperator_admissibleLogWeibullProfile_eventuallyEq
    (Q : Polynomial ℤ) (γ : ℝ) :
    (fun n => polynomialShiftOperator Q (admissibleLogWeibullProfile γ) n) =ᶠ[atTop]
      fun n => logWeibullFiniteDifference γ (polynomialRealCoeffFinsupp Q) n := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [polynomialShiftOperator_apply,
    logWeibullFiniteDifference_polynomialRealCoeffFinsupp]
  apply Finset.sum_congr rfl
  intro j hj
  rw [admissibleLogWeibullProfile_eq (by omega)]
  norm_num

/-- Every nonzero integer shift polynomial of the log-Weibull curvature dominates logarithms. -/
theorem logarithmicallyShiftSeparated_rapidCurvature_admissibleLogWeibullProfile
    {γ : ℝ} (hγ : 1 < γ) :
    LogarithmicallyShiftSeparated
      (rapidCurvature (admissibleLogWeibullProfile γ)) := by
  intro R hR
  let Q : Polynomial ℤ := R * ((Polynomial.X : Polynomial ℤ) - 1) ^ 2
  have hQ : Q ≠ 0 := by
    dsimp [Q]
    exact mul_ne_zero hR (pow_ne_zero _ (by
      simpa using (Polynomial.X_sub_C_ne_zero (R := ℤ) 1)))
  obtain ⟨j₀, _hjdeg, hj₀⟩ := exists_stretchedMoment_ne_of_polynomial hQ
  have hex : ∃ j, stretchedMoment (polynomialRealCoeffFinsupp Q) j ≠ 0 :=
    ⟨j₀, hj₀⟩
  let j := Nat.find hex
  have hj : stretchedMoment (polynomialRealCoeffFinsupp Q) j ≠ 0 := Nat.find_spec hex
  have hcancel : ∀ k < j, stretchedMoment (polynomialRealCoeffFinsupp Q) k = 0 := by
    intro k hk
    by_contra hkne
    have hle := Nat.find_min' hex hkne
    dsimp [j] at hk
    omega
  let d := polynomialRealCoeffFinsupp Q
  let L := logWeibullFiniteDifferenceLeading γ d j
  have hLne : ∀ᶠ x : ℝ in atTop, L x ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hlog : 0 < Real.log x := Real.log_pos hx
    dsimp [L, d, logWeibullFiniteDifferenceLeading, logWeibullDerivativeLeading,
      logWeibull, stretchedExp]
    exact mul_ne_zero
      (div_ne_zero hj (by positivity))
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero (pow_ne_zero _ (by linarith : γ ≠ 0)) (Real.exp_ne_zero _))
          (ne_of_gt (Real.rpow_pos_of_pos hlog _)))
        (zpow_ne_zero _ (by linarith : x ≠ 0)))
  have hFL : Tendsto (fun x : ℝ => logWeibullFiniteDifference γ d x / L x)
      atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one hLne).mp
      (logWeibullFiniteDifference_isEquivalent hγ d j hcancel hj)
  have hFne : ∀ᶠ x : ℝ in atTop, logWeibullFiniteDifference γ d x ≠ 0 :=
    (hFL.eventually_const_lt (show (0 : ℝ) < 1 by norm_num)).mono fun x hx hzero => by
      rw [hzero, zero_div] at hx
      linarith
  have htopReal := tendsto_abs_div_log_add_two_atTop_of_log_isLittleO hFne
    (log_isLittleO_abs_logWeibullFiniteDifference hγ d j hcancel hj)
  have htopNat := htopReal.comp tendsto_natCast_atTop_atTop
  refine htopNat.congr' ?_
  have hprofileEq := polynomialShiftOperator_admissibleLogWeibullProfile_eventuallyEq Q γ
  filter_upwards [hprofileEq] with n hn
  simp only [Function.comp_apply]
  have hfactor := congrFun
    (polynomialShiftOperator_mul_sub_one_sq R (admissibleLogWeibullProfile γ)) n
  have hsumR :
      (∑ r ∈ Finset.range (R.natDegree + 1),
        (R.coeff r : ℝ) * rapidCurvature (admissibleLogWeibullProfile γ) (n + r)) =
      polynomialShiftOperator R (rapidCurvature (admissibleLogWeibullProfile γ)) n := by
    rw [polynomialShiftOperator_apply]
  rw [hsumR, ← hfactor]
  change |logWeibullFiniteDifference γ d (n : ℝ)| / Real.log ((n : ℝ) + 2) =
    |polynomialShiftOperator Q (admissibleLogWeibullProfile γ) n| /
      Real.log ((n : ℝ) + 2)
  rw [hn]

/-- The rapid-convex curvature criterion is insensitive to every finite Taylor prefix. -/
theorem hypertranscendental_of_eventually_rapidConvex_curvatureShiftSeparated
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {b : ℕ → ℝ} (hbRapid : AdmissiblyRapidConvex b)
    (hsep : LogarithmicallyShiftSeparated (rapidCurvature b))
    (hb : ∀ᶠ i : ℕ in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (-b i)) :
    Hypertranscendental f := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hb
  let F := taylorPS f
  let p := finiteTaylorCorrectionToMagnitude F T b
  let g : ℂ → ℂ := fun z => f z + p.eval z
  have hp : ContDiff ℂ (⊤ : ℕ∞) (fun z : ℂ => p.eval z) :=
    contDiff_polynomial_eval p
  have hgsm : ContDiff ℂ (⊤ : ℕ∞) g := hf.add hp
  have htaylor : taylorPS g = F + (p : PowerSeries ℂ) := by
    change taylorPS (fun z => f z + p.eval z) = _
    rw [show (fun z => f z + p.eval z) = f + (fun z => p.eval z) from rfl,
      taylorPS_add hf hp, taylorPS_polynomial_eval]
  have hb' : ∀ i, ‖PowerSeries.coeff i (taylorPS g)‖ = Real.exp (-b i) := by
    intro i
    rw [htaylor, map_add, Polynomial.coeff_coe,
      coeff_finiteTaylorCorrectionToMagnitude]
    by_cases hi : i < T
    · simp only [if_pos hi]
      rw [show PowerSeries.coeff i F +
          ((Real.exp (-b i) : ℂ) - PowerSeries.coeff i F) =
          (Real.exp (-b i) : ℂ) by ring]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    · simp only [if_neg hi, add_zero]
      exact hT i (Nat.le_of_not_gt hi)
  have hg := hypertranscendental_of_rapidConvex_curvatureShiftSeparated
    hgsm hbRapid hb' hsep
  exact (hypertranscendental_add_polynomial_iff hf p).mp hg

/-- Every entire realization with eventual log-Weibull Taylor magnitudes is hypertranscendental. -/
theorem hypertranscendental_of_eventually_logWeibullMagnitude
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {γ : ℝ} (hγ : 1 < γ)
    (hb : ∀ᶠ i : ℕ in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (-logWeibull γ i)) :
    Hypertranscendental f := by
  apply hypertranscendental_of_eventually_rapidConvex_curvatureShiftSeparated hf
    (admissiblyRapidConvex_admissibleLogWeibullProfile hγ)
    (logarithmicallyShiftSeparated_rapidCurvature_admissibleLogWeibullProfile hγ)
  filter_upwards [hb, eventually_ge_atTop 1] with i hi hione
  simpa [admissibleLogWeibullProfile_eq (show 0 < i by omega)] using hi

/-- Paper-form log-magnitude criterion, including eventual full support. -/
theorem hypertranscendental_of_eventually_logWeibull_logMagnitude
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {γ : ℝ} (hγ : 1 < γ)
    (hne : ∀ᶠ i : ℕ in atTop, PowerSeries.coeff i (taylorPS f) ≠ 0)
    (hlog : ∀ᶠ i : ℕ in atTop,
      -Real.log ‖PowerSeries.coeff i (taylorPS f)‖ = logWeibull γ i) :
    Hypertranscendental f := by
  apply hypertranscendental_of_eventually_logWeibullMagnitude hf hγ
  filter_upwards [hne, hlog] with i hi hlogi
  have hnorm : 0 < ‖PowerSeries.coeff i (taylorPS f)‖ := norm_pos_iff.mpr hi
  rw [← Real.exp_log hnorm]
  congr 1
  linarith

theorem tendsto_logWeibull_firstFiniteDifference_atTop
    {γ : ℝ} (hγ : 1 < γ) :
    Tendsto (fun n : ℕ =>
      logWeibullFiniteDifference γ logWeibullFirstStencil n) atTop atTop := by
  have hcancel : ∀ k < 1, stretchedMoment logWeibullFirstStencil k = 0 := by
    intro k hk
    interval_cases k
    exact logWeibullFirstStencil_moments.1
  have hpos := eventually_pos_logWeibullFiniteDifference hγ logWeibullFirstStencil 1
    hcancel (by rw [logWeibullFirstStencil_moments.2]; norm_num)
  have htopDiv := tendsto_abs_div_log_add_two_atTop_of_log_isLittleO
    (hpos.mono fun _ hx => hx.ne')
    (log_isLittleO_abs_logWeibullFiniteDifference hγ logWeibullFirstStencil 1
      hcancel (by rw [logWeibullFirstStencil_moments.2]; norm_num))
  have htopReal : Tendsto
      (logWeibullFiniteDifference γ logWeibullFirstStencil) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ htopDiv
    filter_upwards [hpos, eventually_ge_atTop (Real.exp 1)] with x hx hxe
    have hlog : 1 ≤ Real.log (x + 2) := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1)
        (by linarith)
    rw [abs_of_pos hx]
    exact div_le_self hx.le hlog
  exact htopReal.comp tendsto_natCast_atTop_atTop

/-- Log-Weibull Taylor coefficient with arbitrary unit phase. -/
def logWeibullPhaseCoeff (γ : ℝ) (θ : ℕ → ℝ) (n : ℕ) : ℂ :=
  (Real.exp (-logWeibull γ n) : ℂ) *
    Complex.exp (Complex.I * (θ n : ℂ))

theorem norm_logWeibullPhaseCoeff (γ : ℝ) (θ : ℕ → ℝ) (n : ℕ) :
    ‖logWeibullPhaseCoeff γ θ n‖ = Real.exp (-logWeibull γ n) := by
  simp [logWeibullPhaseCoeff, Complex.norm_exp]

theorem logWeibullPhaseCoeff_ne_zero (γ : ℝ) (θ : ℕ → ℝ) (n : ℕ) :
    logWeibullPhaseCoeff γ θ n ≠ 0 := by
  simp [logWeibullPhaseCoeff, Complex.exp_ne_zero]

theorem logWeibullPhaseCoeff_ratio_tendsto
    {γ : ℝ} (hγ : 1 < γ) (θ : ℕ → ℝ) :
    Tendsto (fun n => ‖logWeibullPhaseCoeff γ θ n.succ‖ /
      ‖logWeibullPhaseCoeff γ θ n‖) atTop (𝓝 0) := by
  have hinc := tendsto_logWeibull_firstFiniteDifference_atTop hγ
  have harg : Tendsto (fun n : ℕ =>
      -logWeibullFiniteDifference γ logWeibullFirstStencil (n : ℝ)) atTop atBot :=
    Filter.tendsto_neg_atTop_atBot.comp hinc
  have hexp := Real.tendsto_exp_atBot.comp harg
  simpa only [Function.comp_apply] using hexp.congr' (by
    filter_upwards with n
    simp only [Function.comp_apply]
    rw [norm_logWeibullPhaseCoeff, norm_logWeibullPhaseCoeff, ← Real.exp_sub,
      logWeibullFiniteDifference_first]
    congr 1
    push_cast
    ring)

/-- Entire log-Weibull series with arbitrary Taylor phases. -/
def logWeibullPhaseFunction (γ : ℝ) (θ : ℕ → ℝ) : ℂ → ℂ :=
  FormalMultilinearSeries.ofScalarsSum (logWeibullPhaseCoeff γ θ)

theorem logWeibullPhaseFunction_eq_tsum
    (γ : ℝ) (θ : ℕ → ℝ) (z : ℂ) :
    logWeibullPhaseFunction γ θ z =
      ∑' n, logWeibullPhaseCoeff γ θ n * z ^ n := by
  simpa [logWeibullPhaseFunction, smul_eq_mul] using
    (FormalMultilinearSeries.ofScalars_sum_eq (logWeibullPhaseCoeff γ θ) z)

theorem logWeibullPhaseSeries_radius_eq_top
    {γ : ℝ} (hγ : 1 < γ) (θ : ℕ → ℝ) :
    (FormalMultilinearSeries.ofScalars ℂ (logWeibullPhaseCoeff γ θ)).radius = ⊤ := by
  exact FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto ℂ
    (logWeibullPhaseCoeff γ θ)
    (Eventually.of_forall (logWeibullPhaseCoeff_ne_zero γ θ))
    (logWeibullPhaseCoeff_ratio_tendsto hγ θ)

theorem contDiff_logWeibullPhaseFunction
    {γ : ℝ} (hγ : 1 < γ) (θ : ℕ → ℝ) :
    ContDiff ℂ (⊤ : ℕ∞) (logWeibullPhaseFunction γ θ) := by
  let p := FormalMultilinearSeries.ofScalars ℂ (logWeibullPhaseCoeff γ θ)
  have hr : p.radius = ⊤ := logWeibullPhaseSeries_radius_eq_top hγ θ
  have hp : HasFPowerSeriesOnBall p.sum p 0 p.radius :=
    p.hasFPowerSeriesOnBall (by rw [hr]; simp)
  have ha : AnalyticOnNhd ℂ p.sum Set.univ := by
    simpa [hr] using hp.analyticOnNhd
  exact ha.contDiff

theorem taylorPS_logWeibullPhaseFunction
    {γ : ℝ} (hγ : 1 < γ) (θ : ℕ → ℝ) (n : ℕ) :
    PowerSeries.coeff n (taylorPS (logWeibullPhaseFunction γ θ)) =
      logWeibullPhaseCoeff γ θ n := by
  exact taylorPS_ofScalarsSum_of_radius_eq_top (logWeibullPhaseCoeff γ θ)
    (logWeibullPhaseSeries_radius_eq_top hγ θ) n

/-- Every arbitrary-phase log-Weibull entire function is hypertranscendental. -/
theorem hypertranscendental_logWeibullPhaseFunction
    {γ : ℝ} (hγ : 1 < γ) (θ : ℕ → ℝ) :
    Hypertranscendental (logWeibullPhaseFunction γ θ) := by
  apply hypertranscendental_of_eventually_logWeibullMagnitude
    (contDiff_logWeibullPhaseFunction hγ θ) hγ
  exact Eventually.of_forall fun n => by
    rw [taylorPS_logWeibullPhaseFunction hγ, norm_logWeibullPhaseCoeff]

end

end GaloisForLFunctions
