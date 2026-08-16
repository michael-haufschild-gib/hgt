import GaloisForLFunctions.RHTower.XiMassTypeZeroCore

/-!
# Type zero of the moving quadrature defect

The continuum prefix of the moving quadrature defect is uniformly bounded up to the caustic and
its exterior piece obeys the same Bessel action estimate as the prime tail.  Hence the continuum
prefix has type zero at every asymptotically caustic boundary, and the moving quadrature defect
has type zero exactly when the moving true-prime cone does — that is, exactly under the Riemann
hypothesis.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-! ## The continuum tail constant is antitone in the slope -/

theorem xiMassBesselExteriorConstant_antitone {a sigma kappa kappa' : ℝ} (ha : 0 < a)
    (hsigma : 0 < sigma) (hkappa : 1 < kappa) (hkk : kappa ≤ kappa') :
    xiMassBesselExteriorConstant a sigma kappa'
      ≤ xiMassBesselExteriorConstant a sigma kappa := by
  have hkappa' : 1 < kappa' := lt_of_lt_of_le hkappa hkk
  have hk1 : (0 : ℝ) < kappa - 1 := by linarith
  have hk1' : (0 : ℝ) < kappa' - 1 := by linarith
  have hratio : (kappa' + 1) / (kappa' - 1) ≤ (kappa + 1) / (kappa - 1) := by
    rw [div_le_div_iff₀ hk1' hk1]
    nlinarith
  have hK : 0 ≤ GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * sigma) 1 :=
    (GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder_pos (mul_pos ha hsigma) 1).le
  rw [xiMassBesselExteriorConstant, xiMassBesselExteriorConstant]
  have hstep : 2 * a * ((kappa' + 1) / (kappa' - 1)) * Real.exp (a * sigma)
      ≤ 2 * a * ((kappa + 1) / (kappa - 1)) * Real.exp (a * sigma) := by
    have := mul_le_mul_of_nonneg_left hratio (by positivity : (0 : ℝ) ≤ 2 * a)
    exact mul_le_mul_of_nonneg_right this (Real.exp_nonneg _)
  exact mul_le_mul_of_nonneg_right hstep hK

theorem xiMassBesselContinuumTailConstant_antitone {a sigma kappa kappa' : ℝ} (ha : 1 / 2 < a)
    (hsigma : 0 < sigma) (hkappa : 1 < kappa) (hkk : kappa ≤ kappa') :
    xiMassBesselContinuumTailConstant a sigma kappa'
      ≤ xiMassBesselContinuumTailConstant a sigma kappa := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hδ : (0 : ℝ) < a - 1 / 2 := by linarith
  rw [xiMassBesselContinuumTailConstant, xiMassBesselContinuumTailConstant]
  exact div_le_div_of_nonneg_right
    (xiMassBesselExteriorConstant_antitone ha0 hsigma hkappa hkk) hδ.le

/-- **The continuum tail at a moving slope.** -/
theorem norm_integral_growingFourierProfile_movingSlope_le {a sigma kappa0 u c e : ℝ}
    (ha : 1 / 2 < a) (hsigma : 0 < sigma) (hkappa0 : 1 < kappa0) (hu : 0 < u)
    (hcone : kappa0 * u ≤ c) (hce : c ≤ e) :
    ‖∫ h in c..e, xiMassCriticalGrowingFourierProfile a sigma u h‖
      ≤ xiMassBesselContinuumTailConstant a sigma kappa0
        * Real.exp (c / 2 - a * Real.sqrt (c ^ 2 - u ^ 2)) := by
  have hkappa00 : (0 : ℝ) < kappa0 := lt_trans zero_lt_one hkappa0
  have hcpos : (0 : ℝ) < c := lt_of_lt_of_le (by positivity) hcone
  have hslope : kappa0 ≤ c / u := (le_div_iff₀ hu).2 hcone
  have hone : 1 < c / u := lt_of_lt_of_le hkappa0 hslope
  have hmul : c / u * u = c := div_mul_cancel₀ c hu.ne'
  have hbase := norm_integral_growingFourierProfile_exterior_le (a := a) (sigma := sigma)
    (kappa := c / u) (u := u) (c := c) (e := e) ha hsigma hone hu.le hcpos (by rw [hmul]) hce
  refine hbase.trans ?_
  have hexp : Real.exp (-(xiMassBesselConeExponent a (c / u) * u))
      = Real.exp (c / 2 - a * Real.sqrt (c ^ 2 - u ^ 2)) := by
    have hact := xiMassAction_at_slope (a := a) (kappa := c / u) (u := u) hone hu.le
    rw [hmul] at hact
    rw [hact]
    congr 1
    ring
  rw [hexp]
  have hCC : xiMassBesselContinuumTailConstant a sigma (c / u)
      ≤ xiMassBesselContinuumTailConstant a sigma kappa0 :=
    xiMassBesselContinuumTailConstant_antitone ha hsigma hkappa0 hslope
  exact mul_le_mul_of_nonneg_right hCC (Real.exp_nonneg _)

/-! ## The moving cone edge -/

theorem tendsto_coneEdge_ratio {f : ℝ → ℝ} {L : ℝ}
    (hf : Tendsto (fun u => f u / u) atTop (nhds L))
    (hf0 : ∀ᶠ u : ℝ in atTop, 0 ≤ f u) :
    Tendsto (fun u => Real.log ((⌊Real.exp (f u)⌋₊ : ℝ) + 1) / u) atTop (nhds L) := by
  have hinvz : Tendsto (fun u : ℝ => u⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have hupper : Tendsto (fun u : ℝ => f u / u + u⁻¹) atTop (nhds L) := by
    have hstep := hf.add hinvz
    simpa using hstep
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hf hupper ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    exact div_le_div_of_nonneg_right (le_log_floor_exp_add_one (f u)) hu.le
  · filter_upwards [hf0, eventually_gt_atTop (0 : ℝ)] with u h0 hu
    have hle := log_floor_exp_add_one_le h0
    have hstep : Real.log ((⌊Real.exp (f u)⌋₊ : ℝ) + 1) / u ≤ (f u + 1) / u :=
      div_le_div_of_nonneg_right hle hu.le
    refine hstep.trans (le_of_eq ?_)
    field_simp

/-! ## Type zero of the continuum prefix -/

set_option maxHeartbeats 800000 in
/-- **The continuum prefix at an asymptotically caustic boundary has type zero.** -/
theorem xiMassTypeZero_continuumPrefix {a c sigma : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma) {Hgt : ℝ → ℝ}
    (hratio : Tendsto (fun u : ℝ => Hgt u / u) atTop (nhds (xiMassSpacelikeSharpSlope a)))
    (hH0 : ∀ᶠ u : ℝ in atTop, 0 ≤ Hgt u) :
    XiMassTypeZero (fun u => ∫ h in (0 : ℝ)..Real.log ((⌊Real.exp (Hgt u)⌋₊ : ℝ) + 1),
      xiMassCriticalGrowingFourierProfile a sigma u h) := by
  have ha : 1 / 2 < a := lt_trans hhalf hca
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hkB : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
  have hkB0 : (0 : ℝ) < xiMassSpacelikeSharpSlope a := lt_trans zero_lt_one hkB
  have hzeroB := xiMassBesselConeExponent_sharpSlope_eq_zero ha
  obtain ⟨k0, hk0def⟩ : ∃ k0 : ℝ, (1 + xiMassSpacelikeSharpSlope a) / 2 = k0 := ⟨_, rfl⟩
  have hk0one : 1 < k0 := by rw [← hk0def]; linarith
  have hk0lt : k0 < xiMassSpacelikeSharpSlope a := by rw [← hk0def]; linarith
  have hCC : 0 ≤ xiMassBesselContinuumTailConstant a sigma k0 := by
    rw [xiMassBesselContinuumTailConstant]
    have h1 : 0 ≤ xiMassBesselExteriorConstant a sigma k0 :=
      xiMassBesselExteriorConstant_nonneg ha0 hsigma hk0one
    have h2 : (0 : ℝ) < a - 1 / 2 := by linarith
    positivity
  obtain ⟨B, hB⟩ := exists_norm_integral_growingFourierProfile_at_besselCone_le
    (a := a) (sigma := sigma) (kappa := xiMassSpacelikeSharpSlope a) ha hsigma hkB le_rfl
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 le_rfl)
  have hedgeB : ∀ u : ℝ,
      xiMassCriticalConeEdge (xiMassConeDepthOfSlope (xiMassSpacelikeSharpSlope a)) u
        = Real.log ((⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊ : ℝ) + 1) := by
    intro u
    rw [xiMassCriticalConeEdge, xiMassConeDepthOfSlope_height hkB]
  -- both edges have caustic ratio
  have hratioH : Tendsto (fun u : ℝ =>
      Real.log ((⌊Real.exp (Hgt u)⌋₊ : ℝ) + 1) / u) atTop
      (nhds (xiMassSpacelikeSharpSlope a)) := tendsto_coneEdge_ratio hratio hH0
  have hratioB : Tendsto (fun u : ℝ =>
      Real.log ((⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊ : ℝ) + 1) / u) atTop
      (nhds (xiMassSpacelikeSharpSlope a)) := by
    refine tendsto_coneEdge_ratio ?_ ?_
    · have hid : ∀ u : ℝ, 0 < u → xiMassSpacelikeSharpSlope a * u / u
          = xiMassSpacelikeSharpSlope a := by
        intro u hu
        field_simp
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      exact (hid u hu).symm
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
      positivity
  have hmin : Tendsto (fun u : ℝ =>
      min (Real.log ((⌊Real.exp (Hgt u)⌋₊ : ℝ) + 1) / u)
        (Real.log ((⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊ : ℝ) + 1) / u)) atTop
      (nhds (xiMassSpacelikeSharpSlope a)) := by
    have hstep := hratioH.min hratioB
    simpa using hstep
  have hact : Tendsto (fun u : ℝ => -(xiMassBesselConeExponent a
      (min (Real.log ((⌊Real.exp (Hgt u)⌋₊ : ℝ) + 1) / u)
        (Real.log ((⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊ : ℝ) + 1) / u)))) atTop
      (nhds 0) := by
    have hcont : Continuous (fun k : ℝ => -(xiMassBesselConeExponent a k)) :=
      (continuous_xiMassBesselConeExponent a).neg
    have hstep := (hcont.tendsto (xiMassSpacelikeSharpSlope a)).comp hmin
    rw [hzeroB, neg_zero] at hstep
    exact hstep
  have hevk0 : ∀ᶠ u : ℝ in atTop,
      k0 < min (Real.log ((⌊Real.exp (Hgt u)⌋₊ : ℝ) + 1) / u)
        (Real.log ((⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊ : ℝ) + 1) / u) :=
    hmin.eventually_const_lt hk0lt
  intro ε hε0
  have hevε : ∀ᶠ u : ℝ in atTop, -(xiMassBesselConeExponent a
      (min (Real.log ((⌊Real.exp (Hgt u)⌋₊ : ℝ) + 1) / u)
        (Real.log ((⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊ : ℝ) + 1) / u))) ≤ ε :=
    hact.eventually_le_const hε0
  refine ⟨B + xiMassBesselContinuumTailConstant a sigma k0, ?_⟩
  filter_upwards [hevk0, hevε, eventually_ge_atTop (1 : ℝ)] with u hu1 hu2 hu3
  have hupos : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu3
  have hcont := continuous_xiMassCriticalGrowingFourierProfile ha0 hsigma u
  obtain ⟨WH, hWH⟩ : ∃ W : ℝ, Real.log ((⌊Real.exp (Hgt u)⌋₊ : ℝ) + 1) = W := ⟨_, rfl⟩
  obtain ⟨WB, hWB⟩ : ∃ W : ℝ,
      Real.log ((⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊ : ℝ) + 1) = W := ⟨_, rfl⟩
  obtain ⟨kk, hkk⟩ : ∃ k : ℝ, min (WH / u) (WB / u) = k := ⟨_, rfl⟩
  rw [hWH, hWB] at hu1 hu2
  rw [hkk] at hu1 hu2
  have hkkmul : kk * u = min WH WB := by
    rw [← hkk, min_mul_of_nonneg _ _ hupos.le, div_mul_cancel₀ _ (ne_of_gt hupos),
      div_mul_cancel₀ _ (ne_of_gt hupos)]
  have hk0le : k0 * u ≤ kk * u := by nlinarith [hu1, hupos]
  have hkone : 1 < kk := lt_trans hk0one hu1
  have hsplit : (∫ h in (0 : ℝ)..WB, xiMassCriticalGrowingFourierProfile a sigma u h)
      + ∫ h in WB..WH, xiMassCriticalGrowingFourierProfile a sigma u h
      = ∫ h in (0 : ℝ)..WH, xiMassCriticalGrowingFourierProfile a sigma u h :=
    intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)
  have hmid : ‖∫ h in WB..WH, xiMassCriticalGrowingFourierProfile a sigma u h‖
      ≤ xiMassBesselContinuumTailConstant a sigma k0
        * Real.exp (-(xiMassBesselConeExponent a kk) * u) := by
    rcases le_total WB WH with hle | hle
    · have hWBval : WB = kk * u := by rw [hkkmul, min_eq_right hle]
      have hcone' : k0 * u ≤ WB := by rw [hWBval]; exact hk0le
      have hbd := norm_integral_growingFourierProfile_movingSlope_le (a := a) (sigma := sigma)
        (kappa0 := k0) (u := u) (c := WB) (e := WH) ha hsigma hk0one hupos hcone' hle
      have hexpeq : Real.exp (WB / 2 - a * Real.sqrt (WB ^ 2 - u ^ 2))
          = Real.exp (-(xiMassBesselConeExponent a kk) * u) := by
        rw [hWBval, xiMassAction_at_slope hkone hupos.le]
      rw [hexpeq] at hbd
      exact hbd
    · have hWHval : WH = kk * u := by rw [hkkmul, min_eq_left hle]
      have hcone' : k0 * u ≤ WH := by rw [hWHval]; exact hk0le
      have hbd := norm_integral_growingFourierProfile_movingSlope_le (a := a) (sigma := sigma)
        (kappa0 := k0) (u := u) (c := WH) (e := WB) ha hsigma hk0one hupos hcone' hle
      have hexpeq : Real.exp (WH / 2 - a * Real.sqrt (WH ^ 2 - u ^ 2))
          = Real.exp (-(xiMassBesselConeExponent a kk) * u) := by
        rw [hWHval, xiMassAction_at_slope hkone hupos.le]
      rw [hexpeq] at hbd
      have hsym : (∫ h in WB..WH, xiMassCriticalGrowingFourierProfile a sigma u h)
          = -∫ h in WH..WB, xiMassCriticalGrowingFourierProfile a sigma u h :=
        intervalIntegral.integral_symm _ _
      rw [hsym, norm_neg]
      exact hbd
  have hbaseB : ‖∫ h in (0 : ℝ)..WB, xiMassCriticalGrowingFourierProfile a sigma u h‖ ≤ B := by
    have := hB u hupos.le
    rw [hedgeB u, hWB] at this
    exact this
  have hexpmono : Real.exp (-(xiMassBesselConeExponent a kk) * u) ≤ Real.exp (ε * u) := by
    refine Real.exp_le_exp.2 ?_
    nlinarith [hu2, hupos]
  have hexp1 : (1 : ℝ) ≤ Real.exp (ε * u) := Real.one_le_exp (by positivity)
  rw [hWH, ← hsplit]
  refine (norm_add_le _ _).trans ?_
  nlinarith [hbaseB, hmid, hexpmono, hexp1, hB0, hCC]

/-! ## The moving quadrature-defect criterion -/

/-- **(23.6) The type-zero quadrature-defect criterion.**  For every moving height whose slope
tends to the balance slope, the prime--continuum quadrature defect below it has vertical type zero
exactly under the Riemann hypothesis. -/
theorem riemannHypothesis_iff_typeZero_movingQuadratureDefect {a c sigma : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma) {Hgt : ℝ → ℝ}
    (hratio : Tendsto (fun u : ℝ => Hgt u / u) atTop (nhds (xiMassSpacelikeSharpSlope a))) :
    RiemannHypothesis ↔ XiMassTypeZero
      (fun u => xiMassPrefixQuadratureDefect a sigma u ⌊Real.exp (Hgt u)⌋₊) := by
  have ha : 1 / 2 < a := lt_trans hhalf hca
  have hkB : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
  have hkB0 : (0 : ℝ) < xiMassSpacelikeSharpSlope a := lt_trans zero_lt_one hkB
  have hH0 : ∀ᶠ u : ℝ in atTop, 0 ≤ Hgt u := by
    have h1 : ∀ᶠ u : ℝ in atTop, 0 < Hgt u / u := hratio.eventually_const_lt hkB0
    filter_upwards [h1, eventually_gt_atTop (0 : ℝ)] with u hu hupos
    rw [lt_div_iff₀ hupos] at hu
    linarith
  have hcont := xiMassTypeZero_continuumPrefix hhalf hca hsigma hratio hH0
  have hdef : ∀ u : ℝ, xiMassPrefixQuadratureDefect a sigma u ⌊Real.exp (Hgt u)⌋₊
      = xiMassMovingPrimeCone a sigma Hgt u
        - ∫ h in (0 : ℝ)..Real.log ((⌊Real.exp (Hgt u)⌋₊ : ℝ) + 1),
            xiMassCriticalGrowingFourierProfile a sigma u h := by
    intro u
    rw [xiMassPrefixQuadratureDefect, xiMassMovingPrimeCone]
  rw [riemannHypothesis_iff_typeZero_movingPrimeCone hhalf hca hsigma hratio]
  constructor
  · intro hP
    exact (hP.sub hcont).congr fun u => (hdef u).symm
  · intro hQ
    refine (hQ.add hcont).congr fun u => ?_
    rw [hdef u]
    ring

end

end RHTower
