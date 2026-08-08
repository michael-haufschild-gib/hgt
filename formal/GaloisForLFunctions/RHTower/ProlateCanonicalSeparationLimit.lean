import GaloisForLFunctions.RHTower.ProlateAllowedEnergy
import GaloisForLFunctions.RHTower.ProlateCanonicalBandMass
import GaloisForLFunctions.RHTower.ProlateCanonicalSeparationTunneling
import GaloisForLFunctions.RHTower.ProlateTurningLayer
import GaloisForLFunctions.RHTower.ConstrainedProlateSignedTrial

/-!
# Unconditional small-separation limit for canonical signed prolate modes

Kaiser trial spaces give every fixed signed-greedy leakage the optimal Gaussian clock.  The radial
ODE gives a strictly slower clock whenever its separation ratio stays positive.  Below the radial
turning threshold this is the clock-preserving tunneling estimate; above it, Sonin energy bounds
the aperture mass while the endpoint collar supplies a polynomial exterior-mass floor.  The two
branches exhaust all nonnegative separation values and force the canonical ratio to zero.
-/

noncomputable section

open Filter MeasureTheory Set

namespace RHTower

open GaloisForLFunctions.RHTower

/-- Every positive separation threshold forces a strict Gaussian-clock leakage lower bound for
the actual canonical signed mode. -/
theorem eventually_signedModeRadial_tunneling_lower
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ a : ℝ in atTop,
      ε ≤ (signedModeRadialData a n).s →
        Real.exp (-((4 * Real.pi - δ) * a ^ 2)) ≤
          evenProlateSignedLeakage a n := by
  let e : ℝ := min ε 1
  have he0 : 0 < e := lt_min hε (by norm_num)
  have he1 : e ≤ 1 := min_le_right _ _
  have heε : e ≤ ε := min_le_left _ _
  let δ : ℝ := 2 * Real.pi * e
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  have hcTop : Tendsto signedModeRadialBandwidth atTop atTop :=
    tendsto_signedModeRadialBandwidth_atTop
  have hceTop : Tendsto (fun a => signedModeRadialBandwidth a * e) atTop atTop :=
    hcTop.atTop_mul_const he0
  have hvalue : ∀ᶠ a : ℝ in atTop,
      1 / 2 ≤ evenProlateSignedValue a n ^ 2 :=
    (evenProlateSignedValue_sq_tendsto_one n).eventually
      (eventually_ge_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hclockLow := eventually_exp_clock_gain_le_radial_polynomial_lower he0
  have hclockHigh := eventually_exp_clock_gain_le_one_div_radial_sq he0 he1
  filter_upwards [eventually_signedModeRadialData_isExact n,
    eventually_evenProlateSignedValue_ne_zero n, eventually_gt_atTop (0 : ℝ),
    hcTop.eventually_ge_atTop 5, hceTop.eventually_ge_atTop 4,
    hvalue, hclockLow, hclockHigh] with
      a hD hvalue0 ha hc5 hce hvalueSq hclockL hclockH
  intro hεs
  let D := signedModeRadialData a n
  let c := signedModeRadialBandwidth a
  have hc : 0 < c := by
    dsimp only [c, signedModeRadialBandwidth]
    positivity
  have hes : e ≤ D.s := heε.trans hεs
  rcases hD with ⟨_hPhi, _hPhi0, _hPhiEven, _hPhi1, _hRdef, hRsm, hReven,
    hR1, _hband, _hprolate, _hs, hs0, hend, hode⟩
  have hR : ∀ t : ℝ, HasDerivAt D.R (deriv D.R t) t := by
    intro t
    exact ((contDiff_infty_iff_deriv.mp hRsm).1 t).hasDerivAt
  have hDR : ∀ t : ℝ, HasDerivAt (deriv D.R) (deriv (deriv D.R) t) t := by
    intro t
    exact ((contDiff_infty_iff_deriv.mp
      (contDiff_infty_iff_deriv.mp hRsm).2).1 t).hasDerivAt
  have heig : ∀ y ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c D.R y = -(D.s * c ^ 2) * D.R y := by
    intro y _hy
    have hy := hode y
    simp only [prolateSLAction]
    nlinarith
  have hint : IntegrableOn (fun x : ℝ => D.R x ^ 2) (Icc (-1 : ℝ) 1)ᶜ := by
    exact (integrable_sq_signedModeRadialData ha n hvalue0).integrableOn
  have hmass := integral_outside_sq_signedModeRadialData_eq_leakage_ratio
    ha n hvalue0
  have hleak : 0 ≤ evenProlateSignedLeakage a n :=
    evenProlateSignedLeakage_nonneg a n
  by_cases hhigh : 1 ≤ D.s
  · have hinside := integral_sq_le_two_of_one_le
      hc hhigh hRsm hReven heig hR1 hend
    have hout := one_div_eight_c_sq_le_integral_outside_sq_radialProlate_of_one_le
      hhigh (by simpa only [c] using hc5) hR1 hR hDR hode hint
    have hlower := leakage_lower_of_high_separation_mass_bounds
      hc hout hvalueSq hleak hinside hmass
    have hclockH' :
        Real.exp (-((4 * Real.pi - δ) * a ^ 2)) ≤ 1 / (32 * c ^ 2) := by
      simpa only [δ, e, c, signedModeRadialBandwidth] using hclockH
    exact hclockH'.trans hlower
  · have hs1 : D.s < 1 := lt_of_not_ge hhigh
    have hspos : 0 < D.s := he0.trans_le hes
    have hcs : 4 ≤ c * D.s := by
      have hmul := mul_le_mul_of_nonneg_left hes hc.le
      have hce' : 4 ≤ c * e := by simpa only [c] using hce
      exact hce'.trans hmul
    have hsqrtGe : D.s ≤ Real.sqrt D.s := by
      rw [Real.le_sqrt hs0 hs0]
      nlinarith [hs1.le]
    have hscale : 1 ≤ c * Real.sqrt D.s := by
      have hmul := mul_le_mul_of_nonneg_left hsqrtGe hc.le
      linarith
    have hinside := integral_sq_le_exp_twice_turning_action
      hc hspos hs1 hcs hscale hRsm heig hR1 hReven
    have hout := one_div_thirty_two_c_sq_le_integral_outside_sq_radialProlate
      hs0 hs1.le (by simpa only [c] using hc5) hR1 hR hDR hode hint
    have hlower := leakage_lower_of_radial_mass_bounds
      hc hspos hout hvalueSq hleak hinside hmass
    have hsqrt : Real.sqrt e ≤ Real.sqrt D.s := Real.sqrt_le_sqrt hes
    have hden : 0 < 256 * Real.exp 1 * c ^ 3 := by positivity
    have hcoef :
        Real.sqrt e / (256 * Real.exp 1 * c ^ 3) ≤
          Real.sqrt D.s / (256 * Real.exp 1 * c ^ 3) :=
      (div_le_div_iff_of_pos_right hden).2 hsqrt
    have hexp :
        Real.exp (-(2 * c * (1 - e))) ≤
          Real.exp (-(2 * c * (1 - D.s))) := by
      rw [Real.exp_le_exp]
      nlinarith
    have hpoly :
        (Real.sqrt e / (256 * Real.exp 1 * c ^ 3)) *
            Real.exp (-(2 * c * (1 - e))) ≤
          (Real.sqrt D.s / (256 * Real.exp 1 * c ^ 3)) *
            Real.exp (-(2 * c * (1 - D.s))) :=
      mul_le_mul hcoef hexp (Real.exp_pos _).le (by positivity)
    have hclockL' :
        Real.exp (-((4 * Real.pi - δ) * a ^ 2)) ≤
          (Real.sqrt e / (256 * Real.exp 1 * c ^ 3)) *
            Real.exp (-(2 * c * (1 - e))) := by
      simpa only [δ, e, c, signedModeRadialBandwidth] using hclockL
    exact hclockL'.trans (hpoly.trans hlower)

/-- **Unconditional fixed-index radial separation limit.** -/
theorem tendsto_signedModeRadialData_s_zero (n : ℕ) :
    Tendsto (fun a : ℝ => (signedModeRadialData a n).s) atTop (nhds 0) := by
  apply tendsto_signedModeRadialData_s_zero_of_tunneling_lower n
  intro ε hε
  exact eventually_signedModeRadial_tunneling_lower n ε hε

/-- Unconditional canonical fixed-mode radial tail law. -/
theorem tendsto_integral_Ioi_signedModeRadialDensity_unconditional
    (n : ℕ) {b : ℝ} (hb : 1 < b) :
    Tendsto (fun a : ℝ => ∫ x in Ioi b,
      GaloisForLFunctions.RHTower.radialProlateDensity
        (signedModeRadialBandwidth a) (signedModeRadialData a n).R x)
      atTop
      (nhds ((∫ x in Ioi b, _root_.RHTower.radialLeakageDensity x) / Real.pi)) :=
  tendsto_integral_Ioi_signedModeRadialDensity n
    (tendsto_signedModeRadialData_s_zero n) hb

/-- Unconditional fixed off-diagonal vanishing for canonical signed radial modes. -/
theorem tendsto_integral_Ioi_signedModeFirstRowRadialProduct_unconditional
    (n : ℕ) {k : ℝ} (hk : 2 ≤ k) :
    Tendsto (fun a : ℝ => ∫ x in Ioi (1 : ℝ),
      GaloisForLFunctions.RHTower.firstRowRadialProduct (signedModeRadialBandwidth a)
        (signedModeRadialData a n).R k x) atTop (nhds 0) :=
  tendsto_integral_Ioi_signedModeFirstRowRadialProduct n
    (tendsto_signedModeRadialData_s_zero n) hk

/-- The canonical first-row cancellation persists after discarding any fixed initial exterior
segment.  This tail form is what dilation covariance needs for Gram entries whose first index is
larger than one. -/
theorem tendsto_integral_Ioi_signedModeFirstRowRadialProduct_from
    (n : ℕ) {k b : ℝ} (hk : 2 ≤ k) (hb : 2 ≤ b) :
    Tendsto (fun a : ℝ => ∫ x in Ioi b,
      GaloisForLFunctions.RHTower.firstRowRadialProduct (signedModeRadialBandwidth a)
        (signedModeRadialData a n).R k x) atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hTailTendsto : Tendsto (fun B : ℝ =>
      4 * GaloisForLFunctions.RHTower.radialProlateDensityEnvelopeConstant *
        ∫ x in Ioi B, GaloisForLFunctions.RHTower.profileDensity x) atTop (nhds 0) := by
    simpa using
      GaloisForLFunctions.RHTower.tendsto_integral_Ioi_profileDensity_atTop_zero.const_mul
        (4 * GaloisForLFunctions.RHTower.radialProlateDensityEnvelopeConstant)
  have hTailSmall : ∀ᶠ B : ℝ in atTop,
      4 * GaloisForLFunctions.RHTower.radialProlateDensityEnvelopeConstant *
        ∫ x in Ioi B, GaloisForLFunctions.RHTower.profileDensity x < ε / 2 :=
    hTailTendsto.eventually (eventually_lt_nhds (by positivity : 0 < ε / 2))
  have hCutLarge : ∀ᶠ B : ℝ in atTop,
      max b (Real.sqrt (1 + 2 / k ^ 2)) ≤ B :=
    eventually_ge_atTop (max b (Real.sqrt (1 + 2 / k ^ 2)))
  obtain ⟨B, hTailB, hCutB⟩ := (hTailSmall.and hCutLarge).exists
  have hbB : b ≤ B := (le_max_left _ _).trans hCutB
  have hb1 : 1 < b := lt_of_lt_of_le (by norm_num) hb
  have hk0 : 0 < k := lt_of_lt_of_le (by norm_num) hk
  have hkSq : 4 ≤ k ^ 2 := by nlinarith
  have hdiv : 2 / k ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ (sq_pos_of_pos hk0)]
    nlinarith
  have harg0 : 0 ≤ 1 + 2 / k ^ 2 := by positivity
  have hLowerStationary : Real.sqrt (1 + 2 / k ^ 2) ≤ b := by
    have hsqrtSq : Real.sqrt (1 + 2 / k ^ 2) ^ 2 = 1 + 2 / k ^ 2 :=
      Real.sq_sqrt harg0
    have hsqrt0 := Real.sqrt_nonneg (1 + 2 / k ^ 2)
    nlinarith
  let D : ℝ → SignedModeRadialData := fun a => signedModeRadialData a n
  let DR : ℝ → ℝ → ℝ := fun a => deriv (D a).R
  let DDR : ℝ → ℝ → ℝ := fun a => deriv (deriv (D a).R)
  have hcompact : Tendsto (fun a : ℝ => ∫ x in b..B,
      GaloisForLFunctions.RHTower.firstRowRadialProduct (signedModeRadialBandwidth a)
        (signedModeRadialData a n).R k x) atTop (nhds 0) := by
    exact GaloisForLFunctions.RHTower.tendsto_integral_firstRowRadialProduct
      (R := fun a => (D a).R) (DR := DR) (DDR := DDR)
      tendsto_signedModeRadialBandwidth_atTop
      (tendsto_signedModeRadialData_s_zero n)
      (eventually_signedModeRadialData_s_nonneg n)
      (by simpa [D] using eventually_signedModeRadialData_R_one n)
      (by simpa [D, DR] using eventually_signedModeRadialData_hasDerivAt n)
      (by simpa [D, DR, DDR] using eventually_signedModeRadialData_hasSecondDerivAt n)
      (by simpa [D, DR, DDR] using eventually_signedModeRadialData_ode n)
      hk hbB hb1 hLowerStationary
  have hcompactSmall : ∀ᶠ a : ℝ in atTop,
      |∫ x in b..B,
        GaloisForLFunctions.RHTower.firstRowRadialProduct (signedModeRadialBandwidth a)
          (signedModeRadialData a n).R k x| < ε / 2 := by
    simpa [Real.dist_eq] using
      (Metric.tendsto_nhds.mp hcompact) (ε / 2) (by positivity : 0 < ε / 2)
  have hsHalf : ∀ᶠ a : ℝ in atTop, (signedModeRadialData a n).s ≤ 1 / 2 :=
    (tendsto_signedModeRadialData_s_zero n).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)) |>.mono fun _ h => h.le
  have hc5 : ∀ᶠ a : ℝ in atTop, 5 ≤ signedModeRadialBandwidth a :=
    tendsto_signedModeRadialBandwidth_atTop.eventually (eventually_ge_atTop 5)
  have hcross := GaloisForLFunctions.RHTower.tendsto_dunsterEndpointCrossing_comp_atTop_one
    tendsto_signedModeRadialBandwidth_atTop
  have hcrossB : ∀ᶠ a : ℝ in atTop,
      GaloisForLFunctions.RHTower.dunsterEndpointCrossing (signedModeRadialBandwidth a) ≤ B :=
    (hcross.eventually (eventually_lt_nhds (hb1.trans_le hbB))).mono fun _ h => h.le
  filter_upwards [hcompactSmall, eventually_signedModeRadialData_s_nonneg n, hsHalf, hc5,
      hcrossB, eventually_signedModeRadialData_R_one n,
      eventually_signedModeRadialData_hasDerivAt n,
      eventually_signedModeRadialData_hasSecondDerivAt n,
      eventually_signedModeRadialData_ode n] with
      a hcompactA hs0 hs1 hc hcrossA hR1 hR hDR hode
  have htail := GaloisForLFunctions.RHTower.abs_integral_Ioi_firstRowRadialProduct_le
    hs0 hs1 hk hc (hb1.trans_le hbB) hcrossA hR1 hR hDR hode
  have hRc : Continuous (signedModeRadialData a n).R :=
    continuous_iff_continuousAt.mpr fun x => (hR x).continuousAt
  have hcont : Continuous
      (GaloisForLFunctions.RHTower.firstRowRadialProduct (signedModeRadialBandwidth a)
        (signedModeRadialData a n).R k) := by
    unfold GaloisForLFunctions.RHTower.firstRowRadialProduct
      GaloisForLFunctions.RHTower.radialProlateRescaledProfile
    fun_prop
  have hInt : IntervalIntegrable
      (GaloisForLFunctions.RHTower.firstRowRadialProduct (signedModeRadialBandwidth a)
        (signedModeRadialData a n).R k) volume b B :=
    hcont.intervalIntegrable b B
  have hIoc : IntegrableOn
      (GaloisForLFunctions.RHTower.firstRowRadialProduct (signedModeRadialBandwidth a)
        (signedModeRadialData a n).R k) (Ioc b B) := by
    rwa [← intervalIntegrable_iff_integrableOn_Ioc_of_le hbB]
  have hIoi := GaloisForLFunctions.RHTower.integrableOn_firstRowRadialProduct_Ioi
    hs0 hs1 hk hc (hb1.trans_le hbB) hcrossA hR1 hR hDR hode
  have hsplit : (∫ x in Ioi b,
      GaloisForLFunctions.RHTower.firstRowRadialProduct (signedModeRadialBandwidth a)
        (signedModeRadialData a n).R k x) =
      (∫ x in b..B,
        GaloisForLFunctions.RHTower.firstRowRadialProduct (signedModeRadialBandwidth a)
          (signedModeRadialData a n).R k x) +
        ∫ x in Ioi B,
          GaloisForLFunctions.RHTower.firstRowRadialProduct (signedModeRadialBandwidth a)
            (signedModeRadialData a n).R k x := by
    rw [intervalIntegral.integral_of_le hbB]
    rw [← Ioc_union_Ioi_eq_Ioi hbB]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hIoc hIoi
  rw [Real.dist_eq, sub_zero, hsplit]
  have hsum := add_lt_add hcompactA (htail.trans_lt hTailB)
  apply (abs_add_le _ _).trans_lt
  linarith

/-! ## Canonical radial dilation Gram entries -/

/-- Exterior dilation Gram entry of the endpoint-normalized canonical radial profile. -/
def signedModeRadialGramEntry (a : ℝ) (n : ℕ) (j k : ℝ) : ℝ :=
  ∫ x in Ioi (1 : ℝ),
    GaloisForLFunctions.RHTower.radialProlateRescaledProfile
        (signedModeRadialBandwidth a) (signedModeRadialData a n).R (j * x) *
      GaloisForLFunctions.RHTower.radialProlateRescaledProfile
        (signedModeRadialBandwidth a) (signedModeRadialData a n).R (k * x)

/-- Exact dilation covariance: scaling by a positive first index turns an arbitrary Gram entry
into a first-row product over the correspondingly shifted exterior tail. -/
theorem signedModeRadialGramEntry_scale_left
    (a : ℝ) (n : ℕ) {j : ℝ} (hj : 0 < j) (k : ℝ) :
    signedModeRadialGramEntry a n j k =
      j⁻¹ * ∫ x in Ioi j,
        GaloisForLFunctions.RHTower.firstRowRadialProduct
          (signedModeRadialBandwidth a) (signedModeRadialData a n).R (k / j) x := by
  let c := signedModeRadialBandwidth a
  let R := (signedModeRadialData a n).R
  have hpoint :
      (fun x : ℝ =>
        GaloisForLFunctions.RHTower.radialProlateRescaledProfile c R (j * x) *
          GaloisForLFunctions.RHTower.radialProlateRescaledProfile c R (k * x)) =
        fun x : ℝ =>
          GaloisForLFunctions.RHTower.firstRowRadialProduct c R (k / j) (j * x) := by
    funext x
    unfold GaloisForLFunctions.RHTower.firstRowRadialProduct
    congr 2
    field_simp [hj.ne']
  rw [signedModeRadialGramEntry]
  change (∫ x in Ioi (1 : ℝ),
    GaloisForLFunctions.RHTower.radialProlateRescaledProfile c R (j * x) *
      GaloisForLFunctions.RHTower.radialProlateRescaledProfile c R (k * x)) = _
  rw [hpoint, MeasureTheory.integral_comp_mul_left_Ioi _ 1 hj, mul_one]
  rfl

/-- Canonical radial Gram entries are symmetric before taking any limit. -/
theorem signedModeRadialGramEntry_comm
    (a : ℝ) (n : ℕ) (j k : ℝ) :
    signedModeRadialGramEntry a n j k = signedModeRadialGramEntry a n k j := by
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro x _hx
  ring

/-- A diagonal radial Gram entry is exactly the reciprocal-dilation multiple of one density
tail. -/
theorem signedModeRadialGramEntry_diag_eq
    (a : ℝ) (n : ℕ) {k : ℝ} (hk : 0 < k) :
    signedModeRadialGramEntry a n k k =
      k⁻¹ * ∫ x in Ioi k,
        GaloisForLFunctions.RHTower.radialProlateDensity
          (signedModeRadialBandwidth a) (signedModeRadialData a n).R x := by
  let c := signedModeRadialBandwidth a
  let R := (signedModeRadialData a n).R
  have hc : 0 ≤ c := by
    dsimp only [c, signedModeRadialBandwidth]
    positivity
  have hpoint :
      (fun x : ℝ =>
        GaloisForLFunctions.RHTower.radialProlateRescaledProfile c R (k * x) *
          GaloisForLFunctions.RHTower.radialProlateRescaledProfile c R (k * x)) =
        fun x : ℝ => GaloisForLFunctions.RHTower.radialProlateDensity c R (k * x) := by
    funext x
    rw [← pow_two,
      GaloisForLFunctions.RHTower.radialProlateRescaledProfile_sq_eq_density hc]
  rw [signedModeRadialGramEntry]
  change (∫ x in Ioi (1 : ℝ),
    GaloisForLFunctions.RHTower.radialProlateRescaledProfile c R (k * x) *
      GaloisForLFunctions.RHTower.radialProlateRescaledProfile c R (k * x)) = _
  rw [hpoint, MeasureTheory.integral_comp_mul_left_Ioi _ 1 hk, mul_one]
  rfl

/-- Unconditional diagonal dilation law for every fixed canonical signed mode and every strict
radial dilation. -/
theorem tendsto_signedModeRadialGramEntry_diag
    (n : ℕ) {k : ℝ} (hk : 1 < k) :
    Tendsto (fun a : ℝ => signedModeRadialGramEntry a n k k) atTop
      (nhds (Real.arcsin (1 / k) / (Real.pi * k))) := by
  have htail :=
    (tendsto_integral_Ioi_signedModeRadialDensity_unconditional n hk).const_mul k⁻¹
  have heq : (∫ x in Ioi k, _root_.RHTower.radialLeakageDensity x) =
      Real.arcsin (1 / k) :=
    _root_.RHTower.integral_Ioi_radialLeakageDensity hk.le
  have hentry :
      Tendsto (fun a : ℝ => signedModeRadialGramEntry a n k k) atTop
        (nhds (k⁻¹ * ((∫ x in Ioi k, _root_.RHTower.radialLeakageDensity x) / Real.pi))) := by
    apply htail.congr'
    filter_upwards with a
    exact (signedModeRadialGramEntry_diag_eq a n (lt_trans one_pos hk)).symm
  convert hentry using 1
  rw [heq]
  field_simp [Real.pi_ne_zero, (lt_trans one_pos hk).ne']

/-- The canonical first row is literally the previously controlled endpoint-normalized product. -/
theorem signedModeRadialGramEntry_one_left
    (a : ℝ) (n : ℕ) (k : ℝ) :
    signedModeRadialGramEntry a n 1 k =
      ∫ x in Ioi (1 : ℝ),
        GaloisForLFunctions.RHTower.firstRowRadialProduct
          (signedModeRadialBandwidth a) (signedModeRadialData a n).R k x := by
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro x _hx
  simp [GaloisForLFunctions.RHTower.firstRowRadialProduct]

/-- Unconditional canonical first-row off-diagonal cancellation. -/
theorem tendsto_signedModeRadialGramEntry_one_left
    (n : ℕ) {k : ℝ} (hk : 2 ≤ k) :
    Tendsto (fun a : ℝ => signedModeRadialGramEntry a n 1 k) atTop (nhds 0) := by
  apply (tendsto_integral_Ioi_signedModeFirstRowRadialProduct_unconditional n hk).congr'
  filter_upwards with a
  exact (signedModeRadialGramEntry_one_left a n k).symm

/-- Every fixed pair whose larger dilation is at least twice the smaller one has vanishing
canonical radial overlap. -/
theorem tendsto_signedModeRadialGramEntry_of_two_mul_le
    (n : ℕ) {j k : ℝ} (hj : 2 ≤ j) (hjk : 2 * j ≤ k) :
    Tendsto (fun a : ℝ => signedModeRadialGramEntry a n j k) atTop (nhds 0) := by
  have hj0 : 0 < j := lt_of_lt_of_le (by norm_num) hj
  have hratio : 2 ≤ k / j := by
    rw [le_div_iff₀ hj0]
    exact hjk
  have htail :=
    (tendsto_integral_Ioi_signedModeFirstRowRadialProduct_from n hratio hj).const_mul j⁻¹
  have hentry :
      Tendsto (fun a : ℝ => signedModeRadialGramEntry a n j k) atTop (nhds (j⁻¹ * 0)) := by
    apply htail.congr'
    filter_upwards with a
    exact (signedModeRadialGramEntry_scale_left a n hj0 k).symm
  simpa using hentry

/-- Symmetric version of separated-dilation cancellation. -/
theorem tendsto_signedModeRadialGramEntry_of_two_mul_le_right
    (n : ℕ) {j k : ℝ} (hk : 2 ≤ k) (hkj : 2 * k ≤ j) :
    Tendsto (fun a : ℝ => signedModeRadialGramEntry a n j k) atTop (nhds 0) := by
  have h := tendsto_signedModeRadialGramEntry_of_two_mul_le n hk hkj
    (j := k) (k := j)
  apply h.congr'
  filter_upwards with a
  exact (signedModeRadialGramEntry_comm a n j k).symm

/-- Orientation-free cancellation for dilation pairs separated by a factor of at least two. -/
theorem tendsto_signedModeRadialGramEntry_of_separated
    (n : ℕ) {j k : ℝ} (hj : 2 ≤ j) (hk : 2 ≤ k)
    (hsep : 2 * j ≤ k ∨ 2 * k ≤ j) :
    Tendsto (fun a : ℝ => signedModeRadialGramEntry a n j k) atTop (nhds 0) := by
  rcases hsep with hjk | hkj
  · exact tendsto_signedModeRadialGramEntry_of_two_mul_le n hj hjk
  · exact tendsto_signedModeRadialGramEntry_of_two_mul_le_right n hk hkj

end RHTower

end
