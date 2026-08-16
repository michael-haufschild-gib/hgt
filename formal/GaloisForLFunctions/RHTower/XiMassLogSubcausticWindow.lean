import GaloisForLFunctions.RHTower.XiMassSubcausticVanishing
import GaloisForLFunctions.RHTower.XiMassLogRetreatTail

/-!
# The logarithmically corrected subcaustic window

Adding a further retreat `q log u` to the `u^{1/10}` boundary layer costs the action only
`m_B q log u`, while the stationary-phase prefactor supplies `u^{-1/2}`.  Hence for every
coefficient `q` with `m_B q ≤ 1/2` the prime-discrepancy annulus between

`H(u) = κ_B u − L u^{1/10} − q log u`

and the caustic stays uniformly bounded.  This is the second, logarithmic layer of the
three-scale budget: exponential action, arithmetic remainder, transport prefactor.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The logarithmically corrected subcaustic height. -/
def xiMassLogSubcausticHeight (a L q u : ℝ) : ℝ :=
  xiMassSpacelikeSharpSlope a * u - (L * u ^ ((1 : ℝ) / 10) + q * Real.log (max u 1))

theorem xiMassLogSubcausticHeight_le {a L q u : ℝ} (hL : 0 ≤ L) (hq : 0 ≤ q) (hu : 0 ≤ u) :
    xiMassLogSubcausticHeight a L q u ≤ xiMassSpacelikeSharpSlope a * u := by
  have h1 : (0 : ℝ) ≤ L * u ^ ((1 : ℝ) / 10) := by positivity
  have h2 : (0 : ℝ) ≤ q * Real.log (max u 1) :=
    mul_nonneg hq (Real.log_nonneg (le_max_right u 1))
  rw [xiMassLogSubcausticHeight]
  linarith

set_option maxHeartbeats 1200000 in
/-- **(21.8) The logarithmically corrected subcaustic annulus stays bounded.** -/
theorem exists_eventually_norm_logSubcausticWindowDefect_le {a sigma : ℝ} (ha : 1 / 2 < a)
    (hsigma : 0 < sigma) :
    ∃ Lc : ℝ, 0 < Lc ∧ ∀ L q : ℝ, 0 < L → L ≤ Lc → 0 ≤ q →
      (2 * a ^ 2 - 1 / 2) * q ≤ 1 / 2 →
      ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
        0 ≤ xiMassLogSubcausticHeight a L q u ∧
        ‖(∑ p ∈ primeLogWindow (xiMassLogSubcausticHeight a L q u)
              (xiMassSpacelikeSharpSlope a * u),
            xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) p)
          - ∫ h in (xiMassLogSubcausticHeight a L q u)..(xiMassSpacelikeSharpSlope a * u),
              xiMassCriticalGrowingFourierProfile a sigma u h‖ ≤ C := by
  obtain ⟨cE, CE, h₀, hcE, hCE, hh₀, hEbd⟩ := exists_norm_xiMassThetaLogDiscrepancy_le
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hδ : (0 : ℝ) < a - 1 / 2 := by linarith
  have hkap : 0 < xiMassSpacelikeSharpSlope a := sharpSlope_pos ha
  have hkone : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
  have hk2 : (0 : ℝ) < xiMassSpacelikeSharpSlope a ^ 2 - 1 := by nlinarith
  have hmB : (0 : ℝ) < 2 * a ^ 2 - 1 / 2 := by nlinarith
  have hkp : (0 : ℝ) < xiMassSpacelikeSharpSlope a ^ ((1 : ℝ) / 10) :=
    Real.rpow_pos_of_pos hkap _
  have hkn : (0 : ℝ) < xiMassSpacelikeSharpSlope a ^ (-((9 : ℝ) / 10)) :=
    Real.rpow_pos_of_pos hkap _
  refine ⟨cE * xiMassSpacelikeSharpSlope a ^ ((1 : ℝ) / 10) / (2 * a ^ 2 - 1 / 2),
    by positivity, fun L q hL hLc hq hqcap => ?_⟩
  have hcap : (2 * a ^ 2 - 1 / 2) * L
      ≤ cE * xiMassSpacelikeSharpSlope a ^ ((1 : ℝ) / 10) := by
    rw [le_div_iff₀ hmB] at hLc
    linarith
  obtain ⟨k0, hk0def⟩ : ∃ k0 : ℝ, (1 + xiMassSpacelikeSharpSlope a) / 2 = k0 := ⟨_, rfl⟩
  have hk0one : 1 < k0 := by rw [← hk0def]; linarith
  have hk0pos : (0 : ℝ) < k0 := by linarith
  have hgapk : (0 : ℝ) < xiMassSpacelikeSharpSlope a - k0 := by rw [← hk0def]; linarith
  have hDnn : 0 ≤ xiMassWindowDefectConstant a sigma k0 :=
    xiMassWindowDefectConstant_nonneg ha0 hsigma hk0one
  obtain ⟨R, hR⟩ : ∃ R : ℝ, L + 4 * q = R := ⟨_, rfl⟩
  have hRpos : (0 : ℝ) < R := by rw [← hR]; linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ,
      8 * a ^ 2 * xiMassSpacelikeSharpSlope a * R ^ 2 / (xiMassSpacelikeSharpSlope a ^ 2 - 1)
        + cE * R * xiMassSpacelikeSharpSlope a ^ (-((9 : ℝ) / 10)) = K := ⟨_, rfl⟩
  refine ⟨CE * xiMassWindowDefectConstant a sigma k0 * Real.exp K * (2 + 1 / (a - 1 / 2)), ?_⟩
  have hgrow : Tendsto (fun u : ℝ => u ^ ((3 : ℝ) / 4)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hev2 : ∀ᶠ u : ℝ in atTop, h₀ ≤ k0 * u :=
    (Filter.tendsto_id.const_mul_atTop hk0pos).eventually_ge_atTop h₀
  have hev3 : ∀ᶠ u : ℝ in atTop,
      R / (xiMassSpacelikeSharpSlope a - k0) ≤ u ^ ((3 : ℝ) / 4) := hgrow.eventually_ge_atTop _
  have hev4 : ∀ᶠ u : ℝ in atTop,
      4 * xiMassSpacelikeSharpSlope a * R / (xiMassSpacelikeSharpSlope a ^ 2 - 1)
        ≤ u ^ ((3 : ℝ) / 4) := hgrow.eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop (1 : ℝ), hev2, hev3, hev4] with u hu1 hu2 hu3 hu4
  have hupos : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu1
  have hpow0 : (0 : ℝ) < u ^ ((1 : ℝ) / 10) := Real.rpow_pos_of_pos hupos _
  have hpow4 : (0 : ℝ) < u ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hupos _
  have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu1
  have hsplit34 : u ^ ((1 : ℝ) / 4) * u ^ ((3 : ℝ) / 4) = u := by
    rw [← Real.rpow_add hupos]
    norm_num
  -- the retreat is at most `R u^{1/4}`
  obtain ⟨r, hr⟩ : ∃ r : ℝ, L * u ^ ((1 : ℝ) / 10) + q * Real.log u = r := ⟨_, rfl⟩
  have hrpos : (0 : ℝ) < r := by
    rw [← hr]
    have : (0 : ℝ) ≤ q * Real.log u := mul_nonneg hq hlog0
    have : (0 : ℝ) < L * u ^ ((1 : ℝ) / 10) := by positivity
    linarith [mul_nonneg hq hlog0]
  have hrle : r ≤ R * u ^ ((1 : ℝ) / 4) := by
    rw [← hr, ← hR]
    have h1 : u ^ ((1 : ℝ) / 10) ≤ u ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
    have h2 : Real.log u ≤ 4 * u ^ ((1 : ℝ) / 4) := log_le_four_mul_rpow hupos
    nlinarith [mul_le_mul_of_nonneg_left h1 hL.le, mul_le_mul_of_nonneg_left h2 hq]
  have hRu : R * u ^ ((1 : ℝ) / 4) * u ^ ((3 : ℝ) / 4) = R * u := by
    rw [mul_assoc, hsplit34]
  -- the retreat stays inside a fixed inner cone
  have hcone : k0 * u ≤ xiMassSpacelikeSharpSlope a * u - r := by
    have h1 : R ≤ (xiMassSpacelikeSharpSlope a - k0) * u ^ ((3 : ℝ) / 4) := by
      rw [div_le_iff₀ hgapk] at hu3
      linarith
    have h2 : R * u ^ ((1 : ℝ) / 4)
        ≤ (xiMassSpacelikeSharpSlope a - k0) * u ^ ((3 : ℝ) / 4) * u ^ ((1 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right h1 hpow4.le
    have h3 : (xiMassSpacelikeSharpSlope a - k0) * u ^ ((3 : ℝ) / 4) * u ^ ((1 : ℝ) / 4)
        = (xiMassSpacelikeSharpSlope a - k0) * u := by
      rw [mul_assoc, mul_comm (u ^ ((3 : ℝ) / 4)), hsplit34]
    rw [h3] at h2
    linarith
  have hHeq : xiMassLogSubcausticHeight a L q u = xiMassSpacelikeSharpSlope a * u - r := by
    rw [xiMassLogSubcausticHeight, max_eq_left hu1, hr]
  have hHT : xiMassLogSubcausticHeight a L q u ≤ xiMassSpacelikeSharpSlope a * u := by
    rw [hHeq]
    linarith
  have hcone' : k0 * u ≤ xiMassLogSubcausticHeight a L q u := by rw [hHeq]; exact hcone
  have hH0 : h₀ ≤ xiMassLogSubcausticHeight a L q u := le_trans hu2 hcone'
  refine ⟨le_trans (by positivity) hcone', ?_⟩
  -- the relative retreat is small
  have hx : 2 * xiMassSpacelikeSharpSlope a * r
      ≤ (1 / 2) * (u * (xiMassSpacelikeSharpSlope a ^ 2 - 1)) := by
    have h1 : 4 * xiMassSpacelikeSharpSlope a * R
        ≤ (xiMassSpacelikeSharpSlope a ^ 2 - 1) * u ^ ((3 : ℝ) / 4) := by
      rw [div_le_iff₀ hk2] at hu4
      linarith
    have h2 : 4 * xiMassSpacelikeSharpSlope a * R * u ^ ((1 : ℝ) / 4)
        ≤ (xiMassSpacelikeSharpSlope a ^ 2 - 1) * u ^ ((3 : ℝ) / 4) * u ^ ((1 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right h1 hpow4.le
    have h3 : (xiMassSpacelikeSharpSlope a ^ 2 - 1) * u ^ ((3 : ℝ) / 4) * u ^ ((1 : ℝ) / 4)
        = (xiMassSpacelikeSharpSlope a ^ 2 - 1) * u := by
      rw [mul_assoc, mul_comm (u ^ ((3 : ℝ) / 4)), hsplit34]
    rw [h3] at h2
    nlinarith [mul_le_mul_of_nonneg_left hrle
      (by positivity : (0 : ℝ) ≤ 2 * xiMassSpacelikeSharpSlope a), h2]
  -- the window estimate
  have hwin := norm_primeLogWindow_quadratureDefect_le (a := a) (sigma := sigma) (kappa := k0)
    (u := u) (H := xiMassLogSubcausticHeight a L q u) (T := xiMassSpacelikeSharpSlope a * u)
    (CE := CE) (cE := cE) ha hsigma hk0one hupos hcone' hHT hCE hcE.le
    (fun h hHh _ => hEbd h (le_trans hH0 hHh))
  refine hwin.trans ?_
  -- the action bound
  have haction := xiMassAction_penetration_le (a := a) (u := u) (r := r) ha hupos hrpos hx
  have hAB : r ≤ xiMassSpacelikeSharpSlope a * u := by
    have hk0u : (0 : ℝ) < k0 * u := mul_pos hk0pos hupos
    linarith
  have hrp := rpow_sub_le (A := xiMassSpacelikeSharpSlope a * u) (B := r) (p := (1 : ℝ) / 10)
    (by positivity) hrpos.le hAB (by norm_num) (by norm_num)
  have hsplitA : (xiMassSpacelikeSharpSlope a * u) ^ ((1 : ℝ) / 10)
      = xiMassSpacelikeSharpSlope a ^ ((1 : ℝ) / 10) * u ^ ((1 : ℝ) / 10) :=
    Real.mul_rpow hkap.le hupos.le
  have hsplitB : (xiMassSpacelikeSharpSlope a * u) ^ ((1 : ℝ) / 10 - 1)
      = xiMassSpacelikeSharpSlope a ^ (-((9 : ℝ) / 10)) * u ^ (-((9 : ℝ) / 10)) := by
    rw [show (1 : ℝ) / 10 - 1 = -((9 : ℝ) / 10) by norm_num]
    exact Real.mul_rpow hkap.le hupos.le
  have hue : u ^ (-((9 : ℝ) / 10)) * u ^ ((1 : ℝ) / 4) = u ^ (-((13 : ℝ) / 20)) := by
    rw [← Real.rpow_add hupos]
    norm_num
  have hule : u ^ (-((13 : ℝ) / 20)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hu1 (by norm_num)
  have hexpo : (xiMassLogSubcausticHeight a L q u) ^ ((1 : ℝ) / 10)
      ≥ xiMassSpacelikeSharpSlope a ^ ((1 : ℝ) / 10) * u ^ ((1 : ℝ) / 10)
        - R * xiMassSpacelikeSharpSlope a ^ (-((9 : ℝ) / 10)) := by
    rw [hHeq]
    refine le_trans ?_ hrp
    rw [hsplitA, hsplitB]
    have hstep : xiMassSpacelikeSharpSlope a ^ (-((9 : ℝ) / 10)) * u ^ (-((9 : ℝ) / 10)) * r
        ≤ R * xiMassSpacelikeSharpSlope a ^ (-((9 : ℝ) / 10)) := by
      have h1 : xiMassSpacelikeSharpSlope a ^ (-((9 : ℝ) / 10)) * u ^ (-((9 : ℝ) / 10)) * r
          ≤ xiMassSpacelikeSharpSlope a ^ (-((9 : ℝ) / 10)) * u ^ (-((9 : ℝ) / 10))
            * (R * u ^ ((1 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left hrle (by positivity)
      have h2 : xiMassSpacelikeSharpSlope a ^ (-((9 : ℝ) / 10)) * u ^ (-((9 : ℝ) / 10))
            * (R * u ^ ((1 : ℝ) / 4))
          = R * xiMassSpacelikeSharpSlope a ^ (-((9 : ℝ) / 10)) * u ^ (-((13 : ℝ) / 20)) := by
        rw [← hue]
        ring
      rw [h2] at h1
      have h3 := mul_le_mul_of_nonneg_left hule
        (by positivity : (0 : ℝ) ≤ R * xiMassSpacelikeSharpSlope a ^ (-((9 : ℝ) / 10)))
      rw [mul_one] at h3
      linarith
    linarith
  -- the combined exponent
  have hcombine : xiMassLogSubcausticHeight a L q u / 2
        - a * Real.sqrt (xiMassLogSubcausticHeight a L q u ^ 2 - u ^ 2)
      + -(cE * xiMassLogSubcausticHeight a L q u ^ ((1 : ℝ) / 10))
      ≤ (2 * a ^ 2 - 1 / 2) * (q * Real.log u) + K := by
    have h1 : xiMassLogSubcausticHeight a L q u / 2
        - a * Real.sqrt (xiMassLogSubcausticHeight a L q u ^ 2 - u ^ 2)
        ≤ (2 * a ^ 2 - 1 / 2) * r
          + 8 * a ^ 2 * xiMassSpacelikeSharpSlope a * R ^ 2
            / (xiMassSpacelikeSharpSlope a ^ 2 - 1) := by
      rw [hHeq]
      refine haction.trans ?_
      have hxx : 4 * a ^ 2 * r
          * (2 * xiMassSpacelikeSharpSlope a * r / (u * (xiMassSpacelikeSharpSlope a ^ 2 - 1)))
          = 8 * a ^ 2 * xiMassSpacelikeSharpSlope a / (xiMassSpacelikeSharpSlope a ^ 2 - 1)
            * (r * r / u) := by
        field_simp
        ring
      rw [hxx]
      have hratio : r * r / u ≤ R ^ 2 := by
        rw [div_le_iff₀ hupos]
        have hsq : r * r ≤ (R * u ^ ((1 : ℝ) / 4)) * (R * u ^ ((1 : ℝ) / 4)) :=
          mul_le_mul hrle hrle hrpos.le (by positivity)
        have hid : (R * u ^ ((1 : ℝ) / 4)) * (R * u ^ ((1 : ℝ) / 4))
            = R ^ 2 * u ^ ((1 : ℝ) / 2) := by
          have : u ^ ((1 : ℝ) / 4) * u ^ ((1 : ℝ) / 4) = u ^ ((1 : ℝ) / 2) := by
            rw [← Real.rpow_add hupos]
            norm_num
          calc (R * u ^ ((1 : ℝ) / 4)) * (R * u ^ ((1 : ℝ) / 4))
              = R ^ 2 * (u ^ ((1 : ℝ) / 4) * u ^ ((1 : ℝ) / 4)) := by ring
            _ = R ^ 2 * u ^ ((1 : ℝ) / 2) := by rw [this]
        rw [hid] at hsq
        have hle : u ^ ((1 : ℝ) / 2) ≤ u := by
          have := Real.rpow_le_rpow_of_exponent_le hu1 (show (1 : ℝ) / 2 ≤ 1 by norm_num)
          rwa [Real.rpow_one] at this
        nlinarith [hsq, hle, sq_nonneg R]
      have hcoefnn : (0 : ℝ) ≤ 8 * a ^ 2 * xiMassSpacelikeSharpSlope a
          / (xiMassSpacelikeSharpSlope a ^ 2 - 1) := by positivity
      have hfin := mul_le_mul_of_nonneg_left hratio hcoefnn
      have hval : 8 * a ^ 2 * xiMassSpacelikeSharpSlope a
            / (xiMassSpacelikeSharpSlope a ^ 2 - 1) * R ^ 2
          = 8 * a ^ 2 * xiMassSpacelikeSharpSlope a * R ^ 2
            / (xiMassSpacelikeSharpSlope a ^ 2 - 1) := by
        field_simp
      rw [hval] at hfin
      linarith
    have h2 : -(cE * xiMassLogSubcausticHeight a L q u ^ ((1 : ℝ) / 10))
        ≤ -(cE * (xiMassSpacelikeSharpSlope a ^ ((1 : ℝ) / 10) * u ^ ((1 : ℝ) / 10)))
          + cE * R * xiMassSpacelikeSharpSlope a ^ (-((9 : ℝ) / 10)) := by
      have hfin := mul_le_mul_of_nonneg_left hexpo hcE.le
      linarith
    have h3 : (2 * a ^ 2 - 1 / 2) * (L * u ^ ((1 : ℝ) / 10))
        ≤ cE * (xiMassSpacelikeSharpSlope a ^ ((1 : ℝ) / 10) * u ^ ((1 : ℝ) / 10)) := by
      have hfin := mul_le_mul_of_nonneg_right hcap hpow0.le
      linarith
    have hrsplit : (2 * a ^ 2 - 1 / 2) * r
        = (2 * a ^ 2 - 1 / 2) * (L * u ^ ((1 : ℝ) / 10))
          + (2 * a ^ 2 - 1 / 2) * (q * Real.log u) := by
      rw [← hr]
      ring
    rw [← hK]
    linarith
  -- the majorant
  have hlogpow : Real.exp ((2 * a ^ 2 - 1 / 2) * (q * Real.log u))
      = u ^ ((2 * a ^ 2 - 1 / 2) * q) := by
    rw [Real.rpow_def_of_pos hupos]
    congr 1
    ring
  have hexpbound : Real.exp (xiMassLogSubcausticHeight a L q u / 2
        - a * Real.sqrt (xiMassLogSubcausticHeight a L q u ^ 2 - u ^ 2))
      * Real.exp (-(cE * xiMassLogSubcausticHeight a L q u ^ ((1 : ℝ) / 10)))
      ≤ u ^ ((2 * a ^ 2 - 1 / 2) * q) * Real.exp K := by
    rw [← Real.exp_add]
    refine (Real.exp_le_exp.2 hcombine).trans (le_of_eq ?_)
    rw [Real.exp_add, hlogpow]
  have hrootpos : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.2 hupos
  have hsqrtid : Real.sqrt u = u ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow u
  have hquot : u ^ ((2 * a ^ 2 - 1 / 2) * q) / Real.sqrt u ≤ 1 := by
    rw [hsqrtid, div_le_one (Real.rpow_pos_of_pos hupos _)]
    exact Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
  have hinv : (0 : ℝ) < 1 / (a - 1 / 2) := by
    rw [one_div]
    exact inv_pos.2 hδ
  have hcoef : (0 : ℝ) ≤ (2 + 1 / (a - 1 / 2)) * (CE * xiMassWindowDefectConstant a sigma k0) :=
    mul_nonneg (by linarith) (mul_nonneg hCE hDnn)
  calc (2 + 1 / (a - 1 / 2))
        * (CE * (xiMassWindowDefectConstant a sigma k0 / Real.sqrt u)
          * Real.exp (xiMassLogSubcausticHeight a L q u / 2
            - a * Real.sqrt (xiMassLogSubcausticHeight a L q u ^ 2 - u ^ 2))
          * Real.exp (-(cE * xiMassLogSubcausticHeight a L q u ^ ((1 : ℝ) / 10))))
      = (2 + 1 / (a - 1 / 2)) * (CE * xiMassWindowDefectConstant a sigma k0)
        * ((Real.exp (xiMassLogSubcausticHeight a L q u / 2
            - a * Real.sqrt (xiMassLogSubcausticHeight a L q u ^ 2 - u ^ 2))
          * Real.exp (-(cE * xiMassLogSubcausticHeight a L q u ^ ((1 : ℝ) / 10))))
          / Real.sqrt u) := by
        field_simp
    _ ≤ (2 + 1 / (a - 1 / 2)) * (CE * xiMassWindowDefectConstant a sigma k0)
        * ((u ^ ((2 * a ^ 2 - 1 / 2) * q) * Real.exp K) / Real.sqrt u) := by
        refine mul_le_mul_of_nonneg_left ?_ hcoef
        exact div_le_div_of_nonneg_right hexpbound hrootpos.le
    _ = (2 + 1 / (a - 1 / 2)) * (CE * xiMassWindowDefectConstant a sigma k0) * Real.exp K
        * (u ^ ((2 * a ^ 2 - 1 / 2) * q) / Real.sqrt u) := by ring
    _ ≤ (2 + 1 / (a - 1 / 2)) * (CE * xiMassWindowDefectConstant a sigma k0) * Real.exp K
        * 1 := by
        refine mul_le_mul_of_nonneg_left hquot ?_
        have : (0 : ℝ) ≤ (2 + 1 / (a - 1 / 2)) * (CE * xiMassWindowDefectConstant a sigma k0) :=
          hcoef
        positivity
    _ = CE * xiMassWindowDefectConstant a sigma k0 * Real.exp K * (2 + 1 / (a - 1 / 2)) := by
        ring

end

end RHTower
