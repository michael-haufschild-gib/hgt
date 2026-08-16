import GaloisForLFunctions.RHTower.XiMassCausticPenetration

/-!
# The subcaustic discrepancy is a vanishing family

Retreating from the balance slope by `L u^{1/10}` costs the exterior action only

`g_u(κ_B u − L u^{1/10}) ≤ m_B L u^{1/10} + O(1)`,  `m_B = 2a² − 1/2`,

while the power-log prime number theorem supplies the gain `c (κ_B u)^{1/10} + O(1)`.  For every
`L` in the closed coefficient chamber `m_B L ≤ c κ_B^{1/10}` the two exponents cancel, and the
stationary-phase prefactor `u^{-1/2}` beats the window width `L u^{1/10}`.  The moving
prime-discrepancy annulus between the retreated height and the caustic therefore tends to zero.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The subcaustic retreat height `H_*(u) = κ_B u − L u^{1/10}`. -/
def xiMassSubcausticHeight (a L u : ℝ) : ℝ :=
  xiMassSpacelikeSharpSlope a * u - L * u ^ ((1 : ℝ) / 10)

/-- The stationary-phase prefactor vanishes. -/
theorem tendsto_one_div_sqrt_zero :
    Tendsto (fun u : ℝ => 1 / Real.sqrt u) atTop (nhds 0) := by
  have hbase := tendsto_rpow_neg_atTop (y := (1 : ℝ) / 2) (by norm_num)
  refine hbase.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  rw [Real.sqrt_eq_rpow, Real.rpow_neg hu.le]
  exact (one_div _).symm

/-- **(19.6) The subcaustic discrepancy annulus vanishes.** -/
theorem exists_tendsto_subcausticWindowDefect_zero {a sigma : ℝ} (ha : 1 / 2 < a)
    (hsigma : 0 < sigma) :
    ∃ Lc : ℝ, 0 < Lc ∧ ∀ L : ℝ, 0 < L → L ≤ Lc →
      Tendsto (fun u : ℝ =>
          ‖(∑ p ∈ primeLogWindow (xiMassSubcausticHeight a L u)
                (xiMassSpacelikeSharpSlope a * u),
              xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) p)
            - ∫ h in (xiMassSubcausticHeight a L u)..(xiMassSpacelikeSharpSlope a * u),
                xiMassCriticalGrowingFourierProfile a sigma u h‖)
        atTop (nhds 0) := by
  obtain ⟨cE, CE, h₀, hcE, hCE, hh₀, hEbd⟩ := exists_norm_xiMassThetaLogDiscrepancy_le
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hkap : 0 < xiMassSpacelikeSharpSlope a := sharpSlope_pos ha
  have hkone : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
  have hk2 : (0 : ℝ) < xiMassSpacelikeSharpSlope a ^ 2 - 1 := by nlinarith
  have hmB : (0 : ℝ) < 2 * a ^ 2 - 1 / 2 := by nlinarith
  have hkp : (0 : ℝ) < xiMassSpacelikeSharpSlope a ^ ((1 : ℝ) / 10) :=
    Real.rpow_pos_of_pos hkap _
  have hkn : (0 : ℝ) < xiMassSpacelikeSharpSlope a ^ (-((9 : ℝ) / 10)) :=
    Real.rpow_pos_of_pos hkap _
  refine ⟨cE * xiMassSpacelikeSharpSlope a ^ ((1 : ℝ) / 10) / (2 * a ^ 2 - 1 / 2),
    by positivity, fun L hL hLc => ?_⟩
  have hcap : (2 * a ^ 2 - 1 / 2) * L
      ≤ cE * xiMassSpacelikeSharpSlope a ^ ((1 : ℝ) / 10) := by
    rw [le_div_iff₀ hmB] at hLc
    linarith
  -- the inner cone slope
  obtain ⟨k0, hk0def⟩ : ∃ k0 : ℝ, (1 + xiMassSpacelikeSharpSlope a) / 2 = k0 := ⟨_, rfl⟩
  have hk0one : 1 < k0 := by rw [← hk0def]; linarith
  have hk0lt : k0 < xiMassSpacelikeSharpSlope a := by rw [← hk0def]; linarith
  have hk0pos : (0 : ℝ) < k0 := by linarith
  have hgapk : (0 : ℝ) < xiMassSpacelikeSharpSlope a - k0 := by linarith
  have hDnn : 0 ≤ xiMassWindowDefectConstant a sigma k0 :=
    xiMassWindowDefectConstant_nonneg ha0 hsigma hk0one
  -- the uniform exponent bound
  obtain ⟨K, hK⟩ : ∃ K : ℝ,
      8 * a ^ 2 * xiMassSpacelikeSharpSlope a * L ^ 2 / (xiMassSpacelikeSharpSlope a ^ 2 - 1)
        + cE * L * xiMassSpacelikeSharpSlope a ^ (-((9 : ℝ) / 10)) = K := ⟨_, rfl⟩
  refine squeeze_zero'
    (g := fun u : ℝ => CE * xiMassWindowDefectConstant a sigma k0 * Real.exp K
      * (2 + 1 / (a - 1 / 2)) * (1 / Real.sqrt u))
    (Eventually.of_forall fun u => norm_nonneg _) ?_ ?_
  · -- the eventual majorant
    have hgrow : Tendsto (fun u : ℝ => u ^ ((9 : ℝ) / 10)) atTop atTop :=
      tendsto_rpow_atTop (by norm_num)
    have hev2 : ∀ᶠ u : ℝ in atTop, h₀ ≤ k0 * u :=
      (Filter.tendsto_id.const_mul_atTop hk0pos).eventually_ge_atTop h₀
    have hev3 : ∀ᶠ u : ℝ in atTop,
        L / (xiMassSpacelikeSharpSlope a - k0) ≤ u ^ ((9 : ℝ) / 10) :=
      hgrow.eventually_ge_atTop _
    have hev4 : ∀ᶠ u : ℝ in atTop,
        4 * xiMassSpacelikeSharpSlope a * L / (xiMassSpacelikeSharpSlope a ^ 2 - 1)
          ≤ u ^ ((9 : ℝ) / 10) := hgrow.eventually_ge_atTop _
    filter_upwards [eventually_ge_atTop (1 : ℝ), hev2, hev3, hev4] with u hu1 hu2 hu3 hu4
    have hupos : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu1
    have hpow0 : (0 : ℝ) < u ^ ((1 : ℝ) / 10) := Real.rpow_pos_of_pos hupos _
    have hpowsplit : u ^ ((1 : ℝ) / 10) * u ^ ((9 : ℝ) / 10) = u := by
      rw [← Real.rpow_add hupos]
      norm_num
    have hrpos : (0 : ℝ) < L * u ^ ((1 : ℝ) / 10) := by positivity
    have hcone : k0 * u ≤ xiMassSubcausticHeight a L u := by
      rw [xiMassSubcausticHeight]
      have h1 : L ≤ (xiMassSpacelikeSharpSlope a - k0) * u ^ ((9 : ℝ) / 10) := by
        rw [div_le_iff₀ hgapk] at hu3
        linarith
      have h2 : L * u ^ ((1 : ℝ) / 10)
          ≤ (xiMassSpacelikeSharpSlope a - k0) * u ^ ((9 : ℝ) / 10) * u ^ ((1 : ℝ) / 10) :=
        mul_le_mul_of_nonneg_right h1 hpow0.le
      have h3 : (xiMassSpacelikeSharpSlope a - k0) * u ^ ((9 : ℝ) / 10) * u ^ ((1 : ℝ) / 10)
          = (xiMassSpacelikeSharpSlope a - k0) * u := by
        rw [mul_assoc, mul_comm (u ^ ((9 : ℝ) / 10)), hpowsplit]
      rw [h3] at h2
      linarith
    have hHT : xiMassSubcausticHeight a L u ≤ xiMassSpacelikeSharpSlope a * u := by
      rw [xiMassSubcausticHeight]
      linarith
    have hH0 : h₀ ≤ xiMassSubcausticHeight a L u := le_trans hu2 hcone
    have hx : 2 * xiMassSpacelikeSharpSlope a * (L * u ^ ((1 : ℝ) / 10))
        ≤ (1 / 2) * (u * (xiMassSpacelikeSharpSlope a ^ 2 - 1)) := by
      have h1 : 4 * xiMassSpacelikeSharpSlope a * L
          ≤ (xiMassSpacelikeSharpSlope a ^ 2 - 1) * u ^ ((9 : ℝ) / 10) := by
        rw [div_le_iff₀ hk2] at hu4
        linarith
      have h2 : 4 * xiMassSpacelikeSharpSlope a * L * u ^ ((1 : ℝ) / 10)
          ≤ (xiMassSpacelikeSharpSlope a ^ 2 - 1) * u ^ ((9 : ℝ) / 10) * u ^ ((1 : ℝ) / 10) :=
        mul_le_mul_of_nonneg_right h1 hpow0.le
      have h3 : (xiMassSpacelikeSharpSlope a ^ 2 - 1) * u ^ ((9 : ℝ) / 10) * u ^ ((1 : ℝ) / 10)
          = (xiMassSpacelikeSharpSlope a ^ 2 - 1) * u := by
        rw [mul_assoc, mul_comm (u ^ ((9 : ℝ) / 10)), hpowsplit]
      rw [h3] at h2
      linarith
    have hwin := norm_primeLogWindow_quadratureDefect_le (a := a) (sigma := sigma) (kappa := k0)
      (u := u) (H := xiMassSubcausticHeight a L u) (T := xiMassSpacelikeSharpSlope a * u)
      (CE := CE) (cE := cE) ha hsigma hk0one hupos hcone hHT hCE hcE.le
      (fun h hHh _ => hEbd h (le_trans hH0 hHh))
    refine hwin.trans ?_
    have haction := xiMassAction_penetration_le (a := a) (u := u) (r := L * u ^ ((1 : ℝ) / 10))
      ha hupos hrpos hx
    have hAB : L * u ^ ((1 : ℝ) / 10) ≤ xiMassSpacelikeSharpSlope a * u := by
      have hc := hcone
      rw [xiMassSubcausticHeight] at hc
      have hk0u : (0 : ℝ) < k0 * u := mul_pos hk0pos hupos
      linarith
    have hrp := rpow_sub_le (A := xiMassSpacelikeSharpSlope a * u)
      (B := L * u ^ ((1 : ℝ) / 10)) (p := (1 : ℝ) / 10)
      (by positivity) hrpos.le hAB (by norm_num) (by norm_num)
    have hsplitA : (xiMassSpacelikeSharpSlope a * u) ^ ((1 : ℝ) / 10)
        = xiMassSpacelikeSharpSlope a ^ ((1 : ℝ) / 10) * u ^ ((1 : ℝ) / 10) :=
      Real.mul_rpow hkap.le hupos.le
    have hsplitB : (xiMassSpacelikeSharpSlope a * u) ^ ((1 : ℝ) / 10 - 1)
        = xiMassSpacelikeSharpSlope a ^ (-((9 : ℝ) / 10)) * u ^ (-((9 : ℝ) / 10)) := by
      rw [show (1 : ℝ) / 10 - 1 = -((9 : ℝ) / 10) by norm_num]
      exact Real.mul_rpow hkap.le hupos.le
    have hue : u ^ (-((9 : ℝ) / 10)) * u ^ ((1 : ℝ) / 10) = u ^ (-((8 : ℝ) / 10)) := by
      rw [← Real.rpow_add hupos]
      norm_num
    have hule : u ^ (-((8 : ℝ) / 10)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hu1 (by norm_num)
    have hexpo : (xiMassSubcausticHeight a L u) ^ ((1 : ℝ) / 10)
        ≥ xiMassSpacelikeSharpSlope a ^ ((1 : ℝ) / 10) * u ^ ((1 : ℝ) / 10)
          - L * xiMassSpacelikeSharpSlope a ^ (-((9 : ℝ) / 10)) := by
      rw [xiMassSubcausticHeight]
      refine le_trans ?_ hrp
      rw [hsplitA, hsplitB]
      have hstep : xiMassSpacelikeSharpSlope a ^ (-((9 : ℝ) / 10)) * u ^ (-((9 : ℝ) / 10))
          * (L * u ^ ((1 : ℝ) / 10))
          = L * xiMassSpacelikeSharpSlope a ^ (-((9 : ℝ) / 10)) * u ^ (-((8 : ℝ) / 10)) := by
        rw [← hue]
        ring
      rw [hstep]
      have hnn : (0 : ℝ) ≤ L * xiMassSpacelikeSharpSlope a ^ (-((9 : ℝ) / 10)) := by positivity
      have hfin := mul_le_mul_of_nonneg_left hule hnn
      rw [mul_one] at hfin
      linarith
    have hcombine : xiMassSubcausticHeight a L u / 2
          - a * Real.sqrt (xiMassSubcausticHeight a L u ^ 2 - u ^ 2)
        + -(cE * xiMassSubcausticHeight a L u ^ ((1 : ℝ) / 10)) ≤ K := by
      have h1 : xiMassSubcausticHeight a L u / 2
          - a * Real.sqrt (xiMassSubcausticHeight a L u ^ 2 - u ^ 2)
          ≤ (2 * a ^ 2 - 1 / 2) * (L * u ^ ((1 : ℝ) / 10))
            + 8 * a ^ 2 * xiMassSpacelikeSharpSlope a * L ^ 2
              / (xiMassSpacelikeSharpSlope a ^ 2 - 1) := by
        rw [xiMassSubcausticHeight]
        refine haction.trans ?_
        have hxx : 4 * a ^ 2 * (L * u ^ ((1 : ℝ) / 10))
            * (2 * xiMassSpacelikeSharpSlope a * (L * u ^ ((1 : ℝ) / 10))
              / (u * (xiMassSpacelikeSharpSlope a ^ 2 - 1)))
            = 8 * a ^ 2 * xiMassSpacelikeSharpSlope a * L ^ 2
                / (xiMassSpacelikeSharpSlope a ^ 2 - 1)
              * (u ^ ((1 : ℝ) / 10) * u ^ ((1 : ℝ) / 10) / u) := by
          field_simp
          ring
        rw [hxx]
        have hratio : u ^ ((1 : ℝ) / 10) * u ^ ((1 : ℝ) / 10) / u ≤ 1 := by
          rw [div_le_one hupos, ← Real.rpow_add hupos]
          have hle : u ^ ((2 : ℝ) / 10) ≤ u ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
          rw [Real.rpow_one] at hle
          calc u ^ ((1 : ℝ) / 10 + (1 : ℝ) / 10) = u ^ ((2 : ℝ) / 10) := by norm_num
            _ ≤ u := hle
        have hcoefnn : (0 : ℝ) ≤ 8 * a ^ 2 * xiMassSpacelikeSharpSlope a * L ^ 2
            / (xiMassSpacelikeSharpSlope a ^ 2 - 1) := by positivity
        have hfin := mul_le_mul_of_nonneg_left hratio hcoefnn
        rw [mul_one] at hfin
        linarith
      have h2 : -(cE * xiMassSubcausticHeight a L u ^ ((1 : ℝ) / 10))
          ≤ -(cE * (xiMassSpacelikeSharpSlope a ^ ((1 : ℝ) / 10) * u ^ ((1 : ℝ) / 10)))
            + cE * L * xiMassSpacelikeSharpSlope a ^ (-((9 : ℝ) / 10)) := by
        have hfin := mul_le_mul_of_nonneg_left hexpo hcE.le
        linarith
      have h3 : (2 * a ^ 2 - 1 / 2) * (L * u ^ ((1 : ℝ) / 10))
          ≤ cE * (xiMassSpacelikeSharpSlope a ^ ((1 : ℝ) / 10) * u ^ ((1 : ℝ) / 10)) := by
        have hfin := mul_le_mul_of_nonneg_right hcap hpow0.le
        linarith
      rw [← hK]
      linarith
    have hexpbound : Real.exp (xiMassSubcausticHeight a L u / 2
          - a * Real.sqrt (xiMassSubcausticHeight a L u ^ 2 - u ^ 2))
        * Real.exp (-(cE * xiMassSubcausticHeight a L u ^ ((1 : ℝ) / 10)))
        ≤ Real.exp K := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 hcombine
    have hrootpos : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.2 hupos
    have hinv : (0 : ℝ) < 1 / (a - 1 / 2) := by
      rw [one_div]
      exact inv_pos.2 (by linarith)
    have hcoef : (0 : ℝ) ≤ (2 + 1 / (a - 1 / 2))
        * (CE * (xiMassWindowDefectConstant a sigma k0 / Real.sqrt u)) := by
      refine mul_nonneg (by linarith) (mul_nonneg hCE ?_)
      exact div_nonneg hDnn hrootpos.le
    calc (2 + 1 / (a - 1 / 2))
          * (CE * (xiMassWindowDefectConstant a sigma k0 / Real.sqrt u)
            * Real.exp (xiMassSubcausticHeight a L u / 2
              - a * Real.sqrt (xiMassSubcausticHeight a L u ^ 2 - u ^ 2))
            * Real.exp (-(cE * xiMassSubcausticHeight a L u ^ ((1 : ℝ) / 10))))
        = (2 + 1 / (a - 1 / 2))
            * (CE * (xiMassWindowDefectConstant a sigma k0 / Real.sqrt u))
          * (Real.exp (xiMassSubcausticHeight a L u / 2
              - a * Real.sqrt (xiMassSubcausticHeight a L u ^ 2 - u ^ 2))
            * Real.exp (-(cE * xiMassSubcausticHeight a L u ^ ((1 : ℝ) / 10)))) := by ring
      _ ≤ (2 + 1 / (a - 1 / 2))
            * (CE * (xiMassWindowDefectConstant a sigma k0 / Real.sqrt u)) * Real.exp K :=
          mul_le_mul_of_nonneg_left hexpbound hcoef
      _ = CE * xiMassWindowDefectConstant a sigma k0 * Real.exp K * (2 + 1 / (a - 1 / 2))
            * (1 / Real.sqrt u) := by ring
  · have := tendsto_one_div_sqrt_zero.const_mul
      (CE * xiMassWindowDefectConstant a sigma k0 * Real.exp K * (2 + 1 / (a - 1 / 2)))
    simpa using this

end

end RHTower
