import GaloisForLFunctions.RHTower.ProlateDunsterUniformTransfer
import GaloisForLFunctions.RHTower.CCMRadialDensityBridge

/-!
# Density transfer for exact radial prolate profiles

The endpoint-normalized exact radial solution is compared directly with the regular Dunster
profile `A_s J₀(c ξ_s)`.  Squaring the uniform Volterra estimate gives an integrable error measured
by the exact profile weight.  This is the analytic bridge needed for weak convergence; no
pointwise limit of the oscillatory squared profile is asserted.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.RHTower

/-- The exact endpoint-normalized radial density. -/
def radialProlateDensity (c : ℝ) (R : ℝ → ℝ) (x : ℝ) : ℝ := c * R x ^ 2

/-- The regular Dunster/Bessel density before oscillatory averaging. -/
def radialProlateBesselDensity (s c x : ℝ) : ℝ :=
  (Real.sqrt c * xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)) ^ 2

/-- Fixed coefficient in the global exact-profile envelope. -/
def radialProlateDensityEnvelopeConstant : ℝ :=
  Real.pi * ((1 + radialProlateUniformTransferConstant) *
    lgBesselCommonEnvelopeConstant) ^ 2

theorem radialProlateDensityEnvelopeConstant_nonneg :
    0 ≤ radialProlateDensityEnvelopeConstant := by
  rw [radialProlateDensityEnvelopeConstant]
  positivity

/-- Fixed coefficient in the exact-to-Bessel squared-density error. -/
def radialProlateDensityTransferConstant : ℝ :=
  Real.pi * radialProlateUniformTransferConstant *
    (radialProlateUniformTransferConstant + 2) *
      lgBesselCommonEnvelopeConstant ^ 2

theorem radialProlateDensityTransferConstant_nonneg :
    0 ≤ radialProlateDensityTransferConstant := by
  rw [radialProlateDensityTransferConstant]
  have hK := radialProlateUniformTransferConstant_nonneg
  have hC := lgBesselCommonEnvelopeConstant_nonneg
  positivity

/-- The squared Liouville amplitude divided by the phase is exactly `pi` times the profile
weight. -/
theorem xiAmplitude_sq_div_phase_eq_pi_mul_profileWeight
    {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    xiAmplitude s x ^ 2 / xiEndpointPhase s x = Real.pi * profileWeight s x := by
  have hphase : 0 < xiEndpointPhase s x := xiEndpointPhase_pos hs0 hs1 hx
  have hamp : 0 < xiAmplitude s x := xiAmplitude_pos hs0 hs1 hx
  have hfourth := xiAmplitude_pow_four hs0 hs1 hx
  have hweight := profileWeight_eq_ampFourth_sq hs1 hx
  have hampFourth := ampFourth_sq hs1 hx
  have hleft : 0 < x ^ 2 - 1 := by nlinarith
  have hright : 0 < x ^ 2 - s := by nlinarith
  have hprod : 0 < (x ^ 2 - 1) * (x ^ 2 - s) := mul_pos hleft hright
  have hsqrt : 0 < Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s)) :=
    Real.sqrt_pos.mpr hprod
  rw [hweight, hampFourth]
  have hsq : xiAmplitude s x ^ 2 =
      xiEndpointPhase s x / Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s)) := by
    apply (sq_eq_sq₀ (sq_nonneg _) (div_nonneg hphase.le hsqrt.le)).mp
    rw [show (xiAmplitude s x ^ 2) ^ 2 = xiAmplitude s x ^ 4 by ring,
      hfourth, div_pow, Real.sq_sqrt hprod.le]
  rw [hsq]
  field_simp

/-- Pointwise exact-to-Bessel profile transfer beyond the deterministic matching point. -/
theorem abs_radialProlate_sub_besselProfile_le
    {s c x : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0)
    (hx : dunsterEndpointCrossing c ≤ x) :
    |R x - xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)|
      ≤ xiAmplitude s x *
        ((radialProlateUniformTransferConstant / c) *
          (lgBesselCommonEnvelopeConstant /
            Real.sqrt (c * xiEndpointPhase s x))) := by
  have hA1 : 1 < dunsterEndpointCrossing c :=
    dunsterEndpointCrossing_gt_one (lt_of_lt_of_le (by norm_num) hc)
  have hxx : 1 < x := hA1.trans_le hx
  have htransfer := abs_radialProlate_sub_regularModel_le
    hs0 hs1 hc (B := x) hx hR1 hR hDR hode ⟨hx, le_rfl⟩
  rw [comparisonSol_prolateNormalForm_eq_div_xiAmplitude hs0 hs1 hxx,
    lgBesselModel] at htransfer
  have hamp : 0 < xiAmplitude s x := xiAmplitude_pos hs0 hs1 hxx
  have hid : R x - xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x) =
      xiAmplitude s x *
        (R x / xiAmplitude s x - besselJ0 (c * xiEndpointPhase s x)) := by
    field_simp
  rw [hid, abs_mul, abs_of_pos hamp]
  exact mul_le_mul_of_nonneg_left htransfer hamp.le

/-- The exact density is dominated by one fixed multiple of the integrable profile weight. -/
theorem radialProlateDensity_le_profileWeight
    {s c x : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0)
    (hx : dunsterEndpointCrossing c ≤ x) :
    radialProlateDensity c R x ≤ radialProlateDensityEnvelopeConstant * profileWeight s x := by
  let K := radialProlateUniformTransferConstant
  let C := lgBesselCommonEnvelopeConstant
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hc1 : 1 ≤ c := le_trans (by norm_num) hc
  have hA1 : 1 < dunsterEndpointCrossing c := dunsterEndpointCrossing_gt_one hc0
  have hxx : 1 < x := hA1.trans_le hx
  have hphase : 0 < xiEndpointPhase s x := xiEndpointPhase_pos hs0 hs1 hxx
  have hv : 1 ≤ c * xiEndpointPhase s x := by
    exact (one_le_c_mul_xiEndpointPhase_crossing hs0 hs1 hc).trans
      (mul_le_mul_of_nonneg_left (xiEndpointPhase_le_of_le hs0 hs1 hA1.le hx) hc0.le)
  have hmodel := (lgBesselCommonEnvelopeConstant_spec s c x hv).1
  rw [lgBesselModel] at hmodel
  have htransfer := abs_radialProlate_sub_regularModel_le
    hs0 hs1 hc (B := x) hx hR1 hR hDR hode ⟨hx, le_rfl⟩
  rw [comparisonSol_prolateNormalForm_eq_div_xiAmplitude hs0 hs1 hxx,
    lgBesselModel] at htransfer
  have hK0 : 0 ≤ K := radialProlateUniformTransferConstant_nonneg
  have hC0 : 0 ≤ C := lgBesselCommonEnvelopeConstant_nonneg
  have hroot : 0 < Real.sqrt (c * xiEndpointPhase s x) := Real.sqrt_pos.mpr (mul_pos hc0 hphase)
  have hcinv : K / c ≤ K := by
    rw [div_le_iff₀ hc0]
    nlinarith
  have hU : |R x / xiAmplitude s x| ≤
      ((1 + K) * C) / Real.sqrt (c * xiEndpointPhase s x) := by
    have htri := abs_add_le
      (R x / xiAmplitude s x - besselJ0 (c * xiEndpointPhase s x))
      (besselJ0 (c * xiEndpointPhase s x))
    have hid : R x / xiAmplitude s x =
        (R x / xiAmplitude s x - besselJ0 (c * xiEndpointPhase s x)) +
          besselJ0 (c * xiEndpointPhase s x) := by ring
    rw [← hid] at htri
    calc
      |R x / xiAmplitude s x|
          ≤ |R x / xiAmplitude s x - besselJ0 (c * xiEndpointPhase s x)| +
              |besselJ0 (c * xiEndpointPhase s x)| := htri
      _ ≤ (K / c) * (C / Real.sqrt (c * xiEndpointPhase s x)) +
              C / Real.sqrt (c * xiEndpointPhase s x) := add_le_add htransfer hmodel
      _ ≤ K * (C / Real.sqrt (c * xiEndpointPhase s x)) +
              C / Real.sqrt (c * xiEndpointPhase s x) := by
            gcongr
      _ = ((1 + K) * C) / Real.sqrt (c * xiEndpointPhase s x) := by ring
  have hamp : 0 < xiAmplitude s x := xiAmplitude_pos hs0 hs1 hxx
  have hRabs : |R x| ≤ xiAmplitude s x *
      (((1 + K) * C) / Real.sqrt (c * xiEndpointPhase s x)) := by
    have heq : |R x| = xiAmplitude s x * |R x / xiAmplitude s x| := by
      calc
        |R x| = |xiAmplitude s x * (R x / xiAmplitude s x)| := by
          congr 1
          field_simp
        _ = |xiAmplitude s x| * |R x / xiAmplitude s x| := abs_mul _ _
        _ = xiAmplitude s x * |R x / xiAmplitude s x| := by rw [abs_of_pos hamp]
    rw [heq]
    exact mul_le_mul_of_nonneg_left hU hamp.le
  have hsq := (sq_le_sq₀ (abs_nonneg (R x)) (by positivity)).2 hRabs
  have hweight := xiAmplitude_sq_div_phase_eq_pi_mul_profileWeight hs0 hs1 hxx
  have hAmp : xiAmplitude s x ^ 2 =
      Real.pi * profileWeight s x * xiEndpointPhase s x := by
    rw [div_eq_iff hphase.ne'] at hweight
    exact hweight
  rw [radialProlateDensity, radialProlateDensityEnvelopeConstant]
  have hRsq : R x ^ 2 = |R x| ^ 2 := (sq_abs (R x)).symm
  rw [hRsq]
  calc
    c * |R x| ^ 2
        ≤ c * (xiAmplitude s x *
          (((1 + K) * C) / Real.sqrt (c * xiEndpointPhase s x))) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hc0.le
    _ = Real.pi * ((1 + K) * C) ^ 2 * profileWeight s x := by
      rw [mul_pow, div_pow, Real.sq_sqrt (mul_pos hc0 hphase).le, hAmp]
      field_simp
    _ = Real.pi * ((1 + radialProlateUniformTransferConstant) *
          lgBesselCommonEnvelopeConstant) ^ 2 * profileWeight s x := by rfl

/-- Squaring the exact-to-Bessel profile estimate costs only `O(c⁻¹)` in the integrable profile
weight. -/
theorem abs_radialProlateDensity_sub_besselDensity_le
    {s c x : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0)
    (hx : dunsterEndpointCrossing c ≤ x) :
    |radialProlateDensity c R x - radialProlateBesselDensity s c x|
      ≤ (radialProlateDensityTransferConstant / c) * profileWeight s x := by
  let K := radialProlateUniformTransferConstant
  let C := lgBesselCommonEnvelopeConstant
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hc1 : 1 ≤ c := le_trans (by norm_num) hc
  have hA1 : 1 < dunsterEndpointCrossing c := dunsterEndpointCrossing_gt_one hc0
  have hxx : 1 < x := hA1.trans_le hx
  have hphase : 0 < xiEndpointPhase s x := xiEndpointPhase_pos hs0 hs1 hxx
  have hv : 1 ≤ c * xiEndpointPhase s x := by
    exact (one_le_c_mul_xiEndpointPhase_crossing hs0 hs1 hc).trans
      (mul_le_mul_of_nonneg_left (xiEndpointPhase_le_of_le hs0 hs1 hA1.le hx) hc0.le)
  have hmodel := (lgBesselCommonEnvelopeConstant_spec s c x hv).1
  rw [lgBesselModel] at hmodel
  have htransfer := abs_radialProlate_sub_regularModel_le
    hs0 hs1 hc (B := x) hx hR1 hR hDR hode ⟨hx, le_rfl⟩
  rw [comparisonSol_prolateNormalForm_eq_div_xiAmplitude hs0 hs1 hxx,
    lgBesselModel] at htransfer
  have hK0 : 0 ≤ K := radialProlateUniformTransferConstant_nonneg
  have hC0 : 0 ≤ C := lgBesselCommonEnvelopeConstant_nonneg
  have hcinv : K / c ≤ K := by
    rw [div_le_iff₀ hc0]
    nlinarith
  have hsum : |R x / xiAmplitude s x + besselJ0 (c * xiEndpointPhase s x)| ≤
      ((K + 2) * C) / Real.sqrt (c * xiEndpointPhase s x) := by
    have htri := abs_add_le
      (R x / xiAmplitude s x - besselJ0 (c * xiEndpointPhase s x))
      (2 * besselJ0 (c * xiEndpointPhase s x))
    have hid : R x / xiAmplitude s x + besselJ0 (c * xiEndpointPhase s x) =
        (R x / xiAmplitude s x - besselJ0 (c * xiEndpointPhase s x)) +
          2 * besselJ0 (c * xiEndpointPhase s x) := by ring
    rw [← hid] at htri
    have htwomodel : |2 * besselJ0 (c * xiEndpointPhase s x)| ≤
        2 * (C / Real.sqrt (c * xiEndpointPhase s x)) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left hmodel (by norm_num)
    calc
      |R x / xiAmplitude s x + besselJ0 (c * xiEndpointPhase s x)|
          ≤ |R x / xiAmplitude s x - besselJ0 (c * xiEndpointPhase s x)| +
              |2 * besselJ0 (c * xiEndpointPhase s x)| := htri
      _ ≤ (K / c) * (C / Real.sqrt (c * xiEndpointPhase s x)) +
              2 * (C / Real.sqrt (c * xiEndpointPhase s x)) :=
        add_le_add htransfer htwomodel
      _ ≤ K * (C / Real.sqrt (c * xiEndpointPhase s x)) +
              2 * (C / Real.sqrt (c * xiEndpointPhase s x)) := by
            gcongr
      _ = ((K + 2) * C) / Real.sqrt (c * xiEndpointPhase s x) := by ring
  have hweight := xiAmplitude_sq_div_phase_eq_pi_mul_profileWeight hs0 hs1 hxx
  have hamp : 0 < xiAmplitude s x := xiAmplitude_pos hs0 hs1 hxx
  have hfac : radialProlateDensity c R x - radialProlateBesselDensity s c x =
      c * xiAmplitude s x ^ 2 *
        ((R x / xiAmplitude s x - besselJ0 (c * xiEndpointPhase s x)) *
          (R x / xiAmplitude s x + besselJ0 (c * xiEndpointPhase s x))) := by
    rw [radialProlateDensity, radialProlateBesselDensity]
    simp only [mul_pow, Real.sq_sqrt hc0.le]
    field_simp
    ring
  rw [hfac, abs_mul, abs_mul, abs_mul, abs_of_pos hc0, abs_of_pos (sq_pos_of_pos hamp)]
  have hprod := mul_le_mul htransfer hsum (abs_nonneg _) (by positivity)
  calc
    c * xiAmplitude s x ^ 2 *
        (|R x / xiAmplitude s x - besselJ0 (c * xiEndpointPhase s x)| *
          |R x / xiAmplitude s x + besselJ0 (c * xiEndpointPhase s x)|)
        ≤ c * xiAmplitude s x ^ 2 *
          (((K / c) * (C / Real.sqrt (c * xiEndpointPhase s x))) *
            (((K + 2) * C) / Real.sqrt (c * xiEndpointPhase s x))) :=
      mul_le_mul_of_nonneg_left hprod (mul_nonneg hc0.le (sq_nonneg _))
    _ = (Real.pi * K * (K + 2) * C ^ 2 / c) * profileWeight s x := by
      have hrootSq : Real.sqrt (c * xiEndpointPhase s x) ^ 2 =
          c * xiEndpointPhase s x := Real.sq_sqrt (mul_pos hc0 hphase).le
      have hAmp : xiAmplitude s x ^ 2 =
          Real.pi * profileWeight s x * xiEndpointPhase s x := by
        rw [div_eq_iff hphase.ne'] at hweight
        linarith
      rw [hAmp]
      field_simp [hc0.ne', hphase.ne']
      rw [hrootSq]
      ring
    _ = (radialProlateDensityTransferConstant / c) * profileWeight s x := by rfl

/-- The `s`-dependent profile weight is uniformly dominated by four times the limiting density. -/
theorem profileWeight_le_four_mul_profileDensity
    {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    profileWeight s x ≤ 4 * profileDensity x := by
  have hdiff := abs_profileWeight_sub_density_le hs0 hs1 hx
  have hden : 0 < x ^ 2 - s := by nlinarith
  have hratio : 3 * s / (x ^ 2 - s) ≤ 3 := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hD0 : 0 ≤ profileDensity x := profileDensity_nonneg hx.le
  have hupper : profileWeight s x - profileDensity x ≤
      3 * s * profileDensity x / (x ^ 2 - s) := (abs_le.mp hdiff).2
  have hsmall : 3 * s * profileDensity x / (x ^ 2 - s) ≤ 3 * profileDensity x := by
    calc
      3 * s * profileDensity x / (x ^ 2 - s) =
          (3 * s / (x ^ 2 - s)) * profileDensity x := by ring
      _ ≤ 3 * profileDensity x := mul_le_mul_of_nonneg_right hratio hD0
  linarith

/-- Every admissible profile weight is integrable on a strict exterior tail. -/
theorem integrableOn_profileWeight
    {s a : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (ha : 1 < a) :
    IntegrableOn (profileWeight s) (Ioi a) := by
  have hsubset : Ioi a ⊆ Ioi (1 : ℝ) := Ioi_subset_Ioi ha.le
  have hdom : IntegrableOn (fun x : ℝ => 4 * profileDensity x) (Ioi a) :=
    (integrableOn_profileDensity.mono_set hsubset).const_mul 4
  have hcont : ContinuousOn (profileWeight s) (Ioi a) := by
    intro x hx
    exact (hasDerivAt_profileWeight hs1 (ha.trans hx)).continuousAt.continuousWithinAt
  refine Integrable.mono' hdom
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (profileWeight_pos hs1 (ha.trans hx)).le]
  exact profileWeight_le_four_mul_profileDensity hs0 hs1 (ha.trans hx)

/-- Uniform total profile-weight bound on every strict exterior tail. -/
theorem integral_Ioi_profileWeight_le_two
    {s a : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (ha : 1 < a) :
    (∫ x in Ioi a, profileWeight s x) ≤ 2 := by
  have hsubset : Ioi a ⊆ Ioi (1 : ℝ) := Ioi_subset_Ioi ha.le
  have hmono : (∫ x in Ioi a, profileWeight s x) ≤
      ∫ x in Ioi a, 4 * profileDensity x := by
    apply integral_mono_ae
      (integrableOn_profileWeight hs0 hs1 ha)
      ((integrableOn_profileDensity.mono_set hsubset).const_mul 4)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact profileWeight_le_four_mul_profileDensity hs0 hs1 (ha.trans hx)
  calc
    (∫ x in Ioi a, profileWeight s x)
        ≤ ∫ x in Ioi a, 4 * profileDensity x := hmono
    _ = 4 * ∫ x in Ioi a, profileDensity x := by rw [integral_const_mul]
    _ ≤ 4 * ∫ x in Ioi (1 : ℝ), profileDensity x := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact setIntegral_mono_set integrableOn_profileDensity
        ((ae_restrict_mem measurableSet_Ioi).mono fun x hx => profileDensity_nonneg hx.le)
        (Filter.Eventually.of_forall hsubset)
    _ = 2 := by rw [integral_Ioi_profileDensity]; ring

/-- The exact Bessel density has the same fixed integrable envelope. -/
theorem radialProlateBesselDensity_le_profileWeight
    {s c x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c)
    (hx : 1 < x) (hv : 1 ≤ c * xiEndpointPhase s x) :
    radialProlateBesselDensity s c x ≤
      Real.pi * lgBesselCommonEnvelopeConstant ^ 2 * profileWeight s x := by
  let C := lgBesselCommonEnvelopeConstant
  have hC0 : 0 ≤ C := lgBesselCommonEnvelopeConstant_nonneg
  have hphase : 0 < xiEndpointPhase s x := xiEndpointPhase_pos hs0 hs1 hx
  have hmodel := (lgBesselCommonEnvelopeConstant_spec s c x hv).1
  rw [lgBesselModel] at hmodel
  have hsq := (sq_le_sq₀ (abs_nonneg (besselJ0 (c * xiEndpointPhase s x)))
    (div_nonneg hC0 (Real.sqrt_nonneg _))).2 hmodel
  have hweight := xiAmplitude_sq_div_phase_eq_pi_mul_profileWeight hs0 hs1 hx
  have hAmp : xiAmplitude s x ^ 2 =
      Real.pi * profileWeight s x * xiEndpointPhase s x := by
    rw [div_eq_iff hphase.ne'] at hweight
    exact hweight
  have hJ : besselJ0 (c * xiEndpointPhase s x) ^ 2 =
      |besselJ0 (c * xiEndpointPhase s x)| ^ 2 := (sq_abs _).symm
  rw [radialProlateBesselDensity, mul_pow, mul_pow, Real.sq_sqrt hc.le, hJ]
  calc
    c * xiAmplitude s x ^ 2 * |besselJ0 (c * xiEndpointPhase s x)| ^ 2
        ≤ c * xiAmplitude s x ^ 2 *
          (C / Real.sqrt (c * xiEndpointPhase s x)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (mul_nonneg hc.le (sq_nonneg _))
    _ = Real.pi * C ^ 2 * profileWeight s x := by
      rw [div_pow, Real.sq_sqrt (mul_pos hc hphase).le, hAmp]
      field_simp
    _ = Real.pi * lgBesselCommonEnvelopeConstant ^ 2 * profileWeight s x := rfl

theorem radialProlateBesselDensity_nonneg (s c x : ℝ) :
    0 ≤ radialProlateBesselDensity s c x := by
  rw [radialProlateBesselDensity]
  positivity

theorem continuousOn_radialProlateBesselDensity
    {s c a : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (ha : 1 < a) :
    ContinuousOn (radialProlateBesselDensity s c) (Ioi a) := by
  have hsub : Ioi a ⊆ Ioi (1 : ℝ) := Ioi_subset_Ioi ha.le
  unfold radialProlateBesselDensity
  exact (((continuousOn_const.mul
    ((continuousOn_xiAmplitude hs0 hs1).mono hsub)).mul
      (continuous_besselJ0.comp_continuousOn
        (continuousOn_const.mul
          ((continuousOn_xiEndpointPhase hs0).mono hsub)))).pow 2)

/-- The regular Bessel density is integrable on every strict exterior tail once its argument has
entered the uniform Bessel regime at the left endpoint. -/
theorem integrableOn_radialProlateBesselDensity
    {s c a : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c)
    (ha : 1 < a) (hca : 1 ≤ c * xiEndpointPhase s a) :
    IntegrableOn (radialProlateBesselDensity s c) (Ioi a) := by
  let K : ℝ := Real.pi * lgBesselCommonEnvelopeConstant ^ 2
  have hdom : IntegrableOn (fun x : ℝ => K * profileWeight s x) (Ioi a) :=
    (integrableOn_profileWeight hs0 hs1 ha).const_mul K
  refine Integrable.mono' hdom
    ((continuousOn_radialProlateBesselDensity hs0 hs1 ha).aestronglyMeasurable
      measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hphase : xiEndpointPhase s a ≤ xiEndpointPhase s x :=
    xiEndpointPhase_le_of_le hs0 hs1 ha.le hx.le
  have hcx : 1 ≤ c * xiEndpointPhase s x :=
    hca.trans (mul_le_mul_of_nonneg_left hphase hc.le)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (radialProlateBesselDensity_nonneg s c x)]
  exact radialProlateBesselDensity_le_profileWeight hs0 hs1 hc (ha.trans hx) hcx

/-- Uniform Bessel-density tail domination by the limiting profile density. -/
theorem integral_Ioi_radialProlateBesselDensity_le
    {s c a : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c)
    (ha : 1 < a) (hca : 1 ≤ c * xiEndpointPhase s a) :
    (∫ x in Ioi a, radialProlateBesselDensity s c x) ≤
      (4 * Real.pi * lgBesselCommonEnvelopeConstant ^ 2) *
        ∫ x in Ioi a, profileDensity x := by
  let K : ℝ := 4 * Real.pi * lgBesselCommonEnvelopeConstant ^ 2
  have hsubset : Ioi a ⊆ Ioi (1 : ℝ) := Ioi_subset_Ioi ha.le
  have htarget : IntegrableOn (fun x : ℝ => K * profileDensity x) (Ioi a) :=
    (integrableOn_profileDensity.mono_set hsubset).const_mul K
  have hmono : (∫ x in Ioi a, radialProlateBesselDensity s c x) ≤
      ∫ x in Ioi a, K * profileDensity x := by
    apply integral_mono_ae
      (integrableOn_radialProlateBesselDensity hs0 hs1 hc ha hca) htarget
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hphase : xiEndpointPhase s a ≤ xiEndpointPhase s x :=
      xiEndpointPhase_le_of_le hs0 hs1 ha.le hx.le
    have hcx : 1 ≤ c * xiEndpointPhase s x :=
      hca.trans (mul_le_mul_of_nonneg_left hphase hc.le)
    have hB := radialProlateBesselDensity_le_profileWeight
      hs0 hs1 hc (ha.trans hx) hcx
    have hW := profileWeight_le_four_mul_profileDensity hs0 hs1 (ha.trans hx)
    have hcoef : 0 ≤ Real.pi * lgBesselCommonEnvelopeConstant ^ 2 := by positivity
    calc
      radialProlateBesselDensity s c x
          ≤ Real.pi * lgBesselCommonEnvelopeConstant ^ 2 * profileWeight s x := hB
      _ ≤ Real.pi * lgBesselCommonEnvelopeConstant ^ 2 * (4 * profileDensity x) :=
        mul_le_mul_of_nonneg_left hW hcoef
      _ = K * profileDensity x := by rw [K]; ring
  calc
    (∫ x in Ioi a, radialProlateBesselDensity s c x)
        ≤ ∫ x in Ioi a, K * profileDensity x := hmono
    _ = K * ∫ x in Ioi a, profileDensity x := by rw [integral_const_mul]
    _ = (4 * Real.pi * lgBesselCommonEnvelopeConstant ^ 2) *
          ∫ x in Ioi a, profileDensity x := by rfl

/-- Global `L¹` exact-to-Bessel density transfer on every tail beginning beyond the matching
point. -/
theorem integral_Ioi_abs_radialProlateDensity_sub_besselDensity_le
    {s c a : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c)
    (hca : dunsterEndpointCrossing c ≤ a)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    (∫ x in Ioi a,
      |radialProlateDensity c R x - radialProlateBesselDensity s c x|)
      ≤ 2 * radialProlateDensityTransferConstant / c := by
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hcross : 1 < dunsterEndpointCrossing c := dunsterEndpointCrossing_gt_one hc0
  have ha : 1 < a := hcross.trans_le hca
  let E : ℝ → ℝ := fun x =>
    (radialProlateDensityTransferConstant / c) * profileWeight s x
  have hEint : IntegrableOn E (Ioi a) :=
    (integrableOn_profileWeight hs0 hs1 ha).const_mul
      (radialProlateDensityTransferConstant / c)
  have hRcont : Continuous R := continuous_iff_continuousAt.mpr fun x => (hR x).continuousAt
  have hBcont : ContinuousOn (radialProlateBesselDensity s c) (Ioi a) := by
    have hsub : Ioi a ⊆ Ioi (1 : ℝ) := Ioi_subset_Ioi ha.le
    unfold radialProlateBesselDensity
    exact (((continuousOn_const.mul
      ((continuousOn_xiAmplitude hs0 hs1).mono hsub)).mul
        (continuous_besselJ0.comp_continuousOn
          (continuousOn_const.mul
            ((continuousOn_xiEndpointPhase hs0).mono hsub)))).pow 2)
  have hFmeas : AEStronglyMeasurable
      (fun x => |radialProlateDensity c R x - radialProlateBesselDensity s c x|)
      (volume.restrict (Ioi a)) := by
    have hExact : Continuous (radialProlateDensity c R) := by
      unfold radialProlateDensity
      fun_prop
    exact ((hExact.continuousOn.sub hBcont).abs.aestronglyMeasurable measurableSet_Ioi)
  have hFint : IntegrableOn
      (fun x => |radialProlateDensity c R x - radialProlateBesselDensity s c x|)
      (Ioi a) := by
    refine Integrable.mono' hEint hFmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    exact abs_radialProlateDensity_sub_besselDensity_le hs0 hs1 hc hR1 hR hDR hode
      (hca.trans hx.le)
  have hmono : (∫ x in Ioi a,
      |radialProlateDensity c R x - radialProlateBesselDensity s c x|) ≤
      ∫ x in Ioi a, E x := by
    apply integral_mono_ae hFint hEint
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact abs_radialProlateDensity_sub_besselDensity_le hs0 hs1 hc hR1 hR hDR hode
      (hca.trans hx.le)
  calc
    (∫ x in Ioi a,
        |radialProlateDensity c R x - radialProlateBesselDensity s c x|)
        ≤ ∫ x in Ioi a, E x := hmono
    _ = (radialProlateDensityTransferConstant / c) *
          ∫ x in Ioi a, profileWeight s x := by rw [integral_const_mul]
    _ ≤ (radialProlateDensityTransferConstant / c) * 2 := by
      gcongr
      · exact div_nonneg radialProlateDensityTransferConstant_nonneg hc0.le
      · exact integral_Ioi_profileWeight_le_two hs0 hs1 ha
    _ = 2 * radialProlateDensityTransferConstant / c := by ring

end GaloisForLFunctions.RHTower

end
