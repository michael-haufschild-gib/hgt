import GaloisForLFunctions.RHTower.CHMDGeneratorWeilOperator

/-!
# The threshold of the arithmetic resolvent is essential spectrum

Along the primitive cusp escape `p_T` (unit-mass normalized translates of a fixed pole-annihilated
compact CHMDTranslation.profile), the resolvent defect `‖(R − 1/2) p_T‖` tends to zero. The explicit generator
formula gives `‖(R − 1/2) v‖ ≤ ‖𝒲₀(Θv)/cosh(·/2)‖_μ / 2`, the pole-free Weil operator commutes
with translation, and it grows at most like the polar rate `cosh(·/2)`; so the numerator is
`O(cosh²(T/2))` while the inverse-Doob mass of the CHMDTranslation.translate grows like `exp(π e^{2T})`. Separated
translates are orthonormal, hence the resolvent has an orthonormal Weyl sequence at `1/2`: the
critical value of the Doob form is not an isolated eigenvalue of finite multiplicity but a point of
the essential spectrum, and in particular `1/2 ∈ spectrum ℝ R`.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump CHMDEscape

/-! ## Translation covariance of the pole-free Weil operator -/

theorem weilOp_translate (f : ℝ → ℝ) (T y : ℝ) :
    weilOp (CHMDTranslation.translate f T) y = weilOp f (y - T) := by
  unfold weilOp CHMDTranslation.translate
  have h1 : ∀ u : ℝ, y + u - T = y - T + u := fun u => by ring
  have h2 : ∀ u : ℝ, y - u - T = y - T - u := fun u => by ring
  simp only [h1, h2]

theorem phiDoobTest_test (t : ℝ) : phiDoobTest (test t) = CHMDTranslation.translate CHMDTranslation.profile t := by
  funext x
  exact phiDoobTest_phiDoobInv _ x

theorem translate_zero (f : ℝ → ℝ) : CHMDTranslation.translate f 0 = f := by
  funext x
  simp [CHMDTranslation.translate]

/-- The generator image of the escape test is the translated Weil operator of the CHMDTranslation.profile. -/
theorem genImage_test (t y : ℝ) :
    genImage (test t) y = weilOp CHMDTranslation.profile (y - t) / Real.cosh (y / 2) := by
  rw [genImage_eq_weilOp (test_contDiff t) (test_compact t), phiDoobTest_test, weilOp_translate]

/-- The Weil operator of the CHMDTranslation.profile grows at most like the polar rate. -/
theorem exists_weilOp_profile_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z, |weilOp CHMDTranslation.profile z| ≤ K * (1 + Real.cosh (z / 2)) := by
  obtain ⟨K, hK0, hK⟩ := exists_weilOp_bound (test_contDiff 0) (test_compact 0)
  refine ⟨K, hK0, fun z => ?_⟩
  have h := hK z
  rwa [phiDoobTest_test, translate_zero] at h

/-! ## Hyperbolic bounds -/

theorem abs_sinh_le_cosh (x : ℝ) : |Real.sinh x| ≤ Real.cosh x := by
  have h : |Real.sinh x| ^ 2 ≤ Real.cosh x ^ 2 := by
    rw [sq_abs, Real.sinh_sq]
    linarith
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (Real.cosh_pos _).le two_ne_zero).mp h

theorem cosh_sub_le (a b : ℝ) : Real.cosh (a - b) ≤ 2 * Real.cosh a * Real.cosh b := by
  rw [Real.cosh_sub]
  have h1 := abs_sinh_le_cosh a
  have h2 := abs_sinh_le_cosh b
  have h3 : Real.sinh a * Real.sinh b ≥ -(Real.cosh a * Real.cosh b) := by
    have := abs_mul (Real.sinh a) (Real.sinh b)
    have h4 : |Real.sinh a * Real.sinh b| ≤ Real.cosh a * Real.cosh b := by
      rw [abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) (Real.cosh_pos _).le
    linarith [neg_abs_le (Real.sinh a * Real.sinh b)]
  linarith

theorem cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp.mpr (le_abs_self x)
  have h2 : Real.exp (-x) ≤ Real.exp |x| := Real.exp_le_exp.mpr (neg_le_abs x)
  linarith

/-! ## The numerator: the generator image of the escape -/

theorem integrable_theta_sq_weight (K t : ℝ) :
    Integrable fun y : ℝ => 2 * K ^ 2 * (riemannKernelReal y + 4 * Real.cosh (t / 2) ^ 2 * massDensity y) :=
  (WeilExcess.integrable_riemannKernelReal.add (integrable_massDensity.const_mul _)).const_mul _

/-- The generator image of the escape test has mass `O(cosh²(t/2))`. -/
theorem exists_genImage_test_bound :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ t,
      ‖genImageL (test t) (test_contDiff t) (test_compact t)‖ ^ 2 ≤ A + B * Real.cosh (t / 2) ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := exists_weilOp_profile_bound
  refine ⟨2 * K ^ 2 * ∫ y, riemannKernelReal y, 4 * K ^ 2,
    mul_nonneg (by positivity) (integral_nonneg fun y => (riemannKernelReal_pos y).le), by positivity,
    fun t => ?_⟩
  unfold genImageL
  rw [norm_sq_eq_integral]
  have hae : (∫ y, ((memLp_genImage (test_contDiff t) (test_compact t)).toLp (genImage (test t))) y ^ 2
      ∂massMeasure) = ∫ y, genImage (test t) y ^ 2 ∂massMeasure := by
    apply integral_congr_ae
    filter_upwards [(memLp_genImage (test_contDiff t) (test_compact t)).coeFn_toLp] with y hy
    rw [hy]
  rw [hae, integral_mass]
  have hpt : ∀ y, massDensity y * genImage (test t) y ^ 2 ≤
      2 * K ^ 2 * (riemannKernelReal y + 4 * Real.cosh (t / 2) ^ 2 * massDensity y) := by
    intro y
    rw [genImage_test, div_pow]
    unfold massDensity
    have hc := Real.cosh_pos (y / 2)
    have hΘ := riemannKernelReal_pos y
    have hw := hK (y - t)
    have hw2 : weilOp CHMDTranslation.profile (y - t) ^ 2 ≤ (K * (1 + Real.cosh ((y - t) / 2))) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hw 2
    have hcs : Real.cosh ((y - t) / 2) ≤ 2 * Real.cosh (y / 2) * Real.cosh (t / 2) := by
      rw [show (y - t) / 2 = y / 2 - t / 2 by ring]
      exact cosh_sub_le _ _
    have hc1 := Real.one_le_cosh (y / 2)
    have hct := Real.one_le_cosh (t / 2)
    have hsq : (1 + Real.cosh ((y - t) / 2)) ^ 2 ≤ 2 * (1 + 4 * Real.cosh (y / 2) ^ 2 * Real.cosh (t / 2) ^ 2) := by
      have h0 : 0 ≤ Real.cosh ((y - t) / 2) := (Real.cosh_pos _).le
      nlinarith [sq_nonneg (1 - Real.cosh ((y - t) / 2)), mul_nonneg (mul_nonneg hc.le (Real.cosh_pos (t/2)).le) h0]
    calc riemannKernelReal y * Real.cosh (y / 2) * (weilOp CHMDTranslation.profile (y - t) ^ 2 / Real.cosh (y / 2) ^ 2)
        = riemannKernelReal y / Real.cosh (y / 2) * weilOp CHMDTranslation.profile (y - t) ^ 2 := by
          field_simp
      _ ≤ riemannKernelReal y / Real.cosh (y / 2) * (K ^ 2 * (2 * (1 + 4 * Real.cosh (y / 2) ^ 2 *
            Real.cosh (t / 2) ^ 2))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc weilOp CHMDTranslation.profile (y - t) ^ 2 ≤ (K * (1 + Real.cosh ((y - t) / 2))) ^ 2 := hw2
            _ = K ^ 2 * (1 + Real.cosh ((y - t) / 2)) ^ 2 := by ring
            _ ≤ K ^ 2 * (2 * (1 + 4 * Real.cosh (y / 2) ^ 2 * Real.cosh (t / 2) ^ 2)) :=
                mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 2 * K ^ 2 * (riemannKernelReal y / Real.cosh (y / 2) +
            4 * Real.cosh (t / 2) ^ 2 * (riemannKernelReal y * Real.cosh (y / 2))) := by
          field_simp
      _ ≤ 2 * K ^ 2 * (riemannKernelReal y + 4 * Real.cosh (t / 2) ^ 2 *
            (riemannKernelReal y * Real.cosh (y / 2))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : riemannKernelReal y / Real.cosh (y / 2) ≤ riemannKernelReal y :=
            div_le_self hΘ.le hc1
          linarith
  have hint : Integrable fun y => massDensity y * genImage (test t) y ^ 2 := by
    have hm := (memLp_genImage (test_contDiff t) (test_compact t)).integrable_sq
    rwa [integrable_mass_iff] at hm
  calc (∫ y, massDensity y * genImage (test t) y ^ 2)
      ≤ ∫ y, 2 * K ^ 2 * (riemannKernelReal y + 4 * Real.cosh (t / 2) ^ 2 * massDensity y) :=
        integral_mono hint (integrable_theta_sq_weight K t) hpt
    _ = 2 * K ^ 2 * (∫ y, riemannKernelReal y) + 4 * K ^ 2 * Real.cosh (t / 2) ^ 2 := by
        rw [integral_const_mul, integral_add WeilExcess.integrable_riemannKernelReal
          (integrable_massDensity.const_mul _), integral_const_mul, integral_massDensity]
        ring

/-! ## The denominator: the inverse-Doob mass of the CHMDTranslation.translate -/

theorem profile_sq_integral_pos : 0 < ∫ x, CHMDTranslation.profile x ^ 2 := by
  have hc : Continuous fun x => CHMDTranslation.profile x ^ 2 := CHMDTranslation.profile_contDiff.continuous.pow 2
  have hint : Integrable fun x => CHMDTranslation.profile x ^ 2 :=
    hc.integrable_of_hasCompactSupport (CHMDTranslation.profile_compact.comp_left (g := fun y : ℝ => y ^ 2) (by simp))
  rw [integral_pos_iff_support_of_nonneg (fun x => sq_nonneg _) hint]
  have hopen : IsOpen (Function.support fun x => CHMDTranslation.profile x ^ 2) := hc.isOpen_support
  refine hopen.measure_pos volume ⟨0, ?_⟩
  simp only [Function.mem_support, ne_eq, pow_eq_zero_iff, OfNat.ofNat_ne_zero, not_false_eq_true]
  rw [CHMDTranslation.profile_zero]
  exact neg_ne_zero.mpr (Real.cosh_pos 1).ne'

/-- The inverse weight at a translated point is super-exponentially large. -/
theorem inverseWeight_lower {R t x : ℝ} (hx : -R ≤ x ∧ x ≤ R) (ht : R ≤ t) :
    Real.exp (Real.pi * Real.exp (2 * (t - R))) / (HedenmalmThetaSource.thetaEnvelopeUpper * Real.exp (9 * (t + R) / 2)) ≤
      CHMDTranslation.inverseWeight (x + t) := by
  unfold CHMDTranslation.inverseWeight
  have hΘ := riemannKernelReal_pos (x + t)
  have hpos : 0 < HedenmalmThetaSource.thetaEnvelopeUpper * Real.exp (9 * (t + R) / 2) :=
    mul_pos HedenmalmThetaSource.thetaEnvelopeUpper_pos (Real.exp_pos _)
  have hup := CHMDThetaTranslate.theta_upper (x + t)
  have hxt : 0 ≤ x + t := by linarith
  rw [abs_of_nonneg hxt] at hup
  unfold HedenmalmThetaSource.thetaEnvelope at hup
  have henv : Real.exp (9 * (x + t) / 2) * Real.exp (-Real.pi * Real.exp (2 * (x + t))) ≤
      Real.exp (9 * (t + R) / 2) * Real.exp (-Real.pi * Real.exp (2 * (t - R))) := by
    apply mul_le_mul _ _ (Real.exp_pos _).le (Real.exp_pos _).le
    · exact Real.exp_le_exp.mpr (by linarith)
    · apply Real.exp_le_exp.mpr
      have := Real.exp_le_exp.mpr (by linarith : 2 * (t - R) ≤ 2 * (x + t))
      nlinarith [Real.pi_pos]
  have hΘle : riemannKernelReal (x + t) ≤ HedenmalmThetaSource.thetaEnvelopeUpper * Real.exp (9 * (t + R) / 2) *
      Real.exp (-Real.pi * Real.exp (2 * (t - R))) := by
    calc riemannKernelReal (x + t) ≤ HedenmalmThetaSource.thetaEnvelopeUpper * (Real.exp (9 * (x + t) / 2) *
          Real.exp (-Real.pi * Real.exp (2 * (x + t)))) := hup
      _ ≤ HedenmalmThetaSource.thetaEnvelopeUpper * (Real.exp (9 * (t + R) / 2) *
          Real.exp (-Real.pi * Real.exp (2 * (t - R)))) :=
          mul_le_mul_of_nonneg_left henv HedenmalmThetaSource.thetaEnvelopeUpper_pos.le
      _ = _ := by ring
  have hc := Real.one_le_cosh ((x + t) / 2)
  rw [div_le_div_iff₀ hpos hΘ]
  have hneg : Real.exp (-Real.pi * Real.exp (2 * (t - R))) =
      (Real.exp (Real.pi * Real.exp (2 * (t - R))))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  have hE : 0 < Real.exp (Real.pi * Real.exp (2 * (t - R))) := Real.exp_pos _
  calc Real.exp (Real.pi * Real.exp (2 * (t - R))) * riemannKernelReal (x + t)
      ≤ Real.exp (Real.pi * Real.exp (2 * (t - R))) * (HedenmalmThetaSource.thetaEnvelopeUpper *
          Real.exp (9 * (t + R) / 2) * Real.exp (-Real.pi * Real.exp (2 * (t - R)))) :=
        mul_le_mul_of_nonneg_left hΘle hE.le
    _ = HedenmalmThetaSource.thetaEnvelopeUpper * Real.exp (9 * (t + R) / 2) := by
        rw [hneg]
        field_simp
    _ ≤ Real.cosh ((x + t) / 2) * (HedenmalmThetaSource.thetaEnvelopeUpper * Real.exp (9 * (t + R) / 2)) := by
        nlinarith

/-- Lower bound of the inverse-Doob mass of the translated CHMDTranslation.profile. -/
theorem inverseMass_translate_lower {R : ℝ}
    (hR : ∀ x, CHMDTranslation.profile x ≠ 0 → -R ≤ x ∧ x ≤ R) {t : ℝ} (ht : R ≤ t) :
    (∫ x, CHMDTranslation.profile x ^ 2) * (Real.exp (Real.pi * Real.exp (2 * (t - R))) /
      (HedenmalmThetaSource.thetaEnvelopeUpper * Real.exp (9 * (t + R) / 2))) ≤ CHMDTranslation.inverseMass (CHMDTranslation.translate CHMDTranslation.profile t) := by
  rw [CHMDTranslation.inverseMass_translate, ← integral_mul_const]
  have hc : Continuous fun x => CHMDTranslation.profile x ^ 2 := CHMDTranslation.profile_contDiff.continuous.pow 2
  have hcs : HasCompactSupport fun x => CHMDTranslation.profile x ^ 2 :=
    CHMDTranslation.profile_compact.comp_left (g := fun y : ℝ => y ^ 2) (by simp)
  have hint1 : Integrable fun x => CHMDTranslation.profile x ^ 2 * (Real.exp (Real.pi * Real.exp (2 * (t - R))) /
      (HedenmalmThetaSource.thetaEnvelopeUpper * Real.exp (9 * (t + R) / 2))) :=
    (hc.integrable_of_hasCompactSupport hcs).mul_const _
  have hint2 : Integrable fun x => CHMDTranslation.profile x ^ 2 * CHMDTranslation.inverseWeight (x + t) :=
    ((CHMDTranslation.profile_contDiff.continuous.pow 2).mul
      (CHMDTranslation.inverseWeight_continuous.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hcs.mul_right
  refine integral_mono hint1 hint2 fun x => ?_
  by_cases hx : CHMDTranslation.profile x = 0
  · simp [hx]
  · exact mul_le_mul_of_nonneg_left (inverseWeight_lower (hR x hx) ht) (sq_nonneg _)

/-! ## The resolvent defect along the escape -/

theorem source_lift_eq (t : ℝ) :
    source (lift t) = (compactLift (test t) (test_contDiff t) (test_compact t)).val.fst := rfl

/-- The resolvent defect of the normalized escape vector. -/
theorem norm_resolvent_sub_half_normalized_le (t : ℝ) :
    ‖resolvent (source (normalized t)) - (1 / 2 : ℝ) • source (normalized t)‖ ≤
      (1 / 2 : ℝ) * (‖genImageL (test t) (test_contDiff t) (test_compact t)‖ / ‖source (lift t)‖) := by
  have h : resolvent (source (normalized t)) - (1 / 2 : ℝ) • source (normalized t) =
      ‖source (lift t)‖⁻¹ • (resolvent (source (lift t)) - (1 / 2 : ℝ) • source (lift t)) := by
    rw [normalized, source_smul, map_smul, smul_sub, smul_comm]
  rw [h, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, source_lift_eq]
  have hb := norm_resolvent_sub_half_le (test_contDiff t) (test_compact t)
  have hpos : 0 < ‖(compactLift (test t) (test_contDiff t) (test_compact t)).val.fst‖ :=
    lift_source_norm_pos t
  calc ‖(compactLift (test t) (test_contDiff t) (test_compact t)).val.fst‖⁻¹ *
        ‖resolvent (compactLift (test t) (test_contDiff t) (test_compact t)).val.fst -
          (1 / 2 : ℝ) • (compactLift (test t) (test_contDiff t) (test_compact t)).val.fst‖
      ≤ ‖(compactLift (test t) (test_contDiff t) (test_compact t)).val.fst‖⁻¹ *
          ((1 / 2 : ℝ) * ‖genImageL (test t) (test_contDiff t) (test_compact t)‖) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hpos.le)
    _ = _ := by rw [div_eq_mul_inv]; ring

theorem cosh_sq_le_exp {t : ℝ} (ht : 0 ≤ t) : Real.cosh (t / 2) ^ 2 ≤ Real.exp t := by
  have h := cosh_le_exp_abs (t / 2)
  rw [abs_of_nonneg (by linarith)] at h
  have h0 := (Real.cosh_pos (t / 2)).le
  calc Real.cosh (t / 2) ^ 2 ≤ Real.exp (t / 2) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = Real.exp t := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

/-- The squared defect ratio is dominated by a super-exponentially decaying function. -/
theorem exists_ratio_bound : ∃ C R : ℝ, 0 ≤ C ∧ 0 < R ∧
    (∀ x, CHMDTranslation.profile x ≠ 0 → -R ≤ x ∧ x ≤ R) ∧ ∀ t, R ≤ t →
      (‖genImageL (test t) (test_contDiff t) (test_compact t)‖ / ‖source (lift t)‖) ^ 2 ≤
        C * Real.exp (9 * (t + R) / 2 + t - Real.pi * Real.exp (2 * (t - R))) := by
  obtain ⟨A, B, hA, hB, hAB⟩ := exists_genImage_test_bound
  obtain ⟨R, hR0, hR⟩ := CHMDTranslation.support_interval CHMDTranslation.profile_compact
  have hP := profile_sq_integral_pos
  refine ⟨(A + B) * HedenmalmThetaSource.thetaEnvelopeUpper / ∫ x, CHMDTranslation.profile x ^ 2, R,
    div_nonneg (mul_nonneg (by linarith) HedenmalmThetaSource.thetaEnvelopeUpper_pos.le) hP.le, hR0, hR,
    fun t ht => ?_⟩
  have ht0 : 0 ≤ t := by linarith
  rw [div_pow, lift_mass]
  have hI := inverseMass_translate_lower hR ht
  have hIpos : 0 < CHMDTranslation.inverseMass (CHMDTranslation.translate CHMDTranslation.profile t) :=
    CHMDTranslation.inverseMass_pos (CHMDTranslation.continuous_translate CHMDTranslation.profile_contDiff.continuous t)
      (CHMDTranslation.compact_translate CHMDTranslation.profile_compact t) (translated_profile_ne_zero t)
  have hnum := hAB t
  have hcosh := cosh_sq_le_exp ht0
  have hexp1 : 1 ≤ Real.exp t := Real.one_le_exp ht0
  set E := Real.exp (Real.pi * Real.exp (2 * (t - R))) with hE
  set D := HedenmalmThetaSource.thetaEnvelopeUpper * Real.exp (9 * (t + R) / 2) with hD
  have hEpos : 0 < E := Real.exp_pos _
  have hDpos : 0 < D := mul_pos HedenmalmThetaSource.thetaEnvelopeUpper_pos (Real.exp_pos _)
  have hden : 0 < (∫ x, CHMDTranslation.profile x ^ 2) * (E / D) := mul_pos hP (div_pos hEpos hDpos)
  have hnum' : ‖genImageL (test t) (test_contDiff t) (test_compact t)‖ ^ 2 ≤ (A + B) * Real.exp t := by
    calc ‖genImageL (test t) (test_contDiff t) (test_compact t)‖ ^ 2
        ≤ A + B * Real.cosh (t / 2) ^ 2 := hnum
      _ ≤ A * Real.exp t + B * Real.exp t := by nlinarith
      _ = (A + B) * Real.exp t := by ring
  have hrhs : (A + B) * HedenmalmThetaSource.thetaEnvelopeUpper / (∫ x, CHMDTranslation.profile x ^ 2) *
      Real.exp (9 * (t + R) / 2 + t - Real.pi * Real.exp (2 * (t - R))) =
      (A + B) * Real.exp t / ((∫ x, CHMDTranslation.profile x ^ 2) * (E / D)) := by
    rw [hE, hD, Real.exp_sub, Real.exp_add]
    field_simp
  rw [hrhs]
  calc ‖genImageL (test t) (test_contDiff t) (test_compact t)‖ ^ 2 / CHMDTranslation.inverseMass (CHMDTranslation.translate CHMDTranslation.profile t)
      ≤ (A + B) * Real.exp t / CHMDTranslation.inverseMass (CHMDTranslation.translate CHMDTranslation.profile t) :=
        div_le_div_of_nonneg_right hnum' hIpos.le
    _ ≤ (A + B) * Real.exp t / ((∫ x, CHMDTranslation.profile x ^ 2) * (E / D)) :=
        div_le_div_of_nonneg_left (mul_nonneg (by linarith) (Real.exp_pos t).le) hden hI

/-- The dominating function tends to zero. -/
theorem bound_tendsto_zero {C : ℝ} (hC : 0 ≤ C) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun t => C * Real.exp (9 * (t + R) / 2 + t - Real.pi * Real.exp (2 * (t - R))))
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun t : ℝ => C * Real.exp (9 * R / 2) * Real.exp (-t)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (C * Real.exp (9 * R / 2))
  refine squeeze_zero' (Eventually.of_forall fun t => mul_nonneg hC (Real.exp_pos _).le) ?_ hlim
  filter_upwards [eventually_ge_atTop (2 * R + 2)] with t ht
  have htR : 0 ≤ 2 * (t - R) := by linarith
  have hq := Real.quadratic_le_exp_of_nonneg htR
  have hsq : 2 * t ≤ (t - R) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ t) (by linarith : (0 : ℝ) ≤ t - 2 * R - 2), sq_nonneg R]
  have hpi := Real.pi_gt_three
  have hexp : 9 * (t + R) / 2 + t - Real.pi * Real.exp (2 * (t - R)) ≤ 9 * R / 2 + -t := by
    nlinarith [Real.exp_pos (2 * (t - R)), mul_nonneg (le_of_lt (by linarith : (0:ℝ) < Real.pi)) htR]
  rw [mul_assoc, ← Real.exp_add]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hC

/-- **The resolvent defect along the primitive cusp escape tends to zero.** -/
theorem resolvent_defect_tendsto_zero :
    Tendsto (fun t => ‖resolvent (source (normalized t)) - (1 / 2 : ℝ) • source (normalized t)‖)
      atTop (𝓝 0) := by
  obtain ⟨C, R, hC, hR0, -, hbound⟩ := exists_ratio_bound
  have hlim : Tendsto (fun t => (1 / 2 : ℝ) * Real.sqrt
      (C * Real.exp (9 * (t + R) / 2 + t - Real.pi * Real.exp (2 * (t - R))))) atTop (𝓝 0) := by
    have := ((bound_tendsto_zero hC hR0).sqrt).const_mul (1 / 2 : ℝ)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop R] with t ht
  refine (norm_resolvent_sub_half_normalized_le t).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine Real.le_sqrt_of_sq_le ?_
  exact hbound t ht

/-! ## The orthonormal Weyl sequence -/

/-- An orthonormal Weyl sequence of the arithmetic resolvent at the threshold `1/2`. -/
theorem exists_weyl_sequence :
    ∃ e : ℕ → MassSpace, Orthonormal ℝ e ∧
      Tendsto (fun n => ‖resolvent (e n) - (1 / 2 : ℝ) • e n‖) atTop (𝓝 0) := by
  obtain ⟨R, hR0, hR⟩ := CHMDTranslation.support_interval CHMDTranslation.profile_compact
  let τ : ℕ → ℝ := fun n => R + (2 * R + 1) * n
  have hτ : Tendsto τ atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => (2 * R + 1) * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by linarith)
    exact tendsto_atTop_add_const_left _ R h1
  refine ⟨fun n => source (normalized (τ n)), ?_, ?_⟩
  · rw [orthonormal_iff_ite]
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [if_true]
      rw [real_inner_self_eq_norm_sq, normalized_source_norm]
      norm_num
    · simp only [hij, if_false]
      rcases lt_or_gt_of_ne hij with h | h
      · apply separated_normalized_inner hR
        have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
        simp only [τ]
        nlinarith
      · rw [real_inner_comm]
        apply separated_normalized_inner hR
        have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
        simp only [τ]
        nlinarith
  · exact resolvent_defect_tendsto_zero.comp hτ

/-- **The threshold `1/2` belongs to the spectrum of the arithmetic resolvent.** -/
theorem half_mem_spectrum_resolvent : (1 / 2 : ℝ) ∈ spectrum ℝ resolvent := by
  rw [spectrum.mem_iff]
  intro hu
  obtain ⟨e, he, hlim⟩ := exists_weyl_sequence
  obtain ⟨b, hb⟩ := hu.exists_left_inv
  have key : ∀ n, (1 : ℝ) ≤ ‖b‖ * ‖resolvent (e n) - (1 / 2 : ℝ) • e n‖ := by
    intro n
    have h1 : e n = b ((algebraMap ℝ (MassSpace →L[ℝ] MassSpace) (1 / 2) - resolvent) (e n)) := by
      have := congrArg (fun T : MassSpace →L[ℝ] MassSpace => T (e n)) hb
      exact this.symm
    have h2 : (algebraMap ℝ (MassSpace →L[ℝ] MassSpace) (1 / 2) - resolvent) (e n) =
        (1 / 2 : ℝ) • e n - resolvent (e n) := by
      rw [sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply]
      rfl
    calc (1 : ℝ) = ‖e n‖ := (he.1 n).symm
      _ = ‖b ((1 / 2 : ℝ) • e n - resolvent (e n))‖ := by rw [← h2, ← h1]
      _ ≤ ‖b‖ * ‖(1 / 2 : ℝ) • e n - resolvent (e n)‖ := b.le_opNorm _
      _ = ‖b‖ * ‖resolvent (e n) - (1 / 2 : ℝ) • e n‖ := by rw [norm_sub_rev]
  have hlim' : Tendsto (fun n => ‖b‖ * ‖resolvent (e n) - (1 / 2 : ℝ) • e n‖) atTop (𝓝 0) := by
    simpa using hlim.const_mul ‖b‖
  obtain ⟨n, hn⟩ := (hlim'.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).exists
  exact absurd (key n) (not_le.mpr hn)

end RHTower.CHMDPolar
