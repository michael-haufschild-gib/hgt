import GaloisForLFunctions.RHTower.LiClockThetaSignedGammaJumps
import GaloisForLFunctions.HTGeometry.LaplaceTransformConvolution
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.Complex.Convex
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Group.IntegralConvolution

/-!
Finite positive measures carried on the nonnegative half-line are determined
by their Laplace transforms at every nonnegative real parameter. The complex
MGFs are admitted on the open negative half-plane, then their characteristic
functions are recovered by a dominated boundary limit.
-/

open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology

namespace RHTower
noncomputable section

local notation "Lap" => GaloisForLFunctions.HTGeometry.laplace

private theorem sgl_real_exp_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) {r : ℝ} (hr : r ≤ 0) :
    Integrable (fun x : ℝ => Real.exp (r*x)) μ := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards [hμ] with x hx
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
  apply Real.exp_le_one_iff.mpr
  nlinarith

private theorem sgl_neg_interior (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) {r : ℝ} (hr : r < 0) :
    r ∈ interior (integrableExpSet id μ) := by
  rw [mem_interior_iff_mem_nhds]
  filter_upwards [gt_mem_nhds hr] with u hu
  exact sgl_real_exp_integrable μ hμ hu.le

private theorem sgl_real_mgf_eq_laplace (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) {r : ℝ} (hr : r ≤ 0) :
    complexMGF id μ (r : ℂ) = ((Lap μ (-r)).toReal : ℂ) := by
  rw [complexMGF_ofReal]
  congr 1
  have hInt := sgl_real_exp_integrable μ hμ hr
  simpa only [mgf, id_eq, GaloisForLFunctions.HTGeometry.laplace,
    neg_mul, neg_neg] using
    (integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => (Real.exp_pos (r*x)).le) hInt.1)

private theorem sgl_mgf_eq_negative_halfPlane (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (hν : ∀ᵐ x ∂ν, 0 ≤ x)
    (hLap : ∀ s : ℝ, 0 ≤ s → Lap μ s = Lap ν s) :
    EqOn (complexMGF id μ) (complexMGF id ν) {z : ℂ | z.re < 0} := by
  have hAμ : AnalyticOnNhd ℂ (complexMGF id μ) {z : ℂ | z.re < 0} :=
    analyticOnNhd_complexMGF.mono fun z hz => sgl_neg_interior μ hμ hz
  have hAν : AnalyticOnNhd ℂ (complexMGF id ν) {z : ℂ | z.re < 0} :=
    analyticOnNhd_complexMGF.mono fun z hz => sgl_neg_interior ν hν hz
  apply AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hAμ hAν
    (convex_halfSpace_re_lt 0).isPreconnected (z₀ := ((-1 : ℝ) : ℂ)) (by norm_num)
  have hreal : ∃ᶠ r : ℝ in 𝓝[≠] (-1), complexMGF id μ r = complexMGF id ν r := by
    have hnegative : ∀ᶠ r : ℝ in 𝓝[≠] (-1), r < 0 :=
      (gt_mem_nhds (by norm_num : (-1 : ℝ) < 0)).filter_mono nhdsWithin_le_nhds
    refine hnegative.frequently.mono fun r hr => ?_
    rw [sgl_real_mgf_eq_laplace μ hμ hr.le,
      sgl_real_mgf_eq_laplace ν hν hr.le, hLap (-r) (by linarith)]
  rw [frequently_iff_seq_forall] at hreal ⊢
  obtain ⟨xs, hxs, heq⟩ := hreal
  refine ⟨fun n => (xs n : ℂ), ?_, fun n => heq n⟩
  rw [tendsto_nhdsWithin_iff] at hxs ⊢
  constructor
  · rw [Filter.tendsto_ofReal_iff]
    exact hxs.1
  · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_inj] using hxs.2

private theorem sgl_boundary_mgf_tendsto (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (ξ : ℝ) :
    Tendsto (fun n : ℕ => complexMGF id μ
      (((-(1 / ((n : ℝ)+1)) : ℝ) : ℂ) + (ξ : ℂ)*Complex.I)) atTop
      (𝓝 (charFun μ ξ)) := by
  have hparameter : Tendsto (fun n : ℕ =>
      (((-(1 / ((n : ℝ)+1)) : ℝ) : ℂ) + (ξ : ℂ)*Complex.I)) atTop
      (𝓝 ((ξ : ℂ)*Complex.I)) := by
    have hneg : Tendsto (fun n : ℕ => -(1 / ((n : ℝ)+1))) atTop (𝓝 (0 : ℝ)) := by
      simpa only [neg_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
    simpa only [Function.comp_def, Complex.ofReal_zero, zero_add] using
      ((Complex.continuous_ofReal.tendsto 0).comp hneg).add_const ((ξ : ℂ)*Complex.I)
  have hDCT := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n : ℕ => fun x : ℝ => Complex.exp
      ((((-(1 / ((n : ℝ)+1)) : ℝ) : ℂ) + (ξ : ℂ)*Complex.I) * (x : ℂ)))
    (f := fun x : ℝ => Complex.exp (((ξ : ℂ)*Complex.I) * (x : ℂ)))
    (fun _ : ℝ => (1 : ℝ)) (fun _ => by fun_prop)
    (integrable_const 1) ?_ ?_
  · change Tendsto (fun n : ℕ => complexMGF id μ
        (((-(1 / ((n : ℝ)+1)) : ℝ) : ℂ) + (ξ : ℂ)*Complex.I)) atTop
        (𝓝 (complexMGF id μ ((ξ : ℂ)*Complex.I))) at hDCT
    simpa only [complexMGF_id_mul_I] using hDCT
  · intro n
    filter_upwards [hμ] with x hx
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
      zero_mul, add_zero]
    have hp : 0 < (n : ℝ)+1 := by positivity
    have hi : 0 < 1 / ((n : ℝ)+1) := by positivity
    nlinarith
  · exact Filter.Eventually.of_forall fun x =>
      (Complex.continuous_exp.tendsto (((ξ : ℂ)*Complex.I) * (x : ℂ))).comp
        (hparameter.mul_const (x : ℂ))

/-- Finite measures carried by `[0, ∞)` with equal Laplace transforms on `s ≥ 0` coincide. -/
theorem finite_halfLine_laplace_ext (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t)
    (hLap : ∀ s : ℝ, 0 ≤ s → Lap μ s = Lap ν s) : μ = ν := by
  have hnegative := sgl_mgf_eq_negative_halfPlane μ ν hμ hν hLap
  apply Measure.ext_of_charFun
  funext ξ
  have heq : (fun n : ℕ => complexMGF id μ
      (((-(1 / ((n : ℝ)+1)) : ℝ) : ℂ) + (ξ : ℂ)*Complex.I)) =
      (fun n : ℕ => complexMGF id ν
      (((-(1 / ((n : ℝ)+1)) : ℝ) : ℂ) + (ξ : ℂ)*Complex.I)) := by
    funext n
    apply hnegative
    simp only [Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero]
    have hp : 0 < (n : ℝ)+1 := by positivity
    have hi : 0 < 1 / ((n : ℝ)+1) := by positivity
    linarith
  have hμlimit := sgl_boundary_mgf_tendsto μ hμ ξ
  rw [heq] at hμlimit
  exact tendsto_nhds_unique hμlimit (sgl_boundary_mgf_tendsto ν hν ξ)

end
end RHTower


open MeasureTheory Set
open scoped ENNReal

namespace RHTower
noncomputable section

/-- Normalizing a measure of positive finite mass gives a probability measure. -/
theorem isProbabilityMeasure_inv_ofReal_smul (μ : Measure ℝ) {mass : ℝ}
    (hmass : 0 < mass) (hμ : μ univ = ENNReal.ofReal mass) :
    IsProbabilityMeasure ((ENNReal.ofReal mass)⁻¹ • μ) := by
  constructor
  rw [Measure.smul_apply, smul_eq_mul, hμ]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hmass).ne' ENNReal.ofReal_ne_top

private theorem sgc_conv_nonnegative (μ ν : Measure ℝ) [SFinite ν]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (hν : ∀ᵐ x ∂ν, 0 ≤ x) :
    ∀ᵐ x ∂μ ∗ ν, 0 ≤ x := by
  rw [Measure.conv]
  apply (ae_map_iff (by fun_prop) measurableSet_Ici).2
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [hμ] with x hx
  filter_upwards [hν] with y hy
  exact add_nonneg hx hy

private theorem sgc_convPow_nonnegative (μ : Measure ℝ) [SFinite μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (n : ℕ) :
    ∀ᵐ x ∂GaloisForLFunctions.HTGeometry.convPow μ n, 0 ≤ x := by
  induction n with
  | zero =>
    rw [GaloisForLFunctions.HTGeometry.convPow]
    exact (ae_dirac_iff measurableSet_Ici).2 le_rfl
  | succ n ih =>
    rw [GaloisForLFunctions.HTGeometry.convPow]
    exact sgc_conv_nonnegative μ _ hμ ih

/-- A compound Poisson law with jumps carried by `[0, ∞)` is carried by `[0, ∞)`. -/
theorem compoundPoisson_ae_nonneg (μ : Measure ℝ) [SFinite μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (lam : ℝ) :
    ∀ᵐ x ∂GaloisForLFunctions.HTGeometry.compoundPoisson lam μ, 0 ≤ x := by
  rw [GaloisForLFunctions.HTGeometry.compoundPoisson,
    GaloisForLFunctions.HTGeometry.convPowMixture, Measure.ae_sum_iff]
  intro n
  exact Measure.ae_smul_measure (sgc_convPow_nonnegative μ hμ n) _

end
end RHTower

namespace RHTower
noncomputable section

/-- `L CP(t·m, G/m)(s) = exp(t (L G(s) - m))` for a jump measure `G` of mass `m`. -/
theorem laplace_normalized_compoundPoisson (μ : Measure ℝ) {mass time s : ℝ}
    (hmass : 0 < mass) (hμ : μ univ = ENNReal.ofReal mass)
    (hcarrier : ∀ᵐ x ∂μ, 0 ≤ x) (htime : 0 ≤ time) (hs : 0 ≤ s) :
    GaloisForLFunctions.HTGeometry.laplace
      (GaloisForLFunctions.HTGeometry.compoundPoisson (time*mass)
        ((ENNReal.ofReal mass)⁻¹ • μ)) s =
      ENNReal.ofReal (Real.exp
        (time*((GaloisForLFunctions.HTGeometry.laplace μ s).toReal-mass))) := by
  haveI := isProbabilityMeasure_inv_ofReal_smul μ hmass hμ
  have hQ : ∀ᵐ x ∂(ENNReal.ofReal mass)⁻¹ • μ, 0 ≤ x :=
    Measure.ae_smul_measure hcarrier _
  have hfin : GaloisForLFunctions.HTGeometry.laplace
      ((ENNReal.ofReal mass)⁻¹ • μ) s ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (GaloisForLFunctions.HTGeometry.laplace_le_one _ hs hQ)
  rw [GaloisForLFunctions.HTGeometry.laplace_compoundPoisson
    (time*mass) (mul_nonneg htime hmass.le) _ s hfin]
  apply congrArg ENNReal.ofReal
  apply congrArg Real.exp
  have hscale : (GaloisForLFunctions.HTGeometry.laplace
      ((ENNReal.ofReal mass)⁻¹ • μ) s).toReal =
      mass⁻¹*(GaloisForLFunctions.HTGeometry.laplace μ s).toReal := by
    simp only [GaloisForLFunctions.HTGeometry.laplace, lintegral_smul_measure,
      ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hmass.le,
      smul_eq_mul]
  rw [hscale]
  field_simp [hmass.ne']

end
end RHTower

namespace RHTower
noncomputable section

local notation "Lap" => GaloisForLFunctions.HTGeometry.laplace
local notation "CP" => GaloisForLFunctions.HTGeometry.compoundPoisson
local notation "CPow" => GaloisForLFunctions.HTGeometry.convPow

private theorem sgc_normalized_cp_coupling (μ τplus τminus : Measure ℝ)
    [IsProbabilityMeasure μ] {mplus mminus : ℝ}
    (hplus : 0 < mplus) (hminus : 0 < mminus)
    (hmplus : τplus univ = ENNReal.ofReal mplus)
    (hmminus : τminus univ = ENNReal.ofReal mminus)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t)
    (hcplus : ∀ᵐ t ∂τplus, 0 ≤ t) (hcminus : ∀ᵐ t ∂τminus, 0 ≤ t)
    (hlog : ∀ s : ℝ, 0 ≤ s →
      Real.log (Lap μ s).toReal =
        ((Lap τplus s).toReal - (Lap τminus s).toReal) - (mplus-mminus)) :
    μ ∗ CP mminus ((ENNReal.ofReal mminus)⁻¹ • τminus) =
      CP mplus ((ENNReal.ofReal mplus)⁻¹ • τplus) := by
  haveI := isProbabilityMeasure_inv_ofReal_smul τplus hplus hmplus
  haveI := isProbabilityMeasure_inv_ofReal_smul τminus hminus hmminus
  haveI := GaloisForLFunctions.HTGeometry.isProbabilityMeasure_compoundPoisson
    mplus hplus.le ((ENNReal.ofReal mplus)⁻¹ • τplus)
  haveI := GaloisForLFunctions.HTGeometry.isProbabilityMeasure_compoundPoisson
    mminus hminus.le ((ENNReal.ofReal mminus)⁻¹ • τminus)
  have hP := compoundPoisson_ae_nonneg _
    (Measure.ae_smul_measure hcplus (ENNReal.ofReal mplus)⁻¹) mplus
  have hM := compoundPoisson_ae_nonneg _
    (Measure.ae_smul_measure hcminus (ENNReal.ofReal mminus)⁻¹) mminus
  apply finite_halfLine_laplace_ext _ _ (sgc_conv_nonnegative _ _ hμ hM) hP
  intro s hs
  have hfin : Lap μ s ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top
    (GaloisForLFunctions.HTGeometry.laplace_le_one μ hs hμ)
  have hpos : 0 < (Lap μ s).toReal := ENNReal.toReal_pos
    (GaloisForLFunctions.HTGeometry.laplace_pos μ s).ne' hfin
  have hμexp : Lap μ s = ENNReal.ofReal
      (Real.exp (((Lap τplus s).toReal - (Lap τminus s).toReal) - (mplus-mminus))) := by
    rw [←hlog s hs, Real.exp_log hpos, ENNReal.ofReal_toReal hfin]
  have hPlap := laplace_normalized_compoundPoisson τplus hplus hmplus hcplus
    (time := 1) zero_le_one hs
  have hMlap := laplace_normalized_compoundPoisson τminus hminus hmminus hcminus
    (time := 1) zero_le_one hs
  simp only [one_mul] at hPlap hMlap
  rw [GaloisForLFunctions.HTGeometry.laplace_conv, hμexp, hMlap, hPlap,
    ←ENNReal.ofReal_mul (Real.exp_nonneg _), ←Real.exp_add]
  congr 2
  ring

private theorem sgc_integer_cp_coupling (μ Qplus Qminus : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure Qplus] [IsProbabilityMeasure Qminus]
    {lamplus lamminus : ℝ} (hplus : 0 ≤ lamplus) (hminus : 0 ≤ lamminus)
    (hunit : μ ∗ CP lamminus Qminus = CP lamplus Qplus) (n : ℕ) :
    CP ((n : ℝ)*lamplus) Qplus = CP ((n : ℝ)*lamminus) Qminus ∗ CPow μ n := by
  haveI := GaloisForLFunctions.HTGeometry.isProbabilityMeasure_compoundPoisson
    lamminus hminus Qminus
  haveI := GaloisForLFunctions.HTGeometry.isProbabilityMeasure_compoundPoisson
    ((n : ℝ)*lamminus) (mul_nonneg (Nat.cast_nonneg n) hminus) Qminus
  have h := congrArg (fun ν => CPow ν n) hunit
  rw [GaloisForLFunctions.HTGeometry.convPow_conv,
    GaloisForLFunctions.HTGeometry.convPow_compoundPoisson lamminus hminus,
    GaloisForLFunctions.HTGeometry.convPow_compoundPoisson lamplus hplus] at h
  rw [←h, Measure.conv_comm]

end
end RHTower

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace RHTower
noncomputable section
local notation "Lap" => GaloisForLFunctions.HTGeometry.laplace

private theorem sgd_parameter_gt_one {p s : ℝ} (hp : 1 < p) (hs : 0 ≤ s) :
    1 < p * Real.exp (s/2) := by
  have he : 1 ≤ Real.exp (s/2) := Real.one_le_exp_iff.mpr (by linarith)
  nlinarith

private theorem sgd_power_parameter (p s : ℝ) (j : ℕ) :
    (p * Real.exp (s/2))^(2*j) = p^(2*j) * Real.exp (s*(j:ℝ)) := by
  have he : Real.exp (s/2)^(2*j) = Real.exp (s*(j:ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [mul_pow, he]

private theorem sgd_numerator_damping (p s : ℝ) (j : ℕ) :
    thetaCuspNormalizedEvenMoment j /
        (((2*j).factorial:ℝ) * (p*Real.exp (s/2))^(2*j)) =
      (thetaCuspNormalizedEvenMoment j / (((2*j).factorial:ℝ) * p^(2*j))) *
        Real.exp (-(s*(j:ℝ))) := by
  rw [sgd_power_parameter, ← mul_assoc, div_mul_eq_div_div]
  simp only [div_eq_mul_inv, Real.exp_neg]

private theorem sgd_ell_damping (p s : ℝ) (j : ℕ) :
    liClockThetaLogJumpCoefficient (p * Real.exp (s/2)) j =
      liClockThetaLogJumpCoefficient p j * Real.exp (-(s*(j:ℝ))) := by
  by_cases hj : j = 0
  · simp [hj, liClockThetaLogJumpCoefficient]
  · simp only [liClockThetaLogJumpCoefficient, if_neg hj]
    rw [sgd_power_parameter, ← mul_assoc, div_mul_eq_div_div]
    simp only [div_eq_mul_inv, Real.exp_neg]

private theorem sgd_part_data {p : ℝ} (hp : 1 < p) (positive : Bool) :
    (∀ j : ℕ, 0 ≤ liClockThetaJumpPart p positive j) ∧
      Summable (liClockThetaJumpPart p positive) := by
  have hn (j : ℕ) : 0 ≤ liClockThetaJumpPart p positive j := by
    unfold liClockThetaJumpPart
    split <;> exact le_max_right _ _
  have hle (j : ℕ) : liClockThetaJumpPart p positive j ≤
      |liClockThetaLogJumpCoefficient p j| := by
    unfold liClockThetaJumpPart
    split
    · exact max_le (le_abs_self _) (abs_nonneg _)
    · exact max_le (neg_le_abs _) (abs_nonneg _)
  exact ⟨hn, Summable.of_nonneg_of_le hn hle (liClockThetaLogJumpCoefficient_admission hp).1⟩

private theorem sgd_parts_sub (p : ℝ) (j : ℕ) :
    liClockThetaJumpPart p true j - liClockThetaJumpPart p false j =
      liClockThetaLogJumpCoefficient p j := by
  by_cases h : 0 ≤ liClockThetaLogJumpCoefficient p j
  · simp [liClockThetaJumpPart, max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
  · have hle : liClockThetaLogJumpCoefficient p j ≤ 0 := (lt_of_not_ge h).le
    simp [liClockThetaJumpPart, max_eq_right hle, max_eq_left (neg_nonneg.mpr hle)]

private theorem sgd_atomic_laplace_admission
    {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j) (hws : Summable w)
    {s : ℝ} (hs : 0 ≤ s) :
    let μ : Measure ℝ := Measure.sum (fun j : ℕ => ENNReal.ofReal (w j) • Measure.dirac (j : ℝ))
    let d : ℕ → ℝ := fun j => w j * Real.exp (-(s * (j : ℝ)))
    Summable d ∧ Integrable (fun t : ℝ => Real.exp (-(s*t))) μ ∧
      Lap μ s = ENNReal.ofReal (∑' j, d j) ∧ Lap μ s ≠ ∞ := by
  dsimp only
  have hn (j : ℕ) : 0 ≤ w j * Real.exp (-(s*(j:ℝ))) :=
    mul_nonneg (hw j) (Real.exp_nonneg _)
  have hle (j : ℕ) : w j * Real.exp (-(s*(j:ℝ))) ≤ w j := by
    have he : Real.exp (-(s*(j:ℝ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hs (Nat.cast_nonneg j)))
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he (hw j)
  have hd := Summable.of_nonneg_of_le hn hle hws
  have he : Lap (Measure.sum (fun j : ℕ => ENNReal.ofReal (w j) • Measure.dirac (j : ℝ))) s =
      ENNReal.ofReal (∑' j : ℕ, w j * Real.exp (-(s*(j:ℝ)))) := by
    rw [GaloisForLFunctions.HTGeometry.laplace, lintegral_sum_measure]
    simp only [lintegral_smul_measure, smul_eq_mul,
      lintegral_dirac' _ (GaloisForLFunctions.HTGeometry.measurable_laplaceKernel s)]
    calc
      (∑' j : ℕ, ENNReal.ofReal (w j) * ENNReal.ofReal (Real.exp (-(s*(j:ℝ))))) =
          ∑' j : ℕ, ENNReal.ofReal (w j * Real.exp (-(s*(j:ℝ)))) :=
        tsum_congr (fun j => (ENNReal.ofReal_mul (hw j)).symm)
      _ = _ := (ENNReal.ofReal_tsum_of_nonneg hn hd).symm
  have hm : Measurable (fun t : ℝ => Real.exp (-(s*t))) := by fun_prop
  have hi : Integrable (fun t : ℝ => Real.exp (-(s*t)))
      (Measure.sum (fun j : ℕ => ENNReal.ofReal (w j) • Measure.dirac (j : ℝ))) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _ => Real.exp_nonneg _))).mpr
    change Lap (Measure.sum (fun j : ℕ => ENNReal.ofReal (w j) • Measure.dirac (j : ℝ))) s < ∞
    rw [he]
    exact ENNReal.ofReal_lt_top
  exact ⟨hd, hi, he, by rw [he]; exact ENNReal.ofReal_ne_top⟩

private theorem sgd_degree_laplace {p : ℝ} (hp : 1 < p)
    {s : ℝ} (hs : 0 ≤ s) :
    Lap (liClockThetaDegreeLaw p) s =
      ENNReal.ofReal (liClockThetaGammaNormalizer (p * Real.exp (s/2)) /
        liClockThetaGammaNormalizer p) := by
  have hp0 : 0 < p := by linarith
  have hp' : 0 < p * Real.exp (s/2) := by positivity
  have hw := liClockThetaDegreeLaw_admission hp0
  have hsum := (liClockThetaGammaNormalizer_source hp').1.div_const
    (liClockThetaGammaNormalizer p)
  have hd : HasSum (fun j : ℕ => liClockThetaDegreeWeight p j * Real.exp (-(s*(j:ℝ))))
      (liClockThetaGammaNormalizer (p * Real.exp (s/2)) / liClockThetaGammaNormalizer p) := by
    apply hsum.congr_fun
    intro j
    rw [sgd_numerator_damping]
    simp only [liClockThetaDegreeWeight, div_eq_mul_inv, mul_inv_rev]
    ring
  have ha := sgd_atomic_laplace_admission (fun j => (hw.1 j).le) hw.2.1.summable hs
  rw [liClockThetaDegreeLaw, ha.2.2.1, hd.tsum_eq]

private theorem sgd_degree_laplace_log {p : ℝ} (hp : 1 < p)
    {s : ℝ} (hs : 0 ≤ s) :
    Real.log (Lap (liClockThetaDegreeLaw p) s).toReal =
      liClockThetaReciprocalLog (p * Real.exp (s/2)) - liClockThetaReciprocalLog p := by
  have hp0 : 0 < p := by linarith
  have hp' : 0 < p * Real.exp (s/2) := by positivity
  have hZ : 0 < liClockThetaGammaNormalizer p :=
    lt_trans zero_lt_one (liClockThetaGammaNormalizer_source hp0).2.2
  have hZ' : 0 < liClockThetaGammaNormalizer (p * Real.exp (s/2)) :=
    lt_trans zero_lt_one (liClockThetaGammaNormalizer_source hp').2.2
  rw [sgd_degree_laplace hp hs, ENNReal.toReal_ofReal (div_nonneg hZ'.le hZ.le)]
  exact Real.log_div hZ'.ne' hZ.ne'

private theorem sgd_degree_jump_laplace {p : ℝ} (hp : 1 < p)
    {s : ℝ} (hs : 0 ≤ s) :
    (∀ positive : Bool, Lap (liClockThetaDegreeJumpMeasure p positive) s ≠ ∞) ∧
      (Lap (liClockThetaDegreeJumpMeasure p true) s).toReal -
        (Lap (liClockThetaDegreeJumpMeasure p false) s).toReal =
          liClockThetaReciprocalLog (p * Real.exp (s/2)) := by
  have ha (positive : Bool) := sgd_atomic_laplace_admission
    (sgd_part_data hp positive).1 (sgd_part_data hp positive).2 hs
  have hr (positive : Bool) : (Lap (liClockThetaDegreeJumpMeasure p positive) s).toReal =
      ∑' j : ℕ, liClockThetaJumpPart p positive j * Real.exp (-(s*(j:ℝ))) := by
    rw [liClockThetaDegreeJumpMeasure, (ha positive).2.2.1,
      ENNReal.toReal_ofReal (tsum_nonneg (fun j =>
        mul_nonneg ((sgd_part_data hp positive).1 j) (Real.exp_nonneg _)))]
  refine ⟨fun positive => (ha positive).2.2.2, ?_⟩
  rw [hr true, hr false, ← (ha true).1.tsum_sub (ha false).1]
  calc
    (∑' j : ℕ, (liClockThetaJumpPart p true j * Real.exp (-(s*(j:ℝ))) -
        liClockThetaJumpPart p false j * Real.exp (-(s*(j:ℝ))))) =
        ∑' j : ℕ, liClockThetaLogJumpCoefficient (p*Real.exp (s/2)) j := by
      apply tsum_congr
      intro j
      rw [← sub_mul, sgd_parts_sub, sgd_ell_damping]
    _ = _ := (liClockThetaLogJumpCoefficient_admission (sgd_parameter_gt_one hp hs)).2.1.tsum_eq

end
end RHTower

/-!
Scratch C05 adapter for both full actual Gamma jump measures.
The bounded global test is admitted before transfer to the positive carriers.
-/

open MeasureTheory Set Filter RHTower
open scoped ENNReal
noncomputable section

namespace RHTower

local notation "Lap" => GaloisForLFunctions.HTGeometry.laplace

private def pgBoundedLaplaceTest (s t : ℝ) : ℝ :=
  Real.exp (-(s * max t 0))

private theorem pgBoundedLaplaceTest_measurable (s : ℝ) :
    Measurable (pgBoundedLaplaceTest s) := by
  exact Real.continuous_exp.measurable.comp
    ((measurable_const.mul (measurable_id.max measurable_const)).neg)

private theorem pgBoundedLaplaceTest_bound {s : ℝ} (hs : 0 ≤ s) (t : ℝ) :
    0 < pgBoundedLaplaceTest s t ∧ pgBoundedLaplaceTest s t ≤ 1 := by
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr ?_⟩
  exact neg_nonpos.mpr (mul_nonneg hs (le_max_right t 0))

private theorem pgJump_test_eq {p : ℝ} (hp : 1 < p) (positive : Bool) (s : ℝ) :
    pgBoundedLaplaceTest s =ᵐ[liClockThetaGammaJumpMeasure p positive]
      (fun t => Real.exp (-(s * t))) := by
  have hc := ((liClockThetaJumpMeasure_admission hp).2 positive).2.2.2.2.2.2
  filter_upwards [hc] with t ht
  unfold pgBoundedLaplaceTest
  rw [max_eq_left ht.le]

private theorem pgSigned_test_eq {p : ℝ} (hp : 1 < p) (s t : ℝ) :
    pgBoundedLaplaceTest s t * liClockThetaSignedGammaDensity p t =
      Real.exp (-(s * t)) * liClockThetaSignedGammaDensity p t := by
  by_cases ht : 0 < t
  · unfold pgBoundedLaplaceTest
    rw [max_eq_left ht.le]
  · have hz : liClockThetaSignedGammaDensity p t = 0 := by
      rw [liClockThetaSignedGammaDensity_eq_primitive hp t]
      exact Set.indicator_of_notMem ht _
    rw [hz, mul_zero, mul_zero]

private theorem pgJump_laplace_admission {p s : ℝ} (hp : 1 < p) (hs : 0 ≤ s)
    (positive : Bool) :
    Integrable (fun t => Real.exp (-(s * t))) (liClockThetaGammaJumpMeasure p positive) ∧
    Lap (liClockThetaGammaJumpMeasure p positive) s ≠ ∞ ∧
    (Lap (liClockThetaGammaJumpMeasure p positive) s).toReal =
      ∫ t, Real.exp (-(s * t)) ∂liClockThetaGammaJumpMeasure p positive := by
  have hb : ∃ C : ℝ, ∀ t, |pgBoundedLaplaceTest s t| ≤ C := by
    refine ⟨1, fun t => ?_⟩
    rw [abs_of_pos (pgBoundedLaplaceTest_bound hs t).1]
    exact (pgBoundedLaplaceTest_bound hs t).2
  have hd := (liClockThetaSignedGammaMeasure_admission hp).2
    (pgBoundedLaplaceTest s) (pgBoundedLaplaceTest_measurable s) hb
  have hiTest : Integrable (pgBoundedLaplaceTest s)
      (liClockThetaGammaJumpMeasure p positive) := by
    cases positive
    · exact hd.2.2.1
    · exact hd.2.1
  have hi := hiTest.congr (pgJump_test_eq hp positive s)
  have he : Lap (liClockThetaGammaJumpMeasure p positive) s =
      ENNReal.ofReal (∫ t, Real.exp (-(s * t))
        ∂liClockThetaGammaJumpMeasure p positive) := by
    exact (ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall fun t => (Real.exp_pos _).le)).symm
  have hn : 0 ≤ ∫ t, Real.exp (-(s * t))
      ∂liClockThetaGammaJumpMeasure p positive :=
    integral_nonneg (fun t => (Real.exp_pos _).le)
  refine ⟨hi, ?_, ?_⟩
  · rw [he]
    exact ENNReal.ofReal_ne_top
  · rw [he, ENNReal.toReal_ofReal hn]

private theorem pgJump_laplace_gap {p s : ℝ} (hp : 1 < p) (hs : 0 ≤ s) :
    Lap (liClockThetaGammaJumpMeasure p true) s ≠ ∞ ∧
    Lap (liClockThetaGammaJumpMeasure p false) s ≠ ∞ ∧
    (Lap (liClockThetaGammaJumpMeasure p true) s).toReal -
      (Lap (liClockThetaGammaJumpMeasure p false) s).toReal =
      liClockThetaReciprocalLog (p+s) := by
  have hpA := pgJump_laplace_admission hp hs true
  have hpB := pgJump_laplace_admission hp hs false
  have hb : ∃ C : ℝ, ∀ t, |pgBoundedLaplaceTest s t| ≤ C := by
    refine ⟨1, fun t => ?_⟩
    rw [abs_of_pos (pgBoundedLaplaceTest_bound hs t).1]
    exact (pgBoundedLaplaceTest_bound hs t).2
  have hd := (liClockThetaSignedGammaMeasure_admission hp).2
    (pgBoundedLaplaceTest s) (pgBoundedLaplaceTest_measurable s) hb
  have hσ : (fun t => pgBoundedLaplaceTest s t * liClockThetaSignedGammaDensity p t) =
      (fun t => Real.exp (-(s * t)) * liClockThetaSignedGammaDensity p t) := by
    funext t
    exact pgSigned_test_eq hp s t
  have ha := integral_congr_ae (pgJump_test_eq hp true s)
  have hb' := integral_congr_ae (pgJump_test_eq hp false s)
  have he := hd.2.2.2
  rw [hσ, (liClockThetaSignedGammaDensity_laplace hp hs).2.1, ha, hb'] at he
  exact ⟨hpA.2.1, hpB.2.1, by rw [hpA.2.2, hpB.2.2]; exact he.symm⟩

private theorem pgMixture_log_laplace {p s : ℝ} (hp : 1 < p) (hs : 0 ≤ s) :
    Real.log (Lap (liClockThetaGammaMixture p) s).toReal =
      liClockThetaReciprocalLog (p+s) - liClockThetaReciprocalLog p :=
  (liClockThetaSignedGammaDensity_laplace hp hs).2.2.1

end RHTower
end

/-!
Private C07/C08 adapter: adding an independent nonnegative probability law
gives an order coupling and increases every measurable, absolutely bounded,
monotone real test. Every single and product test is admitted before use of
pushforward identities or Bochner integral order. Actual signed-Gamma law
identifications and carrier proofs are deliberately left to their source owner.
-/

open MeasureTheory
open scoped MeasureTheory ENNReal

noncomputable section
namespace RHTower

private theorem poissonOrder_prod_probability (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (μ.prod ν) := by
  infer_instance

private theorem poissonOrder_map_fst (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (μ.prod ν).map Prod.fst = μ := by
  rw [Measure.map_fst_prod, measure_univ, one_smul]

private theorem poissonOrder_map_add (μ ν : Measure ℝ) :
    (μ.prod ν).map (fun xy => xy.1 + xy.2) = μ ∗ ν := by
  rfl

private theorem poissonOrder_ae_increment (μ ν : Measure ℝ)
    (hν : ∀ᵐ y ∂ν, 0 ≤ y) :
    ∀ᵐ xy ∂μ.prod ν, xy.1 ≤ xy.1 + xy.2 := by
  have hsecond : ∀ᵐ xy ∂μ.prod ν, 0 ≤ xy.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hν
  exact hsecond.mono fun _ hy => le_add_of_nonneg_right hy

private theorem poissonOrder_bounded_integrable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (h : α → ℝ) (hh : Measurable h)
    (hb : ∃ C : ℝ, ∀ x, |h x| ≤ C) : Integrable h μ := by
  obtain ⟨C, hC⟩ := hb
  refine (integrable_const C).mono' hh.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using hC x

private theorem poissonOrder_single_tests_integrable (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ℝ → ℝ) (hh : Measurable h) (hb : ∃ C : ℝ, ∀ x, |h x| ≤ C) :
    Integrable h μ ∧ Integrable h ν ∧ Integrable h (μ ∗ ν) := by
  exact ⟨poissonOrder_bounded_integrable μ h hh hb,
    poissonOrder_bounded_integrable ν h hh hb,
    poissonOrder_bounded_integrable (μ ∗ ν) h hh hb⟩

private theorem poissonOrder_product_tests_integrable (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ℝ → ℝ) (hh : Measurable h) (hb : ∃ C : ℝ, ∀ x, |h x| ≤ C) :
    Integrable (fun xy => h xy.1) (μ.prod ν) ∧
    Integrable (fun xy => h (xy.1 + xy.2)) (μ.prod ν) := by
  obtain ⟨C, hC⟩ := hb
  refine ⟨poissonOrder_bounded_integrable (μ.prod ν) (fun xy => h xy.1)
      (hh.comp measurable_fst) ⟨C, fun xy => hC xy.1⟩, ?_⟩
  exact poissonOrder_bounded_integrable (μ.prod ν) (fun xy => h (xy.1 + xy.2))
    (hh.comp (measurable_fst.add measurable_snd)) ⟨C, fun xy => hC (xy.1 + xy.2)⟩

private theorem poissonOrder_integral_fst (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ℝ → ℝ) (hh : Measurable h) (hb : ∃ C : ℝ, ∀ x, |h x| ≤ C) :
    (∫ x, h x ∂μ) = ∫ xy, h xy.1 ∂μ.prod ν := by
  have hi : Integrable h ((μ.prod ν).map Prod.fst) := by
    rw [poissonOrder_map_fst μ ν]
    exact (poissonOrder_single_tests_integrable μ ν h hh hb).1
  have hprod : Integrable (fun xy => h xy.1) (μ.prod ν) :=
    (poissonOrder_product_tests_integrable μ ν h hh hb).1
  have hmap := integral_map (μ := μ.prod ν) measurable_fst.aemeasurable
    hi.aestronglyMeasurable
  rw [poissonOrder_map_fst μ ν] at hmap
  exact hmap

private theorem poissonOrder_integral_add (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ℝ → ℝ) (hh : Measurable h) (hb : ∃ C : ℝ, ∀ x, |h x| ≤ C) :
    (∫ xy, h (xy.1 + xy.2) ∂μ.prod ν) = ∫ x, h x ∂(μ ∗ ν) := by
  have hi : Integrable h ((μ.prod ν).map (fun xy => xy.1 + xy.2)) := by
    rw [poissonOrder_map_add μ ν]
    exact (poissonOrder_single_tests_integrable μ ν h hh hb).2.2
  have hprod : Integrable (fun xy => h (xy.1 + xy.2)) (μ.prod ν) :=
    (poissonOrder_product_tests_integrable μ ν h hh hb).2
  have hmap := integral_map (μ := μ.prod ν) (φ := fun xy : ℝ × ℝ => xy.1 + xy.2)
    (measurable_fst.add measurable_snd).aemeasurable hi.aestronglyMeasurable
  rw [poissonOrder_map_add μ ν] at hmap
  exact hmap.symm

private theorem poissonOrder_product_coupling (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ∀ᵐ y ∂ν, 0 ≤ y) :
    IsProbabilityMeasure (μ.prod ν) ∧ (μ.prod ν).map Prod.fst = μ ∧
    (μ.prod ν).map (fun xy => xy.1 + xy.2) = μ ∗ ν ∧
    (∀ᵐ xy ∂μ.prod ν, xy.1 ≤ xy.1 + xy.2) := by
  exact ⟨poissonOrder_prod_probability μ ν, poissonOrder_map_fst μ ν,
    poissonOrder_map_add μ ν, poissonOrder_ae_increment μ ν hν⟩

private theorem poissonOrder_monotone_integral (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ∀ᵐ y ∂ν, 0 ≤ y) (h : ℝ → ℝ) (hh : Measurable h)
    (hmono : Monotone h) (hb : ∃ C : ℝ, ∀ x, |h x| ≤ C) :
    (∫ x, h x ∂μ) ≤ ∫ x, h x ∂(μ ∗ ν) := by
  obtain ⟨hfst, hadd⟩ := poissonOrder_product_tests_integrable μ ν h hh hb
  rw [poissonOrder_integral_fst μ ν h hh hb, ← poissonOrder_integral_add μ ν h hh hb]
  refine integral_mono_ae hfst hadd ?_
  exact (poissonOrder_ae_increment μ ν hν).mono fun _ hxy => hmono hxy

end RHTower
end

namespace RHTower
noncomputable section

local notation "CP" => GaloisForLFunctions.HTGeometry.compoundPoisson
local notation "CPow" => GaloisForLFunctions.HTGeometry.convPow

def liClockThetaDegreeJumpPoisson (p : ℝ) (positive : Bool) (time : ℝ) : Measure ℝ :=
  CP (time*liClockThetaJumpMass p positive)
    ((ENNReal.ofReal (liClockThetaJumpMass p positive))⁻¹ •
      liClockThetaDegreeJumpMeasure p positive)

def liClockThetaGammaJumpPoisson (p : ℝ) (positive : Bool) (time : ℝ) : Measure ℝ :=
  CP (time*liClockThetaJumpMass p positive)
    ((ENNReal.ofReal (liClockThetaJumpMass p positive))⁻¹ •
      liClockThetaGammaJumpMeasure p positive)

theorem liClockThetaJumpPoisson_admission {p : ℝ} (hp : 1 < p)
    (positive : Bool) {time : ℝ} (htime : 0 ≤ time) :
  IsProbabilityMeasure (liClockThetaDegreeJumpPoisson p positive time) ∧
  IsProbabilityMeasure (liClockThetaGammaJumpPoisson p positive time) ∧
  (∀ᵐ t ∂liClockThetaDegreeJumpPoisson p positive time, 0 ≤ t) ∧
  (∀ᵐ t ∂liClockThetaGammaJumpPoisson p positive time, 0 ≤ t) := by
  obtain ⟨hm, hd, hg, hdm, hgm, hdc, hgc⟩ :=
    (liClockThetaJumpMeasure_admission hp).2 positive
  haveI := hd
  haveI := hg
  haveI := isProbabilityMeasure_inv_ofReal_smul _ hm hdm
  haveI := isProbabilityMeasure_inv_ofReal_smul _ hm hgm
  have hD : ∀ᵐ t ∂(ENNReal.ofReal (liClockThetaJumpMass p positive))⁻¹ •
      liClockThetaDegreeJumpMeasure p positive, 0 ≤ t :=
    Measure.ae_smul_measure (hdc.mono fun _ ht => ht.le) _
  have hG : ∀ᵐ t ∂(ENNReal.ofReal (liClockThetaJumpMass p positive))⁻¹ •
      liClockThetaGammaJumpMeasure p positive, 0 ≤ t :=
    Measure.ae_smul_measure (hgc.mono fun _ ht => ht.le) _
  unfold liClockThetaDegreeJumpPoisson liClockThetaGammaJumpPoisson
  exact ⟨GaloisForLFunctions.HTGeometry.isProbabilityMeasure_compoundPoisson _
      (mul_nonneg htime hm.le) _,
    GaloisForLFunctions.HTGeometry.isProbabilityMeasure_compoundPoisson _
      (mul_nonneg htime hm.le) _,
    compoundPoisson_ae_nonneg _ hD _,
    compoundPoisson_ae_nonneg _ hG _⟩

end
end RHTower

namespace RHTower
noncomputable section

local notation "CP" => GaloisForLFunctions.HTGeometry.compoundPoisson
local notation "CPow" => GaloisForLFunctions.HTGeometry.convPow

theorem liClockThetaDegreeLaw_poisson_coupling {p : ℝ} (hp : 1 < p) :
  liClockThetaDegreeLaw p ∗ liClockThetaDegreeJumpPoisson p false 1 =
    liClockThetaDegreeJumpPoisson p true 1 := by
  have hp0 : 0 < p := by linarith
  have ha := liClockThetaDegreeLaw_admission hp0
  haveI := ha.2.2.1
  have hcarrier : ∀ᵐ t ∂liClockThetaDegreeLaw p, 0 ≤ t :=
    ha.2.2.2.2.mono fun t ht => by
      obtain ⟨j, rfl⟩ := ht
      exact Nat.cast_nonneg j
  have h := liClockThetaJumpMeasure_admission hp
  have hP := h.2 true
  have hM := h.2 false
  unfold liClockThetaDegreeJumpPoisson
  simp only [one_mul]
  apply sgc_normalized_cp_coupling _ _ _ hP.1 hM.1
    hP.2.2.2.1 hM.2.2.2.1 hcarrier
    (hP.2.2.2.2.2.1.mono fun _ ht => ht.le)
    (hM.2.2.2.2.2.1.mono fun _ ht => ht.le)
  intro s hs
  rw [(sgd_degree_jump_laplace hp hs).2, h.1]
  exact sgd_degree_laplace_log hp hs

theorem liClockThetaGammaMixture_poisson_coupling {p : ℝ} (hp : 1 < p) :
  liClockThetaGammaMixture p ∗ liClockThetaGammaJumpPoisson p false 1 =
    liClockThetaGammaJumpPoisson p true 1 := by
  have ha := liClockThetaGammaMixture_admission (by linarith : 0 < p)
  haveI := ha.1
  have h := liClockThetaJumpMeasure_admission hp
  have hP := h.2 true
  have hM := h.2 false
  unfold liClockThetaGammaJumpPoisson
  simp only [one_mul]
  apply sgc_normalized_cp_coupling _ _ _ hP.1 hM.1
    hP.2.2.2.2.1 hM.2.2.2.2.1 ha.2.1
    (hP.2.2.2.2.2.2.mono fun _ ht => ht.le)
    (hM.2.2.2.2.2.2.mono fun _ ht => ht.le)
  intro s hs
  rw [(pgJump_laplace_gap hp hs).2.2, h.1]
  exact pgMixture_log_laplace hp hs

theorem liClockThetaJumpPoisson_integer_coupling {p : ℝ} (hp : 1 < p)
    {m : ℕ} (hm : 1 ≤ m) :
  liClockThetaGammaJumpPoisson p true (m : ℝ) =
    liClockThetaGammaJumpPoisson p false (m : ℝ) ∗ CPow (liClockThetaGammaMixture p) m ∧
  liClockThetaDegreeJumpPoisson p true (m : ℝ) =
    liClockThetaDegreeJumpPoisson p false (m : ℝ) ∗ CPow (liClockThetaDegreeLaw p) m := by
  have _htime : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hp0 : 0 < p := by linarith
  haveI := (liClockThetaGammaMixture_admission hp0).1
  haveI := (liClockThetaDegreeLaw_admission hp0).2.2.1
  have h := liClockThetaJumpMeasure_admission hp
  have hP := h.2 true
  have hM := h.2 false
  haveI := isProbabilityMeasure_inv_ofReal_smul _ hP.1 hP.2.2.2.1
  haveI := isProbabilityMeasure_inv_ofReal_smul _ hM.1 hM.2.2.2.1
  haveI := isProbabilityMeasure_inv_ofReal_smul _ hP.1 hP.2.2.2.2.1
  haveI := isProbabilityMeasure_inv_ofReal_smul _ hM.1 hM.2.2.2.2.1
  constructor
  · have hu := liClockThetaGammaMixture_poisson_coupling hp
    simp only [liClockThetaGammaJumpPoisson, one_mul] at hu ⊢
    exact sgc_integer_cp_coupling _ _ _ hP.1.le hM.1.le hu m
  · have hu := liClockThetaDegreeLaw_poisson_coupling hp
    simp only [liClockThetaDegreeJumpPoisson, one_mul] at hu ⊢
    exact sgc_integer_cp_coupling _ _ _ hP.1.le hM.1.le hu m

theorem liClockThetaGammaJumpPoisson_product_coupling {p : ℝ} (hp : 1 < p)
    {m : ℕ} (hm : 1 ≤ m) :
  let μ : Measure (ℝ × ℝ) :=
    (liClockThetaGammaJumpPoisson p false (m : ℝ)).prod
      (CPow (liClockThetaGammaMixture p) m)
  IsProbabilityMeasure μ ∧
  μ.map Prod.fst = liClockThetaGammaJumpPoisson p false (m : ℝ) ∧
  μ.map (fun xy => xy.1+xy.2) = liClockThetaGammaJumpPoisson p true (m : ℝ) ∧
  (∀ᵐ xy ∂μ, xy.1 ≤ xy.1+xy.2) := by
  have ha := liClockThetaGammaMixture_admission (by linarith : 0 < p)
  haveI := ha.1
  haveI := GaloisForLFunctions.HTGeometry.isProbabilityMeasure_convPow
    (liClockThetaGammaMixture p) m
  haveI := (liClockThetaJumpPoisson_admission hp false (Nat.cast_nonneg m)).2.1
  dsimp only
  rw [(liClockThetaJumpPoisson_integer_coupling hp hm).1]
  exact poissonOrder_product_coupling _ _
    (sgc_convPow_nonnegative _ ha.2.1 m)

theorem liClockThetaJumpPoisson_monotone_integral {p : ℝ} (hp : 1 < p)
    {m : ℕ} (hm : 1 ≤ m) (h : ℝ → ℝ) (hh : Measurable h)
    (hmono : Monotone h) (hbound : ∃ C : ℝ, ∀ t, |h t| ≤ C) :
  (∫ t, h t ∂liClockThetaGammaJumpPoisson p false (m : ℝ)) ≤
    (∫ t, h t ∂liClockThetaGammaJumpPoisson p true (m : ℝ)) ∧
  (∫ t, h t ∂liClockThetaDegreeJumpPoisson p false (m : ℝ)) ≤
    (∫ t, h t ∂liClockThetaDegreeJumpPoisson p true (m : ℝ)) := by
  have hp0 : 0 < p := by linarith
  have hG := liClockThetaGammaMixture_admission hp0
  have hD := liClockThetaDegreeLaw_admission hp0
  haveI := hG.1
  haveI := hD.2.2.1
  haveI := GaloisForLFunctions.HTGeometry.isProbabilityMeasure_convPow
    (liClockThetaGammaMixture p) m
  haveI := GaloisForLFunctions.HTGeometry.isProbabilityMeasure_convPow
    (liClockThetaDegreeLaw p) m
  have hP := liClockThetaJumpPoisson_admission hp false (Nat.cast_nonneg m)
  haveI := hP.1
  haveI := hP.2.1
  have hDc : ∀ᵐ t ∂liClockThetaDegreeLaw p, 0 ≤ t :=
    hD.2.2.2.2.mono fun t ht => by
      obtain ⟨j, rfl⟩ := ht
      exact Nat.cast_nonneg j
  rw [(liClockThetaJumpPoisson_integer_coupling hp hm).1,
    (liClockThetaJumpPoisson_integer_coupling hp hm).2]
  exact ⟨poissonOrder_monotone_integral _ _
      (sgc_convPow_nonnegative _ hG.2.1 m) h hh hmono hbound,
    poissonOrder_monotone_integral _ _
      (sgc_convPow_nonnegative _ hDc m) h hh hmono hbound⟩

end
end RHTower

open scoped ENNReal NNReal
open MeasureTheory Set Filter GaloisForLFunctions.HTGeometry

private theorem hgt_nat_measure_sum (Q : Measure ℝ)
    (hQnat : ∀ᵐ x ∂Q, x ∈ Set.range (fun j : ℕ => (j : ℝ))) :
    Q = Measure.sum (fun j : ℕ => Q {(j : ℝ)} • Measure.dirac (j : ℝ)) := by
  have hset : Set.range (fun j : ℕ => (j : ℝ)) = ⋃ j : ℕ, {(j : ℝ)} := by
    ext x
    simp
  have hd : Pairwise (Function.onFun Disjoint (fun j : ℕ => ({(j : ℝ)} : Set ℝ))) := by
    intro i j hij
    apply Set.disjoint_singleton.mpr
    exact_mod_cast hij
  calc
    Q = Q.restrict (Set.range (fun j : ℕ => (j : ℝ))) :=
      (Measure.restrict_eq_self_of_ae_mem hQnat).symm
    _ = Measure.sum (fun j : ℕ => Q.restrict {(j : ℝ)}) := by
      rw [hset, Measure.restrict_iUnion hd (fun j => measurableSet_singleton (j : ℝ))]
    _ = _ := by simp_rw [Measure.restrict_singleton]

private theorem hgt_ae_conv_nonneg (μ ν : Measure ℝ) [SFinite ν]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (hν : ∀ᵐ x ∂ν, 0 ≤ x) :
    ∀ᵐ x ∂(μ ∗ ν), 0 ≤ x := by
  rw [Measure.conv, ae_map_iff (by fun_prop) (by measurability)]
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [hμ] with x hx
  filter_upwards [hν] with y hy
  exact add_nonneg hx hy

private theorem hgt_convPow_nonneg (Q : Measure ℝ) [SFinite Q]
    (hQnat : ∀ᵐ x ∂Q, x ∈ Set.range (fun j : ℕ => (j : ℝ))) (k : ℕ) :
    ∀ᵐ x ∂convPow Q k, 0 ≤ x := by
  have hQ : ∀ᵐ x ∂Q, 0 ≤ x := by
    filter_upwards [hQnat] with x hx
    obtain ⟨j, rfl⟩ := hx
    positivity
  induction k with
  | zero => simp [convPow]
  | succ k hk => exact hgt_ae_conv_nonneg Q (convPow Q k) hQ hk

private theorem hgt_negative_atom_zero (ν : Measure ℝ)
    (hν : ∀ᵐ x ∂ν, 0 ≤ x) {z : ℝ} (hz : z < 0) : ν {z} = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hν] with x hx
  simp only [Set.mem_singleton_iff]
  intro h
  subst x
  linarith

private theorem hgt_conv_atom (Q ν : Measure ℝ) [SFinite ν]
    (hQnat : ∀ᵐ x ∂Q, x ∈ Set.range (fun j : ℕ => (j : ℝ)))
    (hν : ∀ᵐ x ∂ν, 0 ≤ x) (m : ℕ) :
    (Q ∗ ν) {(m : ℝ)} =
      ∑ j ∈ Finset.range (m + 1), Q {(j : ℝ)} * ν {(m : ℝ) - (j : ℝ)} := by
  conv_lhs => rw [hgt_nat_measure_sum Q hQnat]
  rw [sum_conv, Measure.sum_apply _ (measurableSet_singleton _)]
  have he : ∀ j : ℕ, ((Q {(j : ℝ)} • Measure.dirac (j : ℝ)) ∗ ν) {(m : ℝ)} =
      Q {(j : ℝ)} * ν {(m : ℝ) - (j : ℝ)} := by
    intro j
    rw [Measure.conv_smul_left, Measure.smul_apply, Measure.dirac_conv,
      Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
    have hpre : (fun y : ℝ => (j : ℝ) + y) ⁻¹' {(m : ℝ)} = {(m : ℝ) - (j : ℝ)} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor <;> intro h <;> linarith
    rw [hpre]
    rfl
  simp_rw [he]
  apply tsum_eq_sum
  intro j hj
  have hmj : m < j := by
    simp only [Finset.mem_range] at hj
    omega
  have hmjR : (m : ℝ) < (j : ℝ) := by exact_mod_cast hmj
  have hz : (m : ℝ) - (j : ℝ) < 0 := by linarith
  rw [hgt_negative_atom_zero ν hν hz, mul_zero]

private theorem hgt_convPow_atom_zero (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQnat : ∀ᵐ x ∂Q, x ∈ Set.range (fun j : ℕ => (j : ℝ))) (k : ℕ) :
    (convPow Q k {0}).toReal = (Q {0}).toReal ^ k := by
  induction k with
  | zero => simp [convPow]
  | succ k hk =>
    haveI := isProbabilityMeasure_convPow Q k
    have he := hgt_conv_atom Q (convPow Q k) hQnat (hgt_convPow_nonneg Q hQnat k) 0
    norm_num at he
    rw [convPow, he]
    simp only [ENNReal.toReal_mul, hk, pow_succ]
    ring

private theorem hgt_convPow_atom_one_recurrence (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQnat : ∀ᵐ x ∂Q, x ∈ Set.range (fun j : ℕ => (j : ℝ))) (k : ℕ) :
    (convPow Q (k + 1) {1}).toReal =
      (Q {0}).toReal * (convPow Q k {1}).toReal +
      (Q {1}).toReal * (convPow Q k {0}).toReal := by
  haveI := isProbabilityMeasure_convPow Q k
  have he := hgt_conv_atom Q (convPow Q k) hQnat (hgt_convPow_nonneg Q hQnat k) 1
  norm_num [Finset.sum_range_succ] at he
  rw [convPow, he, ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul]

private theorem hgt_convPow_atom_two_recurrence (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQnat : ∀ᵐ x ∂Q, x ∈ Set.range (fun j : ℕ => (j : ℝ))) (k : ℕ) :
    (convPow Q (k + 1) {2}).toReal =
      (Q {0}).toReal * (convPow Q k {2}).toReal +
      (Q {1}).toReal * (convPow Q k {1}).toReal +
      (Q {2}).toReal * (convPow Q k {0}).toReal := by
  haveI := isProbabilityMeasure_convPow Q k
  have he := hgt_conv_atom Q (convPow Q k) hQnat (hgt_convPow_nonneg Q hQnat k) 2
  norm_num [Finset.sum_range_succ] at he
  rw [convPow, he, ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul]

private theorem hgt_convPow_atom_one (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQnat : ∀ᵐ x ∂Q, x ∈ Set.range (fun j : ℕ => (j : ℝ))) (k : ℕ) :
    (convPow Q (k + 1) {1}).toReal =
      (k + 1 : ℕ) * (Q {1}).toReal * (Q {0}).toReal ^ k := by
  induction k with
  | zero => simp [convPow]
  | succ k hk =>
    rw [hgt_convPow_atom_one_recurrence Q hQnat, hk, hgt_convPow_atom_zero Q hQnat]
    push_cast
    rw [pow_succ]
    ring

private theorem hgt_convPow_atom_two (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQnat : ∀ᵐ x ∂Q, x ∈ Set.range (fun j : ℕ => (j : ℝ))) (k : ℕ) :
    (convPow Q (k + 2) {2}).toReal =
      (k + 2 : ℕ) * (Q {2}).toReal * (Q {0}).toReal ^ (k + 1) +
      ((k + 2 : ℕ) : ℝ) * (k + 1 : ℕ) / 2 * (Q {1}).toReal ^ 2 * (Q {0}).toReal ^ k := by
  induction k with
  | zero =>
    rw [show 0 + 2 = (0 + 1) + 1 by rfl, hgt_convPow_atom_two_recurrence Q hQnat]
    norm_num [convPow]
    ring
  | succ k hk =>
    rw [show k + 1 + 2 = (k + 2) + 1 by omega, hgt_convPow_atom_two_recurrence Q hQnat,
      hk, show k + 2 = (k + 1) + 1 by omega, hgt_convPow_atom_one Q hQnat,
      hgt_convPow_atom_zero Q hQnat]
    push_cast
    simp only [pow_succ]
    ring

private theorem hgt_poisson_atom_real_tsum (lam : ℝ) (hlam : 0 ≤ lam)
    (Q : Measure ℝ) [IsProbabilityMeasure Q] (m : ℝ) :
    (compoundPoisson lam Q {m}).toReal =
      ∑' k : ℕ, (Real.exp (-lam) * lam ^ k / k.factorial) * (convPow Q k {m}).toReal := by
  haveI := isProbabilityMeasure_compoundPoisson lam hlam Q
  have hfull : compoundPoisson lam Q {m} ≠ ∞ := measure_ne_top _ _
  have hsumfull : (∑' k : ℕ,
      ENNReal.ofReal (Real.exp (-lam) * lam ^ k / k.factorial) * convPow Q k {m}) ≠ ∞ := by
    rw [← convPowMixture_singleton]
    exact hfull
  rw [compoundPoisson, convPowMixture_singleton,
    ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hsumfull)]
  apply tsum_congr
  intro k
  haveI := isProbabilityMeasure_convPow Q k
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

private theorem hgt_poisson_atom_summable (lam : ℝ) (hlam : 0 ≤ lam)
    (Q : Measure ℝ) [IsProbabilityMeasure Q] (m : ℝ) :
    Summable (fun k : ℕ =>
      (Real.exp (-lam) * lam ^ k / k.factorial) * (convPow Q k {m}).toReal) := by
  haveI := isProbabilityMeasure_compoundPoisson lam hlam Q
  have hfinite : (∑' k : ℕ, ENNReal.ofReal (Real.exp (-lam) * lam ^ k / k.factorial) *
      convPow Q k {m}) ≠ ∞ := by
    rw [← convPowMixture_singleton]
    exact measure_ne_top (compoundPoisson lam Q) {m}
  have hs := ENNReal.summable_toReal hfinite
  convert hs using 1
  funext k
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

private theorem hgt_poisson_power_series (lam a : ℝ) (ha : 0 ≤ a) :
    (∑' k : ℕ, Real.exp (-lam) * a ^ k / k.factorial) =
      Real.exp (-lam) * Real.exp a := by
  have h := congrArg ENNReal.toReal (tsum_ofReal_poisson_scaled lam a ha)
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)] at h
  have ht : ∀ k : ℕ, (ENNReal.ofReal (Real.exp (-lam) * a ^ k / k.factorial)).toReal =
      Real.exp (-lam) * a ^ k / k.factorial := fun k => ENNReal.toReal_ofReal (by positivity)
  simp_rw [ht] at h
  rw [ENNReal.toReal_ofReal (by positivity)] at h
  exact h

private theorem hgt_poisson_atom_zero (lam : ℝ) (hlam : 0 ≤ lam)
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQnat : ∀ᵐ x ∂Q, x ∈ Set.range (fun j : ℕ => (j : ℝ))) :
    (compoundPoisson lam Q {0}).toReal = Real.exp (-lam * (1 - (Q {0}).toReal)) := by
  rw [hgt_poisson_atom_real_tsum lam hlam Q]
  simp_rw [hgt_convPow_atom_zero Q hQnat]
  have he : ∀ k : ℕ, (Real.exp (-lam) * lam ^ k / k.factorial) * (Q {0}).toReal ^ k =
      Real.exp (-lam) * (lam * (Q {0}).toReal) ^ k / k.factorial := by
    intro k
    rw [mul_pow]
    ring
  simp_rw [he]
  rw [hgt_poisson_power_series lam _ (by positivity), ← Real.exp_add]
  congr 1
  ring

private theorem hgt_poisson_atom_one (lam : ℝ) (hlam : 0 ≤ lam)
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQnat : ∀ᵐ x ∂Q, x ∈ Set.range (fun j : ℕ => (j : ℝ))) :
    (compoundPoisson lam Q {1}).toReal =
      Real.exp (-lam * (1 - (Q {0}).toReal)) * (lam * (Q {1}).toReal) := by
  rw [hgt_poisson_atom_real_tsum lam hlam Q,
    (hgt_poisson_atom_summable lam hlam Q 1).tsum_eq_zero_add]
  have he : ∀ k : ℕ,
      (Real.exp (-lam) * lam ^ (k + 1) / (k + 1).factorial) *
        (convPow Q (k + 1) {1}).toReal =
      (lam * (Q {1}).toReal) *
        (Real.exp (-lam) * (lam * (Q {0}).toReal) ^ k / k.factorial) := by
    intro k
    rw [hgt_convPow_atom_one Q hQnat, Nat.factorial_succ, mul_pow, pow_succ]
    push_cast
    have hf : (k.factorial : ℝ) ≠ 0 := by positivity
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  have hz : (convPow Q 0 {1}).toReal = 0 := by norm_num [convPow]
  rw [hz, mul_zero, zero_add]
  simp_rw [he]
  rw [tsum_mul_left, hgt_poisson_power_series lam _ (by positivity), ← Real.exp_add]
  have harg : -lam + lam * (Q {0}).toReal = -lam * (1 - (Q {0}).toReal) := by ring
  rw [harg]
  ring

private theorem hgt_poisson_atom_two (lam : ℝ) (hlam : 0 ≤ lam)
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQnat : ∀ᵐ x ∂Q, x ∈ Set.range (fun j : ℕ => (j : ℝ))) :
    (compoundPoisson lam Q {2}).toReal =
      Real.exp (-lam * (1 - (Q {0}).toReal)) *
        (lam * (Q {2}).toReal + (lam * (Q {1}).toReal)^2 / 2) := by
  let f : ℕ → ℝ := fun k => Real.exp (-lam) * (lam * (Q {0}).toReal) ^ k / k.factorial
  have hfs : Summable f := by
    simp only [f, mul_div_assoc]
    exact (Real.summable_pow_div_factorial _).mul_left _
  have hfexp : ∑' k, f k = Real.exp (-lam * (1 - (Q {0}).toReal)) := by
    rw [hgt_poisson_power_series lam _ (by positivity), ← Real.exp_add]
    congr 1
    ring
  have he : ∀ k : ℕ,
      (Real.exp (-lam) * lam ^ (k + 2) / (k + 2).factorial) *
        (convPow Q (k + 2) {2}).toReal =
      (lam * (Q {2}).toReal) * f (k + 1) + (lam * (Q {1}).toReal)^2 / 2 * f k := by
    intro k
    rw [hgt_convPow_atom_two Q hQnat]
    simp only [f, Nat.factorial_succ, mul_pow, pow_succ]
    push_cast
    have hf : (k.factorial : ℝ) ≠ 0 := by positivity
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [hgt_poisson_atom_real_tsum lam hlam Q]
  have hs := (hgt_poisson_atom_summable lam hlam Q 2).sum_add_tsum_nat_add 2
  have hhead : ∑ k ∈ Finset.range 2,
      (Real.exp (-lam) * lam ^ k / k.factorial) * (convPow Q k {2}).toReal =
      (lam * (Q {2}).toReal) * f 0 := by
    norm_num [Finset.sum_range_succ, convPow, f]
    ring
  rw [← hs, hhead]
  simp_rw [he]
  have hfshift : Summable (fun k => f (k + 1)) := (summable_nat_add_iff 1).2 hfs
  rw [(hfshift.mul_left _).tsum_add (hfs.mul_left _), tsum_mul_left, tsum_mul_left]
  have hsplit := hfs.tsum_eq_zero_add
  calc
    (lam * (Q {2}).toReal) * f 0 +
        ((lam * (Q {2}).toReal) * (∑' k, f (k + 1)) +
          (lam * (Q {1}).toReal)^2 / 2 * (∑' k, f k)) =
      (lam * (Q {2}).toReal) * (f 0 + ∑' k, f (k + 1)) +
        (lam * (Q {1}).toReal)^2 / 2 * (∑' k, f k) := by ring
    _ = _ := by rw [← hsplit, hfexp]; ring

private theorem hgt_poisson_first_three_atoms
    (lam : ℝ) (hlam : 0 ≤ lam) (Q : Measure ℝ)
    (hQprob : IsProbabilityMeasure Q)
    (hQnat : ∀ᵐ x ∂Q, x ∈ Set.range (fun j : ℕ => (j : ℝ))) :
    let μ := compoundPoisson lam Q
    let q0 := (Q {0}).toReal
    let q1 := (Q {1}).toReal
    let q2 := (Q {2}).toReal
    (μ {0}).toReal = Real.exp (-lam * (1 - q0)) ∧
    0 < (μ {0}).toReal ∧
    (μ {1}).toReal / (μ {0}).toReal = lam * q1 ∧
    (μ {2}).toReal / (μ {0}).toReal = lam * q2 + (lam * q1)^2 / 2 := by
  letI := hQprob
  dsimp only
  have h0 := hgt_poisson_atom_zero lam hlam Q hQnat
  have h1 := hgt_poisson_atom_one lam hlam Q hQnat
  have h2 := hgt_poisson_atom_two lam hlam Q hQnat
  refine ⟨h0, ?_, ?_, ?_⟩
  · rw [h0]
    exact Real.exp_pos _
  · rw [h0, h1]
    exact mul_div_cancel_left₀ _ (Real.exp_ne_zero _)
  · rw [h0, h2]
    exact mul_div_cancel_left₀ _ (Real.exp_ne_zero _)

private theorem hgt_poisson_first_three_boundary
    (lam : ℝ) (hlam : 0 ≤ lam) (Q : Measure ℝ)
    (hQprob : IsProbabilityMeasure Q)
    (hQnat : ∀ᵐ x ∂Q, x ∈ Set.range (fun j : ℕ => (j : ℝ))) :
    let μ := compoundPoisson lam Q
    0 < (μ {0}).toReal ∧
    0 ≤ (μ {2}).toReal / (μ {0}).toReal -
      ((μ {1}).toReal / (μ {0}).toReal)^2 / 2 := by
  dsimp only
  obtain ⟨_, h0, h1, h2⟩ := hgt_poisson_first_three_atoms lam hlam Q hQprob hQnat
  refine ⟨h0, ?_⟩
  rw [h1, h2]
  have : 0 ≤ lam * (Q {2}).toReal := mul_nonneg hlam ENNReal.toReal_nonneg
  linarith

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RHTower

private theorem sgd_defect_atoms {p : ℝ} (hp : 0 < p) (j : ℕ) :
    liClockThetaDegreeLaw p {(j : ℝ)} ≠ ∞ ∧
    (liClockThetaDegreeLaw p {(j : ℝ)}).toReal = liClockThetaDegreeWeight p j ∧
    0 < (liClockThetaDegreeLaw p {(j : ℝ)}).toReal := by
  have h := liClockThetaDegreeLaw_admission hp
  rw [h.2.2.2.1 j]
  have hj := h.1 j
  rw [ENNReal.toReal_ofReal hj.le]
  exact ⟨ENNReal.ofReal_ne_top, rfl, hj⟩

private theorem sgd_defect_weight_ratio {p : ℝ} (hp : 0 < p) (j : ℕ) :
    liClockThetaDegreeWeight p j / liClockThetaDegreeWeight p 0 =
      thetaCuspNormalizedEvenMoment j / (((2*j).factorial : ℝ) * p^(2*j)) := by
  have hz : liClockThetaGammaNormalizer p ≠ 0 :=
    ne_of_gt (lt_trans zero_lt_one (liClockThetaGammaNormalizer_source hp).2.2)
  have hf : ((2*j).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2*j)
  simp only [liClockThetaDegreeWeight, thetaCuspNormalizedEvenMoment_zero,
    Nat.mul_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul, mul_one]
  field_simp [hp.ne', hz, hf]

private theorem sgd_degree_three_atom_defect {p : ℝ} (hp : 0 < p) :
    let a : ℕ → ℝ := fun j => (liClockThetaDegreeLaw p {(j : ℝ)}).toReal
    0 < a 0 ∧
      a 2 / a 0 - (a 1 / a 0)^2 / 2 = liClockThetaLogJumpCoefficient p 2 ∧
      liClockThetaLogJumpCoefficient p 2 < 0 := by
  dsimp only
  have hB := liClockThetaLogJumpCoefficient_first_two hp
  refine ⟨(sgd_defect_atoms hp 0).2.2, ?_, hB.2.2.2⟩
  rw [(sgd_defect_atoms hp 2).2.1, (sgd_defect_atoms hp 0).2.1,
    (sgd_defect_atoms hp 1).2.1, sgd_defect_weight_ratio hp 2,
    sgd_defect_weight_ratio hp 1, hB.2.1,
    normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment]
  norm_num
  field_simp [hp.ne']
  ring

end RHTower
end

namespace RHTower
noncomputable section

local notation "CP" => GaloisForLFunctions.HTGeometry.compoundPoisson

theorem liClockThetaDegreeLaw_not_ordinaryPoisson {p : ℝ} (hp : 0 < p)
    (lam : ℝ) (hlam : 0 ≤ lam) (Q : Measure ℝ)
    (hQprob : IsProbabilityMeasure Q)
    (hQnat : ∀ᵐ t ∂Q, t ∈ Set.range (fun j : ℕ => (j : ℝ))) :
  liClockThetaDegreeLaw p ≠ CP lam Q := by
  intro he
  have hD := sgd_degree_three_atom_defect hp
  have hP := hgt_poisson_first_three_boundary lam hlam Q hQprob hQnat
  dsimp only at hD hP
  rw [←he] at hP
  have hnonneg := hP.2
  linarith [hD.2.1, hD.2.2]

end
end RHTower

namespace RHTower
noncomputable section
local notation "CPow" => GaloisForLFunctions.HTGeometry.convPow

private theorem sgc_convPow_dirac_one (n : ℕ) :
    CPow (Measure.dirac (1 : ℝ)) n = Measure.dirac (n : ℝ) := by
  induction n with
  | zero => simp only [GaloisForLFunctions.HTGeometry.convPow, Nat.cast_zero]
  | succ n ih =>
    rw [GaloisForLFunctions.HTGeometry.convPow, ih, Measure.dirac_conv_dirac]
    congr 1
    push_cast
    ring

theorem liClockThetaDegreeLaw_isCompoundPoissonMixture {p : ℝ} (hp : 0 < p) :
  GaloisForLFunctions.HTGeometry.IsCompoundPoissonMixture (liClockThetaDegreeLaw p) := by
  refine ⟨fun j => ENNReal.ofReal (liClockThetaDegreeWeight p j),
    Measure.dirac (1 : ℝ), ?_, inferInstance, ?_⟩
  · intro j
    exact (ENNReal.ofReal_pos.mpr ((liClockThetaDegreeLaw_admission hp).1 j)).ne'
  · simp only [liClockThetaDegreeLaw, GaloisForLFunctions.HTGeometry.convPowMixture,
      sgc_convPow_dirac_one]

end
end RHTower
