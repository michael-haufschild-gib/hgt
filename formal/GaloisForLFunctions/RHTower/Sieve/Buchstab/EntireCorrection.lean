import GaloisForLFunctions.RHTower.Sieve.Buchstab.LaplaceIdentity
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Meromorphic continuation of the Buchstab Laplace integral

The factorial cell estimates control every exponentially weighted moment of
the error. Differentiation of the complex Laplace integral therefore gives
an entire correction. The uncentered transform has a single simple pole.
-/

namespace RHTower.Sieve.Buchstab
open Set MeasureTheory Filter Topology Complex
noncomputable section

private def correction (t : ℝ) := buchstab t-enclosureLimit

private theorem correction_measurable : Measurable correction :=
  measurable_buchstab.sub measurable_const

private def momentWeight (k : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  (-(t:ℂ))^k * (correction t:ℂ) * Complex.exp (-z*t)

private theorem momentWeight_measurable (k : ℕ) (z : ℂ) : Measurable (momentWeight k z) :=
  (((by fun_prop : Measurable fun t : ℝ => (-(t:ℂ))^k)).mul
    (Complex.continuous_ofReal.measurable.comp correction_measurable)).mul (by fun_prop)

private theorem momentWeight_norm (k : ℕ) (z : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖momentWeight k z t‖ = t^k * |correction t| * Real.exp (-z.re*t) := by
  simp [momentWeight,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ht,Complex.norm_exp,Complex.mul_re]

private theorem moment_majorant (k : ℕ) (a : ℝ) :
    IntegrableOn (fun t => t^k * |correction t| * Real.exp (a*t)) (Ioi (0:ℝ)) := by
  have hi := (integrable_buchstab_correction (a+1)).abs.const_mul (k.factorial:ℝ)
  have hm : AEStronglyMeasurable (fun t : ℝ => t^k * |correction t| * Real.exp (a*t))
      (volume.restrict (Ioi (0:ℝ))) := (((measurable_id.pow_const k).mul correction_measurable.abs).mul
    (by fun_prop : Measurable (fun t : ℝ => Real.exp (a*t)))).aestronglyMeasurable
  refine hi.mono' hm ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0:ℝ)))] with t ht
  have ht' : 0 ≤ t := le_of_lt ht
  have hs := NormedSpace.expSeries_div_hasSum_exp t
  have h := hs.summable.le_tsum k (fun j _ => div_nonneg (pow_nonneg ht' _) (Nat.cast_nonneg _))
  rw [hs.tsum_eq,← Real.exp_eq_exp_ℝ] at h
  have hk := (div_le_iff₀ (by positivity : 0 < (k.factorial:ℝ))).mp h
  change ‖t^k * |correction t| * Real.exp (a*t)‖ ≤ (k.factorial:ℝ)*|correction t*Real.exp ((a+1)*t)|
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ht' _) (abs_nonneg _))
    (Real.exp_pos _).le),abs_mul,abs_of_pos (Real.exp_pos _),add_mul,one_mul,Real.exp_add]
  calc
    _ ≤ (Real.exp t * k.factorial) * |correction t| * Real.exp (a*t) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk (abs_nonneg _)) (Real.exp_pos _).le
    _ = _ := by ring

private theorem momentWeight_integrable (k : ℕ) (z : ℂ) :
    IntegrableOn (momentWeight k z) (Ioi (0:ℝ)) := by
  refine (moment_majorant k (-z.re)).mono' (momentWeight_measurable k z).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0:ℝ)))] with t ht
  exact (momentWeight_norm k z (le_of_lt ht)).le

/-- Signed Laplace moments with the sign appropriate to complex differentiation. -/
def correctionMoment (k : ℕ) (z : ℂ) := ∫ t in Ioi (0:ℝ), momentWeight k z t

theorem correctionMoment_eq_integral (k : ℕ) (z : ℂ) :
    correctionMoment k z = ∫ t in Ioi (0:ℝ),
      (-(t:ℂ))^k * ((buchstab t - enclosureLimit : ℝ) : ℂ) * Complex.exp (-z*t) := rfl

/-- Every derivative is the next absolutely convergent moment, also in the left half-plane. -/
theorem hasDerivAt_correctionMoment (k : ℕ) (z : ℂ) :
    HasDerivAt (correctionMoment k) (correctionMoment (k+1) z) z := by
  let U := {w : ℂ | z.re-1 < w.re}
  have hU : U ∈ 𝓝 z := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show z.re-1 < z.re by linarith)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0:ℝ))) (F := momentWeight k) (F' := momentWeight (k+1))
    (bound := fun t => t^(k+1) * |correction t| * Real.exp ((1-z.re)*t)) hU
    (Eventually.of_forall fun w => (momentWeight_integrable k w).1) (momentWeight_integrable k z)
    (momentWeight_integrable (k+1) z).1 _ (moment_majorant (k+1) (1-z.re)) _).2
  · filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0:ℝ)))] with t ht w hw
    rw [momentWeight_norm _ _ (le_of_lt ht)]
    have h : z.re-1 < w.re := hw
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (by linarith) (le_of_lt ht)))
      (mul_nonneg (pow_nonneg (le_of_lt ht) _) (abs_nonneg _))
  · filter_upwards with t w _
    have hd := (((hasDerivAt_id w).neg.mul_const (t:ℂ)).cexp).const_mul
      ((-(t:ℂ))^k * (correction t:ℂ))
    exact hd.congr_deriv (by dsimp [momentWeight]; rw [pow_succ]; ring)

/-- The zero-th signed moment is entire, with no restriction on the transform variable. -/
theorem correctionMoment_entire (k : ℕ) : Differentiable ℂ (correctionMoment k) :=
  fun z => (hasDerivAt_correctionMoment k z).differentiableAt

/-- The Taylor data everywhere are the literal weighted moments of the real profile. -/
theorem iteratedDeriv_correction (k : ℕ) : iteratedDeriv k (correctionMoment 0) = correctionMoment k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ,ih]
    exact funext fun z => (hasDerivAt_correctionMoment k z).deriv

theorem correctionMoment_zero : correctionMoment 0 0 = (enclosureLimit:ℂ)-1 := by
  simp only [correctionMoment,momentWeight,pow_zero,one_mul,neg_zero,zero_mul,Complex.exp_zero,mul_one]
  rw [integral_complex_ofReal]
  simpa [correction] using congrArg Complex.ofReal integral_buchstab_correction

/-- Meromorphic continuation of the uncentered transform with its sole polar term exposed. -/
def continuedMass (z : ℂ) := (enclosureLimit:ℂ)/z + correctionMoment 0 z

theorem continuedMass_differentiableAt (z : {w : ℂ // w ≠ 0}) : DifferentiableAt ℂ continuedMass z.val :=
  (((hasDerivAt_const z.val (enclosureLimit:ℂ)).fun_div (hasDerivAt_id z.val) z.property).add
    (hasDerivAt_correctionMoment 0 z.val)).differentiableAt

/-- Agreement with the original complex Laplace integral on its half-plane of convergence. -/
theorem continuedMass_eq_integral (z : {w : ℂ // 0 < w.re}) :
    continuedMass z = ∫ t in Ioi (0:ℝ), (buchstab t:ℂ)*Complex.exp (-z.val*t) := by
  have hz : (-z.val).re < 0 := neg_lt_zero.mpr z.property
  have hi := (integrableOn_exp_mul_complex_Ioi hz 0).const_mul (enclosureLimit:ℂ)
  have he : (∫ t in Ioi (0:ℝ), (enclosureLimit:ℂ)*Complex.exp (-z.val*t)) = (enclosureLimit:ℂ)/z.val := by
    rw [integral_const_mul,integral_exp_mul_complex_Ioi hz 0]
    simp [div_eq_mul_inv]
  rw [continuedMass,← he,correctionMoment,← integral_add hi (momentWeight_integrable 0 z)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp [momentWeight,correction,sub_mul]

/-- Complex residue at zero in every direction. -/
theorem tendsto_continuedMass_residue :
    Tendsto (fun z : ℂ => z*continuedMass z) (𝓝[≠] 0) (𝓝 (enclosureLimit:ℂ)) := by
  have h : Tendsto (fun z : ℂ => (enclosureLimit:ℂ)+z*correctionMoment 0 z) (𝓝 0)
      (𝓝 ((enclosureLimit:ℂ)+0*correctionMoment 0 0)) :=
    tendsto_const_nhds.add (tendsto_id.mul (correctionMoment_entire 0 0).continuousAt.tendsto)
  rw [zero_mul,add_zero] at h
  refine (h.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz' : z ≠ 0 := hz
  dsimp [continuedMass]
  field_simp [hz']

/-- The complex finite part is independent of the direction of approach. -/
theorem tendsto_continuedMass_finitePart :
    Tendsto (fun z : ℂ => continuedMass z-(enclosureLimit:ℂ)/z) (𝓝 0) (𝓝 ((enclosureLimit:ℂ)-1)) := by
  simpa only [continuedMass,add_sub_cancel_left,correctionMoment_zero] using
    (correctionMoment_entire 0 0).continuousAt.tendsto

#print axioms hasDerivAt_correctionMoment
#print axioms iteratedDeriv_correction
#print axioms continuedMass_eq_integral
#print axioms tendsto_continuedMass_residue
#print axioms tendsto_continuedMass_finitePart
end
end RHTower.Sieve.Buchstab
