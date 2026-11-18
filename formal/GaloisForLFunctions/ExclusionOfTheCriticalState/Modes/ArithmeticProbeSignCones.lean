import GaloisForLFunctions.ExclusionOfTheCriticalState.Modes.SparseProbeShiftReadings
import GaloisForLFunctions.BiScaleUncertainty.Observation.BoundedCoordinateSignCone
import GaloisForLFunctions.RHTower.CompleteHankelSignCone

/-!
# Sign and support from an arithmetic progression of filtered probe samples

Sampling at a+dn changes the moment coordinate to exp(du) and multiplies
the density by a positive weight. For d>0 the new coordinate remains
injective. Consequently its complete Hankel cone detects the sign of the
original filtered profile on the whole half-line. Linear filters on both
sides of an interval recover support in that interval.
-/

noncomputable section
open MeasureTheory Filter Set
open _root_.Polynomial
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations
open _root_.RHTower (CompleteHankelCone completeHankelCone_iff_momentFunctional_square_nonnegative)
local notation "μ" => volume.restrict (Iio (0:ℝ))

private theorem coordinate_term {φ f : ℝ → ℝ} (hm : Measurable φ)
    (hb : ∀ᵐ u ∂μ, |φ u| ≤ 1) (hf : Integrable f μ) (n : ℕ) :
    Integrable (fun u => φ u^n*f u) μ := by
  apply hf.bdd_mul (hm.pow_const n).aestronglyMeasurable
  filter_upwards [hb] with u hu
  simpa only [norm_pow,Real.norm_eq_abs] using pow_le_one₀ (abs_nonneg (φ u)) hu

private theorem exp_bound : ∀ᵐ u ∂μ, |Real.exp u| ≤ 1 := by
  filter_upwards [ae_restrict_mem measurableSet_Iio] with u hu
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (le_of_lt hu)

private theorem eval_weight_sum (P : Polynomial ℝ) (φ f : ℝ → ℝ) (u : ℝ) :
    P.eval (φ u)*f u = ∑ k ∈ P.support, P.coeff k*(φ u^k*f u) := by
  rw [eval_eq_sum,Polynomial.sum_def,Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => mul_assoc _ _ _

private theorem eval_weight_integrable {φ f : ℝ → ℝ}
    (hi : ∀ k : ℕ, Integrable (fun u => φ u^k*f u) μ) (P : Polynomial ℝ) :
    Integrable (fun u => P.eval (φ u)*f u) μ := by
  simp_rw [eval_weight_sum P φ f]
  exact integrable_finsetSum _ fun k _ => (hi k).const_mul _

private theorem coordinate_momentFunctional (s : ℕ → ℝ) {φ f : ℝ → ℝ}
    (hs : ∀ k, s k = ∫ u in Iio (0:ℝ), φ u^k*f u)
    (hi : ∀ k : ℕ, Integrable (fun u => φ u^k*f u) μ) (P : Polynomial ℝ) :
    _root_.HTGeometry.momentFunctional s P = ∫ u in Iio (0:ℝ), P.eval (φ u)*f u := by
  rw [_root_.HTGeometry.momentFunctional_eq_support_sum]
  simp_rw [eval_weight_sum P φ f]
  rw [integral_finsetSum _ fun k _ => (hi k).const_mul _]
  simp only [integral_const_mul,hs]

private def probeWeight (F : ℝ → ℝ) (a : ℕ) (u : ℝ) :=
  Real.exp u^a*(F u*Real.exp (5*u))

private theorem weight_integrable {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) (a : ℕ) :
    Integrable (probeWeight F a) μ :=
  coordinate_term Real.measurable_exp exp_bound
    (integrable_halfLineLaplace_of_domain hF (s := 5) (by norm_num)).integrableOn a

/-- A polynomial shift filter on the literal arithmetic samples multiplies their density by P(exp u). -/
theorem probeShiftReading_integral {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (P : Polynomial ℝ) (a : ℕ) : probeShiftReading P F a =
      ∫ u in Iio (0:ℝ), P.eval (Real.exp u)*(Real.exp u^a*(F u*Real.exp (5*u))) := by
  have hs (k : ℕ) : criticalProbeSample F (a+k) = ∫ u in Iio (0:ℝ), Real.exp u^k*probeWeight F a u := by
    rw [criticalProbeSample_eq_coordinate hF]
    apply integral_congr_ae
    filter_upwards [] with u
    rw [probeWeight,pow_add]; ring
  exact ( _root_.HTGeometry.momentFunctional_eq_support_sum (fun k => criticalProbeSample F (a+k)) P).symm.trans
    (coordinate_momentFunctional _ hs (coordinate_term Real.measurable_exp exp_bound (weight_integrable hF a)) P)

/-- Every positive-step progression of filtered samples detects exactly the sign of the filtered density. -/
theorem probeProgression_filteredCone {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (P : Polynomial ℝ) (a d : ℕ) (hd : 0<d) :
    CompleteHankelCone (fun n => probeShiftReading P F (a+d*n)) ↔
      ∀ᵐ u, 0 ≤ P.eval (Real.exp u)*F u := by
  let φ := fun u : ℝ => Real.exp ((d:ℝ)*u)
  let f := fun u : ℝ => P.eval (Real.exp u)*probeWeight F a u
  have hφ : MeasurableEmbedding φ := (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurableEmbedding
    (fun x y h => mul_left_cancel₀ (Nat.cast_ne_zero.mpr hd.ne') (Real.exp_injective h))
  have hb : ∀ᵐ u ∂μ, |φ u| ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with u hu
    rw [show φ u = Real.exp ((d:ℝ)*u) from rfl,abs_of_pos (Real.exp_pos _),Real.exp_le_one_iff]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (le_of_lt hu)
  have hfm : Measurable f := (P.continuous.measurable.comp Real.measurable_exp).mul
    ((Real.measurable_exp.pow_const _).mul (hF.meas.mul (Real.measurable_exp.comp (measurable_const.mul measurable_id))))
  have hf : Integrable f μ := eval_weight_integrable
    (coordinate_term Real.measurable_exp exp_bound (weight_integrable hF a)) P
  have hs (n : ℕ) : probeShiftReading P F (a+d*n) = ∫ u in Iio (0:ℝ), φ u^n*f u := by
    rw [probeShiftReading_integral hF]
    apply integral_congr_ae
    filter_upwards [] with u
    simp only [φ,f,probeWeight,Real.exp_nat_mul,pow_add,pow_mul]; ring
  rw [completeHankelCone_iff_momentFunctional_square_nonnegative]
  simp_rw [coordinate_momentFunctional _ hs (coordinate_term hφ.measurable hb hf),eval_pow]
  rw [BiScaleUncertainty.Observation.density_nonnegative_iff_coordinate_squares hφ hb hfm hf]
  have he (u : ℝ) : 0 ≤ f u ↔ 0 ≤ P.eval (Real.exp u)*F u := by
    have ht : 0<Real.exp u^a*Real.exp (5*u) := by positivity
    change 0 ≤ P.eval (Real.exp u)*(Real.exp u^a*(F u*Real.exp (5*u))) ↔ _
    rw [show P.eval (Real.exp u)*(Real.exp u^a*(F u*Real.exp (5*u))) =
      (P.eval (Real.exp u)*F u)*(Real.exp u^a*Real.exp (5*u)) by ring,
      mul_nonneg_iff_of_pos_right ht]
  constructor
  · intro h
    filter_upwards [(ae_restrict_iff' measurableSet_Iio).mp h] with u hu
    rcases lt_or_ge u 0 with hneg|hpos
    · exact (he u).1 (hu hneg)
    · rw [hF.support u hpos,mul_zero]
  · intro h
    exact (ae_restrict_of_ae h).mono fun u hu => (he u).2 hu

/-- A single positive-step progression recovers the almost-everywhere nonnegative cone of profiles. -/
theorem probeProgression_nonnegative_iff {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (a d : ℕ) (hd : 0<d) :
    CompleteHankelCone (fun n => criticalProbeSample F (a+d*n)) ↔ 0 ≤ᵐ[volume] F := by
  have reading (n : ℕ) : probeShiftReading (1 : Polynomial ℝ) F n = criticalProbeSample F n := by
    rw [probeShiftReading_integral hF, criticalProbeSample_eq_coordinate hF]
    simp only [eval_one, one_mul]
  simpa only [reading, eval_one, one_mul, Filter.EventuallyLE, Pi.zero_apply] using
    probeProgression_filteredCone hF (1 : Polynomial ℝ) a d hd

/-- Pointwise comparison of two profiles is equivalent to the complete Hankel order on one progression. -/
theorem probeProgression_order_iff {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) (a d : ℕ) (hd : 0<d) :
    CompleteHankelCone (fun n => criticalProbeSample G (a+d*n)-criticalProbeSample F (a+d*n)) ↔
      F ≤ᵐ[volume] G := by
  let H := fun u => G u-F u
  have hh : CriticalHalfLineEnergyDomain H := by
    simpa only [H,neg_one_mul,← sub_eq_add_neg] using hG.add_const_mul hF (-1)
  have hs (n : ℕ) : criticalProbeSample H n = criticalProbeSample G n-criticalProbeSample F n := by
    simp only [criticalProbeSample,H,sub_mul]
    exact integral_sub (integrable_halfLineLaplace_of_domain hG (s := 5+n) (by positivity))
      (integrable_halfLineLaplace_of_domain hF (s := 5+n) (by positivity))
  simpa only [hs,Filter.EventuallyLE,H,Pi.zero_apply,sub_nonneg] using probeProgression_nonnegative_iff hh a d hd

/-- The two affine filters around an interval detect confinement of the complete essential support. -/
theorem probeProgression_interval_support {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hpos : 0 ≤ᵐ[volume] F) (a d : ℕ) (hd : 0<d) (l r : ℝ) :
    (CompleteHankelCone (fun n => probeShiftReading (X-C l) F (a+d*n)) ∧
     CompleteHankelCone (fun n => probeShiftReading (C r-X) F (a+d*n))) ↔
     ∀ᵐ u, F u ≠ 0 → Real.exp u ∈ Icc l r := by
  rw [probeProgression_filteredCone hF _ a d hd,probeProgression_filteredCone hF _ a d hd]
  simp only [eval_sub,eval_X,eval_C]
  constructor
  · rintro ⟨hlo,hhi⟩
    filter_upwards [hpos,hlo,hhi] with u hu hl hr
    intro hn
    have hp : 0<F u := lt_of_le_of_ne hu (Ne.symm hn)
    exact ⟨sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hp).1 hl),
      sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hp).1 hr)⟩
  · intro h
    have hboth : ∀ᵐ u, 0 ≤ (Real.exp u-l)*F u ∧ 0 ≤ (r-Real.exp u)*F u := by
      filter_upwards [h,hpos] with u hu hF'
      by_cases hz : F u=0
      · simp only [hz,mul_zero,le_refl,and_self]
      · exact ⟨mul_nonneg (sub_nonneg.mpr (hu hz).1) hF',mul_nonneg (sub_nonneg.mpr (hu hz).2) hF'⟩
    exact ⟨hboth.mono fun _ h => h.1,hboth.mono fun _ h => h.2⟩

/-- Each sign violation has a finite negative quadratic witness on every positive-step progression. -/
theorem probeProgression_negative_witness {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (P : Polynomial ℝ) (h : ¬ ∀ᵐ u, 0 ≤ P.eval (Real.exp u)*F u) (a d : ℕ) (hd : 0<d) :
    ∃ n : ℕ, ∃ c : Fin n → ℝ, (∑ i, ∑ j, c i*c j*probeShiftReading P F (a+d*(i.val+j.val))) < 0 := by
  have hh := mt (probeProgression_filteredCone hF P a d hd).1 h
  simpa only [CompleteHankelCone,not_forall,not_le] using hh

#print axioms probeShiftReading_integral
#print axioms probeProgression_filteredCone
#print axioms probeProgression_nonnegative_iff
#print axioms probeProgression_order_iff
#print axioms probeProgression_interval_support
#print axioms probeProgression_negative_witness
end GaloisForLFunctions.ExclusionOfTheCriticalState
