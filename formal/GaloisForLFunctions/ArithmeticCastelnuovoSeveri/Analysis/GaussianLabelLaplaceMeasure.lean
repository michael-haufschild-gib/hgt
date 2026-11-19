import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Analysis.GaussianLabelAsymptotic
import GaloisForLFunctions.HTGeometry.BernsteinWidder

/-!
# A Bernstein measure for the normalized Gaussian label loss

Removing the pair coherence and its square-root variance prefactor turns
the missing binary label entropy into a Laplace transform in the variance.
Its finite representing measure has mass 4π. It is the squared-distance
pushforward of the log-odds kernel, so it gives no mass to zero and every
alternating finite difference is strictly positive.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Real Set
open scoped Topology ENNReal
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells.NoisyPair

private def oddsMeasure : Measure ℝ := volume.withDensity fun z => ENNReal.ofReal (oddsKernel z)

private theorem odds_mass : oddsMeasure univ=ENNReal.ofReal (4*π) := by
  rw [oddsMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal oddsKernel_integrable (ae_of_all _ fun z => (oddsKernel_pos z).le),
    oddsKernel_mass]

private instance oddsFinite : IsFiniteMeasure oddsMeasure := ⟨odds_mass.trans_lt ENNReal.ofReal_lt_top⟩

private def oddsRate (h d z : ℝ) := (z-h)^2/(2*d^2)

private theorem oddsRate_measurable (h d : ℝ) : Measurable (oddsRate h d) := by
  unfold oddsRate
  fun_prop

/-- The rates mixed by the binary label at log prior odds h and gap d. -/
def lossMeasure (h d : ℝ) : Measure ℝ := oddsMeasure.map (oddsRate h d)

instance lossMeasure_finite (h d : ℝ) : IsFiniteMeasure (lossMeasure h d) := by
  unfold lossMeasure
  infer_instance

theorem lossMeasure_mass (h d : ℝ) : lossMeasure h d univ=ENNReal.ofReal (4*π) := by
  rw [lossMeasure,Measure.map_apply (oddsRate_measurable _ _) MeasurableSet.univ,preimage_univ,odds_mass]

private theorem rate_support (h d : ℝ) : lossMeasure h d (Ici (0:ℝ))ᶜ=0 := by
  rw [lossMeasure,Measure.map_apply (oddsRate_measurable _ _) measurableSet_Ici.compl]
  have e : oddsRate h d ⁻¹' (Ici (0:ℝ))ᶜ=∅ := by
    ext z
    simp only [mem_preimage,mem_compl_iff,mem_Ici,mem_empty_iff_false,iff_false,not_not]
    exact div_nonneg (sq_nonneg _) (by positivity)
  rw [e,measure_empty]

/-- Distinct Gaussian means give a mixing measure supported on strictly
positive rates in the almost-everywhere sense. -/
theorem lossMeasure_positive_rates (h : ℝ) (d : {u : ℝ // u≠0}) :
    ∀ᵐ r ∂lossMeasure h d.val, 0<r := by
  apply (ae_map_iff (oddsRate_measurable _ _).aemeasurable measurableSet_Ioi).mpr
  have ac : oddsMeasure≪volume := withDensity_absolutelyContinuous _ _
  filter_upwards [ac.ae_le (Measure.ae_ne volume h)] with z hz
  exact div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hz)) (mul_pos (by norm_num) (sq_pos_of_ne_zero d.property))

private theorem laplace_integral (h d t : ℝ) : HTGeometry.finiteRealLaplace (lossMeasure h d) t =
    ∫ z, oddsKernel z*exp (-t*(z-h)^2/(2*d^2)) := by
  rw [HTGeometry.finiteRealLaplace,lossMeasure,integral_map (oddsRate_measurable _ _).aemeasurable (by fun_prop)]
  have hm : Measurable (fun z : ℝ => ENNReal.ofReal (oddsKernel z)) :=
    ENNReal.measurable_ofReal.comp oddsKernel_cont.measurable
  rw [oddsMeasure,integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all volume fun _ => ENNReal.ofReal_lt_top) (fun x : ℝ => exp (-t*oddsRate h d x))]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    change (ENNReal.ofReal (oddsKernel z)).toReal • exp (-t*oddsRate h d z) =
      oddsKernel z*exp (-t*(z-h)^2/(2*d^2))
    rw [ENNReal.toReal_ofReal (oddsKernel_pos z).le,smul_eq_mul,
      show -t*oddsRate h d z = -t*(z-h)^2/(2*d^2) by unfold oddsRate; ring]

/-- Conditional entropy calibrated by its explicit density and separation
factors. The formal variance argument lies on the positive half-line. -/
def calibratedLoss (u v a b t : ℝ) : ℝ :=
  ((labelEntropy u v-labelInformation u v a b (log t))*(sqrt (2*π)*|b-a|))/
    (sqrt (lengthRatio u v*lengthRatio v u)*overlap a b (log t)*sqrt t)

theorem calibrated_laplace (u v : ℝ) (p : {p : ℝ × ℝ // p.1≠p.2}) :
    EqOn (calibratedLoss u v p.val.1 p.val.2)
      (HTGeometry.finiteRealLaplace (lossMeasure (log (lengthRatio v u)-log (lengthRatio u v)) (p.val.2-p.val.1))) (Ioi 0) := by
  rintro t (ht : 0<t)
  rcases p with ⟨⟨a,b⟩,hab⟩
  change calibratedLoss u v a b t=HTGeometry.finiteRealLaplace _ t
  rw [calibratedLoss,exact_boundary_layer _ _ _ _ _ hab,laplace_integral,exp_log ht]
  have h1 := (sqrt_pos.mpr (mul_pos (lengthRatio_pos u v) (lengthRatio_pos v u))).ne'
  have h2 := (sqrt_pos.mpr (by positivity : (0:ℝ)<2*π)).ne'
  have h3 := abs_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hab))
  have h4 := (show 0<overlap a b (log t) from exp_pos _).ne'
  field_simp [h1,h2,h3,h4,(sqrt_pos.mpr ht).ne']

/-- Complete monotonicity and continuity hold for the actual calibrated
conditional entropy at every positive variance. -/
theorem calibrated_complete_monotonicity (u v : ℝ) (p : {p : ℝ × ℝ // p.1≠p.2}) :
    HTGeometry.CompletelyMonotoneOn (calibratedLoss u v p.val.1 p.val.2) :=
  (HTGeometry.completelyMonotoneOn_finiteRealLaplace _ (rate_support _ _)).congr_Ioi
    (calibrated_laplace u v p).symm

/-- The spectral representation makes every equally spaced signed
difference strictly positive, including the zeroth difference. -/
theorem strict_laplace_difference (h : ℝ) (d : {u : ℝ // u≠0}) (k : ℕ) (t delta : {u : ℝ // 0<u}) :
    0<(-1:ℝ)^k*(fwdDiff delta.val)^[k] (HTGeometry.finiteRealLaplace (lossMeasure h d.val)) t.val := by
  let μ := lossMeasure h d.val
  let F := fun r : ℝ => exp (-t.val*r)*(exp (-delta.val*r)-1)^k
  have hi : Integrable F μ := HTGeometry.integrable_finiteRealLaplace_differenceKernel μ (rate_support _ _) t.property delta.property k
  rw [HTGeometry.fwdDiff_iter_finiteRealLaplace _ (rate_support _ _) delta.property _ t.property,← integral_const_mul]
  change 0<∫ r, (-1:ℝ)^k*F r ∂μ
  have pos : ∀ᵐ r ∂μ, 0<(-1:ℝ)^k*F r := by
    filter_upwards [lossMeasure_positive_rates h d] with r hr
    have he : exp (-delta.val*r)<1 := exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr delta.property) hr)
    have e : (-1:ℝ)^k*(exp (-delta.val*r)-1)^k=(1-exp (-delta.val*r))^k := by rw [← mul_pow]; congr 1; ring
    rw [show (-1:ℝ)^k*F r=exp (-t.val*r)*((-1)^k*(exp (-delta.val*r)-1)^k) by unfold F; ring,e]
    exact mul_pos (exp_pos _) (pow_pos (sub_pos.mpr he) _)
  haveI : NeZero μ := ⟨fun hz => by
    have hm := lossMeasure_mass h d.val
    change μ univ=_ at hm
    rw [hz,Measure.coe_zero,Pi.zero_apply] at hm
    exact (ENNReal.ofReal_pos.mpr (by positivity : (0:ℝ)<4*π)).ne' hm.symm⟩
  refine lt_of_le_of_ne (integral_nonneg_of_ae (pos.mono fun _ hx => hx.le)) ?_
  intro hz
  have zero := (integral_eq_zero_iff_of_nonneg_ae (pos.mono fun _ hx => hx.le) (hi.const_mul _)).mp hz.symm
  obtain ⟨r,hr,hr'⟩ := (pos.and zero).exists
  exact hr.ne' hr'

/-- Any order of variance differences of the measured normalized entropy
has the strict alternating sign. -/
theorem calibrated_strict_difference (u v : ℝ) (p : {p : ℝ × ℝ // p.1≠p.2})
    (k : ℕ) (t delta : {u : ℝ // 0<u}) :
    0<(-1:ℝ)^k*(fwdDiff delta.val)^[k] (calibratedLoss u v p.val.1 p.val.2) t.val := by
  let d : {u : ℝ // u≠0} := ⟨p.val.2-p.val.1,sub_ne_zero.mpr (Ne.symm p.property)⟩
  let h := log (lengthRatio v u)-log (lengthRatio u v)
  have he : (fwdDiff delta.val)^[k] (calibratedLoss u v p.val.1 p.val.2) t.val =
      (fwdDiff delta.val)^[k] (HTGeometry.finiteRealLaplace (lossMeasure h d.val)) t.val := by
    rw [fwdDiff_iter_eq_sum_shift,fwdDiff_iter_eq_sum_shift]
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    exact calibrated_laplace u v p (add_pos_of_pos_of_nonneg t.property (nsmul_nonneg delta.property.le j))
  rw [he]
  exact strict_laplace_difference h d k t delta

#print axioms lossMeasure_mass
#print axioms lossMeasure_positive_rates
#print axioms calibrated_laplace
#print axioms calibrated_complete_monotonicity
#print axioms strict_laplace_difference
#print axioms calibrated_strict_difference
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells.NoisyPair
