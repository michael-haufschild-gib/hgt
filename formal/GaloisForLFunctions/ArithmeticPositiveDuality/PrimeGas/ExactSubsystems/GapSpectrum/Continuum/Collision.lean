import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.Continuum.GapLimit
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.CriticalLines
import GaloisForLFunctions.RHTower.EvenSectorSpectralConsistency

/-! # The discrete collision correction to the continuous gap law -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open MeasureTheory Set Filter Topology

theorem primitive_frequency_injective :
    Function.Injective (fun d : ReducedDirection => gapFrequency d.val) := by
  intro d e he
  obtain ⟨k,hk⟩ := (gapFrequency_fiber e.property d.val).mp he
  let E := _root_.RHTower.thetaCuspPrimitiveRayIndexEquivPositivePair
  have heq : E (d,1) = E (e,k) := by
    change (d.val.1*1,d.val.2*1) = (e.val.1*k,e.val.2*k)
    simpa only [mul_one,Prod.eta] using hk
  exact congrArg Prod.fst (E.injective heq)

private theorem gapLaw_direction {x : ℝ} (hx : 1/2 < x) (u : ℝ) :
    (sampledGapLaw x u hx : Measure ℝ) =
      Measure.map (fun d : ReducedDirection => u*gapFrequency d.val) (directionLaw x hx : Measure ReducedDirection) := by
  let A := (scaleLaw x (by linarith) : Measure ℕ+)
  let B := (directionLaw x hx : Measure ReducedDirection)
  let G := fun d : ReducedDirection => u*gapFrequency d.val
  let E := fun p : ℕ+ × ReducedDirection => (p.2.val.1*p.1,p.2.val.2*p.1)
  have hs : (fun q : ℕ+ × ℕ+ => u*gapFrequency q) ∘ E = G ∘ Prod.snd := by
    funext p
    exact congrArg (u*·) (gapFrequency_scale p.2.val.1 p.2.val.2 p.1)
  change Measure.map _ (gibbsPairLaw x hx : Measure (ℕ+ × ℕ+)) = B.map G
  have he : Measure.map E (A.prod B) = _ := primitive_product_samples hx
  rw [← he,Measure.map_map Measurable.of_discrete Measurable.of_discrete,hs,
    ← Measure.map_map Measurable.of_discrete measurable_snd,Measure.map_snd_prod,measure_univ,one_smul]

/-- The probability of a measured line is precisely its Bohr coefficient, at every nonzero scaling. -/
theorem sampledGapLaw_line {x u : ℝ} (hx : 1/2 < x) (hu : u ≠ 0) (d : ReducedDirection) :
    (sampledGapLaw x u hx : Measure ℝ) {u*gapFrequency d.val} =
      ENNReal.ofReal (overlapCoefficient x (gapFrequency d.val)).re := by
  have he : (fun e : ReducedDirection => u*gapFrequency e.val) ⁻¹' {u*gapFrequency d.val} = {d} := by
    ext e
    change u*gapFrequency e.val = u*gapFrequency d.val ↔ e = d
    rw [mul_right_inj' hu]
    exact primitive_frequency_injective.eq_iff
  rw [gapLaw_direction hx,Measure.map_apply Measurable.of_discrete (measurableSet_singleton _),he,directionLaw_atom]

theorem sampledGapLaw_zero {x u : ℝ} (hx : 1/2 < x) (hu : u ≠ 0) :
    (sampledGapLaw x u hx : Measure ℝ).real {0} = (overlapCoefficient x 0).re := by
  let d : ReducedDirection := ⟨(1,1),PNat.coprime_coe.mp (by simp)⟩
  have h0 : gapFrequency d.val = 0 := by simp [d,gapFrequency]
  have he := sampledGapLaw_line hx hu d
  rw [h0,mul_zero] at he
  obtain ⟨r,hr,heq⟩ := primitive_line_positive hx d
  rw [h0] at heq
  rw [measureReal_def,he,← heq,Complex.ofReal_re,ENNReal.toReal_ofReal hr.le]

/-- Exchanging the two Gibbs labels reflects their measured energy gap. -/
theorem sampledGapLaw_map_neg {x : ℝ} (hx : 1/2 < x) (u : ℝ) :
    (sampledGapLaw x u hx : Measure ℝ).map Neg.neg = (sampledGapLaw x u hx : Measure ℝ) := by
  have hr (t : ℝ) : (charFun (sampledGapLaw x u hx : Measure ℝ) t).im = 0 := by
    rw [charFun_sampledGapLaw hx u t,← Complex.ofReal_pow,Complex.ofReal_im]
  simpa only [neg_one_mul] using _root_.RHTower.EvenSector.map_neg_eq_of_charFun_im hr

private theorem symmetric_cumulative_zero (P : ProbabilityMeasure ℝ) (hr : ∀ t, (charFun (P:Measure ℝ) t).im = 0) :
    (P:Measure ℝ).real (Iic 0) = (1+(P:Measure ℝ).real {0})/2 := by
  let μ : Measure ℝ := P
  have href : μ.map Neg.neg = μ := by
    simpa only [neg_one_mul] using _root_.RHTower.EvenSector.map_neg_eq_of_charFun_im hr
  have hset : (Neg.neg : ℝ → ℝ) ⁻¹' Iio 0 = Ioi 0 := by ext t; simp
  have he := congrArg (fun m : Measure ℝ => m (Iio 0)) href
  change (μ.map Neg.neg) (Iio 0) = μ (Iio 0) at he
  rw [Measure.map_apply measurable_neg measurableSet_Iio,hset] at he
  have hside : μ.real (Ioi 0) = μ.real (Iio 0) := congrArg ENNReal.toReal he
  have hp := measureReal_add_measureReal_compl (μ := μ) (s := Iic 0) measurableSet_Iic
  have ht : μ.real (Iic 0) + μ.real (Ioi 0) = 1 := by simpa only [compl_Iic,measureReal_def,measure_univ,ENNReal.toReal_one] using hp
  have hd : Disjoint (Iio (0:ℝ)) {0} := by simp
  have ha := measureReal_union (μ := μ) hd (measurableSet_singleton 0)
  rw [Iio_union_right] at ha
  change μ.real (Iic 0) = (1+μ.real {0})/2
  linarith only [hside,ht,ha]

/-- Swapping the two samples gives equal probabilities on the two open half-lines.
The closed half-line retains half of the collision probability above its continuous limit. -/
theorem sampled_cumulative_zero {x u : ℝ} (hx : 1/2 < x) (hu : u ≠ 0) :
    (sampledGapLaw x u hx : Measure ℝ).real (Iic 0) = (1+(overlapCoefficient x 0).re)/2 := by
  rw [symmetric_cumulative_zero (sampledGapLaw x u hx) (fun t => by
    rw [charFun_sampledGapLaw hx u t,← Complex.ofReal_pow,Complex.ofReal_im]),sampledGapLaw_zero hx hu]

theorem laplace_cumulative_zero :
    (_root_.RHTower.mobiusCriticalLaplaceGapProbabilityMeasure : Measure ℝ).real (Iic 0) = 1/2 := by
  rw [symmetric_cumulative_zero _ (fun t => by
    rw [_root_.RHTower.charFun_mobiusCriticalLaplaceGapProbabilityMeasure,← Complex.ofReal_inv,Complex.ofReal_im])]
  have hz : (_root_.RHTower.mobiusCriticalLaplaceGapProbabilityMeasure : Measure ℝ) {0} = 0 := by
    change (volume.withDensity _) {0} = 0
    simp [withDensity_apply _ (measurableSet_singleton (0:ℝ))]
  simp only [measureReal_def,hz,ENNReal.toReal_zero,add_zero]

/-- Exact quadratic discrepancy from the limiting Laplace distribution function at zero. -/
theorem cumulative_zero_quadratic_limit :
    Tendsto (fun h : Set.Ioi (0:ℝ) =>
      ((criticalGapLaw h : Measure ℝ).real (Iic 0) -
        (_root_.RHTower.mobiusCriticalLaplaceGapProbabilityMeasure : Measure ℝ).real (Iic 0))/h.val^2)
      criticalApproach (𝓝 ((riemannZeta 2).re/2)) := by
  have hv : Tendsto (Subtype.val : Set.Ioi (0:ℝ) → ℝ) criticalApproach (𝓝[>] 0) := tendsto_comap
  have hl := ((Complex.continuous_re.tendsto _).comp (constant_line_quadratic_limit.comp hv)).div_const 2
  apply hl.congr
  intro h
  have htemp : (1+h.val)/2 = excessDamping h := by unfold excessDamping; ring
  change (overlapCoefficient ((1+h.val)/2) 0 / (h.val:ℂ)^2).re/2 = _
  rw [htemp,← Complex.ofReal_pow,Complex.div_ofReal_re,criticalGapLaw,
    sampled_cumulative_zero (excessDamping_gt h) (half_pos h.property).ne',laplace_cumulative_zero]
  ring

#print axioms primitive_frequency_injective
#print axioms sampledGapLaw_line
#print axioms sampledGapLaw_zero
#print axioms sampledGapLaw_map_neg
#print axioms sampled_cumulative_zero
#print axioms laplace_cumulative_zero
#print axioms cumulative_zero_quadratic_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
