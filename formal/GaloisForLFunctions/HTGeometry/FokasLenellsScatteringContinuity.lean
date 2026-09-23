import GaloisForLFunctions.HTGeometry.FokasLenellsSpectralContinuity
import GaloisForLFunctions.HTGeometry.FokasLenellsContourBounds

/-!
# Continuity and measurability of constructed scattering data

Joint Volterra continuity and the spectral-independent integrable effective
coefficient bound allow dominated convergence at both spatial infinities.
The resulting uniformized scattering matrix is continuous on the real line.
Inverting the nonsingular gauge transports continuity to the original
positive spectrum, and Pauli transport supplies every remaining ray.
The explicit normalized potentials give continuous, Borel measurable
reflection quotients without a nonvanishing assumption.
-/

open Complex Matrix Set MeasureTheory Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The free rotation is jointly continuous in frequency, position and vector. -/
theorem continuous_rotatingFrame_parameters :
    Continuous (fun p : ℝ × ℝ × SpectralVector => rotatingFrame p.1 p.2.1 p.2.2) := by
  unfold rotatingFrame FDNLS.staggerPhase
  fun_prop

theorem continuous_uniformizedInteractionSolution_parameter (f g h : SchwartzMap ℝ ℂ)
    (v : SpectralVector) :
    Continuous (fun p : ℝ × ℝ => uniformizedInteractionSolution f g h p.1 v p.2) := by
  have hs := (continuous_spectralSolution_parameter f g h v).comp
    (f := fun p : ℝ × ℝ => ((p.1:ℂ),p.2)) ((Complex.continuous_ofReal.comp continuous_fst).prodMk continuous_snd)
  exact continuous_rotatingFrame_parameters.comp
    (f := fun p : ℝ × ℝ => (p.1,p.2,spectralSolution f g h (p.1:ℂ) v p.2))
    (continuous_fst.prodMk (continuous_snd.prodMk hs))

theorem continuous_uniformizedInteractionRate_parameters (f g h : SchwartzMap ℝ ℂ) :
    Continuous (fun p : ℝ × ℝ × SpectralVector =>
      uniformizedInteractionRate f g h p.1 p.2.1 p.2.2) := by
  unfold uniformizedInteractionRate rotatingFrame effectiveOperator pairOperator
  change Continuous fun p : ℝ × ℝ × SpectralVector =>
    (FDNLS.staggerPhase p.1 p.2.1 *
      (effectiveSchwartzEntries f g h 0 0 p.2.1*(FDNLS.staggerPhase (-p.1) p.2.1*p.2.2.1)+
       effectiveSchwartzEntries f g h 0 1 p.2.1*(FDNLS.staggerPhase (-(-p.1)) p.2.1*p.2.2.2)),
     FDNLS.staggerPhase (-p.1) p.2.1 *
      (effectiveSchwartzEntries f g h 1 0 p.2.1*(FDNLS.staggerPhase (-p.1) p.2.1*p.2.2.1)+
       effectiveSchwartzEntries f g h 1 1 p.2.1*(FDNLS.staggerPhase (-(-p.1)) p.2.1*p.2.2.2)))
  unfold FDNLS.staggerPhase
  fun_prop

theorem continuous_uniformizedOrbitDerivative_parameter (f g h : SchwartzMap ℝ ℂ)
    (v : SpectralVector) (b : Bool) :
    Continuous (fun p : ℝ × ℝ => uniformizedOrbitDerivative f g h p.1 v b p.2) := by
  have hc := (continuous_uniformizedInteractionRate_parameters f g h).comp
    (f := fun p : ℝ × ℝ => (p.1,p.2,uniformizedInteractionSolution f g h p.1 v p.2))
    (continuous_fst.prodMk (continuous_snd.prodMk (continuous_uniformizedInteractionSolution_parameter f g h v)))
  cases b
  · exact hc
  · exact (hc.comp (f := fun p : ℝ × ℝ => (p.1,-p.2))
      (continuous_fst.prodMk continuous_snd.neg)).neg

/-- Dominated convergence passes spectral continuity through both infinite endpoint integrals. -/
theorem continuous_uniformizedAsymptoticVector (f g h : SchwartzMap ℝ ℂ)
    (v : SpectralVector) (b : Bool) : Continuous (fun z : ℝ => uniformizedAsymptoticVector f g h z v b) := by
  unfold uniformizedAsymptoticVector
  refine continuous_const.add (continuous_of_dominated
    (bound := fun x => orientedEffectiveDensity f g h b x*(‖v‖*Real.exp (effectiveMass f g h)))
    (fun z => (uniformizedOrbitDerivative_continuous f g h z v b).aestronglyMeasurable) ?_ ?_ ?_)
  · intro z
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hb := uniformizedOrbit_bound f g h z v b x
    rw [abs_of_pos hx] at hb
    exact (uniformizedOrbitDerivative_bound f g h z v b x).trans
      (mul_le_mul_of_nonneg_left hb (orientedEffectiveDensity_nonneg f g h b x))
  · exact ((orientedEffectiveDensity_integrable f g h b).mul_const _).integrableOn
  · exact Eventually.of_forall (fun x => (continuous_uniformizedOrbitDerivative_parameter f g h v b).comp
      (f := fun z : ℝ => (z,x)) (continuous_id.prodMk continuous_const))

theorem continuous_uniformizedAsymptoticMatrix (f g h : SchwartzMap ℝ ℂ) (b : Bool) :
    Continuous (fun z : ℝ => uniformizedAsymptoticMatrix f g h z b) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j
  · exact (continuous_uniformizedAsymptoticVector f g h (1,0) b).fst
  · exact (continuous_uniformizedAsymptoticVector f g h (0,1) b).fst
  · exact (continuous_uniformizedAsymptoticVector f g h (1,0) b).snd
  · exact (continuous_uniformizedAsymptoticVector f g h (0,1) b).snd

/-- The uniformized scattering matrix is continuous on the whole real line, including zero. -/
theorem continuous_uniformizedScatteringMatrix (f g h : SchwartzMap ℝ ℂ) :
    Continuous (uniformizedScatteringMatrix f g h) := by
  change Continuous (fun z : ℝ => uniformizedAsymptoticMatrix f g h z false*
    (uniformizedAsymptoticMatrix f g h z true)⁻¹)
  simp only [Matrix.inv_def, uniformizedAsymptoticMatrix_det, Ring.inverse_one, one_smul]
  exact (continuous_uniformizedAsymptoticMatrix f g h false).mul
    (continuous_uniformizedAsymptoticMatrix f g h true).matrix_adjugate

/-- Inverting the proved gauge relation recovers the original scattering matrix. -/
theorem scatteringMatrix_eq_uniformized (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    scatteringMatrix q κ =
      (uniformizationGauge 0 (Complex.exp (κ:ℂ)))⁻¹*
        uniformizedScatteringMatrix (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
          (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q)) ((Real.exp κ)^(2 : ℕ))*
            uniformizationGauge 0 (Complex.exp (κ:ℂ)) := by
  rw [uniformizedScatteringMatrix_gauge]
  have hi := Matrix.nonsing_inv_mul (uniformizationGauge 0 (Complex.exp (κ:ℂ)))
    (uniformizationGauge_exp_isUnit_det 0 (κ:ℂ))
  simp only [← Complex.ofReal_exp, Matrix.mul_assoc] at hi ⊢
  rw [← Matrix.mul_assoc ((uniformizationGauge 0 (Real.exp κ:ℂ))⁻¹)
    (uniformizationGauge 0 (Real.exp κ:ℂ)), hi, one_mul, mul_one]

/-- The inverse diagonal gauge is continuous because its exponential spectral parameter never vanishes. -/
theorem continuous_uniformizationGauge_exp_inverse :
    Continuous (fun κ : ℝ => (uniformizationGauge 0 (Complex.exp (κ:ℂ)))⁻¹) := by
  refine continuous_iff_continuousAt.mpr fun κ => ?_
  have hG : Continuous (fun s : ℝ => uniformizationGauge 0 (Complex.exp (s:ℂ))) := by
    unfold uniformizationGauge
    fun_prop
  apply (continuousAt_matrix_inv _ ?_).comp hG.continuousAt
  rw [det_uniformizationGauge]
  simpa only [Ring.inverse_eq_inv'] using
    continuousAt_inv₀ (mul_ne_zero (neg_ne_zero.mpr (two_ne_zero : (2:ℂ) ≠ 0)) (Complex.exp_ne_zero (κ:ℂ)))

/-- The scattering matrix constructed from each Schwartz potential depends continuously on positive spectrum. -/
theorem continuous_scatteringMatrix (q : SchwartzMap ℝ ℂ) : Continuous (scatteringMatrix q) := by
  change Continuous (fun κ : ℝ => scatteringMatrix q κ)
  simp only [scatteringMatrix_eq_uniformized]
  apply (continuous_uniformizationGauge_exp_inverse.mul
    ((continuous_uniformizedScatteringMatrix _ _ _).comp (Real.continuous_exp.pow 2))).mul
  unfold uniformizationGauge
  fun_prop

/-- Continuity of every contour scattering matrix follows from fixed Pauli transport. -/
theorem continuous_contourScatteringMatrix (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) :
    Continuous (contourScatteringMatrix q vertical negative) := by
  exact ((continuous_scatteringMatrix (contourSource q vertical)).const_mul
    (contourConjugator vertical negative)).mul_const (contourConjugator vertical negative)

theorem continuous_contourTransmission (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) :
    Continuous (contourTransmission q vertical negative) :=
  (continuous_apply 0).comp ((continuous_apply 0).comp (continuous_contourScatteringMatrix q vertical negative))

theorem continuous_contourReverseTransmission (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) :
    Continuous (contourReverseTransmission q vertical negative) :=
  (continuous_apply 1).comp ((continuous_apply 1).comp (continuous_contourScatteringMatrix q vertical negative))

theorem continuous_contourReflectionAmplitude (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) :
    Continuous (contourReflectionAmplitude q vertical negative) :=
  (continuous_apply 0).comp ((continuous_apply 1).comp (continuous_contourScatteringMatrix q vertical negative))

theorem continuous_contourReverseReflectionAmplitude (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) :
    Continuous (contourReverseReflectionAmplitude q vertical negative) :=
  (continuous_apply 1).comp ((continuous_apply 0).comp (continuous_contourScatteringMatrix q vertical negative))

/-- The normalized reflection quotients are continuous without a nonvanishing hypothesis. -/
theorem continuous_globalSmall_contourReflection (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) :
    Continuous (contourReflectionCoefficient (globalSmallScatteringPotential q) vertical negative) ∧
    Continuous (contourReverseReflectionCoefficient (globalSmallScatteringPotential q) vertical negative) := by
  constructor
  · exact (continuous_contourReflectionAmplitude _ vertical negative).div
      (continuous_contourTransmission _ vertical negative)
      (fun κ => (globalSmall_contour_transmission_nonzero q vertical negative κ).1)
  · exact (continuous_contourReverseReflectionAmplitude _ vertical negative).div
      (continuous_contourReverseTransmission _ vertical negative)
      (fun κ => (globalSmall_contour_transmission_nonzero q vertical negative κ).2)

/-- The actual small reflection data on each contour ray are Borel measurable. -/
theorem measurable_globalSmall_contourReflection (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) :
    Measurable (contourReflectionCoefficient (globalSmallScatteringPotential q) vertical negative) ∧
    Measurable (contourReverseReflectionCoefficient (globalSmallScatteringPotential q) vertical negative) :=
  ⟨(continuous_globalSmall_contourReflection q vertical negative).1.measurable,
    (continuous_globalSmall_contourReflection q vertical negative).2.measurable⟩

end
end GaloisForLFunctions.HTGeometry.FokasLenells
