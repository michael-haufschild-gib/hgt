import GaloisForLFunctions.RHTower.SelbergMaassPhaseProductLimit
import GaloisForLFunctions.RHTower.SelbergMaassPhaseStress

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open scoped BigOperators
namespace GaloisForLFunctions.RHTower.SelbergMaassPhaseProductLossLimit
open GaloisForLFunctions.HTGeometry
open SelbergMaassCongruenceTrace SelbergMaassPhaseRellich SelbergMaassFourierPartial
  SelbergMaassDilationStress SelbergMaassCharacterSeamFlux SelbergMaassTraceEnergy
  SelbergMaassMean SelbergMaassPhaseStress SelbergMaassPhaseProductLimit
noncomputable section

variable (N : ℕ) {lam : ℝ}
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
  (r s : ZMod (N + 1))

def phaseProductPartial (M : ℕ) : ℂ :=
  ((((N + 1 : ℕ) : ℝ)⁻¹ ^ (3 : ℕ) / 2 : ℝ) : ℂ) *
    ∑ i : PhaseIndex N,
      l2Pair
        (fourierPartialSum
          (SelbergMaassFourierPartial.unitRescaledHorizontalReadout N f (phaseReadout N r s i) 1) M)
        (fun t => (t : ℂ) * fourierPartialSum
          (SelbergMaassFourierPartial.unitRescaledVerticalReadout N f (phaseReadout N r s i) 1) M t)

def phaseProductExact : ℂ :=
  ((((N + 1 : ℕ) : ℝ)⁻¹ ^ (3 : ℕ) / 2 : ℝ) : ℂ) *
    ∑ i : PhaseIndex N,
      l2Pair
        (SelbergMaassFourierPartial.unitRescaledHorizontalReadout N f (phaseReadout N r s i) 1)
        (fun t => (t : ℂ) * SelbergMaassFourierPartial.unitRescaledVerticalReadout N f (phaseReadout N r s i) 1 t)

theorem tendsto_phaseProductPartial :
    Tendsto (phaseProductPartial N f r s) atTop (nhds (phaseProductExact N f r s)) := by
  classical
  unfold phaseProductPartial phaseProductExact
  have hsum (I : Finset (PhaseIndex N)) :
      Tendsto (fun M : ℕ => ∑ i ∈ I,
        l2Pair
          (fourierPartialSum
            (SelbergMaassFourierPartial.unitRescaledHorizontalReadout N f (phaseReadout N r s i) 1) M)
          (fun t => (t : ℂ) * fourierPartialSum
            (SelbergMaassFourierPartial.unitRescaledVerticalReadout N f (phaseReadout N r s i) 1) M t)) atTop
        (nhds (∑ i ∈ I,
          l2Pair
            (SelbergMaassFourierPartial.unitRescaledHorizontalReadout N f (phaseReadout N r s i) 1)
            (fun t => (t : ℂ) * SelbergMaassFourierPartial.unitRescaledVerticalReadout N f (phaseReadout N r s i) 1 t))) := by
    induction I using Finset.induction_on with
    | empty => simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (nhds 0))
    | insert i I hi hI =>
      have hi' := tendsto_unitCoord_sourceReadout_partial_pair N f
        (phaseReadout N r s i) (phaseReadout N r s i) (by norm_num : (0 : ℝ) < 1)
      simpa [Finset.sum_insert, hi] using hi'.add hI
  simpa only [Finset.sum_const_zero, Finset.sum_const] using
    (hsum Finset.univ).const_mul ((((N + 1 : ℕ) : ℝ)⁻¹ ^ (3 : ℕ) / 2 : ℝ)
      : ℂ)

/-- A unit-rescaled horizontal phase readout is the horizontal source derivative at its
literal physical point. -/
private theorem unitRescaledHorizontalReadout_eq_phase (i : PhaseIndex N) (t : ℝ) :
    unitRescaledHorizontalReadout N f (phaseReadout N r s i) 1 t =
      phaseReadout N r s i (sourceDerivative N f 1 (ofComplex (point (t * (N + 1 : ℕ)) 1))) := by
  unfold unitRescaledHorizontalReadout unitRescaledSlice
  change dir 1 (observedField N f (phaseReadout N r s i))
    (point (t * (N + 1 : ℕ)) 1) = _
  have hpoint : ((ofComplex (point (t * (N + 1 : ℕ)) 1) : ℍ) : ℂ) =
      point (t * (N + 1 : ℕ)) 1 :=
    SelbergMaassUnipotentPaths.coe_ofComplex_point (t * (N + 1 : ℕ)) zero_lt_one
  calc
    dir 1 (observedField N f (phaseReadout N r s i))
        (point (t * (N + 1 : ℕ)) 1) =
        dir 1 (observedField N f (phaseReadout N r s i))
          ((ofComplex (point (t * (N + 1 : ℕ)) 1) : ℍ) : ℂ) :=
      congrArg (dir 1 (observedField N f (phaseReadout N r s i))) hpoint.symm
    _ = _ := phaseReadout_dir N f r s i 1 (ofComplex (point (t * (N + 1 : ℕ)) 1))

/-- A unit-rescaled vertical phase readout is the height source derivative at its
literal physical point. -/
private theorem unitRescaledVerticalReadout_eq_phase (i : PhaseIndex N) (t : ℝ) :
    unitRescaledVerticalReadout N f (phaseReadout N r s i) 1 t =
      phaseReadout N r s i
        (sourceDerivative N f Complex.I (ofComplex (point (t * (N + 1 : ℕ)) 1))) := by
  unfold unitRescaledVerticalReadout unitRescaledSlice
  change dir Complex.I (observedField N f (phaseReadout N r s i))
    (point (t * (N + 1 : ℕ)) 1) = _
  have hpoint : ((ofComplex (point (t * (N + 1 : ℕ)) 1) : ℍ) : ℂ) =
      point (t * (N + 1 : ℕ)) 1 :=
    SelbergMaassUnipotentPaths.coe_ofComplex_point (t * (N + 1 : ℕ)) zero_lt_one
  calc
    dir Complex.I (observedField N f (phaseReadout N r s i))
        (point (t * (N + 1 : ℕ)) 1) =
        dir Complex.I (observedField N f (phaseReadout N r s i))
          ((ofComplex (point (t * (N + 1 : ℕ)) 1) : ℍ) : ℂ) :=
      congrArg (dir Complex.I (observedField N f (phaseReadout N r s i))) hpoint.symm
    _ = _ := phaseReadout_dir N f r s i Complex.I (ofComplex (point (t * (N + 1 : ℕ)) 1))

private theorem conj_mul_re_eq_mul_conj_re (a b : ℂ) :
    ((starRingEnd ℂ) a * b).re = (a * (starRingEnd ℂ) b).re := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The finite phase average of rescaled horizontal/vertical readouts is the
literal physical mixed source loss. -/
theorem phaseAverage_rescaledReadouts_re_eq_loss (t : ℝ) :
    ((((N + 1 : ℕ) : ℝ)⁻¹ ^ (3 : ℕ) / 2) *
      ∑ i : PhaseIndex N,
        ((starRingEnd ℂ)
          (unitRescaledHorizontalReadout N f (phaseReadout N r s i) 1 t) *
          unitRescaledVerticalReadout N f (phaseReadout N r s i) 1 t).re) =
      lossPair N r s
        (sourceDerivative N f 1 (ofComplex (point (t * (N + 1 : ℕ)) 1)))
        (sourceDerivative N f Complex.I (ofComplex (point (t * (N + 1 : ℕ)) 1))) := by
  rw [← phaseAverage_pair]
  unfold phaseAverage
  congr 2
  funext i
  rw [unitRescaledHorizontalReadout_eq_phase,
    unitRescaledVerticalReadout_eq_phase, conj_mul_re_eq_mul_conj_re]

private theorem phase_pair_re_eq_integral (i : PhaseIndex N) :
    (l2Pair
      (unitRescaledHorizontalReadout N f (phaseReadout N r s i) 1)
      (fun t => (t : ℂ) * unitRescaledVerticalReadout N f (phaseReadout N r s i) 1 t)).re =
    ∫ t in (0 : ℝ)..1, t *
      ((starRingEnd ℂ)
        (unitRescaledHorizontalReadout N f (phaseReadout N r s i) 1 t) *
        unitRescaledVerticalReadout N f (phaseReadout N r s i) 1 t).re := by
  have hH := continuous_unitRescaledHorizontalReadout N f (phaseReadout N r s i)
    (by norm_num : (0 : ℝ) < 1)
  have hV := continuous_unitRescaledVerticalReadout N f (phaseReadout N r s i)
    (by norm_num : (0 : ℝ) < 1)
  have hI : IntervalIntegrable (fun t : ℝ =>
      (starRingEnd ℂ) (unitRescaledHorizontalReadout N f (phaseReadout N r s i) 1 t) *
        ((t : ℂ) * unitRescaledVerticalReadout N f (phaseReadout N r s i) 1 t)) volume 0 1 := by
    exact ((Complex.conjCLE.continuous.comp hH).mul
      ((Complex.continuous_ofReal.comp continuous_id).mul hV)).intervalIntegrable 0 1
  unfold l2Pair
  change Complex.reCLM (∫ t in (0 : ℝ)..1,
    (starRingEnd ℂ) (unitRescaledHorizontalReadout N f (phaseReadout N r s i) 1 t) *
      ((t : ℂ) * unitRescaledVerticalReadout N f (phaseReadout N r s i) 1 t)) = _
  rw [← Complex.reCLM.intervalIntegral_comp_comm hI]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [Complex.reCLM_apply, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The real phase-product limit is exactly the unit-rescaled mixed source-loss moment.
This preserves the finite phase channel that reaches the core--cusp identity. -/
theorem phaseProductExact_re_eq_unitLossMoment :
    (phaseProductExact N f r s).re =
      ∫ t in (0 : ℝ)..1, t * lossPair N r s
        (sourceDerivative N f 1 (ofComplex (point (t * (N + 1 : ℕ)) 1)))
        (sourceDerivative N f Complex.I (ofComplex (point (t * (N + 1 : ℕ)) 1))) := by
  let c : ℝ := ((N + 1 : ℕ) : ℝ)⁻¹ ^ (3 : ℕ) / 2
  let H : PhaseIndex N → ℝ → ℂ := fun i =>
    unitRescaledHorizontalReadout N f (phaseReadout N r s i) 1
  let V : PhaseIndex N → ℝ → ℂ := fun i =>
    unitRescaledVerticalReadout N f (phaseReadout N r s i) 1
  have hH (i : PhaseIndex N) : Continuous (H i) := by
    exact continuous_unitRescaledHorizontalReadout N f (phaseReadout N r s i)
      (by norm_num : (0 : ℝ) < 1)
  have hV (i : PhaseIndex N) : Continuous (V i) := by
    exact continuous_unitRescaledVerticalReadout N f (phaseReadout N r s i)
      (by norm_num : (0 : ℝ) < 1)
  have hProd (i : PhaseIndex N) : Continuous (fun t : ℝ =>
      t * ((starRingEnd ℂ) (H i t) * V i t).re) := by
    exact continuous_id.mul (Complex.continuous_re.comp
      ((Complex.conjCLE.continuous.comp (hH i)).mul (hV i)))
  have hInt (i : PhaseIndex N) : IntervalIntegrable (fun t : ℝ =>
      c * (t * ((starRingEnd ℂ) (H i t) * V i t).re)) volume 0 1 :=
    (continuous_const.mul (hProd i)).intervalIntegrable 0 1
  have hpair (i : PhaseIndex N) :
      (l2Pair (H i) (fun t => (t : ℂ) * V i t)).re =
      ∫ t in (0 : ℝ)..1, t * ((starRingEnd ℂ) (H i t) * V i t).re := by
    exact phase_pair_re_eq_integral N f r s i
  have havg (t : ℝ) :
      c * ∑ i : PhaseIndex N, ((starRingEnd ℂ) (H i t) * V i t).re =
      lossPair N r s
        (sourceDerivative N f 1 (ofComplex (point (t * (N + 1 : ℕ)) 1)))
        (sourceDerivative N f Complex.I (ofComplex (point (t * (N + 1 : ℕ)) 1))) := by
    exact phaseAverage_rescaledReadouts_re_eq_loss N f r s t
  unfold phaseProductExact
  change (((c : ℂ) * ∑ i : PhaseIndex N,
    l2Pair (H i) (fun t => (t : ℂ) * V i t)).re) = _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hsumre :
      (∑ i : PhaseIndex N, l2Pair (H i) (fun t => (t : ℂ) * V i t)).re =
        ∑ i : PhaseIndex N, (l2Pair (H i) (fun t => (t : ℂ) * V i t)).re := by
    simp
  rw [hsumre, Finset.mul_sum]
  simp_rw [hpair, ← intervalIntegral.integral_const_mul]
  have hsumIntegral :
      (∑ i : PhaseIndex N, ∫ t in (0 : ℝ)..1,
        c * (t * ((starRingEnd ℂ) (H i t) * V i t).re)) =
      ∫ t in (0 : ℝ)..1, ∑ i : PhaseIndex N,
        c * (t * ((starRingEnd ℂ) (H i t) * V i t).re) := by
    symm
    simpa using
      (intervalIntegral.integral_finsetSum (s := Finset.univ)
        (f := fun i t => c * (t * ((starRingEnd ℂ) (H i t) * V i t).re))
        (fun i _ => hInt i))
  rw [hsumIntegral]
  apply intervalIntegral.integral_congr
  intro t _
  change (∑ i : PhaseIndex N, c * (t * ((starRingEnd ℂ) (H i t) * V i t).re)) =
    t * lossPair N r s
      (sourceDerivative N f 1 (ofComplex (point (t * (N + 1 : ℕ)) 1)))
      (sourceDerivative N f Complex.I (ofComplex (point (t * (N + 1 : ℕ)) 1)))
  rw [← Finset.mul_sum Finset.univ (fun i =>
    t * ((starRingEnd ℂ) (H i t) * V i t).re) c]
  rw [← Finset.mul_sum Finset.univ (fun i =>
    ((starRingEnd ℂ) (H i t) * V i t).re) t]
  calc
    c * (t * ∑ i : PhaseIndex N, ((starRingEnd ℂ) (H i t) * V i t).re) =
        t * (c * ∑ i : PhaseIndex N, ((starRingEnd ℂ) (H i t) * V i t).re) := by ring
    _ = _ := by rw [havg]

end
end GaloisForLFunctions.RHTower.SelbergMaassPhaseProductLossLimit
