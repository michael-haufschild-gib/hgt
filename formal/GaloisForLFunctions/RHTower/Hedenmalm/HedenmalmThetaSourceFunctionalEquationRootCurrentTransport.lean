import GaloisForLFunctions.HTGeometry.ConstitutiveEvenPositiveWeightedReflection
import GaloisForLFunctions.HTGeometry.GeneralizedEigenspaceIntertwining
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceConormalSocle
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmShiftedSourceEquation

/-!
# Functional-equation transport of theta-source root currents

Source reflection is promoted from a pointwise integral identity to a unitary involution on the
weighted source Hilbert space and then conjugated through the quantile unitary.  The resulting
operator anticommutes with the fixed compact theta-source inverse, carries the complete generalized
`mu`-block to the `-mu`-block, and acts on its conormal current by the exact Jordan-depth character
`(-1)^(d - 1)`.  Current norm and recovered eigenline are preserved exactly.
-/

open Complex MeasureTheory Module.End
open GaloisForLFunctions.HTGeometry

namespace RHTower.HedenmalmThetaSource

noncomputable section

private abbrev ThetaH := Lp ℂ 2 unitIntervalMeasure
private abbrev ThetaSourceH := HedenmalmQuantile.SourceSpace thetaSource

theorem thetaSourceWeight_even (x : ℝ) :
    HedenmalmQuantile.sourceWeight thetaSource (-x) =
      HedenmalmQuantile.sourceWeight thetaSource x := by
  change (thetaSource.k (-x))⁻¹ = (thetaSource.k x)⁻¹
  rw [thetaSource_even]

/-- Literal source reflection on the theta weighted Hilbert space. -/
def thetaSourceReflection : ThetaSourceH →L[ℂ] ThetaSourceH :=
  positiveWeightedReflection
    (HedenmalmQuantile.measurable_sourceWeight thetaSource) thetaSourceWeight_even

def thetaSourceReflectionLIE : ThetaSourceH ≃ₗᵢ[ℂ] ThetaSourceH :=
  positiveWeightedReflectionLIE
    (HedenmalmQuantile.measurable_sourceWeight thetaSource) thetaSourceWeight_even

theorem thetaSourceReflection_ae (f : ThetaSourceH) :
    thetaSourceReflection f =ᵐ[(volume : Measure ℝ)] fun x => f (-x) :=
  positiveWeightedReflection_ae
    (HedenmalmQuantile.measurable_sourceWeight thetaSource)
    (HedenmalmQuantile.sourceWeight_pos thetaSource) thetaSourceWeight_even f

@[simp] theorem thetaSourceReflection_involutive (f : ThetaSourceH) :
    thetaSourceReflection (thetaSourceReflection f) = f :=
  positiveWeightedReflection_involutive
    (HedenmalmQuantile.measurable_sourceWeight thetaSource) thetaSourceWeight_even f

/-- Source reflection conjugated into the fixed quantile Hilbert space. -/
def thetaQuantileReflectionLIE : ThetaH ≃ₗᵢ[ℂ] ThetaH :=
  (HedenmalmQuantile.quantileUnitary thetaSource).symm.trans
    (thetaSourceReflectionLIE.trans (HedenmalmQuantile.quantileUnitary thetaSource))

def thetaQuantileReflection : ThetaH →L[ℂ] ThetaH :=
  thetaQuantileReflectionLIE.toLinearIsometry.toContinuousLinearMap

@[simp] theorem thetaQuantileReflection_apply (f : ThetaH) :
    thetaQuantileReflection f =
      HedenmalmQuantile.quantileUnitary thetaSource
        (thetaSourceReflection ((HedenmalmQuantile.quantileUnitary thetaSource).symm f)) := rfl

@[simp] theorem thetaQuantileReflection_involutive (f : ThetaH) :
    thetaQuantileReflection (thetaQuantileReflection f) = f := by
  rw [thetaQuantileReflection_apply, thetaQuantileReflection_apply]
  simp

/-- Fixed compact inverse conjugated back into source coordinates. -/
def thetaSourceCoordinateInverse (v : ThetaSourceH) : ThetaSourceH :=
  (HedenmalmQuantile.quantileUnitary thetaSource).symm
    (thetaCompactSourceInverse (HedenmalmQuantile.quantileUnitary thetaSource v))

theorem sourceInverse_ae_eq_thetaSourceCoordinateInverse (v : ThetaSourceH) :
    HedenmalmQuantile.sourceInverse thetaSource (fun x => (v x : ℂ)) =ᵐ[
      (volume : Measure ℝ)] fun x => thetaSourceCoordinateInverse v x := by
  simpa only [thetaSourceCoordinateInverse,
    (HedenmalmQuantile.quantileUnitary thetaSource).symm_apply_apply] using
    sourceInverse_ae_eq_quantileSymm_thetaCompactSourceInverse
      (HedenmalmQuantile.quantileUnitary thetaSource v)

theorem sourceInverse_thetaSourceReflection_neg (v : ThetaSourceH) (x : ℝ) :
    HedenmalmQuantile.sourceInverse thetaSource
        (fun y => ((thetaSourceReflection v) y : ℂ)) (-x) =
      -HedenmalmQuantile.sourceInverse thetaSource (fun y => (v y : ℂ)) x := by
  calc
    HedenmalmQuantile.sourceInverse thetaSource
        (fun y => ((thetaSourceReflection v) y : ℂ)) (-x) =
        HedenmalmQuantile.sourceInverse thetaSource
          (HedenmalmHilbertSchmidt.sourceReflection (fun y => (v y : ℂ))) (-x) := by
      apply sourceInverse_congr_ae
      change (fun y => ((thetaSourceReflection v) y : ℂ)) =ᵐ[(volume : Measure ℝ)]
        fun y => v (-y)
      exact thetaSourceReflection_ae v
    _ = -HedenmalmQuantile.sourceInverse thetaSource (fun y => (v y : ℂ)) x :=
      sourceInverse_sourceReflection_theta
        (HedenmalmQuantile.integrable_sourceSpace thetaSource v) x

theorem thetaSourceReflection_conjugated_inverse (v : ThetaSourceH) :
    thetaSourceReflection (thetaSourceCoordinateInverse (thetaSourceReflection v)) =
      -thetaSourceCoordinateInverse v := by
  have hleft := (sourceInverse_ae_eq_thetaSourceCoordinateInverse
    (thetaSourceReflection v)).comp_tendsto
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  have hright := sourceInverse_ae_eq_thetaSourceCoordinateInverse v
  have hreflect := thetaSourceReflection_ae
    (thetaSourceCoordinateInverse (thetaSourceReflection v))
  have hneg :
      (fun x => ((-thetaSourceCoordinateInverse v : ThetaSourceH) x : ℂ)) =ᵐ[
        (volume : Measure ℝ)] fun x => -thetaSourceCoordinateInverse v x := by
    exact (withDensity_realDensity_ae_eq
      (HedenmalmQuantile.measurable_sourceWeight thetaSource)
      (HedenmalmQuantile.sourceWeight_pos thetaSource)).mp
        (Lp.coeFn_neg (thetaSourceCoordinateInverse v))
  apply Lp.ext
  apply (withDensity_realDensity_ae_eq
    (HedenmalmQuantile.measurable_sourceWeight thetaSource)
    (HedenmalmQuantile.sourceWeight_pos thetaSource)).mpr
  filter_upwards [hreflect, hleft, hright, hneg] with x hrx hlx hrightx hnegx
  rw [hrx, hnegx]
  calc
    thetaSourceCoordinateInverse (thetaSourceReflection v) (-x) =
        HedenmalmQuantile.sourceInverse thetaSource
          (fun y => ((thetaSourceReflection v) y : ℂ)) (-x) := hlx.symm
    _ = -HedenmalmQuantile.sourceInverse thetaSource (fun y => (v y : ℂ)) x :=
      sourceInverse_thetaSourceReflection_neg v x
    _ = -thetaSourceCoordinateInverse v x := by rw [hrightx]

/-- Operator-level functional equation: `R B R = -B`. -/
theorem thetaQuantileReflection_anticommutes (f : ThetaH) :
    thetaQuantileReflection (thetaCompactSourceInverse (thetaQuantileReflection f)) =
      -thetaCompactSourceInverse f := by
  apply (HedenmalmQuantile.quantileUnitary thetaSource).symm.injective
  simpa only [thetaQuantileReflection_apply,
    thetaSourceCoordinateInverse,
    (HedenmalmQuantile.quantileUnitary thetaSource).symm_apply_apply,
    (HedenmalmQuantile.quantileUnitary thetaSource).apply_symm_apply,
    map_neg] using
    thetaSourceReflection_conjugated_inverse
      ((HedenmalmQuantile.quantileUnitary thetaSource).symm f)

theorem thetaQuantileReflection_intertwines_neg (f : ThetaH) :
    thetaQuantileReflection (thetaKernelOperator f) =
      (-thetaKernelOperator) (thetaQuantileReflection f) := by
  have h := thetaQuantileReflection_anticommutes (thetaQuantileReflection f)
  rw [thetaQuantileReflection_involutive] at h
  simpa only [thetaKernelOperator_eq_thetaCompactSourceInverse, neg_apply] using h

/-- Reflection of a nonzero source spectral point. -/
def thetaSpectrumNeg (mu : ThetaNonzeroSpectrum) : ThetaNonzeroSpectrum :=
  ⟨-(mu : ℂ), neg_mem_spectrum_thetaKernelOperator mu.2.2 mu.2.1,
    neg_ne_zero.mpr mu.2.2⟩

@[simp] theorem thetaSpectrumNeg_val (mu : ThetaNonzeroSpectrum) :
    (thetaSpectrumNeg mu : ℂ) = -(mu : ℂ) := rfl

@[simp] theorem thetaSpectrumNeg_involutive (mu : ThetaNonzeroSpectrum) :
    thetaSpectrumNeg (thetaSpectrumNeg mu) = mu := by
  apply Subtype.ext
  simp

/-- Operator reflection is exactly functional-equation reflection under Xi/source recovery. -/
theorem thetaSpectrumNeg_thetaSpectrumOfXiSupport (rho : XiDivisorSupport) :
    thetaSpectrumNeg (thetaSpectrumOfXiSupport rho) =
      thetaSpectrumOfXiSupport (xiZeroReflectEquiv rho) := by
  apply Subtype.ext
  rw [thetaSpectrumNeg_val, thetaSpectrumOfXiSupport_val,
    thetaSpectrumOfXiSupport_val, xiSpectralPointSupport_reflect]
  simp

/-- Source reflection maps the complete generalized `mu`-block exactly onto the `-mu`-block. -/
theorem map_thetaRootBlock_reflection (mu : ThetaNonzeroSpectrum) :
    Submodule.map thetaQuantileReflection.toLinearMap (ThetaRootBlock mu) =
      ThetaRootBlock (thetaSpectrumNeg mu) := by
  calc
    Submodule.map thetaQuantileReflection.toLinearMap (ThetaRootBlock mu) =
        maxGenEigenspace
          (-thetaKernelOperator : Module.End ℂ ThetaH) (mu : ℂ) := by
      apply map_maxGenEigenspace_eq_of_intertwining
      · exact thetaQuantileReflectionLIE.injective
      · exact thetaQuantileReflection_intertwines_neg
      · intro y _hy
        exact ⟨thetaQuantileReflection y, thetaQuantileReflection_involutive y⟩
    _ = ThetaRootBlock (thetaSpectrumNeg mu) := by
      simpa only [ThetaRootBlock, thetaSpectrumNeg_val, neg_neg] using
        maxGenEigenspace_neg_neg
          (thetaKernelOperator : Module.End ℂ ThetaH) (-(mu : ℂ))

theorem thetaQuantileReflection_mem_neg_rootBlock (mu : ThetaNonzeroSpectrum)
    (v : ThetaRootBlock mu) :
    thetaQuantileReflection (v : ThetaH) ∈ ThetaRootBlock (thetaSpectrumNeg mu) := by
  rw [← map_thetaRootBlock_reflection mu]
  exact ⟨v, v.2, rfl⟩

/-- Unitary functional-equation transport between paired complete root blocks. -/
def thetaRootBlockReflectionLIE (mu : ThetaNonzeroSpectrum) :
    ThetaRootBlock mu ≃ₗᵢ[ℂ] ThetaRootBlock (thetaSpectrumNeg mu) where
  toFun v := ⟨thetaQuantileReflection (v : ThetaH),
    thetaQuantileReflection_mem_neg_rootBlock mu v⟩
  map_add' v w := by
    apply Subtype.ext
    exact map_add thetaQuantileReflection (v : ThetaH) (w : ThetaH)
  map_smul' c v := by
    apply Subtype.ext
    exact map_smul thetaQuantileReflection c (v : ThetaH)
  norm_map' v := thetaQuantileReflectionLIE.norm_map (v : ThetaH)
  invFun w := ⟨thetaQuantileReflection (w : ThetaH), by
    simpa using thetaQuantileReflection_mem_neg_rootBlock (thetaSpectrumNeg mu) w⟩
  left_inv v := by
    apply Subtype.ext
    exact thetaQuantileReflection_involutive (v : ThetaH)
  right_inv w := by
    apply Subtype.ext
    exact thetaQuantileReflection_involutive (w : ThetaH)

@[simp] theorem thetaRootBlockReflectionLIE_apply_coe (mu : ThetaNonzeroSpectrum)
    (v : ThetaRootBlock mu) :
    ((thetaRootBlockReflectionLIE mu v : ThetaRootBlock (thetaSpectrumNeg mu)) : ThetaH) =
      thetaQuantileReflection (v : ThetaH) := rfl

theorem finrank_thetaRootBlock_reflection (mu : ThetaNonzeroSpectrum) :
    Module.finrank ℂ (ThetaRootBlock (thetaSpectrumNeg mu)) =
      Module.finrank ℂ (ThetaRootBlock mu) := by
  exact (thetaRootBlockReflectionLIE mu).toLinearEquiv.finrank_eq.symm

theorem thetaRootNilpotentPart_reflection (mu : ThetaNonzeroSpectrum)
    (v : ThetaRootBlock mu) :
    thetaRootNilpotentPart (thetaSpectrumNeg mu) (thetaRootBlockReflectionLIE mu v) =
      -thetaRootBlockReflectionLIE mu (thetaRootNilpotentPart mu v) := by
  apply Subtype.ext
  change thetaKernelOperator (thetaQuantileReflection (v : ThetaH)) -
      (-(mu : ℂ)) • thetaQuantileReflection (v : ThetaH) =
    -thetaQuantileReflection (thetaKernelOperator (v : ThetaH) - (mu : ℂ) • (v : ThetaH))
  have hBR : thetaKernelOperator (thetaQuantileReflection (v : ThetaH)) =
      -thetaQuantileReflection (thetaKernelOperator (v : ThetaH)) := by
    have h := congrArg Neg.neg (thetaQuantileReflection_intertwines_neg (v : ThetaH))
    simpa only [neg_neg, neg_apply] using h.symm
  rw [hBR]
  simp only [map_sub, map_smul, neg_smul]
  module

theorem thetaRootNilpotentPart_pow_reflection (mu : ThetaNonzeroSpectrum)
    (j : ℕ) (v : ThetaRootBlock mu) :
    (thetaRootNilpotentPart (thetaSpectrumNeg mu) ^ j)
        (thetaRootBlockReflectionLIE mu v) =
      ((-1 : ℂ) ^ j) • thetaRootBlockReflectionLIE mu
        ((thetaRootNilpotentPart mu ^ j) v) := by
  induction j generalizing v with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, pow_succ]
      change (thetaRootNilpotentPart (thetaSpectrumNeg mu) ^ j)
          (thetaRootNilpotentPart (thetaSpectrumNeg mu)
            (thetaRootBlockReflectionLIE mu v)) = _
      rw [thetaRootNilpotentPart_reflection]
      simp only [map_neg, ih, pow_succ, smul_neg, neg_smul, mul_smul,
        one_smul, Module.End.mul_apply]

/-- Exact depth character of the reflected source conormal current. -/
theorem thetaSourceConormalCurrent_reflection (mu : ThetaNonzeroSpectrum)
    (v : ThetaRootBlock mu) :
    thetaSourceConormalCurrent (thetaSpectrumNeg mu)
        (thetaRootBlockReflectionLIE mu v) =
      ((-1 : ℂ) ^ (Module.finrank ℂ (ThetaRootBlock mu) - 1)) •
        thetaRootBlockReflectionLIE mu (thetaSourceConormalCurrent mu v) := by
  unfold thetaSourceConormalCurrent nilpotentSocleCurrent
  rw [finrank_thetaRootBlock_reflection]
  exact thetaRootNilpotentPart_pow_reflection mu
    (Module.finrank ℂ (ThetaRootBlock mu) - 1) v

/-- At an actual Xi divisor point, reflection acts by parity of analytic multiplicity minus one. -/
theorem thetaSourceConormalCurrent_reflection_at_XiSupport (rho : XiDivisorSupport)
    (v : ThetaRootBlock (thetaSpectrumOfXiSupport rho)) :
    thetaSourceConormalCurrent (thetaSpectrumNeg (thetaSpectrumOfXiSupport rho))
        (thetaRootBlockReflectionLIE (thetaSpectrumOfXiSupport rho) v) =
      ((-1 : ℂ) ^ (xiSupportMultiplicity rho - 1)) •
        thetaRootBlockReflectionLIE (thetaSpectrumOfXiSupport rho)
          (thetaSourceConormalCurrent (thetaSpectrumOfXiSupport rho) v) := by
  simpa only [finrank_thetaRootBlock_at_XiSupport] using
    thetaSourceConormalCurrent_reflection (thetaSpectrumOfXiSupport rho) v

theorem map_ker_thetaRootNilpotentPart_reflection (mu : ThetaNonzeroSpectrum) :
    Submodule.map (thetaRootBlockReflectionLIE mu).toLinearEquiv.toLinearMap
        (LinearMap.ker (thetaRootNilpotentPart mu)) =
      LinearMap.ker (thetaRootNilpotentPart (thetaSpectrumNeg mu)) := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    have hx0 := LinearMap.mem_ker.mp hx
    apply LinearMap.mem_ker.mpr
    change thetaRootNilpotentPart (thetaSpectrumNeg mu)
      (thetaRootBlockReflectionLIE mu x) = 0
    rw [thetaRootNilpotentPart_reflection, hx0]
    simp
  · intro y hy
    let x : ThetaRootBlock mu := (thetaRootBlockReflectionLIE mu).symm y
    have hxy : thetaRootBlockReflectionLIE mu x = y :=
      (thetaRootBlockReflectionLIE mu).apply_symm_apply y
    refine ⟨x, ?_, hxy⟩
    apply LinearMap.mem_ker.mpr
    apply (thetaRootBlockReflectionLIE mu).injective
    rw [map_zero]
    have href := thetaRootNilpotentPart_reflection mu x
    rw [hxy, LinearMap.mem_ker.mp hy] at href
    exact neg_eq_zero.mp href.symm

/-- Functional-equation transport preserves the complete recovered eigenline. -/
theorem map_range_thetaSourceConormalCurrent_reflection (mu : ThetaNonzeroSpectrum) :
    Submodule.map (thetaRootBlockReflectionLIE mu).toLinearEquiv.toLinearMap
        (LinearMap.range (thetaSourceConormalCurrent mu)) =
      LinearMap.range (thetaSourceConormalCurrent (thetaSpectrumNeg mu)) := by
  rw [range_thetaSourceConormalCurrent mu,
    range_thetaSourceConormalCurrent (thetaSpectrumNeg mu),
    map_ker_thetaRootNilpotentPart_reflection]

theorem norm_thetaSourceConormalCurrent_reflection_apply (mu : ThetaNonzeroSpectrum)
    (v : ThetaRootBlock mu) :
    ‖thetaSourceConormalCurrentCLM (thetaSpectrumNeg mu)
        (thetaRootBlockReflectionLIE mu v)‖ =
      ‖thetaSourceConormalCurrentCLM mu v‖ := by
  change ‖thetaSourceConormalCurrent (thetaSpectrumNeg mu)
      (thetaRootBlockReflectionLIE mu v)‖ = ‖thetaSourceConormalCurrent mu v‖
  rw [thetaSourceConormalCurrent_reflection, norm_smul,
    (thetaRootBlockReflectionLIE mu).norm_map]
  simp

theorem norm_thetaSourceConormalCurrentCLM_neg_le (mu : ThetaNonzeroSpectrum) :
    ‖thetaSourceConormalCurrentCLM (thetaSpectrumNeg mu)‖ ≤
      ‖thetaSourceConormalCurrentCLM mu‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
    (thetaSourceConormalCurrentCLM (thetaSpectrumNeg mu))
    (norm_nonneg (thetaSourceConormalCurrentCLM mu))
  intro y
  let x : ThetaRootBlock mu := (thetaRootBlockReflectionLIE mu).symm y
  have hxy : thetaRootBlockReflectionLIE mu x = y :=
    (thetaRootBlockReflectionLIE mu).apply_symm_apply y
  rw [← hxy, norm_thetaSourceConormalCurrent_reflection_apply,
    (thetaRootBlockReflectionLIE mu).norm_map]
  exact (thetaSourceConormalCurrentCLM mu).le_opNorm x

/-- Reflection preserves the full operator norm of the conormal current. -/
theorem norm_thetaSourceConormalCurrentCLM_reflection (mu : ThetaNonzeroSpectrum) :
    ‖thetaSourceConormalCurrentCLM (thetaSpectrumNeg mu)‖ =
      ‖thetaSourceConormalCurrentCLM mu‖ := by
  apply le_antisymm
  · exact norm_thetaSourceConormalCurrentCLM_neg_le mu
  · have h := norm_thetaSourceConormalCurrentCLM_neg_le (thetaSpectrumNeg mu)
    rw [thetaSpectrumNeg_involutive] at h
    exact h

end

end RHTower.HedenmalmThetaSource
