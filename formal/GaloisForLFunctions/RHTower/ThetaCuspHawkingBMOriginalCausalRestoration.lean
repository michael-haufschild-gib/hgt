import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalScalarRestoration
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCuspJets
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalWeightedAngularData

/-!
Scalar height restoration of the complete original causal potential.

The original cusp-jet theorem controls the height-weighted cutoff residual
uniformly in horizontal position. Compactness of the actual truncated modular
cell supplies the remaining bound. Pairing with the original inverse-height
physical reader proves absolute admission without an extra hypothesis.

The literal height-truncated original potential consequently has its exact
finite part: native causal residual period minus all three transported
principal corrections, plus the original onset lift times the physical source
coefficient. Both source branches and all nonnegative null targets remain.
No temporal, horizon or QNM limit interchange is asserted.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMOriginalCausalRestoration
open D4BMGlobalAngularResponse D4BMJointSource D4BMModularCore D4BMLaplaceRadial
open D4BMOriginalScalarRestoration D4BMOriginalCausalPotential D4BMNativeResponse
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace


private theorem coordinates_continuous : Continuous coordinates := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact UpperHalfPlane.continuous_re
  · exact UpperHalfPlane.continuous_im

private theorem scalar_continuous (u : ℂ) :
    Continuous (fun z : UpperHalfPlane => scalar u (coordinates z)) :=
  (D4BMAngularSeries.cuspLeg_contDiffOn .scalar u).continuousOn.comp_continuous
    coordinates_continuous (fun z => z.im_pos)

private theorem cutoffPower_continuous (k : ℂ) :
    Continuous (fun z : UpperHalfPlane => cutoffPower k (coordinates z)) := by
  have hp : Continuous (fun z : UpperHalfPlane => (z.im:ℂ)^k) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr z.im_pos.ne')).comp
      UpperHalfPlane.continuous_im.continuousAt
  exact (sourceCutoff_smooth.continuous.comp coordinates_continuous).mul hp

/-- The complete original causal potential after its own three cutoff powers,
including all principal amplitudes from the unchanged onset lift. -/
def originalCutoffResidual (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p r : ℝ)
    (z : UpperHalfPlane) : ℂ :=
  originalPotential q branch amp p r z.re (Real.log z.im)-
    ∑ i : Fin 3, D4BMOriginalCuspJets.coefficient q branch amp p r i*
      cutoffPower (principalExponent q i) (coordinates z)

private theorem original_continuous (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p r : ℝ) :
    Continuous (fun z : UpperHalfPlane => originalPotential q branch amp p r z.re (Real.log z.im)) := by
  have hc : Continuous (fun z : UpperHalfPlane => (z.re,Real.log z.im)) :=
    UpperHalfPlane.continuous_re.prodMk (UpperHalfPlane.continuous_im.log (fun z => z.im_pos.ne'))
  have hf := (originalPotential_angular_smooth q branch amp p r).continuous
  have h := hf.comp hc
  convert! h using 1

private theorem cutoffResidual_continuous (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p r : ℝ) :
    Continuous (originalCutoffResidual q branch amp p r) := by
  apply (original_continuous q branch amp p r).sub
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul (cutoffPower_continuous (principalExponent q i))

private theorem cutoffResidual_high (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p r : ℝ)
    (z : UpperHalfPlane) (hy : 3 ≤ z.im) :
    originalCutoffResidual q branch amp p r z =
      D4BMOriginalCuspJets.remainder q branch amp p r ![z.re,Real.log z.im] := by
  have he (i : Fin 3) : cutoffPower (principalExponent q i) (coordinates z) =
      Complex.exp (principalExponent q i*(Real.log z.im:ℂ)) := by
    change (Real.smoothTransition (z.im-2):ℂ)*(z.im:ℂ)^principalExponent q i = _
    rw [Real.smoothTransition.one_of_one_le (by linarith),Complex.ofReal_one,one_mul,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr z.im_pos.ne'),
      ← Complex.ofReal_log z.im_pos.le]
    congr 1
    ring
  simp only [originalCutoffResidual,D4BMOriginalCuspJets.remainder,D4BMOriginalCuspJets.principal,
    Matrix.cons_val,he]

/-- Height-weighted admission follows from the original causal cusp estimates,
with the finite modular core retained and no supplied residual-admission premise. -/
theorem originalCutoffResidual_height_memLp (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r : Ici (0:ℝ)) :
    MemLp (fun z : UpperHalfPlane => (z.im:ℂ)*originalCutoffResidual q branch amp p r z) 2 measure := by
  have hu := D4BMOriginalCuspJets.original_remainder_jet_uniform q branch amp p r [] 1
    ⟨1,by norm_num⟩
  obtain ⟨K,hK⟩ := eventually_atTop.mp hu
  let M := max 4 (Real.exp K)
  have hc : Continuous (fun z : UpperHalfPlane => (z.im:ℂ)*originalCutoffResidual q branch amp p r z) :=
    (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).mul
      (cutoffResidual_continuous q branch amp p r)
  obtain ⟨C,hC⟩ := (truncated_cell_compact M).exists_bound_of_continuousOn hc.continuousOn
  apply MemLp.of_bound hc.aestronglyMeasurable (max C 1)
  filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
  by_cases hy : z.im ≤ M
  · exact (hC z ⟨hz,hy⟩).trans (le_max_left _ _)
  · have hM : M < z.im := lt_of_not_ge hy
    have hy3 : 3 ≤ z.im := by have := le_max_left (4:ℝ) (Real.exp K); dsimp [M] at hM; linarith
    have hlog : K ≤ Real.log z.im := by
      apply Real.exp_le_exp.mp
      rw [Real.exp_log z.im_pos]
      exact (le_max_right _ _).trans hM.le
    have hb := hK (Real.log z.im) hlog z.re
    simp only [one_mul,D4BMSquareCuspJets.coordinateJet] at hb
    change ‖Complex.exp (Real.log z.im:ℂ)*
      D4BMOriginalCuspJets.remainder q branch amp p r ![z.re,Real.log z.im]‖ < 1 at hb
    rw [← Complex.ofReal_exp,Real.exp_log z.im_pos,← cutoffResidual_high q branch amp p r z hy3] at hb
    exact hb.le.trans (le_max_right _ _)

/-- The complete original cutoff residual pairs absolutely with the unchanged physical reader. -/
theorem originalCutoffResidual_scalar_integrable (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r : Ici (0:ℝ)) :
    Integrable (fun z : UpperHalfPlane => scalar (physicalAngularParameter q) (coordinates z)*
      originalCutoffResidual q branch amp p r z) measure := by
  have h := (physicalDualDensity_memLp q).integrable_mul
    (originalCutoffResidual_height_memLp q branch amp p r)
  apply h.congr
  filter_upwards with z
  change ((z.im:ℂ)⁻¹*scalar (physicalAngularParameter q) (coordinates z))*
    ((z.im:ℂ)*originalCutoffResidual q branch amp p r z) = _
  field_simp [Complex.ofReal_ne_zero.mpr z.im_pos.ne']

/-- Literal height restoration of an integrable residual plus the original three cutoff powers. -/
theorem integrable_residual_restoration (q : XiZeroCopy) (R : UpperHalfPlane → ℂ) (b : Fin 3 → ℂ)
    (hR : Integrable (fun z => scalar (physicalAngularParameter q) (coordinates z)*R z) measure) :
    Tendsto (fun Y => truncatedIntegral (fun z => scalar (physicalAngularParameter q) (coordinates z)*
      (R z+∑ i : Fin 3, b i*cutoffPower (principalExponent q i) (coordinates z))) Y-
        principalCounterterm q b Y) atTop
      (𝓝 ((∫ z, scalar (physicalAngularParameter q) (coordinates z)*R z ∂measure)-
        ∑ i : Fin 3, scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)/
          physicalAngularGap q q i*b i)) := by
  have he : (fun Y => truncatedIntegral (fun z => scalar (physicalAngularParameter q) (coordinates z)*
      (R z+∑ i : Fin 3, b i*cutoffPower (principalExponent q i) (coordinates z))) Y-
        principalCounterterm q b Y) =ᶠ[atTop]
      (fun Y => truncatedIntegral (fun z => scalar (physicalAngularParameter q) (coordinates z)*R z) Y-
        ∑ i : Fin 3, scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)/
          physicalAngularGap q q i*b i) := by
    filter_upwards [eventually_ge_atTop (4:ℝ)] with Y hY
    have hp (i : Fin 3) : IntegrableOn (fun z : UpperHalfPlane => scalar (physicalAngularParameter q) (coordinates z)*
        cutoffPower (principalExponent q i) (coordinates z)) {z : UpperHalfPlane | z.im ≤ Y} measure :=
      truncated_integrable _ ((scalar_continuous (physicalAngularParameter q)).mul
        (cutoffPower_continuous (principalExponent q i))) Y
    have hs := principal_sum_restoration q b Y hY
    have hv (z : UpperHalfPlane) : scalar (physicalAngularParameter q) (coordinates z)*
        (R z+∑ i : Fin 3, b i*cutoffPower (principalExponent q i) (coordinates z)) =
      scalar (physicalAngularParameter q) (coordinates z)*R z+
        ∑ i : Fin 3, b i*(scalar (physicalAngularParameter q) (coordinates z)*cutoffPower (principalExponent q i) (coordinates z)) := by
      rw [mul_add,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hi : truncatedIntegral (fun z => scalar (physicalAngularParameter q) (coordinates z)*
        (R z+∑ i : Fin 3, b i*cutoffPower (principalExponent q i) (coordinates z))) Y =
      truncatedIntegral (fun z => scalar (physicalAngularParameter q) (coordinates z)*R z) Y+
        ∑ i : Fin 3, b i*truncatedIntegral (fun z => scalar (physicalAngularParameter q) (coordinates z)*
          cutoffPower (principalExponent q i) (coordinates z)) Y := by
      unfold truncatedIntegral
      simp_rw [hv]
      rw [integral_add hR.integrableOn (integrable_finsetSum (Finset.univ : Finset (Fin 3))
        (fun i _ => (hp i).const_mul (b i))),
        integral_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ => (hp i).const_mul (b i))]
      simp_rw [integral_const_mul]
    rw [hi]
    linear_combination hs
  exact ((truncatedIntegral_tendsto _ hR).sub_const _).congr' he.symm

/-- Height finite part of the complete original causal potential, with admission proved from its own jets. -/
theorem original_causal_finitePart (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p r : Ici (0:ℝ)) :
    Tendsto (fun Y => truncatedIntegral (fun z => scalar (physicalAngularParameter q) (coordinates z)*
      originalPotential q branch amp p r z.re (Real.log z.im)) Y-
      principalCounterterm q (D4BMOriginalCuspJets.coefficient q branch amp p r) Y) atTop
      (𝓝 ((∫ z, scalar (physicalAngularParameter q) (coordinates z)*
        originalCutoffResidual q branch amp p r z ∂measure)-
        ∑ i : Fin 3, scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)/
          physicalAngularGap q q i*D4BMOriginalCuspJets.coefficient q branch amp p r i)) := by
  have h := integrable_residual_restoration q (originalCutoffResidual q branch amp p r)
    (D4BMOriginalCuspJets.coefficient q branch amp p r)
    (originalCutoffResidual_scalar_integrable q branch amp p r)
  have he (z : UpperHalfPlane) : originalCutoffResidual q branch amp p r z+
      (∑ i : Fin 3, D4BMOriginalCuspJets.coefficient q branch amp p r i*
        cutoffPower (principalExponent q i) (coordinates z)) =
      originalPotential q branch amp p r z.re (Real.log z.im) := by
    unfold originalCutoffResidual
    ring
  simpa only [he] using h

/-- The full cutoff residual is exactly the native causal residual plus the original lifted square residual. -/
theorem originalCutoffResidual_decomposition (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r : ℝ) (z : UpperHalfPlane) :
    originalCutoffResidual q branch amp p r z =
      fullNullResidual q (physicalRate q branch) amp p r z.re (Real.log z.im)+
        nullLift (physicalRate q branch) amp p r*squareResidual q (coordinates z) := by
  have hs : cutoff (coordinates z)*principalSquare q (coordinates z) =
      ∑ i : Fin 3, principalAmplitude q i*cutoffPower (principalExponent q i) (coordinates z) := by
    rw [principalSquare_expansion q _ z.im_pos,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [cutoffPower]
    ring
  simp only [originalCutoffResidual,originalPotential,D4BMOriginalCausalPotential.sourceProfile,fullNullResidual,
    Real.exp_log z.im_pos,D4BMOriginalCuspJets.coefficient,add_mul,Finset.sum_add_distrib,
    squareResidual]
  change _ = _+nullLift (physicalRate q branch) amp p r*
    (fullSquarePotential q (coordinates z)-cutoff (coordinates z)*principalSquare q (coordinates z))
  rw [hs]
  simp only [coordinates,mul_assoc,← Finset.mul_sum]
  ring

/-- The literal native causal residual pairs absolutely with the original physical scalar. -/
theorem original_nativeResidual_scalar_integrable (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r : Ici (0:ℝ)) :
    Integrable (fun z : UpperHalfPlane => scalar (physicalAngularParameter q) (coordinates z)*
      fullNullResidual q (physicalRate q branch) amp p r z.re (Real.log z.im)) measure := by
  have h := (originalCutoffResidual_scalar_integrable q branch amp p r).sub
    ((scalar_squareResidual_integrable q (physicalAngularParameter q)).const_mul
      (nullLift (physicalRate q branch) amp p r))
  apply h.congr
  filter_upwards with z
  change scalar (physicalAngularParameter q) (coordinates z)*originalCutoffResidual q branch amp p r z-
    nullLift (physicalRate q branch) amp p r*(scalar (physicalAngularParameter q) (coordinates z)*
      squareResidual q (coordinates z)) = _
  rw [originalCutoffResidual_decomposition]
  ring

/-- Full original scalar restoration: native residual, all transported principal channels,
and the complete onset lift have their exact source-determined coefficients. -/
theorem original_causal_restoration (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p r : Ici (0:ℝ)) :
    Tendsto (fun Y => truncatedIntegral (fun z => scalar (physicalAngularParameter q) (coordinates z)*
      originalPotential q branch amp p r z.re (Real.log z.im)) Y-
      principalCounterterm q (D4BMOriginalCuspJets.coefficient q branch amp p r) Y) atTop
      (𝓝 ((∫ z, scalar (physicalAngularParameter q) (coordinates z)*
        fullNullResidual q (physicalRate q branch) amp p r z.re (Real.log z.im) ∂measure)-
        (∑ i : Fin 3, scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)/
          physicalAngularGap q q i*principalNullResponse q (physicalRate q branch) amp i p r)+
        nullLift (physicalRate q branch) amp p r*physicalSelfSourceCoefficient q)) := by
  have hi : (∫ z, scalar (physicalAngularParameter q) (coordinates z)*
      originalCutoffResidual q branch amp p r z ∂measure) =
    (∫ z, scalar (physicalAngularParameter q) (coordinates z)*
      fullNullResidual q (physicalRate q branch) amp p r z.re (Real.log z.im) ∂measure)+
      nullLift (physicalRate q branch) amp p r*scalarResidualPeriod q (physicalAngularParameter q) := by
    simp_rw [originalCutoffResidual_decomposition,mul_add,
      show ∀ z : UpperHalfPlane, scalar (physicalAngularParameter q) (coordinates z)*
        (nullLift (physicalRate q branch) amp p r*squareResidual q (coordinates z)) =
        nullLift (physicalRate q branch) amp p r*(scalar (physicalAngularParameter q) (coordinates z)*
          squareResidual q (coordinates z)) by intro z; ring]
    rw [integral_add (original_nativeResidual_scalar_integrable q branch amp p r)
      ((scalar_squareResidual_integrable q (physicalAngularParameter q)).const_mul _),integral_const_mul]
    rfl
  have hs : (∑ i : Fin 3, scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)/
      physicalAngularGap q q i*D4BMOriginalCuspJets.coefficient q branch amp p r i) =
    (∑ i : Fin 3, scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)/
      physicalAngularGap q q i*principalNullResponse q (physicalRate q branch) amp i p r)+
    nullLift (physicalRate q branch) amp p r*(∑ i : Fin 3,
      scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)*principalAmplitude q i/physicalAngularGap q q i) := by
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold D4BMOriginalCuspJets.coefficient
    ring
  have h := original_causal_finitePart q branch amp p r
  rw [hi,hs] at h
  convert! h using 1
  congr 1
  unfold physicalSelfSourceCoefficient
  ring

end
end RHTower.D4BMOriginalCausalRestoration
