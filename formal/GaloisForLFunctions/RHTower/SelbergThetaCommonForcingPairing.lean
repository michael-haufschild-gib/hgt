import GaloisForLFunctions.RHTower.SelbergThetaCommonForcingGram
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMStripMeanAdmission
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMHalfRowIntegralInterchange

/-!
# Literal scalar source pairing for the native common theta forcing

The complete positive theta field has a global bound by modular reduction. This admits
absolute primitive-row unfolding of its product with every actual common-forcing response.
Strip Fubini gives one fixed strictly positive horizontal weight, independent of the Xi copy.
The resulting height integral equals the actual native Hilbert pairing. True constant-mode
centering retains its exact finite-volume correction.

This identifies the scalar input to the native Gram displacement law. It does not assert
that the complex response has a sign, or construct normalized packets with vanishing residual.
-/

open Complex Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped ComplexConjugate ContDiff
open GaloisForLFunctions.HTGeometry
set_option autoImplicit false
namespace RHTower.SelbergThetaCommonForcingPairing
open D4BMModularCore D4BMJointSource D4BMGlobalAngularResponse
open SelbergThetaNativeSource SelbergThetaCommonForcing SelbergNativeConstantMode
noncomputable section

/-- The complete positive theta field is bounded on every modular translate. -/
theorem positiveSource_globally_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, positiveSource z ≤ C := by
  obtain ⟨C,hC,hb⟩ := positiveSource_bounded
  refine ⟨C,hC,fun z => ?_⟩
  obtain ⟨g,hg⟩ := exists_smul_mem_fd z
  have he := positiveSource_invariant (QuotientGroup.mk g) z
  exact he ▸ hb (g • z) hg

private theorem height_continuous (q : XiZeroCopy) :
    Continuous (fun z : UpperHalfPlane => heightProfile q z.im) := by
  apply Continuous.mul
  · exact Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp ((UpperHalfPlane.continuous_im.log (fun z => z.im_ne_zero)).div_const 2))
  · exact (continuous_iff_continuousAt.mpr (fun x => (profile_hasDerivAt q x).continuousAt)).comp
      ((UpperHalfPlane.continuous_im.log (fun z => z.im_ne_zero)).div_const 2)

private theorem height_strip_integrable (q : XiZeroCopy) :
    IntegrableOn (fun z : UpperHalfPlane => heightProfile q z.im) modularStrip volume := by
  obtain ⟨C,_,hC⟩ := heightProfile_power_bound q 2
  obtain ⟨D,_,hD⟩ := heightProfile_power_bound q 0
  apply modularStrip_integrable_of_two_bounds _ (height_continuous q) 2 C D (by norm_num)
  · intro z _ _
    exact hC z.im z.im_pos
  · intro z _ _
    simpa using hD z.im z.im_pos

private def seedProduct (q : XiZeroCopy) (z : UpperHalfPlane) : ℂ :=
  heightProfile q z.im * (positiveSource z:ℂ)

private theorem product_strip_integrable (q : XiZeroCopy) :
    IntegrableOn (seedProduct q) modularStrip volume := by
  obtain ⟨C,_,hC⟩ := positiveSource_globally_bounded
  apply (height_strip_integrable q).mul_bdd (c := C)
    (Complex.continuous_ofReal.measurable.comp positiveSource_measurable).aestronglyMeasurable.restrict
  apply Eventually.of_forall
  intro z
  change ‖(positiveSource z:ℂ)‖ ≤ C
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (positiveSource_pos z)] using hC z

private theorem seedProduct_periodic (q : XiZeroCopy) (n : ℤ) (z : UpperHalfPlane) :
    seedProduct q (ModularGroup.T^n • z) = seedProduct q z := by
  change heightProfile q (ModularGroup.T^n • z).im * _ = _
  rw [im_T_zpow_smul]
  congr 1
  exact congrArg Complex.ofReal (positiveSource_invariant (QuotientGroup.mk (ModularGroup.T^n)) z)

private theorem seedProduct_rows (q : XiZeroCopy) (z : UpperHalfPlane) :
    (∑' v : gammaSetHalf, seedProduct q (gammaSetMatrix v.1 • z)) =
      source q z * (positiveSource z:ℂ) := by
  have he (v : gammaSetHalf) : positiveSource (gammaSetMatrix v.1 • z) = positiveSource z :=
    positiveSource_invariant (QuotientGroup.mk (gammaSetMatrix v.1)) z
  unfold seedProduct
  simp_rw [he]
  rw [tsum_mul_right,← source_eq_rows]

/-- Absolute unfolding retains every primitive row of the actual common-forcing response. -/
private theorem source_positive_pairing_unfold (q : XiZeroCopy) :
    (∫ z, source q z * (positiveSource z:ℂ) ∂angularMeasure) =
      ∫ z in modularStrip, seedProduct q z := by
  have he := modularStrip_integral_halfRow_sum _ (seedProduct_periodic q)
    (product_strip_integrable q)
  simpa only [seedProduct_rows] using! he

/-- The fixed positive theta source, averaged over the complete horizontal period. -/
def horizontalWeight (y : ℝ) : ℝ :=
  ∫ x in Ico (0:ℝ) 1, positiveSource (ofComplex (⟨x,y⟩:ℂ))

private theorem horizontal_integrable (y : ℝ) :
    IntegrableOn (fun x : ℝ => positiveSource (ofComplex (⟨x,y⟩:ℂ))) (Ico (0:ℝ) 1) := by
  obtain ⟨C,_,hC⟩ := positiveSource_globally_bounded
  have hm : Measurable (fun x : ℝ => positiveSource (ofComplex (⟨x,y⟩:ℂ))) :=
    positiveSource_measurable.comp
      (cuspStripPoint_measurable.comp (measurable_const.prodMk measurable_id))
  apply (integrable_const C).mono' hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  exact (Real.norm_eq_abs _).trans_le (by rw [abs_of_pos (positiveSource_pos _)]; exact hC _)

/-- This scalar weight is strictly positive at every height, before any Xi parameter is chosen. -/
theorem horizontalWeight_pos (y : ℝ) : 0 < horizontalWeight y := by
  unfold horizontalWeight
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall (fun x => (positiveSource_pos _).le)) (horizontal_integrable y)]
  have hs : Function.support (fun x : ℝ => positiveSource (ofComplex (⟨x,y⟩:ℂ))) = univ := by
    ext x
    simp [Function.mem_support, (positiveSource_pos _).ne']
  rw [hs,univ_inter]
  simp

/-- One positive, parameter-independent height weight controls the full scalar theta response. -/
def scalarResponse (q : XiZeroCopy) : ℂ :=
  ∫ y in Ioi (0:ℝ), (y^(2 : ℕ))⁻¹ • (heightProfile q y * (horizontalWeight y:ℂ))

private theorem point_im (x y : ℝ) (hy : 0 < y) :
    (ofComplex (⟨x,y⟩:ℂ)).im = y := by
  rw [ofComplex_apply_of_im_pos hy]
  rfl

/-- The displayed scalar integral is absolutely admitted in the original height measure. -/
theorem scalarResponse_integrable (q : XiZeroCopy) :
    IntegrableOn (fun y : ℝ => (y^(2 : ℕ))⁻¹ •
      (heightProfile q y * (horizontalWeight y:ℂ))) (Ioi (0:ℝ)) := by
  have hi := (integrableOn_modularStrip_iff _).mp (product_strip_integrable q)
  rw [Measure.volume_eq_prod,IntegrableOn,← Measure.prod_restrict] at hi
  have hj : IntegrableOn (fun y : ℝ => ∫ x in Ico (0:ℝ) 1,
      stripChartIntegrand (seedProduct q) (y,x)) (Ioi (0:ℝ)) := hi.integral_prod_left
  apply hj.congr_fun _ measurableSet_Ioi
  intro y hy
  dsimp only [stripChartIntegrand,seedProduct]
  simp_rw [point_im _ _ hy]
  rw [integral_smul,integral_const_mul,integral_complex_ofReal]
  rfl

/-- The native source pairing is the literal positive-weight scalar response. -/
theorem source_positive_pairing_eq_scalarResponse (q : XiZeroCopy) :
    (∫ z, source q z * (positiveSource z:ℂ) ∂angularMeasure) = scalarResponse q := by
  rw [source_positive_pairing_unfold, setIntegral_modularStrip_eq_iterated _
    (product_strip_integrable q)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  unfold seedProduct
  simp_rw [point_im _ _ hy]
  rw [integral_const_mul,integral_complex_ofReal]
  rfl

private theorem nativeSource_coe (q : XiZeroCopy) :
    (nativeSource q : UpperHalfPlane → ℂ) =ᵐ[angularMeasure] source q :=
  (source_memLp q).coeFn_toLp

private theorem nativePositive_coe :
    (nativePositive : UpperHalfPlane → ℂ) =ᵐ[angularMeasure] (fun z => (positiveSource z:ℂ)) :=
  positiveSource_memLp.ofReal.coeFn_toLp

/-- Exact native Hilbert pairing, including all modular rows. -/
theorem nativePositive_inner_source (q : XiZeroCopy) :
    inner ℂ nativePositive (nativeSource q) = scalarResponse q := by
  rw [L2.inner_def]
  apply Eq.trans _ (source_positive_pairing_eq_scalarResponse q)
  apply integral_congr_ae
  filter_upwards [nativePositive_coe,nativeSource_coe q] with z hp hq
  simp [hp,hq]

private theorem constant_source_inner (q : XiZeroCopy) :
    inner ℂ constantVector (nativeSource q) = (sourceMass:ℂ)/(1+(xiSpectralPoint q)^(2 : ℕ)) := by
  rw [inner_constantVector,integral_congr_ae (nativeSource_coe q),source_integral]

private theorem constant_positive_inner :
    inner ℂ constantVector nativePositive = (sourceMass:ℂ) := by
  rw [inner_constantVector,integral_congr_ae nativePositive_coe,
    integral_complex_ofReal,positiveSource_integral]

private theorem positive_constant_inner :
    inner ℂ nativePositive constantVector = (sourceMass:ℂ) := by
  rw [← inner_conj_symm,constant_positive_inner,Complex.conj_ofReal]

/-- Full native scalar pairing with the true constant-mode correction. -/
theorem sourcePairing_eq_scalarResponse (q : XiZeroCopy) :
    SelbergThetaCommonForcingGram.sourcePairing q =
      -(1/4:ℂ) * (scalarResponse q -
        (sourceMass:ℂ)^(2 : ℕ) / ((1+(xiSpectralPoint q)^(2 : ℕ)) * inner ℂ constantVector constantVector)) := by
  have hz : inner ℂ constantVector (centered (nativeSource q)) = 0 := by
    rw [inner_constantVector,integral_centered]
  unfold SelbergThetaCommonForcingGram.sourcePairing SelbergThetaCommonForcingGram.forcing
    SelbergThetaCommonForcingGram.vector
  rw [centeredDomain_coe,inner_smul_left]
  norm_num only [map_neg,map_div₀,map_one,map_ofNat]
  rw [show inner ℂ (centered nativePositive) (centered (nativeSource q)) =
      inner ℂ nativePositive (centered (nativeSource q)) by
    rw [centered,inner_sub_left,constantComponent,inner_smul_left,hz,mul_zero,sub_zero]]
  rw [centered,inner_sub_right,constantComponent,inner_smul_right,
    nativePositive_inner_source,constant_source_inner,positive_constant_inner]
  congr 2
  field_simp

end
end RHTower.SelbergThetaCommonForcingPairing
