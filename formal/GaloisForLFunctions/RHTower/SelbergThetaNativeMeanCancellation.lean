import GaloisForLFunctions.RHTower.SelbergThetaNativeScalarBoundary
import GaloisForLFunctions.RHTower.SelbergModularHyperbolicArea
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Exact cancellation of the native theta mean residue

The original hyperbolic measure of the modular fundamental domain is `pi/3`.
Its planar slices are evaluated by the existing inverse-square ray primitive
and the arcsine primitive on the curved boundary. The value of zeta at two
identifies this volume with `2*xi(2)`.

Thus the contour residue equals the literal native constant-mode correction.
For every actual Xi copy, the centered source pairing is exactly the admitted
arithmetic Cauchy integral with density `Xi(t)^2*boundaryWeight(t)`.
-/

open Complex Set Filter Topology MeasureTheory UpperHalfPlane
open scoped ENNReal
namespace RHTower.SelbergThetaNativeMeanCancellation
noncomputable section
open GaloisForLFunctions.RHTower.SelbergMaassTraceStokes
open GaloisForLFunctions.RHTower.SelbergModularDomainSlices
open GaloisForLFunctions.RHTower.SelbergMaassFullCurvatureBudget
open GaloisForLFunctions.RHTower.SelbergModularHyperbolicArea
open SelbergThetaHorizontalBoundary SelbergThetaNativeScalarBoundary

private theorem full_weight_integral_eq_arc :
    (∫ p in fullDomain, 1 / p.2 ^ 2) =
      ∫ x in Icc (-(1/2:ℝ)) (1/2), 1 / arcHeight x := by
  have hprod : Integrable (fullDomain.indicator fun p : ℝ × ℝ => 1 / p.2 ^ 2)
      (volume.prod volume) := by
    simpa only [← Measure.volume_eq_prod] using
      full_weight_integrable.integrable_indicator fullDomain_measurable
  rw [← integral_indicator fullDomain_measurable, Measure.volume_eq_prod,
    integral_prod _ hprod, ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ Icc (-(1/2:ℝ)) (1/2)
  · rw [Set.indicator_of_mem hx]
    have he : (fun y : ℝ => fullDomain.indicator (fun p => 1 / p.2 ^ 2) (x,y)) =
        (Ici (arcHeight x)).indicator (fun y : ℝ => 1 / y ^ 2) := by
      funext y
      by_cases hy : arcHeight x ≤ y
      · rw [Set.indicator_of_mem (show (x,y) ∈ fullDomain from ⟨hx,hy⟩),
          Set.indicator_of_mem (show y ∈ Ici (arcHeight x) from hy)]
      · rw [Set.indicator_of_notMem (show (x,y) ∉ fullDomain from fun h => hy h.2),
          Set.indicator_of_notMem (show y ∉ Ici (arcHeight x) from hy)]
    rw [he, integral_indicator measurableSet_Ici, inverse_square_integral (arcHeight_pos hx)]
  · rw [Set.indicator_of_notMem hx]
    have he : (fun y : ℝ => fullDomain.indicator (fun p => 1 / p.2 ^ 2) (x,y)) = 0 := by
      funext y
      exact Set.indicator_of_notMem (show (x,y) ∉ fullDomain from fun h => hx h.1) _
    rw [he]
    exact MeasureTheory.integral_zero (ℝ) (ℝ)

private theorem arc_reciprocal_integral :
    (∫ x in Icc (-(1/2:ℝ)) (1/2), 1 / arcHeight x) = Real.pi / 3 := by
  have hab : -(1/2:ℝ) ≤ 1/2 := by norm_num
  have hc : ContinuousOn (fun x : ℝ => 1 / arcHeight x) (Icc (-(1/2:ℝ)) (1/2)) :=
    continuousOn_const.div continuous_arcHeight.continuousOn
      (fun x hx => (arcHeight_pos hx).ne')
  have hi : IntegrableOn (fun x : ℝ => 1 / arcHeight x) (Icc (-(1/2:ℝ)) (1/2)) :=
    hc.integrableOn_Icc
  have hd : ∀ x ∈ uIcc (-(1/2:ℝ)) (1/2),
      HasDerivAt Real.arcsin (1 / arcHeight x) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact Real.hasDerivAt_arcsin (by linarith [hx.1]) (by linarith [hx.2])
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hi)
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc] at h
  rw [h, Real.arcsin_neg]
  have ha : Real.arcsin (1/2) = Real.pi / 6 := by
    rw [← Real.sin_pi_div_six]
    exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [ha]
  ring

/-- Exact area of the literal full planar modular domain. -/
theorem full_weight_integral_eq_pi_div_three :
    (∫ p in fullDomain, 1 / p.2 ^ 2) = Real.pi / 3 :=
  full_weight_integral_eq_arc.trans arc_reciprocal_integral

private theorem coe_fd_eq_preimage_fullDomain :
    UpperHalfPlane.coe '' ModularGroup.fd =
      Complex.measurableEquivRealProd ⁻¹' fullDomain := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    have hx : w.re ∈ Icc (-(1/2:ℝ)) (1/2) := abs_le.mp hw.2
    refine ⟨hx,?_⟩
    have hs := arcHeight_sq hx
    have hn := hw.1
    change 1 ≤ w.re*w.re+w.im*w.im at hn
    change arcHeight w.re ≤ w.im
    nlinarith [arcHeight_pos hx, w.im_pos]
  · intro hz
    have hz' : z.re ∈ Icc (-(1/2:ℝ)) (1/2) ∧ arcHeight z.re ≤ z.im := hz
    have hy : 0 < z.im := (arcHeight_pos hz'.1).trans_le hz'.2
    refine ⟨⟨z,hy⟩,⟨?_,?_⟩,rfl⟩
    · change 1 ≤ z.re*z.re+z.im*z.im
      have hs := arcHeight_sq hz'.1
      nlinarith [arcHeight_pos hz'.1]
    · exact abs_le.mpr hz'.1

/-- The original invariant modular measure has exact volume `pi/3`. -/
theorem native_volume_fd : (volume : Measure UpperHalfPlane) ModularGroup.fd =
    ENNReal.ofReal (Real.pi/3) := by
  rw [GaloisForLFunctions.HTGeometry.volume_eq_lintegral_ofReal,
    coe_fd_eq_preimage_fullDomain]
  have h := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p : ℝ × ℝ => ENNReal.ofReal (1 / p.2 ^ 2)) fullDomain
  simp only [one_div] at h
  change (∫⁻ z : ℂ in Complex.measurableEquivRealProd ⁻¹' fullDomain,
    ENNReal.ofReal ((z.im ^ 2)⁻¹)) =
    ∫⁻ p : ℝ × ℝ in fullDomain, ENNReal.ofReal ((p.2 ^ 2)⁻¹) at h
  rw [h]
  simp_rw [← one_div]
  rw [← ofReal_integral_eq_lintegral_ofReal full_weight_integrable
    (Eventually.of_forall (fun p : ℝ × ℝ => div_nonneg zero_le_one (sq_nonneg p.2))),
    full_weight_integral_eq_pi_div_three]

/-- Exact norm of the constant vector in the original native Hilbert space. -/
theorem constantVector_inner : inner ℂ SelbergNativeConstantMode.constantVector
    SelbergNativeConstantMode.constantVector = ((Real.pi/3:ℝ):ℂ) := by
  rw [SelbergNativeConstantMode.inner_constantVector,
    integral_congr_ae SelbergNativeConstantMode.constantVector_coe, integral_const]
  simp only [Complex.real_smul, mul_one]
  change (((volume.restrict ModularGroup.fd).real univ):ℂ) = _
  simp [MeasureTheory.measureReal_def, native_volume_fd, ENNReal.toReal_ofReal (div_nonneg Real.pi_pos.le (by norm_num : (0:ℝ) ≤ 3))]

/-- Arithmetic normalization of the volume residue. -/
theorem two_xi_two : 2 * xi 2 = ((Real.pi/3:ℝ):ℂ) := by
  have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hg : Complex.Gammaℝ 2 = (Real.pi:ℂ)⁻¹ := by
    norm_num [Complex.Gammaℝ, Complex.cpow_neg_one]
  have h := riemannZeta_def_of_ne_zero (by norm_num : (2:ℂ) ≠ 0)
  rw [riemannZeta_two, hg, ← xi_two] at h
  push_cast
  field_simp at h ⊢
  linear_combination -h

/-- The contour's constant residue is exactly the native constant-mode projection. -/
theorem mean_residue_cancel (q : XiZeroCopy) :
    2*mainTerm*xi (3/2)/(1+(xiSpectralPoint q)^2) =
      (SelbergThetaNativeSource.sourceMass:ℂ)^2 /
        ((1+(xiSpectralPoint q)^2)*inner ℂ SelbergNativeConstantMode.constantVector
          SelbergNativeConstantMode.constantVector) := by
  rw [mainTerm_eq, sourceMass_eq_xi, constantVector_inner, ← two_xi_two]
  field_simp

/-- Exact native source pairing after cancellation of its constant-mode residue. -/
theorem sourcePairing_eq_cauchy (q : XiZeroCopy) :
    SelbergThetaCommonForcingGram.sourcePairing q =
      (1/(4*(Real.pi:ℂ)))*∫ t : ℝ,
        (Xi t:ℂ)^2*(boundaryWeight t:ℂ)/((t:ℂ)^2-(xiSpectralPoint q)^2) := by
  rw [sourcePairing_cauchy, mean_residue_cancel]
  ring

end
end RHTower.SelbergThetaNativeMeanCancellation
