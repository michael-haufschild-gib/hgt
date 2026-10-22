import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspFieldIntegral
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCutoffPowerFlux
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCompleteAngularSourceProjection

/-! Exact reduction of the full scalar-field cutoff period with the original hyperbolic measure. -/
open Set Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMGlobalAngularResponse D4BMAngularSeries D4BMCuspProjection D4BMModularCore
noncomputable section

/-- The full scalar field has exactly its two original Weyl powers as horizontal mean. -/
theorem mean_scalar (u : ℂ) {y : ℝ} (hy : 0 < y) :
    mean (fun x => scalar u ![x,y]) = principal u ![0,y] := by
  have ht : Continuous (fun x : ℝ => tail u ![x,y]) :=
    (cuspTailPart_contDiffOn .scalar u).continuousOn.comp_continuous (by fun_prop) (fun _ => hy)
  change (∫ x in Ioc (-1/2:ℝ) (1/2), principal u ![0,y]+tail u ![x,y]) = _
  rw [integral_add (integrable_const _) ht.integrableOn_Ioc]
  change (∫ _x in Ioc (-1/2:ℝ) (1/2), principal u ![0,y])+mean (fun x => tail u ![x,y]) = _
  rw [mean_tail u hy]
  norm_num

/-- Exact full-field horizontal pairing, with every nonconstant Fourier mode integrated. -/
theorem mean_scalar_cutoffCommutator (u k : ℂ) {y : ℝ} (hy : 0 < y) :
    mean (fun x => scalar u ![x,y]*cutoffCommutator k ![x,y]) =
      principal u ![0,y]*cutoffCommutator k ![0,y] := by
  have he (x : ℝ) : cutoffCommutator k ![x,y] = cutoffCommutator k ![0,y] := by
    rw [cutoffCommutator_height,cutoffCommutator_height]
    rfl
  simp_rw [he]
  change (∫ x in Ioc (-1/2:ℝ) (1/2), scalar u ![x,y]*cutoffCommutator k ![0,y]) = _
  rw [integral_mul_const]
  change mean (fun x => scalar u ![x,y])*cutoffCommutator k ![0,y] = _
  rw [mean_scalar u hy]

/-- The original modular integral is exactly the finite transition-strip integral. -/
theorem scalarCutoffPeriod_eq_strip (u k : ℂ) :
    scalarCutoffPeriod u k = ∫ y in (1:ℝ)..4,
      principal u ![0,y]*cutoffCommutator k ![0,y]/(y:ℂ)^(2 : ℕ) := by
  let F (z : ℂ) := scalar u ![z.re,z.im]*cutoffCommutator k ![z.re,z.im]
  have hi : Integrable (fun z : UpperHalfPlane => F z) measure :=
    scalar_cutoffCommutator_integrable u k
  have hz (z : ℂ) (hz : z.im ≤ 1) : F z = 0 := by
    dsimp [F]
    rw [cutoffCommutator_low k ![z.re,z.im] (by change z.im < 2; linarith),mul_zero]
  have h := integral_cusp_field_from 1 (by norm_num) F hi hz
  change scalarCutoffPeriod u k = _ at h
  rw [h]
  have he : (∫ y in Ioi (1:ℝ), mean (fun x => F (Complex.measurableEquivRealProd.symm (x,y)))/(y:ℂ)^(2 : ℕ)) =
      ∫ y in Ioi (1:ℝ), principal u ![0,y]*cutoffCommutator k ![0,y]/(y:ℂ)^(2 : ℕ) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    change mean (fun x => scalar u ![x,y]*cutoffCommutator k ![x,y])/(y:ℂ)^(2 : ℕ) = _
    rw [mean_scalar_cutoffCommutator u k (by change 1<y at hy; linarith)]
  rw [he,intervalIntegral.integral_of_le (show (1:ℝ)≤4 by norm_num)]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (show Ioc (1:ℝ) 4 ⊆ Ioi 1 from fun y hy => hy.1)
  intro y hy
  have h4 : 4 < y := by
    by_contra hn
    exact hy.2 ⟨hy.1,le_of_not_gt hn⟩
  rw [cutoffCommutator_high k ![0,y] (by change 3<y; linarith),mul_zero,zero_div]

/-- Both original Weyl coefficients multiply actual cutoff moments; no Fourier term is omitted. -/
theorem scalarCutoffPeriod_eq_moments (u k : ℂ) :
    scalarCutoffPeriod u k =
      d4BMCompletedEisensteinCuspConstantCoefficient u false*
        cutoffPowerMoment (d4BMCompletedEisensteinCuspWeylExponent u false) k+
      d4BMCompletedEisensteinCuspConstantCoefficient u true*
        cutoffPowerMoment (d4BMCompletedEisensteinCuspWeylExponent u true) k := by
  let dm := d4BMCompletedEisensteinCuspWeylExponent u false
  let dp := d4BMCompletedEisensteinCuspWeylExponent u true
  let cm := d4BMCompletedEisensteinCuspConstantCoefficient u false
  let cp := d4BMCompletedEisensteinCuspConstantCoefficient u true
  rw [scalarCutoffPeriod_eq_strip]
  have he : (∫ y in (1:ℝ)..4, principal u ![0,y]*cutoffCommutator k ![0,y]/(y:ℂ)^(2 : ℕ)) =
      ∫ y in (1:ℝ)..4, cm*((y:ℂ)^(dm-2)*cutoffCommutator k ![0,y])+
        cp*((y:ℂ)^(dp-2)*cutoffCommutator k ![0,y]) := by
    apply intervalIntegral.integral_congr
    intro y hy
    dsimp only
    have hp : 0 < y := by
      norm_num only [uIcc_of_le (show (1:ℝ)≤4 by norm_num),mem_Icc] at hy
      linarith [hy.1]
    have hn : (y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
    have htwo : (y:ℂ)^(2:ℂ) = (y:ℂ)^(2 : ℕ) := by norm_cast
    rw [Complex.cpow_sub dm 2 hn,Complex.cpow_sub dp 2 hn]
    rw [htwo]
    dsimp [D4BMGlobalAngularResponse.principal,d4BMCompletedEisensteinCuspConstantPart,d4BMCompletedEisensteinCuspConstantTerm,
      d4BMCompletedEisensteinCuspConstantMaassFactor,dm,dp,cm,cp]
    ring
  rw [he,intervalIntegral.integral_add
    ((cutoffPowerSource_intervalIntegrable dm k).const_mul cm)
    ((cutoffPowerSource_intervalIntegrable dp k).const_mul cp),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  rfl

end
end RHTower.D4BMJointSource
