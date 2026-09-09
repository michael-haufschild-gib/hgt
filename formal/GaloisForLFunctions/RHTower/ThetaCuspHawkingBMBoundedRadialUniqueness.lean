import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceHorizonModeLimits
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourcePrincipalWavePotential
import GaloisForLFunctions.HTGeometry.NegativeWronskianUniqueness
import GaloisForLFunctions.HTGeometry.NegativeRayBoundedDerivative

/-! The original radial equation determines bounded zero-trace solutions without a supplied derivative bound. -/
open Complex Set Filter Topology
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- A bounded homogeneous defect with the original zero trace vanishes; its derivative bound is derived internally. -/
theorem bounded_radial_homogeneous_eq_zero {w chi : ℂ} (hc : Chamber w chi)
    {f g : ℝ → ℂ}
    (hf : ∀ t < 0, HasDerivAt f (g t) t)
    (hg : ∀ t < 0, HasDerivAt g ((w^2+(horizonCoordinate t:ℂ)*(1/4+chi^2))*f t) t)
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ t < 0, ‖f t‖ ≤ C)
    (hzero : Tendsto f (𝓝[<] (0:ℝ)) (𝓝 0)) : ∀ t < 0, f t = 0 := by
  let Q : ℝ → ℂ := fun t => w^2+(horizonCoordinate t:ℂ)*(1/4+chi^2)
  have hfc : ContinuousOn f (Iio (0:ℝ)) :=
    fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hqc : ContinuousOn Q (Iio (0:ℝ)) := by
    exact (continuous_const.add
      ((Complex.continuous_ofReal.comp horizonCoordinate_continuous).mul continuous_const)).continuousOn
  obtain ⟨C,hC,hCbound⟩ := hb
  have hQ (t : ℝ) : ‖Q t‖ ≤ ‖w‖^2+‖1/4+chi^2‖ := by
    have hh : ‖(horizonCoordinate t:ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real,Real.norm_of_nonneg (horizonCoordinate_nonneg t)]
      exact horizonCoordinate_le_one t
    apply (norm_add_le _ _).trans
    rw [norm_pow,norm_mul]
    exact add_le_add_right (mul_le_of_le_one_left (norm_nonneg _) hh) _
  have hgb : ∃ D : ℝ, 0 ≤ D ∧ ∀ t < -1, ‖g t‖ ≤ D := by
    let M := (‖w‖^2+‖1/4+chi^2‖)*C
    refine ⟨4*C+M,by dsimp [M]; positivity,fun t ht => ?_⟩
    apply norm_complex_deriv_le_of_bounded_negative hf hg (hqc.mul hfc) hCbound ?_ t (by linarith)
    intro x hx
    rw [norm_mul]
    exact mul_le_mul (hQ x) (hCbound x hx) (norm_nonneg _) (by positivity)
  have hm (outer : Bool) (t : ℝ) (ht : t < 0) :
      HasDerivAt (tortoiseMode outer w chi) (tortoiseModeFirst outer w chi t) t ∧
        HasDerivAt (tortoiseModeFirst outer w chi) (Q t*tortoiseMode outer w chi t) t := by
    have h := tortoiseMode_hasDerivAt hc outer t ht
    refine ⟨h.1,h.2.congr_deriv ?_⟩
    rw [tortoiseMode_equation hc outer t ht]
  exact negative_homogeneous_eq_zero hf hg
    (fun t ht => (hm false t ht).1) (fun t ht => (hm false t ht).2)
    (fun t ht => (hm true t ht).1) (fun t ht => (hm true t ht).2)
    (neg_ne_zero.mpr (connection_ne_zero hc)) (fun t ht => tortoiseMode_wronskian hc t ht)
    (connection_ne_zero hc) (tortoiseHorizon_boundary hc) hzero
    (tortoiseHorizon_tendsto_horizon hc) (tortoiseHorizonFirst_tendsto_horizon hc)
    ⟨C,hC,hCbound⟩ hgb

end
end RHTower.D4BMJointSource
