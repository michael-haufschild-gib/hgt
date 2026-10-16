import GaloisForLFunctions.RHTower.CHMDStationaryGroundDomain
import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier

/-!
# The exact bounded ground-state potential

The maximal-domain ground-state correction is multiplication by an explicit
bounded real function. All singular integration is justified by the first
Levy displacement moment, including the two changes of integration order.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph

def thetaSecondDifference (t x : ℝ) : ℝ :=
  (riemannKernelReal (x + t) - riemannKernelReal x) +
    (riemannKernelReal (x - t) - riemannKernelReal x)

theorem measurable_thetaSecondDifference :
    Measurable (fun p : ℝ × ℝ => thetaSecondDifference p.1 p.2) := by
  unfold thetaSecondDifference
  exact ((continuous_riemannKernelReal.measurable.comp (measurable_snd.add measurable_fst)).sub
    (continuous_riemannKernelReal.measurable.comp measurable_snd)).add
      ((continuous_riemannKernelReal.measurable.comp (measurable_snd.sub measurable_fst)).sub
        (continuous_riemannKernelReal.measurable.comp measurable_snd))

theorem abs_thetaSecondDifference_le (t x : ℝ) :
    |thetaSecondDifference t x| ≤ 2 * (thetaLipConstant : ℝ) * |t| := by
  have hp := theta_lipschitz.norm_sub_le (x + t) x
  have hm := theta_lipschitz.norm_sub_le (x - t) x
  simp only [Real.norm_eq_abs, add_sub_cancel_left] at hp
  simp only [show x - t - x = -t by ring, Real.norm_eq_abs, abs_neg] at hm
  exact (abs_add_le _ _).trans (by linarith)

theorem norm_thetaSecondDifference_kernel_le {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ‖archLevyDensity t * thetaSecondDifference t x‖ ≤
      2 * (thetaLipConstant : ℝ) * (t * archLevyDensity t) := by
  rw [norm_mul, Real.norm_of_nonneg (archLevyDensity_pos ht).le, Real.norm_eq_abs]
  have h := mul_le_mul_of_nonneg_left (abs_thetaSecondDifference_le t x)
    (archLevyDensity_pos ht).le
  rw [abs_of_pos ht] at h
  nlinarith only [h]

theorem integrable_thetaSecondDifference_kernel (x : ℝ) :
    IntegrableOn (fun t => archLevyDensity t * thetaSecondDifference t x) (Ioi 0) := by
  apply (integrableOn_mul_archLevyDensity.const_mul (2 * (thetaLipConstant : ℝ))).mono'
  · exact (measurable_archLevyDensity.mul (measurable_thetaSecondDifference.comp
      (measurable_id.prodMk measurable_const))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_thetaSecondDifference_kernel_le ht x

def thetaGroundPotential (x : ℝ) : ℝ :=
  (∫ t in Ioi (0 : ℝ), archLevyDensity t * thetaSecondDifference t x) / Real.cosh (x / 2)

def thetaGroundPotentialBound : ℝ :=
  2 * (thetaLipConstant : ℝ) * ∫ t in Ioi (0 : ℝ), t * archLevyDensity t

theorem thetaGroundPotentialBound_nonneg : 0 ≤ thetaGroundPotentialBound := by
  apply mul_nonneg (by positivity)
  exact setIntegral_nonneg measurableSet_Ioi fun t ht =>
    mul_nonneg ht.le (archLevyDensity_pos ht).le

theorem measurable_thetaGroundPotential : Measurable thetaGroundPotential := by
  have hm : StronglyMeasurable (fun p : ℝ × ℝ =>
      archLevyDensity p.2 * thetaSecondDifference p.2 p.1) :=
    ((measurable_archLevyDensity.comp measurable_snd).mul
      (measurable_thetaSecondDifference.comp (measurable_snd.prodMk measurable_fst))).stronglyMeasurable
  exact (hm.integral_prod_right' (ν := volume.restrict (Ioi 0))).measurable.div
    (Real.continuous_cosh.comp (continuous_id.div_const 2)).measurable

theorem norm_thetaGroundPotential_le (x : ℝ) :
    ‖thetaGroundPotential x‖ ≤ thetaGroundPotentialBound := by
  have hn := norm_integral_le_of_norm_le
    (integrableOn_mul_archLevyDensity.const_mul (2 * (thetaLipConstant : ℝ)))
    ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => norm_thetaSecondDifference_kernel_le ht x)
  rw [integral_const_mul] at hn
  rw [thetaGroundPotential, norm_div, Real.norm_of_nonneg (Real.cosh_pos _).le]
  apply (div_le_iff₀ (Real.cosh_pos _)).mpr
  exact hn.trans (le_mul_of_one_le_right thetaGroundPotentialBound_nonneg (Real.one_le_cosh _))

def groundPotentialOperator : Lp ℝ 2 massMeasure →L[ℝ] Lp ℝ 2 massMeasure :=
  lpBoundedMulCLM measurable_thetaGroundPotential thetaGroundPotentialBound_nonneg
    norm_thetaGroundPotential_le

theorem groundPotentialOperator_ae (u : Lp ℝ 2 massMeasure) :
    groundPotentialOperator u =ᵐ[massMeasure] fun x => thetaGroundPotential x * u x :=
  lpBoundedMulCLM_coeFn _ _ _ u

theorem groundPotentialOperator_symmetric (u v : Lp ℝ 2 massMeasure) :
    ⟪groundPotentialOperator u, v⟫_ℝ = ⟪u, groundPotentialOperator v⟫_ℝ :=
  lpBoundedMulCLM_inner_real _ _ _ (fun _ => rfl) u v

theorem inner_groundPotentialOperator_self (u : Lp ℝ 2 massMeasure) :
    ⟪groundPotentialOperator u, u⟫_ℝ = ∫ x, thetaGroundPotential x * u x ^ 2 ∂massMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [groundPotentialOperator_ae u] with x hx
  simp only [hx, RCLike.inner_apply', conj_trivial]
  ring

/-- Translation of the backward row and Fubini produce the literal potential. -/
theorem integral_thetaGroundCorrection {v : ℝ → ℝ} (hv : Measurable v)
    (h2 : MemLp v 2 massMeasure) :
    (∫ e, thetaGroundCorrection v e ∂archBase) =
      ∫ x, thetaGroundPotential x * v x ^ 2 ∂massMeasure := by
  have hp := integrable_thetaGroundRow hv h2 1
  have hm := integrable_thetaGroundRow hv h2 (-1)
  have hshift : Integrable (fun e : ℝ × ℝ => thetaGroundRow v (-1) (e.1, e.2 + e.1)) archBase := by
    change Integrable (fun e : ℝ × ℝ => thetaGroundRow v (-1) (e.1, e.2 + e.1))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume)
    simpa only [Function.comp_def, add_comm] using
      (measurePreserving_prod_add (volume.restrict (Ioi (0 : ℝ))) volume).integrable_comp_of_integrable hm
  have heq : (∫ e : ℝ × ℝ, thetaGroundRow v (-1) (e.1, e.2 + e.1) ∂archBase) =
      ∫ e, thetaGroundRow v (-1) e ∂archBase := by
    rw [archBase, integral_prod _ hshift, integral_prod _ hm]
    apply integral_congr_ae
    filter_upwards with t
    exact integral_add_right_eq_self (fun x => thetaGroundRow v (-1) (t, x)) t
  change (∫ e, thetaGroundRow v 1 e + thetaGroundRow v (-1) (e.1, e.2 + e.1) ∂archBase) = _
  rw [integral_add hp hshift, heq, ← integral_add hp hm,
    archBase, integral_prod_symm _ (hp.add hm)]
  rw [massMeasure, integral_weighted volume continuous_massDensity.measurable
    (Eventually.of_forall fun x => (massDensity_pos x).le)]
  apply integral_congr_ae
  filter_upwards with x
  have hrow : (fun t => thetaGroundRow v 1 (t, x) + thetaGroundRow v (-1) (t, x)) =
      fun t => (riemannKernelReal x * v x ^ 2) *
        (archLevyDensity t * thetaSecondDifference t x) := by
    funext t
    simp only [thetaGroundRow, thetaSecondDifference, one_mul, neg_mul, one_mul, sub_eq_add_neg]
    ring
  rw [hrow, integral_const_mul]
  unfold massDensity thetaGroundPotential
  field_simp [(Real.cosh_pos (x / 2)).ne']

theorem arch_energy_eq_stationary_add_potential {v : ℝ → ℝ} (hv : Measurable v)
    (h2 : MemLp v 2 massMeasure) (hd : MemLp (difference v) 2 archMeasure) :
    (∫ e, difference v e ^ 2 ∂archMeasure) = stationaryEnergy (thetaProduct v) +
      ∫ x, thetaGroundPotential x * v x ^ 2 ∂massMeasure := by
  rw [arch_energy_eq_stationary_add_correction hv h2 hd, integral_thetaGroundCorrection hv h2]

end RHTower.CHMDDoobGraph
