import GaloisForLFunctions.RHTower.SoninDilationContinuity
import Mathlib.MeasureTheory.Integral.Bochner.L1

/-!
# Archimedean integrated scaling representation

Unconditional construction of the integrated normalized-dilation representation on the even
archimedean Hilbert space. Kernels live intrinsically in L¹(ℝ, du); log-scale Lebesgue measure
is multiplicative Haar measure under u = log r.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- Source test kernels on the logarithmic form of ℝ₊*, with Haar measure du = dr/r. -/
abbrev CCMLogKernel := ℝ →₁[volume] ℂ

/-- Strongly continuous Connes--Consani scaling orbit on the even archimedean Hilbert space. -/
def ccmLogDilationOrbit (f : evenSubspace) (u : ℝ) : evenSubspace :=
  evenDilationUnitary (Real.exp (-u)) (Real.exp_pos (-u)) f

@[simp] theorem norm_ccmLogDilationOrbit (f : evenSubspace) (u : ℝ) :
    ‖ccmLogDilationOrbit f u‖ = ‖f‖ := by
  exact (evenDilationUnitary (Real.exp (-u)) (Real.exp_pos (-u))).norm_map f

/-- Pointwise formula
theta(exp u) f(x) = exp(-u/2) f(exp(-u) x) from source normalization. -/
theorem ccmLogDilationOrbit_ae (f : evenSubspace) (u : ℝ) :
    ((((ccmLogDilationOrbit f u : evenSubspace) : SoninL2) : ℝ → ℂ)) =ᵐ[volume]
      fun x : ℝ => (Real.sqrt (Real.exp (-u)) : ℂ) *
        ((f : SoninL2) : ℝ → ℂ) (Real.exp (-u) * x) := by
  rw [ccmLogDilationOrbit, coe_evenDilationUnitary_apply]
  exact dilation_ae (Real.exp (-u)) (Real.exp_pos (-u)) f

/-- Additive log-scale representation law for the multiplicative scaling group. -/
theorem ccmLogDilationOrbit_add (f : evenSubspace) (u v : ℝ) :
    ccmLogDilationOrbit (ccmLogDilationOrbit f v) u =
      ccmLogDilationOrbit f (u + v) := by
  apply Subtype.ext
  change dilation (Real.exp (-u)) (Real.exp_pos (-u))
      (dilation (Real.exp (-v)) (Real.exp_pos (-v)) (f : SoninL2)) =
    dilation (Real.exp (-(u + v))) (Real.exp_pos (-(u + v))) (f : SoninL2)
  rw [dilation_dilation]
  apply Lp.ext
  filter_upwards [
    dilation_ae (Real.exp (-u) * Real.exp (-v))
      (mul_pos (Real.exp_pos (-u)) (Real.exp_pos (-v))) (f : SoninL2),
    dilation_ae (Real.exp (-(u + v))) (Real.exp_pos (-(u + v))) (f : SoninL2)
  ] with x hleft hright
  rw [hleft, hright]
  have hscale : Real.exp (-u) * Real.exp (-v) = Real.exp (-(u + v)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hscale]

/-- Strong continuity of source scaling representation in logarithmic scale. -/
theorem continuous_ccmLogDilationOrbit (f : evenSubspace) :
    Continuous (ccmLogDilationOrbit f) := by
  apply Continuous.subtype_mk
  have h := (continuousOn_rayDilate (f : SoninL2)).comp_continuous
    (Real.continuous_exp.comp continuous_neg) (fun u => Real.exp_pos (-u))
  change Continuous (fun u : ℝ => rayDilate (Real.exp (-u)) (f : SoninL2)) at h
  convert h using 1
  funext u
  rw [rayDilate_of_pos (Real.exp_pos (-u))]

theorem integrable_ccmLogKernel_smul_orbit (g : CCMLogKernel) (f : evenSubspace) :
    Integrable (fun u : ℝ => g u • ccmLogDilationOrbit f u) volume := by
  have hmeas : AEStronglyMeasurable
      (fun u : ℝ => g u • ccmLogDilationOrbit f u) volume := by
    exact (L1.aestronglyMeasurable_coeFn g).smul
      (continuous_ccmLogDilationOrbit f).aestronglyMeasurable
  refine Integrable.mono' ((L1.integrable_coeFn g).norm.mul_const ‖f‖) hmeas ?_
  filter_upwards [] with u
  rw [norm_smul, norm_ccmLogDilationOrbit]

/-- Vector-valued integrated normalized-dilation action. -/
def ccmIntegratedScalingVector (g : CCMLogKernel) (f : evenSubspace) : evenSubspace :=
  ∫ u : ℝ, g u • ccmLogDilationOrbit f u

theorem ccmIntegratedScalingVector_add (g : CCMLogKernel) (f h : evenSubspace) :
    ccmIntegratedScalingVector g (f + h) =
      ccmIntegratedScalingVector g f + ccmIntegratedScalingVector g h := by
  rw [ccmIntegratedScalingVector, ccmIntegratedScalingVector, ccmIntegratedScalingVector,
    ← integral_add (integrable_ccmLogKernel_smul_orbit g f)
      (integrable_ccmLogKernel_smul_orbit g h)]
  apply integral_congr_ae
  filter_upwards [] with u
  simp [ccmLogDilationOrbit, smul_add]

theorem ccmIntegratedScalingVector_smul (g : CCMLogKernel) (c : ℂ)
    (f : evenSubspace) :
    ccmIntegratedScalingVector g (c • f) = c • ccmIntegratedScalingVector g f := by
  rw [ccmIntegratedScalingVector, ccmIntegratedScalingVector, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with u
  simp [ccmLogDilationOrbit, smul_smul, mul_comm]

/-- Sharp L¹-to-operator pointwise bound for integrated scaling action. -/
theorem norm_ccmIntegratedScalingVector_le (g : CCMLogKernel) (f : evenSubspace) :
    ‖ccmIntegratedScalingVector g f‖ ≤ ‖g‖ * ‖f‖ := by
  calc
    ‖ccmIntegratedScalingVector g f‖
        ≤ ∫ u : ℝ, ‖g u • ccmLogDilationOrbit f u‖ :=
          norm_integral_le_integral_norm _
    _ = ∫ u : ℝ, ‖g u‖ * ‖f‖ := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [norm_smul, norm_ccmLogDilationOrbit]
    _ = (∫ u : ℝ, ‖g u‖) * ‖f‖ := integral_mul_const _ _
    _ = ‖g‖ * ‖f‖ := by rw [L1.norm_eq_integral_norm]

/-- Actual bounded source operator rho(g) = integral g(u) theta(exp u) du. -/
def ccmIntegratedScaling (g : CCMLogKernel) : evenSubspace →L[ℂ] evenSubspace :=
  LinearMap.mkContinuous
    { toFun := ccmIntegratedScalingVector g
      map_add' := ccmIntegratedScalingVector_add g
      map_smul' := ccmIntegratedScalingVector_smul g }
    ‖g‖ (norm_ccmIntegratedScalingVector_le g)

@[simp] theorem ccmIntegratedScaling_apply (g : CCMLogKernel) (f : evenSubspace) :
    ccmIntegratedScaling g f = ∫ u : ℝ, g u • ccmLogDilationOrbit f u := rfl

theorem norm_ccmIntegratedScaling_apply_le (g : CCMLogKernel) (f : evenSubspace) :
    ‖ccmIntegratedScaling g f‖ ≤ ‖g‖ * ‖f‖ :=
  norm_ccmIntegratedScalingVector_le g f

/-- Integrated source representation is contractive. -/
theorem norm_ccmIntegratedScaling_le (g : CCMLogKernel) :
    ‖ccmIntegratedScaling g‖ ≤ ‖g‖ := by
  exact ContinuousLinearMap.opNorm_le_bound (ccmIntegratedScaling g) (norm_nonneg g)
    (norm_ccmIntegratedScaling_apply_le g)

theorem ccmIntegratedScaling_add (g h : CCMLogKernel) :
    ccmIntegratedScaling (g + h) = ccmIntegratedScaling g + ccmIntegratedScaling h := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [ccmIntegratedScaling_apply, add_apply]
  rw [← integral_add (integrable_ccmLogKernel_smul_orbit g f)
    (integrable_ccmLogKernel_smul_orbit h f)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add g h] with u hu
  rw [hu, Pi.add_apply, add_smul]

theorem ccmIntegratedScaling_smul (c : ℂ) (g : CCMLogKernel) :
    ccmIntegratedScaling (c • g) = c • ccmIntegratedScaling g := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [ccmIntegratedScaling_apply, smul_apply]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c g] with u hu
  rw [hu, Pi.smul_apply, smul_eq_mul, smul_smul]

/-- Integrated scaling as a contractive linear map from source L¹ convolution space. -/
def ccmIntegratedScalingMap :
    CCMLogKernel →L[ℂ] (evenSubspace →L[ℂ] evenSubspace) :=
  LinearMap.mkContinuous
    { toFun := ccmIntegratedScaling
      map_add' := ccmIntegratedScaling_add
      map_smul' := ccmIntegratedScaling_smul }
    1 (fun g => by simpa using norm_ccmIntegratedScaling_le g)

@[simp] theorem ccmIntegratedScalingMap_apply (g : CCMLogKernel) :
    ccmIntegratedScalingMap g = ccmIntegratedScaling g := rfl

end RHTower
