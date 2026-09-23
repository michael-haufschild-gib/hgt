import GaloisForLFunctions.RHTower.SelbergScatteringSourceBounds
import GaloisForLFunctions.RHTower.SelbergScatteringCutoffDerivatives
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMHeightLaplacian

/-!
# Original corrected source in the native closed graph

Expanding modular cutoffs approximate the complete original source in native
Hilbert norm. Their literal operator images converge to the full forced target:
the two scaled cutoff derivative multipliers vanish strongly. Continuity of the
native bounded inverse identifies the original source in its actual closed
operator domain and proves its exact forced and bounded resolvent equations.

This proves graph admission, not occurrence for the entire-transform operator.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped MatrixGroups ContDiff
namespace RHTower.SelbergScatteringSourceGraph
open D4BMModularCore D4BMGlobalAngularResponse D4BMAngularSeries D4BMJointSource
open SelbergScatteringCuspSubtraction SelbergScatteringSourceVector SelbergScatteringSourceBounds
open SelbergScatteringSourceApproximation SelbergScatteringCutoffDerivatives
open SelbergScatteringNativeResidual SelbergScatteringEntireOperator
noncomputable section

private def heightProfile (n : ℕ) (y : ℝ) : ℂ := (heightWeight n y : ℂ)

private theorem weight_smooth (n : ℕ) : ContDiff ℝ ∞ (heightWeight n) :=
  smoothWeight_contDiff _ _

private theorem profile_smooth (n : ℕ) : ContDiff ℝ ∞ (heightProfile n) :=
  Complex.ofRealCLM.contDiff.comp (weight_smooth n)

private theorem profile_deriv (n : ℕ) :
    deriv (heightProfile n) = (fun y => ((deriv (heightWeight n) y : ℝ) : ℂ)) := by
  funext y
  exact (((weight_smooth n).differentiable (by simp) y).hasDerivAt.ofReal_comp).deriv

private theorem profile_second (n : ℕ) (y : ℝ) :
    deriv (deriv (heightProfile n)) y = ((iteratedDeriv 2 (heightWeight n) y : ℝ) : ℂ) := by
  rw [profile_deriv,iteratedDeriv_succ,iteratedDeriv_one]
  have hs := (contDiff_infty_iff_deriv.mp (weight_smooth n)).2
  exact ((hs.differentiable (by simp) y).hasDerivAt.ofReal_comp).deriv

private theorem height_coord_deriv (f : ℝ → ℂ) (hf : Differentiable ℝ f)
    (i : Fin 2) (z : Fin 2 → ℝ) :
    coordDeriv i (fun w => f (w 1)) z = if i=1 then deriv f (z 1) else 0 := by
  have hd := (hf (z 1)).hasDerivAt.hasFDerivAt.comp z
    ((show (Fin 2 → ℝ) →L[ℝ] ℝ from ContinuousLinearMap.proj 1).hasFDerivAt)
  change HasFDerivAt (fun w : Fin 2 → ℝ => f (w 1)) _ z at hd
  rw [coordDeriv,hd.fderiv]
  fin_cases i <;> simp [ContinuousLinearMap.comp_apply]

private theorem residual_smooth_at (q : XiZeroCopy) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    ContDiffAt ℝ 2 (residual q) z := by
  have hs : ContDiffOn ℝ ∞ (residual q) D4BMAngularSeries.domain :=
    (cuspLeg_contDiffOn .scalar (physicalAngularParameter q)).sub
      (sourceCutoff_smooth.contDiffOn.mul (cuspConstantPart_contDiffOn .scalar (physicalAngularParameter q)))
  exact ((contDiffOn_infty.mp hs) 2).contDiffAt
    ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)

private theorem profile_forcing (q : XiZeroCopy) (n : ℕ) (z : UpperHalfPlane) :
    heightProfile n z.im * cutoffForcing q (coordinates z) = cutoffForcing q (coordinates z) := by
  by_cases hy : z.im ≤ 3
  · have hh : z.im ≤ cutoffHeight n := by unfold cutoffHeight; have := Nat.cast_nonneg (α := ℝ) n; linarith
    rw [heightProfile,heightWeight_one n z.im hh]
    simp
  · rw [cutoffForcing_high q (coordinates z) (lt_of_not_ge hy),mul_zero]

set_option maxHeartbeats 800000 in
/-- The complete source product rule retains both cutoff derivative terms in
the original hyperbolic chart, including on the closed modular seams. -/
theorem sourceCore_laplacian_on_fd (q : XiZeroCopy) (n : ℕ) (z : UpperHalfPlane) (hz : z ∈ fd) :
    chartLaplacian (sourceCore q n).field z =
      (heightWeight n z.im : ℂ)*chartLaplacian (globalResidual q) z +
        cutoffDerivative 2 n z * globalResidual q z +
        2*cutoffDerivative 1 n z * weightedDeriv Complex.I (globalResidual q) z := by
  have hr : globalResidual q =ᶠ[𝓝 z] (fun w => residual q (coordinates w)) :=
    cellGermExtension_germ _ (residual_cell_compatible q) z hz
  have hg : (sourceCore q n).field =ᶠ[𝓝 z]
      (fun w => heightProfile n w.im * residual q (coordinates w)) :=
    (modularCutoff_germ n z hz).mul hr
  have hp : ContDiff ℝ ∞ (fun w : Fin 2 → ℝ => heightProfile n (w 1)) :=
    (profile_smooth n).comp
      (show (Fin 2 → ℝ) →L[ℝ] ℝ from ContinuousLinearMap.proj 1).contDiff
  have hl : chartLaplacian (sourceCore q n).field z =
      hyperbolicLaplacian (fun w => heightProfile n (w 1)*residual q w) (coordinates z) := by
    rw [chartLaplacian_congr hg]
    exact chartLaplacian_coordinates (fun w : Fin 2 → ℝ => heightProfile n (w 1)*residual q w) z
  rw [hl,SelbergScatteringHeightConjugation.hyperbolicLaplacian_mul
    ((contDiff_infty.mp hp) 2).contDiffAt (residual_smooth_at q (coordinates z) z.im_pos),
    D4BMCuspProjection.height_laplacian _ (profile_smooth n),
    height_coord_deriv _ ((profile_smooth n).differentiable (by simp)),
    height_coord_deriv _ ((profile_smooth n).differentiable (by simp)),
    profile_second,profile_deriv,globalResidual_vertical_on_fd q z hz,
    chartLaplacian_congr hr,chartLaplacian_coordinates,globalResidual_eq_on_fd q z hz]
  simp only [show (0:Fin 2)≠1 by norm_num,if_false,ite_true,zero_mul,zero_add,
    cutoffDerivative,iteratedDeriv_one,Complex.ofReal_mul,Complex.ofReal_pow,pow_one,heightProfile,
    show coordinates z 1 = z.im from rfl]
  change _ = (heightWeight n z.im : ℂ)*hyperbolicLaplacian (residual q) (coordinates z) +
    (z.im:ℂ)^(2 : ℕ) * ((iteratedDeriv 2 (heightWeight n) z.im : ℝ) : ℂ)*residual q (coordinates z) +
    2*((z.im:ℂ)*((deriv (heightWeight n) z.im : ℝ) : ℂ))*
      ((z.im:ℂ)*coordDeriv 1 (residual q) (coordinates z))
  ring

/-- The original compact transition forcing is unchanged by every expanding
cutoff; the only new errors are its two complete derivative terms. -/
theorem sourceCore_operator_on_fd (q : XiZeroCopy) (n : ℕ) (z : UpperHalfPlane) (hz : z ∈ fd) :
    (sourceCore q n).field z - chartLaplacian (sourceCore q n).field z =
      scatteringEnergy (q.1:ℂ)*(sourceCore q n).field z + cutoffForcing q (coordinates z) -
        cutoffDerivative 2 n z*globalResidual q z -
        2*cutoffDerivative 1 n z*weightedDeriv Complex.I (globalResidual q) z := by
  rw [sourceCore_laplacian_on_fd q n z hz,sourceCore_field_on_fd q n z hz]
  have he := globalResidual_operator_on_fd q z hz
  have hh := profile_forcing q n z
  change (heightWeight n z.im : ℂ)*cutoffForcing q (coordinates z) = cutoffForcing q (coordinates z) at hh
  linear_combination (heightWeight n z.im : ℂ)*he + hh

/-- Exact native Hilbert-space image of the full source approximants. All
cutoff derivatives and the original forcing remain present. -/
theorem sourceApproxDomain_operator_eq (q : XiZeroCopy) (n : ℕ) :
    energyOperator (sourceApproxDomain q n) =
      scatteringEnergy (q.1:ℂ) • (sourceApproxDomain q n : Space) +
        SelbergScatteringCutoffForcing.forcingVector q -
        cutoffDerivativeOperator 2 n (sourceVector q) -
        (2:ℂ) • cutoffDerivativeOperator 1 n (sourceVerticalVector q) := by
  let v : Space := sourceApproxDomain q n
  let e := scatteringEnergy (q.1:ℂ)
  let h := SelbergScatteringCutoffForcing.forcingVector q
  let d2 := cutoffDerivativeOperator 2 n (sourceVector q)
  let d1 := cutoffDerivativeOperator 1 n (sourceVerticalVector q)
  apply Lp.ext
  filter_upwards [sourceApproxDomain_operator_coe q n,
    Lp.coeFn_sub (e • v+h-d2) ((2:ℂ) • d1),Lp.coeFn_sub (e • v+h) d2,
    Lp.coeFn_add (e • v) h,Lp.coeFn_smul e v,Lp.coeFn_smul (2:ℂ) d1,
    cutoffDerivativeOperator_coe 2 n (sourceVector q),
    cutoffDerivativeOperator_coe 1 n (sourceVerticalVector q),
    sourceVector_coe q,sourceVerticalVector_coe q,SelbergScatteringCutoffForcing.forcingVector_coe q,
    (core_field_memLp (sourceCore q n).field (sourceCore q n).smooth (sourceCore q n).compact).coeFn_toLp,
    ae_restrict_mem isClosed_fd.measurableSet] with z hA hs1 hs2 ha hv ht hd2 hd1 hV hD hH hc hz
  change energyOperator (sourceApproxDomain q n) z = (e • v+h-d2-(2:ℂ) • d1 : Space) z
  simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at hs1 hs2 ha hv ht
  rw [hA,hs1,hs2,ha,hv,ht]
  change (sourceCore q n).field z - chartLaplacian (sourceCore q n).field z =
    e * (sourceApproxDomain q n : Space) z + h z -
      cutoffDerivativeOperator 2 n (sourceVector q) z -
      2*cutoffDerivativeOperator 1 n (sourceVerticalVector q) z
  change (sourceApproxDomain q n : Space) z = (sourceCore q n).field z at hc
  rw [hd2,hd1,hV,hD,hH,hc]
  simpa only [mul_assoc] using sourceCore_operator_on_fd q n z hz

/-- The complete original operator images converge in native Hilbert norm to
the admitted literal source image; both derivative errors vanish strongly. -/
theorem sourceApproxDomain_operator_tendsto (q : XiZeroCopy) :
    Tendsto (fun n => energyOperator (sourceApproxDomain q n)) atTop
      (𝓝 (sourceOperatorTarget q)) := by
  have ht := (((sourceApproxDomain_tendsto q).const_smul (scatteringEnergy (q.1:ℂ))).add
    (tendsto_const_nhds (x := SelbergScatteringCutoffForcing.forcingVector q))).sub
      (cutoffDerivativeOperator_tendsto_zero 2 (by norm_num) (sourceVector q))
  have h := ht.sub ((cutoffDerivativeOperator_tendsto_zero 1 (by norm_num)
    (sourceVerticalVector q)).const_smul (2:ℂ))
  simpa only [sourceApproxDomain_operator_eq,smul_zero,sub_zero,sourceOperatorTarget] using h

/-- The actual source and its actual operator-image target satisfy the native
bounded inverse identity, by their two independently proved norm limits. -/
theorem nativeCovariance_sourceOperatorTarget (q : XiZeroCopy) :
    nativeCovariance (sourceOperatorTarget q) = sourceVector q := by
  have ht := (nativeCovariance.continuous.tendsto (sourceOperatorTarget q)).comp
    (sourceApproxDomain_operator_tendsto q)
  have hb (n : ℕ) : nativeCovariance (energyOperator (sourceApproxDomain q n)) =
      (sourceApproxDomain q n : Space) :=
    closedDenseInverse_C_apply nativeCovariance nativeCovariance_injective (sourceApproxDomain q n)
  exact tendsto_nhds_unique (ht.congr hb) (sourceApproxDomain_tendsto q)

/-- The complete original corrected source belongs to the original native
closed operator domain. No source-domain premise is supplied. -/
theorem sourceVector_mem_energyOperator_domain (q : XiZeroCopy) :
    sourceVector q ∈ energyOperator.domain := by
  rw [← nativeCovariance_sourceOperatorTarget q]
  exact (closedDenseInverse_apply_C nativeCovariance nativeCovariance_injective (sourceOperatorTarget q)).1

def sourceNativeDomain (q : XiZeroCopy) : energyOperator.domain :=
  ⟨sourceVector q,sourceVector_mem_energyOperator_domain q⟩

/-- The constructed native domain source has exactly its original full
differential image; the graph identification has no unresolved hypothesis. -/
theorem sourceNativeDomain_operator (q : XiZeroCopy) :
    energyOperator (sourceNativeDomain q) = sourceOperatorTarget q := by
  have h := closedDenseInverse_apply_C nativeCovariance nativeCovariance_injective (sourceOperatorTarget q)
  have he : sourceNativeDomain q = ⟨nativeCovariance (sourceOperatorTarget q),h.1⟩ :=
    Subtype.ext (nativeCovariance_sourceOperatorTarget q).symm
  rw [he]
  exact h.2

/-- The complete original source satisfies its retained forced equation in the
actual native closed operator, at the full complex Xi scattering energy. -/
theorem sourceNativeDomain_equation (q : XiZeroCopy) :
    energyOperator (sourceNativeDomain q) -
      scatteringEnergy (q.1:ℂ) • (sourceNativeDomain q : Space) =
        SelbergScatteringCutoffForcing.forcingVector q := by
  rw [sourceNativeDomain_operator]
  change (scatteringEnergy (q.1:ℂ) • sourceVector q +
    SelbergScatteringCutoffForcing.forcingVector q) - scatteringEnergy (q.1:ℂ) • sourceVector q = _
  abel

/-- Exact bounded resolvent transport of the original differential forcing,
with the admitted source itself identified on the left. -/
theorem sourceVector_native_resolvent_equation (q : XiZeroCopy) :
    sourceVector q - scatteringEnergy (q.1:ℂ) • nativeCovariance (sourceVector q) =
      nativeCovariance (SelbergScatteringCutoffForcing.forcingVector q) := by
  have h := nativeCovariance_sourceOperatorTarget q
  rw [sourceOperatorTarget,map_add,map_smul] at h
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using h.symm)

end
end RHTower.SelbergScatteringSourceGraph
