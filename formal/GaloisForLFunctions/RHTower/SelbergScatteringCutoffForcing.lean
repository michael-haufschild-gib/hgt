import GaloisForLFunctions.RHTower.SelbergScatteringSourceVector
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCutoffPowerFlux

/-!
# Exact original transition forcing and its scalar cancellation

The full source equation retains the outgoing Weyl coefficient times the actual
cutoff commutator. That complete forcing is admitted and nonzero in the original
modular Hilbert space, as its complementary boundary moment proves. Its absolutely
convergent bilinear pairing with the original scattering field is nevertheless
zero. No vanishing of the forcing or of the entire-operator residual is inferred.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.SelbergScatteringCutoffForcing
open D4BMModularCore D4BMGlobalAngularResponse D4BMAngularSeries D4BMJointSource
open SelbergScatteringCuspSubtraction
noncomputable section

private theorem coefficient_ne (q : XiZeroCopy) : reflectedCompletedLambda ((q.1:ℂ)-1) ≠ 0 := by
  obtain ⟨he,hn,_⟩ := physicalScalar_cutoff_calibration q
  intro h
  apply hn
  rw [he,h,mul_zero]

/-- The actual source equation leaves exactly the original outgoing coefficient times its cutoff commutator. -/
theorem cutoffForcing_eq_commutator (q : XiZeroCopy) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    cutoffForcing q z = reflectedCompletedLambda ((q.1:ℂ)-1)*
      cutoffCommutator (1-(q.1:ℂ)/2) z := by
  let k : ℂ := 1-(q.1:ℂ)/2
  have hn : domain ∈ 𝓝 z :=
    (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz
  have hf : ContDiffAt ℝ 2 (cutoffPower k) z :=
    ((contDiff_infty.mp sourceCutoff_smooth 2).contDiffOn.mul (height_cpow_contDiffOn k 2)).contDiffAt hn
  have he : (fun w => cutoff w*principal (physicalAngularParameter q) w) =
      fun w => reflectedCompletedLambda ((q.1:ℂ)-1)*cutoffPower k w := by
    funext w
    rw [physicalScalar_principal]
    dsimp [cutoffPower,k]
    ring
  rw [cutoffForcing,he,hyperbolicLaplacian_const_mul hf,physicalScalar_principal]
  unfold D4BMJointSource.cutoffCommutator
  rw [physicalAngularParameter_eq]
  dsimp [k]
  ring

private theorem forcing_continuous (q : XiZeroCopy) :
    Continuous (fun z : UpperHalfPlane => cutoffForcing q (coordinates z)) := by
  have hc : Continuous coordinates := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact UpperHalfPlane.continuous_re
    · exact UpperHalfPlane.continuous_im
  have h := (continuous_const (y := reflectedCompletedLambda ((q.1:ℂ)-1))).mul
    ((cutoffCommutator_continuousOn (1-(q.1:ℂ)/2)).comp_continuous hc (fun z => z.im_pos))
  apply h.congr
  intro z
  exact (cutoffForcing_eq_commutator q _ z.im_pos).symm

/-- The complete original transition forcing is admitted in the native modular measure. -/
theorem cutoffForcing_memLp (q : XiZeroCopy) :
    MemLp (fun z : UpperHalfPlane => cutoffForcing q (coordinates z)) 2 measure := by
  have h := (cutoffCommutator_memLp (1-(q.1:ℂ)/2)).const_mul
    (reflectedCompletedLambda ((q.1:ℂ)-1))
  apply (memLp_congr_ae (Filter.Eventually.of_forall (fun z : UpperHalfPlane =>
    cutoffForcing_eq_commutator q (coordinates z) z.im_pos))).mpr h

/-- The literal differential forcing as an actual native Hilbert vector. -/
def forcingVector (q : XiZeroCopy) : Space :=
  (cutoffForcing_memLp q).toLp (fun z => cutoffForcing q (coordinates z))

theorem forcingVector_coe (q : XiZeroCopy) :
    (forcingVector q : UpperHalfPlane → ℂ) =ᵐ[measure] (fun z => cutoffForcing q (coordinates z)) :=
  (cutoffForcing_memLp q).coeFn_toLp

/-- Exact boundary flux of the complementary height test against the full commutator. -/
theorem cutoffCommutator_complement_moment (k : ℂ) :
    cutoffPowerMoment (1-k) k = 2*k-1 := by
  rw [cutoffPowerMoment_eq,show 1-k+k-1=0 by ring,
    show (1-k)*(1-k-1)-k*(k-1)=0 by ring]
  simp only [Complex.cpow_zero,mul_one,zero_mul,add_zero]
  ring

/-- The original compact transition forcing is nonzero for every actual Xi copy. -/
theorem forcingVector_ne_zero (q : XiZeroCopy) : forcingVector q ≠ 0 := by
  intro hzero
  have hz : (forcingVector q : UpperHalfPlane → ℂ) =ᵐ[measure] (fun _ => (0:ℂ)) := by
    rw [hzero]
    exact Lp.coeFn_zero ℂ 2 measure
  have hg := (forcingVector_coe q).symm.trans hz
  change (fun z => cutoffForcing q (coordinates z)) =ᵐ[volume.restrict fd] (fun _ => (0:ℂ)) at hg
  have hclosure : fd ⊆ closure (interior fd) := by
    rw [← fdo_eq_interior_fd,← fd_eq_closure_fdo]
  have he := Measure.eqOn_of_ae_eq hg (forcing_continuous q).continuousOn continuousOn_const hclosure
  let k : ℂ := 1-(q.1:ℂ)/2
  have hcomm (y : ℝ) (hy : y ∈ uIcc (1:ℝ) 4) : cutoffCommutator k ![0,y] = 0 := by
    have hy1 : 1 ≤ y := by
      rw [uIcc_of_le (by norm_num : (1:ℝ)≤4)] at hy
      exact hy.1
    let z : UpperHalfPlane := ⟨⟨0,y⟩,by linarith⟩
    have hfd : z ∈ fd := by
      constructor
      · change 1 ≤ (0:ℝ)*0+y*y
        nlinarith
      · change |(0:ℝ)| ≤ 1/2
        norm_num
    have hh := he hfd
    change cutoffForcing q (coordinates z) = 0 at hh
    rw [cutoffForcing_eq_commutator q (coordinates z) z.im_pos] at hh
    exact (mul_eq_zero.mp hh).resolve_left (coefficient_ne q)
  have hm : cutoffPowerMoment (1-k) k = 0 := by
    unfold cutoffPowerMoment
    calc
      _ = ∫ _y in (1:ℝ)..4, (0:ℂ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        dsimp only
        rw [hcomm y hy,mul_zero]
      _ = 0 := by simp
  rw [cutoffCommutator_complement_moment] at hm
  have hr := congrArg Complex.re hm
  dsimp [k] at hr
  norm_num at hr
  have hq := (xi_divisor_support_re_mem_open_unit q.1).2
  linarith


/-- The full original scattering field has an absolutely convergent pairing with its retained forcing. -/
theorem scalar_forcing_integrable (q : XiZeroCopy) :
    Integrable (fun z : UpperHalfPlane => scalar (physicalAngularParameter q) (coordinates z)*
      cutoffForcing q (coordinates z)) measure := by
  have hi := (scalar_cutoffCommutator_integrable (physicalAngularParameter q) (1-(q.1:ℂ)/2)).const_mul
    (reflectedCompletedLambda ((q.1:ℂ)-1))
  apply hi.congr
  filter_upwards with z
  rw [cutoffForcing_eq_commutator q (coordinates z) z.im_pos]
  ring

/-- The full scalar pairing vanishes even though the actual forcing vector is nonzero. -/
theorem scalar_forcing_pairing_zero (q : XiZeroCopy) :
    (∫ z : UpperHalfPlane, scalar (physicalAngularParameter q) (coordinates z)*
      cutoffForcing q (coordinates z) ∂measure) = 0 := by
  have he : (∫ z : UpperHalfPlane, scalar (physicalAngularParameter q) (coordinates z)*
      cutoffForcing q (coordinates z) ∂measure) =
      reflectedCompletedLambda ((q.1:ℂ)-1)*scalarCutoffPeriod (physicalAngularParameter q) (1-(q.1:ℂ)/2) := by
    rw [scalarCutoffPeriod,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    rw [cutoffForcing_eq_commutator q (coordinates z) z.im_pos]
    ring
  rw [he,(physicalScalar_cutoff_calibration q).2.2,mul_zero]

end
end RHTower.SelbergScatteringCutoffForcing
