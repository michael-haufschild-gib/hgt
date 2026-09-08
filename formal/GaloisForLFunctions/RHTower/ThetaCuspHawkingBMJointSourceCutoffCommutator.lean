import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceAngularAdmission

/-! Every angular cutoff derivative is retained and admitted for the full principal radial assembly. -/
open MeasureTheory Set Filter Topology
open scoped ContDiff
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMJointSource
open D4BMGlobalAngularResponse D4BMAngularSeries
noncomputable section

def cutoffPower (k : ℂ) (z : Fin 2 → ℝ) : ℂ := cutoff z*(z 1:ℂ)^k

/-- The exact differential cutoff commutator, retaining all first and second cutoff derivatives. -/
def cutoffCommutator (k : ℂ) (z : Fin 2 → ℝ) : ℂ :=
  hyperbolicLaplacian (cutoffPower k) z-cutoff z*(k*(k-1)*(z 1:ℂ)^k)

private theorem laplacian_continuous {f : (Fin 2 → ℝ) → ℂ}
    (hf : ContDiffOn ℝ 2 f domain) : ContinuousOn (hyperbolicLaplacian f) domain := by
  intro z hz
  have hfo : ContDiffAt ℝ 2 f z := hf.contDiffAt
    ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)
  have hd (i : Fin 2) : ContDiffAt ℝ 1 (coordDeriv i f) z :=
    (hfo.fderiv_right (by norm_num)).clm_apply contDiffAt_const
  have hdd (i : Fin 2) : ContinuousAt (coordDeriv i (coordDeriv i f)) z :=
    (((hd i).fderiv_right (show (0 : WithTop ℕ∞)+1 ≤ 1 by norm_num)).clm_apply
      contDiffAt_const).continuousAt
  exact (((Complex.ofRealCLM.continuous.continuousAt.comp (continuous_apply 1).continuousAt).pow 2).mul
    ((hdd 0).add (hdd 1))).continuousWithinAt

theorem cutoffCommutator_continuousOn (k : ℂ) : ContinuousOn (cutoffCommutator k) domain := by
  have hc : ContDiff ℝ 2 cutoff := (contDiff_infty.mp sourceCutoff_smooth) 2
  have hp : ContDiffOn ℝ 2 (cutoffPower k) domain :=
    hc.contDiffOn.mul (height_cpow_contDiffOn k 2)
  exact (laplacian_continuous hp).sub (sourceCutoff_smooth.continuous.continuousOn.mul
    (continuousOn_const.mul (height_cpow_contDiffOn k 0).continuousOn))

/-- The complete cutoff commutator is zero above the transition strip. -/
theorem cutoffCommutator_high (k : ℂ) (z : Fin 2 → ℝ) (hz : 3 < z 1) :
    cutoffCommutator k z = 0 := by
  have he : cutoffPower k =ᶠ[𝓝 z] (fun y : Fin 2 → ℝ => (y 1:ℂ)^k) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with y hy
    unfold cutoffPower cutoff
    rw [Real.smoothTransition.one_of_one_le (by linarith)]
    simp
  rw [cutoffCommutator,hyperbolicLaplacian_congr he,height_cpow_hyperbolicLaplacian k z (by linarith)]
  unfold cutoff
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  simp

/-- The full actual cutoff commutator belongs to the invariant angular L² space, for every exponent. -/
theorem cutoffCommutator_memLp (k : ℂ) :
    MemLp (fun z : UpperHalfPlane => cutoffCommutator k (coordinates z)) 2 D4BMModularCore.measure := by
  apply cuspBound_memLp _ (cutoffCommutator_continuousOn k) 0
  intro z hz
  rw [cutoffCommutator_high k z hz,norm_zero]

def cutoffCommutatorVector (k : ℂ) : D4BMModularCore.Space :=
  (cutoffCommutator_memLp k).toLp (fun z => cutoffCommutator k (coordinates z))

end
end RHTower.D4BMJointSource
