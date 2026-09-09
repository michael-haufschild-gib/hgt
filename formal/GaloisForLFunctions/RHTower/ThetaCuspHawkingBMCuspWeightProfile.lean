import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCellGermExtension
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Bounded approximations to cusp height with one uniform logarithmic derivative bound. -/
open Set Filter Topology
open scoped ContDiff
namespace RHTower.D4BMJointWave
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def cuspWeightCutoff (y : ℝ) : ℝ := Real.smoothTransition (y-2)

private theorem cutoff_smooth : ContDiff ℝ ∞ cuspWeightCutoff :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

private theorem cutoff_low (y : ℝ) (hy : y ≤ 2) : cuspWeightCutoff y = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem cutoff_high (y : ℝ) (hy : 3 ≤ y) : cuspWeightCutoff y = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem cutoff_deriv_zero (y : ℝ) (hy : y < 2 ∨ 3 < y) :
    deriv cuspWeightCutoff y = 0 := by
  rcases hy with hy | hy
  · have he : cuspWeightCutoff =ᶠ[𝓝 y] fun _ => (0:ℝ) := by
      filter_upwards [gt_mem_nhds hy] with z hz
      exact cutoff_low z hz.le
    rw [he.deriv_eq,deriv_const]
  · have he : cuspWeightCutoff =ᶠ[𝓝 y] fun _ => (1:ℝ) := by
      filter_upwards [lt_mem_nhds hy] with z hz
      exact cutoff_high z hz.le
    rw [he.deriv_eq,deriv_const]

private theorem exists_slope_bound : ∃ B : ℝ, 0 ≤ B ∧
    ∀ y ∈ Icc (2:ℝ) 3, |deriv cuspWeightCutoff y| ≤ B := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (cutoff_smooth.continuous_deriv (by simp)).continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro y hy
  simpa only [Real.norm_eq_abs] using (hC y hy).trans (le_max_left C 0)

def cuspWeightSlopeBound : ℝ := exists_slope_bound.choose
def cuspWeightBase : ℝ := 18*cuspWeightSlopeBound+1

theorem cuspWeightSlopeBound_nonneg : 0 ≤ cuspWeightSlopeBound :=
  exists_slope_bound.choose_spec.1

theorem cuspWeightBase_one_le : 1 ≤ cuspWeightBase := by
  dsimp [cuspWeightBase]
  linarith [cuspWeightSlopeBound_nonneg]

/-- The original cutoff makes the bounded weight constant across every low modular seam. -/
def cuspWeightProfile (N y : ℝ) : ℝ :=
  cuspWeightBase+cuspWeightCutoff y*(N*y/(N+y))

/-- The limiting weight agrees with height up to fixed positive bounds on the quotient. -/
def cuspWeightLimit (y : ℝ) : ℝ := cuspWeightBase+cuspWeightCutoff y*y

theorem cuspWeightProfile_low (N y : ℝ) (hy : y ≤ 2) :
    cuspWeightProfile N y = cuspWeightBase := by
  simp only [cuspWeightProfile,cutoff_low y hy,zero_mul,add_zero]

theorem cuspWeightProfile_bounds (N y : ℝ) (hN : 0 < N) (hy : 0 < y) :
    cuspWeightBase ≤ cuspWeightProfile N y ∧ cuspWeightProfile N y ≤ cuspWeightBase+N := by
  have hp : 0 ≤ N*y/(N+y) := by positivity
  have hpn : N*y/(N+y) ≤ N := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  have he0 := Real.smoothTransition.nonneg (y-2)
  have he1 := Real.smoothTransition.le_one (y-2)
  change 0 ≤ cuspWeightCutoff y at he0
  change cuspWeightCutoff y ≤ 1 at he1
  dsimp [cuspWeightProfile]
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg he0 hp)
  · have := mul_le_mul_of_nonneg_right he1 hp
    nlinarith

theorem cuspWeightProfile_le_limit (N y : ℝ) (hN : 0 < N) (hy : 0 < y) :
    cuspWeightProfile N y ≤ cuspWeightLimit y := by
  have hp : N*y/(N+y) ≤ y := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  exact add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hp (Real.smoothTransition.nonneg (y-2)))

theorem cuspWeightLimit_height_le (y : ℝ) (hy : 0 < y) : y ≤ 3*cuspWeightLimit y := by
  by_cases h3 : 3 ≤ y
  · rw [cuspWeightLimit,cutoff_high y h3,one_mul]
    nlinarith [cuspWeightBase_one_le]
  · have hm : cuspWeightBase ≤ cuspWeightLimit y :=
      le_add_of_nonneg_right (mul_nonneg (Real.smoothTransition.nonneg (y-2)) hy.le)
    linarith [cuspWeightBase_one_le]

theorem cuspWeightProfile_hasDerivAt (N y : ℝ) (hN : 0 < N) (hy : 0 < y) :
    HasDerivAt (cuspWeightProfile N)
      (deriv cuspWeightCutoff y*(N*y/(N+y))+
        cuspWeightCutoff y*(N^2/(N+y)^2)) y := by
  have hη := (cutoff_smooth.differentiable (by simp)).differentiableAt.hasDerivAt (x := y)
  have hp : HasDerivAt (fun x : ℝ => N*x/(N+x)) (N^2/(N+y)^2) y := by
    apply (((hasDerivAt_id y).const_mul N).div
      ((hasDerivAt_id y).const_add N) (by positivity : N+y ≠ 0)).congr_deriv
    simp only [id_eq]
    ring
  simpa only [cuspWeightProfile,Pi.mul_apply] using! (hη.mul hp).const_add cuspWeightBase

/-- The logarithmic slope is bounded independently of the truncation parameter. -/
theorem cuspWeightProfile_gradient_bound (N y : ℝ) (hN : 0 < N) (hy : 0 < y) :
    |y*deriv (cuspWeightProfile N) y| ≤ (3/2:ℝ)*cuspWeightProfile N y := by
  let p := N*y/(N+y)
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hpy : p ≤ y := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  have hB := cuspWeightSlopeBound_nonneg
  have he0 : 0 ≤ cuspWeightCutoff y := Real.smoothTransition.nonneg _
  have hfirst : |y*deriv cuspWeightCutoff y*p| ≤ 9*cuspWeightSlopeBound := by
    by_cases hmid : y ∈ Icc (2:ℝ) 3
    · have hd := exists_slope_bound.choose_spec.2 y hmid
      have hyp : y*p ≤ 9 := by
        calc
          y*p ≤ y*y := mul_le_mul_of_nonneg_left hpy hy.le
          _ ≤ 3*3 := mul_le_mul hmid.2 hmid.2 hy.le (by norm_num)
          _ = 9 := by norm_num
      calc
        _ = (y*p)*|deriv cuspWeightCutoff y| := by
          rw [abs_mul,abs_mul,abs_of_pos hy,abs_of_nonneg hp0]
          ring
        _ ≤ (y*p)*cuspWeightSlopeBound := mul_le_mul_of_nonneg_left hd (mul_nonneg hy.le hp0)
        _ ≤ _ := mul_le_mul_of_nonneg_right hyp hB
    · have hd : deriv cuspWeightCutoff y = 0 := cutoff_deriv_zero y (by
        simp only [mem_Icc,not_and_or,not_le] at hmid
        exact hmid)
      simp only [hd,mul_zero,zero_mul,abs_zero]
      positivity
  have hsecond : 0 ≤ cuspWeightCutoff y*(y*(N^2/(N+y)^2)) := by positivity
  have hsecond_le : cuspWeightCutoff y*(y*(N^2/(N+y)^2)) ≤ cuspWeightCutoff y*p := by
    apply mul_le_mul_of_nonneg_left _ he0
    have hr : N/(N+y) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    calc
      _ = (N/(N+y))*p := by
        dsimp [p]
        field_simp [ne_of_gt (add_pos hN hy)]
      _ ≤ 1*p := mul_le_mul_of_nonneg_right hr hp0
      _ = _ := one_mul _
  rw [(cuspWeightProfile_hasDerivAt N y hN hy).deriv]
  have habs : |y*(deriv cuspWeightCutoff y*p+cuspWeightCutoff y*(N^2/(N+y)^2))| ≤
      9*cuspWeightSlopeBound+cuspWeightCutoff y*p := by
    calc
      _ = |y*deriv cuspWeightCutoff y*p+cuspWeightCutoff y*(y*(N^2/(N+y)^2))| := by congr 1; ring
      _ ≤ |y*deriv cuspWeightCutoff y*p|+|cuspWeightCutoff y*(y*(N^2/(N+y)^2))| := abs_add_le _ _
      _ ≤ _ := by rw [abs_of_nonneg hsecond]; exact add_le_add hfirst hsecond_le
  change |y*(deriv cuspWeightCutoff y*p+cuspWeightCutoff y*(N^2/(N+y)^2))| ≤ _
  apply habs.trans
  change 9*cuspWeightSlopeBound+cuspWeightCutoff y*p ≤
    (3/2:ℝ)*(18*cuspWeightSlopeBound+1+cuspWeightCutoff y*p)
  nlinarith [mul_nonneg he0 hp0]

/-- Every bounded weight is smooth at every positive height. -/
theorem cuspWeightProfile_contDiffAt (N y : ℝ) (hN : 0 < N) (hy : 0 < y) :
    ContDiffAt ℝ ∞ (cuspWeightProfile N) y := by
  exact contDiffAt_const.add (cutoff_smooth.contDiffAt.mul
    ((contDiffAt_const.mul contDiffAt_id).div (contDiffAt_const.add contDiffAt_id)
      (ne_of_gt (add_pos hN hy))))

end
end RHTower.D4BMJointWave
