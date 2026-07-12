import GaloisForLFunctions.RHTower.XiCTaylorSuperaccurateSchedule
import GaloisForLFunctions.RHTower.XiTaylorAnisotropicMesh

/-!
# Reading a super-accurate Xi Taylor schedule on the anisotropic mesh

The Taylor schedule controls the closed ball whose radius is its schedule parameter.  To evaluate
it on a moving anisotropic mesh without any separate compactness hypothesis, enlarge the parameter
by the ceiling of the actual centered evaluation norm.  The resulting index is explicit, is at
least the mesh resolution, and places the evaluation point in the controlled ball tautologically.
-/

open Complex Metric Filter Topology

namespace RHTower

noncomputable section

/-- The centered Xi coordinate of the right-approximating anisotropic mesh point. -/
def xiCTaylorAnisotropicCenteredPoint (sigma : ℂ) (n : ℕ) : ℂ :=
  xiCTaylorCenteredPoint (xiTaylorAnisotropicRightApprox sigma (n + 1))

@[simp] theorem half_add_xiCTaylorCenteredPoint_mul_I (s : ℂ) :
    1 / 2 + xiCTaylorCenteredPoint s * I = s := by
  rw [xiCTaylorCenteredPoint, mul_assoc]
  have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
  rw [hI, mul_one]
  ring

@[simp] theorem XiC_xiCTaylorCenteredPoint (s : ℂ) :
    XiC (xiCTaylorCenteredPoint s) = xi s := by
  simp only [XiC, half_add_xiCTaylorCenteredPoint_mul_I]

/-- The centered anisotropic points converge to the centered target. -/
theorem tendsto_xiCTaylorAnisotropicCenteredPoint (sigma : ℂ) :
    Tendsto (xiCTaylorAnisotropicCenteredPoint sigma) atTop
      (nhds (xiCTaylorCenteredPoint sigma)) := by
  have hs : Tendsto
      (fun n : ℕ => xiTaylorAnisotropicRightApprox sigma (n + 1)) atTop
      (nhds sigma) :=
    (tendsto_xiTaylorAnisotropicRightApprox_succ sigma).mono_right nhdsWithin_le_nhds
  have hc : Continuous xiCTaylorCenteredPoint := by
    unfold xiCTaylorCenteredPoint
    fun_prop
  exact hc.continuousAt.tendsto.comp hs

/-- The source-selected Taylor schedule stage used at anisotropic mesh resolution `n + 1`.
The norm ceiling makes expanding-ball membership automatic. -/
def xiCTaylorAnisotropicScheduleStage (sigma : ℂ) (n : ℕ) : ℕ :=
  n + 1 + ⌈‖xiCTaylorAnisotropicCenteredPoint sigma n‖⌉₊

theorem succ_le_xiCTaylorAnisotropicScheduleStage (sigma : ℂ) (n : ℕ) :
    n + 1 ≤ xiCTaylorAnisotropicScheduleStage sigma n := by
  simp only [xiCTaylorAnisotropicScheduleStage]
  omega

/-- At the anisotropic stage, the schedule tolerance eventually dominates any prescribed fixed
inverse power of the mesh resolution. -/
theorem xiCTaylorScheduleTolerance_stage_le_inv_pow
    (sigma : ℂ) {d n : ℕ} (hd : d ≤ n + 1) :
    xiCTaylorScheduleTolerance (xiCTaylorAnisotropicScheduleStage sigma n) ≤
      ((((n + 1 : ℕ) : ℝ) ^ d)⁻¹) := by
  let k : ℕ := xiCTaylorAnisotropicScheduleStage sigma n
  have hnk : n + 1 ≤ k := succ_le_xiCTaylorAnisotropicScheduleStage sigma n
  have hbase : (((n + 1 : ℕ) : ℝ)) ≤ (((k + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show n + 1 ≤ k + 1 by omega)
  have hbasePow : (((n + 1 : ℕ) : ℝ)) ^ d ≤ (((k + 1 : ℕ) : ℝ)) ^ d :=
    pow_le_pow_left₀ (by positivity) hbase d
  have hdk : d ≤ k + 1 := by omega
  have hexpPow : (((k + 1 : ℕ) : ℝ)) ^ d ≤ (((k + 1 : ℕ) : ℝ)) ^ (k + 1) :=
    pow_le_pow_right₀ (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k))) hdk
  unfold xiCTaylorScheduleTolerance
  change ((((k + 1 : ℕ) : ℝ) ^ (k + 1))⁻¹) ≤
    ((((n + 1 : ℕ) : ℝ) ^ d)⁻¹)
  exact inv_anti₀ (by positivity) (hbasePow.trans hexpPow)

/-- The centered mesh point lies in the expanding ball controlled by its explicit schedule
stage. -/
theorem xiCTaylorAnisotropicCenteredPoint_mem_closedBall_stage
    (sigma : ℂ) (n : ℕ) :
    xiCTaylorAnisotropicCenteredPoint sigma n ∈
      closedBall (0 : ℂ) (xiCTaylorAnisotropicScheduleStage sigma n) := by
  rw [mem_closedBall, dist_zero_right]
  calc
    ‖xiCTaylorAnisotropicCenteredPoint sigma n‖ ≤
        (⌈‖xiCTaylorAnisotropicCenteredPoint sigma n‖⌉₊ : ℝ) :=
      Nat.le_ceil _
    _ ≤ (xiCTaylorAnisotropicScheduleStage sigma n : ℝ) := by
      exact_mod_cast (show ⌈‖xiCTaylorAnisotropicCenteredPoint sigma n‖⌉₊ ≤
        xiCTaylorAnisotropicScheduleStage sigma n by
          simp only [xiCTaylorAnisotropicScheduleStage]
          omega)

/-- A super-accurate schedule gives its simultaneous value and derivative estimates at the
moving centered anisotropic mesh point, with no compact-set side condition left to discharge. -/
theorem xiCTaylorSuperaccurateSchedule_at_anisotropicCenteredPoint
    {N : ℕ → ℕ} (hN : XiCTaylorSuperaccurateSchedule N)
    (sigma : ℂ) (n : ℕ) :
    dist
        (XiC (xiCTaylorAnisotropicCenteredPoint sigma n))
        (xiCTaylorApprox
          (N (xiCTaylorAnisotropicScheduleStage sigma n))
          (xiCTaylorAnisotropicCenteredPoint sigma n)) <
        xiCTaylorScheduleTolerance (xiCTaylorAnisotropicScheduleStage sigma n) ∧
      dist
        (deriv XiC (xiCTaylorAnisotropicCenteredPoint sigma n))
        (deriv
          (xiCTaylorApprox (N (xiCTaylorAnisotropicScheduleStage sigma n)))
          (xiCTaylorAnisotropicCenteredPoint sigma n)) <
        xiCTaylorScheduleTolerance (xiCTaylorAnisotropicScheduleStage sigma n) := by
  exact hN.2 _ _
    (xiCTaylorAnisotropicCenteredPoint_mem_closedBall_stage sigma n)

end

end RHTower
