import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiCheckpointAffineEventCurrent
import GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilXiScrewGreenConnection

/-!
# Signed curvature measure behind the CCM-FU Suzuki event current

Removing Suzuki's smooth within-cell Bregman remainder leaves a piecewise-affine arithmetic
current.  This module identifies its slope jump with one literal signed curvature cell:

`integral K - critical Mellin atom`.

The positive endpoint resets are substantially smaller than their prior unit bound: they are
`O(N⁻³ᐟ²)` and hence absolutely summable.  The exact endpoint source is therefore a base affine
memory plus the discrete Green potential of the signed prime--archimedean curvature cells, modulo
one uniformly bounded reset prefix.  No prime or archimedean term is estimated separately in the
signed cell.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set
open GaloisForLFunctions.RHTower
open scoped Interval

/-- Literal signed curvature carried by the `N`th logarithmic event cell: smooth Suzuki curvature
minus the critical Mellin atom born at the right endpoint. -/
def suzukiCheckpointSignedCurvatureCell (N : ℕ) : ℝ :=
  (∫ t in Real.log (N : ℝ)..Real.log ((N + 1 : ℕ) : ℝ),
    screwRegularKernel t) - criticalMellinAtomWeight (N + 1)

/-- The signed curvature cell is exactly the jump of the floor-selected affine slope. -/
theorem suzukiCheckpointAffineSlope_succ_sub_eq_signedCurvatureCell
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiCheckpointAffineSlope (N + 1) - suzukiCheckpointAffineSlope N =
      suzukiCheckpointSignedCurvatureCell N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hNp1pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hlogle : Real.log (N : ℝ) ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
    (Real.log_le_log_iff hNpos hNp1pos).mpr (by exact_mod_cast Nat.le_succ N)
  have hderiv : ∀ t ∈ Set.uIcc (Real.log (N : ℝ))
      (Real.log ((N + 1 : ℕ) : ℝ)),
      HasDerivAt suzukiCheckpointReservoirDeriv (screwRegularKernel t) t := by
    intro t ht
    rw [Set.uIcc_of_le hlogle] at ht
    exact hasDerivAt_suzukiCheckpointReservoirDeriv (hlogNpos.trans_le ht.1)
  have hint : IntervalIntegrable screwRegularKernel volume
      (Real.log (N : ℝ)) (Real.log ((N + 1 : ℕ) : ℝ)) := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_screwRegularKernel.mono (by
      intro t ht
      rw [Set.uIcc_of_le hlogle] at ht
      exact hlogNpos.trans_le ht.1)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [suzukiCheckpointAffineSlope_succ_sub hN]
  unfold suzukiCheckpointSignedCurvatureCell
  rw [hFTC, criticalMellinAtomWeight_eq_screwPrimeWeight (by omega : 0 < N + 1)]

/-- Every affine event slope is its first-event slope plus the accumulated signed curvature
measure. -/
theorem suzukiCheckpointAffineSlope_eq_base_add_sum_signedCurvatureCell
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiCheckpointAffineSlope N = suzukiCheckpointAffineSlope 2 +
      ∑ j ∈ Finset.Ico 2 N, suzukiCheckpointSignedCurvatureCell j := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
      rw [Finset.sum_Ico_succ_top hN, ← add_assoc, ← ih]
      rw [← suzukiCheckpointAffineSlope_succ_sub_eq_signedCurvatureCell hN]
      ring

/-- Sharp event-scale improvement over the prior unit reset bound. -/
theorem suzukiCheckpointEventCurvatureJump_le_sqrt_div_sq
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiCheckpointEventCurvatureJump N ≤
      Real.sqrt ((N + 1 : ℕ) : ℝ) / (N : ℝ) ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNp1pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hNle : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ N
  have hlog : Real.log (N : ℝ) ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
    (Real.log_le_log_iff hNpos hNp1pos).mpr hNle
  have hbase := suzukiCheckpointBregman_nonneg_le_exp_max_mul_sq hN
    (show Real.log ((N + 1 : ℕ) : ℝ) ∈ suzukiCheckpointCell N from ⟨hlog, le_rfl⟩)
    (show Real.log (N : ℝ) ∈ suzukiCheckpointCell N from ⟨le_rfl, hlog⟩)
  have hgap : Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ) ≤ 1 / (N : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hNp1pos hNpos)
    rw [Real.log_div hNp1pos.ne' hNpos.ne'] at h
    calc
      _ ≤ ((N + 1 : ℕ) : ℝ) / (N : ℝ) - 1 := h
      _ = 1 / (N : ℝ) := by
        push_cast
        field_simp [hNpos.ne']
        ring
  have hgap0 : 0 ≤ Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ) :=
    sub_nonneg.mpr hlog
  have hgapSq :
      (Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)) ^ 2 ≤
        (1 / (N : ℝ)) ^ 2 := by
    nlinarith
  have hsqrt : Real.exp (Real.log ((N + 1 : ℕ) : ℝ) / 2) =
      Real.sqrt ((N + 1 : ℕ) : ℝ) := by
    rw [← Real.log_sqrt hNp1pos.le, Real.exp_log (Real.sqrt_pos.mpr hNp1pos)]
  unfold suzukiCheckpointEventCurvatureJump
  calc
    _ ≤ Real.exp
        (max (Real.log ((N + 1 : ℕ) : ℝ)) (Real.log (N : ℝ)) / 2) *
          (Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)) ^ 2 := hbase.2
    _ = Real.sqrt ((N + 1 : ℕ) : ℝ) *
          (Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)) ^ 2 := by
      rw [max_eq_left hlog, hsqrt]
    _ ≤ Real.sqrt ((N + 1 : ℕ) : ℝ) * (1 / (N : ℝ)) ^ 2 := by
      gcongr
    _ = Real.sqrt ((N + 1 : ℕ) : ℝ) / (N : ℝ) ^ 2 := by
      field_simp [hNpos.ne']

/-- Endpoint reset packets have finite total variation. -/
theorem summable_suzukiCheckpointEventCurvatureJump :
    Summable suzukiCheckpointEventCurvatureJump := by
  have hpow : Summable (fun N : ℕ =>
      2 * (N : ℝ) ^ (-(3 / 2 : ℝ))) :=
    (Real.summable_nat_rpow.mpr (by norm_num)).mul_left 2
  have hmajor : Summable (fun N : ℕ =>
      2 * Real.sqrt (N : ℝ) / (N : ℝ) ^ 2) := by
    refine hpow.congr (fun N => ?_)
    symm
    by_cases hN0 : N = 0
    · simp [hN0]
    · have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
      rw [Real.sqrt_eq_rpow,
        show (-(3 / 2 : ℝ)) = (1 / 2 : ℝ) - 2 by ring,
        Real.rpow_sub hNpos, Real.rpow_two]
      ring
  refine Summable.of_norm_bounded_eventually_nat hmajor ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with N hN
  have hq := suzukiCheckpointEventCurvatureJump_mem_unitInterval hN
  have hsqrt : Real.sqrt ((N + 1 : ℕ) : ℝ) ≤
      2 * Real.sqrt (N : ℝ) := by
    have hN0 : (0 : ℝ) ≤ N := by positivity
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · rw [sq]
      have hsq := Real.sq_sqrt hN0
      have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
      push_cast
      nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg hq.1]
  exact (suzukiCheckpointEventCurvatureJump_le_sqrt_div_sq hN).trans (by
    gcongr)

/-- Reset packets have a uniform total-variation budget over every finite event prefix. -/
theorem exists_uniform_bound_suzukiCheckpointEventCurvatureJump_prefix :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |∑ j ∈ Finset.Ico 2 N, suzukiCheckpointEventCurvatureJump j| ≤ C := by
  let C : ℝ := ∑' j : ℕ, |suzukiCheckpointEventCurvatureJump j|
  have hsum : Summable (fun j : ℕ => |suzukiCheckpointEventCurvatureJump j|) :=
    summable_suzukiCheckpointEventCurvatureJump.abs
  refine ⟨C, tsum_nonneg (fun _ => abs_nonneg _), ?_⟩
  intro N
  calc
    |∑ j ∈ Finset.Ico 2 N, suzukiCheckpointEventCurvatureJump j| ≤
        ∑ j ∈ Finset.Ico 2 N, |suzukiCheckpointEventCurvatureJump j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ C := hsum.sum_le_tsum _ (fun _ _ => abs_nonneg _)

/-- Finite discrete Green potential of the signed prime--archimedean event curvature. -/
def suzukiCheckpointSignedCurvatureGreenPotential (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico 2 N, suzukiCheckpointSignedCurvatureCell j *
    (Real.log (N : ℝ) - Real.log ((j + 1 : ℕ) : ℝ))

/-- Successor law for the signed curvature Green potential. -/
theorem suzukiCheckpointSignedCurvatureGreenPotential_succ
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiCheckpointSignedCurvatureGreenPotential (N + 1) =
      suzukiCheckpointSignedCurvatureGreenPotential N +
        (suzukiCheckpointAffineSlope N - suzukiCheckpointAffineSlope 2) *
          (Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)) := by
  have hslope := suzukiCheckpointAffineSlope_eq_base_add_sum_signedCurvatureCell hN
  have hslopeDiff : suzukiCheckpointAffineSlope N - suzukiCheckpointAffineSlope 2 =
      ∑ j ∈ Finset.Ico 2 N, suzukiCheckpointSignedCurvatureCell j := by
    linarith
  unfold suzukiCheckpointSignedCurvatureGreenPotential
  rw [Finset.sum_Ico_succ_top hN]
  simp only [sub_self, mul_zero, add_zero]
  rw [hslopeDiff]
  calc
    (∑ j ∈ Finset.Ico 2 N, suzukiCheckpointSignedCurvatureCell j *
        (Real.log ((N + 1 : ℕ) : ℝ) - Real.log ((j + 1 : ℕ) : ℝ))) =
      ∑ j ∈ Finset.Ico 2 N,
        (suzukiCheckpointSignedCurvatureCell j *
            (Real.log (N : ℝ) - Real.log ((j + 1 : ℕ) : ℝ)) +
          suzukiCheckpointSignedCurvatureCell j *
            (Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ))) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = (∑ j ∈ Finset.Ico 2 N, suzukiCheckpointSignedCurvatureCell j *
            (Real.log (N : ℝ) - Real.log ((j + 1 : ℕ) : ℝ))) +
          ∑ j ∈ Finset.Ico 2 N, suzukiCheckpointSignedCurvatureCell j *
            (Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)) := by
          rw [Finset.sum_add_distrib]
    _ = _ := by rw [Finset.sum_mul]

/-- Exact endpoint Green formula: all non-affine source growth is a signed prime--archimedean
Green potential plus an absolutely summable positive reset prefix. -/
theorem suzukiPsi_log_nat_eq_affine_add_signedCurvatureGreen_add_resets
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiPsi (Real.log (N : ℝ)) =
      suzukiPsi (Real.log 2) +
        suzukiCheckpointAffineSlope 2 * (Real.log (N : ℝ) - Real.log 2) +
        suzukiCheckpointSignedCurvatureGreenPotential N +
        ∑ j ∈ Finset.Ico 2 N, suzukiCheckpointEventCurvatureJump j := by
  induction N, hN using Nat.le_induction with
  | base => simp [suzukiCheckpointSignedCurvatureGreenPotential]
  | succ N hN ih =>
      rw [suzukiCheckpoint_endpoint_recurrence_affineSlope_curvature hN, ih,
        suzukiCheckpointSignedCurvatureGreenPotential_succ hN,
        Finset.sum_Ico_succ_top hN]
      ring

end RHTower
