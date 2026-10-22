import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureUniformGridAliasNoGo
import Mathlib.Algebra.Field.Periodic

/-!+# Uniform phase quantization for the physical HCF reporter

Reduce actual ordinates modulo one, then use the left node of their uniform phase
bin. The reporter error tends to zero uniformly over all real ordinates, hence
independently of the arithmetic cutoff, weights, and phase shift.
-/

open GaloisForLFunctions.HTGeometry Filter Topology Set

namespace RHTower

noncomputable section

/-- Reindexing the physical lattice, without appealing to a formal Fourier surrogate. -/
theorem paperCriticalFeaturePeriodization_periodic :
    Function.Periodic criticalFeatureRealBoundaryPeriodization 1 := by
  intro x
  unfold criticalFeatureRealBoundaryPeriodization
  calc
    (∑' n : ℤ, criticalFeatureRealBoundaryWeight 0 (x + 1 + n)) =
        ∑' n : ℤ, criticalFeatureRealBoundaryWeight 0 (x + ((n + 1 : ℤ) : ℝ)) := by
      congr 1
      funext n
      congr 1
      push_cast
      ring
    _ = ∑' n : ℤ, criticalFeatureRealBoundaryWeight 0 (x + n) :=
      (Equiv.addRight (1 : ℤ)).tsum_eq
        (fun n : ℤ => criticalFeatureRealBoundaryWeight 0 (x + n))

theorem paperCriticalFeaturePeriodization_fract (x : ℝ) :
    criticalFeatureRealBoundaryPeriodization (Int.fract x) =
      criticalFeatureRealBoundaryPeriodization x := by
  simpa only [Int.fract, zsmul_eq_mul, mul_one] using
    paperCriticalFeaturePeriodization_periodic.sub_zsmul_eq (x := x) (Int.floor x)

/-- The actual left phase-bin index, defined for every real ordinate. -/
def paperCriticalFeaturePhaseBin (N : ℕ) (x : ℝ) : Fin (N + 1) :=
  ⟨⌊Int.fract x * ((N + 1 : ℕ) : ℝ)⌋₊, by
    apply (Nat.floor_lt (mul_nonneg (Int.fract_nonneg x) (Nat.cast_nonneg _))).mpr
    simpa only [one_mul] using mul_lt_mul_of_pos_right (Int.fract_lt_one x)
      (by positivity : (0 : ℝ) < ((N + 1 : ℕ) : ℝ))⟩

def paperCriticalFeaturePhaseNode (N : ℕ) (x : ℝ) : ℝ :=
  uniformNode 0 1 (N + 1) (paperCriticalFeaturePhaseBin N x)

theorem paperCriticalFeaturePhaseNode_mem (N : ℕ) (x : ℝ) :
    paperCriticalFeaturePhaseNode N x ∈ Icc (0 : ℝ) 1 :=
  uniformNode_mem_Icc zero_le_one (Nat.succ_pos N) (paperCriticalFeaturePhaseBin N x).isLt.le

/-- The left phase node is no more than one mesh width from the fractional ordinate. -/
theorem paperCriticalFeaturePhaseNode_dist (N : ℕ) (x : ℝ) :
    dist (Int.fract x) (paperCriticalFeaturePhaseNode N x) < 1 / ((N + 1 : ℕ) : ℝ) := by
  have hd : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hnonneg : 0 ≤ Int.fract x * ((N + 1 : ℕ) : ℝ) :=
    mul_nonneg (Int.fract_nonneg x) hd.le
  have hlo := Nat.floor_le hnonneg
  have hhi := Nat.lt_floor_add_one (Int.fract x * ((N + 1 : ℕ) : ℝ))
  have hnode : paperCriticalFeaturePhaseNode N x =
      (⌊Int.fract x * ((N + 1 : ℕ) : ℝ)⌋₊ : ℝ) / ((N + 1 : ℕ) : ℝ) := by
    simp [paperCriticalFeaturePhaseNode, paperCriticalFeaturePhaseBin, uniformNode]
  have hle : paperCriticalFeaturePhaseNode N x ≤ Int.fract x := by
    rw [hnode]
    exact (div_le_iff₀ hd).mpr hlo
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hle)]
  apply (lt_div_iff₀ hd).mpr
  rw [sub_mul, hnode, div_mul_cancel₀ _ hd.ne']
  linarith

private theorem reporter_error_bound (N : ℕ) (x : ℝ) :
    |criticalFeatureRealBoundaryPeriodization x -
      criticalFeatureRealBoundaryPeriodization (paperCriticalFeaturePhaseNode N x)| ≤
        (37 : ℝ) / 100 := by
  have hx := abs_le.mp (abs_criticalFeatureRealBoundaryPeriodization_sub_two_pi_le x)
  have hy := abs_le.mp (abs_criticalFeatureRealBoundaryPeriodization_sub_two_pi_le
    (paperCriticalFeaturePhaseNode N x))
  apply abs_le.mpr
  constructor <;> linarith

private theorem reporter_error_bdd (N : ℕ) :
    BddAbove (Set.range fun x : ℝ => |criticalFeatureRealBoundaryPeriodization x -
      criticalFeatureRealBoundaryPeriodization (paperCriticalFeaturePhaseNode N x)|) := by
  refine ⟨(37 : ℝ) / 100, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact reporter_error_bound N x

/-- A uniform error budget for replacing actual phases by grid nodes. -/
def paperCriticalFeatureQuantizationError (N : ℕ) : ℝ :=
  ⨆ x : ℝ, |criticalFeatureRealBoundaryPeriodization x -
    criticalFeatureRealBoundaryPeriodization (paperCriticalFeaturePhaseNode N x)|

theorem paperCriticalFeaturePhaseNode_error_le (N : ℕ) (x : ℝ) :
    |criticalFeatureRealBoundaryPeriodization x -
      criticalFeatureRealBoundaryPeriodization (paperCriticalFeaturePhaseNode N x)| ≤
        paperCriticalFeatureQuantizationError N :=
  le_ciSup (reporter_error_bdd N) x

theorem paperCriticalFeatureQuantizationError_nonneg (N : ℕ) :
    0 ≤ paperCriticalFeatureQuantizationError N :=
  (abs_nonneg _).trans (paperCriticalFeaturePhaseNode_error_le N 0)

theorem paperCriticalFeatureQuantizationError_le (N : ℕ) :
    paperCriticalFeatureQuantizationError N ≤ (37 : ℝ) / 100 :=
  ciSup_le (reporter_error_bound N)

/-- Quantization error vanishes uniformly, including for moving arithmetic sources. -/
theorem paperCriticalFeatureQuantizationError_tendsto :
    Tendsto paperCriticalFeatureQuantizationError atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  have huniform : UniformContinuousOn criticalFeatureRealBoundaryPeriodization (Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous
      continuous_criticalFeatureRealBoundaryPeriodization.continuousOn
  obtain ⟨delta, hdelta, hdeltaSpec⟩ :=
    Metric.uniformContinuousOn_iff.mp huniform (eps / 2) (half_pos heps)
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / delta)
  refine ⟨K, fun N hN => ?_⟩
  have hmesh : 1 / ((N + 1 : ℕ) : ℝ) < delta := by
    have hd : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    have hKN : (K : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ_of_le hN
    have hprod := (div_lt_iff₀ hdelta).mp hK
    apply (div_lt_iff₀ hd).mpr
    nlinarith
  have herror : paperCriticalFeatureQuantizationError N ≤ eps / 2 := by
    apply ciSup_le
    intro x
    have hfrac : Int.fract x ∈ Icc (0 : ℝ) 1 :=
      ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
    have h := hdeltaSpec (Int.fract x) hfrac (paperCriticalFeaturePhaseNode N x)
      (paperCriticalFeaturePhaseNode_mem N x)
      ((paperCriticalFeaturePhaseNode_dist N x).trans hmesh)
    rw [Real.dist_eq, paperCriticalFeaturePeriodization_fract] at h
    exact h.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (paperCriticalFeatureQuantizationError_nonneg N)]
  exact herror.trans_lt (half_lt_self heps)

end

end RHTower
