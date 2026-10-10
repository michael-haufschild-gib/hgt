import GaloisForLFunctions.RHTower.PaperKreinWallFourierModel
import GaloisForLFunctions.HTGeometry.PaperIntervalWallEnergy

/-! # A singular Fourier completion of the native Krein chambers

Continuous finite Fourier sums reconstruct the actual rigged time-axis action outside one
null set, simultaneously at all source heights and for all vector assignments at the wall.
Every cutoff is zero at the wall. Hence Fourier recovery of the assigned wall vector occurs
exactly when that vector is zero, while the whole chamber geometry survives almost everywhere.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry MeasureTheory Filter Set Topology
open PreDivisorReflectionDefectStabilization

/-- One actual rigged vector for every Fourier depth and source position. -/
def paperKreinWallFourierSum (N : ℕ) (x : ℝ) : DeningerHeightKothe :=
  fourierPartialSum (paperIntervalWallStep 0) N x • preDivisorRiggedPrimeTimeAxis

theorem paperKreinWallFourierSum_continuous (N : ℕ) :
    Continuous (paperKreinWallFourierSum N) :=
  (continuous_fourierPartialSum (paperIntervalWallStep 0) N).smul continuous_const

/-- Coordinatewise Fourier summation is the coordinate of this single rigged vector. -/
theorem paperKreinWallFourierSum_coordinate (t : ℝ) (v : DeningerHeightKothe)
    (q : DeningerPrimeLattice) (N : ℕ) (x : ℝ) :
    (paperKreinWallFourierSum N x : DeningerPrimeLattice → ℂ) q =
      fourierPartialSum
        (fun y => (paperKreinWallCompletion t v y : DeningerPrimeLattice → ℂ) q) N x := by
  rw [paperKreinWallCompletion_partialSum]
  change fourierPartialSum (paperIntervalWallStep 0) N x *
    (preDivisorRiggedPrimeTimeAxis : DeningerPrimeLattice → ℂ) q = _
  exact mul_comm _ _

theorem paperKreinWallFourierSum_wall (N : ℕ) : paperKreinWallFourierSum N (1 / 2) = 0 := by
  rw [paperKreinWallFourierSum, paperIntervalWallStep_partialSum_wall, zero_smul]

/-- Spectral recovery at the wall characterizes its zero vector exactly. -/
theorem paperKreinWallFourierSum_recovery_at_wall_iff (t : ℝ) (v : DeningerHeightKothe) :
    Tendsto (fun N => paperKreinWallFourierSum N (1 / 2)) atTop
      (𝓝 (paperKreinWallCompletion t v (1 / 2))) ↔ v = 0 := by
  simp only [paperKreinWallFourierSum_wall, paperKreinWallCompletion_wall]
  constructor
  · intro h
    exact tendsto_nhds_unique h tendsto_const_nhds
  · rintro rfl
    exact tendsto_const_nhds

/-- One null set works before choosing either the height or any of the possible wall vectors. -/
theorem paperKreinWallFourierSum_common_convergence :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ x ∈ Ioc (0 : ℝ) 1, x ∉ E → ∀ (t : ℝ) (v : DeningerHeightKothe),
        Tendsto (fun N => paperKreinWallFourierSum N x) atTop
          (𝓝 (paperKreinWallCompletion t v x)) := by
  obtain ⟨E, hEm, hEz, hE⟩ := paperIntervalWallStep_common_convergence
  refine ⟨E ∪ {1 / 2}, hEm.union (measurableSet_singleton _),
    measure_union_null hEz (measure_singleton _), ?_⟩
  intro x hx hxe t v
  have hxE : x ∉ E := fun h => hxe (Or.inl h)
  have hxw : x ≠ 1 / 2 := fun h => hxe (Or.inr h)
  have hs := paperKreinWallSource_action t ⟨x, hx.1.le, hx.2⟩
  rw [paperKreinWallCompletion, if_neg hxw, hs]
  exact (hE x hx hxE 0).smul_const preDivisorRiggedPrimeTimeAxis

/-- In particular the canonical, unmodified source-selected action is reconstructed. -/
theorem paperKreinWallFourierSum_native_convergence :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ x ∈ Ioc (0 : ℝ) 1, x ∉ E → ∀ t : ℝ,
        Tendsto (fun N => paperKreinWallFourierSum N x) atTop
          (𝓝 (preDivisorRiggedPrimeFundamentalSymmetry (paperKreinWallSourcePoint t x)
            preDivisorRiggedPrimeTimeAxis)) := by
  obtain ⟨E, hm, hz, hE⟩ := paperKreinWallFourierSum_common_convergence
  exact ⟨E, hm, hz, fun x hx he t => by
    simpa only [paperKreinWallCompletion_zero] using hE x hx he t 0⟩

/-- All lattice-coordinate chamber energies are retained, independently of the wall vector. -/
theorem paperKreinWallCompletion_spectral_energy (t : ℝ) (v : DeningerHeightKothe)
    (q : DeningerPrimeLattice) :
    HasSum (fun k : ℤ => ‖l2Pair (fourierChar k)
      (fun x => (paperKreinWallCompletion t v x : DeningerPrimeLattice → ℂ) q)‖ ^ 2)
      (‖(preDivisorRiggedPrimeTimeAxis : DeningerPrimeLattice → ℂ) q‖ ^ 2) := by
  simpa only [paperKreinWallCompletion_coefficient, norm_mul, mul_pow, mul_one] using
    (paperIntervalWallStep_parseval 0).mul_left
      (‖(preDivisorRiggedPrimeTimeAxis : DeningerPrimeLattice → ℂ) q‖ ^ 2)

/-- The actual first-prime observer obstructs uniform recovery for every possible wall vector. -/
theorem paperKreinWallCompletion_not_uniform (t : ℝ) (v : DeningerHeightKothe) :
    ¬ TendstoUniformlyOn (fun N => fourierPartialSum
        (fun x => (paperKreinWallCompletion t v x : DeningerPrimeLattice → ℂ)
          (preDivisorRiggedPrimeAxis (nthPrimePoint 0))) N)
      (fun x => (paperKreinWallCompletion t v x : DeningerPrimeLattice → ℂ)
          (preDivisorRiggedPrimeAxis (nthPrimePoint 0))) atTop (Icc (0 : ℝ) 1) := by
  intro h
  let w := (v : DeningerPrimeLattice → ℂ) (preDivisorRiggedPrimeAxis (nthPrimePoint 0))
  have he := h.congr_right (g := paperIntervalWallStep w) (fun x hx =>
    paperKreinWallCompletion_first_coordinate t v ⟨x, hx⟩)
  apply paperIntervalWallStep_not_uniform w
  apply he.congr
  exact Eventually.of_forall fun N x _ => by
    rw [paperKreinWallCompletion_partialSum, paperKreinTimeAxis_first_coordinate, one_mul]
    exact (paperIntervalWallStep_partialSum w 0 N x).symm

end
end RHTower
