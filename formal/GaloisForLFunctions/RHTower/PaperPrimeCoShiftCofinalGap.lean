import GaloisForLFunctions.RHTower.PaperPrimeCoShiftFiniteKernels

/-!
# The exact cofinal gap of arithmetic co-shift ground projections

Finite-prime kernel projections converge strongly to the full arithmetic ground projection.
Nevertheless, every finite projection stays operator-norm and essential-norm distance one from
that limit. The paper compact-ideal cost is infinite at every finite packet and zero at the limit.
The nonzero full ground line therefore lies outside the norm-closed arithmetic shift algebra.
-/

namespace RHTower.PrimeCoShift

noncomputable section

open Filter Topology GaloisForLFunctions.HTGeometry
open scoped Classical ENNReal

/-- Orthogonal projection onto the native all-prime common eigenspace. -/
def paperCoShiftGroundProjection (s : ℂ) : H →L[ℂ] H := (eigenSubmodule s).starProjection

/-- The all-prime ground projection has rank at most one and is always compact. -/
theorem paperCoShiftGroundProjection_compact (s : ℂ) :
    IsCompactOperator (paperCoShiftGroundProjection s) := by
  haveI : FiniteDimensional ℂ (eigenSubmodule s) := by
    by_cases hs : 1 / 2 < s.re
    · rw [eigenSubmodule_eq_span hs]
      infer_instance
    · rw [eigenSubmodule_eq_bot (le_of_not_gt hs)]
      infer_instance
  exact isCompactOperator_starProjection_finiteDimensional _

/-- The full ground projection vanishes exactly on and below the Hilbert threshold. -/
theorem paperCoShiftGroundProjection_eq_zero_iff (s : ℂ) :
    paperCoShiftGroundProjection s = 0 ↔ s.re ≤ 1 / 2 := by
  constructor
  · intro h
    by_contra hs
    have hs' : 1 / 2 < s.re := lt_of_not_ge hs
    have hfix : paperCoShiftGroundProjection s (groundState s) = groundState s :=
      Submodule.starProjection_eq_self_iff.mpr (groundState_mem_eigenSubmodule hs')
    rw [h, zero_apply] at hfix
    exact groundState_ne_zero hs' hfix.symm
  · intro hs
    simp [paperCoShiftGroundProjection, eigenSubmodule_eq_bot hs]

/-- Above the threshold the nonzero full ground projection is outside the closed shift algebra. -/
theorem paperCoShiftGroundProjection_mem_algebra_iff (s : ℂ) :
    paperCoShiftGroundProjection s ∈ paperPrimeCoShiftAlgebra ↔ s.re ≤ 1 / 2 := by
  constructor
  · intro h
    have hz := (paperPrimeCoShiftAlgebra_compact_iff_zero ⟨_, h⟩).mp
      (paperCoShiftGroundProjection_compact s)
    exact (paperCoShiftGroundProjection_eq_zero_iff s).mp
      (congrArg (fun A : paperPrimeCoShiftAlgebra => (A : H →L[ℂ] H)) hz)
  · intro h
    rw [(paperCoShiftGroundProjection_eq_zero_iff s).mpr h]
    exact zero_mem _

theorem paperCoShiftGroundProjection_traceCost (s : ℂ) :
    compactOperatorTraceCost H (paperCoShiftGroundProjection s) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr (paperCoShiftGroundProjection_compact s)

private theorem ground_le_finite (s : ℂ) (F : Finset Nat.Primes) :
    eigenSubmodule s ≤ F.inf (rowKer s) := by
  rw [eigenSubmodule_eq_iInf]
  exact Finset.le_inf fun p _ => iInf_le _ p

/-- The finite-prime kernel projections converge on every fixed Hilbert vector. -/
theorem paperCoShiftFiniteProjection_strong_tendsto (s : PaperCoShiftParameter) (x : H) :
    Tendsto (fun F : Finset Nat.Primes => paperCoShiftFiniteProjection s F x)
      atTop (𝓝 (paperCoShiftGroundProjection s.1 x)) := by
  have hinf : (⨅ F : Finset Nat.Primes, F.inf (rowKer s.1)) = eigenSubmodule s.1 := by
    rw [eigenSubmodule_eq_iInf]
    refine le_antisymm (le_iInf fun p => ?_)
      (le_iInf fun F => Finset.le_inf fun p _ => iInf_le _ p)
    exact (iInf_le _ ({p} : Finset Nat.Primes)).trans (by simp)
  haveI : (⨅ F : Finset Nat.Primes, F.inf (rowKer s.1)).HasOrthogonalProjection := by
    rw [hinf]
    infer_instance
  have hanti : Antitone (fun F : Finset Nat.Primes => F.inf (rowKer s.1)) :=
    fun _ _ h => Finset.inf_mono h
  have h := starProjection_tendsto_iInf_of_antitone
    (fun F : Finset Nat.Primes => F.inf (rowKer s.1)) hanti x
  rw [starProjection_congr hinf x] at h
  exact h

/-- Despite strong convergence, every finite packet stays norm distance exactly one from the
full ground projection. -/
theorem paperCoShiftFiniteProjection_norm_sub_ground
    (s : PaperCoShiftParameter) (F : Finset Nat.Primes) :
    ‖paperCoShiftFiniteProjection s F - paperCoShiftGroundProjection s.1‖ = 1 := by
  apply le_antisymm
  · apply (paperCoShiftFiniteProjection s F - paperCoShiftGroundProjection s.1).opNorm_le_bound
      (by norm_num)
    intro x
    have hfix : paperCoShiftFiniteProjection s F (paperCoShiftGroundProjection s.1 x) =
        paperCoShiftGroundProjection s.1 x :=
      Submodule.starProjection_eq_self_iff.mpr
        (ground_le_finite s.1 F ((eigenSubmodule s.1).starProjection_apply_mem x))
    calc
      ‖(paperCoShiftFiniteProjection s F - paperCoShiftGroundProjection s.1) x‖ =
          ‖paperCoShiftFiniteProjection s F (x - paperCoShiftGroundProjection s.1 x)‖ := by
            rw [map_sub, hfix, sub_apply]
      _ ≤ ‖x - paperCoShiftGroundProjection s.1 x‖ :=
        (F.inf (rowKer s.1)).norm_starProjection_apply_le _
      _ = ‖(eigenSubmodule s.1)ᗮ.starProjection x‖ := by
        rw [Submodule.starProjection_orthogonal_val]
        rfl
      _ ≤ 1 * ‖x‖ := by
        simpa only [one_mul] using (eigenSubmodule s.1)ᗮ.norm_starProjection_apply_le x
  · have h := paperPrimeCoShiftAlgebra_norm_le_sub_compact
      ⟨_, paperCoShiftFiniteProjection_mem_algebra s F⟩
      ⟨_, paperCoShiftGroundProjection_compact s.1⟩
    simpa only [paperCoShiftFiniteProjection_norm] using h

/-- Even after any further compact correction, the finite-to-cofinal error retains size one. -/
theorem paperCoShiftFiniteProjection_error_compactIdealDistance
    (s : PaperCoShiftParameter) (F : Finset Nat.Primes) :
    compactIdealDistance (paperCoShiftFiniteProjection s F - paperCoShiftGroundProjection s.1) =
      1 := by
  apply le_antisymm
  · simpa only [sub_zero, paperCoShiftFiniteProjection_norm_sub_ground] using
      compactIdealDistance_le
        (paperCoShiftFiniteProjection s F - paperCoShiftGroundProjection s.1) 0 isCompactOperator_zero
  · apply le_compactIdealDistance
    intro K hK
    have h := paperPrimeCoShiftAlgebra_norm_le_sub_compact
      ⟨_, paperCoShiftFiniteProjection_mem_algebra s F⟩
      ⟨paperCoShiftGroundProjection s.1 + K, (paperCoShiftGroundProjection_compact s.1).add hK⟩
    simpa only [paperCoShiftFiniteProjection_norm, sub_add_eq_sub_sub] using h

theorem paperCoShiftFiniteProjection_error_traceCost
    (s : PaperCoShiftParameter) (F : Finset Nat.Primes) :
    compactOperatorTraceCost H
      (paperCoShiftFiniteProjection s F - paperCoShiftGroundProjection s.1) = ∞ := by
  apply (compactOperatorTraceCost_eq_top_iff _).mpr
  intro h
  have hz := compactIdealDistance_eq_zero_of_isCompactOperator _ h
  rw [paperCoShiftFiniteProjection_error_compactIdealDistance] at hz
  exact one_ne_zero hz

/-- The strong cofinal limit cannot be promoted to operator-norm convergence. -/
theorem paperCoShiftFiniteProjection_not_norm_tendsto (s : PaperCoShiftParameter) :
    ¬ Tendsto (fun F : Finset Nat.Primes => paperCoShiftFiniteProjection s F)
      atTop (𝓝 (paperCoShiftGroundProjection s.1)) := by
  intro h
  have hn := (h.sub (tendsto_const_nhds (x := paperCoShiftGroundProjection s.1))).norm
  simp only [paperCoShiftFiniteProjection_norm_sub_ground, sub_self, norm_zero] at hn
  have he : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hn
  exact one_ne_zero he

end

end RHTower.PrimeCoShift
