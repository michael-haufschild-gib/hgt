import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesKotheBoundary
import GaloisForLFunctions.RHTower.DeningerPrimeLogHeightMellin

/-!
# Phase-sensitive Mellin response of the Gamma-sewn Stokes connection

The critical Stokes connection from the preceding module is extended through the closed Euler
chamber by its source-projective boundary value.  Every centered Mellin jet observes this crossing
continuously.  Hence the actual height phase survives the aperture limit before norm, Gram,
determinant, or reflection folding.

This supplies the phase-sensitive response object demanded by the P-G59 no-go.  It does not claim
that any chosen source vector already gives the continued Xi trace or a passive response.
-/

open Complex Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Additivity of the full Kummer-lattice Stokes frequency. -/
theorem gammaSewnMobiusApertureStokesKotheFrequency_add
    (s : ℝ) (m n : DeningerPrimeLattice) :
    gammaSewnMobiusApertureStokesKotheFrequency s (m + n) =
      gammaSewnMobiusApertureStokesKotheFrequency s m +
        gammaSewnMobiusApertureStokesKotheFrequency s n := by
  refine Finsupp.sum_add_index' (by simp) ?_
  intro p z w
  push_cast
  ring

/-- Reflection reverses the signed Stokes frequency. -/
theorem gammaSewnMobiusApertureStokesKotheFrequency_neg
    (s : ℝ) (m : DeningerPrimeLattice) :
    gammaSewnMobiusApertureStokesKotheFrequency s (-m) =
      -gammaSewnMobiusApertureStokesKotheFrequency s m := by
  have h : gammaSewnMobiusApertureStokesKotheFrequency s (-m) +
      gammaSewnMobiusApertureStokesKotheFrequency s m = 0 := by
    rw [← gammaSewnMobiusApertureStokesKotheFrequency_add]
    simp
  linarith

/-- Globally defined closed-chamber source operator.  Outside `s ≥ 1` it is frozen at the critical
boundary; only its restriction to the closed chamber is used. -/
def gammaSewnMobiusApertureStokesKotheClosedOperator (s : ℝ) :
    DeningerHeightKothe →ₗ[ℂ] DeningerHeightKothe :=
  if hs : 1 ≤ s then gammaSewnMobiusApertureStokesKotheOperator s hs
  else gammaSewnMobiusApertureStokesKotheOperator 1 (by norm_num)

theorem gammaSewnMobiusApertureStokesKotheClosedOperator_eq
    {s : ℝ} (hs : 1 ≤ s) :
    gammaSewnMobiusApertureStokesKotheClosedOperator s =
      gammaSewnMobiusApertureStokesKotheOperator s hs := by
  simp only [gammaSewnMobiusApertureStokesKotheClosedOperator, dif_pos hs]

@[simp] theorem gammaSewnMobiusApertureStokesKotheClosedOperator_one :
    gammaSewnMobiusApertureStokesKotheClosedOperator 1 =
      gammaSewnMobiusApertureStokesKotheOperator 1 (by norm_num) := by
  exact gammaSewnMobiusApertureStokesKotheClosedOperator_eq (by norm_num)

/-- The globally packaged operator converges strongly in every defining source seminorm. -/
theorem tendsto_deningerHeightSeminorm_gammaSewnMobiusApertureStokesKotheClosedOperator
    (k : ℕ) (a : DeningerHeightKothe) :
    Tendsto
      (fun s : ℝ => deningerHeightSeminorm k
        (gammaSewnMobiusApertureStokesKotheClosedOperator s a -
          gammaSewnMobiusApertureStokesKotheClosedOperator 1 a))
      (nhdsWithin (1 : ℝ) (Set.Ici 1)) (𝓝 0) := by
  apply tendsto_gammaSewnMobiusApertureStokesKotheBoundarySeminorm k a |>.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  simpa only [gammaSewnMobiusApertureStokesKotheClosedOperator_eq hs,
    gammaSewnMobiusApertureStokesKotheClosedOperator_one] using
      (deningerHeightSeminorm_gammaSewnMobiusApertureStokesKotheOperator_sub_one
        hs k a).symm

private theorem gammaSewnMobiusApertureStokesMellinTerm_summable
    (z : ℂ) (j k : ℕ) (hk : |(z - 1 / 2).re| + (j : ℝ) ≤ (k : ℝ))
    (a : DeningerHeightKothe) :
    Summable fun m : DeningerPrimeLattice =>
      deningerMellinSymbol z j m * (a : DeningerPrimeLattice → ℂ) m := by
  refine Summable.of_norm_bounded (a.2 k) fun m => ?_
  show ‖deningerMellinSymbol z j m * (a : DeningerPrimeLattice → ℂ) m‖ ≤
    deningerHeightKotheData.w k m * ‖(a : DeningerPrimeLattice → ℂ) m‖
  rw [deningerHeightKotheData_w, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (deningerMellinSymbol_norm_le z j k hk m) (norm_nonneg _)

/-- Linearity under subtraction for a Mellin jet, with an explicit source seminorm witnessing
absolute convergence. -/
theorem deningerMellinJet_sub_of_growth
    (z : ℂ) (j k : ℕ) (hk : |(z - 1 / 2).re| + (j : ℝ) ≤ (k : ℝ))
    (a b : DeningerHeightKothe) :
    deningerMellinJet z j (a - b) =
      deningerMellinJet z j a - deningerMellinJet z j b := by
  rw [deningerMellinJet, deningerMellinJet, deningerMellinJet]
  rw [← (gammaSewnMobiusApertureStokesMellinTerm_summable z j k hk a).tsum_sub
    (gammaSewnMobiusApertureStokesMellinTerm_summable z j k hk b)]
  refine tsum_congr fun m => ?_
  rw [Submodule.coe_sub, Pi.sub_apply]
  ring

/-- Phase-sensitive centered Mellin response of the closed Stokes connection. -/
def gammaSewnMobiusApertureStokesMellinResponse
    (s : ℝ) (z : ℂ) (j : ℕ) (a : DeningerHeightKothe) : ℂ :=
  deningerMellinJet z j
    (gammaSewnMobiusApertureStokesKotheClosedOperator s a)

/-- **Mellin response crossing.**  Every phase-sensitive centered Mellin jet has a path-independent
right boundary value at critical aperture on every nuclear source vector. -/
theorem tendsto_gammaSewnMobiusApertureStokesMellinResponse
    (z : ℂ) (j k : ℕ) (hk : |(z - 1 / 2).re| + (j : ℝ) ≤ (k : ℝ))
    (a : DeningerHeightKothe) :
    Tendsto
      (fun s : ℝ => gammaSewnMobiusApertureStokesMellinResponse s z j a)
      (nhdsWithin (1 : ℝ) (Set.Ici 1))
      (𝓝 (gammaSewnMobiusApertureStokesMellinResponse 1 z j a)) := by
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun s => norm_nonneg _) (fun s => ?_)
    (tendsto_deningerHeightSeminorm_gammaSewnMobiusApertureStokesKotheClosedOperator k a)
  ·
    rw [gammaSewnMobiusApertureStokesMellinResponse,
      gammaSewnMobiusApertureStokesMellinResponse,
      ← deningerMellinJet_sub_of_growth z j k hk]
    exact deningerMellinJet_norm_le z j k hk _

/-- The Stokes connection anticommutes with Kummer reflection before the phase is observed. -/
theorem gammaSewnMobiusApertureStokesKotheOperator_reflect
    {s : ℝ} (hs : 1 ≤ s) (a : DeningerHeightKothe) :
    gammaSewnMobiusApertureStokesKotheOperator s hs (deningerHeightReflect a) =
      -deningerHeightReflect
        (gammaSewnMobiusApertureStokesKotheOperator s hs a) := by
  ext m
  rw [gammaSewnMobiusApertureStokesKotheOperator_coe hs,
    deningerHeightReflect_coe, Submodule.coe_neg, Pi.neg_apply,
    deningerHeightReflect_coe,
    gammaSewnMobiusApertureStokesKotheOperator_coe hs,
    gammaSewnMobiusApertureStokesKotheFrequency_neg]
  push_cast
  ring

end RHTower
