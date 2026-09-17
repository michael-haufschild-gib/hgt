/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael and the HGT contributors
-/
import GaloisForLFunctions.RHTower.GammaValuationSchurLabelledProfile
import GaloisForLFunctions.RHTower.DeningerBigWittPrimeSeamDirichletTransport

/-!
# Big-Witt prime-seam obstruction for the labelled Gamma valuation profile

The source-defined reciprocal-prime Big-Witt seam energy has only constant
prime potentials in its bounded radical.  On a summable ordered prime profile,
that constant potential must be zero.  Thus this finite seam boundary cannot
be the nonzero coefficient-faithful transport required by route P.
-/

namespace RHTower

noncomputable section

/-- The `e`th ordered prime profile, reindexed by marked primes. -/
def gammaValuationAdjacentPrimitivePrimeProfile
    (a : DeningerHeightKothe) (e : ℕ) (p : Nat.Primes) : ℂ :=
  gammaValuationAdjacentPrimitiveProfile a (e, nthPrimeEquiv.symm p)

/-- A fixed ordered-prime depth slice of the labelled profile remains summable
when enumerated by marked primes. -/
theorem gammaValuationAdjacentPrimitivePrimeProfile_summable
    (a : DeningerHeightKothe) (e : ℕ) :
    Summable (fun n : ℕ =>
      gammaValuationAdjacentPrimitivePrimeProfile a e (nthPrimeEquiv n)) := by
  have hinj : Function.Injective (fun n : ℕ => (e, n)) := by
    intro n m hnm
    exact congrArg Prod.snd hnm
  have h := (summable_gammaValuationAdjacentPrimitiveProfile a).comp_injective hinj
  refine h.congr ?_
  intro n
  change gammaValuationAdjacentPrimitiveProfile a (e, n) =
    gammaValuationAdjacentPrimitiveProfile a (e,
      nthPrimeEquiv.symm (nthPrimeEquiv n))
  rw [nthPrimeEquiv.symm_apply_apply]

/-- At a fixed depth, bounded canonical Big-Witt prime-seam energy is
equivalent to literal prime-power source vanishing. -/
theorem gammaValuationAdjacentPrimitivePrimeProfile_seam_bounded_iff_axis_zero
    (a : DeningerHeightKothe) (e : ℕ) :
    DeningerBigWittPrimeSeamSourceEnergyBounded
        (gammaValuationAdjacentPrimitivePrimeProfile a e) ↔
      ∀ n : ℕ, gammaValuationNthPrimeCoord e a n = 0 := by
  constructor
  · intro hbound
    obtain ⟨c, hc⟩ :=
      deningerBigWittPrimeSeamSourceEnergyBounded_iff_constant _ |>.mp hbound
    have hsum := gammaValuationAdjacentPrimitivePrimeProfile_summable a e
    have hzero := hsum.tendsto_atTop_zero
    have hconst : (fun n : ℕ =>
        gammaValuationAdjacentPrimitivePrimeProfile a e (nthPrimeEquiv n)) =
        fun _ : ℕ => c := by
      funext n
      simpa using hc (nthPrimeEquiv n)
    rw [hconst] at hzero
    have hc0 : c = 0 := by
      exact tendsto_nhds_unique tendsto_const_nhds hzero
    have hprofile_zero : ∀ n : ℕ,
        gammaValuationAdjacentPrimitiveProfile a (e, n) = 0 := by
      intro n
      rw [show gammaValuationAdjacentPrimitiveProfile a (e, n) =
        gammaValuationAdjacentPrimitivePrimeProfile a e (nthPrimeEquiv n) by
          change gammaValuationAdjacentPrimitiveProfile a (e, n) =
            gammaValuationAdjacentPrimitiveProfile a (e,
              nthPrimeEquiv.symm (nthPrimeEquiv n))
          rw [nthPrimeEquiv.symm_apply_apply]]
      rw [hc (nthPrimeEquiv n), hc0]
    have hstep : ∀ n : ℕ, gammaValuationNthPrimeCoord e a n =
        gammaValuationNthPrimeCoord e a (n + 1) := by
      intro n
      have hprofile : gammaValuationAdjacentPrimitiveProfile a (e, n) = 0 := by
        exact hprofile_zero n
      have hterm : gammaValuationAdjacentPrimitiveTerm e a n = 0 := by
        simpa [gammaValuationAdjacentPrimitiveProfile] using hprofile
      have hfactor : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero n
      exact sub_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left hfactor)
    let d : ℕ → ℂ := fun n => gammaValuationNthPrimeCoord e a n
    have hweight := summable_gammaValuationNthPrimeCoord_indexWeight e a
    have hcoord : Summable d := by
      refine Summable.of_norm_bounded hweight ?_
      intro n
      change ‖gammaValuationNthPrimeCoord e a n‖ ≤
        (n + 1 : ℝ) * ‖gammaValuationNthPrimeCoord e a n‖
      exact le_mul_of_one_le_left (norm_nonneg _)
        (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
    have htail := hcoord.tendsto_atTop_zero
    have hdconst : d = fun _ : ℕ => d 0 := by
      funext n
      induction n with
      | zero => rfl
      | succ n ih =>
          exact (show d n = d (n + 1) by exact hstep n).symm.trans ih
    rw [hdconst] at htail
    have hd0 : d 0 = 0 := by
      exact tendsto_nhds_unique tendsto_const_nhds htail
    intro n
    change d n = 0
    rw [hdconst]
    exact hd0
  · intro hzero
    apply (deningerBigWittPrimeSeamSourceEnergyBounded_iff_constant _).mpr
    refine ⟨0, ?_⟩
    intro p
    simp only [gammaValuationAdjacentPrimitivePrimeProfile,
      gammaValuationAdjacentPrimitiveProfile,
      gammaValuationAdjacentPrimitiveTerm, hzero, sub_self, mul_zero]

/-- Requiring the canonical Big-Witt seam-energy bound at every retained depth
annihilates the entire ordered primitive profile. -/
theorem gammaValuationAdjacentPrimitivePrimeProfile_allDepth_seam_bounded_iff_zero
    (a : DeningerHeightKothe) :
    (∀ e : ℕ, DeningerBigWittPrimeSeamSourceEnergyBounded
      (gammaValuationAdjacentPrimitivePrimeProfile a e)) ↔
      ∀ en : ℕ × ℕ, gammaValuationAdjacentPrimitiveProfile a en = 0 := by
  constructor
  · intro hbound
    apply (gammaValuationAdjacentPrimitiveProfile_eq_zero_iff_axis_zero a).mpr
    intro e n
    exact (gammaValuationAdjacentPrimitivePrimeProfile_seam_bounded_iff_axis_zero a e).mp
      (hbound e) n
  · intro hzero e
    apply (gammaValuationAdjacentPrimitivePrimeProfile_seam_bounded_iff_axis_zero a e).mpr
    have haxis := (gammaValuationAdjacentPrimitiveProfile_eq_zero_iff_axis_zero a).mp hzero
    exact haxis e

end

end RHTower
