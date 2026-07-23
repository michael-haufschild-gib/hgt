import GaloisForLFunctions.HTGeometry.RankOneDuality
import GaloisForLFunctions.HTGeometry.PowerSumTorelli
import GaloisForLFunctions.RHTower.LocalFactorDuality
import GaloisForLFunctions.RHTower.SatakeReality
import Mathlib.Analysis.Complex.Circle

/-!
# Unitary rank-one duality, Satake reality, and finite Torelli

Rank-one duality is inversion, whereas Satake reality is conjugation closure.  On the unit circle
these involutions coincide.  Consequently a finite unitary rank-one spectrum is dual-closed
exactly when its first cardinality-many secular moments are real.  In that phase every moment is
real and the local Euler factor is invariant under dualization.
-/

open scoped BigOperators
open Finset

namespace GaloisForLFunctions

noncomputable section

/-- A finite spectrum of unitary rank-one multipliers, viewed in `ℂ`. -/
def unitaryRankOneSpectrum {n : ℕ} (f : Fin n → Circle) : Multiset ℂ :=
  univ.val.map fun i => (f i : ℂ)

/-- The same spectrum after applying the abstract rank-one dual multiplier. -/
def unitaryRankOneDualSpectrum {n : ℕ} (f : Fin n → Circle) : Multiset ℂ :=
  univ.val.map fun i => ((rankOneDualMultiplier (f i) : Circle) : ℂ)

/-- On a unitary complex multiplier, abstract rank-one duality is complex conjugation. -/
theorem coe_rankOneDualMultiplier_circle (z : Circle) :
    ((rankOneDualMultiplier z : Circle) : ℂ) =
      (starRingEnd ℂ) (z : ℂ) := by
  simpa [rankOneDualMultiplier] using Circle.coe_inv_eq_conj z

/-- The dualized unitary spectrum is exactly the conjugate spectrum. -/
theorem unitaryRankOneDualSpectrum_eq_conjugate {n : ℕ} (f : Fin n → Circle) :
    unitaryRankOneDualSpectrum f =
      (unitaryRankOneSpectrum f).map (starRingEnd ℂ) := by
  rw [unitaryRankOneDualSpectrum, unitaryRankOneSpectrum, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro i _
  exact coe_rankOneDualMultiplier_circle (f i)

/-- The dualized unitary spectrum is also the pointwise inverse complex spectrum. -/
theorem unitaryRankOneDualSpectrum_eq_inverse {n : ℕ} (f : Fin n → Circle) :
    unitaryRankOneDualSpectrum f =
      (unitaryRankOneSpectrum f).map fun z => z⁻¹ := by
  rw [unitaryRankOneDualSpectrum, unitaryRankOneSpectrum, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro i _
  simp [rankOneDualMultiplier, Function.comp_apply]

/-- **Unitary duality--Torelli law.**  A finite unitary rank-one spectrum is closed under its
abstract dual exactly when its first cardinality-many secular moments are real. -/
theorem unitaryRankOneDualSpectrum_closed_iff_firstMoments_real
    {n : ℕ} (f : Fin n → Circle) :
    unitaryRankOneDualSpectrum f = unitaryRankOneSpectrum f ↔
      ∀ k ≤ n,
        (starRingEnd ℂ) ((univ.val.map (fun i => (f i : ℂ) ^ k)).sum) =
          (univ.val.map (fun i => (f i : ℂ) ^ k)).sum := by
  rw [unitaryRankOneDualSpectrum_eq_conjugate]
  constructor
  · intro hclosed k _
    simpa only [unitaryRankOneSpectrum, Multiset.map_map, Function.comp_apply] using
      selfDual_moment_real (unitaryRankOneSpectrum f) hclosed k
  · intro hmoment
    let g : Fin n → ℂ := fun i => (starRingEnd ℂ) (f i : ℂ)
    have hconjPower (k : ℕ) :
        (univ.val.map (fun i => g i ^ k)).sum =
          (starRingEnd ℂ) ((univ.val.map (fun i => (f i : ℂ) ^ k)).sum) := by
      rw [map_multiset_sum, Multiset.map_map]
      apply congrArg Multiset.sum
      apply Multiset.map_congr rfl
      intro i _
      simp only [g, Function.comp_apply, map_pow]
    have hp : ∀ k, k ≤ n →
        (univ.val.map (fun i => (f i : ℂ) ^ k)).sum =
          (univ.val.map (fun i => g i ^ k)).sum := by
      intro k hk
      exact (hmoment k hk).symm.trans (hconjPower k).symm
    have hfg : univ.val.map (fun i => (f i : ℂ)) = univ.val.map g :=
      powerSum_torelli_finite (fun i => (f i : ℂ)) g hp
    rw [unitaryRankOneSpectrum, Multiset.map_map]
    simpa only [g, Function.comp_apply] using hfg.symm

/-- Dual closure of a unitary rank-one spectrum gives the local Euler-factor functional equation. -/
theorem unitaryRankOneDualSpectrum_localFactor_eq
    {n : ℕ} (f : Fin n → Circle)
    (hdual : unitaryRankOneDualSpectrum f = unitaryRankOneSpectrum f)
    (x : ℂ) :
    ((unitaryRankOneSpectrum f).map (fun a => 1 - a * x)).prod =
      ((unitaryRankOneSpectrum f).map (fun a => 1 - a⁻¹ * x)).prod := by
  apply selfDual_localFactor_eq
  rw [← unitaryRankOneDualSpectrum_eq_inverse]
  exact hdual

/-- In the unitary rank-one phase, dual closure simultaneously forces reality of every secular
moment and dual invariance of every local Euler factor. -/
theorem unitaryRankOneDualSpectrum_allMoments_real_and_localFactor_eq
    {n : ℕ} (f : Fin n → Circle)
    (hdual : unitaryRankOneDualSpectrum f = unitaryRankOneSpectrum f) :
    (∀ m : ℕ,
        (starRingEnd ℂ) ((univ.val.map (fun i => (f i : ℂ) ^ m)).sum) =
          (univ.val.map (fun i => (f i : ℂ) ^ m)).sum) ∧
      (∀ x : ℂ,
        ((unitaryRankOneSpectrum f).map (fun a => 1 - a * x)).prod =
          ((unitaryRankOneSpectrum f).map (fun a => 1 - a⁻¹ * x)).prod) := by
  have hconj : (unitaryRankOneSpectrum f).map (starRingEnd ℂ) =
      unitaryRankOneSpectrum f := by
    rw [← unitaryRankOneDualSpectrum_eq_conjugate, hdual]
  constructor
  · intro m
    simpa only [unitaryRankOneSpectrum, Multiset.map_map, Function.comp_apply] using
      selfDual_moment_real (unitaryRankOneSpectrum f) hconj m
  · exact unitaryRankOneDualSpectrum_localFactor_eq f hdual

end

end GaloisForLFunctions
