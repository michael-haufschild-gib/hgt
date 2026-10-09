import GaloisForLFunctions.RHTower.WeilLogShiftFactorialAmplitudeSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Closed and null factorial-regular finite error sets

The affine classification becomes a closed exceptional set in finite-dimensional
amplitude spaces. One native late impulse direction makes it Haar-null and
nowhere dense. In a finite list of impulse columns no independence is required.
-/

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

namespace RHTower

/-- Existential factorial regularity at any shift is closed on every
finite-dimensional affine family, despite its unbounded majorant parameters. -/
theorem isClosed_weilLogShiftFactorialAmplitudeSpace {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (center : ℕ →ᵇ ℝ) (T : E →ₗ[ℝ] (ℕ →ᵇ ℝ)) :
    IsClosed (weilLogShiftFactorialAmplitudeSpace center T : Set E) :=
  (weilLogShiftFactorialAmplitudeSpace center T).closed_of_finiteDimensional

/-- A common late-column threshold makes the full regular-amplitude affine
subspace null for every Haar measure and nowhere dense in every finite dimension. -/
theorem exists_weilLogShiftFactorialAmplitudeSpace_null_nowhereDense :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
      (center : ℕ →ᵇ ℝ) (T : E →ₗ[ℝ] (ℕ →ᵇ ℝ)) (k : ℕ), K ≤ k →
      (∃ v : E, T v = weilLogShiftRecoveryUnitHistory k) →
      ∀ (μ : Measure E) [μ.IsAddHaarMeasure],
        μ (weilLogShiftFactorialAmplitudeSpace center T : Set E) = 0 ∧
        IsNowhereDense (weilLogShiftFactorialAmplitudeSpace center T : Set E) := by
  obtain ⟨K, hK, hproper⟩ := exists_weilLogShiftFactorialAmplitudeSpace_ne_top
  refine ⟨K, hK, ?_⟩
  intro E _ _ _ _ _ center T k hk hdir μ _
  have hnull := Measure.addHaar_affineSubspace μ
    (weilLogShiftFactorialAmplitudeSpace center T) (hproper E center T k hk hdir)
  exact ⟨hnull, IsNowhereDense.of_isClosed_null
    (isClosed_weilLogShiftFactorialAmplitudeSpace center T) hnull⟩

/-- A finite list of impulse indices defines a linear history-error map.
Repeated indices are allowed. -/
def weilLogShiftFiniteImpulseMap {d : ℕ} (indices : Fin d → ℕ) :
    (Fin d → ℝ) →ₗ[ℝ] (ℕ →ᵇ ℝ) where
  toFun a := ∑ i, a i • weilLogShiftRecoveryUnitHistory (indices i)
  map_add' a b := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_eq_mul, smul_smul, RingHom.id_apply, Finset.smul_sum]

/-- Each coordinate amplitude exposes its unit impulse, with no distinctness
assumption on the list of indices. -/
theorem weilLogShiftFiniteImpulseMap_single {d : ℕ} (indices : Fin d → ℕ) (i : Fin d) :
    weilLogShiftFiniteImpulseMap indices (Pi.single i 1) =
      weilLogShiftRecoveryUnitHistory (indices i) := by
  change (∑ j, (Pi.single i (1 : ℝ) : Fin d → ℝ) j •
    weilLogShiftRecoveryUnitHistory (indices j)) = _
  simp [Pi.single_apply]

/-- For every finite error list containing one sufficiently late column, the
amplitudes admitting any factorial-majorant shift form a closed, Lebesgue-null,
nowhere-dense set. The threshold is uniform in dimension, center, and index list. -/
theorem exists_weilLogShiftFiniteImpulse_exception_closed_null_nowhereDense :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ (d : ℕ) (indices : Fin d → ℕ) (center : ℕ →ᵇ ℝ),
      (∃ i : Fin d, K ≤ indices i) →
      let S : Set (Fin d → ℝ) := {a | ∃ y : ℝ, WeilLogShiftHasFactorialMajorant
        (weilLogShiftRecoveryMoment y
          (center + ∑ i, a i • weilLogShiftRecoveryUnitHistory (indices i)))}
      IsClosed S ∧ volume S = 0 ∧ IsNowhereDense S := by
  obtain ⟨K, hK, hnull⟩ := exists_weilLogShiftFactorialAmplitudeSpace_null_nowhereDense
  refine ⟨K, hK, ?_⟩
  intro d indices center hi
  obtain ⟨i, hi⟩ := hi
  let T := weilLogShiftFiniteImpulseMap indices
  have hdir : ∃ v : Fin d → ℝ, T v = weilLogShiftRecoveryUnitHistory (indices i) :=
    ⟨Pi.single i 1, weilLogShiftFiniteImpulseMap_single indices i⟩
  have hpair := hnull (Fin d → ℝ) center T (indices i) hi hdir volume
  have hset : {a : Fin d → ℝ | ∃ y : ℝ, WeilLogShiftHasFactorialMajorant
        (weilLogShiftRecoveryMoment y
          (center + ∑ j, a j • weilLogShiftRecoveryUnitHistory (indices j)))} =
      (weilLogShiftFactorialAmplitudeSpace center T : Set (Fin d → ℝ)) := by
    ext a
    exact (mem_weilLogShiftFactorialAmplitudeSpace center T a).symm
  dsimp only
  rw [hset]
  exact ⟨isClosed_weilLogShiftFactorialAmplitudeSpace center T, hpair⟩

end RHTower
