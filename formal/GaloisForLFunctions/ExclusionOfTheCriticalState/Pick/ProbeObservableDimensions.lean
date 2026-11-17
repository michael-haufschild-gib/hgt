import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeHullRanks
import GaloisForLFunctions.RepresentationLifting.Actions.EndomorphismCharacter

/-!
# Exact observable dimensions in the finite reflection hull

Conjugation by the actual zero reflection splits hull endomorphisms into
commuting and cross-sector parts. Their dimensions are respectively
`r₊²+r₋²` and `2r₊r₋`, where the two ranks come from the sector probe Grams.
Thus the Gram data measures exactly how many intrinsic operator directions
reflection dephasing removes.

This applies Aoki's invariant-trace averaging mechanism
(arXiv:2611.20592, Lemma 3) to the endomorphism representation.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open RepresentationLifting.OperatorCharacter
variable {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x})

/-- Reflection acts by conjugation on all observables of the finite probe hull. -/
def hullConjugation : Module.End ℂ (Module.End ℂ (reflectionHull p)) :=
  sandwich (hullReflection p) (hullReflection p)

/-- Intrinsic reflection dephasing on the finite probe hull. -/
def hullEvenObservable : Module.End ℂ (Module.End ℂ (reflectionHull p)) :=
  (1 / 2 : ℂ) • (1 + hullConjugation p)

/-- Cross-sector component removed by finite-hull reflection dephasing. -/
def hullOddObservable : Module.End ℂ (Module.End ℂ (reflectionHull p)) :=
  (1 / 2 : ℂ) • (1 - hullConjugation p)

theorem hullConjugation_sq : hullConjugation p * hullConjugation p = 1 := by
  apply LinearMap.ext
  intro A
  change hullReflection p * (hullReflection p * A * hullReflection p) * hullReflection p = A
  calc
    _ = (hullReflection p * hullReflection p) * A * (hullReflection p * hullReflection p) := by
      simp only [mul_assoc]
    _ = A := by rw [hullReflection_sq, one_mul, mul_one]

theorem hullEvenObservable_idempotent : IsIdempotentElem (hullEvenObservable p) := by
  change hullEvenObservable p * hullEvenObservable p = hullEvenObservable p
  unfold hullEvenObservable
  simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, one_mul, mul_one,
    hullConjugation_sq]
  module

theorem hullOddObservable_idempotent : IsIdempotentElem (hullOddObservable p) := by
  change hullOddObservable p * hullOddObservable p = hullOddObservable p
  apply LinearMap.ext
  intro A
  have hC : hullConjugation p (hullConjugation p A) = A :=
    LinearMap.congr_fun (hullConjugation_sq p) A
  change (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (A - hullConjugation p A) -
    hullConjugation p ((1 / 2 : ℂ) • (A - hullConjugation p A))) =
      (1 / 2 : ℂ) • (A - hullConjugation p A)
  rw [map_smul, map_sub, hC]
  module

theorem hullEvenObservable_add_odd : hullEvenObservable p + hullOddObservable p = 1 := by
  unfold hullEvenObservable hullOddObservable
  module

private theorem hullEvenObservable_mul_odd : hullEvenObservable p * hullOddObservable p = 0 := by
  apply LinearMap.ext
  intro A
  have hC : hullConjugation p (hullConjugation p A) = A :=
    LinearMap.congr_fun (hullConjugation_sq p) A
  change (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (A - hullConjugation p A) +
    hullConjugation p ((1 / 2 : ℂ) • (A - hullConjugation p A))) = 0
  rw [map_smul, map_sub, hC]
  module

/-- The cross-sector component is exactly the kernel of dephasing. -/
theorem hullEvenObservable_ker :
    LinearMap.ker (hullEvenObservable p) = LinearMap.range (hullOddObservable p) := by
  ext A
  constructor
  · intro hA
    refine ⟨A, ?_⟩
    have h := LinearMap.congr_fun (hullEvenObservable_add_odd p) A
    change hullEvenObservable p A + hullOddObservable p A = A at h
    rw [show hullEvenObservable p A = 0 from hA, zero_add] at h
    exact h
  · rintro ⟨B, rfl⟩
    exact LinearMap.congr_fun (hullEvenObservable_mul_odd p) B

/-- The conjugation character is the square of the signed probe-rank difference. -/
theorem hullConjugation_trace :
    LinearMap.trace ℂ (Module.End ℂ (reflectionHull p)) (hullConjugation p) =
      (((positiveProbeGram p).rank : ℂ) - ((negativeProbeGram p).rank : ℂ)) ^ 2 := by
  rw [hullConjugation, trace_sandwich, hullReflection_trace_eq_sector_ranks, pow_two]

/-- Dephasing retains exactly the two diagonal sector blocks. -/
theorem hullEvenObservable_finrank :
    Module.finrank ℂ (LinearMap.range (hullEvenObservable p)) =
      (positiveProbeGram p).rank ^ 2 + (negativeProbeGram p).rank ^ 2 := by
  letI : Module.Free ℂ (LinearMap.range (hullEvenObservable p)) :=
    Module.Free.of_divisionRing ℂ (LinearMap.range (hullEvenObservable p))
  letI : Module.Free ℂ (LinearMap.ker (hullEvenObservable p)) :=
    Module.Free.of_divisionRing ℂ (LinearMap.ker (hullEvenObservable p))
  have ht : LinearMap.trace ℂ (Module.End ℂ (reflectionHull p)) (hullEvenObservable p) =
      (Module.finrank ℂ (LinearMap.range (hullEvenObservable p)) : ℂ) :=
    LinearMap.IsProj.trace (R := ℂ) (M := Module.End ℂ (reflectionHull p))
      (LinearMap.IsIdempotentElem.isProj_range _ (hullEvenObservable_idempotent p))
  have he : (Module.finrank ℂ (LinearMap.range (hullEvenObservable p)) : ℂ) =
      (((positiveProbeGram p).rank : ℂ) ^ 2 + ((negativeProbeGram p).rank : ℂ) ^ 2) := by
    rw [← ht]
    simp only [hullEvenObservable, map_smul, map_add, LinearMap.trace_one, smul_eq_mul,
      Module.finrank_linearMap, reflectionHull_finrank_eq_sector_ranks, Nat.cast_mul,
      Nat.cast_add, hullConjugation_trace]
    ring
  exact_mod_cast he

/-- Reflection dephasing removes both off-diagonal blocks, with no further loss. -/
theorem hullOddObservable_finrank :
    Module.finrank ℂ (LinearMap.range (hullOddObservable p)) =
      2 * (positiveProbeGram p).rank * (negativeProbeGram p).rank := by
  letI : Module.Free ℂ (LinearMap.range (hullOddObservable p)) :=
    Module.Free.of_divisionRing ℂ (LinearMap.range (hullOddObservable p))
  letI : Module.Free ℂ (LinearMap.ker (hullOddObservable p)) :=
    Module.Free.of_divisionRing ℂ (LinearMap.ker (hullOddObservable p))
  have ht : LinearMap.trace ℂ (Module.End ℂ (reflectionHull p)) (hullOddObservable p) =
      (Module.finrank ℂ (LinearMap.range (hullOddObservable p)) : ℂ) :=
    LinearMap.IsProj.trace (R := ℂ) (M := Module.End ℂ (reflectionHull p))
      (LinearMap.IsIdempotentElem.isProj_range _ (hullOddObservable_idempotent p))
  have he : (Module.finrank ℂ (LinearMap.range (hullOddObservable p)) : ℂ) =
      2 * ((positiveProbeGram p).rank : ℂ) * ((negativeProbeGram p).rank : ℂ) := by
    rw [← ht]
    rw [hullOddObservable, map_smul,
      map_sub (LinearMap.trace ℂ (Module.End ℂ (reflectionHull p)))
        (1 : Module.End ℂ (Module.End ℂ (reflectionHull p))) (hullConjugation p)]
    simp only [LinearMap.trace_one, smul_eq_mul,
      Module.finrank_linearMap, reflectionHull_finrank_eq_sector_ranks, Nat.cast_mul,
      Nat.cast_add, hullConjugation_trace]
    ring
  exact_mod_cast he

/-- Exact number of operator directions erased by reflection dephasing. -/
theorem hullEvenObservable_nullity :
    Module.finrank ℂ (LinearMap.ker (hullEvenObservable p)) =
      2 * (positiveProbeGram p).rank * (negativeProbeGram p).rank := by
  rw [hullEvenObservable_ker, hullOddObservable_finrank]

/-- The retained observables are exactly the reflection commutant inside the hull. -/
theorem mem_range_hullEvenObservable_iff (A : Module.End ℂ (reflectionHull p)) :
    A ∈ LinearMap.range (hullEvenObservable p) ↔ hullReflection p * A = A * hullReflection p := by
  have hsq (B : Module.End ℂ (reflectionHull p)) :
      hullConjugation p (hullConjugation p B) = B :=
    LinearMap.congr_fun (hullConjugation_sq p) B
  constructor
  · rintro ⟨B, rfl⟩
    have hfix : hullConjugation p (hullEvenObservable p B) = hullEvenObservable p B := by
      change hullConjugation p ((1 / 2 : ℂ) • (B + hullConjugation p B)) =
        (1 / 2 : ℂ) • (B + hullConjugation p B)
      rw [map_smul, map_add, hsq]
      module
    have h := congrArg (fun C => C * hullReflection p) hfix
    change (hullReflection p * hullEvenObservable p B * hullReflection p) * hullReflection p = _ at h
    simpa only [mul_assoc, hullReflection_sq, mul_one] using h
  · intro h
    refine ⟨A, ?_⟩
    change (1 / 2 : ℂ) • (A + hullReflection p * A * hullReflection p) = A
    rw [h, mul_assoc, hullReflection_sq, mul_one]
    module

#print axioms hullEvenObservable_nullity
#print axioms hullEvenObservable_finrank
#print axioms hullOddObservable_finrank
#print axioms mem_range_hullEvenObservable_iff
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
