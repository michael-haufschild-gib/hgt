import GaloisForLFunctions.HTGeometry.PaperCayleyRationalReconstruction
import GaloisForLFunctions.RHTower.ConnesConsaniOnePrimeSourceDefect

/-! # Rational reconstruction throughout the native scattering operator algebra

One null set serves every prime, every finite operator word, every member of a
countable input family, and every finite complex mixture of outputs. The literal
one-prime scattering product is also reconstructed with its actual symbol.
-/

namespace RHTower
noncomputable section
open MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry
open scoped BigOperators

/-- Native Hardy projections, scattering multipliers, and both source defects. -/
def paperScatteringRationalOperator (p : Nat.Primes × Fin 8) : SoninL2 →L[ℂ] SoninL2 :=
  ![ccmHardyProjection, 1 - ccmHardyProjection, ccmArchimedeanScatteringL2Multiplier,
    connesConsaniPrimeScatteringMultiplier p.1, connesConsaniOnePrimeScatteringMultiplier p.1,
    connesConsaniPrimeSourceDefect p.1, connesConsaniOnePrimeSourceDefect p.1,
    ContinuousLinearMap.adjoint (connesConsaniOnePrimeSourceDefect p.1)] p.2

/-- Every finite ordered word in the actual source operators. -/
def paperScatteringRationalWord : List (Nat.Primes × Fin 8) → SoninL2 →L[ℂ] SoninL2
  | [] => 1
  | p :: w => paperScatteringRationalOperator p * paperScatteringRationalWord w

/-- Rational cutoffs reconstruct the whole countably generated source orbit and all its mixtures. -/
theorem paperScatteringRationalOrbit_common_span_reconstruction
    {κ : Type*} [Countable κ] (f : κ → SoninL2) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ t ∉ E, ∀ (S : Finset (List (Nat.Primes × Fin 8) × κ))
        (c : List (Nat.Primes × Fin 8) × κ → ℂ),
        Tendsto (fun N => ∑ j ∈ S, c j * paperCayleyRationalPartialSum
          (paperScatteringRationalWord j.1 (f j.2)) N t)
          atTop (𝓝 (∑ j ∈ S, c j * (paperScatteringRationalWord j.1 (f j.2)) t)) :=
  paperCayleyRational_common_span_reconstruction
    (fun j : List (Nat.Primes × Fin 8) × κ => paperScatteringRationalWord j.1 (f j.2))

/-- The recovered one-prime output is exactly multiplication by the native scattering symbol. -/
theorem paperScatteringRational_literal_common_reconstruction
    {κ : Type*} [Countable κ] (f : κ → SoninL2) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ t ∉ E, ∀ (p : Nat.Primes) j,
        Tendsto (fun N => paperCayleyRationalPartialSum
          (connesConsaniOnePrimeScatteringMultiplier p (f j)) N t)
          atTop (𝓝 (connesConsaniOnePrimeScatteringSymbol p t * f j t)) := by
  have ha : ∀ᵐ t ∂volume, ∀ j : Nat.Primes × κ,
      connesConsaniOnePrimeScatteringMultiplier j.1 (f j.2) t =
        connesConsaniOnePrimeScatteringSymbol j.1 t * f j.2 t :=
    ae_all_iff.mpr (fun j => connesConsaniOnePrimeScatteringMultiplier_ae j.1 (f j.2))
  obtain ⟨D, hsub, hDm, hDz⟩ := exists_measurable_superset_of_null (ae_iff.mp ha)
  obtain ⟨E, hEm, hEz, hc⟩ := paperCayleyRational_common_reconstruction
    (fun j : Nat.Primes × κ => connesConsaniOnePrimeScatteringMultiplier j.1 (f j.2))
  refine ⟨E ∪ D, hEm.union hDm, measure_union_null hEz hDz, ?_⟩
  intro t ht p j
  have hpoint : ∀ j : Nat.Primes × κ,
      connesConsaniOnePrimeScatteringMultiplier j.1 (f j.2) t =
        connesConsaniOnePrimeScatteringSymbol j.1 t * f j.2 t := by
    by_contra h
    exact ht (Or.inr (hsub h))
  simpa only [hpoint (p, j)] using hc t (fun h => ht (Or.inl h)) (p, j)

end
end RHTower
