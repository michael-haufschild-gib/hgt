/-
# The transversality tail obeys a power law

The tail is the sum of two shell masses: the near-degenerate part of the coefficient sphere and the
part where some character has a small tangential gradient.  The first has a power-law bound from
the discriminant; each of the finitely many characters has one from the criticality polynomial; and
the union over characters costs the sum of the individual bounds, not a product.  Adding the two
gives the tail bound.

Main results:
* `toSphere_exists_sublevel_le` — the union of finitely many sublevel sets.
* `exists_toSphere_transversalityTail_le` — **the tail power law**.
-/
import GaloisForLFunctions.HTGeometry.ShellCriticalityDomination
import GaloisForLFunctions.HTGeometry.SpectralDiscriminantPolynomial

open Set MeasureTheory Metric
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {m : ℕ}

/-- **The union of finitely many sublevel sets costs the sum of their bounds.** -/
theorem toSphere_exists_sublevel_le {K : Type*} [Fintype K]
    (h : K → sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 → ℝ) (B : K → ℝ≥0∞) (ε : ℝ)
    (hb : ∀ κ, volume.toSphere {ω | h κ ω ≤ ε} ≤ B κ) :
    volume.toSphere {ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 | ∃ κ, h κ ω ≤ ε}
      ≤ ∑ κ, B κ := by
  classical
  have hset : {ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 | ∃ κ, h κ ω ≤ ε}
      = ⋃ κ : K, {ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 | h κ ω ≤ ε} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  rw [hset]
  refine le_trans (measure_iUnion_le _) ?_
  rw [tsum_fintype]
  exact Finset.sum_le_sum fun κ _ => hb κ

/-- **The transversality tail power law.**  A discriminant with a power-law sublevel bound and a
finite family of observables each with its own power-law sublevel bound give the tail the sum of
those bounds. -/
theorem exists_toSphere_transversalityTail_le {K : Type*} [Fintype K]
    {Disc : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 → ℝ}
    {h : K → sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 → ℝ} {α₀ : ℝ} {α : K → ℝ}
    (hDisc : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ ε : ℝ, 0 ≤ ε →
      volume.toSphere {ω | Disc ω ≤ ε} ≤ C * ENNReal.ofReal (ε ^ α₀))
    (hh : ∀ κ, ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ ∀ ε : ℝ, 0 ≤ ε →
      volume.toSphere {ω | h κ ω ≤ ε} ≤ A * ENNReal.ofReal (ε ^ α κ)) :
    ∃ (C : ℝ≥0∞) (A : K → ℝ≥0∞), C ≠ ⊤ ∧ (∀ κ, A κ ≠ ⊤) ∧
      ∀ ζ g : ℝ, 0 ≤ ζ → 0 ≤ g →
        volume.toSphere {ω | Disc ω ≤ ζ}
            + volume.toSphere {ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 |
                ∃ κ, h κ ω ≤ g}
          ≤ C * ENNReal.ofReal (ζ ^ α₀) + ∑ κ, A κ * ENNReal.ofReal (g ^ α κ) := by
  classical
  obtain ⟨C, hCtop, hCb⟩ := hDisc
  choose A hAtop hAb using hh
  refine ⟨C, A, hCtop, hAtop, fun ζ g hζ hg => ?_⟩
  refine add_le_add (hCb ζ hζ) ?_
  exact toSphere_exists_sublevel_le h (fun κ => A κ * ENNReal.ofReal (g ^ α κ)) g
    fun κ => hAb κ g hg

end

end GaloisForLFunctions.HTGeometry
