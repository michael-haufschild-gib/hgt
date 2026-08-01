import GaloisForLFunctions.HTGeometry.AffineCouplingProtectedRelationLaw
import GaloisForLFunctions.HTGeometry.SeparableInfiniteProjectiveRecurrenceLaw

/-!
# Separable interaction recurrence along an entire coupling ray

For arbitrary countable product spectra, one arbitrarily weak separable
trace-class direction controls the complete affine coupling ray.  Only a
countable set of coupling strengths can carry an accidental projective
relation.  At every other strength the coupled relation set is the exact
intersection of the bare and interaction relation sets; the chosen direction
makes that intersection trivial.

Consequently every nonexceptional coupling has full projective future hull,
all finite temporal ranks, no nonzero exact global return, and syndetic
traversal of every positive summable recurrence probe's complete interval.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Set

/-- **Separable complete recurrence-ray law.** Every pair of countable
spectra admits one arbitrarily weak separable trace-class interaction
direction for which all but countably many coupling strengths have complete
projective recurrence. -/
theorem exists_arbitrarilyWeak_separable_completeProjectiveRecurrenceRayLaw
    {A B : Type*} [Countable A] [Countable B] [Infinite (A × B)]
    (left : A → ℝ) (right : B → ℝ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (u : A → ℝ) (v : B → ℝ),
      ∃ hw : Summable (fun x : A × B => |u x.1 * v x.2|),
        ∃ C : Set ℝ,
          Summable (fun i => |u i|) ∧
          Summable (fun j => |v j|) ∧
          (∀ x : A × B, |u x.1 * v x.2| < δ) ∧
          ‖realSummableDiagonalOperator
            (fun x : A × B => u x.1 * v x.2) hw‖ < δ ∧
          IsSelfAdjoint
            (realSummableDiagonalOperator
              (fun x : A × B => u x.1 * v x.2) hw) ∧
          RHTower.MemSchattenClass 1
            (realSummableDiagonalOperator
              (fun x : A × B => u x.1 * v x.2) hw) ∧
          C.Countable ∧
          (∀ a b : ℝ, a < b → ∃ g ∈ Set.Ioo a b, g ∉ C) ∧
          ∀ g ∉ C,
            {k : ProjectiveCharacter (A × B) |
              projectiveCharacterDetuning k
                (fun x : A × B =>
                  left x.1 + right x.2 + g * (u x.1 * v x.2)) = 0} =
              {k : ProjectiveCharacter (A × B) |
                projectiveCharacterDetuning k
                  (fun x : A × B => left x.1 + right x.2) = 0 ∧
                projectiveCharacterDetuning k
                  (fun x : A × B => u x.1 * v x.2) = 0} ∧
            RHTower.maximalRealDiagonalDomain
                (fun x : A × B =>
                  left x.1 + right x.2 + g * (u x.1 * v x.2)) =
              RHTower.maximalRealDiagonalDomain
                (fun x : A × B => left x.1 + right x.2) ∧
            IsSelfAdjoint
              (RHTower.maximalRealDiagonal
                (fun x : A × B =>
                  left x.1 + right x.2 + g * (u x.1 * v x.2))) ∧
            FinitelySupportedMaximallyProjectiveEnergy
              (fun x : A × B =>
                left x.1 + right x.2 + g * (u x.1 * v x.2)) ∧
            (∀ n : ℕ, ∃ e : Fin (n + 1) ↪ A × B,
              projectiveTemporalRank
                ((fun x : A × B =>
                  left x.1 + right x.2 + g * (u x.1 * v x.2)) ∘ e) = n) ∧
            ∀ anchor : A × B,
              screwRelationLattice
                  (anchoredProjectiveGap
                    (fun x : A × B =>
                      left x.1 + right x.2 + g * (u x.1 * v x.2))
                    anchor) = {0} ∧
              screwHull
                  (anchoredProjectiveGap
                    (fun x : A × B =>
                      left x.1 + right x.2 + g * (u x.1 * v x.2))
                    anchor) = Set.univ ∧
              (∀ T : ℝ,
                closure
                    (screwPhase
                      (anchoredProjectiveGap
                        (fun x : A × B =>
                          left x.1 + right x.2 + g * (u x.1 * v x.2))
                        anchor) '' Set.Ici T) =
                  Set.univ) ∧
              (∀ t : ℝ,
                screwPhase
                    (anchoredProjectiveGap
                      (fun x : A × B =>
                        left x.1 + right x.2 + g * (u x.1 * v x.2))
                      anchor) t = 0 →
                  t = 0) ∧
              ∀ (a : {x : A × B // x ≠ anchor} → ℝ),
                (∀ x, 0 < a x) → Summable a →
                liminf
                    (screwSeries a
                      (anchoredProjectiveGap
                        (fun x : A × B =>
                          left x.1 + right x.2 + g * (u x.1 * v x.2))
                        anchor)) Filter.atTop = 0 ∧
                limsup
                    (screwSeries a
                      (anchoredProjectiveGap
                        (fun x : A × B =>
                          left x.1 + right x.2 + g * (u x.1 * v x.2))
                        anchor)) Filter.atTop =
                  2 * ∑' x, a x ∧
                (∀ y : ℝ, 0 ≤ y → y ≤ 2 * ∑' x, a x →
                  ∀ ε : ℝ, 0 < ε →
                    ∃ L : ℝ, 0 < L ∧ ∀ tau : ℝ,
                      ∃ t ∈ Set.Icc tau (tau + L),
                        |screwSeries a
                            (anchoredProjectiveGap
                              (fun x : A × B =>
                                left x.1 + right x.2 +
                                  g * (u x.1 * v x.2))
                              anchor) t - y| < ε) ∧
                ∀ y : ℝ, 0 < y → y < 2 * ∑' x, a x →
                  ∃ L : ℝ, 0 < L ∧ ∀ tau : ℝ,
                    ∃ t ∈ Set.Icc tau (tau + L),
                      screwSeries a
                          (anchoredProjectiveGap
                            (fun x : A × B =>
                              left x.1 + right x.2 +
                                g * (u x.1 * v x.2))
                            anchor) t = y := by
  classical
  obtain ⟨u, v, hw, hu, hv, hsmall, hnorm, hself, htrace,
      hmaxDirection⟩ :=
    exists_arbitrarilyWeak_traceClassSeparableInteraction_saturating
      (fun _ : A => 0) (fun _ : B => 0) δ hδ
  let energy : A × B → ℝ := fun x => left x.1 + right x.2
  let direction : A × B → ℝ := fun x => u x.1 * v x.2
  have hmaxDirection' :
      FinitelySupportedMaximallyProjectiveEnergy direction := by
    simpa [direction] using hmaxDirection
  let C : Set ℝ := projectiveAffineCrossingSet energy direction
  have hC : C.Countable :=
    projectiveAffineCrossingSet_countable energy direction
  refine ⟨u, v, hw, C, hu, hv, hsmall, hnorm, hself, htrace,
    hC, ?_, ?_⟩
  · intro a b hab
    exact exists_not_mem_projectiveAffineCrossingSet_in_interval
      energy direction hab
  · intro g hg
    have hrelation :=
      projectiveRelationSet_affine_eq_common_of_not_mem
        energy direction g hg
    have hmaxg :
        FinitelySupportedMaximallyProjectiveEnergy
          (fun x : A × B => energy x + g * direction x) := by
      intro k hk
      have hcommon :=
        (projectiveCharacter_affineRelation_iff_common_of_not_mem
          energy direction g hg k).1 hk
      exact hmaxDirection' k hcommon.2
    have hwg : Summable (fun x : A × B => |g * direction x|) := by
      simpa [direction, abs_mul] using hw.mul_left |g|
    have hdomain := maximalRealDiagonalDomain_add_summable_eq
      energy (fun x : A × B => g * direction x) hwg
    have hHamiltonian := RHTower.maximalRealDiagonal_isSelfAdjoint
      (fun x : A × B => energy x + g * direction x)
    have hranks := hmaxg.unboundedFiniteWindowTemporalRank
    refine ⟨?_, hdomain, hHamiltonian, ?_, ?_, ?_⟩
    · simpa [energy, direction, add_assoc] using hrelation
    · simpa [energy, direction, add_assoc] using hmaxg
    · simpa [energy, direction, add_assoc] using hranks
    · intro anchor
      refine ⟨
        screwRelationLattice_anchoredProjectiveGap_eq_zero
          (fun x : A × B => energy x + g * direction x) anchor hmaxg,
        screwHull_anchoredProjectiveGap_eq_univ
          (fun x : A × B => energy x + g * direction x) anchor hmaxg,
        closure_screwPhase_anchoredProjectiveGap_image_Ici_eq_univ
          (fun x : A × B => energy x + g * direction x) anchor hmaxg,
        hmaxg.no_nonzeroExactProjectiveReturn anchor,
        ?_⟩
      intro a hpos hsum
      have hcomplete := completeSaturatedProjectiveRecurrenceLaw
        (fun x : A × B => energy x + g * direction x)
        hmaxg anchor a hpos hsum
      exact ⟨hcomplete.2.2.2.2.1,
        hcomplete.2.2.2.2.2.1,
        hcomplete.2.2.2.2.2.2.1,
        hcomplete.2.2.2.2.2.2.2⟩

end

end GaloisForLFunctions.HTGeometry
