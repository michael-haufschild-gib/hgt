import GaloisForLFunctions.HTGeometry.CountableProjectiveFutureUniversalityLaw

/-!
# Separable infinite projective-recurrence law

One arbitrarily weak separable diagonal interaction simultaneously removes
every finitely supported projective spectral relation, preserves the domain
and self-adjointness of an arbitrary countable pure-point Hamiltonian, and
forces complete projective recurrence on the resulting infinite spectrum.

The interaction is trace class and operator-norm small.  Nevertheless every
finite temporal rank occurs on one of its finite spectral windows, every
future phase tail is dense in the full projective product torus, no nonzero
exact global return survives, and every strictly positive summable defect
probe recurrently sweeps its entire allowed interval.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter

/-- **Arbitrarily weak separable infinite-recurrence law.**  For every pair
of countable real spectra whose product carrier is infinite, and every
positive operator-norm budget, one rank-one separable trace-class
interaction realizes all finite temporal ranks and the complete saturated
projective recurrence law. -/
theorem exists_arbitrarilyWeak_separable_completeProjectiveRecurrenceLaw
    {A B : Type*} [Countable A] [Countable B] [Infinite (A × B)]
    (left : A → ℝ) (right : B → ℝ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (u : A → ℝ) (v : B → ℝ),
      ∃ hw : Summable (fun x : A × B => |u x.1 * v x.2|),
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
        RHTower.maximalRealDiagonalDomain
            (fun x : A × B =>
              left x.1 + right x.2 + u x.1 * v x.2) =
          RHTower.maximalRealDiagonalDomain
            (fun x : A × B => left x.1 + right x.2) ∧
        IsSelfAdjoint
          (RHTower.maximalRealDiagonal
            (fun x : A × B =>
              left x.1 + right x.2 + u x.1 * v x.2)) ∧
        FinitelySupportedMaximallyProjectiveEnergy
          (fun x : A × B =>
            left x.1 + right x.2 + u x.1 * v x.2) ∧
        (∀ n : ℕ, ∃ e : Fin (n + 1) ↪ A × B,
          projectiveTemporalRank
            ((fun x : A × B =>
              left x.1 + right x.2 + u x.1 * v x.2) ∘ e) = n) ∧
        ∀ anchor : A × B,
          screwRelationLattice
              (anchoredProjectiveGap
                (fun x : A × B =>
                  left x.1 + right x.2 + u x.1 * v x.2)
                anchor) = {0} ∧
          screwHull
              (anchoredProjectiveGap
                (fun x : A × B =>
                  left x.1 + right x.2 + u x.1 * v x.2)
                anchor) = Set.univ ∧
          (∀ T : ℝ,
            closure
                (screwPhase
                  (anchoredProjectiveGap
                    (fun x : A × B =>
                      left x.1 + right x.2 + u x.1 * v x.2)
                    anchor) '' Set.Ici T) =
              Set.univ) ∧
          (∀ t : ℝ,
            screwPhase
                (anchoredProjectiveGap
                  (fun x : A × B =>
                    left x.1 + right x.2 + u x.1 * v x.2)
                  anchor) t = 0 →
              t = 0) ∧
          ∀ (a : {x : A × B // x ≠ anchor} → ℝ),
            (∀ x, 0 < a x) → Summable a →
            liminf
                (screwSeries a
                  (anchoredProjectiveGap
                    (fun x : A × B =>
                      left x.1 + right x.2 + u x.1 * v x.2)
                    anchor)) Filter.atTop = 0 ∧
            limsup
                (screwSeries a
                  (anchoredProjectiveGap
                    (fun x : A × B =>
                      left x.1 + right x.2 + u x.1 * v x.2)
                    anchor)) Filter.atTop =
              2 * ∑' x, a x ∧
            (∀ y : ℝ, 0 ≤ y → y ≤ 2 * ∑' x, a x →
              ∀ ε : ℝ, 0 < ε →
                ∃ L : ℝ, 0 < L ∧ ∀ tau : ℝ,
                  ∃ t ∈ Set.Icc tau (tau + L),
                    |screwSeries a
                        (anchoredProjectiveGap
                          (fun x : A × B =>
                            left x.1 + right x.2 + u x.1 * v x.2)
                          anchor) t - y| < ε) ∧
            ∀ y : ℝ, 0 < y → y < 2 * ∑' x, a x →
              ∃ L : ℝ, 0 < L ∧ ∀ tau : ℝ,
                ∃ t ∈ Set.Icc tau (tau + L),
                  screwSeries a
                      (anchoredProjectiveGap
                        (fun x : A × B =>
                          left x.1 + right x.2 + u x.1 * v x.2)
                        anchor) t = y := by
  obtain ⟨u, v, hw, hu, hv, hsmall, hnorm, hinteractionSelf,
      htrace, hdomain, hhamiltonianSelf, hmax⟩ :=
    exists_arbitrarilyWeak_traceClassSeparableHamiltonian_saturating
      left right δ hδ
  let energy : A × B → ℝ := fun x =>
    left x.1 + right x.2 + u x.1 * v x.2
  have hmaxEnergy : FinitelySupportedMaximallyProjectiveEnergy energy := by
    simpa [energy] using hmax
  refine ⟨u, v, hw, hu, hv, hsmall, hnorm, hinteractionSelf,
    htrace, hdomain, hhamiltonianSelf, hmax, ?_, ?_⟩
  · simpa [energy] using hmaxEnergy.unboundedFiniteWindowTemporalRank
  · intro anchor
    refine ⟨
      screwRelationLattice_anchoredProjectiveGap_eq_zero
        energy anchor hmaxEnergy,
      screwHull_anchoredProjectiveGap_eq_univ
        energy anchor hmaxEnergy,
      closure_screwPhase_anchoredProjectiveGap_image_Ici_eq_univ
        energy anchor hmaxEnergy,
      hmaxEnergy.no_nonzeroExactProjectiveReturn anchor,
      ?_⟩
    intro a hpos hsum
    have hcomplete := completeSaturatedProjectiveRecurrenceLaw
      energy hmaxEnergy anchor a hpos hsum
    exact ⟨hcomplete.2.2.2.2.1,
      hcomplete.2.2.2.2.2.1,
      hcomplete.2.2.2.2.2.2.1,
      hcomplete.2.2.2.2.2.2.2⟩

end

end GaloisForLFunctions.HTGeometry
