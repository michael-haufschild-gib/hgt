import GaloisForLFunctions.HTGeometry.SummableSpectrumScrewRecurrence

/-!
# Universal countable relation-hull recurrence law

For an arbitrary countable real frequency family, finite integer relations
determine the compact phase hull.  Every forward tail is dense in that hull.
Every strictly positive summable phase-defect probe consequently sweeps one
closed interval: all its values are recurrently approximated within bounded
waiting windows, every interior value is recurrently attained exactly, and
the endpoint reaches its absolute upper bound exactly under the parity law
for finite integer relations.

No simplicity or rational-independence premise is used.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter

/-- **Countable relation-hull recurrence law.**  Every countable frequency
family, with arbitrary finite integer relations, has a complete compact
recurrence classification. -/
theorem countableRelationHullRecurrenceLaw
    {I : Type*} [Countable I]
    (omega a : I → ℝ)
    (hpos : ∀ i, 0 < a i) (hsum : Summable a) :
    screwHull omega = screwAnnihilator omega ∧
    (∀ T : ℝ,
      closure (screwPhase omega '' Set.Ici T) = screwHull omega) ∧
    (∀ T : ℝ,
      closure (screwSeries a omega '' Set.Ici T) =
        Set.Icc 0 (screwHullMax a omega)) ∧
    liminf (screwSeries a omega) atTop = 0 ∧
    limsup (screwSeries a omega) atTop = screwHullMax a omega ∧
    (∀ y : ℝ, 0 ≤ y → y ≤ screwHullMax a omega →
      ∀ ε : ℝ, 0 < ε →
        ∃ L : ℝ, 0 < L ∧ ∀ tau : ℝ,
          ∃ t ∈ Set.Icc tau (tau + L),
            |screwSeries a omega t - y| < ε) ∧
    (∀ y : ℝ, 0 < y → y < screwHullMax a omega →
      ∃ L : ℝ, 0 < L ∧ ∀ tau : ℝ,
        ∃ t ∈ Set.Icc tau (tau + L),
          screwSeries a omega t = y) ∧
    (screwHullMax a omega = 2 * ∑' i, a i ↔
      ∀ n : I →₀ ℤ, n ∈ screwRelationLattice omega →
        Even (n.sum fun _ m => m)) := by
  have hnonneg : ∀ i, 0 ≤ a i := fun i => (hpos i).le
  refine ⟨screwHull_eq_screwAnnihilator omega,
    closure_screwPhase_image_Ici omega,
    closure_screwSeries_image_Ici hnonneg hsum,
    screwSeries_liminf_eq_zero hnonneg hsum,
    screwSeries_limsup_eq_screwHullMax hnonneg hsum,
    ?_, ?_, screwHullMax_eq_two_mul_tsum_iff hpos hsum⟩
  · intro y hy0 hyM ε hε
    exact exists_window_screwSeries_near hnonneg hsum ⟨hy0, hyM⟩ hε
  · intro y hy0 hyM
    exact exists_window_screwSeries_eq hnonneg hsum hy0 hyM

end

end GaloisForLFunctions.HTGeometry
