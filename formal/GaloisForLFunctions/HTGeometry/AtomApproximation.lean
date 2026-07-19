import GaloisForLFunctions.HTGeometry.CarriedAtomic

/-!
# The remaining core, isolated

For a representing measure carried by a countable set, the variational property of the Christoffel
limit turns every polynomial normalised at a point of the carrier into an upper bound

`λ(ξ) ≤ ∑_{η ∈ F} μ{η}·p(η)²`.

The right side always contains the term `μ{ξ}`, so the bound `λ(ξ) ≤ μ{ξ}` — the reverse of the
general atom bound, and the last thing this card needs — follows as soon as the remaining terms can
be made small.  That approximation statement is what is isolated here.
-/

open scoped BigOperators
open MeasureTheory

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **Integration against a measure carried by a countable set is a sum over that set.** -/
theorem lintegral_eq_tsum_atoms (μ : Measure ℝ) [IsFiniteMeasure μ] {F : Set ℝ}
    (hF : F.Countable) (hFm : MeasurableSet F) (hcar : μ Fᶜ = 0) (f : ℝ → ENNReal) :
    ∫⁻ x, f x ∂μ = ∑' η : ↥F, μ {(η : ℝ)} * f (η : ℝ) := by
  conv_lhs => rw [measure_eq_fiberMeasure_of_carried μ hF hFm hcar]
  rw [lintegral_fiberMeasure]
  exact tsum_congr fun η => by rw [ENNReal.ofReal_toReal (measure_ne_top μ _)]

/-- **Every polynomial normalised at `ξ` bounds `λ(ξ)` by a weighted sum over the carrier.** -/
theorem christoffelLimit_le_tsum_atoms (h : PositiveMomentForm s) {μ : Measure ℝ}
    [IsFiniteMeasure μ] (hmom : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s μ)
    {F : Set ℝ} (hF : F.Countable) (hFm : MeasurableSet F) (hcar : μ Fᶜ = 0)
    (ξ : ℝ) (p : Polynomial ℝ) (hp : p.eval ξ = 1) :
    ENNReal.ofReal (christoffelLimit s ξ)
      ≤ ∑' η : ↥F, μ {(η : ℝ)} * ENNReal.ofReal ((p.eval (η : ℝ)) ^ 2) := by
  have hs : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂μ := fun k => (hmom k).2.symm
  have hint : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) μ := fun k => (hmom k).1
  have hvar : christoffelLimit s ξ ≤ momentInner s p p :=
    christoffelLimit_le_momentInner_self h ξ p hp
  have hsq : momentInner s p p = ∫ x, (p.eval x) ^ 2 ∂μ := by
    rw [momentInner_def]
    have hpp : p * p = p ^ 2 := by ring
    rw [hpp, momentFunctional_pow_two_eq_integral_sq s hs hint p]
  have hInt : Integrable (fun y : ℝ => (Polynomial.eval y p) ^ 2) μ := by
    refine (integrable_eval hint (p ^ 2)).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Polynomial.eval_pow]
  have hnn : 0 ≤ᵐ[μ] fun y : ℝ => (Polynomial.eval y p) ^ 2 :=
    Filter.Eventually.of_forall fun y => sq_nonneg _
  calc ENNReal.ofReal (christoffelLimit s ξ)
      ≤ ENNReal.ofReal (∫ x, (p.eval x) ^ 2 ∂μ) := by
        rw [← hsq]
        exact ENNReal.ofReal_le_ofReal hvar
    _ = ∫⁻ x, ENNReal.ofReal ((p.eval x) ^ 2) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hInt hnn
    _ = ∑' η : ↥F, μ {(η : ℝ)} * ENNReal.ofReal ((p.eval (η : ℝ)) ^ 2) :=
        lintegral_eq_tsum_atoms μ hF hFm hcar _

/-- The approximation property that the remaining core asks for: polynomials normalised at `ξ` whose
weighted square sum over the carrier tends to the atom at `ξ`. -/
def AtomApproximable (μ : Measure ℝ) (F : Set ℝ) (ξ : ℝ) : Prop :=
  ∀ ε : ENNReal, 0 < ε → ∃ p : Polynomial ℝ, p.eval ξ = 1 ∧
    ∑' η : ↥F, μ {(η : ℝ)} * ENNReal.ofReal ((p.eval (η : ℝ)) ^ 2) ≤ μ {ξ} + ε

/-- **The approximation property gives the reverse atom bound.** -/
theorem ofReal_christoffelLimit_le_measure_singleton (h : PositiveMomentForm s) {μ : Measure ℝ}
    [IsFiniteMeasure μ] (hmom : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s μ)
    {F : Set ℝ} (hF : F.Countable) (hFm : MeasurableSet F) (hcar : μ Fᶜ = 0)
    {ξ : ℝ} (happrox : AtomApproximable μ F ξ) :
    ENNReal.ofReal (christoffelLimit s ξ) ≤ μ {ξ} := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨p, hp, hle⟩ := happrox (ε : ENNReal) (by exact_mod_cast hε)
  exact le_trans (christoffelLimit_le_tsum_atoms h hmom hF hFm hcar ξ p hp) hle

/-- **The atoms are the Christoffel limits, given the approximation property.**  This closes the
weight identification for every point where the approximation holds. -/
theorem measure_singleton_eq_ofReal_christoffelLimit (h : PositiveMomentForm s) {μ : Measure ℝ}
    [IsFiniteMeasure μ] (hmom : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s μ)
    {F : Set ℝ} (hF : F.Countable) (hFm : MeasurableSet F) (hcar : μ Fᶜ = 0)
    {ξ : ℝ} (happrox : AtomApproximable μ F ξ) :
    μ {ξ} = ENNReal.ofReal (christoffelLimit s ξ) :=
  le_antisymm (measure_singleton_le_ofReal_christoffelLimit h hmom ξ)
    (ofReal_christoffelLimit_le_measure_singleton h hmom hF hFm hcar happrox)

end HTGeometry
