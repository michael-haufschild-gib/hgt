import GaloisForLFunctions.HTGeometry.ComplexPolynomialZeroMeasure

/-!
# Polynomial avoidance under absolutely continuous finite-coordinate laws

Finite-jet nondegeneracy is used through one measure-theoretic mechanism: the law of a finite
complex coordinate packet is absolutely continuous with respect to Lebesgue measure, while the
zero set of a nonzero polynomial is Lebesgue-null.  This file records that mechanism once and
upgrades it to a countable family of packets of varying dimensions.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- An absolutely continuous finite complex coordinate law assigns measure zero to the pullback
of the zero set of every nonzero multivariate polynomial. -/
theorem measure_mvPolynomial_eval_eq_zero_of_map_absolutelyContinuous
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {n : ℕ}
    (X : Ω → (Fin n → ℂ)) (hX : Measurable X)
    (hAC : (Measure.map X μ).AbsolutelyContinuous
      (volume : Measure (Fin n → ℂ)))
    (P : MvPolynomial (Fin n) ℂ) (hP : P ≠ 0) :
    μ {ω | MvPolynomial.eval (X ω) P = 0} = 0 := by
  let Z : Set (Fin n → ℂ) := {x | MvPolynomial.eval x P = 0}
  have hZ : MeasurableSet Z :=
    isClosed_singleton.preimage P.continuous_eval |>.measurableSet
  have hpre : X ⁻¹' Z = {ω | MvPolynomial.eval (X ω) P = 0} := rfl
  rw [← hpre, ← Measure.map_apply hX hZ]
  exact hAC (mvPolynomial_zero_set_volume_fin n P hP)

/-- Countably many nonzero polynomial constraints, each read through its own absolutely
continuous finite-coordinate marginal, fail only on one null event.  Packet dimensions may vary
with the constraint. -/
theorem measure_exists_mvPolynomial_eval_eq_zero_of_countable
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] (μ : Measure Ω)
    (n : ι → ℕ) (X : ∀ i, Ω → (Fin (n i) → ℂ))
    (hX : ∀ i, Measurable (X i))
    (hAC : ∀ i, (Measure.map (X i) μ).AbsolutelyContinuous
      (volume : Measure (Fin (n i) → ℂ)))
    (P : ∀ i, MvPolynomial (Fin (n i)) ℂ) (hP : ∀ i, P i ≠ 0) :
    μ {ω | ∃ i, MvPolynomial.eval (X i ω) (P i) = 0} = 0 := by
  have hnull : ∀ i, μ {ω | MvPolynomial.eval (X i ω) (P i) = 0} = 0 :=
    fun i => measure_mvPolynomial_eval_eq_zero_of_map_absolutelyContinuous
      μ (X i) (hX i) (hAC i) (P i) (hP i)
  have hset : {ω | ∃ i, MvPolynomial.eval (X i ω) (P i) = 0} =
      ⋃ i, {ω | MvPolynomial.eval (X i ω) (P i) = 0} := by
    ext ω
    simp
  rw [hset]
  exact measure_iUnion_null hnull

/-- Almost-everywhere form of countable polynomial avoidance. -/
theorem ae_forall_mvPolynomial_eval_ne_zero_of_countable
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] (μ : Measure Ω)
    (n : ι → ℕ) (X : ∀ i, Ω → (Fin (n i) → ℂ))
    (hX : ∀ i, Measurable (X i))
    (hAC : ∀ i, (Measure.map (X i) μ).AbsolutelyContinuous
      (volume : Measure (Fin (n i) → ℂ)))
    (P : ∀ i, MvPolynomial (Fin (n i)) ℂ) (hP : ∀ i, P i ≠ 0) :
    ∀ᵐ ω ∂μ, ∀ i, MvPolynomial.eval (X i ω) (P i) ≠ 0 := by
  rw [ae_iff]
  simpa only [not_forall, Classical.not_not] using
    measure_exists_mvPolynomial_eval_eq_zero_of_countable μ n X hX hAC P hP

end

end GaloisForLFunctions.HTGeometry
