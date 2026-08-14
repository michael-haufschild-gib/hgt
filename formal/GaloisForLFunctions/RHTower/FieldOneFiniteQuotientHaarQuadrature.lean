import GaloisForLFunctions.RHTower.FieldOneFiniteCyclicHaarQuadrature

/-!
# Exact Haar quadrature through arbitrary finite additive quotients

The cyclic quadrature theorem extends without loss to every finite additive
quotient of a compact Haar probability group.  This is the simultaneous
finite-place quadrature needed for a finite product of p-adic residue groups.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory
open scoped BigOperators

/-- Translating a complete system of representatives of any finite additive
quotient only permutes its classes. -/
theorem fieldOneFiniteQuotient_average_eq
    {G Q : Type*} [AddCommGroup G] [AddCommGroup Q] [Fintype Q]
    (q : G →+ Q) (hq : Function.Surjective q)
    (rep : Q → G) (hrep : ∀ r, q (rep r) = r)
    (f : G → ℂ)
    (hclass : ∀ {x y : G}, q x = q y → f x = f y)
    (x : G) :
    ∑ r : Q, f (rep r + x) = ∑ r : Q, f (rep r) := by
  obtain ⟨s, hs⟩ := hq (q x)
  apply Finset.sum_equiv (Equiv.addRight (q x))
  · simp
  · intro r _
    apply hclass
    rw [map_add, hrep, hrep]
    rfl

/-- Exact quadrature for an integrable function constant on the fibers of a
surjective finite additive quotient of a compact Haar probability space. -/
theorem fieldOneFiniteQuotient_sampleSum_eq_nsmul_integral
    {G Q : Type*} [AddCommGroup G] [AddCommGroup Q] [Fintype Q]
    [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [IsTopologicalAddGroup G]
    (μ : Measure G) [μ.IsAddLeftInvariant]
    (hμ : μ Set.univ = 1)
    (q : G →+ Q) (hq : Function.Surjective q)
    (rep : Q → G) (hrep : ∀ r, q (rep r) = r)
    (f : G → ℂ) (hf : Integrable f μ)
    (hclass : ∀ {x y : G}, q x = q y → f x = f y) :
    ∑ r : Q, f (rep r) =
      Fintype.card Q • (∫ x, f x ∂μ) := by
  calc
    ∑ r : Q, f (rep r) =
        ∫ _ : G, (∑ r : Q, f (rep r)) ∂μ := by
      rw [integral_const, Measure.real, hμ]
      simp
    _ = ∫ x : G, (∑ r : Q, f (rep r + x)) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x =>
        (fieldOneFiniteQuotient_average_eq
          q hq rep hrep f hclass x).symm
    _ = ∑ r : Q, ∫ x : G, f (rep r + x) ∂μ := by
      apply integral_finsetSum
      intro r _
      exact hf.comp_add_left _
    _ = ∑ _r : Q, ∫ x : G, f x ∂μ := by
      apply Finset.sum_congr rfl
      intro r _
      exact integral_add_left_eq_self f _
    _ = Fintype.card Q • (∫ x, f x ∂μ) := by
      rw [Finset.sum_const, Finset.card_univ]

end

end GaloisForLFunctions.RHTower
