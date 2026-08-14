import GaloisForLFunctions.RHTower.FieldOneFiniteCyclicFourierParseval
import Mathlib.MeasureTheory.Group.Measure

/-!
# Exact Haar quadrature through a cyclic quotient

Finite nonarchimedean Fourier analysis repeatedly reduces a locally constant
function to a cyclic quotient.  These theorems give the exact Haar quadrature
for that reduction.  Representatives need not form a homomorphism; only their
literal quotient values enter the proof.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory
open scoped BigOperators

/-- Translating a complete system of cyclic quotient representatives only
permutes the quotient classes. -/
theorem fieldOneFiniteCyclicQuotient_average_eq
    {G : Type*} [AddCommGroup G]
    (N : ℕ) [NeZero N]
    (q : G →+ ZMod N) (hq : Function.Surjective q)
    (rep : ZMod N → G) (hrep : ∀ r, q (rep r) = r)
    (f : G → ℂ)
    (hclass : ∀ {x y : G}, q x = q y → f x = f y)
    (x : G) :
    ∑ r : ZMod N, f (rep r + x) =
      ∑ r : ZMod N, f (rep r) := by
  obtain ⟨s, hs⟩ := hq (q x)
  apply Finset.sum_equiv (Equiv.addRight (q x))
  · simp
  · intro r _
    apply hclass
    rw [map_add, hrep, hrep]
    rfl

/-- Exact quadrature for an integrable function constant on fibers of a
surjective cyclic quotient of a compact additive Haar space of mass one. -/
theorem fieldOneFiniteCyclicQuotient_sampleSum_eq_nsmul_integral
    {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [MeasurableSpace G] [BorelSpace G] [IsTopologicalAddGroup G]
    (μ : Measure G) [μ.IsAddLeftInvariant]
    (hμ : μ Set.univ = 1)
    (N : ℕ) [NeZero N]
    (q : G →+ ZMod N) (hq : Function.Surjective q)
    (rep : ZMod N → G) (hrep : ∀ r, q (rep r) = r)
    (f : G → ℂ) (hf : Integrable f μ)
    (hclass : ∀ {x y : G}, q x = q y → f x = f y) :
    ∑ r : ZMod N, f (rep r) = N • (∫ x, f x ∂μ) := by
  calc
    ∑ r : ZMod N, f (rep r) =
        ∫ _ : G, (∑ r : ZMod N, f (rep r)) ∂μ := by
      rw [integral_const, Measure.real, hμ]
      simp
    _ = ∫ x : G, (∑ r : ZMod N, f (rep r + x)) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x =>
        (fieldOneFiniteCyclicQuotient_average_eq
          N q hq rep hrep f hclass x).symm
    _ = ∑ r : ZMod N, ∫ x : G, f (rep r + x) ∂μ := by
      apply integral_finsetSum
      intro r _
      exact hf.comp_add_left _
    _ = ∑ _r : ZMod N, ∫ x : G, f x ∂μ := by
      apply Finset.sum_congr rfl
      intro r _
      exact integral_add_left_eq_self f _
    _ = N • (∫ x, f x ∂μ) := by
      rw [Finset.sum_const, Finset.card_univ, ZMod.card]

end

end GaloisForLFunctions.RHTower
