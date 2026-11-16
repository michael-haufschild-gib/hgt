import GaloisForLFunctions.RHTower.FieldOneFiniteQuotientHaarQuadrature
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Probabilities of finite-quotient events

Exact Haar quadrature applied to an indicator identifies every event
determined by a finite additive quotient with its uniform counting
probability. Continuity of the quotient supplies measurability.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting

open MeasureTheory

/-- A continuous finite quotient sends Haar probability to uniform counting probability. -/
theorem haar_finite_quotient_probability
    {G Q : Type*} [AddCommGroup G] [AddCommGroup Q] [Fintype Q]
    [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [IsTopologicalAddGroup G] [TopologicalSpace Q] [DiscreteTopology Q]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (q : G →+ Q) (hq : Function.Surjective q) (hc : Continuous q) (P : Q → Prop) :
    μ.real {x | P (q x)} = (Nat.card {r : Q // P r} : ℝ) / Nat.card Q := by
  classical
  let rep : Q → G := fun r => (hq r).choose
  have hrep (r : Q) : q (rep r) = r := (hq r).choose_spec
  have hs : MeasurableSet {x : G | P (q x)} :=
    ((isOpen_discrete {r : Q | P r}).preimage hc).measurableSet
  let f : G → ℂ := {x : G | P (q x)}.indicator (fun _ => 1)
  have hf : Integrable f μ := (integrable_const (1 : ℂ)).indicator hs
  have hclass : ∀ {x y : G}, q x = q y → f x = f y := by
    intro x y h
    simp only [f, Set.indicator_apply, Set.mem_setOf_eq, h]
  have h := RHTower.fieldOneFiniteQuotient_sampleSum_eq_nsmul_integral
    μ (measure_univ) q hq rep hrep f hf hclass
  have hsum : (∑ r : Q, f (rep r)) = (Nat.card {r : Q // P r} : ℂ) := by
    simp only [f, Set.indicator_apply, Set.mem_setOf_eq, hrep]
    rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hsum] at h
  change (Nat.card {r : Q // P r} : ℂ) =
    Fintype.card Q • (∫ x, {x : G | P (q x)}.indicator (fun _ => (1 : ℂ)) x ∂μ) at h
  rw [integral_indicator hs, setIntegral_const] at h
  have hr : (Nat.card {r : Q // P r} : ℝ) =
      (Nat.card Q : ℝ) * μ.real {x : G | P (q x)} := by
    have h' : (Nat.card {r : Q // P r} : ℂ) =
        (Nat.card Q : ℂ) * (μ.real {x : G | P (q x)} : ℂ) := by
      simpa only [Nat.card_eq_fintype_card, nsmul_eq_mul, Complex.real_smul, mul_one] using h
    exact_mod_cast h'
  have hn : (Nat.card Q : ℝ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := Q)).ne'
  exact (eq_div_iff hn).mpr (by rw [mul_comm]; exact hr.symm)

#print axioms haar_finite_quotient_probability

end GaloisForLFunctions.RepresentationLifting
