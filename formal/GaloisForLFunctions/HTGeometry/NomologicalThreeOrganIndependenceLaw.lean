import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Logical independence and scalar no-go for three nomological organs

Descent, vertical-symbol conservativity, and relative action properness are logically independent
even on the real history group.  Polynomial rank laws coupling the three independently variable
natural-number ranks are necessarily zero.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Additive pair-response law in the one-object observer chart. -/
def PairResponseDescentLaw (rho : ℝ → ℝ) : Prop :=
  rho 0 = 0 ∧ ∀ x y, rho (x + y) = rho x + rho y

/-- Conservativity of the one-dimensional vertical symbol `rho'(0)`. -/
def VerticalSymbolConservative (rho : ℝ → ℝ) : Prop :=
  ∃ d : ℝ, d ≠ 0 ∧ HasDerivAt rho d 0

/-- Nonnegative, normalized, subadditive action with compact finite sublevels. -/
def RelativeInfCompactAction (A : ℝ → ℝ) : Prop :=
  (∀ x, 0 ≤ A x) ∧ A 0 = 0 ∧
    (∀ x y, A (x + y) ≤ A x + A y) ∧
    ∀ R : ℝ, IsCompact {x | A x ≤ R}

private theorem absoluteValue_relativeInfCompactAction :
    RelativeInfCompactAction abs := by
  refine ⟨abs_nonneg, abs_zero, abs_add_le, ?_⟩
  intro R
  convert ProperSpace.isCompact_closedBall (0 : ℝ) R using 1
  ext x
  simp

private theorem zero_not_relativeInfCompactAction :
    ¬ RelativeInfCompactAction (fun _ : ℝ => 0) := by
  intro h
  have hc : IsCompact (Set.univ : Set ℝ) := by
    simpa using h.2.2.2 0
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall 0
  have hR0 : (0 : ℝ) ∈ Metric.closedBall 0 R := hR (by simp)
  have hR1 : R + 1 ∈ Metric.closedBall (0 : ℝ) R := hR (by simp)
  simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_zero] at hR0 hR1
  rw [abs_of_nonneg (by linarith)] at hR1
  linarith

/-- Exact three witnesses proving pairwise logical independence of descent, symbol
conservativity, and relative inf-compactness. -/
theorem nomological_three_organ_logical_independence :
    (VerticalSymbolConservative (fun v : ℝ => v + v ^ (2 : ℕ)) ∧
      RelativeInfCompactAction abs ∧
      ¬ PairResponseDescentLaw (fun v : ℝ => v + v ^ (2 : ℕ))) ∧
    (PairResponseDescentLaw (fun _ : ℝ => 0) ∧
      RelativeInfCompactAction abs ∧
      ¬ VerticalSymbolConservative (fun _ : ℝ => 0)) ∧
    (PairResponseDescentLaw id ∧
      VerticalSymbolConservative id ∧
      ¬ RelativeInfCompactAction (fun _ : ℝ => 0)) := by
  have hquad : HasDerivAt (fun v : ℝ => v + v ^ (2 : ℕ)) 1 0 := by
    have h := (hasDerivAt_id' (0 : ℝ)).add ((hasDerivAt_id' (0 : ℝ)).pow 2)
    have h' : HasDerivAt ((fun x : ℝ => x) + (fun x : ℝ => x) ^ (2 : ℕ)) 1 0 :=
      h.congr_deriv (by norm_num)
    exact h'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
  refine ⟨⟨⟨1, one_ne_zero, hquad⟩, absoluteValue_relativeInfCompactAction, ?_⟩,
    ⟨⟨by simp, by simp⟩, absoluteValue_relativeInfCompactAction, ?_⟩,
    ⟨⟨by simp [id], by simp [id]⟩, ⟨1, one_ne_zero, hasDerivAt_id 0⟩,
      zero_not_relativeInfCompactAction⟩⟩
  · intro h
    have htwo := h.2 1 1
    norm_num at htwo
  · rintro ⟨d, hd, hderiv⟩
    have : d = 0 := hderiv.unique (hasDerivAt_const (0 : ℝ) 0)
    exact hd this

/-- A polynomial over any characteristic-zero domain that vanishes at every natural-number input
is the zero polynomial. -/
theorem polynomial_eq_zero_of_eval_natCast_eq_zero
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (P : Polynomial R) (hP : ∀ n : ℕ, P.eval (n : R) = 0) :
    P = 0 := by
  apply P.eq_of_infinite_eval_eq 0
  apply (Set.infinite_range_of_injective (Nat.cast_injective :
    Function.Injective (fun n : ℕ => (n : R)))).mono
  rintro x ⟨n, rfl⟩
  simpa using hP n

/-- No nonzero real- or complex-coefficient polynomial scalar law can vanish on every independently
realized natural-number rank triple.  Nested univariate polynomials encode three variables. -/
theorem scalar_three_rank_polynomial_no_go
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (F : Polynomial (Polynomial (Polynomial R)))
    (hF : ∀ h p r : ℕ,
      ((F.eval (h : Polynomial (Polynomial R))).eval (p : Polynomial R)).eval (r : R) = 0) :
    F = 0 := by
  apply polynomial_eq_zero_of_eval_natCast_eq_zero
  intro h
  apply polynomial_eq_zero_of_eval_natCast_eq_zero
  intro p
  apply polynomial_eq_zero_of_eval_natCast_eq_zero
  intro r
  exact hF h p r

end

end GaloisForLFunctions.HTGeometry
