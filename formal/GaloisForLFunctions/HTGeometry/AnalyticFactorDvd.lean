import GaloisForLFunctions.HTGeometry.PunctureCancellation
import GaloisForLFunctions.HTGeometry.DiscRootMultiset
import Mathlib.Topology.Algebra.Polynomial

/-!
# An analytic factorization on a disc forces polynomial divisibility

If a polynomial agrees on a disc with a continuous function times the product of the linear factors
at a multiset, and every element of that multiset lies in the disc, then the polynomial is divisible
by that product *in the polynomial ring*.

The proof peels one factor at a time: evaluating at a root of the product exhibits it as a root of
the polynomial, so a linear factor splits off, and the linear factor then cancels from the analytic
identity, leaving the same situation one degree down.  Multiplicities need no separate treatment —
a repeated element of the multiset is simply peeled twice.

* `HTGeometry.multisetProd_dvd_of_analytic_factor`.
-/

open Metric

namespace HTGeometry

/-- **An analytic factorization on a disc gives divisibility of polynomials.** -/
theorem multisetProd_dvd_of_analytic_factor {c : ℂ} {R : ℝ} (M : Multiset ℂ) :
    ∀ (P : Polynomial ℂ) (q : ℂ → ℂ), (∀ r ∈ M, r ∈ ball c R) →
      ContinuousOn q (ball c R) →
      (∀ z ∈ ball c R, P.eval z = q z * multisetLinearProd M z) →
      (M.map fun r => Polynomial.X - Polynomial.C r).prod ∣ P := by
  classical
  induction M using Multiset.induction_on with
  | empty =>
    intro P q _ _ _
    simp
  | cons r M' ih =>
    intro P q hM hq heq
    have hr : r ∈ ball c R := hM r (Multiset.mem_cons_self r M')
    have hM' : ∀ x ∈ M', x ∈ ball c R := fun x hx => hM x (Multiset.mem_cons_of_mem hx)
    have hsplit : ∀ z : ℂ,
        multisetLinearProd (r ::ₘ M') z = (z - r) * multisetLinearProd M' z := by
      intro z
      simp [multisetLinearProd]
    -- `r` is a root of `P`, so a linear factor splits off
    have hroot : P.IsRoot r := by
      have := heq r hr
      rw [hsplit r] at this
      simpa using this
    obtain ⟨P₁, hP₁⟩ := (Polynomial.dvd_iff_isRoot (a := r) (p := P)).2 hroot
    -- cancel that factor from the analytic identity
    have hcancel : ∀ z ∈ ball c R,
        (z - r) * P₁.eval z = (z - r) * (q z * multisetLinearProd M' z) := by
      intro z hz
      have h1 : P.eval z = (z - r) * P₁.eval z := by
        rw [hP₁]
        simp
      have h2 := heq z hz
      rw [hsplit z, h1] at h2
      rw [h2]
      ring
    have hcontF : ContinuousOn (fun z : ℂ => P₁.eval z) (ball c R) :=
      P₁.continuous.continuousOn
    have hcontG : ContinuousOn (fun z : ℂ => q z * multisetLinearProd M' z) (ball c R) :=
      hq.mul (continuous_multisetLinearProd M').continuousOn
    have hEq := eqOn_of_sub_mul_eqOn hcontF hcontG hcancel
    -- one degree down
    have hdvd₁ := ih P₁ q hM' hq hEq
    have hprod : ((r ::ₘ M').map fun x => Polynomial.X - Polynomial.C x).prod
        = (Polynomial.X - Polynomial.C r)
          * (M'.map fun x => Polynomial.X - Polynomial.C x).prod := by
      simp
    rw [hprod, hP₁]
    exact mul_dvd_mul_left _ hdvd₁

end HTGeometry
