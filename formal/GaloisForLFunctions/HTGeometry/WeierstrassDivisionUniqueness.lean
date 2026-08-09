import GaloisForLFunctions.HTGeometry.AnalyticFactorDvd
import GaloisForLFunctions.HTGeometry.LowDegreeVanishing

/-!
# Uniqueness of division by a monic polynomial on a disc

Division of a holomorphic function by the monic polynomial of a root multiset — quotient
holomorphic, remainder of degree below the number of roots — is unique.  Two such decompositions of
the same function have the same remainder coefficients and the same quotient.

The remainder is settled first: the difference of the two remainders is a polynomial of degree below
`card M` which the analytic identity exhibits as divisible by the product of the linear factors, so
it vanishes.  The quotients then differ by a function killed by that product, and cancelling the
factors one at a time shows the difference is zero.

* `HTGeometry.eqOn_of_multisetLinearProd_mul_eqOn`;
* `HTGeometry.divisionOnDisc_unique`.
-/

open Metric

namespace HTGeometry

/-- **The product of the linear factors cancels from an identity on a disc.** -/
theorem eqOn_of_multisetLinearProd_mul_eqOn {c : ℂ} {R : ℝ} (M : Multiset ℂ) :
    ∀ (F G : ℂ → ℂ), ContinuousOn F (ball c R) → ContinuousOn G (ball c R) →
      (∀ z ∈ ball c R, multisetLinearProd M z * F z = multisetLinearProd M z * G z) →
      ∀ z ∈ ball c R, F z = G z := by
  classical
  induction M using Multiset.induction_on with
  | empty =>
    intro F G _ _ h z hz
    have := h z hz
    simpa [multisetLinearProd] using this
  | cons r M' ih =>
    intro F G hF hG h
    have hstep : ∀ z ∈ ball c R,
        (z - r) * (multisetLinearProd M' z * F z)
          = (z - r) * (multisetLinearProd M' z * G z) := by
      intro z hz
      have := h z hz
      simpa [multisetLinearProd, mul_assoc] using this
    have hcontF : ContinuousOn (fun z : ℂ => multisetLinearProd M' z * F z) (ball c R) :=
      (continuous_multisetLinearProd M').continuousOn.mul hF
    have hcontG : ContinuousOn (fun z : ℂ => multisetLinearProd M' z * G z) (ball c R) :=
      (continuous_multisetLinearProd M').continuousOn.mul hG
    exact ih F G hF hG (eqOn_of_sub_mul_eqOn hcontF hcontG hstep)

/-- **Division by the monic polynomial of a root multiset is unique on a disc.**

Both the remainder coefficients below `card M` and the quotient are determined. -/
theorem divisionOnDisc_unique {c : ℂ} {R : ℝ} {M : Multiset ℂ}
    (hM : ∀ r ∈ M, r ∈ ball c R) {a b : ℕ → ℂ} {q₁ q₂ : ℂ → ℂ}
    (hq₁ : ContinuousOn q₁ (ball c R)) (hq₂ : ContinuousOn q₂ (ball c R))
    (heq : ∀ z ∈ ball c R,
      multisetLinearProd M z * q₁ z
          + ∑ l ∈ Finset.range (Multiset.card M), a l * z ^ l
        = multisetLinearProd M z * q₂ z
          + ∑ l ∈ Finset.range (Multiset.card M), b l * z ^ l) :
    (∀ l < Multiset.card M, a l = b l) ∧ ∀ z ∈ ball c R, q₁ z = q₂ z := by
  classical
  set k : ℕ := Multiset.card M with hk
  obtain ⟨d, hd⟩ : ∃ d : ℕ → ℂ, d = fun l => a l - b l := ⟨_, rfl⟩
  set P : Polynomial ℂ :=
    ∑ l ∈ Finset.range k, Polynomial.C (d l) * Polynomial.X ^ l with hP
  have hPeval : ∀ z : ℂ, P.eval z = ∑ l ∈ Finset.range k, (a l - b l) * z ^ l := by
    intro z
    rw [hP, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [hd]
  -- the analytic identity makes the remainder difference divisible by the linear product
  have hfact : ∀ z ∈ ball c R, P.eval z = (q₂ z - q₁ z) * multisetLinearProd M z := by
    intro z hz
    have h := heq z hz
    have hsplit : ∑ l ∈ Finset.range k, (a l - b l) * z ^ l
        = (∑ l ∈ Finset.range k, a l * z ^ l) - ∑ l ∈ Finset.range k, b l * z ^ l := by
      rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [hPeval z, hsplit]
    linear_combination h
  have hcontq : ContinuousOn (fun z : ℂ => q₂ z - q₁ z) (ball c R) := hq₂.sub hq₁
  have hdvd := multisetProd_dvd_of_analytic_factor M P (fun z => q₂ z - q₁ z) hM hcontq hfact
  -- degree below `card M` forces it to vanish
  have hzeroP : P = 0 := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hP, hk0]
      simp
    · refine eq_zero_of_multisetProd_dvd_of_natDegree_lt hdvd ?_
      have hdegle : P.natDegree ≤ k - 1 := by
        rw [hP]
        refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun l hl => ?_
        have hl' := Finset.mem_range.1 hl
        exact le_trans (le_trans (Polynomial.natDegree_C_mul_le _ _)
          (le_of_eq (Polynomial.natDegree_X_pow l))) (by omega)
      omega
  have hcoeff : ∀ l < k, a l = b l := by
    intro l hl
    have hc := congrArg (fun p : Polynomial ℂ => p.coeff l) hzeroP
    simp only [Polynomial.coeff_zero] at hc
    rw [hP] at hc
    have hsub : d l = 0 := by
      simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Finset.sum_ite_eq', Finset.mem_range, hl] using hc
    have : a l - b l = 0 := by rw [hd] at hsub; exact hsub
    exact sub_eq_zero.1 this
  refine ⟨hcoeff, ?_⟩
  -- with equal remainders the quotients differ by something the product kills
  refine eqOn_of_multisetLinearProd_mul_eqOn M q₁ q₂ hq₁ hq₂ fun z hz => ?_
  have h := heq z hz
  have hrem : ∑ l ∈ Finset.range k, a l * z ^ l = ∑ l ∈ Finset.range k, b l * z ^ l := by
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [hcoeff l (Finset.mem_range.1 hl)]
  rw [hrem] at h
  exact add_right_cancel h

end HTGeometry
