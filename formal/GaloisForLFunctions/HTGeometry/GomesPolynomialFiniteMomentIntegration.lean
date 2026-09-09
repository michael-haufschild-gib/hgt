import GaloisForLFunctions.HTGeometry.GomesPolynomialExpSeparation

/-!
# Polynomial observables from finite moment prefixes

Every bounded-degree polynomial observable is an exact finite linear combination of
raw moment observations. The exponential separation functional therefore depends on
only finitely many moments, with cutoff determined by the compared log-profiles.
-/

noncomputable section
open Polynomial MeasureTheory Filter
open scoped Topology NNReal ENNReal SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- Every polynomial is integrable against every finite polynomial exponential measure. -/
theorem gomesPolynomialMeasure_polynomial_integrable (P : GomesFinitePolynomialProfile) (A : ℝ[X]) :
    Integrable (fun x : ℝ => A.eval x) (gomesDilatonMeasure P.val) := by
  change Integrable _ (volume.withDensity (fun x => ENNReal.ofReal (dilatonWeight P.val x)))
  rw [integrable_withDensity_iff_integrable_smul'
    (gomesDilatonWeight_continuous P.val).measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply (gomesPolynomialAmplitude_integrable P A).congr (Eventually.of_forall (fun x => ?_))
  rw [ENNReal.toReal_ofReal (dilatonWeight_pos P.val x).le, smul_eq_mul]
  exact mul_comm _ _

/-- The polynomial observable agrees exactly with its Lebesgue density integral. -/
theorem gomesPolynomialMeasure_integral_polynomial (P : GomesFinitePolynomialProfile) (A : ℝ[X]) :
    (∫ x : ℝ, A.eval x ∂(gomesDilatonMeasure P.val)) =
      ∫ x : ℝ, A.eval x * Real.exp (P.val.eval x) := by
  change (∫ x : ℝ, A.eval x ∂(volume.withDensity
    (fun x => ENNReal.ofReal (dilatonWeight P.val x)))) = _
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (gomesDilatonWeight_continuous P.val).measurable.ennreal_ofReal.aemeasurable
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    change (ENNReal.ofReal (dilatonWeight P.val x)).toReal • A.eval x =
      A.eval x * Real.exp (P.val.eval x)
    rw [ENNReal.toReal_ofReal (dilatonWeight_pos P.val x).le, smul_eq_mul]
    exact mul_comm _ _)

/-- A polynomial observable of degree at most d uses only moments zero through d. -/
theorem gomesPolynomialMeasure_integral_eval_prefix (P : GomesFinitePolynomialProfile) (d : ℕ)
    (A : {A : ℝ[X] // A.natDegree ≤ d}) :
    (∫ x : ℝ, A.val.eval x ∂(gomesDilatonMeasure P.val)) =
      ∑ n ∈ Finset.range (d + 1), A.val.coeff n *
        (∫ x : ℝ, x ^ n ∂(gomesDilatonMeasure P.val)) := by
  have he : (fun x : ℝ => A.val.eval x) =
      fun x => ∑ n ∈ Finset.range (d + 1), A.val.coeff n * x ^ n :=
    funext (eval_eq_sum_range' (Nat.lt_succ_of_le A.property))
  rw [he, integral_finsetSum]
  · simp only [integral_const_mul]
  · intro n _
    have hn : Integrable (fun x : ℝ => x ^ n) (gomesDilatonMeasure P.val) := by
      simpa only [eval_pow, eval_X] using gomesPolynomialMeasure_polynomial_integrable P (X ^ n)
    exact hn.const_mul (A.val.coeff n)

/-- Matching a finite moment prefix is equivalent to matching all polynomial tests of that degree. -/
theorem gomesPolynomialMeasure_prefix_polynomial_iff (P Q : GomesFinitePolynomialProfile) (d : ℕ) :
    (∀ n : ℕ, n ≤ d → (∫ x : ℝ, x ^ n ∂(gomesDilatonMeasure P.val)) =
      ∫ x : ℝ, x ^ n ∂(gomesDilatonMeasure Q.val)) ↔
      ∀ A : {A : ℝ[X] // A.natDegree ≤ d},
        (∫ x : ℝ, A.val.eval x ∂(gomesDilatonMeasure P.val)) =
          ∫ x : ℝ, A.val.eval x ∂(gomesDilatonMeasure Q.val) := by
  constructor
  · intro h A
    rw [gomesPolynomialMeasure_integral_eval_prefix P d A,
      gomesPolynomialMeasure_integral_eval_prefix Q d A]
    apply Finset.sum_congr rfl
    intro n hn
    rw [h n (Nat.le_of_lt_succ (Finset.mem_range.mp hn))]
  · intro h n hn
    have he := h ⟨X ^ n, (natDegree_X_pow_le n).trans hn⟩
    simpa only [eval_pow, eval_X] using he

/-- Exponential separation is exactly one polynomial observable evaluated against the two measures. -/
theorem gomesPolynomialSeparation_integral_difference (P Q : GomesFinitePolynomialProfile) :
    gomesPolynomialSeparation P Q =
      (∫ x : ℝ, (P.val - Q.val).eval x ∂(gomesDilatonMeasure P.val)) -
        ∫ x : ℝ, (P.val - Q.val).eval x ∂(gomesDilatonMeasure Q.val) := by
  rw [gomesPolynomialMeasure_integral_polynomial, gomesPolynomialMeasure_integral_polynomial,
    ← integral_sub (gomesPolynomialAmplitude_integrable P (P.val - Q.val))
      (gomesPolynomialAmplitude_integrable Q (P.val - Q.val))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    simp only [gomesPolynomialSeparationDensity, dilatonWeight, eval_sub]
    ring)

end GaloisForLFunctions.HTGeometry
