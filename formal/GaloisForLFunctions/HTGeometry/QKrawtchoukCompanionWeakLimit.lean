import GaloisForLFunctions.HTGeometry.QKrawtchoukFiniteMeasures
import GaloisForLFunctions.HTGeometry.QKrawtchoukCompanionDeterminacy
import GaloisForLFunctions.HTGeometry.MethodOfMomentsReal

/-!
# Weak convergence of the finite companion laws

The actual finite Al-Salam--Carlitz recurrences have uniformly bounded
coefficients inside their finite blocks. Their characteristic polynomials
have no zeros outside one fixed compact interval, so the finite probability
laws share a compact support bound. The existing method of moments then
turns the proved moment limits into weak convergence to the unique companion
law. No extension-selection datum is needed for this branch of the
q-Krawtchouk limit in arXiv:2609.24149, Section 8.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
open GaloisForLFunctions.HTGeometry (HasFactorialMomentBound tendsto_of_tendsto_moments)

namespace HTGeometry

/-- A uniform diagonal bound for every finite companion recurrence. -/
theorem qKrawtchoukCompanionFiniteDiagonal_abs_le (t u : ℝ) (K n : ℕ) :
    |qKrawtchoukCompanionFiniteDiagonal t u K n| ≤ 2 + 2 * Real.exp u := by
  have hq0 : 0 ≤ qKrawtchoukEdgeBase t := (Real.exp_pos _).le
  have hq1 : qKrawtchoukEdgeBase t ≤ 1 := Real.exp_le_one_iff.mpr (by
    have := Real.exp_pos t
    linarith)
  have hc : |Real.exp u - 1| ≤ 1 + Real.exp u := by
    rw [abs_le]
    constructor <;> linarith [Real.exp_pos u]
  rw [qKrawtchoukCompanionFiniteDiagonal]
  calc
    _ ≤ |alSalamCarlitzDiagonal t u n| +
        |(Real.exp u - 1) * qKrawtchoukEdgeBase t ^ K| := abs_add_le _ _
    _ = |alSalamCarlitzDiagonal t u n| +
        |Real.exp u - 1| * qKrawtchoukEdgeBase t ^ K := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg hq0 K)]
    _ ≤ (1 + Real.exp u) + (1 + Real.exp u) * 1 :=
      add_le_add (alSalamCarlitzDiagonal_abs_le t u n)
        (mul_le_mul hc (pow_le_one₀ hq0 hq1) (pow_nonneg hq0 K) (by positivity))
    _ = _ := by ring

/-- A uniform lower-coefficient bound on the whole finite companion block. -/
theorem qKrawtchoukCompanionFiniteLower_abs_le (t u : ℝ) (K : ℕ) (i : Fin (2 * K)) :
    |qKrawtchoukCompanionFiniteLower t u K ((i : ℕ) + 1)| ≤ Real.exp u := by
  have hcut : qKrawtchoukEdgeCutoff t K ((i : ℕ) + 1) ≤ 1 := by
    rw [qKrawtchoukEdgeCutoff_eq]
    linarith [Real.exp_pos (-Real.exp t *
      (2 * (K : ℝ) - (((i : ℕ) + 1 : ℕ) : ℝ) + 1))]
  rw [abs_of_pos (qKrawtchoukFiniteLower_pos t u K i).2,
    qKrawtchoukCompanionFiniteLower]
  calc
    _ ≤ alSalamCarlitzLower t u ((i : ℕ) + 1) * 1 :=
      mul_le_mul_of_nonneg_left hcut (alSalamCarlitzLower_succ_pos t u i).le
    _ ≤ Real.exp u := by
      simpa only [mul_one, abs_of_pos (alSalamCarlitzLower_succ_pos t u i)] using
        alSalamCarlitzLower_abs_le t u i

private theorem finite_favard_growth (α β : ℕ → ℝ) (N : ℕ) (A B x : ℝ)
    (hB : 0 ≤ B) (hα : ∀ j < N, |α j| ≤ A)
    (hβ : ∀ j, j + 1 < N → |β (j + 1)| ≤ B) (hx : 1 + A + B < |x|) :
    1 ≤ |(favardPoly α β N).eval x| := by
  have hgap (j : ℕ) (hj : j < N) : 1 + B ≤ |x - α j| := by
    have ht := abs_add_le (x - α j) (α j)
    rw [sub_add_cancel] at ht
    linarith [hα j hj]
  have hrec : ∀ k, k < N → 1 ≤ |(favardPoly α β k).eval x| ∧
      |(favardPoly α β k).eval x| ≤ |(favardPoly α β (k + 1)).eval x| := by
    intro k
    induction k with
    | zero =>
        intro hk
        simp only [Nat.zero_add, favardPoly_zero, favardPoly_one, Polynomial.eval_one,
          Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, abs_one]
        exact ⟨le_rfl, by linarith [hgap 0 hk]⟩
    | succ k ih =>
        intro hk
        have hp := ih (by omega)
        refine ⟨hp.1.trans hp.2, ?_⟩
        rw [show k + 1 + 1 = k + 2 by omega, favardPoly_succ_succ]
        simp only [Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_X, Polynomial.eval_C]
        have ht := abs_add_le
          ((x - α (k + 1)) * (favardPoly α β (k + 1)).eval x -
            β (k + 1) * (favardPoly α β k).eval x)
          (β (k + 1) * (favardPoly α β k).eval x)
        rw [sub_add_cancel, abs_mul, abs_mul] at ht
        have hlow := mul_le_mul_of_nonneg_right (hgap (k + 1) hk)
          (abs_nonneg ((favardPoly α β (k + 1)).eval x))
        have hhigh : |β (k + 1)| * |(favardPoly α β k).eval x| ≤
            B * |(favardPoly α β (k + 1)).eval x| :=
          (mul_le_mul_of_nonneg_right (hβ k hk) (abs_nonneg _)).trans
            (mul_le_mul_of_nonneg_left hp.2 hB)
        nlinarith
  cases N with
  | zero => simp only [favardPoly_zero, Polynomial.eval_one, abs_one, le_refl]
  | succ N =>
      have h := hrec N (by omega)
      exact h.1.trans h.2

/-- Every finite companion law is carried by the same explicit compact interval. -/
theorem qKrawtchoukCompanionFiniteMeasure_carried (t u : ℝ) (K : ℕ) :
    (qKrawtchoukCompanionFiniteMeasure t u K : Measure ℝ)
      (Set.Icc (-(3 + 3 * Real.exp u)) (3 + 3 * Real.exp u))ᶜ = 0 := by
  have hae := (integral_eq_zero_iff_of_nonneg (fun y : ℝ =>
      sq_nonneg ((favardPoly (qKrawtchoukCompanionFiniteDiagonal t u K)
        (qKrawtchoukCompanionFiniteLower t u K) (2 * K + 1)).eval y))
    (qKrawtchoukCompanionFiniteMeasure_integrable t u K _)).mp
      (qKrawtchoukCompanionFiniteMeasure_characteristic t u K)
  change (qKrawtchoukCompanionFiniteMeasure t u K : Measure ℝ)
    {y | ¬ y ∈ Set.Icc (-(3 + 3 * Real.exp u)) (3 + 3 * Real.exp u)} = 0
  apply ae_iff.mp
  filter_upwards [hae] with y hy
  apply abs_le.mp
  by_contra hbound
  have hlarge : 1 + (2 + 2 * Real.exp u) + Real.exp u < |y| := by
    have := lt_of_not_ge hbound
    linarith
  have h := finite_favard_growth (qKrawtchoukCompanionFiniteDiagonal t u K)
    (qKrawtchoukCompanionFiniteLower t u K) (2 * K + 1)
    (2 + 2 * Real.exp u) (Real.exp u) y (Real.exp_pos u).le
    (fun j _ => qKrawtchoukCompanionFiniteDiagonal_abs_le t u K j)
    (fun j hj => qKrawtchoukCompanionFiniteLower_abs_le t u K ⟨j, by omega⟩) hlarge
  have hz : (favardPoly (qKrawtchoukCompanionFiniteDiagonal t u K)
      (qKrawtchoukCompanionFiniteLower t u K) (2 * K + 1)).eval y = 0 := by
    change _ ^ 2 = 0 at hy
    nlinarith [hy]
  rw [hz, abs_zero] at h
  linarith

/-- The actual uniquely determined companion probability measure. -/
def alSalamCarlitzMeasure (t u : ℝ) : ProbabilityMeasure ℝ :=
  (alSalamCarlitzMoment_compact_unique t u).choose

/-- The canonical companion law realizes every prescribed moment. -/
theorem alSalamCarlitzMeasure_moments (t u : ℝ) :
    GaloisForLFunctions.HTGeometry.HasHamburgerMoments (alSalamCarlitzMoment t u)
      (alSalamCarlitzMeasure t u : Measure ℝ) :=
  (alSalamCarlitzMoment_compact_unique t u).choose_spec.1

/-- The actual limit law has the previously proved compact support bound. -/
theorem alSalamCarlitzMeasure_carried (t u : ℝ) :
    (alSalamCarlitzMeasure t u : Measure ℝ)
      (Set.Icc (-(2 + 2 * Real.exp u)) (2 + 2 * Real.exp u))ᶜ = 0 :=
  (alSalamCarlitzMoment_compact_unique t u).choose_spec.2.1

private theorem factorial_bound (μ : ProbabilityMeasure ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), |x| ≤ R) :
    HasFactorialMomentBound (μ : Measure ℝ) R := by
  intro n
  have hfac : (1 : ℝ) ≤ (Nat.factorial n : ℝ) := by
    exact_mod_cast (show 1 ≤ Nat.factorial n from Nat.factorial_pos n)
  calc
    _ ≤ ∫⁻ _ : ℝ, ENNReal.ofReal (R ^ n) ∂(μ : Measure ℝ) := by
      apply lintegral_mono_ae
      filter_upwards [hμ] with x hx
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (abs_nonneg x) hx n)
    _ = ENNReal.ofReal (R ^ n) := by simp only [lintegral_const, measure_univ, mul_one]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      have := mul_le_mul_of_nonneg_right hfac (pow_nonneg hR n)
      simpa only [one_mul] using this)

/-- Moment convergence of the concrete finite companion laws is weak convergence
to the actual Al-Salam--Carlitz law, with all support and existence inputs discharged. -/
theorem qKrawtchoukCompanionFiniteMeasure_tendsto (t u : ℝ) :
    Tendsto (qKrawtchoukCompanionFiniteMeasure t u) atTop (𝓝 (alSalamCarlitzMeasure t u)) := by
  apply tendsto_of_tendsto_moments (M := 3 + 3 * Real.exp u) (by positivity)
  · intro K
    apply factorial_bound _ (by positivity)
    have h : ∀ᵐ x ∂(qKrawtchoukCompanionFiniteMeasure t u K : Measure ℝ),
        x ∈ Set.Icc (-(3 + 3 * Real.exp u)) (3 + 3 * Real.exp u) :=
      ae_iff.mpr (qKrawtchoukCompanionFiniteMeasure_carried t u K)
    filter_upwards [h] with x hx
    exact abs_le.mpr hx
  · apply factorial_bound _ (by positivity)
    have h : ∀ᵐ x ∂(alSalamCarlitzMeasure t u : Measure ℝ),
        x ∈ Set.Icc (-(2 + 2 * Real.exp u)) (2 + 2 * Real.exp u) :=
      ae_iff.mpr (alSalamCarlitzMeasure_carried t u)
    filter_upwards [h] with x hx
    have := abs_le.mpr hx
    linarith [Real.exp_pos u]
  · intro n
    rw [(alSalamCarlitzMeasure_moments t u n).2]
    exact qKrawtchoukCompanionFiniteMeasure_moment_tendsto t u n

end HTGeometry
