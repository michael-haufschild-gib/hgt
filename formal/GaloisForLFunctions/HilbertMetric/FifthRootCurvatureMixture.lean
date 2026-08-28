import GaloisForLFunctions.HilbertMetric.FifthRootCurvatureCusp

/-!
# Law of total variance for fifth-root curvature

The fifth-root divided-drop numerator is quadratic in accumulated drop `A`,
endpoint flux `D`, and flux curvature `J`.  Its polarization has an exact
variance remainder.  Consequently fifth-root curvature is closed under adding
two positive-drop profiles; no comparison between their flux ratios is needed.
-/

namespace HilbertMetric

noncomputable section

/-- Algebraic fifth-root curvature form in accumulated-drop coordinates. -/
def fifthRootCurvatureJetForm (t A D J : ℝ) : ℝ :=
  24 * A ^ 2 - 9 * t * A * D + t ^ 2 * (5 * A * J - 4 * D ^ 2)

/-- The functional numerator is its algebraic jet form with
`A = f(0)-f(t)`, `D = -f'(t)`, and `J = -f''(t)`. -/
theorem fifthRootDividedDropCurvatureNumerator_eq_jetForm
    (f : ℝ → ℝ) (t : ℝ) :
    fifthRootDividedDropCurvatureNumerator f t =
      fifthRootCurvatureJetForm t (f 0 - f t)
        (-iteratedDeriv 1 f t) (-iteratedDeriv 2 f t) := by
  unfold fifthRootDividedDropCurvatureNumerator fifthRootCurvatureJetForm
  ring

/-- **Fifth-root law of total variance.**  After clearing only the two drop
denominators, curvature of a sum is the two component curvatures plus the
square of their normalized-flux disagreement.  This identity has no sign or
regularity hypotheses. -/
theorem fifthRootCurvatureJetForm_add_totalVariance
    (t A₁ D₁ J₁ A₂ D₂ J₂ : ℝ) :
    A₁ * A₂ * fifthRootCurvatureJetForm t
        (A₁ + A₂) (D₁ + D₂) (J₁ + J₂) =
      A₂ * (A₁ + A₂) * fifthRootCurvatureJetForm t A₁ D₁ J₁ +
      A₁ * (A₁ + A₂) * fifthRootCurvatureJetForm t A₂ D₂ J₂ +
      4 * t ^ 2 * (A₁ * D₂ - A₂ * D₁) ^ 2 := by
  unfold fifthRootCurvatureJetForm
  ring

/-- Peeling form of the total-variance identity.  A distinguished component
`(a,d,j)` is removed from a total jet `(A,D,J)`; the variance remainder depends
only on the projective flux mismatch `aD-Ad`. -/
theorem fifthRootCurvatureJetForm_peel_totalVariance
    (t A D J a d j : ℝ) :
    a * (A - a) * fifthRootCurvatureJetForm t A D J =
      (A - a) * A * fifthRootCurvatureJetForm t a d j +
      a * A * fifthRootCurvatureJetForm t (A - a) (D - d) (J - j) +
      4 * t ^ 2 * (a * D - A * d) ^ 2 := by
  have h := fifthRootCurvatureJetForm_add_totalVariance
    t a d j (A - a) (D - d) (J - j)
  unfold fifthRootCurvatureJetForm at h ⊢
  ring_nf at h ⊢

/-- Adding two positive-drop profiles with nonnegative fifth-root curvature
preserves nonnegative fifth-root curvature. -/
theorem fifthRootCurvatureJetForm_add_nonneg
    {t A₁ D₁ J₁ A₂ D₂ J₂ : ℝ}
    (hA₁ : 0 < A₁) (hA₂ : 0 < A₂)
    (hC₁ : 0 ≤ fifthRootCurvatureJetForm t A₁ D₁ J₁)
    (hC₂ : 0 ≤ fifthRootCurvatureJetForm t A₂ D₂ J₂) :
    0 ≤ fifthRootCurvatureJetForm t
      (A₁ + A₂) (D₁ + D₂) (J₁ + J₂) := by
  have hRhs : 0 ≤
      A₂ * (A₁ + A₂) * fifthRootCurvatureJetForm t A₁ D₁ J₁ +
      A₁ * (A₁ + A₂) * fifthRootCurvatureJetForm t A₂ D₂ J₂ +
      4 * t ^ 2 * (A₁ * D₂ - A₂ * D₁) ^ 2 := by
    positivity
  have hEq := fifthRootCurvatureJetForm_add_totalVariance
    t A₁ D₁ J₁ A₂ D₂ J₂
  have hprod : 0 ≤ A₁ * A₂ * fifthRootCurvatureJetForm t
      (A₁ + A₂) (D₁ + D₂) (J₁ + J₂) := by
    rw [hEq]
    exact hRhs
  exact (mul_nonneg_iff_of_pos_left (mul_pos hA₁ hA₂)).mp (by
    simpa only [mul_assoc] using hprod)

/-- Every nonempty finite positive-drop mixture preserves nonnegative
fifth-root curvature.  The variance square is generated at each insertion,
so no pairwise flux ordering is required. -/
theorem fifthRootCurvatureJetForm_finset_sum_nonneg
    {ι : Type*} [DecidableEq ι] {t : ℝ} (s : Finset ι)
    (A D J : ι → ℝ) (hs : s.Nonempty)
    (hA : ∀ i ∈ s, 0 < A i)
    (hC : ∀ i ∈ s, 0 ≤ fifthRootCurvatureJetForm t (A i) (D i) (J i)) :
    0 ≤ fifthRootCurvatureJetForm t
      (∑ i ∈ s, A i) (∑ i ∈ s, D i) (∑ i ∈ s, J i) := by
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s ha ih =>
      by_cases hs' : s.Nonempty
      · have hAsum : 0 < ∑ i ∈ s, A i :=
          Finset.sum_pos (fun i hi => hA i (Finset.mem_insert_of_mem hi)) hs'
        rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
        exact fifthRootCurvatureJetForm_add_nonneg
          (hA a (Finset.mem_insert_self a s)) hAsum
          (hC a (Finset.mem_insert_self a s))
          (ih hs'
            (fun i hi => hA i (Finset.mem_insert_of_mem hi))
            (fun i hi => hC i (Finset.mem_insert_of_mem hi)))
      · rw [Finset.not_nonempty_iff_eq_empty.mp hs']
        simpa using hC a (Finset.mem_insert_self a s)

end

end HilbertMetric
