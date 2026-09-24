import GaloisForLFunctions.HTGeometry.Zeta5AndreiefTransfer

/-!
# Even Hankel moments as squared alternants

This applies Andréief's identity to the even-moment matrices used in the
corpus's rank-two and rank-three Hankel arguments. Restriction to `[0,1]`
makes every moment integrable without a theorem hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- Every finite even-moment Hankel determinant on the unit interval is an
integral of a squared alternant. -/
theorem zeta5_unitInterval_evenHankel_det (n : ℕ) :
    (Matrix.of fun i j : Fin n =>
      ∫ x in Set.Icc (0 : ℝ) 1, x ^ (2 * (i : ℕ) + 2 * (j : ℕ))).det =
        1 / (n.factorial : ℝ) *
          ∫ x : Fin n → ℝ,
            (Matrix.of fun (a b : Fin n) => (x b) ^ (2 * (a : ℕ))).det ^ 2
              ∂(Measure.pi fun _ => volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  have hint : ∀ i j : Fin n,
      Integrable (fun x : ℝ => x ^ (2 * (i : ℕ)) * x ^ (2 * (j : ℕ))) μ := by
    intro i j
    have h : Integrable (fun x : ℝ => x ^ (2 * (i : ℕ) + 2 * (j : ℕ))) μ := by
      exact (continuous_id.pow _).continuousOn.integrableOn_Icc
    simpa only [pow_add] using h
  have h := zeta5_andreief μ
    (fun (i : Fin n) (x : ℝ) => x ^ (2 * (i : ℕ)))
    (fun (i : Fin n) (x : ℝ) => x ^ (2 * (i : ℕ))) hint
  simpa only [μ, ← pow_add, pow_two] using h

/-- Nonnegativity of every even-moment Hankel determinant on `[0,1]`. -/
theorem zeta5_unitInterval_evenHankel_det_nonneg (n : ℕ) :
    0 ≤ (Matrix.of fun i j : Fin n =>
      ∫ x in Set.Icc (0 : ℝ) 1, x ^ (2 * (i : ℕ) + 2 * (j : ℕ))).det := by
  rw [zeta5_unitInterval_evenHankel_det]
  exact mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _)

end

end GaloisForLFunctions.HTGeometry
