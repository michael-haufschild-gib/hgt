import GaloisForLFunctions.HTGeometry.FiniteResponseForce

/-!
# Finite AIR response and macroscopic drift

The attraction–indifference–repulsion law and odd-force cancellation from
Araújo, arXiv:2609.05560, equations (7) and section 4.4. The cancellation is valid for
arbitrary signed finite source weights and arbitrary threshold parameters.
-/
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Attraction, indifference, and repulsion with the paper's exact endpoint conventions. -/
def airResponse (epsilon₁ epsilon₂ eta u : ℝ) : ℝ :=
  if |u| < epsilon₁ then u else if |u| < epsilon₂ then 0 else -eta * u

theorem airResponse_neg (epsilon₁ epsilon₂ eta u : ℝ) :
    airResponse epsilon₁ epsilon₂ eta (-u) = -airResponse epsilon₁ epsilon₂ eta u := by
  unfold airResponse
  rw [abs_neg]
  split_ifs <;> ring

theorem airResponse_zero (epsilon₁ epsilon₂ eta : ℝ) : airResponse epsilon₁ epsilon₂ eta 0 = 0 := by
  unfold airResponse
  split_ifs <;> ring

/-- Internal AIR pair forces cannot translate a finite source packet. -/
theorem airResponse_total_internal_force_zero {ι : Type*} [Fintype ι]
    (epsilon₁ epsilon₂ eta : ℝ) (w z : ι → ℝ) :
    ∑ i, w i * finiteResponseForce (airResponse epsilon₁ epsilon₂ eta) w z (z i) = 0 := by
  let S := ∑ i, ∑ j, w i * w j * airResponse epsilon₁ epsilon₂ eta (z j - z i)
  have hs : S = -S := by
    calc
      S = ∑ i, ∑ j, w j * w i * airResponse epsilon₁ epsilon₂ eta (z i - z j) :=
        Finset.sum_comm
      _ = ∑ i, ∑ j, -(w i * w j * airResponse epsilon₁ epsilon₂ eta (z j - z i)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [show z i - z j = -(z j - z i) by ring, airResponse_neg]
        ring
      _ = -S := by simp only [Finset.sum_neg_distrib, S]
  have hz : S = 0 := by linarith
  simpa only [S, finiteResponseForce, Finset.mul_sum, mul_assoc] using hz

/-- The weighted mean velocity is exactly the represented-versus-direct force discrepancy. -/
theorem airResponse_weighted_mean_drift {ι κ : Type*} [Fintype ι] [Fintype κ]
    (epsilon₁ epsilon₂ eta lam : ℝ) (w z : ι → ℝ) (v t : κ → ℝ) :
    (∑ i, w i * ((1 - lam) * finiteResponseForce (airResponse epsilon₁ epsilon₂ eta) w z (z i) +
      lam * finiteResponseForce (airResponse epsilon₁ epsilon₂ eta) v t (z i))) =
        lam * ∑ i, w i *
          (finiteResponseForce (airResponse epsilon₁ epsilon₂ eta) v t (z i) -
            finiteResponseForce (airResponse epsilon₁ epsilon₂ eta) w z (z i)) := by
  have hz := airResponse_total_internal_force_zero epsilon₁ epsilon₂ eta w z
  have h (i : ι) : w i * ((1 - lam) *
      finiteResponseForce (airResponse epsilon₁ epsilon₂ eta) w z (z i) +
        lam * finiteResponseForce (airResponse epsilon₁ epsilon₂ eta) v t (z i)) =
      (1 - lam) * (w i * finiteResponseForce (airResponse epsilon₁ epsilon₂ eta) w z (z i)) +
        lam * (w i * finiteResponseForce (airResponse epsilon₁ epsilon₂ eta) v t (z i)) := by ring
  simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
  rw [hz]
  ring

/-- Force distortion bounds the macroscopic drift for arbitrary signed source weights. -/
theorem airResponse_weighted_mean_drift_bound {κ : Type*} [Fintype κ] {n : ℕ}
    (epsilon₁ epsilon₂ eta lam : ℝ) (w z : Fin (n + 1) → ℝ) (v t : κ → ℝ) :
    |∑ i, w i * ((1 - lam) * finiteResponseForce (airResponse epsilon₁ epsilon₂ eta) w z (z i) +
      lam * finiteResponseForce (airResponse epsilon₁ epsilon₂ eta) v t (z i))| ≤
        |lam| * (∑ i, |w i|) * finiteResponseDistortion (airResponse epsilon₁ epsilon₂ eta) w z v t z := by
  rw [airResponse_weighted_mean_drift, abs_mul, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg lam)
  calc
    _ ≤ ∑ i, |w i * (finiteResponseForce (airResponse epsilon₁ epsilon₂ eta) v t (z i) -
      finiteResponseForce (airResponse epsilon₁ epsilon₂ eta) w z (z i))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |w i| * finiteResponseDistortion (airResponse epsilon₁ epsilon₂ eta) w z v t z := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg (w i))
      exact norm_le_pi_norm
        (fun j => finiteResponseForce (airResponse epsilon₁ epsilon₂ eta) v t (z j) -
          finiteResponseForce (airResponse epsilon₁ epsilon₂ eta) w z (z j)) i
    _ = _ := (Finset.sum_mul ..).symm

end
end GaloisForLFunctions.HTGeometry
