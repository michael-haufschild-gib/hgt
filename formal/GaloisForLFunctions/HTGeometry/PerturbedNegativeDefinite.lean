import GaloisForLFunctions.HTGeometry.AtomMassLimitHerglotz

/-!
# Negative definiteness survives a small perturbation

The lower bound on the Krein index compares a scaled Gram matrix with its limit, a negative
diagonal.  Rather than argue by compactness of a unit sphere, it is enough to compare the two
quadratic forms with a common quadratic modulus: a form bounded above by `-δ‖x‖²` stays negative
under any perturbation bounded by `ε‖x‖²` with `ε < δ`.

The estimate is uniform in the vector, so it converts a limit statement about the forms into a
negative definiteness statement holding eventually.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Negative definiteness under a dominated perturbation.**  A quadratic form bounded above by
`-δ‖x‖²` remains strictly negative on nonzero vectors after a perturbation bounded by `ε‖x‖²` with
`ε < δ`. -/
theorem neg_of_perturbed_negDef {E : Type*} [NormedAddCommGroup E]
    (Q Q₀ : E → ℝ) {δ ε : ℝ} (hε : ε < δ)
    (h₀ : ∀ x, Q₀ x ≤ -δ * ‖x‖ ^ (2 : ℕ))
    (hpert : ∀ x, |Q x - Q₀ x| ≤ ε * ‖x‖ ^ (2 : ℕ)) :
    ∀ x : E, x ≠ 0 → Q x < 0 := by
  intro x hx
  have hnorm : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hsq : 0 < ‖x‖ ^ (2 : ℕ) := by positivity
  have hupper : Q x ≤ Q₀ x + ε * ‖x‖ ^ (2 : ℕ) := by
    have := (abs_le.1 (hpert x)).2
    linarith
  have hchain : Q x ≤ (-δ + ε) * ‖x‖ ^ (2 : ℕ) := by
    have := h₀ x
    nlinarith [hupper, this]
  have hneg : (-δ + ε) < 0 := by linarith
  nlinarith [hchain, hsq, hneg]

/-- **Eventual negative definiteness from a limit.**  If the forms converge with a uniform quadratic
modulus and the limiting form is negative definite with margin `δ`, then every form beyond the
threshold is negative definite. -/
theorem eventually_neg_of_tendsto_negDef {E : Type*} [NormedAddCommGroup E]
    {ι : Type*} {l : Filter ι} (Q : ι → E → ℝ) (Q₀ : E → ℝ) {δ : ℝ}
    (h₀ : ∀ x, Q₀ x ≤ -δ * ‖x‖ ^ (2 : ℕ))
    (hmod : ∀ᶠ i in l, ∀ x, |Q i x - Q₀ x| ≤ (δ / 2) * ‖x‖ ^ (2 : ℕ))
    (hδ : 0 < δ) :
    ∀ᶠ i in l, ∀ x : E, x ≠ 0 → Q i x < 0 := by
  filter_upwards [hmod] with i hi
  refine neg_of_perturbed_negDef (Q i) Q₀ ?_ h₀ hi
  linarith

/-- The negative diagonal form has the margin required above. -/
theorem negDiagonal_le {n : ℕ} (c : Fin n → ℝ) {δ : ℝ} (hδ : ∀ j, c j ≤ -δ)
    (x : Fin n → ℝ) :
    ∑ j, c j * (x j) ^ (2 : ℕ) ≤ -δ * ∑ j, (x j) ^ (2 : ℕ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hsq : 0 ≤ (x j) ^ (2 : ℕ) := sq_nonneg _
  exact mul_le_mul_of_nonneg_right (hδ j) hsq

end

end GaloisForLFunctions.HTGeometry
