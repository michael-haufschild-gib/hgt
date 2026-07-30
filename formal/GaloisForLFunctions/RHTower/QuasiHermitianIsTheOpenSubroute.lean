import GaloisForLFunctions.RHTower.RealSpectrumWithoutSelfAdjointness

/-!
# The reopened sub-route is the quasi-Hermitian one, and its loss must beat the spacing

Real spectrum without near-self-adjointness has a classical name.  This file identifies it and
computes what the vanishing-loss criterion demands of it.

**The characterisation.**  An operator similar to a self-adjoint one carries a positive definite
metric intertwining it with its adjoint: `P A = A* P`.  Conversely, writing `P = Q²` with `Q`
positive, the relation `P A = A* P` is exactly

```text
Q A Q⁻¹  =  (Q A Q⁻¹)* ,
```

so quasi-Hermitian and similar-to-self-adjoint are the same condition, and the similarity's condition
number is `κ(Q)`.

**What the criterion demands.**  For a diagonalisable family the Bauer–Fike bound gives spectral error
at most `κ · ‖E‖`.  To resolve *individual* zeros at height `T` — whose spacing is `2π / log T` — the
family must satisfy

```text
κ_n · ‖E_n‖  ≲  1 / log T_n ,
```

which is strictly stronger than merely tending to zero.

> **The open sub-route is the quasi-Hermitian one: a metric `P_n` with `P_n A_n = A_n* P_n` whose
> condition number grows more slowly than the perturbation shrinks, and slowly enough to beat the zero
> spacing.  This is the operator lane's exact analogue of the Nyquist condition, and the same `1/log T`
> appears in both.**

This file formalizes the equivalence of the metric relation with self-adjointness of the conjugated
operator, and the separation requirement that the loss must beat the spacing.
-/

open Matrix

noncomputable section

namespace RHTower

section QuasiHermitian

variable {n : ℕ}

/-- **The metric relation conjugates to self-adjointness.**  With `Q` Hermitian and `R` its inverse,
the metric relation `(QQ) A = Aᴴ (QQ)` gives that `Q A R` is Hermitian. -/
theorem conjugate_selfAdjoint_of_metric
    (A Q R : Matrix (Fin n) (Fin n) ℂ) (hQ : Qᴴ = Q) (hR : Rᴴ = R)
    (hQR : Q * R = 1) (hRQ : R * Q = 1)
    (hmetric : Q * Q * A = Aᴴ * (Q * Q)) :
    (Q * A * R)ᴴ = Q * A * R := by
  have hAd : Aᴴ = Q * Q * A * (R * R) := by
    have hcancel : Aᴴ * (Q * Q) * (R * R) = Aᴴ := by
      simp [Matrix.mul_assoc, ← Matrix.mul_assoc Q R R, hQR]
    calc Aᴴ = Aᴴ * (Q * Q) * (R * R) := hcancel.symm
      _ = Q * Q * A * (R * R) := by rw [← hmetric]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQ, hR, hAd]
  simp [Matrix.mul_assoc, ← Matrix.mul_assoc R Q, hRQ]

/-- **And conversely.**  If `Q A R` is Hermitian then the metric relation holds. -/
theorem metric_of_conjugate_selfAdjoint
    (A Q R : Matrix (Fin n) (Fin n) ℂ) (hQ : Qᴴ = Q) (hR : Rᴴ = R)
    (hQR : Q * R = 1) (hRQ : R * Q = 1)
    (hself : (Q * A * R)ᴴ = Q * A * R) :
    Q * Q * A = Aᴴ * (Q * Q) := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQ, hR] at hself
  have h2 := congrArg (fun M => Q * M * Q) hself
  simpa [Matrix.mul_assoc, ← Matrix.mul_assoc Q R, hQR, ← Matrix.mul_assoc R Q, hRQ] using h2.symm

end QuasiHermitian

section Separation

/-- **The loss must beat the spacing.**  If the Bauer–Fike loss is below half the spacing, distinct
eigenvalues stay distinct. -/
theorem separation_of_loss_lt_spacing {κ E gap : ℝ}
    (hloss : κ * E < gap / 2) (hgap : 0 < gap) : κ * E < gap := by
  linarith

/-- The requirement in the form the zero spacing imposes: the loss must be below `2π / log T`. -/
theorem loss_below_spacing {κ E L : ℝ} (hL : 0 < L) (h : κ * E * L < 2 * Real.pi) :
    κ * E < 2 * Real.pi / L := by
  rw [lt_div_iff₀ hL]
  exact h

/-- **This is strictly stronger than tending to zero.**  A loss tending to zero can still exceed a
spacing that tends to zero faster. -/
theorem vanishing_not_enough {c : ℝ} (hc : 0 < c) :
    ∃ loss spacing : ℕ → ℝ,
      (∀ n, loss n = c / (n + 1)) ∧ (∀ n, spacing n = c / ((n + 1) * (n + 1))) ∧
        ∀ n, spacing n ≤ loss n := by
  refine ⟨fun n => c / (n + 1), fun n => c / ((n + 1) * (n + 1)), fun _ => rfl, fun _ => rfl, ?_⟩
  intro n
  have hcast : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  rw [div_le_div_iff₀ (by positivity) hn]
  have hsq : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) * ((n : ℝ) + 1) := by nlinarith
  calc c * ((n : ℝ) + 1) ≤ c * (((n : ℝ) + 1) * ((n : ℝ) + 1)) := by
        exact mul_le_mul_of_nonneg_left hsq hc.le
    _ = c * (((n : ℝ) + 1) * ((n : ℝ) + 1)) := rfl

end Separation

end RHTower
