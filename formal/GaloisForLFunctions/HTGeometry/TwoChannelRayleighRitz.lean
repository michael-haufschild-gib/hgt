import GaloisForLFunctions.HTGeometry.TwoChannelRobertson

/-!
# Two-channel Rayleigh--Ritz adjugate witness

For a positive-definite two-channel overlap/energy matrix, the optimal
response direction is obtained without division by applying the adjugate
matrix to the response vector.  This is the two-dimensional algebraic core of
the nonorthogonal-basis Rayleigh--Ritz generalized eigenvalue method.
-/

namespace HTGeometry

/-- Quotient-free two-channel Rayleigh--Ritz optimization.  The displayed
adjugate witness has energy `det * response` and coupling `response`, so one
matrix inequality supplies a positive variational witness. -/
theorem exists_positive_twoChannelRayleighWitness_of_adjugate
    (A B D c₁ c₂ κ L : ℝ)
    (hdet : 0 < A * D - B ^ (2 : ℕ))
    (hresponse : 0 < D * c₁ ^ (2 : ℕ) - 2 * B * c₁ * c₂ + A * c₂ ^ (2 : ℕ))
    (hcert : κ * (A * D - B ^ (2 : ℕ)) ≤
      L * (D * c₁ ^ (2 : ℕ) - 2 * B * c₁ * c₂ + A * c₂ ^ (2 : ℕ))) :
    ∃ a b : ℝ,
      0 < A * a ^ (2 : ℕ) + 2 * B * a * b + D * b ^ (2 : ℕ) ∧
      κ * (A * a ^ (2 : ℕ) + 2 * B * a * b + D * b ^ (2 : ℕ)) ≤
        L * (a * c₁ + b * c₂) ^ (2 : ℕ) := by
  let a := D * c₁ - B * c₂
  let b := A * c₂ - B * c₁
  let Δ := A * D - B ^ (2 : ℕ)
  let Q := D * c₁ ^ (2 : ℕ) - 2 * B * c₁ * c₂ + A * c₂ ^ (2 : ℕ)
  have hcoupling : a * c₁ + b * c₂ = Q := by
    dsimp [a, b, Q]
    ring
  have henergy : A * a ^ (2 : ℕ) + 2 * B * a * b + D * b ^ (2 : ℕ) = Δ * Q := by
    dsimp [a, b, Δ, Q]
    ring
  have hΔ : 0 < Δ := by simpa only [Δ] using hdet
  have hQ : 0 < Q := by simpa only [Q] using hresponse
  have hcert' : κ * Δ ≤ L * Q := by simpa only [Δ, Q] using hcert
  refine ⟨a, b, ?_, ?_⟩
  · rw [henergy]
    exact mul_pos hΔ hQ
  · rw [henergy, hcoupling]
    nlinarith

/-- Reverse two-channel Rayleigh bound.  The determinant identity is the
two-dimensional generalized Cauchy--Schwarz relation, so any positive-energy
witness forces the corresponding matrix certificate. -/
theorem twoChannelRayleighMatrixCertificate_of_positiveWitness
    (A B D c₁ c₂ κ L a b : ℝ)
    (hdet : 0 < A * D - B ^ (2 : ℕ))
    (hL : 0 ≤ L)
    (henergy : 0 < A * a ^ (2 : ℕ) + 2 * B * a * b + D * b ^ (2 : ℕ))
    (hcert : κ * (A * a ^ (2 : ℕ) + 2 * B * a * b + D * b ^ (2 : ℕ)) ≤
      L * (a * c₁ + b * c₂) ^ (2 : ℕ)) :
    κ * (A * D - B ^ (2 : ℕ)) ≤
      L * (D * c₁ ^ (2 : ℕ) - 2 * B * c₁ * c₂ + A * c₂ ^ (2 : ℕ)) := by
  let Δ := A * D - B ^ (2 : ℕ)
  let E := A * a ^ (2 : ℕ) + 2 * B * a * b + D * b ^ (2 : ℕ)
  let C := a * c₁ + b * c₂
  let Q := D * c₁ ^ (2 : ℕ) - 2 * B * c₁ * c₂ + A * c₂ ^ (2 : ℕ)
  let R := (B * a + D * b) * c₁ - (A * a + B * b) * c₂
  have hidentity : Δ * C ^ (2 : ℕ) + R ^ (2 : ℕ) = E * Q := by
    dsimp [Δ, E, C, Q, R]
    ring
  have hΔ : 0 ≤ Δ := le_of_lt (by simpa only [Δ] using hdet)
  have hE : 0 < E := by simpa only [E] using henergy
  have hcert' : κ * E ≤ L * C ^ (2 : ℕ) := by simpa only [E, C] using hcert
  have hcs : Δ * C ^ (2 : ℕ) ≤ E * Q := by
    nlinarith [sq_nonneg R]
  have hscaleDet : Δ * (κ * E) ≤ Δ * (L * C ^ (2 : ℕ)) :=
    mul_le_mul_of_nonneg_left hcert' hΔ
  have hscaleL : L * (Δ * C ^ (2 : ℕ)) ≤ L * (E * Q) :=
    mul_le_mul_of_nonneg_left hcs hL
  have hcombined : E * (κ * Δ) ≤ E * (L * Q) := by
    calc
      E * (κ * Δ) = Δ * (κ * E) := by ring
      _ ≤ Δ * (L * C ^ (2 : ℕ)) := hscaleDet
      _ = L * (Δ * C ^ (2 : ℕ)) := by ring
      _ ≤ L * (E * Q) := hscaleL
      _ = E * (L * Q) := by ring
  have hmatrix : κ * Δ ≤ L * Q :=
    (mul_le_mul_iff_of_pos_left hE).mp hcombined
  simpa only [Δ, Q] using hmatrix

end HTGeometry
