import GaloisForLFunctions.HTGeometry.ConstitutiveInvariantPositivityKMSWall

/-!
# The KMS exchange identity across many commuting modes

The exchange identity `φ(ab) = φ(b σ(a))` — the algebraic form of the KMS boundary condition at
imaginary time — determines a normalised functional on the monomials of a family of commuting
isometries.  Two steps do it: a monomial carrying a nonzero net charge in one mode is killed
outright, and a diagonal block `V^n (V^*)^n` can be peeled off at the cost of the factor `qⁿ`.
-/

namespace GaloisForLFunctions.HTGeometry

section KMSMultiMode

variable {A : Type*} [Ring A] [Algebra ℂ A]
variable (φ : A →ₗ[ℂ] ℂ) (σ : A →ₐ[ℂ] A)

/-- **Off-diagonal vanishing.**  A monomial carrying a nonzero net charge in one mode is annihilated
by every functional satisfying the exchange identity: the exchange multiplies it by the mode's
weight, and the weight is not one. -/
theorem kms_eq_zero_of_commuting
    (hexch : ∀ a b : A, φ (a * b) = φ (b * σ a))
    {v a : A} {q : ℂ} (hσ : σ v = q • v) (hq : q ≠ 1) (hcomm : v * a = a * v) :
    φ (v * a) = 0 := by
  have h0 := hexch v a
  rw [hσ, mul_smul_comm, map_smul, smul_eq_mul, ← hcomm] at h0
  have h2 : (1 - q) * φ (v * a) = 0 := by
    rw [sub_mul, one_mul]
    exact sub_eq_zero.mpr h0
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hq
  · exact h

/-- The same for a power of the isometry. -/
theorem kms_pow_eq_zero_of_commuting
    (hexch : ∀ a b : A, φ (a * b) = φ (b * σ a))
    {v a : A} {q : ℂ} {n : ℕ} (hσ : σ v = q • v) (hq : q ^ n ≠ 1)
    (hcomm : v ^ n * a = a * v ^ n) :
    φ (v ^ n * a) = 0 :=
  kms_eq_zero_of_commuting φ σ hexch (alg_map_pow_smul σ hσ n) hq hcomm

/-- **Peeling one diagonal block.**  If the remaining word commutes with the mode's isometry, the
block `V^n (V^*)^n` contributes exactly the factor `qⁿ`. -/
theorem kms_diagonal_step
    (hexch : ∀ a b : A, φ (a * b) = φ (b * σ a))
    {v w a : A} {q : ℂ} {n : ℕ} (hσ : σ v = q • v) (hiso : w * v = 1)
    (hva : v ^ n * a = a * v ^ n) :
    φ (v ^ n * w ^ n * a) = q ^ n * φ a := by
  have h := hexch (v ^ n) (w ^ n * a)
  rw [alg_map_pow_smul σ hσ n, mul_smul_comm, map_smul, smul_eq_mul] at h
  have hreduce : w ^ n * a * v ^ n = a := by
    calc w ^ n * a * v ^ n = w ^ n * (a * v ^ n) := by rw [mul_assoc]
      _ = w ^ n * (v ^ n * a) := by rw [hva]
      _ = w ^ n * v ^ n * a := by rw [mul_assoc]
      _ = a := by rw [isometry_pow hiso n, one_mul]
  rw [hreduce, ← mul_assoc] at h
  exact h

end KMSMultiMode

end GaloisForLFunctions.HTGeometry
