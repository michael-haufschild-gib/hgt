import GaloisForLFunctions.HTGeometry.SubwindingChordComparison

/-!
# Commutators against a small operator

A commutator is unchanged by adding a scalar or a commuting term to either slot, and its
Hilbert--Schmidt energy is at most `(2c)²` times the energy of the other slot when the first slot
moves every vector by at most `c`.  The factor `2` comes from the two products, and the estimate
`‖A - B‖² ≤ 2‖A‖² + 2‖B‖²` supplies it without a Minkowski inequality.

This is the step that converts an operator-norm approximation of a unitary into a Hilbert--Schmidt
bound on the commutator with any Hermitian candidate logarithm.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

section OperatorBound

open _root_.Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The energy of a difference is at most twice the sum of the energies. -/
theorem hsSqRe_sub_le (A B : Matrix n n ℂ) :
    hsSqRe (A - B) ≤ 2 * hsSqRe A + 2 * hsSqRe B := by
  rw [hsSqRe_eq_sum, hsSqRe_eq_sum, hsSqRe_eq_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [Matrix.sub_apply]
  have htri : ‖A b a - B b a‖ ≤ ‖A b a‖ + ‖B b a‖ := norm_sub_le _ _
  have hAB : (0 : ℝ) ≤ ‖A b a - B b a‖ := norm_nonneg _
  have hsq : ‖A b a - B b a‖ ^ (2 : ℕ) ≤ (‖A b a‖ + ‖B b a‖) ^ (2 : ℕ) := by nlinarith [htri, hAB]
  nlinarith [hsq, sq_nonneg (‖A b a‖ - ‖B b a‖)]

omit [DecidableEq n] in
/-- Hilbert--Schmidt energy is invariant under the conjugate transpose. -/
theorem hsSqRe_conjTranspose (A : Matrix n n ℂ) : hsSqRe Aᴴ = hsSqRe A := by
  rw [hsSqRe_eq_sum, hsSqRe_eq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.norm_conj]

omit [DecidableEq n] in
/-- Right multiplication is bounded by the operator norm of the adjoint. -/
theorem hsSqRe_mul_right_le (A E : Matrix n n ℂ) {c : ℝ}
    (hE : ∀ v : n → ℂ, ∑ l, ‖(Eᴴ *ᵥ v) l‖ ^ (2 : ℕ) ≤ c ^ (2 : ℕ) * ∑ l, ‖v l‖ ^ (2 : ℕ)) :
    hsSqRe (A * E) ≤ c ^ (2 : ℕ) * hsSqRe A := by
  have hconj : hsSqRe (A * E) = hsSqRe (Eᴴ * Aᴴ) := by
    rw [← Matrix.conjTranspose_mul, hsSqRe_conjTranspose]
  rw [hconj]
  have h := hsSqRe_mul_left_le Eᴴ Aᴴ hE
  rwa [hsSqRe_conjTranspose] at h

omit [DecidableEq n] in
/-- **The commutator bound.**  A slot that moves every vector by at most `c`, in either the operator
or the adjoint direction, makes the commutator energy at most `(2c)²` times the other slot's. -/
theorem hsSqRe_commutator_le_of_opBound (E A : Matrix n n ℂ) {c : ℝ}
    (hE : ∀ v : n → ℂ, ∑ l, ‖(E *ᵥ v) l‖ ^ (2 : ℕ) ≤ c ^ (2 : ℕ) * ∑ l, ‖v l‖ ^ (2 : ℕ))
    (hEH : ∀ v : n → ℂ, ∑ l, ‖(Eᴴ *ᵥ v) l‖ ^ (2 : ℕ) ≤ c ^ (2 : ℕ) * ∑ l, ‖v l‖ ^ (2 : ℕ)) :
    hsSqRe (E * A - A * E) ≤ (2 * c) ^ (2 : ℕ) * hsSqRe A := by
  have h1 := hsSqRe_mul_left_le E A hE
  have h2 := hsSqRe_mul_right_le A E hEH
  have h3 := hsSqRe_sub_le (E * A) (A * E)
  nlinarith [h1, h2, h3]

/-! ## Commutators ignore scalars and commuting terms -/

/-- A commutator is unchanged by subtracting a scalar from the second slot. -/
theorem commutator_sub_smul_one (X Y : Matrix n n ℂ) (c : ℂ) :
    X * (Y - c • (1 : Matrix n n ℂ)) - (Y - c • (1 : Matrix n n ℂ)) * X
      = X * Y - Y * X := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul]
  abel

omit [DecidableEq n] in
/-- A commutator is unchanged by adding a term that commutes with the first slot. -/
theorem commutator_add_commuting (X Y Z : Matrix n n ℂ) (h : X * Z = Z * X) :
    X * (Y + Z) - (Y + Z) * X = X * Y - Y * X := by
  rw [Matrix.mul_add, Matrix.add_mul, h]
  abel

omit [DecidableEq n] in
/-- A commutator with a commuting factor removed from the first slot. -/
theorem commutator_sub_commuting (X Y Z : Matrix n n ℂ) (h : Z * Y = Y * Z) :
    (X - Z) * Y - Y * (X - Z) = X * Y - Y * X := by
  rw [Matrix.sub_mul, Matrix.mul_sub, h]
  abel

end OperatorBound

/-! ## The assembled estimates -/

section Assembly

open _root_.Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- **Theorem D, `(30)`.**  A commutator gap against the orbit, a commutator rewrite, and an
operator-norm approximation combine to force the transverse part of a candidate logarithm below
`(2ε/α)` times its distance to the scalars. -/
theorem transverse_le_of_gap_and_approx (U A E K : Matrix n n ℂ) {α ε : ℝ} (hα : 0 < α)
    (hgap : α ^ (2 : ℕ) * hsSqRe A ≤ hsSqRe (U * A - A * U))
    (hrewrite : U * A - A * U = E * K - K * E)
    (hE : ∀ v : n → ℂ, ∑ l, ‖(E *ᵥ v) l‖ ^ (2 : ℕ) ≤ ε ^ (2 : ℕ) * ∑ l, ‖v l‖ ^ (2 : ℕ))
    (hEH : ∀ v : n → ℂ, ∑ l, ‖(Eᴴ *ᵥ v) l‖ ^ (2 : ℕ) ≤ ε ^ (2 : ℕ) * ∑ l, ‖v l‖ ^ (2 : ℕ)) :
    hsSqRe A ≤ (2 * ε / α) ^ (2 : ℕ) * hsSqRe K := by
  have hbound := hsSqRe_commutator_le_of_opBound E K hE hEH
  rw [hrewrite] at hgap
  have hchain : α ^ (2 : ℕ) * hsSqRe A ≤ (2 * ε) ^ (2 : ℕ) * hsSqRe K := le_trans hgap hbound
  have hα2 : 0 < α ^ (2 : ℕ) := by positivity
  rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ hα2]
  nlinarith [hchain]

omit [DecidableEq n] in
/-- **Theorem C.1's assembled estimate.**  A tangent gap, a chord comparison and an operator-norm
approximation combine into a distance bound with the constant of the card. -/
theorem subwinding_transverse_le (H K V E : Matrix n n ℂ) {γ C ε : ℝ} (hγ : 0 < γ)
    (hgap : γ ^ (2 : ℕ) * hsSqRe K ≤ hsSqRe (H * K - K * H))
    (hcomp : hsSqRe (H * K - K * H) ≤ C ^ (2 : ℕ) * hsSqRe (H * V - V * H))
    (hrewrite : H * V - V * H = E * H - H * E)
    (hE : ∀ v : n → ℂ, ∑ l, ‖(E *ᵥ v) l‖ ^ (2 : ℕ) ≤ ε ^ (2 : ℕ) * ∑ l, ‖v l‖ ^ (2 : ℕ))
    (hEH : ∀ v : n → ℂ, ∑ l, ‖(Eᴴ *ᵥ v) l‖ ^ (2 : ℕ) ≤ ε ^ (2 : ℕ) * ∑ l, ‖v l‖ ^ (2 : ℕ)) :
    hsSqRe K ≤ (C * (2 * ε) / γ) ^ (2 : ℕ) * hsSqRe H := by
  have hbound := hsSqRe_commutator_le_of_opBound E H hE hEH
  rw [hrewrite] at hcomp
  have hchain : γ ^ (2 : ℕ) * hsSqRe K ≤ C ^ (2 : ℕ) * ((2 * ε) ^ (2 : ℕ) * hsSqRe H) := by
    refine le_trans hgap (le_trans hcomp ?_)
    have hC2 : (0 : ℝ) ≤ C ^ (2 : ℕ) := sq_nonneg C
    exact mul_le_mul_of_nonneg_left hbound hC2
  have hγ2 : 0 < γ ^ (2 : ℕ) := by positivity
  rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ hγ2]
  nlinarith [hchain]

end Assembly


end GaloisForLFunctions.HTGeometry
