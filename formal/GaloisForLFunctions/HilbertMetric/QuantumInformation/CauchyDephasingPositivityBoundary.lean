import GaloisForLFunctions.HilbertMetric.QuantumInformation.CauchyDephasing
import GaloisForLFunctions.HilbertMetric.QuantumInformation.JordanPositivityBoundary

/-!
# Information preservation and loss of positivity reflection

The Cauchy channel is injective at every finite step. Nevertheless, it
maps an explicit nonpositive Jordan matrix to a positive Gram whenever
its rates differ. Thus positivity reflection has exactly the constant-rate
boundary, while entrywise information remains recoverable.
-/

noncomputable section
open Matrix
open scoped ComplexOrder ComplexConjugate
namespace GaloisForLFunctions.HilbertMetric.CauchyDephasing
open CauchyJordan

/-- A one-row Gram factor made from the square-root rates. -/
def rateRow {n : ℕ} (r : Fin n → ℝ) : Matrix (Fin 1) (Fin n) ℂ :=
  fun _ i => (Real.exp (r i / 2) : ℂ)

/-- Dephasing turns the forward Jordan test matrix into an explicit positive Gram. -/
theorem channel_jordanSymbol_eq_gram {n : ℕ} (r : Fin n → ℝ) :
    channel r (jordanSymbol r) = (rateRow r)ᴴ * rateRow r := by
  rw [channel_eq_inverseJordan, jordanSymbol, inverseJordan_jordan]
  ext i j
  rw [rateDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, rateRow, Fin.sum_univ_one]
  change (Real.exp (r i / 2) : ℂ) * 1 * (Real.exp (r j / 2) : ℂ) =
    conj (Real.exp (r i / 2) : ℂ) * (Real.exp (r j / 2) : ℂ)
  rw [Complex.conj_ofReal, mul_one]

theorem channel_jordanSymbol_posSemidef {n : ℕ} (r : Fin n → ℝ) :
    (channel r (jordanSymbol r)).PosSemidef := by
  rw [channel_jordanSymbol_eq_gram]
  exact posSemidef_conjTranspose_mul_self _

/-- Positive output from a nonpositive input occurs exactly when the rates are not all equal. -/
theorem channel_has_nonpositive_preimage_iff {n : ℕ} (r : Fin n → ℝ) :
    (∃ A : Matrix (Fin n) (Fin n) ℂ, ¬ A.PosSemidef ∧ (channel r A).PosSemidef) ↔
      ¬ ∀ i j, r i = r j := by
  constructor
  · rintro ⟨A, hbad, hgood⟩ heq
    have hc : channel r A = A := by
      ext i j
      change (coherence (r i) (r j) : ℂ) * A i j = A i j
      rw [heq i j, coherence_self, Complex.ofReal_one, one_mul]
    rw [hc] at hgood
    exact hbad hgood
  · intro h
    exact ⟨jordanSymbol r,
      fun hp => h ((jordanSymbol_posSemidef_iff r).mp hp), channel_jordanSymbol_posSemidef r⟩

/-- Exact recovery from one finite dephasing step. -/
def recoverChannel {n : ℕ} (r : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => A i j / (coherence (r i) (r j) : ℂ)

theorem recoverChannel_channel {n : ℕ} (r : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) : recoverChannel r (channel r A) = A := by
  ext i j
  have hq : (coherence (r i) (r j) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (coherence_pos _ _).ne'
  simp only [recoverChannel, channel]
  field_simp [hq]

theorem channel_recoverChannel {n : ℕ} (r : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) : channel r (recoverChannel r A) = A := by
  ext i j
  have hq : (coherence (r i) (r j) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (coherence_pos _ _).ne'
  simp only [recoverChannel, channel]
  field_simp [hq]

/-- Finite dephasing retains every matrix entry despite failing to reflect positivity. -/
theorem channel_injective {n : ℕ} (r : Fin n → ℝ) : Function.Injective (channel r) := by
  intro A B h
  have hr := congrArg (recoverChannel r) h
  simpa only [recoverChannel_channel] using hr

#print axioms channel_jordanSymbol_eq_gram
#print axioms channel_has_nonpositive_preimage_iff
#print axioms recoverChannel_channel
#print axioms channel_recoverChannel
#print axioms channel_injective
end GaloisForLFunctions.HilbertMetric.CauchyDephasing
