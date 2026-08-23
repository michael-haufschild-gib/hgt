import GaloisForLFunctions.RHTower.MobiusCoprimeSignatureFlow
import GaloisForLFunctions.RHTower.MobiusMertensLittlewood

namespace RHTower

noncomputable section

/-- The complex Mertens partial sum is the real Mertens function embedded in `ℂ`. -/
theorem mobiusMertensPartialSum_eq_sieveMertensM (N : ℕ) :
    mobiusMertensPartialSum N = (RHTower.Sieve.mertensM N : ℂ) := by
  rw [mobiusMertensPartialSum, RHTower.Sieve.mertensM]
  simp only [mobiusComplexCoefficient]
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  norm_num

/-- Norm of the Mertens partial sum is the absolute spectral signature. -/
theorem norm_mobiusMertensPartialSum_eq_abs_finiteMobiusCoprimeSignature (N : ℕ) :
    ‖mobiusMertensPartialSum N‖ = |((finiteMobiusCoprimeSignature N : ℤ) : ℝ)| := by
  rw [mobiusMertensPartialSum_eq_sieveMertensM,
    ← finiteMobiusCoprimeSignature_eq_mertensM]
  simp

/-- Every strict half-power bound for the coprimality-matrix signature. -/
def FiniteMobiusCoprimeSignatureAllStrictHalfPowerBound : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
    |((finiteMobiusCoprimeSignature N : ℤ) : ℝ)| ≤
      C * ((N : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ)

/-- Signature half-power growth is exactly the classical Mertens half-power bound. -/
theorem finiteMobiusCoprimeSignatureAllStrictHalfPowerBound_iff_mobiusMertens :
    FiniteMobiusCoprimeSignatureAllStrictHalfPowerBound ↔
      MobiusMertensAllStrictHalfPowerBound := by
  constructor
  · intro h δ hδ
    obtain ⟨C, hC, hbound⟩ := h δ hδ
    exact ⟨C, hC, fun N => by
      rw [norm_mobiusMertensPartialSum_eq_abs_finiteMobiusCoprimeSignature]
      exact hbound N⟩
  · intro h δ hδ
    obtain ⟨C, hC, hbound⟩ := h δ hδ
    exact ⟨C, hC, fun N => by
      rw [← norm_mobiusMertensPartialSum_eq_abs_finiteMobiusCoprimeSignature]
      exact hbound N⟩

/-- The exact spectral-signature form of Littlewood's criterion. -/
theorem finiteMobiusCoprimeSignatureAllStrictHalfPowerBound_iff_riemannHypothesis :
    FiniteMobiusCoprimeSignatureAllStrictHalfPowerBound ↔ RiemannHypothesis :=
  finiteMobiusCoprimeSignatureAllStrictHalfPowerBound_iff_mobiusMertens.trans
    mobiusMertensAllStrictHalfPowerBound_iff_riemannHypothesis

end

end RHTower
