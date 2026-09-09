import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinInstrument
import GaloisForLFunctions.HTGeometry.MarkovianReturnRecovery

/-!
# From finite Kraus data to the quantum dynamical semigroup framework

Infrastructure exposed by applying Schaffer–Exl, arXiv:2609.04530, to conditional
spin evolution. The corpus's normalized finite rectangular Kraus representation
and its separate completely-positive trace-preserving channel framework are linked
by a proved full ancilla-amplification identity. The bridge constructs every
required channel law from the existing Kraus completeness equation and preserves
the exact action of the explicitly constructed spin filter.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder Kronecker
open Matrix
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- Every raw finite Kraus sum has the expected full ancilla amplification. -/
theorem finiteKrausSum_amplify {d : ℕ} {κ : Type*} [Fintype κ]
    (K : κ → Matrix (Fin d) (Fin d) ℂ) (m : Type) [Fintype m] [DecidableEq m]
    (X : Matrix (Fin d × m) (Fin d × m) ℂ) :
    amplify (fun ρ => ∑ a, K a * ρ * (K a)ᴴ) m X =
      ∑ a, (K a ⊗ₖ (1 : Matrix m m ℂ)) * X * (K a ⊗ₖ (1 : Matrix m m ℂ))ᴴ := by
  calc
    _ = ∑ a, amplify (fun ρ => K a * ρ * star (K a)) m X := by
      ext i j
      simp [amplify, Matrix.star_eq_conjTranspose, Matrix.sum_apply]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      simpa only [Matrix.star_eq_conjTranspose] using amplify_conj (K a) X

/-- Structural bridge from the existing normalized Kraus representation to the existing
completely-positive trace-preserving channel type; no channel law is postulated. -/
def quantumChannelFromRectangularKraus {d : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Phi : FiniteRectangularKrausChannel d d κ) : QuantumChannel (Fin d) where
  map := Phi.evolveMatrix
  map_add := by
    intro X Y
    simp [FiniteRectangularKrausChannel.evolveMatrix, Matrix.mul_add, Matrix.add_mul,
      Finset.sum_add_distrib]
  map_smul := by
    intro c X
    simp only [FiniteRectangularKrausChannel.evolveMatrix, Matrix.mul_smul,
      Matrix.smul_mul, Finset.smul_sum]
  completelyPositive := by
    intro m _ _ X hX
    change (amplify (fun ρ => ∑ a, Phi.operator a * ρ * (Phi.operator a)ᴴ) m X).PosSemidef
    rw [finiteKrausSum_amplify]
    exact Matrix.posSemidef_sum Finset.univ (fun a _ =>
      hX.mul_mul_conjTranspose_same (Phi.operator a ⊗ₖ (1 : Matrix m m ℂ)))
  tracePreserving := by
    intro X
    have h := Phi.trace_evolve_mul X 1
    simpa only [Matrix.mul_one, FiniteRectangularKrausChannel.pullbackMatrix,
      Phi.completeness] using h

/-- The earlier conditional-spin instrument is now an actual channel in the semigroup framework. -/
def spinFilterQuantumChannel (k : ℂ) : QuantumChannel (Fin 2) :=
  quantumChannelFromRectangularKraus (spinFilterChannel k)

/-- The framework bridge preserves the literal matrix action of the constructed instrument. -/
theorem spinFilterQuantumChannel_map (k : ℂ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (spinFilterQuantumChannel k).map ρ = (spinFilterChannel k).evolveMatrix ρ := rfl

end
end GaloisForLFunctions.HTGeometry.SchafferExl
