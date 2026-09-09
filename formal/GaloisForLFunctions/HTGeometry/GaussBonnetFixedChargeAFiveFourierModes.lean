import GaloisForLFunctions.QuantumAlg.Primitives.QFT
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
Five distinct Fourier indices and their exact positive weights for the critical
Gibbs kernel derived from arXiv:2609.00025. Grids contain at least eight points.
-/
namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem grid_size_bound (n : ℕ) : 8 ≤ 2 ^ (n + 3) := by
  have hp : 0 < (2 : ℕ) ^ n := pow_pos (by omega) n
  rw [pow_add]
  norm_num
  omega

/-- Frequencies 0, 1, 2, -2, -1, represented in the dyadic grid. -/
def egbFixedChargeAFiveFourierModes (n : ℕ) : Fin 5 → Fin (2 ^ (n + 3)) :=
  ![⟨0, by have := grid_size_bound n; omega⟩,
    ⟨1, by have := grid_size_bound n; omega⟩,
    ⟨2, by have := grid_size_bound n; omega⟩,
    ⟨2 ^ (n + 3) - 2, by have := grid_size_bound n; omega⟩,
    ⟨2 ^ (n + 3) - 1, by have := grid_size_bound n; omega⟩]

/-- These five harmonics never alias on the chosen grids. -/
theorem egbFixedChargeAFiveFourierModes_injective (n : ℕ) :
    Function.Injective (egbFixedChargeAFiveFourierModes n) := by
  intro i j h
  have hb := grid_size_bound n
  have hv := congrArg Fin.val h
  fin_cases i <;> fin_cases j <;>
    norm_num [egbFixedChargeAFiveFourierModes] at hv <;> omega

/-- Dimensionless Fourier coefficients, ordered as 0, 1, 2, -2, -1. -/
def egbFixedChargeAFourierWeights : Fin 5 → ℝ :=
  ![3 / 8, 1 / 4, 1 / 16, 1 / 16, 1 / 4]

/-- Every one of the five critical harmonics has a strictly positive coefficient. -/
theorem egbFixedChargeAFourierWeights_pos (k : Fin 5) :
    0 < egbFixedChargeAFourierWeights k := by
  fin_cases k <;> norm_num [egbFixedChargeAFourierWeights]

/-- The finite spectrum, with the remaining frequencies assigned zero. -/
def egbFixedChargeACriticalFourierSpectrum (n : ℕ) (j : Fin (2 ^ (n + 3))) : ℂ :=
  ∑ k : Fin 5, ((2 : ℝ) ^ (n + 3) * egbFixedChargeAFourierWeights k : ℂ) *
    (Pi.single (egbFixedChargeAFiveFourierModes n k) (1 : ℂ) :
      Fin (2 ^ (n + 3)) → ℂ) j

/-- Exact eigenvalue at each of the five occupied frequencies. -/
theorem egbFixedChargeACriticalFourierSpectrum_mode (n : ℕ) (k : Fin 5) :
    egbFixedChargeACriticalFourierSpectrum n (egbFixedChargeAFiveFourierModes n k) =
      ((2 : ℝ) ^ (n + 3) * egbFixedChargeAFourierWeights k : ℂ) := by
  classical
  unfold egbFixedChargeACriticalFourierSpectrum
  simp [Pi.single_apply, (egbFixedChargeAFiveFourierModes_injective n).eq_iff]

/-- The spectrum has no other nonzero frequencies. -/
theorem egbFixedChargeACriticalFourierSpectrum_support
    (n : ℕ) (j : Fin (2 ^ (n + 3))) :
    egbFixedChargeACriticalFourierSpectrum n j ≠ 0 ↔
      ∃ k : Fin 5, j = egbFixedChargeAFiveFourierModes n k := by
  classical
  constructor
  · intro hn
    by_contra he
    have hne : ∀ k : Fin 5, egbFixedChargeAFiveFourierModes n k ≠ j := by
      intro k h
      exact he ⟨k, h.symm⟩
    apply hn
    simp [egbFixedChargeACriticalFourierSpectrum, Pi.single_apply, hne]
  · rintro ⟨k, rfl⟩
    rw [egbFixedChargeACriticalFourierSpectrum_mode]
    exact_mod_cast (ne_of_gt (mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2) (n + 3))
      (egbFixedChargeAFourierWeights_pos k)))

/-- Exactly five nonzero eigenvalues are present, proved through a finite bijection. -/
theorem egbFixedChargeACriticalFourierSpectrum_card (n : ℕ) :
    Fintype.card {j // egbFixedChargeACriticalFourierSpectrum n j ≠ 0} = 5 := by
  classical
  let f : Fin 5 → {j // egbFixedChargeACriticalFourierSpectrum n j ≠ 0} :=
    fun k => ⟨egbFixedChargeAFiveFourierModes n k,
      (egbFixedChargeACriticalFourierSpectrum_support n _).mpr ⟨k, rfl⟩⟩
  have hi : Function.Injective f := by
    intro i j h
    exact egbFixedChargeAFiveFourierModes_injective n (congrArg Subtype.val h)
  have hs : Function.Surjective f := by
    intro j
    obtain ⟨k, hk⟩ := (egbFixedChargeACriticalFourierSpectrum_support n j.val).mp j.property
    exact ⟨k, Subtype.ext hk.symm⟩
  have h := Fintype.card_congr (Equiv.ofBijective f ⟨hi, hs⟩)
  simpa only [Fintype.card_fin] using h.symm

end

end GaloisForLFunctions.HTGeometry
