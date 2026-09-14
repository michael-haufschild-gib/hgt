import GaloisForLFunctions.HTGeometry.BipartitePureNormalization
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Dynamic chirality in photonic time crystals

Closed algebraic content from arXiv:2609.08748: helical decomposition of a rotating modulation,
its co-rotating transport law, the shared integer action on Floquet frequency and orbital angular
momentum, and unconditional normalized channel populations. Numerical propagation claims are not
encoded.
-/

noncomputable section

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- Traveling phase `m θ - Ω t` of a rotating photonic-time-crystal modulation. -/
def rotatingModulationPhase (m : ℤ) (θ Ω t : ℝ) : ℝ :=
  (m : ℝ) * θ - Ω * t

/-- Positive helical component of the real rotating modulation. -/
def rotatingPositiveHarmonic (m : ℤ) (θ Ω t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (rotatingModulationPhase m θ Ω t : ℂ))

/-- Negative helical component of the real rotating modulation. -/
def rotatingNegativeHarmonic (m : ℤ) (θ Ω t : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (rotatingModulationPhase m θ Ω t : ℂ))

/-- Equation (9): a real rotating cosine is the balanced sum of its helicities. -/
theorem rotatingCosine_exp_split (m : ℤ) (θ Ω t : ℝ) :
    (Real.cos (rotatingModulationPhase m θ Ω t) : ℂ) =
      (rotatingPositiveHarmonic m θ Ω t +
        rotatingNegativeHarmonic m θ Ω t) / 2 := by
  rw [rotatingPositiveHarmonic, rotatingNegativeHarmonic,
    Complex.ofReal_cos, Complex.cos]
  congr 2
  · congr 1
    ring
  · congr 1
    ring

theorem norm_rotatingPositiveHarmonic (m : ℤ) (θ Ω t : ℝ) :
    ‖rotatingPositiveHarmonic m θ Ω t‖ = 1 := by
  rw [rotatingPositiveHarmonic, Complex.norm_exp]
  simp [Complex.mul_re]

theorem norm_rotatingNegativeHarmonic (m : ℤ) (θ Ω t : ℝ) :
    ‖rotatingNegativeHarmonic m θ Ω t‖ = 1 := by
  rw [rotatingNegativeHarmonic, Complex.norm_exp]
  simp [Complex.mul_re]

/-- The traveling pattern is unchanged along its co-rotating spacetime direction. -/
theorem rotatingModulationPhase_transport
    (m : ℤ) (θ Ω t s : ℝ) :
    rotatingModulationPhase m (θ + Ω * s) Ω (t + (m : ℝ) * s) =
      rotatingModulationPhase m θ Ω t := by
  simp [rotatingModulationPhase]
  ring

theorem rotatingPositiveHarmonic_transport
    (m : ℤ) (θ Ω t s : ℝ) :
    rotatingPositiveHarmonic m (θ + Ω * s) Ω (t + (m : ℝ) * s) =
      rotatingPositiveHarmonic m θ Ω t := by
  rw [rotatingPositiveHarmonic, rotatingPositiveHarmonic,
    rotatingModulationPhase_transport]

theorem rotatingNegativeHarmonic_transport
    (m : ℤ) (θ Ω t s : ℝ) :
    rotatingNegativeHarmonic m (θ + Ω * s) Ω (t + (m : ℝ) * s) =
      rotatingNegativeHarmonic m θ Ω t := by
  rw [rotatingNegativeHarmonic, rotatingNegativeHarmonic,
    rotatingModulationPhase_transport]

/-- Complex permittivity profile in equation (1), retaining its loss coordinate. -/
def rotatingComplexPermittivity
    (εbar δε εLoss : ℝ) (m : ℤ) (θ Ω t : ℝ) : ℂ :=
  ((εbar * (1 + δε * Real.cos (rotatingModulationPhase m θ Ω t)) : ℝ) : ℂ) +
    Complex.I * (εLoss : ℂ)

@[simp] theorem rotatingComplexPermittivity_re
    (εbar δε εLoss : ℝ) (m : ℤ) (θ Ω t : ℝ) :
    (rotatingComplexPermittivity εbar δε εLoss m θ Ω t).re =
      εbar * (1 + δε * Real.cos (rotatingModulationPhase m θ Ω t)) := by
  simp only [rotatingComplexPermittivity, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

@[simp] theorem rotatingComplexPermittivity_im
    (εbar δε εLoss : ℝ) (m : ℤ) (θ Ω t : ℝ) :
    (rotatingComplexPermittivity εbar δε εLoss m θ Ω t).im = εLoss := by
  simp only [rotatingComplexPermittivity, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem rotatingComplexPermittivity_helical_decomposition
    (εbar δε εLoss : ℝ) (m : ℤ) (θ Ω t : ℝ) :
    rotatingComplexPermittivity εbar δε εLoss m θ Ω t =
      (εbar : ℂ) + ((εbar * δε / 2 : ℝ) : ℂ) *
        (rotatingPositiveHarmonic m θ Ω t +
          rotatingNegativeHarmonic m θ Ω t) +
        Complex.I * (εLoss : ℂ) := by
  calc
    _ = (εbar : ℂ) + ((εbar * δε : ℝ) : ℂ) *
        (Real.cos (rotatingModulationPhase m θ Ω t) : ℂ) +
        Complex.I * (εLoss : ℂ) := by
      rw [rotatingComplexPermittivity]
      push_cast
      ring
    _ = _ := by
      rw [rotatingCosine_exp_split]
      push_cast
      ring

/-- Frequency of Floquet channel `n`, equation (10). -/
def floquetSidebandFrequency (ω Ω : ℝ) (n : ℤ) : ℝ :=
  ω + (n : ℝ) * Ω

/-- Orbital angular momentum of Floquet channel `n`, equation (10). -/
def floquetSidebandAngularMomentum (ℓ m n : ℤ) : ℤ :=
  ℓ + n * m

@[simp] theorem floquetSidebandFrequency_zero (ω Ω : ℝ) :
    floquetSidebandFrequency ω Ω 0 = ω := by
  simp [floquetSidebandFrequency]

@[simp] theorem floquetSidebandAngularMomentum_zero (ℓ m : ℤ) :
    floquetSidebandAngularMomentum ℓ m 0 = ℓ := by
  simp [floquetSidebandAngularMomentum]

/-- Sideband shifts form an additive integer action on frequency. -/
theorem floquetSidebandFrequency_add (ω Ω : ℝ) (n k : ℤ) :
    floquetSidebandFrequency ω Ω (n + k) =
      floquetSidebandFrequency (floquetSidebandFrequency ω Ω n) Ω k := by
  simp [floquetSidebandFrequency]
  ring

/-- Sideband shifts form the same additive integer action on angular momentum. -/
theorem floquetSidebandAngularMomentum_add (ℓ m n k : ℤ) :
    floquetSidebandAngularMomentum ℓ m (n + k) =
      floquetSidebandAngularMomentum (floquetSidebandAngularMomentum ℓ m n) m k := by
  simp [floquetSidebandAngularMomentum]
  ring

theorem floquetSidebandFrequency_reflection (ω Ω : ℝ) (n : ℤ) :
    floquetSidebandFrequency ω Ω n + floquetSidebandFrequency ω Ω (-n) = 2 * ω := by
  simp [floquetSidebandFrequency]
  ring

theorem floquetSidebandAngularMomentum_reflection (ℓ m n : ℤ) :
    floquetSidebandAngularMomentum ℓ m n +
        floquetSidebandAngularMomentum ℓ m (-n) = 2 * ℓ := by
  simp [floquetSidebandAngularMomentum]
  ring

/-- Frequency and angular momentum are locked to the same Floquet-channel shift. -/
theorem floquetSideband_frequency_momentum_locking
    (ω Ω : ℝ) (ℓ m n : ℤ) :
    (m : ℝ) * (floquetSidebandFrequency ω Ω n - ω) =
      Ω * ((floquetSidebandAngularMomentum ℓ m n - ℓ : ℤ) : ℝ) := by
  simp [floquetSidebandFrequency, floquetSidebandAngularMomentum]
  ring

theorem floquetSideband_first_order (ω Ω : ℝ) (ℓ m : ℤ) :
    floquetSidebandFrequency ω Ω 1 = ω + Ω ∧
    floquetSidebandFrequency ω Ω (-1) = ω - Ω ∧
    floquetSidebandAngularMomentum ℓ m 1 = ℓ + m ∧
    floquetSidebandAngularMomentum ℓ m (-1) = ℓ - m := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [floquetSidebandFrequency]
  · simp [floquetSidebandFrequency]
    ring
  · simp [floquetSidebandAngularMomentum]
  · simp [floquetSidebandAngularMomentum]
    ring

/-- Paper's `m = 4`, `ℓ₀ = ±1` chirality split: `(+5,+3)` versus `(-3,-5)`. -/
theorem dynamicChirality_orderFour_channels :
    floquetSidebandAngularMomentum 1 4 1 = 5 ∧
    floquetSidebandAngularMomentum 1 4 (-1) = -3 ∧
    floquetSidebandAngularMomentum (-1) 4 1 = 3 ∧
    floquetSidebandAngularMomentum (-1) 4 (-1) = -5 := by
  norm_num [floquetSidebandAngularMomentum]

/-- Equation (7), made total by normalizing any raw coefficient array first. -/
def normalizedFloquetChannelPopulation (channels modes : ℕ)
    (raw : Fin (channels + 1) × Fin (modes + 1) → ℂ)
    (n : Fin (channels + 1)) : ℝ :=
  ∑ σ, Complex.normSq (normalizedBipartitePureState channels modes raw (n, σ))

theorem normalizedFloquetChannelPopulation_nonneg (channels modes : ℕ)
    (raw : Fin (channels + 1) × Fin (modes + 1) → ℂ)
    (n : Fin (channels + 1)) :
    0 ≤ normalizedFloquetChannelPopulation channels modes raw n := by
  exact Finset.sum_nonneg fun σ _ => Complex.normSq_nonneg _

/-- Normalized channel populations form a probability distribution for every raw array. -/
theorem normalizedFloquetChannelPopulation_total (channels modes : ℕ)
    (raw : Fin (channels + 1) × Fin (modes + 1) → ℂ) :
    ∑ n, normalizedFloquetChannelPopulation channels modes raw n = 1 := by
  change bipartitePureMass channels modes
    (normalizedBipartitePureState channels modes raw) = 1
  exact normalizedBipartitePureState_mass channels modes raw

theorem normalizedFloquetChannelPopulation_le_one (channels modes : ℕ)
    (raw : Fin (channels + 1) × Fin (modes + 1) → ℂ)
    (n : Fin (channels + 1)) :
    normalizedFloquetChannelPopulation channels modes raw n ≤ 1 := by
  have hle : normalizedFloquetChannelPopulation channels modes raw n ≤
      ∑ k, normalizedFloquetChannelPopulation channels modes raw k :=
    Finset.single_le_sum
      (fun k _ => normalizedFloquetChannelPopulation_nonneg channels modes raw k)
      (Finset.mem_univ n)
  rwa [normalizedFloquetChannelPopulation_total] at hle

theorem normalizedFloquetCoefficient_le_channel (channels modes : ℕ)
    (raw : Fin (channels + 1) × Fin (modes + 1) → ℂ)
    (n : Fin (channels + 1)) (σ : Fin (modes + 1)) :
    Complex.normSq (normalizedBipartitePureState channels modes raw (n, σ)) ≤
      normalizedFloquetChannelPopulation channels modes raw n := by
  exact Finset.single_le_sum
    (fun k _ => Complex.normSq_nonneg
      (normalizedBipartitePureState channels modes raw (n, k)))
    (Finset.mem_univ σ)

end GaloisForLFunctions.HTGeometry
