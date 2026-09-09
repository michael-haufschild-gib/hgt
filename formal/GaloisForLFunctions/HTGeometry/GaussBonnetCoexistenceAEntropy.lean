import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceAGibbs

/-!
# Entropy and latent heat across logarithmic-entropy coexistence

The two global minima have a strictly positive entropy jump and latent
heat. The entropy reference cancels exactly. Relative to the same two
radii's area entropy, the Gauss–Bonnet logarithm supplies an explicit
nonnegative enhancement, strictly positive precisely at nonzero coupling.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry
open CPV

def egbCoexistenceAEntropyJump (k τ θ : ℝ) : ℝ :=
  Real.pi * exp k ^ 2 * (1 - thermalRatio τ ^ 2) +
    4 * Real.pi * exp k ^ 2 * egbCoexistenceACouplingWeight τ θ * exp τ

def egbCoexistenceALatentHeat (k τ θ : ℝ) : ℝ :=
  egbCoexistenceATemperature k τ θ * egbCoexistenceAEntropyJump k τ θ

theorem egbCoexistenceA_entropy_jump (k τ θ l : ℝ) :
    egbEntropyA (egbCoexistenceACouplingRoot k τ θ) l (egbCoexistenceLargeRadius k) -
      egbEntropyA (egbCoexistenceACouplingRoot k τ θ) l (egbCoexistenceSmallRadius k τ) =
    egbCoexistenceAEntropyJump k τ θ := by
  have hL : log (exp k / exp l) = k - l := by rw [← exp_sub, log_exp]
  have hS : log (thermalRatio τ * exp k / exp l) = -exp τ + k - l := by
    rw [thermalRatio, ← exp_add, ← exp_sub, log_exp]
  unfold egbEntropyA egbCoexistenceLargeRadius egbCoexistenceSmallRadius egbCoexistenceAEntropyJump
  rw [egbCoexistenceACouplingRoot_sq, hL, hS]
  ring

theorem egbCoexistenceAEntropyJump_pos (k τ θ : ℝ) : 0 < egbCoexistenceAEntropyJump k τ θ := by
  have hz := thermalRatio_pos τ
  have hz1 := thermalRatio_lt_one τ
  have hgap : 0 < 1 - thermalRatio τ ^ 2 := by nlinarith
  have hb := (egbCoexistenceACouplingWeight_bounds τ θ).1
  unfold egbCoexistenceAEntropyJump
  positivity

/-- The reference scale cancels from the entropy discontinuity. -/
theorem egbCoexistenceA_entropy_jump_reference_invariant (k τ θ l₁ l₂ : ℝ) :
    egbEntropyA (egbCoexistenceACouplingRoot k τ θ) l₁ (egbCoexistenceLargeRadius k) -
      egbEntropyA (egbCoexistenceACouplingRoot k τ θ) l₁ (egbCoexistenceSmallRadius k τ) =
    egbEntropyA (egbCoexistenceACouplingRoot k τ θ) l₂ (egbCoexistenceLargeRadius k) -
      egbEntropyA (egbCoexistenceACouplingRoot k τ θ) l₂ (egbCoexistenceSmallRadius k τ) := by
  rw [egbCoexistenceA_entropy_jump, egbCoexistenceA_entropy_jump]

/-- Exact logarithmic enhancement over area entropy at the same pair of radii. -/
theorem egbCoexistenceA_entropy_enhancement (k τ θ : ℝ) :
    egbCoexistenceAEntropyJump k τ θ -
      (egbEntropyB (egbCoexistenceLargeRadius k) - egbEntropyB (egbCoexistenceSmallRadius k τ)) =
    4 * Real.pi * egbCoexistenceACouplingRoot k τ θ ^ 2 * exp τ := by
  rw [egbCoexistence_entropy_jump, egbCoexistenceACouplingRoot_sq]
  unfold egbCoexistenceAEntropyJump
  ring

theorem egbCoexistenceA_entropy_enhancement_nonneg (k τ θ : ℝ) :
    egbEntropyB (egbCoexistenceLargeRadius k) - egbEntropyB (egbCoexistenceSmallRadius k τ) ≤
      egbCoexistenceAEntropyJump k τ θ := by
  rw [← sub_nonneg, egbCoexistenceA_entropy_enhancement]
  positivity

theorem egbCoexistenceA_entropy_enhancement_pos_iff (k τ θ : ℝ) :
    egbEntropyB (egbCoexistenceLargeRadius k) - egbEntropyB (egbCoexistenceSmallRadius k τ) <
      egbCoexistenceAEntropyJump k τ θ ↔ egbCoexistenceACouplingRoot k τ θ ≠ 0 := by
  rw [← sub_pos, egbCoexistenceA_entropy_enhancement]
  have hp : 0 < 4 * Real.pi * exp τ := by positivity
  rw [show 4 * Real.pi * egbCoexistenceACouplingRoot k τ θ ^ 2 * exp τ =
    (4 * Real.pi * exp τ) * egbCoexistenceACouplingRoot k τ θ ^ 2 by ring,
    mul_pos_iff_of_pos_left hp, sq_pos_iff]

theorem egbCoexistenceALatentHeat_pos (k τ θ : ℝ) : 0 < egbCoexistenceALatentHeat k τ θ :=
  mul_pos (egbCoexistenceATemperature_pos k τ θ) (egbCoexistenceAEntropyJump_pos k τ θ)

/-- Equal global Gibbs minima force the exact enthalpy/latent-heat identity. -/
theorem egbCoexistenceA_latent_heat (k τ θ : ℝ) :
    egbMass (egbCoexistenceAPressure k τ θ) (egbCoexistenceACharge k τ θ)
      (egbCoexistenceACouplingRoot k τ θ) (egbCoexistenceLargeRadius k) -
    egbMass (egbCoexistenceAPressure k τ θ) (egbCoexistenceACharge k τ θ)
      (egbCoexistenceACouplingRoot k τ θ) (egbCoexistenceSmallRadius k τ) = egbCoexistenceALatentHeat k τ θ := by
  have h := egbCoexistenceA_equal_gibbs k τ θ 0
  unfold egbOffShellGibbsA at h
  rw [egbCoexistenceALatentHeat, ← egbCoexistenceA_entropy_jump k τ θ 0]
  nlinarith [h]

theorem egbCoexistenceA_enthalpy_jump_pos (k τ θ : ℝ) :
    0 < egbMass (egbCoexistenceAPressure k τ θ) (egbCoexistenceACharge k τ θ)
      (egbCoexistenceACouplingRoot k τ θ) (egbCoexistenceLargeRadius k) -
    egbMass (egbCoexistenceAPressure k τ θ) (egbCoexistenceACharge k τ θ)
      (egbCoexistenceACouplingRoot k τ θ) (egbCoexistenceSmallRadius k τ) := by
  rw [egbCoexistenceA_latent_heat]
  exact egbCoexistenceALatentHeat_pos k τ θ

end GaloisForLFunctions.HTGeometry
