import GaloisForLFunctions.RHTower.IharaBlockSelector

/-!
# The normalized two-spin Lee--Yang block

For two Ising spins with ferromagnetic coupling, normalization in the field fugacity gives the
quadratic block

`1 + 2 c z + z^2`,

where `c = exp(-2J)` lies in `[0,1]` when `J ≥ 0`.  This file identifies that polynomial with the
already formalized reciprocal quadratic selector and proves that its zeros lie on the unit circle
exactly when `c^2 ≤ 1`.

The finite result is classical infrastructure, not an RH theorem.  It also supplies a sharp no-go:
reciprocity remains true outside the ferromagnetic chamber and therefore cannot replace the
coefficient inequality.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions

/-- The normalized two-spin Ising fugacity block. -/
def leeYangPairBlock (c : ℝ) (z : ℂ) : ℂ :=
  1 + (2 * c : ℝ) * z + z ^ 2

/-- Both zeros of the pair block lie on the unit circle. -/
def leeYangPairCircle (c : ℝ) : Prop :=
  ∀ z : ℂ, leeYangPairBlock c z = 0 → Complex.normSq z = 1

/-- The pair block is the `q = 1`, `lambda = -2c` reciprocal selector. -/
theorem leeYangPairBlock_eq_iharaBlock (c : ℝ) (z : ℂ) :
    leeYangPairBlock c z = iharaBlock 1 (-2 * c) z := by
  simp only [leeYangPairBlock, iharaBlock]
  push_cast
  ring

/-- Exact two-spin Lee--Yang selector. -/
theorem leeYangPairCircle_iff (c : ℝ) :
    leeYangPairCircle c ↔ c ^ 2 ≤ 1 := by
  constructor
  · intro hc
    have hcircle : zerosOnCriticalCircle 1 (-2 * c) := by
      intro z hz
      have hz' : leeYangPairBlock c z = 0 := by
        rwa [leeYangPairBlock_eq_iharaBlock]
      simpa using hc z hz'
    have hbound :=
      (zerosOnCriticalCircle_iff_spectral_bound
        (q := (1 : ℝ)) (lambda := -2 * c) (by norm_num)).mp hcircle
    dsimp [blockSpectralBound] at hbound
    nlinarith
  · intro hc
    have hbound : blockSpectralBound 1 (-2 * c) := by
      dsimp [blockSpectralBound]
      nlinarith
    have hcircle :=
      (zerosOnCriticalCircle_iff_spectral_bound
        (q := (1 : ℝ)) (lambda := -2 * c) (by norm_num)).mpr hbound
    intro z hz
    have hz' : iharaBlock 1 (-2 * c) z = 0 := by
      rwa [← leeYangPairBlock_eq_iharaBlock]
    simpa using hcircle z hz'

/-- A ferromagnetic coefficient in `[0,1]` satisfies the unit-circle selector. -/
theorem leeYangPairCircle_of_ferromagneticCoefficient {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : leeYangPairCircle c := by
  rw [leeYangPairCircle_iff]
  nlinarith

/-- Fugacity reciprocity is automatic, independently of the ferromagnetic inequality. -/
theorem leeYangPairBlock_reciprocal (c : ℝ) {z : ℂ} (hz : z ≠ 0) :
    z ^ 2 * leeYangPairBlock c z⁻¹ = leeYangPairBlock c z := by
  rw [leeYangPairBlock_eq_iharaBlock, leeYangPairBlock_eq_iharaBlock]
  simpa using iharaBlock_reciprocal_identity
    (q := (1 : ℝ)) (lambda := -2 * c) (by norm_num) hz

/-- Positive no-go boundary: reciprocal symmetry survives at `c = 2`, but circle localization does
not.  The missing datum is the coefficient chamber, not another functional equation. -/
theorem leeYangPair_reciprocity_does_not_force_circle :
    (∀ z : ℂ, z ≠ 0 → z ^ 2 * leeYangPairBlock 2 z⁻¹ = leeYangPairBlock 2 z) ∧
      ¬ leeYangPairCircle 2 := by
  refine ⟨fun z hz => leeYangPairBlock_reciprocal 2 hz, ?_⟩
  rw [leeYangPairCircle_iff]
  norm_num

end GaloisForLFunctions.RHTower
