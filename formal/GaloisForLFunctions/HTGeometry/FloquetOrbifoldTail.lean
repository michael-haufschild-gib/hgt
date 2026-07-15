import GaloisForLFunctions.HTGeometry.SchwarzianProjectiveInvariant
import Mathlib.Tactic

/-!
# A stroboscopic orbifold current from individually erasing rational steps

The rational maps `R₁(z)=z²+1` and `R₂(z)=(z-1)²` compose to the power map `z⁴`.  This file
formalizes the exact phase-current transport identities showing that the protected current lives
in the ordered two-step protocol rather than either static frame.
-/

open scoped Differential

namespace GaloisForLFunctions

noncomputable section

def floquetR₁ {K : Type*} [Field K] (x : K) : K := x ^ 2 + 1

def floquetR₂ {K : Type*} [Field K] (x : K) : K := (x - 1) ^ 2

def phaseZeroCurrent {K : Type*} [Field K] [Differential K] (x : K) : K := x′ / x

def phaseOneCurrent {K : Type*} [Field K] [Differential K] (x : K) : K := x′ / (x - 1)

private theorem deriv_one {K : Type*} [Field K] [Differential K] : (1 : K)′ = 0 :=
  Differential.deriv.map_one_eq_zero

/-- The phase-zero period map is the fourth-power map. -/
theorem floquetR₂_comp_R₁ {K : Type*} [Field K] (x : K) :
    floquetR₂ (floquetR₁ x) = x ^ 4 := by
  simp [floquetR₁, floquetR₂]
  ring

/-- The rotated phase-one period map is the translate-conjugate fourth-power map. -/
theorem floquetR₁_comp_R₂ {K : Type*} [Field K] (x : K) :
    floquetR₁ (floquetR₂ x) = (x - 1) ^ 4 + 1 := by
  simp [floquetR₁, floquetR₂]
  ring

/-- The first step transports the phase-one logarithmic current to twice the phase-zero current. -/
theorem phaseOneCurrent_floquetR₁
    {K : Type*} [Field K] [CharZero K] [Differential K]
    (x : K) (hx : x ≠ 0) :
    phaseOneCurrent (floquetR₁ x) = 2 * phaseZeroCurrent x := by
  simp only [phaseOneCurrent, phaseZeroCurrent, floquetR₁]
  simp only [map_add, Derivation.leibniz_pow, deriv_one, add_zero,
    nsmul_eq_mul, smul_eq_mul]
  field_simp [hx]
  ring

/-- The second step transports the phase-zero current back to twice the phase-one current. -/
theorem phaseZeroCurrent_floquetR₂
    {K : Type*} [Field K] [CharZero K] [Differential K]
    (x : K) (hx : x - 1 ≠ 0) :
    phaseZeroCurrent (floquetR₂ x) = 2 * phaseOneCurrent x := by
  simp only [phaseOneCurrent, phaseZeroCurrent, floquetR₂]
  simp only [Derivation.leibniz_pow, map_sub, deriv_one, sub_zero,
    nsmul_eq_mul, smul_eq_mul]
  field_simp [hx]
  ring

/-- One full period returns the phase-zero current with Floquet multiplier four. -/
theorem phaseZeroCurrent_twoStep
    {K : Type*} [Field K] [CharZero K] [Differential K]
    (x : K) (hx : x ≠ 0) :
    phaseZeroCurrent (floquetR₂ (floquetR₁ x)) = 4 * phaseZeroCurrent x := by
  rw [floquetR₂_comp_R₁]
  simp only [phaseZeroCurrent, Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul]
  field_simp [hx]
  ring

/-- The rotated period returns the phase-one current with the same multiplier four. -/
theorem phaseOneCurrent_rotatedTwoStep
    {K : Type*} [Field K] [CharZero K] [Differential K]
    (x : K) (hx : x - 1 ≠ 0) :
    phaseOneCurrent (floquetR₁ (floquetR₂ x)) = 4 * phaseOneCurrent x := by
  rw [floquetR₁_comp_R₂]
  simp only [phaseOneCurrent, map_add, Derivation.leibniz_pow, map_sub,
    deriv_one, sub_zero, add_zero, nsmul_eq_mul, smul_eq_mul]
  field_simp [hx]
  ring

end


end GaloisForLFunctions
