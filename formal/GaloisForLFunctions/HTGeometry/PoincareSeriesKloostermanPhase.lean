import GaloisForLFunctions.HTGeometry.PoincareSeriesExponentialExpansion
import GaloisForLFunctions.RHTower.Sieve.KloostermanSum

/-!
# The Kloosterman phases of the Poincaré series

For the row `(c, u)` with matrix `M_{c,u}` of top-left entry `a`, the determinant relation
`a d₀ - b c = 1` gives `a ≡ u⁻¹ (mod c)`, so the phase `e(ma/c) e(n d₀/c)` produced by the
exponential expansion is the classical Kloosterman phase `e((m ū + n u)/c)`, and its sum over the
units is the Kloosterman sum `S(m, n; c)`.
-/

open UpperHalfPlane hiding I
open Complex RHTower.Sieve
open scoped Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable (c : ℕ+) (u : (ZMod c)ˣ)

/-- `a ≡ u⁻¹ (mod c)`. -/
theorem unitTop_cast_eq_inv : ((unitTop c u : ℤ) : ZMod c) = ((u⁻¹ : (ZMod c)ˣ) : ZMod c) := by
  have h := unitRowMatrix_det c u
  have h' : ((unitTop c u * ((u : ZMod c).val : ℤ) - (unitRowMatrix c u) 0 1 * c : ℤ) : ZMod c)
      = 1 := by
    rw [h]
    simp
  push_cast at h'
  rw [ZMod.natCast_self, mul_zero, sub_zero, ZMod.natCast_zmod_val] at h'
  exact (Units.inv_eq_of_mul_eq_one_left h').symm

/-- The phase `e(m a/c) e(n d₀/c)` is the Kloosterman phase at `u⁻¹`. -/
theorem exp_phase_eq_kloostermanPhase (m n : ℕ) :
    Complex.exp (2 * π * I * m * (unitTop c u : ℂ) / c) *
        Complex.exp (2 * π * I * n * unitVal c u / c)
      = kloostermanPhase c (m : ZMod c) (n : ZMod c) u⁻¹ := by
  rw [kloostermanPhase, inv_inv, ← unitTop_cast_eq_inv]
  have : ((m : ZMod c) * ((unitTop c u : ℤ) : ZMod c) + (n : ZMod c) * (u : ZMod c))
      = (((m : ℤ) * unitTop c u + (n : ℤ) * ((u : ZMod c).val : ℤ) : ℤ) : ZMod c) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [this, ZMod.stdAddChar_coe, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [unitVal]
  ring

/-- **The Kloosterman sum**: `Σ_u e(m a_u/c) e(n d₀/c) = S(m, n; c)`. -/
theorem sum_exp_phase_eq_kloostermanSum (m n : ℕ) :
    ∑ u : (ZMod c)ˣ, Complex.exp (2 * π * I * m * (unitTop c u : ℂ) / c) *
        Complex.exp (2 * π * I * n * unitVal c u / c)
      = kloostermanSum c (m : ZMod c) (n : ZMod c) := by
  rw [kloostermanSum, ← Equiv.sum_comp (kloostermanUnitInvEquiv c)
    (kloostermanPhase c (m : ZMod c) (n : ZMod c))]
  refine Finset.sum_congr rfl fun u _ => ?_
  exact exp_phase_eq_kloostermanPhase c u m n

end

end GaloisForLFunctions.HTGeometry
