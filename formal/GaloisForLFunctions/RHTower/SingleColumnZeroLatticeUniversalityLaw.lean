import GaloisForLFunctions.RHTower.ColumnRigidity
import GaloisForLFunctions.RHTower.ColumnarInterferential

/-!
# Single-column zero-lattice universality

The modulus equation of a single Dirichlet column fixes the real part of every zero.  The column's
phase periodicity propagates each such zero through a full vertical arithmetic progression.  These
two independently formalized mechanisms combine into an exact divisor-lattice law.
-/

namespace RHTower

/-- **Single-column zero-lattice universality law.**  Every zero of `1 - A b⁻ˢ`, with nonzero
amplitude and integer base at least two, lies on the line `Re s = log ‖A‖ / log b` and generates
zeros at every integer translate by the fundamental vertical period `2π / log b`. -/
theorem singleColumn_zeroLine_and_verticalLattice
    {A : ℂ} (hA : A ≠ 0) {b : ℕ} (hb : 2 ≤ b) {s₀ : ℂ}
    (hzero : 1 - A * (b : ℂ) ^ (-s₀) = 0) :
    s₀.re = Real.log ‖A‖ / Real.log b ∧
      ∀ k : ℤ,
        1 - A * (b : ℂ) ^
          (-(s₀ + (k * (2 * Real.pi / Real.log b)) * Complex.I)) = 0 := by
  refine ⟨factor_zero_line hA hb hzero, ?_⟩
  have hperiod := columnar_zero_periodic
    (Ω := Set.univ)
    (F := fun s => 1 - A * (b : ℂ) ^ (-s))
    (R := fun _ => 1)
    (ψ := fun q => 1 - A * q)
    (by simp) hb (by intro s hs; simp) (Set.mem_univ s₀) hzero
  simpa using hperiod

end RHTower
