import GaloisForLFunctions.RHTower.XiZeroSumDivergence

/-!
# SP-E trace-class genus obstruction

The cofinal Stokes child is positive Schatten-one, so an ordinary Fredholm spectral landing has an
absolutely summable eigenvalue sequence. A multiplicity-exact Xi landing would force those
eigenvalues, up to one nonzero scalar, to be reciprocals of the centered Xi divisor. The corpus's
unconditional genus-one theorem proves that reciprocal Xi norms are not summable. Hence no
trace-class SP-E child—at any nonzero scalar normalization—can have the Xi divisor.

This kills the current ordinary/balanced trace-class landing, not SP-E geometry. Any survivor must
retain a Hilbert--Schmidt but non-trace-class genus-one channel and use a regularized determinant.
-/

open Complex

namespace RHTower

noncomputable section

/-- A multiplicity-exact scalar-rescaled Xi divisor realized by an absolutely summable spectral
sequence. This is the spectral datum required by an ordinary trace-class Fredholm determinant. -/
structure RoutePPrimitiveGammaJuliaStokesTraceClassXiDivisorLanding where
  scale : ℂ
  scale_ne_zero : scale ≠ 0
  eigenvalue : XiZeroCopy → ℂ
  summable_norm : Summable (fun q => ‖eigenvalue q‖)
  eigenvalue_mul_spectralPoint : ∀ q, eigenvalue q * xiSpectralPoint q = scale

/-- The Xi divisor has genus one, so no nonzero scalar rescaling of its reciprocal divisor is an
absolutely summable spectral sequence. -/
theorem not_routePPrimitiveGammaJuliaStokesTraceClassXiDivisorLanding : ¬ Nonempty RoutePPrimitiveGammaJuliaStokesTraceClassXiDivisorLanding := by
  rintro ⟨L⟩
  have hscaleNorm : ‖L.scale‖ ≠ 0 := norm_ne_zero_iff.mpr L.scale_ne_zero
  have heq (q : XiZeroCopy) :
      1 / ‖xiSpectralPoint q‖ = ‖L.scale‖⁻¹ * ‖L.eigenvalue q‖ := by
    have hspectral : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
    have hnorm := congrArg norm (L.eigenvalue_mul_spectralPoint q)
    rw [norm_mul] at hnorm
    have hspectralNorm : ‖xiSpectralPoint q‖ ≠ 0 := norm_ne_zero_iff.mpr hspectral
    field_simp [hscaleNorm, hspectralNorm]
    nlinarith
  apply not_summable_inv_norm_xiSpectralPoint
  exact (L.summable_norm.mul_left ‖L.scale‖⁻¹).congr fun q => (heq q).symm

end

end RHTower
