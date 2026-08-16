import GaloisForLFunctions.HTGeometry.TruncatedConvolutionCommutator
import GaloisForLFunctions.RHTower.CCMGeneralParityOddGroundAdapter

/-!
# The Fourier compression of a truncated convolution is a centered divided-difference packet

The exact commutator law for an even `C¹` kernel says that the matrix of the truncated convolution
in the exponential basis is the divided difference of its boundary source.  Transporting that
statement to the centered parity index of the parity-free odd-ground law identifies the compressed
form as a centered divided-difference matrix with an odd source and a reflection-even diagonal:
exactly the matrix class for which a simple odd kernel vector has a real-rooted Fourier transform.
-/

open Matrix

open scoped Matrix ComplexOrder

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The centered source of the truncated-convolution packet. -/
def truncConvParitySource (k : ℝ → ℝ) (N : ℕ) (i : CCMCenteredParityIndex N) : ℝ :=
  -(convSource k (ccmParityCenteredMode N i)).re

/-- The centered diagonal of the truncated-convolution packet. -/
def truncConvParityDiagonal (k : ℝ → ℝ) (N : ℕ) (i : CCMCenteredParityIndex N) : ℝ :=
  (convMatrix k (ccmParityCenteredMode N i) (ccmParityCenteredMode N i)).re

/-- **The source is odd.** -/
theorem truncConvParitySource_odd (k : ℝ → ℝ) (N : ℕ) (i : CCMCenteredParityIndex N) :
    truncConvParitySource k N (ccmCenteredParityReflection N i)
      = -truncConvParitySource k N i := by
  rw [truncConvParitySource, truncConvParitySource, ccmParityCenteredMode_reflection,
    convSource_re_neg]

/-- **The diagonal is reflection even.** -/
theorem truncConvParityDiagonal_even {k : ℝ → ℝ} (heven : ∀ u, k (-u) = k u) (N : ℕ)
    (i : CCMCenteredParityIndex N) :
    truncConvParityDiagonal k N (ccmCenteredParityReflection N i)
      = truncConvParityDiagonal k N i := by
  rw [truncConvParityDiagonal, truncConvParityDiagonal, ccmParityCenteredMode_reflection,
    convMatrix_reflect heven]

/-- **The matrix identification.**  Every entry of the compressed truncated convolution is the
corresponding entry of the centered divided-difference matrix built from its boundary source and
its own diagonal. -/
theorem ccmDividedDifferenceMatrix_truncConv {k k' : ℝ → ℝ} (hk : ∀ u, HasDerivAt k (k' u) u)
    (hk'c : Continuous k') (heven : ∀ u, k (-u) = k u) (N : ℕ)
    (i j : CCMCenteredParityIndex N) :
    ccmDividedDifferenceMatrix (ccmParityCenteredClock N) (truncConvParitySource k N)
        (truncConvParityDiagonal k N) i j
      = (convMatrix k (ccmParityCenteredMode N i) (ccmParityCenteredMode N j)).re := by
  rw [ccmDividedDifferenceMatrix]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, truncConvParityDiagonal]
  · rw [if_neg hij]
    have hclock : ccmParityCenteredClock N i - ccmParityCenteredClock N j ≠ 0 := by
      intro h
      exact hij (ccmParityCenteredClock_injective N (by linarith [sub_eq_zero.1 h]))
    have hmode : ccmParityCenteredClock N i - ccmParityCenteredClock N j
        = ((ccmParityCenteredMode N i : ℝ) - (ccmParityCenteredMode N j : ℝ)) := by
      rw [ccmParityCenteredClock, ccmParityCenteredClock]
    have hcomm := convMatrix_re_commutator hk hk'c heven
      (ccmParityCenteredMode N i) (ccmParityCenteredMode N j)
    rw [truncConvParitySource, truncConvParitySource]
    rw [hmode] at hclock ⊢
    field_simp
    linarith [hcomm]

/-- The truncated-convolution packet on the centered parity index. -/
def truncConvParityPacket (k : ℝ → ℝ) (N : ℕ) (mu : ℝ) :
    Matrix (CCMCenteredParityIndex N) (CCMCenteredParityIndex N) ℂ :=
  ccmCenteredParityPacket (truncConvParitySource k N) (truncConvParityDiagonal k N) mu

/-- **The compressed truncated convolution, shifted by any spectral floor, is a centered parity
packet.**  Its entries away from the diagonal are the divided differences of the boundary source,
its source is odd, and its diagonal is reflection even, so a simple odd kernel vector of the packet
has a real-rooted band-limited Fourier transform. -/
theorem truncConvParityPacket_compactFourier_zero_im_eq_zero {k k' : ℝ → ℝ}
    (_hk : ∀ u, HasDerivAt k (k' u) u) (_hk'c : Continuous k') (heven : ∀ u, k (-u) = k u)
    {N : ℕ} {mu : ℝ} (hpsd : (truncConvParityPacket k N mu).PosSemidef)
    {c : Fin N → ℂ} (hc : c ≠ 0)
    (hground : truncConvParityPacket k N mu *ᵥ (ccmOddParityFrame N *ᵥ c) = 0)
    (hline : ∀ v : CCMCenteredParityIndex N → ℂ,
      truncConvParityPacket k N mu *ᵥ v = 0 →
        ∃ z : ℂ, v = z • (ccmOddParityFrame N *ᵥ c))
    {z : ℂ}
    (hzero : compactFourier (ccmTrigPoly N (ccmOddGroundCoeff N c)) 0 (2 * Real.pi) z = 0) :
    z.im = 0 :=
  ccmCenteredDividedDifferenceOddGround_compactFourier_zero_im_eq_zero
    (truncConvParitySource_odd k N) (truncConvParityDiagonal_even heven N)
    hpsd hc hground hline hzero

end

end RHTower
