import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ClippedProbeIndex
import GaloisForLFunctions.HilbertMetric.Spectral.ClippedCertificates

/-!
# Scalar certificates assembled from probe combinations

Each row of a coefficient matrix supplies a scalar clipped confinement mass.
Their sum is bounded by the full compressed clipped energy, so scalar masses
and pairwise bare energies alone certify negative directions and right zeros.
No eigenvalue of the compressed confinement matrix needs to be evaluated.
-/

open Matrix
open scoped ComplexOrder
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry ArithmeticCastelnuovoSeveri HilbertMetric.Clipped
noncomputable section

/-- Additive scalar certificates for an arbitrary family of actual probe combinations. -/
theorem probe_scalar_clipped_index_bound {R : ℝ} (hR : 0 < R)
    {N M : ℕ} {p : Fin N → ℝ} (hp : ∀ i, 4 < p i)
    (V : Matrix (Fin M) (Fin N) ℂ) (c : ℝ) :
    (∑ i, quadratic c ((V * probeConfinementBlock R p * Vᴴ) i i).re) -
      2 * c * (trace (V * confinedProbeGram R p * Vᴴ)).re -
      c ^ 2 * hermNegIndex (confinedProbeGram R p) ≤
        ∑ i, ∑ j, Complex.normSq ((V * probeGram p * Vᴴ) i j) := by
  have hd := diagonal_clipped_lower
    ((probeConfinementBlock_posSemidef hR hp).mul_mul_conjTranspose_same V).isHermitian c
  have h := clipped_compressed_probe_negative_index hR hp V c
  linarith only [hd, h]

/-- A fully scalar finite certificate for at least `m+1` zeros right of the line. -/
theorem rightZero_count_of_scalar_clipped_excess {R : ℝ} (hR : 0 < R)
    {N M : ℕ} {p : Fin N → ℝ} (hp : ∀ i, 4 < p i)
    (V : Matrix (Fin M) (Fin N) ℂ) (c : ℝ) (m : ℕ)
    (hexcess : (∑ i, ∑ j, Complex.normSq ((V * probeGram p * Vᴴ) i j)) + c ^ 2 * m <
      (∑ i, quadratic c ((V * probeConfinementBlock R p * Vᴴ) i i).re) -
        2 * c * (trace (V * confinedProbeGram R p * Vᴴ)).re) :
    ((m + 1 : ℕ) : ℕ∞) ≤ (rightZeros Zeta23.zetaZeroConfig).encard := by
  apply rightZero_count_of_clipped_excess hR hp V c m
  have hd := diagonal_clipped_lower
    ((probeConfinementBlock_posSemidef hR hp).mul_mul_conjTranspose_same V).isHermitian c
  linarith only [hd, hexcess]

#print axioms probe_scalar_clipped_index_bound
#print axioms rightZero_count_of_scalar_clipped_excess

end
end GaloisForLFunctions.ExclusionOfTheCriticalState
