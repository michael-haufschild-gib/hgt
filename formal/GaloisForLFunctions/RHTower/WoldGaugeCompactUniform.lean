import GaloisForLFunctions.RHTower.PrimeWoldGammaGlobalBoundaryVolume
import GaloisForLFunctions.RHTower.AcceleratedWoldType

/-!
# The compact-uniform Wold--Gamma gauge bound

Tangent normalization of the reflected occupation phase introduces exactly the irregular gauge
`exp(2t / ε_S)`, where `ε_S` is the finite-prime Wold boundary volume, and reflection inverts the
raw phase.  Consequently, on a compact set where the raw phase is bounded above and below, the
logarithm of the normalized phase and of its reflection is at most `log C + 2M / ε_S`.
-/

open Complex

open GaloisForLFunctions

namespace RHTower

/-- The norm of the tangent-normalized phase splits off the irregular gauge exactly. -/
theorem norm_finitePrimeGenusOnePolarizedPhase (S : Finset Nat.Primes) (t : ℂ) :
    ‖finitePrimeGenusOnePolarizedPhase S t‖
      = Real.exp (2 * t.re / finitePrimeWoldBoundaryVolume S)
        * ‖finitePrimeGenusZeroPolarizedPhase S t‖ := by
  have hpos : 0 < finitePrimeWoldBoundaryVolume S := finitePrimeWoldBoundaryVolume_pos S
  rw [finitePrimeGenusOnePolarizedPhase_eq_irregularGauge_mul, norm_mul, Complex.norm_exp]
  congr 2
  have hre : (2 * t * ((finitePrimeWoldBoundaryVolume S : ℝ) : ℂ)⁻¹).re
      = 2 * t.re / finitePrimeWoldBoundaryVolume S := by
    rw [← Complex.ofReal_inv]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  exact hre

/-- **`(14c)` for the tree's own comparison.**  The finite-aperture comparison `(14b)` is a unitary
factor tensored with the diagonal pair `(Φ^(1)_S(t), exp(2t/ε_S))`.  The unitary contributes nothing
to either norm, so on a compact set where the tangent-normalized phase is bounded above and below
by `C` and the real part by `M`, the logarithm of the larger of the comparison and its inverse is
at most `log C + 2M/ε_S`. -/
theorem log_max_blockComparison_le {S : Finset Nat.Primes} {t : ℂ} {C M : ℝ}
    (hC : 1 ≤ C) (h1 : C⁻¹ ≤ ‖finitePrimeGenusOnePolarizedPhase S t‖)
    (h2 : ‖finitePrimeGenusOnePolarizedPhase S t‖ ≤ C) (ht : |t.re| ≤ M) :
    Real.log (max
        (max ‖finitePrimeGenusOnePolarizedPhase S t‖
          (Real.exp (2 * t.re / finitePrimeWoldBoundaryVolume S)))
        (max ‖finitePrimeGenusOnePolarizedPhase S t‖⁻¹
          (Real.exp (-(2 * t.re / finitePrimeWoldBoundaryVolume S)))))
      ≤ Real.log C + 2 * M / finitePrimeWoldBoundaryVolume S := by
  have hε : 0 < finitePrimeWoldBoundaryVolume S := finitePrimeWoldBoundaryVolume_pos S
  have habs : |‖finitePrimeGenusOnePolarizedPhase S t‖|
      = ‖finitePrimeGenusOnePolarizedPhase S t‖ := abs_of_nonneg (norm_nonneg _)
  have hkey := log_max_gauge_le (C := C) (M := M)
    (a := finitePrimeWoldBoundaryVolume S) (t := t.re)
    (φ := ‖finitePrimeGenusOnePolarizedPhase S t‖) hC hε (by rw [habs]; exact h1)
    (by rw [habs]; exact h2) ht
  rwa [habs] at hkey

/-- The reflected branch of the raw phase, recorded for the same comparison: reflection inverts the
raw phase, and tangent normalization contributes the opposite gauge. -/
theorem norm_finitePrimeGenusOnePolarizedPhase_neg (S : Finset Nat.Primes) (t : ℂ) :
    ‖finitePrimeGenusOnePolarizedPhase S (-t)‖
      = ‖finitePrimeGenusOnePolarizedPhase S t‖⁻¹ := by
  rw [finitePrimeGenusOnePolarizedPhase_reflection, norm_inv]

end RHTower
