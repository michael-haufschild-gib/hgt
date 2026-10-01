import GaloisForLFunctions.RHTower.CompactGaussianReflectedCarrierIdentity
import GaloisForLFunctions.RHTower.ReflectedCompactTargetEvent
import GaloisForLFunctions.RHTower.ReflectedCompactTargetCatalogue

open Complex Finset
noncomputable section
namespace RHTower
open SteinhausModel

/-- Complete deterministic error assembly for the original frozen AFE. The
five error terms retain their actual coefficients, phases and polynomial cutoff. -/
theorem norm_reflectedCompactTarget_error_le
    {s : ℂ} (hs0 : 1 / 2 < s.re) (hs1 : s.re < 1)
    (tau : ℝ) (N L Y : ℕ) (hN : 0 < N) (hYN : Y ≤ N) (hNL : N ≤ L) (hLY : L < Y * Y)
    (ω ξ ω0 : Omega) (f g : ℂ → ℂ) (C eB eW eG eC eT : ℝ)
    (hrow : ‖reflectedCompactGaussianRow s N tau‖ ≤ C)
    (hbackground : ‖compactGaussianRetainedCarrier s N L
      (steinhausWindowRetainedPrimes L N Y) (steinhausLogPhaseShift ω tau)‖ ≤ eB)
    (hwindow : ‖(∑ p ∈ largePrimes N Y, charFactor 1 (ξ p) *
      compactGaussianNormalizedPrimeChannel s N p tau (L / p) (steinhausLogPhaseShift ω tau)) - g s‖ ≤ eW)
    (hcatalogue : ‖reflectedCompactReferenceTarget f N tau ω0 s - g s‖ ≤ eG)
    (hcorrection : ‖steinhausCompactReflectedCorrection (s + (tau : ℂ) * I) N
      (freezeSteinhausPrefix (steinhausWindowRetainedPrimes L N Y) ω ξ) -
        steinhausCompactReflectedCorrection (s + (tau : ℂ) * I) N ω0‖ ≤ eC)
    (htail : ‖steinhausFullReflectedPrimalCarrier (s.re - 1 / 2) (tau + s.im) N
      (freezeSteinhausPrefix (steinhausWindowRetainedPrimes L N Y) ω ξ) -
        ∑ n ∈ Icc 1 L,
          smoothAFEZetaRightReflectedPrimalPositiveCoefficient (s.re - 1 / 2) (tau + s.im) 1 N n *
            X n (freezeSteinhausPrefix (steinhausWindowRetainedPrimes L N Y) ω ξ)‖ ≤ eT) :
    ‖steinhausCompactReflectedAFE (s + (tau : ℂ) * I) N
      (freezeSteinhausPrefix (steinhausWindowRetainedPrimes L N Y) ω ξ) - f s‖ ≤
        eT + C * (eB + eW + eG) + eC := by
  let η := freezeSteinhausPrefix (steinhausWindowRetainedPrimes L N Y) ω ξ
  let A := reflectedCompactGaussianRow s N tau
  let B := compactGaussianRetainedCarrier s N L (steinhausWindowRetainedPrimes L N Y)
    (steinhausLogPhaseShift ω tau)
  let W := ∑ p ∈ largePrimes N Y, charFactor 1 (ξ p) *
    compactGaussianNormalizedPrimeChannel s N p tau (L / p) (steinhausLogPhaseShift ω tau)
  let H := reflectedCompactReferenceTarget f N tau ω0 s
  let P := steinhausFullReflectedPrimalCarrier (s.re - 1 / 2) (tau + s.im) N η
  let F := ∑ n ∈ Icc 1 L,
    smoothAFEZetaRightReflectedPrimalPositiveCoefficient (s.re - 1 / 2) (tau + s.im) 1 N n * X n η
  let Q := steinhausCompactReflectedCorrection (s + (tau : ℂ) * I) N η
  let Q0 := steinhausCompactReflectedCorrection (s + (tau : ℂ) * I) N ω0
  have hpoint : rightDisplacedLinePt (s.re - 1 / 2) s.im = s := by
    apply Complex.ext <;> simp [rightDisplacedLinePt]
  have hshift : rightDisplacedLinePt (s.re - 1 / 2) (tau + s.im) = s + (tau : ℂ) * I := by
    apply Complex.ext <;> simp [rightDisplacedLinePt]
    ring
  have hfinite : F = A * (B + W) := by
    simpa only [hpoint] using reflectedPrimalFrozenWindow_eq_compactGaussian
      (s.re - 1 / 2) s.im tau L N Y hN hYN hNL hLY ω ξ
  have hAN : A ≠ 0 := reflectedCompactGaussianRow_ne_zero (by exact_mod_cast hN) (by linarith) hs1 tau
  have href : A * H = f s - Q0 := by
    dsimp only [H, reflectedCompactReferenceTarget, A]
    rw [← mul_assoc, mul_inv_cancel₀ hAN, one_mul]
  have hAFE : steinhausCompactReflectedAFE (s + (tau : ℂ) * I) N η = P + Q := by
    dsimp only [P, Q, steinhausFullReflectedPrimalCarrier, steinhausCompactReflectedAFE]
    rw [hshift]
  have heq : steinhausCompactReflectedAFE (s + (tau : ℂ) * I) N η - f s =
      (P - F) + A * (B + (W - g s) + (g s - H)) + (Q - Q0) := by
    rw [hAFE, hfinite]
    linear_combination href
  have hG : ‖g s - H‖ ≤ eG := by rw [norm_sub_rev]; exact hcatalogue
  have hinside : ‖B + (W - g s) + (g s - H)‖ ≤ eB + eW + eG :=
    (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add hbackground hwindow)) hG)
  have hC : 0 ≤ C := (norm_nonneg A).trans hrow
  change ‖steinhausCompactReflectedAFE (s + (tau : ℂ) * I) N η - f s‖ ≤ _
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add htail
      (by rw [norm_mul]; exact mul_le_mul hrow hinside (norm_nonneg _) hC))) hcorrection)

end RHTower
