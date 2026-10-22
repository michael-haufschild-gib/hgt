import GaloisForLFunctions.HTGeometry.GammaCutoffIdentityBounds
import GaloisForLFunctions.RHTower.Suzuki.SuzukiGammaWallCutoffCommutator

/-!
# The cutoff commutator is the corpus's wall commutator

`R(χF) − χ·RF` is, integrand by integrand, the corpus's `gammaWallCommutator`: subtracting the two
second differences cancels the diagonal term and leaves only cutoff *differences*, so no derivative
of the profile occurs inside.  Identifying the two objects transfers the two-sided `O(e^{-|L|})`
wall — and hence membership in the block source class — to the commutator terms of `(14)`.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry
open _root_.RHTower (gammaJumpKernel)

/-- On the positive ray the two kernels agree. -/
theorem gammaJumpKernel_eq_gammaTransportKernel {s : ℝ} (hs : 0 < s) :
    gammaJumpKernel s = gammaTransportKernel s := by
  rw [gammaJumpKernel, gammaTransportKernel, abs_of_pos hs]

/-- **The cutoff commutator of the transport is the wall commutator.** -/
theorem gammaCommutator_eq_gammaWallCommutator {F F' χ χ' : ℝ → ℝ} {MF MW : ℝ}
    (hF : ∀ x, HasDerivAt F (F' x) x) (hMF : ∀ x, |F' x| ≤ MF)
    (hW : ∀ x, HasDerivAt (fun y => χ y * F y) (χ' x * F x + χ x * F' x) x)
    (hMW : ∀ x, |χ' x * F x + χ x * F' x| ≤ MW) (L : ℝ) :
    gammaCommutator χ F L = gammaWallCommutator χ F L := by
  have hint1 := integrableOn_secondDifference_mul_kernel hW hMW L
  have hint2 := integrableOn_secondDifference_mul_kernel hF hMF L
  rw [gammaCommutator, gammaTransport, gammaTransport, gammaWallCommutator,
    ← integral_const_mul, ← integral_sub hint1 (hint2.const_mul (χ L))]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hspos : (0 : ℝ) < s := hs
  have hker := gammaJumpKernel_eq_gammaTransportKernel hspos
  show secondDifference (fun y => χ y * F y) L s * gammaTransportKernel s
      - χ L * (secondDifference F L s * gammaTransportKernel s)
    = gammaJumpKernel s * ((χ L - χ (L + s)) * F (L + s) + (χ L - χ (L - s)) * F (L - s))
  rw [hker, secondDifference, secondDifference]
  ring

end GaloisForLFunctions.RHTower
