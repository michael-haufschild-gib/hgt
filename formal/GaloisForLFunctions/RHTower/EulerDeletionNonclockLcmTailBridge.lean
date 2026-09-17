import GaloisForLFunctions.RHTower.EulerDeletionTruncatedDivisorPairCorrelation
import GaloisForLFunctions.RHTower.EulerDeletionTailTruncatedDivisorBridge

/-!
# Non-clock lcm bridge for one physical EDQ refinement block

The selected physical block retains its literal source endpoint and source--tail cross term.
Only the square of its signed beta deviation is re-expressed through the exact non-clock lcm
fibres proved in `EulerDeletionTruncatedDivisorPairCorrelation`.
-/

noncomputable section
set_option autoImplicit false

open Finset ArithmeticFunction
open scoped BigOperators

namespace RHTower.DeletionResidueMartingale

/-- The square of one literal selected truncated-divisor block has an exact source term, signed
source--deviation cross term, and non-clock lcm-fibre tail.  No term is bounded or discarded. -/
theorem truncatedDivisorBlockKernel_sq_eq_source_cross_nonclockLcm
    (N l u b : ℕ) (x : ℝ) (hlN : l < N) :
    let t := u + b * clock l + 1
    let Q := canonicalClockRatio N (l + 1)
    let C := clock (l + 1)
    let D : ℝ :=
      ∑ s ∈ range Q, x ^ (s * C) *
        ((C : ℝ) * ∑ q ∈ Icc 1 N, ((moebius q : ℤ) : ℝ) / (q : ℝ) -
          ∑ k ∈ Ioc (t + s * C) (t + (s + 1) * C), truncMoebiusDivisorSum N k)
    let A : ℝ := (1 - x ^ clock N) * pairedMoebiusSource N (u + b * clock l)
    let B : ℝ := x ^ C
    let H : ℝ := (1 - x ^ clock N)⁻¹
    let G : ℝ := ∑ a ∈ range C, x ^ a
    let R : ℝ :=
      ∑ n ∈ (Icc 1 N ×ˢ Icc 1 N).image (fun de => Nat.lcm de.1 de.2) |>.filter
        (fun n => ¬ n ∣ C),
        finiteLcmPairFibre (Icc 1 N)
          (fun d => ((moebius d : ℤ) : ℝ) *
            ∑ s ∈ range (Q - 1),
              (∑ i ∈ range (s + 1), divisorWindowDiscrepancy d (t + i * C) C) *
                x ^ (s * C)) n
    truncatedDivisorBlockKernel N l u b x ^ 2 =
      (x ^ (u + b * clock l) * H / G) ^ 2 *
        (A ^ 2 + 2 * A * B * D + B ^ 2 * (1 - x ^ C) ^ 2 * R) := by
  dsimp
  let t := u + b * clock l + 1
  let Q := canonicalClockRatio N (l + 1)
  let C := clock (l + 1)
  let D : ℝ := ∑ s ∈ range Q, x ^ (s * C) *
    ((C : ℝ) * ∑ q ∈ Icc 1 N, ((moebius q : ℤ) : ℝ) / (q : ℝ) -
      ∑ k ∈ Ioc (t + s * C) (t + (s + 1) * C), truncMoebiusDivisorSum N k)
  let A : ℝ := (1 - x ^ clock N) * pairedMoebiusSource N (u + b * clock l)
  let B : ℝ := x ^ C
  let H : ℝ := (1 - x ^ clock N)⁻¹
  let G : ℝ := ∑ a ∈ range C, x ^ a
  let R : ℝ := ∑ n ∈ (Icc 1 N ×ˢ Icc 1 N).image (fun de => Nat.lcm de.1 de.2) |>.filter
      (fun n => ¬ n ∣ C),
      finiteLcmPairFibre (Icc 1 N)
        (fun d => ((moebius d : ℤ) : ℝ) *
          ∑ s ∈ range (Q - 1),
            (∑ i ∈ range (s + 1), divisorWindowDiscrepancy d (t + i * C) C) *
              x ^ (s * C)) n
  have hD : D ^ 2 = (1 - x ^ C) ^ 2 * R := by
    simpa [D, R, C, Q, t] using
      (selectedRefinementBlock_betaDeviation_sq_eq_childClockFactor_nonclockLcmFibres
        N l u b x hlN)
  have hkernel : truncatedDivisorBlockKernel N l u b x =
      x ^ (u + b * clock l) * (A + B * D) * H / G := by
    unfold truncatedDivisorBlockKernel
    dsimp [A, B, H, D, G, C, Q, t]
    ring
  rw [hkernel]
  calc
    (x ^ (u + b * clock l) * (A + B * D) * H / G) ^ 2 =
        (x ^ (u + b * clock l) * H / G) ^ 2 *
          (A ^ 2 + 2 * A * B * D + B ^ 2 * D ^ 2) := by ring
    _ = _ := by
      rw [hD]
      dsimp [A, B, H, G, D, R, C, Q, t]
      ring

end RHTower.DeletionResidueMartingale
