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
    truncatedDivisorBlockKernel N l u b x ^ (2 : ℕ) =
      (x ^ (u + b * clock l) * H / G) ^ (2 : ℕ) *
        (A ^ (2 : ℕ) + 2 * A * B * D + B ^ (2 : ℕ) * (1 - x ^ C) ^ (2 : ℕ) * R) := by
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
  have hD : D ^ (2 : ℕ) = (1 - x ^ C) ^ (2 : ℕ) * R := by
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
    (x ^ (u + b * clock l) * (A + B * D) * H / G) ^ (2 : ℕ) =
        (x ^ (u + b * clock l) * H / G) ^ (2 : ℕ) *
          (A ^ (2 : ℕ) + 2 * A * B * D + B ^ (2 : ℕ) * D ^ (2 : ℕ)) := by ring
    _ = _ := by
      rw [hD]
      dsimp [A, B, H, G, D, R, C, Q, t]
      ring

/-- The complete literal EDQ block has one signed residual amplitude.  The source endpoint and
the former source--deviation cross term combine linearly with the same future-cofactor total
whose square is the non-clock lcm energy. -/
theorem truncatedDivisorBlockKernel_eq_source_futureCofactor
    (N l u b : ℕ) (x : ℝ) (hlN : l < N) :
    truncatedDivisorBlockKernel N l u b x =
      (x ^ (u + b * clock l) *
        ((1 - x ^ clock N) * pairedMoebiusSource N (u + b * clock l) +
          x ^ clock (l + 1) * (1 - x ^ clock (l + 1)) *
            ∑ m ∈ futureResidualCarrier N (l + 1),
              ∑ r ∈ futureOldCofactorCarrier N (l + 1) m,
                clockResidualBetaWeight (l + 1) (u + b * clock l + 1)
                  (canonicalClockRatio N (l + 1) - 1) x (m * r)) *
        (1 - x ^ clock N)⁻¹) /
    (∑ a ∈ range (clock (l + 1)), x ^ a) := by
  unfold truncatedDivisorBlockKernel
  have hdeviation :
      (∑ s ∈ range (canonicalClockRatio N (l + 1)),
        x ^ (s * clock (l + 1)) *
          ((clock (l + 1) : ℝ) *
              ∑ d ∈ Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ) -
            ∑ k ∈ Ioc (u + b * clock l + s * clock (l + 1) + 1)
              (u + b * clock l + (s + 1) * clock (l + 1) + 1),
              truncMoebiusDivisorSum N k)) =
        (1 - x ^ clock (l + 1)) *
          ∑ m ∈ futureResidualCarrier N (l + 1),
            ∑ r ∈ futureOldCofactorCarrier N (l + 1) m,
              clockResidualBetaWeight (l + 1) (u + b * clock l + 1)
                (canonicalClockRatio N (l + 1) - 1) x (m * r) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (selectedRefinementBlock_betaDeviation_eq_childClockFactor_futureCofactor_sum
        N l u b x hlN)
  rw [hdeviation]
  ring

/-- On every physical beta coordinate, the actual canonical child block is the same explicit
source-plus-future-cofactor scalar.  This carries the rank-one EDQ reduction into the literal
resolvent integrand used by the drift energy. -/
theorem canonicalRefinementBlockKernel_eq_source_futureCofactor
    (N l u b : ℕ) (x : ℝ) (hlN : l < N) (hx : 0 ≤ x) :
    canonicalRefinementBlockKernel N l u b x =
      (x ^ (u + b * clock l) *
        ((1 - x ^ clock N) * pairedMoebiusSource N (u + b * clock l) +
          x ^ clock (l + 1) * (1 - x ^ clock (l + 1)) *
            ∑ m ∈ futureResidualCarrier N (l + 1),
              ∑ r ∈ futureOldCofactorCarrier N (l + 1) m,
                clockResidualBetaWeight (l + 1) (u + b * clock l + 1)
                  (canonicalClockRatio N (l + 1) - 1) x (m * r)) *
        (1 - x ^ clock N)⁻¹) /
      (∑ a ∈ range (clock (l + 1)), x ^ a) := by
  rw [canonicalRefinementBlockKernel_eq_truncatedDivisorBlockKernel N l u b hlN x hx,
    truncatedDivisorBlockKernel_eq_source_futureCofactor N l u b x hlN]

/-- The terminal child block closes exactly.  At the last refinement its sole beta coordinate
is the joint-clock predecessor, where the complete paired Möbius source vanishes.  This is the
endpoint condition available for a signed summation-by-parts law across refinement time. -/
theorem terminalRefinementBlockKernel_eq_zero (n : ℕ) (x : ℝ) :
    canonicalRefinementBlockKernel (n + 1) n (clock n - 1)
      (clock (n + 1) / clock n - 1) x = 0 := by
  classical
  rw [canonicalRefinementBlockKernel_eq_canonical_finite_kernel]
  have hratio : canonicalClockRatio (n + 1) (n + 1) = 1 := by
    rw [canonicalClockRatio_eq_div_of_le (n + 1) (n + 1) le_rfl]
    exact Nat.div_self (clock_pos (n + 1))
  rw [hratio]
  simp only [Fin.sum_univ_one, Fin.val_zero, Nat.zero_mul, pow_zero, one_mul]
  have hclock : (clock (n + 1) / clock n) * clock n = clock (n + 1) :=
    Nat.div_mul_cancel (clock_dvd (Nat.le_succ n))
  have hclockpos : 0 < clock n := clock_pos n
  have hle : clock n ≤ clock (n + 1) :=
    Nat.le_of_dvd (clock_pos (n + 1)) (clock_dvd (Nat.le_succ n))
  have hindex :
      clock n - 1 + (clock (n + 1) / clock n - 1) * clock n = clock (n + 1) - 1 := by
    calc
      clock n - 1 + (clock (n + 1) / clock n - 1) * clock n =
          clock n - 1 + ((clock (n + 1) / clock n) * clock n - clock n) := by
            rw [Nat.sub_mul]
            simp
      _ = clock n - 1 + (clock (n + 1) - clock n) := by rw [hclock]
      _ = clock (n + 1) - 1 := by omega
  rw [hindex]
  have hsource : pairedMoebiusSource (n + 1) (clock (n + 1) - 1 + 0) = 0 := by
    simpa using pairedMoebiusSource_clock_pred_eq_zero (n + 1)
  rw [hsource]
  ring

end RHTower.DeletionResidueMartingale
