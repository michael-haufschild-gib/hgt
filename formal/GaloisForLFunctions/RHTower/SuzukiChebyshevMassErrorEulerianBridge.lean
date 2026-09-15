import GaloisForLFunctions.RHTower.SuzukiAnchoredCesaroScaleConnection
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevDrift

/-!
# Eulerian prime--continuum form of the Suzuki mass-error current

The corrected Chebyshev mass-error current is exactly its finite historical sum of literal
prime-minus-continuum increments. This removes the anchored averaging layer from the SP-E source
gate: moderation is precisely signed cancellation in the displayed Eulerian sum.
-/

open scoped BigOperators

namespace GaloisForLFunctions.RHTower

open _root_.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Exact Eulerian form of the corrected Chebyshev mass-error current. The summand is the
literal Suzuki prime atom less the exact continuum square-root increment, and the coefficient is
the checkpoint's historical weight. -/
theorem suzukiChebyshevMassErrorCesaroDefect_eq_weightedPrimeIncrements
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiChebyshevMassErrorCesaroDefect N =
      (∑ k ∈ Finset.Ico 2 (N + 1), ((k + 1 : ℕ) : ℝ) *
        (RiemannGaussian.suzukiPrimeWeight (k - 1) -
          2 * ((((k + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) -
            ((k : ℕ) : ℝ) ^ (1 / 2 : ℝ)))) / (N + 1 : ℕ) := by
  rw [suzukiChebyshevMassErrorCesaroDefect_eq_highPass]
  have hsum :
      ∑ k ∈ Finset.Ico 2 (N + 1), ((k + 1 : ℕ) : ℝ) *
          (RiemannGaussian.suzukiChebyshevWeightedMassError ((k + 1 : ℕ) : ℝ) -
            RiemannGaussian.suzukiChebyshevWeightedMassError (k : ℝ)) =
        ((N + 1 : ℕ) : ℝ) *
            RiemannGaussian.suzukiChebyshevWeightedMassError ((N + 1 : ℕ) : ℝ) -
          (3 * RiemannGaussian.suzukiChebyshevWeightedMassError ((2 : ℕ) : ℝ) +
            ∑ j ∈ Finset.Ico 3 (N + 1),
              RiemannGaussian.suzukiChebyshevWeightedMassError (j : ℝ)) := by
    induction N, hN using Nat.le_induction with
    | base => norm_num; ring
    | succ N hN ih =>
        rw [Finset.sum_Ico_succ_top (by omega : 2 ≤ N + 1),
          Finset.sum_Ico_succ_top (by omega : 3 ≤ N + 1), ih]
        push_cast
        ring
  change anchoredCesaroHighPass
      (fun j => RiemannGaussian.suzukiChebyshevWeightedMassError (j : ℝ)) N = _
  rw [anchoredCesaroHighPass, anchoredCesaroPotential]
  have hden : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hden]
  calc
    _ = ∑ k ∈ Finset.Ico 2 (N + 1), ((k + 1 : ℕ) : ℝ) *
          (RiemannGaussian.suzukiChebyshevWeightedMassError ((k + 1 : ℕ) : ℝ) -
            RiemannGaussian.suzukiChebyshevWeightedMassError (k : ℝ)) := by
      nlinarith [hsum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
      have hstep := RiemannGaussian.suzukiChebyshevWeightedMassError_nat_succ (k - 1)
      have hprevious : k - 1 + 1 = k := by omega
      have hnext : k - 1 + 2 = k + 1 := by omega
      rw [hprevious, hnext] at hstep
      simpa using congrArg (fun z : ℝ => ((k + 1 : ℕ) : ℝ) * z) hstep

end

end GaloisForLFunctions.RHTower
