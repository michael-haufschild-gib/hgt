import GaloisForLFunctions.RHTower.Sieve.BalancedPairs
import GaloisForLFunctions.RHTower.Sieve.BlockMean

/-!
# The bilinear all-interval theorem as an interface

Matomäki–Radziwiłł's Theorem 2 says that for a real multiplicative `f` with `|f| ≤ 1` the balanced
pair sum is the square of the block mean, up to an error that vanishes in the card's parameter
regime:

    pairSum f x h / (h·√x·log 2)  -  (blockMean f x)²  →  0.

That statement is the card's `(5)` and is the only input of the whole argument that is not proved
here.  It is recorded as a `Prop` so that every consequence can be derived and machine-checked
against it.

Given the interface at `μ` and at `μ²`, together with the two block-mean limits already proved, the
card's `(7)` follows: both sign classes have density `D²/2`.
-/

namespace RHTower.Sieve

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

/-- The balanced pair sum of an arbitrary weight. -/
noncomputable def pairSum (f : ℕ → ℝ) (x h : ℝ) : ℝ :=
  ∑ q ∈ balancedPairs x h, f q.1 * f q.2

/-- **The bilinear all-interval theorem**, for one weight and one window law. -/
def MRBilinear (f : ℕ → ℝ) (hh : ℝ → ℝ) : Prop :=
  Tendsto (fun x => pairSum f x (hh x) / (hh x * Real.sqrt x * Real.log 2)
      - (blockMean f x) ^ 2) atTop (𝓝 0)

/-- The signed pair sum is the pair sum of `μ`. -/
theorem signedPairSum_eq_pairSum (x h : ℝ) :
    signedPairSum x h = pairSum (fun n : ℕ => ((μ n : ℤ) : ℝ)) x h := rfl

/-- The squarefree pair count is the pair sum of `μ²`. -/
theorem squarefreePairCount_eq_pairSum (x h : ℝ) :
    squarefreePairCount x h = pairSum (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ 2) x h := rfl

/-- **The signed pair sum vanishes**, given the interface at `μ`. -/
theorem tendsto_signedPairSum_of_MR {hh : ℝ → ℝ}
    (hMR : MRBilinear (fun n : ℕ => ((μ n : ℤ) : ℝ)) hh) :
    Tendsto (fun x => signedPairSum x (hh x) / (hh x * Real.sqrt x * Real.log 2))
      atTop (𝓝 0) := by
  have hmean := tendsto_blockMean_moebius
  have hsq : Tendsto (fun x => (blockMean (fun n : ℕ => ((μ n : ℤ) : ℝ)) x) ^ 2)
      atTop (𝓝 0) := by
    have := hmean.pow 2
    simpa using this
  have := hMR.add hsq
  rw [zero_add] at this
  refine this.congr fun x => ?_
  rw [signedPairSum_eq_pairSum]
  ring

/-- **The squarefree pair count has density `D²`**, given the interface at `μ²`. -/
theorem tendsto_squarefreePairCount_of_MR {hh : ℝ → ℝ}
    (hMR : MRBilinear (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ 2) hh) :
    Tendsto (fun x => squarefreePairCount x (hh x) / (hh x * Real.sqrt x * Real.log 2))
      atTop (𝓝 (squarefreeDensity ^ 2)) := by
  have hmean := tendsto_blockMean_moebius_sq
  have hsq : Tendsto (fun x => (blockMean (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ 2) x) ^ 2)
      atTop (𝓝 (squarefreeDensity ^ 2)) := hmean.pow 2
  have hadd := hMR.add hsq
  rw [zero_add] at hadd
  refine hadd.congr fun x => ?_
  rw [squarefreePairCount_eq_pairSum]
  ring

/-- **Card equation (7).**  Both sign classes carry half the squarefree pair density. -/
theorem tendsto_signClass_of_MR {hh : ℝ → ℝ}
    (hMR1 : MRBilinear (fun n : ℕ => ((μ n : ℤ) : ℝ)) hh)
    (hMR2 : MRBilinear (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ 2) hh) :
    Tendsto (fun x => signClassCount x (hh x) 1 / (hh x * Real.sqrt x * Real.log 2))
        atTop (𝓝 (squarefreeDensity ^ 2 / 2))
      ∧ Tendsto (fun x => signClassCount x (hh x) (-1) / (hh x * Real.sqrt x * Real.log 2))
        atTop (𝓝 (squarefreeDensity ^ 2 / 2)) :=
  tendsto_signClass_of_limits (N := fun x => hh x * Real.sqrt x * Real.log 2)
    (tendsto_squarefreePairCount_of_MR hMR2) (tendsto_signedPairSum_of_MR hMR1)

end RHTower.Sieve
