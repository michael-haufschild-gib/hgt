import GaloisForLFunctions.RHTower.Sieve.BudgetLimit

/-!
# The short-interval mean square for the Möbius function

The Möbius function has square-root cancellation on average over short intervals of length
`exp((log x)^β)` for every `β` in the admissible window.  This is the mean-square form of the
Matomäki–Radziwiłł theorem, and it is unconditional.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- **The short-interval mean square for the Möbius function.**  For every admissible pair of
exponents the fibre mean square of `μ` over windows of length `exp((log x)^β)` is negligible. -/
theorem averagedMeanSquare_moebius_cardLength {β : ℝ} (γ : ℝ) (hβ0 : 9 / 10 < β) (hβ1 : β < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hγβ0 : 9 / 10 < γ * β) (hγβ1 : γ * β < 1) :
    AveragedMeanSquare (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℝ))
      (cardLength β) := by
  have hβ0' : (0 : ℝ) < β := by linarith
  refine averagedMeanSquare_moebius_of_omegaBudget
    (zlo := siftStart (γ * β)) (zhi := ladderTop β γ)
    (cardLength_le_sqrt hβ0' hβ1)
    (Filter.Eventually.of_forall fun x => cardLength_pos β x)
    ?_ ?_ (tendsto_normalised_omegaBudget hβ0 hβ1 hγ0 hγ1 hγβ0 hγβ1)
  · filter_upwards [eventually_ladderTop_facts hβ0' hγ0 hγ1 hγβ1] with x hfacts
    exact hfacts.2.2
  · filter_upwards [(tendsto_ladderMass hβ0' hγ0 hγ1 hγβ1).eventually_gt_atTop (0 : ℝ)]
      with x hx
    exact hx

/-- **Matomäki–Radziwiłł for the Möbius function**, at the exponent `99/100`. -/
theorem averagedMeanSquare_moebius :
    AveragedMeanSquare (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℝ))
      (cardLength (99 / 100)) :=
  averagedMeanSquare_moebius_cardLength (99 / 100) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end

end RHTower.Sieve
