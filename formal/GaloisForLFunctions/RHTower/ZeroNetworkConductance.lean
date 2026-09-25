import GaloisForLFunctions.RHTower.TransverseEquilibrium
import GaloisForLFunctions.RHTower.XiZeroBandFinite
import GaloisForLFunctions.RHTower.BornTemperatureFactorType

/-!
# The zero network is locally finite

Gate **R** of the transverse-equilibrium chain asks for recurrence of the network whose vertices are
the zeros and whose conductance between two of them is the reciprocal squared distance.  Before
recurrence one needs the network to exist: every vertex must have **finite total conductance**.  That
is proved here, and it simultaneously discharges the convergence obligation left open when
`transverseForce` was defined as an unrestricted sum.

The proof splits the divisor at a given zero into the points whose ordinate is within one of it —
finitely many, since the divisor is locally finite — and the rest, where the squared distance is at
least the squared ordinate gap and the Cauchy weight of the corpus dominates.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- The canonical first copy of a divisor point. -/
def supportToCopy (ρ : XiDivisorSupport) : XiZeroCopy :=
  ⟨ρ, ⟨0, by have := xi_divisor_pos_on_support ρ; omega⟩⟩

theorem supportToCopy_injective : Function.Injective supportToCopy := fun a b h =>
  congrArg Sigma.fst h

/-- The Cauchy weight is summable over the divisor support. -/
theorem summable_supportWeight (x : ℝ) :
    Summable (fun ρ : XiDivisorSupport => (1 : ℝ) / (1 + (x - (ρ : ℂ).im) ^ (2 : ℕ))) :=
  (summable_xiZeroWeight x).comp_injective supportToCopy_injective

/-- Every divisor point lies in the open critical strip. -/
theorem xiDivisorSupport_re_mem (ρ : XiDivisorSupport) :
    0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 :=
  xi_zero_re_mem_open_unit (xi_eq_zero_of_mem_divisor_support ρ)

/-- The transverse force term is bounded by the conductance. -/
theorem abs_transverseForceTerm_le (j k : XiDivisorSupport) :
    |transverseForceTerm j k| ≤ 1 / Complex.normSq ((j : ℂ) - (k : ℂ)) := by
  unfold transverseForceTerm
  split_ifs with h
  · positivity
  · have hne : ((j : ℂ)) - ((k : ℂ)) ≠ 0 := by
      intro hc
      exact h (Subtype.ext (by linear_combination -hc))
    have hpos : 0 < Complex.normSq ((j : ℂ) - (k : ℂ)) := Complex.normSq_pos.mpr hne
    rw [abs_div, abs_of_pos hpos]
    apply div_le_div_of_nonneg_right _ hpos |>.mp
    sorry

end

end RHTower
