import GaloisForLFunctions.RHTower.FZZCigarParityLinearReplicaAreaHolonomySelector
import GaloisForLFunctions.HTGeometry.FZZCigarTorusReplicaNeutrality

/-!
# FZZ charge-balanced holonomy-only area no-go

The full neutral FZZ screening condensate cannot be truncated: every depth has nonzero
coefficient when the cosmological constant is nonzero.  This file therefore treats an arbitrary
infinite tower, with external reporter charges included in each sector's total charge balance.

For the pure multiplicative holonomy class, the result is exact.  The replica product rule turns
each sector into one positive and one negative character monomial.  Total charge balance makes
their exponents equal, while the higher-genus cigar identity `β γ = 1` cancels the common power.
Every term, and hence the entire `tsum` without a convergence premise, is twist-independent.

Consequently no scalar predicate of this tower—including a fixed passivity inequality—can select
`twist.im = 0`.  This kills the FZZ-P chain

`Mellin twist → charge-balanced holonomy-only area response → passivity → critical line → RH`.

It does not kill full cigar dynamics.  The positive survivor must contain non-character twist
dependence (for example twisted determinants, ghosts, prime forms, or branch/localization data)
and must retain or localize the marked Mellin twist before full Jacobian integration.
-/

open Complex

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry.FZZCigar

/-- Screening and reporter powers whose total positive and negative holonomy charges agree. -/
structure FZZChargeBalancedHolonomySector where
  screeningPlus : ℕ
  screeningMinus : ℕ
  reporterPlus : ℕ
  reporterMinus : ℕ
  balance : screeningPlus + reporterPlus = screeningMinus + reporterMinus

/-- Replica-area tangent of one pure multiplicative holonomy sector.

`plusLogDerivative` and `minusLogDerivative` are twist-independent logarithmic tangent data.
Any determinant, ghost, prime-form, or branch dependence on the twist is deliberately outside
this class. -/
def fzzChargeBalancedHolonomyAreaTerm
    (sector : FZZChargeBalancedHolonomySector) (cycle : ℤ)
    (coefficient plusLogDerivative minusLogDerivative twist : ℂ) : ℂ :=
  let β := higherGenusBetaTwistMultiplier cycle twist
  let γ := higherGenusGammaTwistMultiplier cycle twist
  coefficient * β ^ sector.reporterPlus * γ ^ sector.reporterMinus *
    torusReplicaTangent
      (β ^ sector.screeningPlus) (γ ^ sector.screeningMinus)
      (plusLogDerivative * β ^ sector.screeningPlus)
      (minusLogDerivative * γ ^ sector.screeningMinus)

/-- Total charge balance cancels all pure β/γ holonomy dependence in one area sector. -/
theorem fzzChargeBalancedHolonomyAreaTerm_eq
    (sector : FZZChargeBalancedHolonomySector) (cycle : ℤ)
    (coefficient plusLogDerivative minusLogDerivative twist : ℂ) :
    fzzChargeBalancedHolonomyAreaTerm sector cycle coefficient
        plusLogDerivative minusLogDerivative twist =
      coefficient * (plusLogDerivative + minusLogDerivative) := by
  let β := higherGenusBetaTwistMultiplier cycle twist
  let γ := higherGenusGammaTwistMultiplier cycle twist
  have hβγ : β * γ = 1 := higherGenusBetaTwist_mul_gammaTwist cycle twist
  have hbalance : sector.reporterPlus + sector.screeningPlus =
      sector.reporterMinus + sector.screeningMinus := by
    simpa [Nat.add_comm] using sector.balance
  unfold fzzChargeBalancedHolonomyAreaTerm torusReplicaTangent
  dsimp only
  change coefficient * β ^ sector.reporterPlus * γ ^ sector.reporterMinus *
      (plusLogDerivative * β ^ sector.screeningPlus * γ ^ sector.screeningMinus +
        β ^ sector.screeningPlus *
          (minusLogDerivative * γ ^ sector.screeningMinus)) =
    coefficient * (plusLogDerivative + minusLogDerivative)
  calc
    _ = coefficient * (plusLogDerivative + minusLogDerivative) *
        (β ^ (sector.reporterPlus + sector.screeningPlus) *
          γ ^ (sector.reporterMinus + sector.screeningMinus)) := by
      rw [pow_add, pow_add]
      ring
    _ = coefficient * (plusLogDerivative + minusLogDerivative) *
        (β ^ (sector.reporterMinus + sector.screeningMinus) *
          γ ^ (sector.reporterMinus + sector.screeningMinus)) := by rw [hbalance]
    _ = coefficient * (plusLogDerivative + minusLogDerivative) := by
      rw [← mul_pow, hβγ, one_pow, mul_one]

/-- Infinite pure-holonomy screening tower. -/
def fzzChargeBalancedHolonomyAreaTower
    (sector : ℕ → FZZChargeBalancedHolonomySector) (cycle : ℤ)
    (coefficient plusLogDerivative minusLogDerivative : ℕ → ℂ)
    (twist : ℂ) : ℂ :=
  ∑' depth, fzzChargeBalancedHolonomyAreaTerm (sector depth) cycle
    (coefficient depth) (plusLogDerivative depth) (minusLogDerivative depth) twist

/-- The full tower is exactly twist-independent, without a convergence premise. -/
theorem fzzChargeBalancedHolonomyAreaTower_eq
    (sector : ℕ → FZZChargeBalancedHolonomySector) (cycle : ℤ)
    (coefficient plusLogDerivative minusLogDerivative : ℕ → ℂ)
    (twist : ℂ) :
    fzzChargeBalancedHolonomyAreaTower sector cycle coefficient
        plusLogDerivative minusLogDerivative twist =
      ∑' depth, coefficient depth *
        (plusLogDerivative depth + minusLogDerivative depth) := by
  apply tsum_congr
  intro depth
  exact fzzChargeBalancedHolonomyAreaTerm_eq
    (sector depth) cycle (coefficient depth) (plusLogDerivative depth)
      (minusLogDerivative depth) twist

/-- No scalar predicate of a charge-balanced pure-holonomy area tower can select real twists. -/
theorem not_fzzChargeBalancedHolonomyAreaTower_value_selector
    (sector : ℕ → FZZChargeBalancedHolonomySector) (cycle : ℤ)
    (coefficient plusLogDerivative minusLogDerivative : ℕ → ℂ)
    (P : ℂ → Prop) :
    ¬ ∀ twist : ℂ,
      P (fzzChargeBalancedHolonomyAreaTower sector cycle coefficient
          plusLogDerivative minusLogDerivative twist) ↔ twist.im = 0 := by
  intro hselector
  have hzero := hselector 0
  have hI := hselector Complex.I
  have hconst :
      fzzChargeBalancedHolonomyAreaTower sector cycle coefficient
          plusLogDerivative minusLogDerivative Complex.I =
        fzzChargeBalancedHolonomyAreaTower sector cycle coefficient
          plusLogDerivative minusLogDerivative 0 := by
    rw [fzzChargeBalancedHolonomyAreaTower_eq,
      fzzChargeBalancedHolonomyAreaTower_eq]
  have hpzero : P (fzzChargeBalancedHolonomyAreaTower sector cycle coefficient
      plusLogDerivative minusLogDerivative 0) := hzero.mpr (by simp)
  have hpI : P (fzzChargeBalancedHolonomyAreaTower sector cycle coefficient
      plusLogDerivative minusLogDerivative Complex.I) := by
    rw [hconst]
    exact hpzero
  have : Complex.I.im = 0 := hI.mp hpI
  norm_num at this

/-- In particular, no fixed norm bound turns this tower into the radial passivity selector. -/
theorem not_fzzChargeBalancedHolonomyAreaTower_passivity_selector
    (sector : ℕ → FZZChargeBalancedHolonomySector) (cycle : ℤ)
    (coefficient plusLogDerivative minusLogDerivative : ℕ → ℂ)
    (bound : ℝ) :
    ¬ ∀ twist : ℂ,
      ‖fzzChargeBalancedHolonomyAreaTower sector cycle coefficient
          plusLogDerivative minusLogDerivative twist‖ ≤ bound ↔ twist.im = 0 :=
  not_fzzChargeBalancedHolonomyAreaTower_value_selector sector cycle coefficient
    plusLogDerivative minusLogDerivative (fun value => ‖value‖ ≤ bound)

end

end RHTower
