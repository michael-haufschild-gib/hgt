import GaloisForLFunctions.ArithmeticCorrelationGeometry.SubpowerReceiverEnergyTranslatesZeros
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.SignedAveragedContinuationAndTheZeroWidthBand
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.Real.Cardinality

/-!
# The escape alternative

At damping `ε > 0` the damped Möbius receiver either **admits** — its energy
`E_ε(T) = Σ_{n ≤ T} A_ε(n)²/(n(n+1))` stays bounded — or **escapes**. This file shows that escape is
exactly the presence of zeros of `ζ` right of `½ + ε`, up to a countable set of dampings.

* **An uncancelled zero forces escape** (`not_admits_of_uncancelled_zero`,
  `not_energy_le_rpow_of_uncancelled_zero`). If `ζ(ρ) = 0`, `½ + ε < Re ρ < 1` and
  `ζ(ρ − ε) ≠ 0`, the energy is unbounded; more precisely it is `O(T^κ)` for no
  `κ < 2(Re ρ − ε) − 1`. This is the pole of the Mellin pairing at `ρ − ε` (ACG).
* **Escape lies below the zero width** (`le_of_not_admits`): an escaping damping has
  `ε ≤ Θ − ½`, `Θ` the zero abscissa (ACE).
* **Cancellation is countable** (`countable_cancellingDampings`). The dampings `ε` at which some zero
  `ρ` has `ζ(ρ − ε) = 0` form a countable set: the zeros of `ζ` are countable.
* **The escape set** (`not_admits_of_mem_Ioo_of_not_mem`). Every `ε ∈ (0, Θ − ½)` outside that
  countable set escapes. So the escaping dampings lie in `(0, Θ − ½]` and fill `(0, Θ − ½)` up to a
  countable set.
* **RH is the absence of escape** (`riemannHypothesis_iff_forall_admits`): RH holds iff the
  receiver admits at every damping `ε > 0`.

This is the second half of the report's Q1: escape at `ε` is the presence of zeros right of
`½ + ε`. Under RH there is no escape and completeness is empty; off RH every damping below the zero
width escapes, apart from countably many, and the structure of the escape states is the
energy-split question (`TheEscapeCompletenessCriterion`).
-/

open Set Filter Topology
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy (Admits dampedMobiusEnergy
  admits_dampedMobiusEnergy_of_zetaZeroAbscissa_sub_half_lt)
open GaloisForLFunctions.ArithmeticCorrelationGeometry (riemannZeta_sub_eq_zero_of_energy_growth)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- **Polynomial energy is too small for an uncancelled zero**: if `ζ(ρ) = 0`,
`(1 + κ)/2 + ε < Re ρ < 1` and `ζ(ρ − ε) ≠ 0`, the energy is not `O((T+1)^κ)`. -/
theorem not_energy_le_rpow_of_uncancelled_zero {ε : ℝ} (hε : 0 < ε) {κ : ℝ} (hκ : 0 ≤ κ)
    {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hre : (1 + κ) / 2 + ε < ρ.re) (hre1 : ρ.re < 1)
    (hne : riemannZeta (ρ - ε) ≠ 0) :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, dampedMobiusEnergy ε T ≤ C * ((T : ℝ) + 1) ^ κ := by
  rintro ⟨C, hC, hE⟩
  exact hne (riemannZeta_sub_eq_zero_of_energy_growth hε hC hκ hE hρ hre hre1)

/-- **An uncancelled zero right of `½ + ε` forces escape.** -/
theorem not_admits_of_uncancelled_zero {ε : ℝ} (hε : 0 < ε) {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hre : 1 / 2 + ε < ρ.re) (hre1 : ρ.re < 1) (hne : riemannZeta (ρ - ε) ≠ 0) :
    ¬ Admits dampedMobiusEnergy ε := by
  rintro ⟨B, hB⟩
  refine not_energy_le_rpow_of_uncancelled_zero hε le_rfl hρ (by linarith) hre1 hne
    ⟨max B 0, le_max_right _ _, fun T => ?_⟩
  rw [Real.rpow_zero, mul_one]
  exact (hB T).trans (le_max_left _ _)

/-- **Escape lies below the zero width**: an escaping damping has `ε ≤ Θ − ½`. -/
theorem le_of_not_admits {ε : ℝ} (h : ¬ Admits dampedMobiusEnergy ε) :
    ε ≤ RHTower.zetaZeroAbscissa - 1 / 2 := by
  by_contra hlt
  exact h (admits_dampedMobiusEnergy_of_zetaZeroAbscissa_sub_half_lt (not_le.mp hlt))

/-- The dampings at which some zero `ρ` of `ζ` is cancelled, `ζ(ρ − ε) = 0`. -/
def cancellingDampings : Set ℝ :=
  {ε : ℝ | ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ riemannZeta (ρ - ε) = 0}

theorem countable_riemannZetaZeros : riemannZetaZeros.Countable :=
  (HereditarilyLindelofSpace.isLindelof riemannZetaZeros).countable_of_isDiscrete
    isDiscrete_riemannZetaZeros

/-- **Cancellation is countable.** -/
theorem countable_cancellingDampings : cancellingDampings.Countable := by
  have hset : cancellingDampings =
      ⋃ ρ ∈ riemannZetaZeros, (fun ε : ℝ => ρ - (ε : ℂ)) ⁻¹' riemannZetaZeros := by
    ext ε
    simp [cancellingDampings, mem_riemannZetaZeros]
  rw [hset]
  refine countable_riemannZetaZeros.biUnion fun ρ _ => countable_riemannZetaZeros.preimage ?_
  intro a b hab
  have := congrArg Complex.re hab
  simpa using this

/-- **The escape set**: every `ε ∈ (0, Θ − ½)` outside the countable set of cancelling dampings
escapes. -/
theorem not_admits_of_mem_Ioo_of_not_mem {ε : ℝ}
    (hε : ε ∈ Ioo 0 (RHTower.zetaZeroAbscissa - 1 / 2)) (hc : ε ∉ cancellingDampings) :
    ¬ Admits dampedMobiusEnergy ε := by
  obtain ⟨ρ, hρ, hre1, hre⟩ :=
    RHTower.exists_zetaZero_mem_openStrip_lt_re (b := 1 / 2 + ε) (by linarith [hε.2])
  exact not_admits_of_uncancelled_zero hε.1 hρ hre hre1 fun h0 => hc ⟨ρ, hρ, h0⟩

/-- **RH is the absence of escape**: RH holds iff the damped Möbius receiver admits at every
damping `ε > 0`. -/
theorem riemannHypothesis_iff_forall_admits :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → Admits dampedMobiusEnergy ε := by
  constructor
  · intro hRH ε hε
    have hΘ := RHTower.zetaZeroAbscissa_eq_half_iff_riemannHypothesis.mpr hRH
    exact admits_dampedMobiusEnergy_of_zetaZeroAbscissa_sub_half_lt (by linarith)
  · intro hadm
    by_contra hRH
    have hΘ : 1 / 2 < RHTower.zetaZeroAbscissa :=
      lt_of_le_of_ne RHTower.half_le_zetaZeroAbscissa fun h =>
        hRH (RHTower.zetaZeroAbscissa_eq_half_iff_riemannHypothesis.mp h.symm)
    -- an interval is not countable, so it meets the complement of the cancelling dampings
    obtain ⟨ε, hεI, hεc⟩ : ∃ ε ∈ Ioo 0 (RHTower.zetaZeroAbscissa - 1 / 2),
        ε ∉ cancellingDampings := by
      by_contra hall
      have hsub : Ioo 0 (RHTower.zetaZeroAbscissa - 1 / 2) ⊆ cancellingDampings :=
        fun ε hε => by_contra fun hn => hall ⟨ε, hε, hn⟩
      have := (countable_cancellingDampings.mono hsub)
      rw [Real.Ioo_countable_iff] at this
      linarith
    exact not_admits_of_mem_Ioo_of_not_mem hεI hεc (hadm ε hεI.1)

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
