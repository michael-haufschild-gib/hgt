import GaloisForLFunctions.RHTower.SuzukiAnchoredCesaroScaleConnection
import GaloisForLFunctions.RHTower.BlaschkeLocalizedClockAsymptotic

/-!
# Square-root PNT envelopes cannot close the Suzuki Cesàro source

The completed Suzuki transition source is already identified in the corpus with an anchored
Cesàro high-pass of the weighted Chebyshev mass error, plus explicit retained corrections.  Its
aligned Gamma energy is an exact squared readout, and boundedness of that energy is equivalent to
RH.  A tempting source-first proof would therefore try to turn the unconditional square-root
envelope and sublinearity of a PNT remainder into uniform boundedness of the high-pass.

This module kills that entire inference class.  The maximally regular witness `a n = sqrt n` is
nonnegative, monotone, pointwise bounded by the square-root envelope, and sublinear.  Nevertheless
its literal Suzuki anchored high-pass tends to positive infinity.  The proof uses the corpus's
sharp unit-Riesz prefix inequality

`3 * sum_{r=1}^N sqrt r <= 2 * (N+1) * sqrt (N+1)`

to obtain the explicit lower envelope `sqrt (N+1) / 3 - 2`.

Consequently the common HB/FZZ-P/RBH/PW-B Ward source cannot be discharged from magnitude
control, PNT sublinearity, positivity, or monotone regularity alone.  Any surviving proof must use
genuinely signed arithmetic cancellation across checkpoints (or a stronger arithmetic invariant
that implies it).  No computation, hypothesis, or new axiom is used.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.RHTower

open _root_.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Canonical hostile witness at the exact unconditional square-root envelope. -/
def suzukiSqrtEnvelopeWitness (n : ℕ) : ℝ :=
  Real.sqrt (n : ℝ)

/-- The anchored history tail is contained in the corpus's unit-Riesz square-root prefix. -/
theorem suzukiSqrtEnvelopeWitness_tail_le_prefix {N : ℕ} (hN : 2 ≤ N) :
    (∑ j ∈ Finset.Ico 3 (N + 1), suzukiSqrtEnvelopeWitness j) ≤
      unitRieszSqrtPrefixMass N := by
  rw [unitRieszSqrtPrefixMass_eq_sum_Ico_one]
  change (∑ j ∈ Finset.Ico 3 (N + 1), suzukiSqrtEnvelopeWitness j) ≤
    ∑ j ∈ Finset.Ico 1 (N + 1), suzukiSqrtEnvelopeWitness j
  rw [← Finset.sum_Ico_consecutive (fun j => suzukiSqrtEnvelopeWitness j)
    (by omega : 1 ≤ 3) (by omega : 3 ≤ N + 1)]
  have hhead : 0 ≤ ∑ j ∈ Finset.Ico 1 3, suzukiSqrtEnvelopeWitness j := by
    apply Finset.sum_nonneg
    intro j hj
    exact Real.sqrt_nonneg _
  linarith

/-- The sharp square-root prefix bound controls the witness's anchored potential from above. -/
theorem suzukiSqrtEnvelopeWitness_potential_le {N : ℕ} (hN : 2 ≤ N) :
    anchoredCesaroPotential suzukiSqrtEnvelopeWitness N ≤
      (2 / 3 : ℝ) * Real.sqrt ((N : ℝ) + 1) + 2 := by
  have htail := suzukiSqrtEnvelopeWitness_tail_le_prefix hN
  have hprefix := unitRieszSqrtPrefixMass_upper N
  have hsqrt2 : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hden : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [anchoredCesaroPotential]
  simp only [suzukiSqrtEnvelopeWitness, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  simp only [suzukiSqrtEnvelopeWitness] at htail
  apply (div_le_iff₀ hden).2
  change 3 * Real.sqrt (2 : ℝ) +
      (∑ j ∈ Finset.Ico 3 (N + 1), Real.sqrt (j : ℝ)) ≤
    ((2 / 3 : ℝ) * Real.sqrt ((N : ℝ) + 1) + 2) * ((N : ℝ) + 1)
  have hNreal : (3 : ℝ) ≤ (N : ℝ) + 1 := by
    exact_mod_cast (show 3 ≤ N + 1 by omega)
  nlinarith

/-- The witness current has a cofinal square-root lower envelope. -/
theorem suzukiSqrtEnvelopeWitness_highPass_lower {N : ℕ} (hN : 2 ≤ N) :
    (1 / 3 : ℝ) * Real.sqrt ((N : ℝ) + 1) - 2 ≤
      anchoredCesaroHighPass suzukiSqrtEnvelopeWitness N := by
  have hpot := suzukiSqrtEnvelopeWitness_potential_le hN
  rw [anchoredCesaroHighPass]
  change (1 / 3 : ℝ) * Real.sqrt ((N : ℝ) + 1) - 2 ≤
    Real.sqrt (((N + 1 : ℕ) : ℝ)) - anchoredCesaroPotential suzukiSqrtEnvelopeWitness N
  push_cast
  linarith

theorem tendsto_suzukiSqrtEnvelopeWitness_lower_atTop :
    Tendsto (fun N : ℕ => (1 / 3 : ℝ) * Real.sqrt ((N : ℝ) + 1) - 2)
      atTop atTop := by
  have hshift : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt ((N : ℝ) + 1)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hshift
  have hscale : Tendsto (fun N : ℕ => (1 / 3 : ℝ) * Real.sqrt ((N : ℝ) + 1))
      atTop atTop := hsqrt.const_mul_atTop (by norm_num)
  simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-2) hscale

/-- Despite all envelope regularity, the exact Suzuki anchored current diverges. -/
theorem tendsto_suzukiSqrtEnvelopeWitness_highPass_atTop :
    Tendsto (anchoredCesaroHighPass suzukiSqrtEnvelopeWitness) atTop atTop := by
  apply tendsto_atTop_mono' atTop
    (show (fun N : ℕ => (1 / 3 : ℝ) * Real.sqrt ((N : ℝ) + 1) - 2) ≤ᶠ[atTop]
      anchoredCesaroHighPass suzukiSqrtEnvelopeWitness from ?_)
    tendsto_suzukiSqrtEnvelopeWitness_lower_atTop
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact suzukiSqrtEnvelopeWitness_highPass_lower hN

/-- Abstract producer strategy being ruled out: square-root envelope plus sublinearity, even with
nonnegativity and monotonicity, forces uniform boundedness of the Suzuki current. -/
def SuzukiSquareRootEnvelopeSublinearForcesBoundedHighPass : Prop :=
  ∀ a : ℕ → ℝ,
    (∀ n, 0 ≤ a n) →
    Monotone a →
    (∀ n, |a n| ≤ Real.sqrt (n : ℝ)) →
    Tendsto (fun n => a n / (n : ℝ)) atTop (𝓝 0) →
    ∃ C : ℝ, ∀ N, |anchoredCesaroHighPass a N| ≤ C

theorem suzukiSqrtEnvelopeWitness_abs_le (n : ℕ) :
    |suzukiSqrtEnvelopeWitness n| ≤ Real.sqrt (n : ℝ) := by
  unfold suzukiSqrtEnvelopeWitness
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]

theorem suzukiSqrtEnvelopeWitness_nonnegative (n : ℕ) :
    0 ≤ suzukiSqrtEnvelopeWitness n :=
  Real.sqrt_nonneg _

theorem suzukiSqrtEnvelopeWitness_monotone :
    Monotone suzukiSqrtEnvelopeWitness := by
  intro m n hmn
  apply Real.sqrt_le_sqrt
  exact_mod_cast hmn

theorem tendsto_suzukiSqrtEnvelopeWitness_div_natCast_zero :
    Tendsto (fun n => suzukiSqrtEnvelopeWitness n / (n : ℝ)) atTop (𝓝 0) := by
  simpa [suzukiSqrtEnvelopeWitness] using
    _root_.RHTower.tendsto_sqrt_natCast_div_natCast_atTop_zero

/-- The envelope/sublinearity producer implication is false. -/
theorem not_suzukiSquareRootEnvelopeSublinearForcesBoundedHighPass :
    ¬ SuzukiSquareRootEnvelopeSublinearForcesBoundedHighPass := by
  intro hroute
  obtain ⟨C, hC⟩ := hroute suzukiSqrtEnvelopeWitness
    suzukiSqrtEnvelopeWitness_nonnegative
    suzukiSqrtEnvelopeWitness_monotone
    suzukiSqrtEnvelopeWitness_abs_le
    tendsto_suzukiSqrtEnvelopeWitness_div_natCast_zero
  have hevent : ∀ᶠ N in atTop,
      C < anchoredCesaroHighPass suzukiSqrtEnvelopeWitness N :=
    tendsto_suzukiSqrtEnvelopeWitness_highPass_atTop.eventually (eventually_gt_atTop C)
  obtain ⟨N, hN⟩ := hevent.exists
  have habs := le_abs_self (anchoredCesaroHighPass suzukiSqrtEnvelopeWitness N)
  linarith [hC N]

/-- Closed route-class capstone.  The common Suzuki Ward source cannot be obtained from its known
PNT magnitude envelope and sublinearity without new signed arithmetic cancellation. -/
theorem suzukiPNTEnvelopeCesaroProducerRouteKilled :
    ¬ SuzukiSquareRootEnvelopeSublinearForcesBoundedHighPass :=
  not_suzukiSquareRootEnvelopeSublinearForcesBoundedHighPass

end

end GaloisForLFunctions.RHTower
