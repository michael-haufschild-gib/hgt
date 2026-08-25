import GaloisForLFunctions.RHTower.KapustinGammaToeplitzPhase

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Phase-coordinate form of a nonzero Smirnov Toeplitz-kernel element.  Inner--outer
factorization gives a nondecreasing inner phase `α`; Kolmogorov's theorem makes the regularized
Hilbert transform of the outer logarithm sublinear. -/
structure SmirnovToeplitzPhaseWitness (γ : ℝ → ℝ) where
  innerPhase : ℝ → ℝ
  outerHilbertPhase : ℝ → ℝ
  innerPhase_monotone : Monotone innerPhase
  phase_balance : ∀ x, γ x + innerPhase x = outerHilbertPhase x
  outerHilbertPhase_sublinear_atTop :
    Tendsto (fun x => outerHilbertPhase x / x) atTop (nhds 0)

/-- Makarov--Poltoratski upper-density obstruction at `κ = 0`, in the exact phase criterion:
a Toeplitz phase whose excess over the exponential inner phase grows to `+∞` cannot have a
nonzero Smirnov kernel element. -/
theorem not_smirnovToeplitzPhaseWitness_of_sub_id_tendsto_atTop
    {γ : ℝ → ℝ}
    (hgrowth : Tendsto (fun x => γ x - x) atTop atTop) :
    ¬ Nonempty (SmirnovToeplitzPhaseWitness γ) := by
  rintro ⟨W⟩
  have houter : ∀ᶠ x : ℝ in atTop, W.outerHilbertPhase x / x < (1 / 4 : ℝ) :=
    W.outerHilbertPhase_sublinear_atTop.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hinner : ∀ᶠ x : ℝ in atTop, W.innerPhase 0 ≤ W.innerPhase x :=
    (eventually_ge_atTop 0).mono fun x hx => W.innerPhase_monotone hx
  have hxpos : ∀ᶠ x : ℝ in atTop, 0 < x := eventually_gt_atTop 0
  have hlarge : ∀ᶠ x : ℝ in atTop, 4 * |W.innerPhase 0| < x :=
    eventually_gt_atTop (4 * |W.innerPhase 0|)
  have hgrowth0 : ∀ᶠ x : ℝ in atTop, 0 < γ x - x :=
    hgrowth.eventually (eventually_gt_atTop 0)
  have hall : ∀ᶠ x : ℝ in atTop,
      W.outerHilbertPhase x / x < (1 / 4 : ℝ) ∧
      W.innerPhase 0 ≤ W.innerPhase x ∧ 0 < x ∧
      4 * |W.innerPhase 0| < x ∧ 0 < γ x - x := by
    filter_upwards [houter, hinner, hxpos, hlarge, hgrowth0] with x ho hi hx hl hg
    exact ⟨ho, hi, hx, hl, hg⟩
  obtain ⟨x, ho, hi, hx, hl, hg⟩ := hall.exists
  have houter_lt : W.outerHilbertPhase x < x / 4 :=
    by
      have := (div_lt_iff₀ hx).mp (by simpa using ho)
      simpa [div_eq_mul_inv, mul_comm] using this
  have hinner_lower : -x / 4 < W.innerPhase x := by
    have habs : -|W.innerPhase 0| ≤ W.innerPhase 0 := neg_abs_le _
    have hquarter : |W.innerPhase 0| < x / 4 := by linarith
    linarith
  have hγ : γ x < x / 2 := by
    have hbalance := W.phase_balance x
    linarith
  linarith

end GaloisForLFunctions.HTGeometry

namespace RHTower

open GaloisForLFunctions.HTGeometry

theorem noSmirnovToeplitzPhaseWitness_kapustinToeplitzPhase :
    ¬ Nonempty (SmirnovToeplitzPhaseWitness kapustinToeplitzPhase) :=
  not_smirnovToeplitzPhaseWitness_of_sub_id_tendsto_atTop
    tendsto_kapustinToeplitzPhase_sub_id_atTop

end RHTower
