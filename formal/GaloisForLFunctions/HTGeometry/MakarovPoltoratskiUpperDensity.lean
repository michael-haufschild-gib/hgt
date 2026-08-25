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

def SmirnovToeplitzPhaseWitness.add {γ δ : ℝ → ℝ}
    (Wγ : SmirnovToeplitzPhaseWitness γ)
    (Wδ : SmirnovToeplitzPhaseWitness δ) :
    SmirnovToeplitzPhaseWitness (fun x => γ x + δ x) where
  innerPhase := fun x => Wγ.innerPhase x + Wδ.innerPhase x
  outerHilbertPhase := fun x => Wγ.outerHilbertPhase x + Wδ.outerHilbertPhase x
  innerPhase_monotone := Wγ.innerPhase_monotone.add Wδ.innerPhase_monotone
  phase_balance := by
    intro x
    rw [show γ x + δ x + (Wγ.innerPhase x + Wδ.innerPhase x) =
      (γ x + Wγ.innerPhase x) + (δ x + Wδ.innerPhase x) by ring,
      Wγ.phase_balance, Wδ.phase_balance]
  outerHilbertPhase_sublinear_atTop := by
    convert Wγ.outerHilbertPhase_sublinear_atTop.add
      Wδ.outerHilbertPhase_sublinear_atTop using 1
    · funext x
      rw [add_div]
    · ring

def SmirnovToeplitzPhaseWitness.congr {γ δ : ℝ → ℝ}
    (W : SmirnovToeplitzPhaseWitness γ) (h : ∀ x, γ x = δ x) :
    SmirnovToeplitzPhaseWitness δ where
  innerPhase := W.innerPhase
  outerHilbertPhase := W.outerHilbertPhase
  innerPhase_monotone := W.innerPhase_monotone
  phase_balance := by intro x; rw [← h x, W.phase_balance]
  outerHilbertPhase_sublinear_atTop := W.outerHilbertPhase_sublinear_atTop

theorem tendsto_div_atTop_zero_of_abs_le
    {f : ℝ → ℝ} {C : ℝ} (hf : ∀ x, |f x| ≤ C) :
    Tendsto (fun x => f x / x) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨max 1 (C / ε + 1), ?_⟩
  intro x hx
  rw [Real.dist_eq]
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one
    (le_trans (le_max_left 1 (C / ε + 1)) hx)
  have hCdiv : C / x < ε := by
    have hxC : C / ε < x := lt_of_lt_of_le (lt_add_one (C / ε))
      (le_trans (le_max_right 1 (C / ε + 1)) hx)
    apply (div_lt_iff₀ hx0).2
    simpa [mul_comm] using (div_lt_iff₀ hε).mp hxC
  rw [sub_zero, abs_div, abs_of_pos hx0]
  exact lt_of_le_of_lt (div_le_div_of_nonneg_right (hf x) hx0.le) hCdiv

/-- Smirnov--Kolmogorov bounded-phase multiplier at exponent `p = 1/2`, in phase coordinates. -/
noncomputable def boundedPhaseBlaschkeFourWitness (b : ℝ → ℝ) (C : ℝ) (_hC : 0 ≤ C)
    (hb : ∀ x, |b x| ≤ C) :
    SmirnovToeplitzPhaseWitness (fun x => -8 * Real.arctan x + 2 * b x) where
  innerPhase := fun x => 8 * Real.arctan x
  outerHilbertPhase := fun x => 2 * b x
  innerPhase_monotone := ((show StrictMono Real.arctan from
    fun _ _ h => Real.arctan_lt_arctan_iff.mpr h).const_mul
      (by norm_num : (0 : ℝ) < 8)).monotone
  phase_balance := by intro x; ring
  outerHilbertPhase_sublinear_atTop := by
    apply tendsto_div_atTop_zero_of_abs_le (C := 2 * C)
    intro x
    rw [abs_mul]
    simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using
      mul_le_mul_of_nonneg_left (hb x) (by norm_num : (0 : ℝ) ≤ 2)

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

/-- Exact bounded-phase product step in Kapustin's proof: a Hardy phase witness for the gauge,
together with a bounded representative of the positive-real cancellation, creates a forbidden
witness for the reciprocal-Gamma Toeplitz symbol. -/
noncomputable def kapustinToeplitzPhaseWitness_of_boundedCancellation
    (ψ b : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hψ : SmirnovToeplitzPhaseWitness (fun x => -2 * ψ x))
    (hb : ∀ x, |b x| ≤ C)
    (hphase : ∀ x,
      kapustinToeplitzPhase x =
        -2 * ψ x + (-8 * Real.arctan x + 2 * b x)) :
    SmirnovToeplitzPhaseWitness kapustinToeplitzPhase :=
  (hψ.add (boundedPhaseBlaschkeFourWitness b C hC hb)).congr fun x => (hphase x).symm

theorem noSmirnovToeplitzPhaseWitness_kapustinToeplitzPhase :
    ¬ Nonempty (SmirnovToeplitzPhaseWitness kapustinToeplitzPhase) :=
  not_smirnovToeplitzPhaseWitness_of_sub_id_tendsto_atTop
    tendsto_kapustinToeplitzPhase_sub_id_atTop

end RHTower
