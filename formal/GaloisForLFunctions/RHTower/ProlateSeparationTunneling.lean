import GaloisForLFunctions.RHTower.FuchsProlateScale

/-!
# Exponential tunneling forces the prolate separation ratio to zero

Fixed-index prolate leakage has the Gaussian clock `exp (-β a²)`.  A mode whose normalized
separation ratio stays above `ε > 0` tunnels through a strictly shorter forbidden region, hence
has a lower bound with clock `exp (-(β-δ) a²)` for some `δ > 0`.  No polynomial prefactor can
reconcile those two estimates.

This module formalizes that last implication independently of the WKB construction.  Its
capstone is deliberately filter-level: once the concrete angular/radial comparison supplies the
strict clock gain at every positive separation threshold, convergence of the separation ratio is
automatic.  No spectral numbering or simplicity premise enters this reduction.
-/

noncomputable section

open Filter

namespace RHTower

/-- A fixed polynomial times the faster Gaussian clock is eventually strictly smaller than the
same unit-prefactor Gaussian with any positive clock gain. -/
theorem eventually_const_mul_pow_mul_exp_neg_lt_exp_clock_gain
    (C β : ℝ) (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ a : ℝ in atTop,
      C * a ^ m * Real.exp (-(β * a ^ 2)) <
        Real.exp (-((β - δ) * a ^ 2)) := by
  have hzero :=
    (tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero m hδ).const_mul C
  rw [mul_zero] at hzero
  have hsmall : ∀ᶠ a : ℝ in atTop,
      C * (a ^ m * Real.exp (-(δ * a ^ 2))) < 1 :=
    hzero.eventually (eventually_lt_nhds zero_lt_one)
  filter_upwards [hsmall] with a ha
  have hfactor :
      C * a ^ m * Real.exp (-(β * a ^ 2)) =
        (C * (a ^ m * Real.exp (-(δ * a ^ 2)))) *
          Real.exp (-((β - δ) * a ^ 2)) := by
    calc
      C * a ^ m * Real.exp (-(β * a ^ 2)) =
          C * a ^ m *
            (Real.exp (-(δ * a ^ 2)) * Real.exp (-((β - δ) * a ^ 2))) := by
              rw [← Real.exp_add]
              congr 2
              ring
      _ = (C * (a ^ m * Real.exp (-(δ * a ^ 2)))) *
          Real.exp (-((β - δ) * a ^ 2)) := by ring
  rw [hfactor]
  simpa only [one_mul] using
    (mul_lt_mul_of_pos_right ha (Real.exp_pos (-((β - δ) * a ^ 2))))

/-- **Tunneling separation principle.**  Let `d(a)` be a nonnegative mode leakage and `s(a)` its
normalized separation ratio.  Suppose

* `s(a) ≥ 0` eventually;
* `d(a)` is eventually bounded above by one fixed polynomial times `exp (-β a²)`;
* for every `ε > 0`, the alternative `s(a) ≥ ε` forces a leakage lower bound whose Gaussian
  exponent gains some `δ(ε) > 0`.

Then `s(a) → 0`.  This is the exact contradiction needed to turn a uniform WKB barrier estimate
into the radial small-separation input consumed by the Dunster modules. -/
theorem tendsto_separation_zero_of_gaussian_upper_of_tunneling_lower
    {d s : ℝ → ℝ} {C β : ℝ} {m : ℕ}
    (hs_nonneg : ∀ᶠ a : ℝ in atTop, 0 ≤ s a)
    (hd_upper : ∀ᶠ a : ℝ in atTop,
      d a ≤ C * a ^ m * Real.exp (-(β * a ^ 2)))
    (hd_lower : ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ a : ℝ in atTop,
        ε ≤ s a → Real.exp (-((β - δ) * a ^ 2)) ≤ d a) :
    Tendsto s atTop (nhds 0) := by
  rw [tendsto_order]
  constructor
  · intro b hb
    filter_upwards [hs_nonneg] with a ha
    exact lt_of_lt_of_le hb ha
  · intro ε hε
    obtain ⟨δ, hδ, hd_lower_ε⟩ := hd_lower ε hε
    have hclock :=
      eventually_const_mul_pow_mul_exp_neg_lt_exp_clock_gain C β m hδ
    filter_upwards [hd_upper, hd_lower_ε, hclock] with a hupper hlower hclocka
    by_contra hnot
    have hεs : ε ≤ s a := le_of_not_gt hnot
    have hlowera := hlower hεs
    have hstrict : d a < Real.exp (-((β - δ) * a ^ 2)) :=
      hupper.trans_lt hclocka
    exact (not_lt_of_ge hlowera) hstrict

/-- Variant adapted to trial spaces whose Gaussian exponent can be made arbitrarily close to the
optimal clock.  The upper estimate may lose any prescribed `η > 0`; the tunneling obstruction at
separation threshold `ε` supplies one fixed positive gain `δ`, and choosing `η < δ` gives the
contradiction. -/
theorem tendsto_separation_zero_of_arbitrarily_sharp_gaussian_upper_of_tunneling_lower
    {d s : ℝ → ℝ} {β : ℝ} (hβ : 0 < β)
    (hs_nonneg : ∀ᶠ a : ℝ in atTop, 0 ≤ s a)
    (hd_upper : ∀ η : ℝ, 0 < η → η < β →
      ∀ᶠ a : ℝ in atTop,
        d a ≤ Real.exp (-((β - η) * a ^ 2)))
    (hd_lower : ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ a : ℝ in atTop,
        ε ≤ s a → Real.exp (-((β - δ) * a ^ 2)) ≤ d a) :
    Tendsto s atTop (nhds 0) := by
  rw [tendsto_order]
  constructor
  · intro b hb
    filter_upwards [hs_nonneg] with a ha
    exact lt_of_lt_of_le hb ha
  · intro ε hε
    obtain ⟨δ, hδ, hd_lower_ε⟩ := hd_lower ε hε
    let η : ℝ := min (δ / 2) (β / 2)
    have hη : 0 < η := by
      dsimp only [η]
      exact lt_min (by positivity) (by positivity)
    have hηδ : η < δ := by
      have hle : η ≤ δ / 2 := min_le_left _ _
      linarith
    have hηβ : η < β := by
      have hle : η ≤ β / 2 := min_le_right _ _
      linarith
    have hupper := hd_upper η hη hηβ
    filter_upwards [hupper, hd_lower_ε, eventually_gt_atTop (0 : ℝ)] with
      a hu hl ha
    by_contra hnot
    have hεs : ε ≤ s a := le_of_not_gt hnot
    have hlo := hl hεs
    have hclock :
        Real.exp (-((β - η) * a ^ 2)) <
          Real.exp (-((β - δ) * a ^ 2)) := by
      rw [Real.exp_lt_exp]
      have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
      nlinarith
    exact (not_lt_of_ge hlo) (hu.trans_lt hclock)

end RHTower

end
