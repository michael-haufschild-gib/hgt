import GaloisForLFunctions.HTGeometry.MaximumTermCentralIndex

/-!
# A Lipschitz bound for the central index from monotonicity alone

The Gaussian decay of the terms needs the central index to grow at most linearly on the sampling
window.  Asking for that at *every* scale is a genuine regularity hypothesis, and extracting it
costs a dyadic argument over all scales.  Asking for it only on scales `[v₀, H]` costs nothing at
all: the central index is nondecreasing, so its increment over any such scale is at most its
increment over the whole window, and dividing that single number by `v₀` gives a Lipschitz constant
valid throughout.

The point is that the Gaussian argument only ever uses scales bounded below — the optimal step
`k / (2L)` is at least `K / (2L)` — so this restricted form is all it needs.  The regularity input
therefore reduces to a bound on one number, the spread of the central index across the window, and
that is exactly what the measure estimate for monotone increments controls.
-/

namespace GaloisForLFunctions.HTGeometry

variable {a : ℕ → ℂ}

/-- The spread of the central index across a logarithmic window. -/
noncomputable def centralIndexSpread (a : ℕ → ℂ) (x H : ℝ) : ℝ :=
  (centralIndex a (Real.exp (x + H)) : ℝ) - (centralIndex a (Real.exp (x - H)) : ℝ)

/-- The spread is nonnegative. -/
theorem centralIndexSpread_nonneg (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {x H : ℝ}
    (hH : 0 ≤ H) : 0 ≤ centralIndexSpread a x H := by
  have hmono : centralIndex a (Real.exp (x - H)) ≤ centralIndex a (Real.exp (x + H)) :=
    centralIndex_mono ha (Real.exp_pos _) (Real.exp_le_exp.mpr (by linarith)) hn₀
  have : ((centralIndex a (Real.exp (x - H)) : ℕ) : ℝ)
      ≤ ((centralIndex a (Real.exp (x + H)) : ℕ) : ℝ) := by exact_mod_cast hmono
  rw [centralIndexSpread]
  linarith

/-- **Restricted Lipschitz bound above.**  On scales at least `v₀` the central index rises at most
linearly with constant the spread divided by `v₀`. -/
theorem centralIndex_le_add_spread_div_mul
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {x H v₀ : ℝ} (hv₀ : 0 < v₀) :
    ∀ v : ℝ, v₀ ≤ v → v ≤ H →
      (centralIndex a (Real.exp (x + v)) : ℝ)
        ≤ (centralIndex a (Real.exp x) : ℝ) + (centralIndexSpread a x H / v₀) * v := by
  intro v hv hvH
  have hHpos : 0 < H := lt_of_lt_of_le hv₀ (le_trans hv hvH)
  have hmono1 : centralIndex a (Real.exp (x + v)) ≤ centralIndex a (Real.exp (x + H)) :=
    centralIndex_mono ha (Real.exp_pos _) (Real.exp_le_exp.mpr (by linarith)) hn₀
  have hmono2 : centralIndex a (Real.exp (x - H)) ≤ centralIndex a (Real.exp x) :=
    centralIndex_mono ha (Real.exp_pos _) (Real.exp_le_exp.mpr (by linarith)) hn₀
  have hc1 : ((centralIndex a (Real.exp (x + v)) : ℕ) : ℝ)
      ≤ ((centralIndex a (Real.exp (x + H)) : ℕ) : ℝ) := by exact_mod_cast hmono1
  have hc2 : ((centralIndex a (Real.exp (x - H)) : ℕ) : ℝ)
      ≤ ((centralIndex a (Real.exp x) : ℕ) : ℝ) := by exact_mod_cast hmono2
  have hspreadnn : 0 ≤ centralIndexSpread a x H :=
    centralIndexSpread_nonneg ha hn₀ hHpos.le
  have hstep : centralIndexSpread a x H ≤ (centralIndexSpread a x H / v₀) * v := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hv₀]
    nlinarith [hspreadnn, hv]
  have hdiff : (centralIndex a (Real.exp (x + v)) : ℝ) - (centralIndex a (Real.exp x) : ℝ)
      ≤ centralIndexSpread a x H := by
    rw [centralIndexSpread]
    linarith
  linarith

/-- **Restricted Lipschitz bound below.** -/
theorem sub_spread_div_mul_le_centralIndex
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {x H v₀ : ℝ} (hv₀ : 0 < v₀) :
    ∀ v : ℝ, v₀ ≤ v → v ≤ H →
      (centralIndex a (Real.exp x) : ℝ) - (centralIndexSpread a x H / v₀) * v
        ≤ (centralIndex a (Real.exp (x - v)) : ℝ) := by
  intro v hv hvH
  have hHpos : 0 < H := lt_of_lt_of_le hv₀ (le_trans hv hvH)
  have hmono1 : centralIndex a (Real.exp (x - H)) ≤ centralIndex a (Real.exp (x - v)) :=
    centralIndex_mono ha (Real.exp_pos _) (Real.exp_le_exp.mpr (by linarith)) hn₀
  have hmono2 : centralIndex a (Real.exp x) ≤ centralIndex a (Real.exp (x + H)) :=
    centralIndex_mono ha (Real.exp_pos _) (Real.exp_le_exp.mpr (by linarith)) hn₀
  have hc1 : ((centralIndex a (Real.exp (x - H)) : ℕ) : ℝ)
      ≤ ((centralIndex a (Real.exp (x - v)) : ℕ) : ℝ) := by exact_mod_cast hmono1
  have hc2 : ((centralIndex a (Real.exp x) : ℕ) : ℝ)
      ≤ ((centralIndex a (Real.exp (x + H)) : ℕ) : ℝ) := by exact_mod_cast hmono2
  have hspreadnn : 0 ≤ centralIndexSpread a x H :=
    centralIndexSpread_nonneg ha hn₀ hHpos.le
  have hstep : centralIndexSpread a x H ≤ (centralIndexSpread a x H / v₀) * v := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hv₀]
    nlinarith [hspreadnn, hv]
  have hdiff : (centralIndex a (Real.exp x) : ℝ) - (centralIndex a (Real.exp (x - v)) : ℝ)
      ≤ centralIndexSpread a x H := by
    rw [centralIndexSpread]
    linarith
  linarith

end GaloisForLFunctions.HTGeometry
