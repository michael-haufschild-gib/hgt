import GaloisForLFunctions.RHTower.Sieve.MarkerBadCount

/-!
# Markers sharing a start are close

Two outer factors with the same fibre start lie in the same interval `(x/(t+1), x/t]`, whose length
is `x/(t(t+1))`.  Above a lower bound `T₁` for the starts this is a uniform separation, which is
the hypothesis the second-moment estimate of `Sieve/FibreMultiplicitySecondMoment` consumes.

At the marker scale `√x` the separation is `O(1)` and the sieve has nothing to do; at the lifted
scale `√(x log x)` it is `≍ log x`, and the shifted-pair sum over `d ≤ K` is exactly what
`Sieve/PrimePairAverage` bounds.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The start determines a window for the outer factor.** -/
theorem start_interval_of_fibreStartIdx {x : ℝ} (hx : 0 < x) {p t : ℕ} (hp : 1 ≤ p) (ht : 1 ≤ t)
    (h : fibreStartIdx x p = t) :
    x / ((t : ℝ) + 1) ≤ (p : ℝ) ∧ (p : ℝ) < x / (t : ℝ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hdiv : (0 : ℝ) < x / (p : ℝ) := div_pos hx hp0
  have hceil1 : 1 ≤ ⌈x / (p : ℝ)⌉₊ := Nat.one_le_ceil_iff.2 hdiv
  have hceil : ⌈x / (p : ℝ)⌉₊ = t + 1 := by
    rw [fibreStartIdx] at h
    omega
  obtain ⟨hlow, hhigh⟩ := (Nat.ceil_eq_iff (by omega : t + 1 ≠ 0)).1 hceil
  push_cast at hlow hhigh
  have ht0' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have ht1 : (0 : ℝ) < (t : ℝ) + 1 := by linarith
  constructor
  · rw [div_le_iff₀ ht1]
    rw [div_le_iff₀ hp0] at hhigh
    linarith
  · rw [lt_div_iff₀ ht0']
    have hgt : (t : ℝ) < x / (p : ℝ) := by linarith
    rw [lt_div_iff₀ hp0] at hgt
    linarith

/-- **Two outer factors with the same start are within `x/(t(t+1))`.** -/
theorem sub_lt_of_fibreStartIdx_eq {x : ℝ} (hx : 0 < x) {p q t : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (ht : 1 ≤ t) (hpt : fibreStartIdx x p = t) (hqt : fibreStartIdx x q = t) :
    (q : ℝ) - (p : ℝ) < x / ((t : ℝ) * ((t : ℝ) + 1)) := by
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have ht1 : (0 : ℝ) < (t : ℝ) + 1 := by linarith
  have hid : x / (t : ℝ) - x / ((t : ℝ) + 1) = x / ((t : ℝ) * ((t : ℝ) + 1)) := by
    field_simp
    ring
  obtain ⟨hpl, -⟩ := start_interval_of_fibreStartIdx hx hp ht hpt
  obtain ⟨-, hqu⟩ := start_interval_of_fibreStartIdx hx hq ht hqt
  linarith [hid]

/-- **A uniform separation above a lower bound for the starts.** -/
theorem marker_separation {x : ℝ} (hx : 0 < x) {T₁ : ℕ} (hT₁ : 1 ≤ T₁) {p q : ℕ}
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpT : T₁ ≤ fibreStartIdx x p) (heq : fibreStartIdx x q = fibreStartIdx x p) :
    (q : ℝ) ≤ (p : ℝ) + x / ((T₁ : ℝ) * ((T₁ : ℝ) + 1)) := by
  have ht : 1 ≤ fibreStartIdx x p := le_trans hT₁ hpT
  have hlt := sub_lt_of_fibreStartIdx_eq hx hp hq ht rfl heq
  have hT0 : (0 : ℝ) < (T₁ : ℝ) := by exact_mod_cast hT₁
  have htT : (T₁ : ℝ) ≤ ((fibreStartIdx x p : ℕ) : ℝ) := by exact_mod_cast hpT
  have hmono : x / (((fibreStartIdx x p : ℕ) : ℝ) * (((fibreStartIdx x p : ℕ) : ℝ) + 1))
      ≤ x / ((T₁ : ℝ) * ((T₁ : ℝ) + 1)) := by
    refine div_le_div_of_nonneg_left hx.le (by positivity) ?_
    nlinarith [htT, hT0]
  linarith

/-- **The separation, as the natural-number hypothesis the second moment consumes.** -/
theorem marker_separation_nat {x : ℝ} (hx : 0 < x) {T₁ K : ℕ} (hT₁ : 1 ≤ T₁)
    (hK : x / ((T₁ : ℝ) * ((T₁ : ℝ) + 1)) ≤ (K : ℝ)) {p q : ℕ}
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpT : T₁ ≤ fibreStartIdx x p) (heq : fibreStartIdx x q = fibreStartIdx x p) :
    q ≤ p + K := by
  have h := marker_separation hx hT₁ hp hq hpT heq
  have : (q : ℝ) ≤ ((p + K : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast this

end

end RHTower.Sieve
