/-
The vanishing abscissa: the Lindelöf hypothesis as a statement about one real number.

Let `μ` be the growth exponent — convex, nonnegative, with `μ(1) = 0` and
`μ(σ) - μ(1-σ) = 1/2 - σ`.  Two elementary consequences bracket the set where it vanishes.

* The functional equation forces `μ(σ) ≥ 1/2 - σ`, so `μ(σ) > 0` for every `σ < 1/2`.
* Convexity together with `μ(1) = 0` and nonnegativity makes the vanishing set upward closed: if
  `μ(s) = 0` and `s ≤ σ ≤ 1` then `μ(σ) = 0`.

So the vanishing set is an interval reaching to the right, and its left endpoint

    **σ* := inf { σ : μ(σ) = 0 }**

satisfies **`1/2 ≤ σ* ≤ 1`** unconditionally, with

    **the Lindelöf hypothesis  ⟺  σ* = 1/2.**

That reformulates the problem as: does a single real number, already known to lie in `[1/2, 1]`,
equal its unconditional lower bound?

Knowing any upper bound `σ* ≤ s` with `s < 1` strengthens the refutation amplifier of the disproof
route: a value `μ(σ) = v` at `1/2 ≤ σ < s` gives

    **μ(1/2) ≥ v · (s - 1/2)/(s - σ)** ,

which at `s = 1` is the previously recorded `v/(2(1-σ))` and is strictly larger for `s < 1`.
-/
import GaloisForLFunctions.HTGeometry.RefutationDeficitAndBandRatio

namespace HTGeometry

namespace ConvexGrowthExponent

variable (G : ConvexGrowthExponent)

/-! ### The vanishing set is bracketed -/

/-- **The functional equation forces positivity strictly left of the critical line.** -/
theorem mu_pos_of_lt_half {σ : ℚ} (h : σ < 1 / 2) : 0 < G.mu σ := by
  have hfe := G.functionalEquation σ
  have hnn := G.nonneg (1 - σ)
  linarith

/-- Hence the growth exponent never vanishes to the left of the critical line. -/
theorem mu_ne_zero_of_lt_half {σ : ℚ} (h : σ < 1 / 2) : G.mu σ ≠ 0 :=
  ne_of_gt (G.mu_pos_of_lt_half h)

/-- **The vanishing set is upward closed inside the strip.** -/
theorem vanishing_upward_closed {s σ : ℚ} (hs : G.mu s = 0) (hs1 : s < 1)
    (h1 : s ≤ σ) (h2 : σ ≤ 1) : G.mu σ = 0 := by
  have hd : 0 < 1 - s := by linarith
  have ht0 : (0 : ℚ) ≤ (1 - σ) / (1 - s) := by
    apply div_nonneg <;> linarith
  have ht1 : (1 - σ) / (1 - s) ≤ 1 := by
    rw [div_le_one hd]; linarith
  have hcv := G.convex s 1 ((1 - σ) / (1 - s)) ht0 ht1
  have hpt : (1 - σ) / (1 - s) * s + (1 - (1 - σ) / (1 - s)) * 1 = σ := by
    field_simp
    ring
  rw [hpt, hs, G.atOne] at hcv
  have := G.nonneg σ
  linarith

/-- Vanishing at `1` is given. -/
theorem vanishing_at_one : G.mu 1 = 0 := G.atOne

/-! ### The reformulation -/

/-- **The Lindelöf hypothesis is the vanishing of the exponent at the critical line**, which by
upward closure is the vanishing on the whole of `[1/2, 1]`. -/
theorem lindelof_iff_vanishing_from_half :
    G.mu (1 / 2) = 0 ↔ ∀ σ : ℚ, 1 / 2 ≤ σ → σ ≤ 1 → G.mu σ = 0 :=
  G.lindelof_iff_vanishes

/-- **No abscissa strictly below the critical line can be the left endpoint of the vanishing set.** -/
theorem no_vanishing_below_half {σ : ℚ} (h : σ < 1 / 2) : G.mu σ ≠ 0 :=
  G.mu_ne_zero_of_lt_half h

/-- **The bracket.**  The exponent vanishes at `1` and nowhere below the critical line, so its
vanishing set has a left endpoint in `[1/2, 1]`. -/
theorem vanishing_bracket :
    G.mu 1 = 0 ∧ ∀ σ : ℚ, σ < 1 / 2 → G.mu σ ≠ 0 :=
  ⟨G.atOne, fun _ h => G.mu_ne_zero_of_lt_half h⟩

/-! ### The sharpened refutation amplifier -/

/-- **Convexity against a known vanishing point `s`.** -/
theorem mu_le_chord_to_vanishing {s σ : ℚ} (hs : G.mu s = 0) (h1 : 1 / 2 ≤ σ) (h2 : σ < s) :
    G.mu σ ≤ (s - σ) / (s - 1 / 2) * G.mu (1 / 2) := by
  have hd : 0 < s - 1 / 2 := by linarith
  have ht0 : (0 : ℚ) ≤ (s - σ) / (s - 1 / 2) := by
    apply div_nonneg <;> linarith
  have ht1 : (s - σ) / (s - 1 / 2) ≤ 1 := by
    rw [div_le_one hd]; linarith
  have hcv := G.convex (1 / 2) s ((s - σ) / (s - 1 / 2)) ht0 ht1
  have hpt : (s - σ) / (s - 1 / 2) * (1 / 2 : ℚ) + (1 - (s - σ) / (s - 1 / 2)) * s = σ := by
    field_simp
    ring
  rw [hpt, hs] at hcv
  linarith

/-- **The sharpened amplifier.**  A value at `σ` amplifies by `(s - 1/2)/(s - σ)` on the critical
line, once a vanishing point `s` is known. -/
theorem mu_half_ge_sharpened {s σ : ℚ} (hs : G.mu s = 0) (h1 : 1 / 2 ≤ σ) (h2 : σ < s) :
    G.mu σ * ((s - 1 / 2) / (s - σ)) ≤ G.mu (1 / 2) := by
  have hsσ : 0 < s - σ := by linarith
  have hd : 0 < s - 1 / 2 := by linarith
  have hchord := G.mu_le_chord_to_vanishing hs h1 h2
  have hkey : G.mu σ * (s - 1 / 2) ≤ G.mu (1 / 2) * (s - σ) := by
    have hmul := mul_le_mul_of_nonneg_right hchord (le_of_lt hd)
    have hcancel : (s - σ) / (s - 1 / 2) * G.mu (1 / 2) * (s - 1 / 2)
        = G.mu (1 / 2) * (s - σ) := by
      field_simp
      ring
    rw [hcancel] at hmul
    exact hmul
  rw [mul_div_assoc'] at *
  rw [div_le_iff₀ hsσ]
  linarith

end ConvexGrowthExponent

/-! ### The amplifier as a function of the known vanishing point -/

/-- The refutation amplifier when a vanishing point `s` is available. -/
def sharpAmplifier (s σ : ℚ) : ℚ := (s - 1 / 2) / (s - σ)

/-- **At `s = 1` it is the previously recorded amplifier.** -/
theorem sharpAmplifier_at_one (σ : ℚ) : sharpAmplifier 1 σ = refutationAmplifier σ := by
  unfold sharpAmplifier refutationAmplifier
  rw [show (1 : ℚ) - 1 / 2 = 1 / 2 by norm_num]
  rw [div_eq_div_iff_of_ne] <;> ring_nf
  · ring
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)

/-- **A better vanishing point gives a stronger amplifier.** -/
theorem sharpAmplifier_antitone {s s' σ : ℚ} (h1 : 1 / 2 ≤ σ) (h2 : σ < s') (h3 : s' < s) :
    sharpAmplifier s σ < sharpAmplifier s' σ := by
  unfold sharpAmplifier
  have hd : 0 < s - σ := by linarith
  have hd' : 0 < s' - σ := by linarith
  rw [div_lt_div_iff₀ hd hd']
  nlinarith

/-- At `s = 9/10` and `σ = 7/10` the amplifier is `2`, against `5/3` at `s = 1`. -/
theorem sharpAmplifier_example :
    sharpAmplifier (9 / 10) (7 / 10) = 2 ∧ sharpAmplifier 1 (7 / 10) = 5 / 3 := by
  constructor
  · unfold sharpAmplifier; norm_num
  · rw [sharpAmplifier_at_one]; exact amplifier_at_seven_tenths

end HTGeometry
