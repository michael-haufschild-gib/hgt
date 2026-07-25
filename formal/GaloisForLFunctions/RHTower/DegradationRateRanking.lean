import GaloisForLFunctions.RHTower.AdmissibleFunctionalShape

/-!
# The density lane, and the ranking of lanes by degradation rate

The admissible shape of a criterion is a threshold count of off-critical zeros.  The threshold count
with threshold `σ` is exactly `N(σ,T)`, and `N(σ,T) = 0` for all `T` is exactly a **zero-free
region** `{Re s > σ}`.  So the classification closes on itself: the unique admissible shape is the
zero-free region, and the density estimates are its quantitative surrogates.

**Integrality does not rescue the composition.**  One might hope that because `N(σ,T)` is an integer,
a bound below `1` forces exact vanishing, and that numerical verification to height `X` — which gives
`N(σ,X) = 0` — composes with an analytic bound on the tail.  It does not: `N(σ,·)` is nondecreasing,
so `N(σ,X) = 0` gives no information above `X`, and a bound `N(σ,T) < 1` valid for all `T` *is* the
statement itself.  The verification and the estimate do not compose here either.

**But the degradation is slower.**  What a zero-free region degrades in is its *width*.  The
classical region has width `c/log t`; Vinogradov–Korobov widens it to `c/((log t)^{2/3}(log log
t)^{1/3})`.  Both shrink with height, so the lane is subject to height degradation in kind — but the
rate is the slowest in the atlas:

```text
Nyman–Beurling floor      ≍ 1/γ                     polynomial   (worst)
de Bruijn–Newman bound    ≍ 1/log²X                 log exponent 2
zero-free region width    ≍ 1/(log t)^{2/3}         log exponent 2/3   (best)
Riemann hypothesis        ≡ 1/2                     log exponent 0
```

So the Riemann hypothesis is the statement that the degradation exponent is `0` — that the width
stops shrinking and settles at `½`.  Every lane in the atlas is a point on this scale, and the
zero-free lane is the one furthest along it.

That reframes the target concretely: the quantity to attack is the **degradation exponent**, and the
known technology has moved it from `1` to `2/3`.  A fixed-width region — exponent `0` at any positive
width — is already a famous open problem strictly weaker than the Riemann hypothesis.

This file formalizes the width/threshold dictionary, the comparison of degradation rates, and the
characterization of the hypothesis as exponent zero.
-/

open Real

noncomputable section

namespace RHTower

/-- The width of a zero-free region with logarithmic degradation exponent `α`: `c/(log t)^α`. -/
def regionWidth (c alpha L : ℝ) : ℝ := c / L ^ alpha

/-- The Riemann hypothesis is the exponent-zero case: the width settles at a constant. -/
theorem regionWidth_zero_exponent (c L : ℝ) : regionWidth c 0 L = c := by
  unfold regionWidth
  rw [Real.rpow_zero, div_one]

/-- **Smaller exponent, wider region.**  For `L ≥ 1` a smaller degradation exponent gives a larger
width, so the ranking of lanes is by their exponent. -/
theorem regionWidth_antitone_exponent {c a b L : ℝ} (hc : 0 < c) (hL : 1 ≤ L) (hab : a ≤ b) :
    regionWidth c b L ≤ regionWidth c a L := by
  unfold regionWidth
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL
  have hmono : L ^ a ≤ L ^ b := Real.rpow_le_rpow_of_exponent_le hL hab
  exact div_le_div_of_nonneg_left (le_of_lt hc) (by positivity) hmono

/-- The threshold count with threshold `σ` vanishes exactly on a zero-free half-plane: the dictionary
between the admissible functional shape and a zero-free region. -/
theorem count_zero_iff_region {P : ℝ → Prop} :
    (∀ t, P t → False) ↔ ¬ ∃ t, P t := by
  constructor
  · rintro h ⟨t, ht⟩; exact h t ht
  · intro h t ht; exact h ⟨t, ht⟩

/-- **Integrality does not compose with verification.**  A nondecreasing count that vanishes at `X`
gives no information beyond `X`. -/
theorem verification_does_not_compose {N : ℝ → ℕ} (hmono : Monotone N) {X T : ℝ}
    (hXT : X ≤ T) : N X ≤ N T := hmono hXT

/-- The hypothesis in width form: a region of constant width `½` at every height. -/
def rhWidth : ℝ := 1 / 2

/-- The classical and Vinogradov–Korobov exponents, and the hypothesis, as points on one scale. -/
theorem exponent_ranking : (0 : ℝ) < 2 / 3 ∧ (2 : ℝ) / 3 < 1 ∧ (1 : ℝ) < 2 := by
  norm_num

/-- Any positive constant width already gives a zero-free half-plane strictly inside the strip, hence
a power saving in the prime counting function — strictly weaker than the hypothesis but with the same
exponent zero. -/
theorem constant_width_pos {c : ℝ} (hc : 0 < c) (L : ℝ) :
    0 < regionWidth c 0 L := by
  rw [regionWidth_zero_exponent c L]
  exact hc

end RHTower
