import GaloisForLFunctions.ArithmeticIncidencePositivity.FirstPrimeMicroFold

/-!
# The sharp micro-fold: every prime-power atom is dominated near its reflection point

On the strip `S = [L − r, r]` around `m = L/2`, `η = r − m`, the micro-fold of `FirstPrimeMicroFold`
compares the surplus of the pairs of `S × S` with the odd part `α(x) = (F(x) − F(L − x))/2`. Folding
`α` onto `[m, r]` (it is odd about `m`) turns the four pairs `x, L − x, y, L − y` into a same-side
pair at distance `|u − v|` and a crossing pair at distance `u + v`, `u = |x − m|`, `v = |y − m|`:

    Σ₄ ≥ 2k₀(|u − v|)(a − b)² + 2k₀(u + v)(a + b)² = 2k(u, v)(a − b)² + 4k₀(u + v)(a² + b²),

`k₀(t) = ω(t) − ω(2p)`, `k(u, v) = ω(|u − v|) − ω(u + v)` the surplus kernel. The micro-fold of
`FirstPrimeMicroFold` dropped the surplus term; here it is kept and transformed in the gauge
`g(t) = η/10 + t` (`sharpQuadruple_ge`). The potential `2U_g(u) + 4K(u)`,
`K(u) = ∫_0^η k₀(u + v) dv`, is at least `1.94 − η/p − 3η²` (`sharpFold_potential_ge`).

**Why `2`.** In the scaling limit `η → 0` the strip problem is the regional logarithmic kernel
`1/(2|s − t|)` on `[−1, 1]`, and its odd ground state is exactly linear:
`∫_{−1}^{1} (s − t)/|s − t| dt = 2s`. The gauge `g(t) = t` gives `U = 1 − ℓ`, `4K = 2ℓ`,
`ℓ = log((u + η)/u)`, so the potential is identically `2`: the logarithms cancel. The constant of
`FirstPrimeMicroFold`, `log 2 + ½`, came from dropping the surplus and treating one variable crudely.

**Theorems.**
* `sharpMicroFold_strip_ge`: `∫_S ∫_S k(x, y)(F x − F y)² ≥ (1.94 − η/p − 3η²) ∫_S α²` for
  `η ≤ 1/10`, `p = L − r > 0`, `2η ≤ 2p`.
* `two_mul_primePowerShift_le_stripSurplus`: for every `n ≥ 2` and every odd `F` supported in
  `[−r, r]`, `½ log n < r ≤ ½ log n + 1/10`,
  `2 Λ(n)/√n ∫ F(x) F(x + log n) ≤ ∫_{S_n} ∫_{S_n} k(F x − F y)²`, `S_n = [log n − r, r]`: since
  `Λ(n)/√n ≤ log n/√n ≤ 2/e < 0.736`, every prime-power atom is paid by the archimedean surplus of its
  own reflection strip — a Harnack inequality across every prime shift, with constant `> 1.5`.
-/

open MeasureTheory Set Filter Topology intervalIntegral
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-- The ground-state weight of the folded odd part in the gauge `g(t) = β + t`:
`W(u, v) = 2 k(u, v)(1 − g(v)/g(u)) + 4 k₀(u + v)`. -/
def sharpFoldWeight (p β u v : ℝ) : ℝ :=
  2 * (surplusKernel u v * (1 - (β + v) / (β + u))) + 4 * microFoldKernel p (u + v)

/-- The algebra of the folded pair with its ground-state transform: the same-side rate `m₁` exceeds
the crossing rate `m₂` by the surplus `s`. -/
theorem sharpFold_core {a b m₁ m₂ s q : ℝ} (hq : 0 < q) (hs : m₁ - m₂ = s)
    (hdeg : 0 ≤ s ∨ (a = b ∧ q = 1)) :
    a ^ 2 * (2 * (s * (1 - q)) + 4 * m₂) + b ^ 2 * (2 * (s * (1 - 1 / q)) + 4 * m₂) ≤
      2 * m₁ * (a - b) ^ 2 + 2 * m₂ * (a + b) ^ 2 := by
  have hgs : s * (a ^ 2 * (1 - q) + b ^ 2 * (1 - 1 / q)) ≤ s * (a - b) ^ 2 := by
    rcases hdeg with hs0 | ⟨hab, hq1⟩
    · have := sq_sub_ge_groundState a b (show (0 : ℝ) < 1 by norm_num) hq
      rw [div_one] at this
      exact mul_le_mul_of_nonneg_left this hs0
    · rw [hab, hq1]; simp
  have e : 2 * m₁ * (a - b) ^ 2 + 2 * m₂ * (a + b) ^ 2 =
      2 * (s * (a - b) ^ 2) + 4 * m₂ * (a ^ 2 + b ^ 2) := by
    rw [← hs]; ring
  rw [e]
  nlinarith [hgs]

/-- A same-side or crossing group of two pairs controls the corresponding odd difference. -/
theorem sharpFold_group {m S1 S2 A A' B B' : ℝ} (h1 : m * (A - B) ^ 2 ≤ S1)
    (h2 : m * (A' - B') ^ 2 ≤ S2) (hm : 0 ≤ m ∨ (A = B ∧ A' = B')) :
    2 * m * ((A - A') / 2 - (B - B') / 2) ^ 2 ≤ S1 + S2 := by
  rcases hm with hm | ⟨hab, hab'⟩
  · have e : (A - B) ^ 2 + (A' - B') ^ 2 =
        2 * ((A + A' - B - B') / 2) ^ 2 + 2 * ((A - A') / 2 - (B - B') / 2) ^ 2 := by ring
    nlinarith [mul_nonneg hm (sq_nonneg ((A + A' - B - B') / 2))]
  · subst hab hab'
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h1 h2 ⊢
    linarith

theorem surplusKernel_zero_left {v : ℝ} (hv : 0 ≤ v) : surplusKernel 0 v = 0 := by
  unfold surplusKernel; rw [zero_sub, abs_neg, abs_of_nonneg hv, zero_add, sub_self]

/-- The surplus kernel is nonnegative off the diagonal of the closed quadrant. -/
theorem surplusKernel_nonneg' {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u ≠ v) :
    0 ≤ surplusKernel u v := by
  rcases eq_or_lt_of_le hu with h0 | h0
  · rw [← h0, surplusKernel_zero_left hv]
  rcases eq_or_lt_of_le hv with h0' | h0'
  · rw [← h0', surplusKernel_comm, surplusKernel_zero_left hu]
  exact surplusKernel_nonneg h0 h0' huv

/-- **The folded pair in the gauge `β + t`.** If the same-side rate exceeds the crossing rate
`k₀(u + v)` by the surplus `k(u, v)`, the two rates dominate `a² W(u, v) + b² W(v, u)`. -/
theorem sharpFold_folded {p β u v a b m₁ m₂ : ℝ} (hβ : 0 < β) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hm : m₁ - m₂ = surplusKernel u v) (hm₂ : m₂ = microFoldKernel p (u + v))
    (hdeg : u = v → a = b) :
    a ^ 2 * sharpFoldWeight p β u v + b ^ 2 * sharpFoldWeight p β v u ≤
      2 * m₁ * (a - b) ^ 2 + 2 * m₂ * (a + b) ^ 2 := by
  have hβu : 0 < β + u := by positivity
  have hβv : 0 < β + v := by positivity
  have hq : 0 < (β + v) / (β + u) := div_pos hβv hβu
  have hqinv : (β + u) / (β + v) = 1 / ((β + v) / (β + u)) := by field_simp
  unfold sharpFoldWeight
  rw [surplusKernel_comm v u, add_comm v u, hqinv, ← hm₂]
  refine sharpFold_core hq hm ?_
  by_cases huv : u = v
  · exact Or.inr ⟨hdeg huv, by rw [huv, div_self hβv.ne']⟩
  · exact Or.inl (surplusKernel_nonneg' hu hv huv)

/-- **The sharp quadruple inequality.** For `x, y` in the strip, with `u = |x − m|`, `v = |y − m|`,
`m = L/2`, the four surplus terms of `x, L − x, y, L − y` dominate
`α(x)² W(u, v) + α(y)² W(v, u)`. -/
theorem sharpQuadruple_ge {p r L β x y : ℝ} (hp : 0 < p) (hL : p + r = L) (hr3 : r - p ≤ 2 * p)
    (hβ : 0 < β) (hx : x ∈ Icc p r) (hy : y ∈ Icc p r) (F : ℝ → ℝ) :
    reflectedOddPart F L x ^ 2 * sharpFoldWeight p β |x - L / 2| |y - L / 2| +
        reflectedOddPart F L y ^ 2 * sharpFoldWeight p β |y - L / 2| |x - L / 2| ≤
      surplusKernel x y * (F x - F y) ^ 2 +
        surplusKernel (L - x) (L - y) * (F (L - x) - F (L - y)) ^ 2 +
        surplusKernel x (L - y) * (F x - F (L - y)) ^ 2 +
        surplusKernel (L - x) y * (F (L - x) - F y) ^ 2 := by
  have hxL : L - x ∈ Icc p r := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hyL : L - y ∈ Icc p r := ⟨by linarith [hy.2], by linarith [hy.1]⟩
  set U := x - L / 2 with hU
  set V := y - L / 2 with hV
  -- the four pairs, with the micro-fold kernel at the folded distances
  have k1 := microFoldKernel_mul_le hp hx hy F
  have k2 := microFoldKernel_mul_le hp hxL hyL F
  have k3 := microFoldKernel_mul_le hp hx hyL F
  have k4 := microFoldKernel_mul_le hp hxL hy F
  have e1 : |x - y| = |U - V| := by rw [hU, hV]; ring_nf
  have e2 : |L - x - (L - y)| = |U - V| := by rw [hU, hV, abs_sub_comm]; ring_nf
  have e3 : |x - (L - y)| = |U + V| := by rw [hU, hV]; ring_nf
  have e4 : |L - x - y| = |U + V| := by rw [hU, hV, ← abs_neg]; ring_nf
  rw [e1] at k1; rw [e2] at k2; rw [e3] at k3; rw [e4] at k4
  -- the same-side group and the crossing group
  have g12 := sharpFold_group k1 k2 (by
    by_cases hxy : U = V
    · right
      have : x = y := by linarith
      rw [this]; exact ⟨rfl, rfl⟩
    · left
      exact microFoldKernel_nonneg (abs_pos.mpr (sub_ne_zero.mpr hxy))
        (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]))
  have g34 := sharpFold_group k3 k4 (by
    by_cases hxy : U + V = 0
    · right
      have : y = L - x := by linarith
      rw [this, sub_sub_cancel]; exact ⟨rfl, rfl⟩
    · left
      exact microFoldKernel_nonneg (abs_pos.mpr hxy)
        (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]))
  unfold reflectedOddPart
  set a := (F x - F (L - x)) / 2 with ha
  set b := (F y - F (L - y)) / 2 with hb
  have g34' : 2 * microFoldKernel p |U + V| * (a + b) ^ 2 ≤
      surplusKernel x (L - y) * (F x - F (L - y)) ^ 2 +
        surplusKernel (L - x) y * (F (L - x) - F y) ^ 2 := by
    have e : a - (F (L - y) - F (L - (L - y))) / 2 = a + b := by
      rw [hb, sub_sub_cancel]; ring
    rw [e] at g34; exact g34
  rcases le_total 0 U with hU0 | hU0 <;> rcases le_total 0 V with hV0 | hV0
  · -- both on the right: same-side distance `|u − v|`, crossing distance `u + v`
    have hf := sharpFold_folded (p := p) (a := a) (b := b) (m₁ := microFoldKernel p |U - V|)
      (m₂ := microFoldKernel p |U + V|) hβ (abs_nonneg U) (abs_nonneg V)
      (by unfold microFoldKernel surplusKernel
          rw [abs_of_nonneg hU0, abs_of_nonneg hV0, abs_of_nonneg (by linarith : 0 ≤ U + V)]; ring)
      (by rw [abs_of_nonneg hU0, abs_of_nonneg hV0, abs_of_nonneg (by linarith : 0 ≤ U + V)])
      (fun h => by
        rw [abs_of_nonneg hU0, abs_of_nonneg hV0] at h
        have : x = y := by linarith
        rw [ha, hb, this])
    linarith only [hf, g12, g34']
  · -- `x` right, `y` left: the two groups exchange their distances
    have hf := sharpFold_folded (p := p) (a := a) (b := -b) (m₁ := microFoldKernel p |U + V|)
      (m₂ := microFoldKernel p |U - V|) hβ (abs_nonneg U) (abs_nonneg V)
      (by unfold microFoldKernel surplusKernel
          rw [abs_of_nonneg hU0, abs_of_nonpos hV0, abs_of_nonneg (by linarith : 0 ≤ U - V)]
          ring_nf)
      (by rw [abs_of_nonneg hU0, abs_of_nonpos hV0, abs_of_nonneg (by linarith : 0 ≤ U - V)]; ring_nf)
      (fun h => by
        rw [abs_of_nonneg hU0, abs_of_nonpos hV0] at h
        have : y = L - x := by linarith
        rw [ha, hb, this, sub_sub_cancel]; ring)
    rw [neg_sq, sub_neg_eq_add, ← sub_eq_add_neg] at hf
    linarith only [hf, g12, g34']
  · -- `x` left, `y` right
    have hf := sharpFold_folded (p := p) (a := a) (b := -b) (m₁ := microFoldKernel p |U + V|)
      (m₂ := microFoldKernel p |U - V|) hβ (abs_nonneg U) (abs_nonneg V)
      (by unfold microFoldKernel surplusKernel
          rw [abs_of_nonpos hU0, abs_of_nonneg hV0, abs_of_nonpos (by linarith : U - V ≤ 0)]
          ring_nf)
      (by rw [abs_of_nonpos hU0, abs_of_nonneg hV0, abs_of_nonpos (by linarith : U - V ≤ 0)]; ring_nf)
      (fun h => by
        rw [abs_of_nonpos hU0, abs_of_nonneg hV0] at h
        have : y = L - x := by linarith
        rw [ha, hb, this, sub_sub_cancel]; ring)
    rw [neg_sq, sub_neg_eq_add, ← sub_eq_add_neg] at hf
    linarith only [hf, g12, g34']
  · -- both on the left
    have hf := sharpFold_folded (p := p) (a := a) (b := b) (m₁ := microFoldKernel p |U - V|)
      (m₂ := microFoldKernel p |U + V|) hβ (abs_nonneg U) (abs_nonneg V)
      (by unfold microFoldKernel surplusKernel
          rw [abs_of_nonpos hU0, abs_of_nonpos hV0, abs_of_nonpos (by linarith : U + V ≤ 0)]
          ring_nf)
      (by rw [abs_of_nonpos hU0, abs_of_nonpos hV0, abs_of_nonpos (by linarith : U + V ≤ 0)]; ring_nf)
      (fun h => by
        rw [abs_of_nonpos hU0, abs_of_nonpos hV0] at h
        have : x = y := by linarith
        rw [ha, hb, this])
    linarith only [hf, g12, g34']

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
