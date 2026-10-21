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
`K(u) = ∫_0^η k₀(u + v) dv`, is at least `1.9 − η/p − 3η²` (`sharpFold_potential_ge`).

**Why `2`.** In the scaling limit `η → 0` the strip problem is the regional logarithmic kernel
`1/(2|s − t|)` on `[−1, 1]`, and its odd ground state is exactly linear:
`∫_{−1}^{1} (s − t)/|s − t| dt = 2s`. The gauge `g(t) = t` gives `U = 1 − ℓ`, `4K = 2ℓ`,
`ℓ = log((u + η)/u)`, so the potential is identically `2`: the logarithms cancel. The constant of
`FirstPrimeMicroFold`, `log 2 + ½`, came from dropping the surplus and treating one variable crudely.

**Theorems.**
* `sharpMicroFold_strip_ge`: `∫_S ∫_S k(x, y)(F x − F y)² ≥ (1.9 − η/p − 3η²) ∫_S α²` for
  `η ≤ 1/12`, `p = L − r > 0`, `2η ≤ 2p`.
* `two_mul_primePowerShift_le_stripSurplus`: for every `n ≥ 2` and every odd `F` supported in
  `[−r, r]`, `½ log n < r ≤ ½ log n + 1/12`,
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
    have e : a - (F (L - y) - F y) / 2 = a + b := by
      rw [hb]; ring
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
          rw [abs_of_nonpos hU0, abs_of_nonneg hV0, abs_of_nonpos (by linarith : U - V ≤ 0),
            show -U - V = -(U + V) by ring, abs_neg]
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
          rw [abs_of_nonpos hU0, abs_of_nonpos hV0, abs_of_nonpos (by linarith : U + V ≤ 0),
            show -U - -V = -(U - V) by ring, abs_neg]
          ring_nf)
      (by rw [abs_of_nonpos hU0, abs_of_nonpos hV0, abs_of_nonpos (by linarith : U + V ≤ 0)]; ring_nf)
      (fun h => by
        rw [abs_of_nonpos hU0, abs_of_nonpos hV0] at h
        have : x = y := by linarith
        rw [ha, hb, this])
    linarith only [hf, g12, g34']

/-! ### The potential of the folded odd part -/

/-- The remainder of the linear gauge on a short window: `surplusRemainder η u ≤ η³/8`. -/
theorem surplusRemainder_le_of_le {η u : ℝ} (hu : 0 ≤ u) (huη : u ≤ η) (hη1 : η ≤ 1 / 12) :
    surplusRemainder η u ≤ η ^ 3 / 8 := by
  have hη : 0 ≤ η := le_trans hu huη
  have h2 : u ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ hu huη 2
  have h3 : u ^ 3 ≤ η ^ 3 := pow_le_pow_left₀ hu huη 3
  have h4 : u ^ 4 ≤ η ^ 4 := pow_le_pow_left₀ hu huη 4
  have h4' : η ^ 4 ≤ η ^ 3 / 12 := by
    have := mul_le_mul_of_nonneg_left hη1 (pow_nonneg hη 3)
    nlinarith
  unfold surplusRemainder
  nlinarith [mul_nonneg hu (pow_nonneg hη 2), mul_nonneg (pow_nonneg hu 2) hη,
    mul_nonneg (pow_nonneg hu 3) hη, mul_nonneg (pow_nonneg hu 2) (pow_nonneg hη 2),
    mul_nonneg hu (pow_nonneg hη 3)]

/-- **The potential of the sharp micro-fold.** In the gauge `g(t) = η/10 + t` on `[0, η]`,
`2U_g(u) + 4K(u) ≥ 1.9 − η/p − 3η²`, `K(u) = Ω(u) − Ω(u + η) − η ω(2p)`: the logarithms of the
surplus and of the killing cancel to the exact odd eigenvalue `2` of the regional logarithmic kernel,
up to the gauge offset and the curvature of `ω`. -/
theorem sharpFold_potential_ge {p η u : ℝ} (hp : 0 < p) (hη : 0 < η) (hη1 : η ≤ 1 / 12)
    (hu : 0 < u) (huη : u ≤ η) :
    19 / 10 - η / p - 3 * η ^ 2 ≤
      2 * surplusPotential (cubicGauge (η / 10) 1 0 0) η u +
        4 * (archLevyAntideriv u - archLevyAntideriv (u + η) - η * archLevyDensity (2 * p)) := by
  have hl2 := Real.log_two_gt_d9
  set G := η / 10 + u with hG
  have hG0 : 0 < G := by positivity
  have hg : cubicGauge (η / 10) 1 0 0 u = G := by unfold cubicGauge; rw [hG]; ring
  have hU := mul_surplusPotential_cubicGauge_ge (η / 10) 1 0 0 (L := 1) hu huη (by linarith)
    (by rw [hg]; exact hG0) (fun _ _ _ _ _ _ => by norm_num)
  rw [hg] at hU
  set Up := surplusPotential (cubicGauge (η / 10) 1 0 0) η u with hUp
  set ℓ := Real.log (u + η) - Real.log u with hℓ
  have hmain : cubicSurplusMain 1 0 0 η u = u * (1 - ℓ) := by
    unfold cubicSurplusMain; rw [hℓ, add_comm u η]; ring
  rw [hmain, one_mul] at hU
  -- the window ratio, by the tangent at `2`
  set T := 2 * u / (u + η) with hTdef
  have hℓt : Real.log 2 + 1 - T ≤ ℓ := by
    have := log_ge_tangent (show 0 < (u + η) / u by positivity) (show (0 : ℝ) < 2 by norm_num)
    rw [Real.log_div (by positivity) hu.ne'] at this
    have e : 2 / ((u + η) / u) = T := by rw [hTdef]; field_simp
    rw [e] at this; rw [hℓ]; linarith
  have hT : T * (u + η) = 2 * u := by rw [hTdef]; field_simp
  have hT1 : T ≤ 1 := by rw [hTdef, div_le_one (by positivity)]; linarith
  have hrem := surplusRemainder_le_of_le hu.le huη hη1
  -- the killing on `[0, η]`
  have hΩ1 := archLevyAntideriv_ge hu
  have hΩ2 := archLevyAntideriv_le_expansion (show 0 < u + η by linarith)
  have l4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [Real.log_div hu.ne' (by norm_num), l4] at hΩ1
  rw [Real.log_div (by linarith) (by norm_num), l4] at hΩ2
  have hω := archLevyDensity_le_inv (show 0 < 2 * p by linarith)
  have hηp : η * (1 / (2 * (2 * p)) + 1 / 4) = η / p / 4 + η / 4 := by field_simp; ring
  set K4 := 4 * (archLevyAntideriv u - archLevyAntideriv (u + η) - η * archLevyDensity (2 * p))
    with hK4
  have hK : 2 * ℓ - (u + η) ^ 2 / 24 - 5 * (u + η) ^ 3 / 96 - η / p ≤ K4 := by
    have := mul_le_mul_of_nonneg_left hω hη.le
    rw [hηp] at this
    rw [hK4, hℓ]; linarith
  clear_value Up K4 T ℓ G
  -- the polynomial core
  have hGη : G ≤ 11 / 10 * η := by rw [hG]; linarith
  have hs2 : (u + η) ^ 2 ≤ 4 * η ^ 2 := by nlinarith
  have hs3 : (u + η) ^ 3 ≤ 8 * η ^ 3 := by
    have := pow_le_pow_left₀ (by linarith : 0 ≤ u + η) (by linarith : u + η ≤ 2 * η) 3
    nlinarith
  have hcurv : G * ((u + η) ^ 2 / 24 + 5 * (u + η) ^ 3 / 96) ≤ 23 / 100 * η ^ 3 := by
    have hη3 : η ^ 3 ≤ η ^ 2 / 12 := by nlinarith [pow_pos hη 2]
    have h1 : (u + η) ^ 2 / 24 + 5 * (u + η) ^ 3 / 96 ≤ η ^ 2 / 6 + 5 * η ^ 2 / 144 := by
      linarith only [hs2, hs3, hη3]
    have h2 := mul_le_mul hGη h1 (by positivity) (by positivity)
    linarith only [h2, pow_pos hη 3]
  have hpoly : (19 / 10 * G + 1 / 5 * η ^ 3) * (u + η) ≤
      (2 * u + η / 5 * (6931 / 10000 + 1)) * (u + η) - 2 / 5 * η * u := by
    have hη4 : η ^ 3 * (u + η) ≤ η ^ 2 / 72 := by
      have h1 : η ^ 3 * (u + η) ≤ η ^ 3 * (2 * η) := mul_le_mul_of_nonneg_left (by linarith)
        (pow_nonneg hη.le 3)
      have hη2 : η ^ 2 ≤ 1 / 144 := by
        have := mul_le_mul hη1 hη1 hη.le (by norm_num)
        linarith only [this]
      have h2 := mul_le_mul_of_nonneg_left hη2 (sq_nonneg η)
      linarith only [h1, h2]
    rw [hG]
    linarith only [sq_nonneg (u - 7569 / 10000 * η), hη4, sq_nonneg η]
  have hcore : 19 / 10 * G + 1 / 5 * η ^ 3 ≤ 2 * u + η / 5 * (6931 / 10000 + 1 - T) := by
    have hpos : 0 < u + η := by linarith
    have e : (2 * u + η / 5 * (6931 / 10000 + 1)) * (u + η) - 2 / 5 * η * u =
        (2 * u + η / 5 * (6931 / 10000 + 1 - T)) * (u + η) := by
      have : η / 5 * T * (u + η) = 2 / 5 * η * u := by
        rw [mul_assoc, hT]; ring
      linear_combination this
    rw [e] at hpoly
    exact le_of_mul_le_mul_right hpoly hpos
  -- assembly
  have hGU := mul_le_mul_of_nonneg_left (show G * Up ≥ u * (1 - ℓ) - surplusRemainder η u from hU)
    (show (0 : ℝ) ≤ 2 by norm_num)
  have hGK := mul_le_mul_of_nonneg_left hK hG0.le
  have hℓG := mul_le_mul_of_nonneg_left hℓt (show (0 : ℝ) ≤ η / 5 by positivity)
  have key : G * (19 / 10 - η / p - 3 * η ^ 2) ≤ G * (2 * Up + K4) := by
    have e1 : G * (2 * Up + K4) = 2 * (G * Up) + G * K4 := by ring
    have e2 : G * (2 * ℓ - (u + η) ^ 2 / 24 - 5 * (u + η) ^ 3 / 96 - η / p) =
        2 * u * ℓ + η / 5 * ℓ - G * ((u + η) ^ 2 / 24 + 5 * (u + η) ^ 3 / 96) - G * (η / p) := by
      rw [hG]; ring
    have e3 : G * (19 / 10 - η / p - 3 * η ^ 2) = 19 / 10 * G - G * (η / p) - 3 * η ^ 2 * G := by
      ring
    have hG3 : 3 / 10 * η ^ 3 ≤ 3 * η ^ 2 * G := by
      rw [hG]; linarith only [mul_nonneg (pow_nonneg hη.le 2) hu.le]
    have s1 : 2 * u - 2 * surplusRemainder η u + η / 5 * ℓ -
        G * ((u + η) ^ 2 / 24 + 5 * (u + η) ^ 3 / 96) - G * (η / p) ≤ G * (2 * Up + K4) := by
      rw [e1]; rw [e2] at hGK; linarith only [hGU, hGK]
    have s2 : η / 5 * (6931 / 10000) ≤ η / 5 * Real.log 2 :=
      mul_le_mul_of_nonneg_left (by linarith only [hl2]) (by positivity)
    have s3 : 19 / 10 * G + 1 / 5 * η ^ 3 - η ^ 3 / 4 - 23 / 100 * η ^ 3 - G * (η / p) ≤
        2 * u - 2 * surplusRemainder η u + η / 5 * ℓ -
          G * ((u + η) ^ 2 / 24 + 5 * (u + η) ^ 3 / 96) - G * (η / p) := by
      linarith only [hcore, hℓG, s2, hrem, hcurv]
    rw [e3]
    linarith only [s1, s3, hG3, pow_pos hη 3]
  exact le_of_mul_le_mul_left key hG0

/-! ### The integrated weight -/

theorem measurable_sharpFoldWeight (p β : ℝ) :
    Measurable (Function.uncurry (sharpFoldWeight p β)) := by
  unfold sharpFoldWeight microFoldKernel
  have hk : Measurable fun z : ℝ × ℝ => surplusKernel z.1 z.2 := measurable_surplusKernel
  refine ((hk.mul (measurable_const.sub ((measurable_const.add measurable_snd).div
    (measurable_const.add measurable_fst)))).const_mul 2).add
    (((measurable_archLevyDensity.comp (measurable_fst.add measurable_snd)).sub
      measurable_const).const_mul 4)

/-- The weight is bounded on the half-window by `3/β + 4(ω(u + v) + |ω(2p)|)`. -/
theorem abs_sharpFoldWeight_le {p β u v : ℝ} (hβ : 0 < β) (hu : 0 < u) (hv : 0 ≤ v)
    (huv : |u - v| ≤ 1) :
    |sharpFoldWeight p β u v| ≤ 3 / β + 4 * (archLevyDensity (u + v) + |archLevyDensity (2 * p)|) := by
  unfold sharpFoldWeight microFoldKernel
  have h1 : |surplusKernel u v * (1 - (β + v) / (β + u))| ≤ 3 / 2 * |(1 : ℝ)| / β := by
    rcases eq_or_lt_of_le hv with h0 | h0
    · rw [← h0, surplusKernel_comm, surplusKernel_zero_left hu.le, zero_mul, abs_zero]
      positivity
    refine abs_surplusKernel_mul_le (h := fun t => β + t) hu h0 huv hβ (by linarith) ?_
    simp only [one_mul]; rw [show β + u - (β + v) = u - v by ring]
  rw [abs_one, mul_one] at h1
  have h2 := archLevyDensity_pos (show 0 < u + v by linarith)
  have h3 := abs_sub (archLevyDensity (u + v)) (archLevyDensity (2 * p))
  rw [abs_of_pos h2] at h3
  have h4 := abs_add_le (2 * (surplusKernel u v * (1 - (β + v) / (β + u))))
    (4 * (archLevyDensity (u + v) - archLevyDensity (2 * p)))
  rw [abs_mul, abs_mul (4 : ℝ), abs_two, show |(4 : ℝ)| = 4 by norm_num] at h4
  have : 2 * (3 / 2 / β) = 3 / β := by ring
  linarith

/-- Integrals of a function of `|y − m|` over a window symmetric about `m`. -/
theorem integral_abs_sub_symm {w : ℝ → ℝ} {m η C : ℝ} (hη : 0 ≤ η) (hwm : Measurable w)
    (hwb : ∀ v ∈ Icc 0 η, |w v| ≤ C) :
    (∫ y in (m - η)..(m + η), w |y - m|) = 2 * ∫ v in (0 : ℝ)..η, w v := by
  have hleft : (∫ y in (m - η)..m, w |y - m|) = ∫ v in (0 : ℝ)..η, w v := by
    have e : EqOn (fun y => w |y - m|) (fun y => w (m - y)) (uIcc (m - η) m) := fun y hy => by
      rw [uIcc_of_le (by linarith)] at hy
      simp only [abs_of_nonpos (by linarith [hy.2] : y - m ≤ 0), neg_sub]
    rw [intervalIntegral.integral_congr e, intervalIntegral.integral_comp_sub_left (fun v => w v) m,
      sub_self, show m - (m - η) = η by ring]
  have hright : (∫ y in m..(m + η), w |y - m|) = ∫ v in (0 : ℝ)..η, w v := by
    have e : EqOn (fun y => w |y - m|) (fun y => w (y - m)) (uIcc m (m + η)) := fun y hy => by
      rw [uIcc_of_le (by linarith)] at hy
      simp only [abs_of_nonneg (by linarith [hy.1] : 0 ≤ y - m)]
    rw [intervalIntegral.integral_congr e, intervalIntegral.integral_comp_sub_right (fun v => w v) m,
      sub_self, show m + η - m = η by ring]
  have hwm' : Measurable fun y => w |y - m| := hwm.comp (measurable_id.sub_const m).abs
  have hiL : IntervalIntegrable (fun y => w |y - m|) volume (m - η) m :=
    intervalIntegrable_of_abs_le (by linarith) hwm'
      fun y hy => hwb _ ⟨abs_nonneg _, by rw [abs_le]; constructor <;> linarith [hy.1, hy.2]⟩
  have hiR : IntervalIntegrable (fun y => w |y - m|) volume m (m + η) :=
    intervalIntegrable_of_abs_le (by linarith) hwm'
      fun y hy => hwb _ ⟨abs_nonneg _, by rw [abs_le]; constructor <;> linarith [hy.1, hy.2]⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hiL hiR, hleft, hright]
  ring

/-- The transformed surplus of the linear gauge as an interval integral. -/
theorem integral_surplus_linearGauge {η u : ℝ} (hη : 0 ≤ η) :
    (∫ v in (0 : ℝ)..η, surplusKernel u v * (1 - (η / 10 + v) / (η / 10 + u))) =
      surplusPotential (cubicGauge (η / 10) 1 0 0) η u := by
  unfold surplusPotential
  rw [intervalIntegral.integral_of_le hη]
  refine setIntegral_congr_fun measurableSet_Ioc fun v _ => ?_
  simp only [cubicGauge]; ring_nf

/-- The killing of the folded odd part: `∫_0^η k₀(u + v) dv = Ω(u) − Ω(u + η) − η ω(2p)`. -/
theorem integral_microFoldKernel_add {p η u : ℝ} (hη : 0 ≤ η) (hu : 0 < u) :
    (∫ v in (0 : ℝ)..η, microFoldKernel p (u + v)) =
      archLevyAntideriv u - archLevyAntideriv (u + η) - η * archLevyDensity (2 * p) := by
  unfold microFoldKernel
  have hc : ContinuousOn (fun v => archLevyDensity (u + v)) (uIcc 0 η) := by
    refine continuousOn_archLevyDensity.comp (by fun_prop) fun v hv => ?_
    rw [uIcc_of_le hη] at hv
    exact mem_Ioi.mpr (by linarith [hv.1])
  rw [intervalIntegral.integral_sub hc.intervalIntegrable intervalIntegrable_const,
    intervalIntegral.integral_comp_add_left (fun t => archLevyDensity t) u, add_zero,
    integral_archLevyDensity_Icc hu (by linarith), intervalIntegral.integral_const, smul_eq_mul,
    sub_zero]

/-- **The integrated weight.** For `0 < u ≤ η`,
`∫_{m−η}^{m+η} W(u, |y − m|) dy = 2 (2U_g(u) + 4K(u))`, `g(t) = η/10 + t`. -/
theorem integral_sharpFoldWeight {p η u m : ℝ} (hη : 0 < η) (hu : 0 < u) (huη : u ≤ η)
    (hη1 : η ≤ 1) :
    (∫ y in (m - η)..(m + η), sharpFoldWeight p (η / 10) u |y - m|) =
      2 * (2 * surplusPotential (cubicGauge (η / 10) 1 0 0) η u +
        4 * (archLevyAntideriv u - archLevyAntideriv (u + η) - η * archLevyDensity (2 * p))) := by
  have hβ : 0 < η / 10 := by positivity
  have hwm : Measurable (sharpFoldWeight p (η / 10) u) :=
    (measurable_sharpFoldWeight p (η / 10)).of_uncurry_left
  have hwb : ∀ v ∈ Icc 0 η, |sharpFoldWeight p (η / 10) u v| ≤
      3 / (η / 10) + 4 * (archLevyDensity u + |archLevyDensity (2 * p)|) := fun v hv => by
    have := abs_sharpFoldWeight_le (p := p) hβ hu hv.1
      (by rw [abs_le]; constructor <;> linarith [hv.1, hv.2])
    have hmono : archLevyDensity (u + v) ≤ archLevyDensity u :=
      strictAntiOn_archLevyDensity.antitoneOn hu (show 0 < u + v by linarith [hv.1])
        (by linarith [hv.1])
    linarith
  rw [integral_abs_sub_symm hη.le hwm hwb]
  have hi1 : IntervalIntegrable (fun v => surplusKernel u v * (1 - (η / 10 + v) / (η / 10 + u)))
      volume 0 η := by
    refine intervalIntegrable_of_abs_le (C := 3 / 2 * |(1 : ℝ)| / (η / 10)) hη.le
      ((measurable_surplusKernel.of_uncurry_left).mul (measurable_const.sub
        ((measurable_const.add measurable_id).div measurable_const))) fun v hv => ?_
    rcases eq_or_lt_of_le hv.1 with h0 | h0
    · rw [← h0, surplusKernel_comm, surplusKernel_zero_left hu.le, zero_mul, abs_zero]
      positivity
    exact abs_surplusKernel_mul_le (h := fun t => η / 10 + t) hu h0
      (by rw [abs_le]; constructor <;> linarith [hv.1, hv.2]) hβ (by linarith)
      (by simp only [one_mul]; rw [show η / 10 + u - (η / 10 + v) = u - v by ring])
  have hi2 : IntervalIntegrable (fun v => microFoldKernel p (u + v)) volume 0 η := by
    unfold microFoldKernel
    refine ContinuousOn.intervalIntegrable ?_
    refine (continuousOn_archLevyDensity.comp (by fun_prop) fun v hv => ?_).sub continuousOn_const
    rw [uIcc_of_le hη.le] at hv
    exact mem_Ioi.mpr (by linarith [hv.1])
  have hsplit : (∫ v in (0 : ℝ)..η, sharpFoldWeight p (η / 10) u v) =
      2 * (∫ v in (0 : ℝ)..η, surplusKernel u v * (1 - (η / 10 + v) / (η / 10 + u))) +
        4 * ∫ v in (0 : ℝ)..η, microFoldKernel p (u + v) := by
    unfold sharpFoldWeight
    rw [intervalIntegral.integral_add (hi1.const_mul 2) (hi2.const_mul 4),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hsplit, integral_surplus_linearGauge hη.le, integral_microFoldKernel_add hη.le hu]

/-! ### The sharp micro-fold of the strip -/

/-- Measurability of a kernel read at the folded distances `|x − m|`, `|y − m|`. -/
theorem measurable_uncurry_abs_sub {f : ℝ → ℝ → ℝ} (hf : Measurable (Function.uncurry f)) (m : ℝ) :
    Measurable fun z : ℝ × ℝ => f |z.1 - m| |z.2 - m| :=
  hf.comp ((measurable_fst.sub_const m).abs.prodMk (measurable_snd.sub_const m).abs)

/-- Fubini on a box for a bounded measurable kernel: the two orders of integration agree. -/
theorem integral_integral_swap_box {f : ℝ → ℝ → ℝ} {p r C : ℝ} (hpr : p ≤ r)
    (hf : Measurable (Function.uncurry f)) (hb : ∀ x ∈ Icc p r, ∀ y ∈ Icc p r, |f x y| ≤ C) :
    (∫ x in p..r, ∫ y in p..r, f y x) = ∫ x in p..r, ∫ y in p..r, f x y := by
  have hint : Integrable (Function.uncurry fun x y => f y x)
      ((volume.restrict (Ioc p r)).prod (volume.restrict (Ioc p r))) := by
    rw [Measure.prod_restrict]
    refine Measure.integrableOn_of_bounded (M := C) ?_ ?_ ?_
    · rw [Measure.prod_prod]; exact ENNReal.mul_ne_top (by simp) (by simp)
    · exact (hf.comp measurable_swap).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with z hz
      rw [Real.norm_eq_abs]
      exact hb z.2 ⟨hz.2.1.le, hz.2.2⟩ z.1 ⟨hz.1.1.le, hz.1.2⟩
  have e1 : (∫ x in p..r, ∫ y in p..r, f y x) = ∫ x in Ioc p r, ∫ y in Ioc p r, f y x := by
    rw [intervalIntegral.integral_of_le hpr]
    refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
    rw [intervalIntegral.integral_of_le hpr]
  have e2 : (∫ x in p..r, ∫ y in p..r, f x y) = ∫ x in Ioc p r, ∫ y in Ioc p r, f x y := by
    rw [intervalIntegral.integral_of_le hpr]
    refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
    rw [intervalIntegral.integral_of_le hpr]
  rw [e1, e2]
  exact integral_integral_swap (f := fun x y => f y x) hint

/-- The odd part about `L/2` vanishes linearly at the centre: `|α(x)| ≤ K |x − L/2|`. -/
theorem abs_reflectedOddPart_le {F : ℝ → ℝ} {K L : ℝ} (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|)
    (x : ℝ) : |reflectedOddPart F L x| ≤ K * |x - L / 2| := by
  unfold reflectedOddPart
  have := hFL x (L - x)
  rw [show x - (L - x) = 2 * (x - L / 2) by ring, abs_mul, abs_two] at this
  rw [abs_div, abs_two]; linarith

/-- The folded potential bound: `|α(x)² W(|x − m|, |y − m|)| ≤ C_Φ` on the strip. -/
theorem abs_foldedWeight_le {F : ℝ → ℝ} {K p L η x y : ℝ} (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|)
    (hη0 : 0 < η) (hη12 : η ≤ 1 / 12) (hu : |x - L / 2| ≤ η) (hv : |y - L / 2| ≤ η) :
    abs (reflectedOddPart F L x ^ 2 * sharpFoldWeight p (η / 10) |x - L / 2| |y - L / 2|) ≤
      30 * K ^ 2 * η + K ^ 2 * (2 * η + η ^ 2) + 4 * K ^ 2 * η ^ 2 * |archLevyDensity (2 * p)| := by
  have hβ : 0 < η / 10 := by positivity
  have hα := abs_reflectedOddPart_le (L := L) hFL x
  have hK0 : 0 ≤ K := by
    have := hFL 1 0; norm_num at this; linarith [abs_nonneg (F 1 - F 0)]
  have hα2 : reflectedOddPart F L x ^ 2 ≤ K ^ 2 * |x - L / 2| ^ 2 := by
    rw [← sq_abs]
    have := mul_le_mul hα hα (abs_nonneg _) (by positivity)
    nlinarith [abs_nonneg (reflectedOddPart F L x)]
  have hC0 : 0 ≤ 30 * K ^ 2 * η + K ^ 2 * (2 * η + η ^ 2) +
      4 * K ^ 2 * η ^ 2 * |archLevyDensity (2 * p)| := by positivity
  rcases eq_or_lt_of_le (abs_nonneg (x - L / 2)) with h0 | h0
  · have : reflectedOddPart F L x = 0 := by
      rw [← h0, mul_zero] at hα; exact abs_nonpos_iff.mp hα
    rw [this]; simpa using hC0
  set u := |x - L / 2| with hudef
  set v := |y - L / 2| with hvdef
  have hv0 : 0 ≤ v := abs_nonneg _
  have hW := abs_sharpFoldWeight_le (p := p) hβ h0 hv0
    (by rw [abs_le]; constructor <;> linarith)
  have hω := archLevyDensity_le_inv (show 0 < u + v by positivity)
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  have hω0 := archLevyDensity_pos (show 0 < u + v by positivity)
  calc reflectedOddPart F L x ^ 2 * |sharpFoldWeight p (η / 10) u v|
      ≤ K ^ 2 * u ^ 2 * (3 / (η / 10) + 4 * (archLevyDensity (u + v) +
          |archLevyDensity (2 * p)|)) := mul_le_mul hα2 hW (abs_nonneg _) (by positivity)
    _ ≤ 30 * K ^ 2 * η + K ^ 2 * (2 * η + η ^ 2) +
          4 * K ^ 2 * η ^ 2 * |archLevyDensity (2 * p)| := by
      have hu2 : u ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hu 2
      have e30 : K ^ 2 * u ^ 2 * (3 / (η / 10)) ≤ 30 * K ^ 2 * η := by
        have e : K ^ 2 * u ^ 2 * (3 / (η / 10)) = 30 * K ^ 2 * (u ^ 2 / η) := by
          field_simp; ring
        rw [e]
        have : u ^ 2 / η ≤ η := by rw [div_le_iff₀ hη0]; nlinarith
        exact mul_le_mul_of_nonneg_left this (by positivity)
      have h1 : u ^ 2 * archLevyDensity (u + v) ≤ u / 2 + u ^ 2 / 4 := by
        have h2 := mul_le_mul_of_nonneg_left hω (sq_nonneg u)
        have h3 : u ^ 2 * (1 / (2 * (u + v))) ≤ u / 2 := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        nlinarith
      have h4 : K ^ 2 * (u ^ 2 * archLevyDensity (u + v)) ≤ K ^ 2 * (u / 2 + u ^ 2 / 4) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg K)
      have h5 : K ^ 2 * (u / 2 + u ^ 2 / 4) ≤ K ^ 2 * ((2 * η + η ^ 2) / 4) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg K)
      have h6 : K ^ 2 * u ^ 2 * |archLevyDensity (2 * p)| ≤
          K ^ 2 * η ^ 2 * |archLevyDensity (2 * p)| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu2 (sq_nonneg K)) (abs_nonneg _)
      have e : K ^ 2 * u ^ 2 * (3 / (η / 10) + 4 * (archLevyDensity (u + v) +
          |archLevyDensity (2 * p)|)) = K ^ 2 * u ^ 2 * (3 / (η / 10)) +
          4 * (K ^ 2 * (u ^ 2 * archLevyDensity (u + v))) +
          4 * (K ^ 2 * u ^ 2 * |archLevyDensity (2 * p)|) := by ring
      rw [e]
      linarith

section SharpStrip

variable {F : ℝ → ℝ} {K p r L : ℝ} (hF : Continuous F) (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|)
  (hp : 0 < p) (hpr : p < r) (hL : p + r = L) (hr3 : r - p ≤ 2 * p) (hr6 : r - p ≤ 1 / 6)

include hF hFL hp hpr hL hr3 hr6 in
/-- **The sharp micro-fold of the strip.** With `η = (r − p)/2` and `p + r = L`,
`∫_p^r ∫_p^r k(x, y)(F x − F y)² ≥ (1.9 − η/p − 3η²) ∫_p^r α²`. -/
theorem sharpMicroFold_strip_ge :
    (19 / 10 - (r - p) / 2 / p - 3 * ((r - p) / 2) ^ 2) * (∫ x in p..r, reflectedOddPart F L x ^ 2) ≤
      ∫ x in p..r, ∫ y in p..r, surplusKernel x y * (F x - F y) ^ 2 := by
  have hr1 : r - p ≤ 1 := by linarith
  set C : ℝ := 3 / 2 * K ^ 2 * (r - p) with hC
  have hmg := measurable_stripIntegrand hF
  have hrefl : ∀ x, x ∈ Icc p r → L - x ∈ Icc p r := fun x hx =>
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hbd : ∀ x ∈ Icc p r, ∀ y ∈ Icc p r, |stripIntegrand F x y| ≤ C := fun x hx y hy =>
    abs_strip_integrand_le hFL hp hr1 hx hy
  obtain ⟨hi0, ho0⟩ := intervalIntegrable_iterated hpr.le hmg hbd
  have hm1 := measurable_uncurry_reflect_both hmg L
  have hm2 := measurable_uncurry_reflect_snd hmg L
  have hm3 := measurable_uncurry_reflect_fst hmg L
  obtain ⟨hi1, ho1⟩ := intervalIntegrable_iterated hpr.le hm1 fun x hx y hy =>
    hbd _ (hrefl x hx) _ (hrefl y hy)
  obtain ⟨hi2, ho2⟩ := intervalIntegrable_iterated hpr.le hm2 fun x hx y hy =>
    hbd _ hx _ (hrefl y hy)
  obtain ⟨hi3, ho3⟩ := intervalIntegrable_iterated hpr.le hm3 fun x hx y hy =>
    hbd _ (hrefl x hx) _ hy
  set T := ∫ x in p..r, ∫ y in p..r, stripIntegrand F x y with hT
  -- the three reflected copies equal `T`
  have hT1 : (∫ x in p..r, ∫ y in p..r, stripIntegrand F (L - x) (L - y)) = T := by
    have e : (fun x => ∫ y in p..r, stripIntegrand F (L - x) (L - y)) = fun x => ∫ y in p..r, stripIntegrand F (L - x) y :=
      funext fun x => integral_strip_reflect hL (stripIntegrand F (L - x))
    rw [e]
    exact integral_strip_reflect hL (fun x => ∫ y in p..r, stripIntegrand F x y)
  have hT2 : (∫ x in p..r, ∫ y in p..r, stripIntegrand F x (L - y)) = T := by
    have e : (fun x => ∫ y in p..r, stripIntegrand F x (L - y)) = fun x => ∫ y in p..r, stripIntegrand F x y :=
      funext fun x => integral_strip_reflect hL (stripIntegrand F x)
    rw [e]
  have hT3 : (∫ x in p..r, ∫ y in p..r, stripIntegrand F (L - x) y) = T :=
    integral_strip_reflect hL (fun x => ∫ y in p..r, stripIntegrand F x y)
  -- the sum of the four copies, as one iterated integral
  have hsum : (∫ x in p..r, ∫ y in p..r, (stripIntegrand F x y + stripIntegrand F (L - x) (L - y) + stripIntegrand F x (L - y) + stripIntegrand F (L - x) y)) =
      4 * T := by
    have hin : ∀ x ∈ uIcc p r, (∫ y in p..r, (stripIntegrand F x y + stripIntegrand F (L - x) (L - y) + stripIntegrand F x (L - y) + stripIntegrand F (L - x) y)) =
        (∫ y in p..r, stripIntegrand F x y) + (∫ y in p..r, stripIntegrand F (L - x) (L - y)) + (∫ y in p..r, stripIntegrand F x (L - y)) +
          ∫ y in p..r, stripIntegrand F (L - x) y := fun x hx => by
      rw [uIcc_of_le hpr.le] at hx
      rw [intervalIntegral.integral_add ((hi0 x hx).add (hi1 x hx) |>.add (hi2 x hx)) (hi3 x hx),
        intervalIntegral.integral_add ((hi0 x hx).add (hi1 x hx)) (hi2 x hx),
        intervalIntegral.integral_add (hi0 x hx) (hi1 x hx)]
    rw [intervalIntegral.integral_congr hin, intervalIntegral.integral_add ((ho0.add ho1).add ho2) ho3,
      intervalIntegral.integral_add (ho0.add ho1) ho2, intervalIntegral.integral_add ho0 ho1,
      hT1, hT2, hT3]
    ring
  -- integrability of the summed integrand
  have hms : Measurable (Function.uncurry fun x y => stripIntegrand F x y +
      stripIntegrand F (L - x) (L - y) + stripIntegrand F x (L - y) + stripIntegrand F (L - x) y) := by
    have := ((hmg.add hm1).add hm2).add hm3
    exact this
  obtain ⟨his, hos⟩ := intervalIntegrable_iterated (C := 4 * C) hpr.le hms fun x hx y hy => by
    have h0 := hbd x hx y hy
    have h1 := hbd _ (hrefl x hx) _ (hrefl y hy)
    have h2 := hbd _ hx _ (hrefl y hy)
    have h3 := hbd _ (hrefl x hx) _ hy
    calc |stripIntegrand F x y + stripIntegrand F (L - x) (L - y) + stripIntegrand F x (L - y) +
          stripIntegrand F (L - x) y|
        ≤ |stripIntegrand F x y| + |stripIntegrand F (L - x) (L - y)| + |stripIntegrand F x (L - y)| +
          |stripIntegrand F (L - x) y| := by
          have := abs_add_le (stripIntegrand F x y + stripIntegrand F (L - x) (L - y) +
            stripIntegrand F x (L - y)) (stripIntegrand F (L - x) y)
          have := abs_add_le (stripIntegrand F x y + stripIntegrand F (L - x) (L - y))
            (stripIntegrand F x (L - y))
          have := abs_add_le (stripIntegrand F x y) (stripIntegrand F (L - x) (L - y))
          linarith
      _ ≤ 4 * C := by linarith
  -- the folded weight
  set η := (r - p) / 2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hη12 : η ≤ 1 / 12 := by rw [hη]; linarith
  have hmp : L / 2 - η = p := by rw [hη]; linarith
  have hmr : L / 2 + η = r := by rw [hη]; linarith
  have hβ : 0 < η / 10 := by positivity
  have hαc : Continuous fun x => reflectedOddPart F L x ^ 2 := by
    unfold reflectedOddPart; fun_prop
  have hΦm : Measurable (Function.uncurry fun x y =>
      reflectedOddPart F L x ^ 2 * sharpFoldWeight p (η / 10) |x - L / 2| |y - L / 2|) :=
    ((hαc.measurable.comp measurable_fst).mul
      (measurable_uncurry_abs_sub (measurable_sharpFoldWeight p (η / 10)) (L / 2)))
  have hΦb : ∀ x ∈ Icc p r, ∀ y ∈ Icc p r,
      abs (reflectedOddPart F L x ^ 2 * sharpFoldWeight p (η / 10) |x - L / 2| |y - L / 2|) ≤
        30 * K ^ 2 * η + K ^ 2 * (2 * η + η ^ 2) + 4 * K ^ 2 * η ^ 2 * |archLevyDensity (2 * p)| :=
    fun x hx y hy => abs_foldedWeight_le hFL hη0 hη12
      (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2])
      (by rw [abs_le]; constructor <;> linarith [hy.1, hy.2])
  obtain ⟨hiΦ, hoΦ⟩ := intervalIntegrable_iterated hpr.le hΦm hΦb
  have hΦm' : Measurable (Function.uncurry fun x y =>
      reflectedOddPart F L y ^ 2 * sharpFoldWeight p (η / 10) |y - L / 2| |x - L / 2|) :=
    hΦm.comp measurable_swap
  obtain ⟨hiΦ', hoΦ'⟩ := intervalIntegrable_iterated hpr.le hΦm' fun x hx y hy => hΦb y hy x hx
  -- the pointwise inequality, integrated
  have hinner1 : ∀ x ∈ Icc p r,
      (∫ y in p..r, reflectedOddPart F L x ^ 2 * sharpFoldWeight p (η / 10) |x - L / 2| |y - L / 2|) +
        (∫ y in p..r, reflectedOddPart F L y ^ 2 * sharpFoldWeight p (η / 10) |y - L / 2| |x - L / 2|) ≤
      ∫ y in p..r, (stripIntegrand F x y + stripIntegrand F (L - x) (L - y) +
        stripIntegrand F x (L - y) + stripIntegrand F (L - x) y) := fun x hx => by
    rw [← intervalIntegral.integral_add (hiΦ x hx) (hiΦ' x hx)]
    refine intervalIntegral.integral_mono_on hpr.le ((hiΦ x hx).add (hiΦ' x hx)) (his x hx)
      fun y hy => ?_
    unfold stripIntegrand
    exact sharpQuadruple_ge hp hL hr3 hβ hx hy F
  have hint1 :
      (∫ x in p..r, ∫ y in p..r,
          reflectedOddPart F L x ^ 2 * sharpFoldWeight p (η / 10) |x - L / 2| |y - L / 2|) +
        (∫ x in p..r, ∫ y in p..r,
          reflectedOddPart F L y ^ 2 * sharpFoldWeight p (η / 10) |y - L / 2| |x - L / 2|) ≤
        4 * T := by
    rw [← intervalIntegral.integral_add hoΦ hoΦ', ← hsum]
    exact intervalIntegral.integral_mono_on hpr.le (hoΦ.add hoΦ') hos fun x hx => hinner1 x hx
  have hswap := integral_integral_swap_box hpr.le hΦm hΦb
  -- the inner integral is the potential of the folded odd part
  have hinner : ∀ x ∈ Icc p r, 2 * (19 / 10 - η / p - 3 * η ^ 2) * reflectedOddPart F L x ^ 2 ≤
      ∫ y in p..r, reflectedOddPart F L x ^ 2 * sharpFoldWeight p (η / 10) |x - L / 2| |y - L / 2| := by
    intro x hx
    have hu : |x - L / 2| ≤ η := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
    rcases eq_or_lt_of_le (abs_nonneg (x - L / 2)) with h0 | h0
    · have hα := abs_reflectedOddPart_le (L := L) hFL x
      have : reflectedOddPart F L x = 0 := by
        rw [← h0, mul_zero] at hα; exact abs_nonpos_iff.mp hα
      rw [this]; simp
    have hI := integral_sharpFoldWeight (p := p) (m := L / 2) hη0 h0 hu (by linarith)
    rw [hmp, hmr] at hI
    rw [intervalIntegral.integral_const_mul, hI]
    have hpot := sharpFold_potential_ge hp hη0 hη12 h0 hu
    rw [mul_comm (2 * (19 / 10 - η / p - 3 * η ^ 2))]
    exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
  have hmono := intervalIntegral.integral_mono_on hpr.le ((hαc.intervalIntegrable p r).const_mul
    (2 * (19 / 10 - η / p - 3 * η ^ 2))) hoΦ fun x hx => hinner x hx
  rw [intervalIntegral.integral_const_mul] at hmono
  rw [hswap] at hint1
  have hTdef : T = ∫ x in p..r, ∫ y in p..r, surplusKernel x y * (F x - F y) ^ 2 := rfl
  rw [← hTdef]
  linarith

end SharpStrip

/-! ### Every prime-power atom -/

/-- `Λ(n)/√n ≤ log n/√n ≤ 2/e < 0.7358` for every `n`. -/
theorem vonMangoldtAtom_le (n : ℕ) : vonMangoldtAtom n ≤ 7358 / 10000 := by
  unfold vonMangoldtAtom
  split_ifs with hn
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    have he := Real.exp_one_gt_d9
    have hΛ : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
    -- `log y ≤ y/e`
    have hlog : Real.log (Real.sqrt n) ≤ Real.sqrt n / Real.exp 1 := by
      have h1 := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt n / Real.exp 1 by positivity)
      rw [Real.log_div hs.ne' (Real.exp_pos 1).ne', Real.log_exp] at h1
      linarith
    have hln : Real.log n = 2 * Real.log (Real.sqrt n) := by
      rw [Real.log_sqrt hn0.le]; ring
    rw [div_le_iff₀ hs]
    have h2 : 2 * (Real.sqrt n / Real.exp 1) ≤ 7358 / 10000 * Real.sqrt n := by
      rw [show 2 * (Real.sqrt n / Real.exp 1) = Real.sqrt n * (2 / Real.exp 1) by ring,
        mul_comm (7358 / 10000 : ℝ)]
      refine mul_le_mul_of_nonneg_left ?_ hs.le
      rw [div_le_iff₀ (Real.exp_pos 1)]; linarith
    linarith
  · norm_num

theorem vonMangoldtAtom_nonneg (n : ℕ) : 0 ≤ vonMangoldtAtom n := by
  unfold vonMangoldtAtom
  split_ifs
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  · exact le_rfl

section PrimePower

variable {F : ℝ → ℝ} {K r : ℝ} {n : ℕ} (hn : 2 ≤ n) (hF : Continuous F) (hFc : HasCompactSupport F)
  (hodd : ∀ x, F (-x) = -F x) (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|)
  (hsupp : ∀ x, r < |x| → F x = 0) (hr : Real.log n / 2 < r) (hr' : r ≤ Real.log n / 2 + 1 / 12)

include hn hF hFc hodd hFL hsupp hr hr' in
/-- **Harnack across every prime-power shift.** For `n ≥ 2` and every odd `F` supported in
`[−r, r]`, `½ log n < r ≤ ½ log n + 1/12`, the atom of `n` is paid by the archimedean surplus of its
reflection strip `S_n = [log n − r, r]`:
`2 Λ(n)/√n ∫ F(x) F(x + log n) dx ≤ ∫_{S_n} ∫_{S_n} k(x, y)(F x − F y)²`. -/
theorem two_mul_primePowerShift_le_stripSurplus :
    2 * (vonMangoldtAtom n * ∫ x, F x * F (x + Real.log n)) ≤
      2 * stripSurplus F (Real.log n - r) r := by
  have hl2 := Real.log_two_gt_d9
  have hn2 : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  set L := Real.log n with hLdef
  set p := L - r with hpdef
  have hpr : p < r := by rw [hpdef]; linarith
  have hp : 26324 / 100000 ≤ p := by rw [hpdef]; linarith
  have hp0 : 0 < p := by linarith
  have hL : p + r = L := by rw [hpdef]; ring
  have hr3 : r - p ≤ 2 * p := by rw [hpdef]; linarith
  have hr6 : r - p ≤ 1 / 6 := by rw [hpdef]; linarith
  have hr1 : r - p ≤ 1 := by linarith
  have hms := sharpMicroFold_strip_ge hF hFL hp0 hpr hL hr3 hr6
  have hT : (∫ x in p..r, ∫ y in p..r, surplusKernel x y * (F x - F y) ^ 2) =
      2 * stripSurplus F p r := integral_strip_eq_two_mul_stripSurplus hF hFL hp0 hpr.le hr1
  have hshift := integral_mul_shift_le_reflectedOdd hF hFc hodd (r := r) (L := L) (by linarith)
    (by rw [← hpdef]; exact hpr.le) hsupp
  rw [← hpdef] at hshift
  have hw0 := vonMangoldtAtom_nonneg n
  have hw1 := vonMangoldtAtom_le n
  have hα0 : 0 ≤ ∫ x in p..r, reflectedOddPart F L x ^ 2 :=
    intervalIntegral.integral_nonneg hpr.le fun _ _ => sq_nonneg _
  -- the constant of the sharp micro-fold exceeds `2 · 0.7358`
  have hη : (r - p) / 2 ≤ 1 / 12 := by linarith
  have hηp : (r - p) / 2 / p ≤ 317 / 1000 := by
    rw [div_le_iff₀ hp0]; linarith
  have hη2 : 3 * ((r - p) / 2) ^ 2 ≤ 3 / 144 := by
    have h0 : 0 ≤ (r - p) / 2 := by linarith
    nlinarith
  have hC : 2 * (7358 / 10000) ≤ 19 / 10 - (r - p) / 2 / p - 3 * ((r - p) / 2) ^ 2 := by linarith
  have k1 := mul_le_mul_of_nonneg_left hshift hw0
  have k2 := mul_le_mul_of_nonneg_right hC hα0
  have k3 := mul_le_mul_of_nonneg_right hw1 hα0
  linarith

end PrimePower

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
