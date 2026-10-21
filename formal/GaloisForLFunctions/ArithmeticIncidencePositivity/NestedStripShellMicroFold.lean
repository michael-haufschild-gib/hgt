import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimePowerEvenPartHarnack

/-!
# The shell micro-fold: a strip pays its odd part without the pairs of an inner strip

For an odd test supported in `[−r, r]` the prime strips `S_n = [log n − r, r]` share the right end `r`,
so they are nested. On the strip `S = [p, r]`, `L = p + r`, centre `m = L/2`, half-width
`η = (r − p)/2`, let `S' = [p', r]` be an inner strip lying right of the centre, `c = p' − m > 0`.

**Only one pair of a quadruple meets the inner box.** A point `m − u` of the left half never exceeds
`p' > m`, so of the four pairs `x, L − x, y, L − y` only the right–right pair `(m + u, m + v)` can lie in
`(p', r]²`, and it does exactly when `u, v > c` (`u = |x − m|`, `v = |y − m|`). Off this corner the
sharp quadruple bound of `SharpMicroFoldHarnack` holds verbatim for the shell integrand (the strip
integrand with the inner box removed); on the corner the remaining three pairs are nonnegative.

**The corner costs little.** On `c < u, v ≤ η` the folded weight is at most `(2 + η/2)/c + 1`
(`sharpFoldWeight_le_corner`: `k(u, v)(u − v) ≤ ½ + (u − v)/4` and `4ω(u + v) ≤ 1/c + 1`), and the
corner has width `η − c = r − p'`. Hence (`sharpMicroFold_shell_ge`)

    T(p, r) − T(p', r) ≥ (λ₀ − (r − p')((2 + η/2)/c + 1)) ∫_p^r α²,   λ₀ = 1.9 − η/p − 3η²,

`T(p, r) = ∫_p^r ∫_p^r k(x, y)(F x − F y)²` (`stripBoxEnergy`), `α` the odd part of `F` about `m`. The
shell `[p, r]² \ (p', r]²` pays the odd part of the outer atom at a loss of the order of the width
ratio `(r − p')/c` of the two strips, and leaves the inner box to the inner strip.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### Box energies and the shell integrand -/

/-- The surplus energy of the box `[p, r]²`, both orders: `T(p, r) = ∫_p^r ∫_p^r k(x, y)(F x − F y)²`. -/
def stripBoxEnergy (F : ℝ → ℝ) (p r : ℝ) : ℝ := ∫ x in p..r, ∫ y in p..r, stripIntegrand F x y

/-- The strip integrand with the inner box `(p', ∞)²` removed. -/
def shellIntegrand (F : ℝ → ℝ) (p' x y : ℝ) : ℝ :=
  if p' < x ∧ p' < y then 0 else stripIntegrand F x y

/-- The sharp folded weight with the corner `u, v > c` removed. -/
def shellFoldWeight (p β c u v : ℝ) : ℝ := if c < u ∧ c < v then 0 else sharpFoldWeight p β u v

theorem stripIntegrand_nonneg (F : ℝ → ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 ≤ stripIntegrand F x y := by
  unfold stripIntegrand
  by_cases hxy : x = y
  · rw [hxy, sub_self]; simp
  · exact mul_nonneg (surplusKernel_nonneg hx hy hxy) (sq_nonneg _)

theorem shellIntegrand_nonneg (F : ℝ → ℝ) (p' : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 ≤ shellIntegrand F p' x y := by
  unfold shellIntegrand
  split_ifs
  · exact le_rfl
  · exact stripIntegrand_nonneg F hx hy

theorem abs_shellIntegrand_le (F : ℝ → ℝ) (p' x y : ℝ) :
    |shellIntegrand F p' x y| ≤ |stripIntegrand F x y| := by
  unfold shellIntegrand
  split_ifs
  · rw [abs_zero]; exact abs_nonneg _
  · exact le_rfl

theorem measurable_shellIntegrand {F : ℝ → ℝ} (hF : Continuous F) (p' : ℝ) :
    Measurable (Function.uncurry (shellIntegrand F p')) := by
  have hs : MeasurableSet {z : ℝ × ℝ | p' < z.1 ∧ p' < z.2} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const measurable_snd)
  exact Measurable.ite hs measurable_const (measurable_stripIntegrand hF)

theorem measurable_shellFoldWeight (p β c : ℝ) :
    Measurable (Function.uncurry (shellFoldWeight p β c)) := by
  have hs : MeasurableSet {z : ℝ × ℝ | c < z.1 ∧ c < z.2} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const measurable_snd)
  exact Measurable.ite hs measurable_const (measurable_sharpFoldWeight p β)

/-- **Removing the inner box.** For `0 < p ≤ p' ≤ r`, `r − p ≤ 1`:
`∫_p^r ∫_p^r shell = T(p, r) − T(p', r)`. -/
theorem integral_shellIntegrand_eq {F : ℝ → ℝ} {K p p' r : ℝ} (hF : Continuous F)
    (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) (hp : 0 < p) (hpp' : p ≤ p') (hp'r : p' ≤ r)
    (hr1 : r - p ≤ 1) :
    (∫ x in p..r, ∫ y in p..r, shellIntegrand F p' x y) =
      stripBoxEnergy F p r - stripBoxEnergy F p' r := by
  have hpr : p ≤ r := hpp'.trans hp'r
  have hmg := measurable_stripIntegrand hF
  have hbd : ∀ x ∈ Icc p r, ∀ y ∈ Icc p r, |stripIntegrand F x y| ≤ 3 / 2 * K ^ 2 * (r - p) :=
    fun x hx y hy => abs_strip_integrand_le hFL hp hr1 hx hy
  have hbs : ∀ x ∈ Icc p r, ∀ y ∈ Icc p r, |shellIntegrand F p' x y| ≤ 3 / 2 * K ^ 2 * (r - p) :=
    fun x hx y hy => (abs_shellIntegrand_le F p' x y).trans (hbd x hx y hy)
  obtain ⟨hgi, hgo⟩ := intervalIntegrable_iterated hpr hmg hbd
  obtain ⟨hsi, hso⟩ := intervalIntegrable_iterated hpr (measurable_shellIntegrand hF p') hbs
  obtain ⟨-, hgo'⟩ := intervalIntegrable_iterated hp'r hmg fun x hx y hy =>
    hbd x ⟨hpp'.trans hx.1, hx.2⟩ y ⟨hpp'.trans hy.1, hy.2⟩
  have hsub1 : uIcc p p' ⊆ uIcc p r := by
    rw [uIcc_of_le hpp', uIcc_of_le hpr]; exact Icc_subset_Icc le_rfl hp'r
  have hsub2 : uIcc p' r ⊆ uIcc p r := by
    rw [uIcc_of_le hp'r, uIcc_of_le hpr]; exact Icc_subset_Icc hpp' le_rfl
  -- the rows below `p'` keep every pair
  have hlow : (∫ x in p..p', ∫ y in p..r, shellIntegrand F p' x y) =
      ∫ x in p..p', ∫ y in p..r, stripIntegrand F x y := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun x hx => ?_)
    rw [uIoc_of_le hpp'] at hx
    have e : shellIntegrand F p' x = stripIntegrand F x := funext fun y => by
      unfold shellIntegrand; rw [if_neg fun h => absurd h.1 (not_lt.mpr hx.2)]
    rw [e]
  -- the rows above `p'` lose the inner box
  have hhigh : (∫ x in p'..r, ∫ y in p..r, shellIntegrand F p' x y) =
      ∫ x in p'..r, ((∫ y in p..r, stripIntegrand F x y) - ∫ y in p'..r, stripIntegrand F x y) := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun x hx => ?_)
    rw [uIoc_of_le hp'r] at hx
    have hxI : x ∈ Icc p r := ⟨hpp'.trans hx.1.le, hx.2⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals ((hsi x hxI).mono_set hsub1)
        ((hsi x hxI).mono_set hsub2),
      ← intervalIntegral.integral_add_adjacent_intervals ((hgi x hxI).mono_set hsub1)
        ((hgi x hxI).mono_set hsub2)]
    have e1 : (∫ y in p..p', shellIntegrand F p' x y) = ∫ y in p..p', stripIntegrand F x y := by
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun y hy => ?_)
      rw [uIoc_of_le hpp'] at hy
      unfold shellIntegrand; rw [if_neg fun h => absurd h.2 (not_lt.mpr hy.2)]
    have e2 : (∫ y in p'..r, shellIntegrand F p' x y) = ∫ _ in p'..r, (0 : ℝ) := by
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun y hy => ?_)
      rw [uIoc_of_le hp'r] at hy
      unfold shellIntegrand; rw [if_pos ⟨hx.1, hy.1⟩]
    rw [e1, e2, intervalIntegral.integral_zero]
    ring
  unfold stripBoxEnergy
  rw [← intervalIntegral.integral_add_adjacent_intervals (hso.mono_set hsub1) (hso.mono_set hsub2),
    hlow, hhigh, intervalIntegral.integral_sub (hgo.mono_set hsub2) hgo',
    ← intervalIntegral.integral_add_adjacent_intervals (hgo.mono_set hsub1) (hgo.mono_set hsub2)]
  ring

/-- **Nested boxes.** For `0 < p ≤ p' ≤ r`, `r − p ≤ 1`: `T(p', r) ≤ T(p, r)`. -/
theorem stripBoxEnergy_mono {F : ℝ → ℝ} {K p p' r : ℝ} (hF : Continuous F)
    (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) (hp : 0 < p) (hpp' : p ≤ p') (hp'r : p' ≤ r)
    (hr1 : r - p ≤ 1) : stripBoxEnergy F p' r ≤ stripBoxEnergy F p r := by
  have h := integral_shellIntegrand_eq hF hFL hp hpp' hp'r hr1
  have h0 : 0 ≤ ∫ x in p..r, ∫ y in p..r, shellIntegrand F p' x y :=
    intervalIntegral.integral_nonneg (hpp'.trans hp'r) fun x hx =>
      intervalIntegral.integral_nonneg (hpp'.trans hp'r) fun y hy =>
        shellIntegrand_nonneg F p' (hp.trans_le hx.1) (hp.trans_le hy.1)
  linarith

/-- The four reflected copies of a bounded box integrand have the same integral over the strip. -/
theorem integral_quadruple_eq {f : ℝ → ℝ → ℝ} {p r L C : ℝ} (hpr : p ≤ r) (hL : p + r = L)
    (hf : Measurable (Function.uncurry f)) (hb : ∀ x ∈ Icc p r, ∀ y ∈ Icc p r, |f x y| ≤ C) :
    (∫ x in p..r, ∫ y in p..r, (f x y + f (L - x) (L - y) + f x (L - y) + f (L - x) y)) =
      4 * ∫ x in p..r, ∫ y in p..r, f x y := by
  have hrefl : ∀ x, x ∈ Icc p r → L - x ∈ Icc p r := fun x hx =>
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  obtain ⟨hi0, ho0⟩ := intervalIntegrable_iterated hpr hf hb
  obtain ⟨hi1, ho1⟩ := intervalIntegrable_iterated hpr (measurable_uncurry_reflect_both hf L)
    fun x hx y hy => hb _ (hrefl x hx) _ (hrefl y hy)
  obtain ⟨hi2, ho2⟩ := intervalIntegrable_iterated hpr (measurable_uncurry_reflect_snd hf L)
    fun x hx y hy => hb _ hx _ (hrefl y hy)
  obtain ⟨hi3, ho3⟩ := intervalIntegrable_iterated hpr (measurable_uncurry_reflect_fst hf L)
    fun x hx y hy => hb _ (hrefl x hx) _ hy
  set T := ∫ x in p..r, ∫ y in p..r, f x y with hT
  have hT1 : (∫ x in p..r, ∫ y in p..r, f (L - x) (L - y)) = T := by
    have e : (fun x => ∫ y in p..r, f (L - x) (L - y)) = fun x => ∫ y in p..r, f (L - x) y :=
      funext fun x => integral_strip_reflect hL (f (L - x))
    rw [e]
    exact integral_strip_reflect hL (fun x => ∫ y in p..r, f x y)
  have hT2 : (∫ x in p..r, ∫ y in p..r, f x (L - y)) = T := by
    have e : (fun x => ∫ y in p..r, f x (L - y)) = fun x => ∫ y in p..r, f x y :=
      funext fun x => integral_strip_reflect hL (f x)
    rw [e]
  have hT3 : (∫ x in p..r, ∫ y in p..r, f (L - x) y) = T :=
    integral_strip_reflect hL (fun x => ∫ y in p..r, f x y)
  have hin : ∀ x ∈ uIcc p r,
      (∫ y in p..r, (f x y + f (L - x) (L - y) + f x (L - y) + f (L - x) y)) =
        (∫ y in p..r, f x y) + (∫ y in p..r, f (L - x) (L - y)) + (∫ y in p..r, f x (L - y)) +
          ∫ y in p..r, f (L - x) y := fun x hx => by
    rw [uIcc_of_le hpr] at hx
    rw [intervalIntegral.integral_add (((hi0 x hx).add (hi1 x hx)).add (hi2 x hx)) (hi3 x hx),
      intervalIntegral.integral_add ((hi0 x hx).add (hi1 x hx)) (hi2 x hx),
      intervalIntegral.integral_add (hi0 x hx) (hi1 x hx)]
  rw [intervalIntegral.integral_congr hin,
    intervalIntegral.integral_add ((ho0.add ho1).add ho2) ho3,
    intervalIntegral.integral_add (ho0.add ho1) ho2, intervalIntegral.integral_add ho0 ho1,
    hT1, hT2, hT3]
  ring

/-! ### The quadruple off the corner -/

/-- **The shell quadruple inequality.** With `c = p' − L/2 > 0`, the four shell terms of
`x, L − x, y, L − y` dominate `α(x)² W̃(u, v) + α(y)² W̃(v, u)`: off the corner `u, v > c` no pair
meets the inner box and the sharp quadruple bound applies; on the corner both sides are compared
with `0`. -/
theorem shellQuadruple_ge {p r L β p' x y : ℝ} (hp : 0 < p) (hL : p + r = L) (hr3 : r - p ≤ 2 * p)
    (hβ : 0 < β) (hx : x ∈ Icc p r) (hy : y ∈ Icc p r) (F : ℝ → ℝ) :
    reflectedOddPart F L x ^ 2 * shellFoldWeight p β (p' - L / 2) |x - L / 2| |y - L / 2| +
        reflectedOddPart F L y ^ 2 * shellFoldWeight p β (p' - L / 2) |y - L / 2| |x - L / 2| ≤
      shellIntegrand F p' x y + shellIntegrand F p' (L - x) (L - y) +
        shellIntegrand F p' x (L - y) + shellIntegrand F p' (L - x) y := by
  have hxL : L - x ∈ Icc p r := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hyL : L - y ∈ Icc p r := ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hx0 : 0 < x := hp.trans_le hx.1
  have hy0 : 0 < y := hp.trans_le hy.1
  have hxL0 : 0 < L - x := hp.trans_le hxL.1
  have hyL0 : 0 < L - y := hp.trans_le hyL.1
  by_cases hcorner : p' - L / 2 < |x - L / 2| ∧ p' - L / 2 < |y - L / 2|
  · have h1 : shellFoldWeight p β (p' - L / 2) |x - L / 2| |y - L / 2| = 0 := by
      unfold shellFoldWeight; rw [if_pos hcorner]
    have h2 : shellFoldWeight p β (p' - L / 2) |y - L / 2| |x - L / 2| = 0 := by
      unfold shellFoldWeight; rw [if_pos ⟨hcorner.2, hcorner.1⟩]
    rw [h1, h2, mul_zero, mul_zero, add_zero]
    linarith [shellIntegrand_nonneg F p' hx0 hy0, shellIntegrand_nonneg F p' hxL0 hyL0,
      shellIntegrand_nonneg F p' hx0 hyL0, shellIntegrand_nonneg F p' hxL0 hy0]
  · have hW1 : shellFoldWeight p β (p' - L / 2) |x - L / 2| |y - L / 2| =
        sharpFoldWeight p β |x - L / 2| |y - L / 2| := by
      unfold shellFoldWeight; rw [if_neg hcorner]
    have hW2 : shellFoldWeight p β (p' - L / 2) |y - L / 2| |x - L / 2| =
        sharpFoldWeight p β |y - L / 2| |x - L / 2| := by
      unfold shellFoldWeight; rw [if_neg fun h => hcorner ⟨h.2, h.1⟩]
    -- a point of the pair above `p'` is `m + u` with `u > c`
    have hside : ∀ z a, (a = z ∨ a = L - z) → p' < a → p' - L / 2 < |z - L / 2| := by
      intro z a ha h
      rw [lt_abs]
      rcases ha with ha | ha
      · left; rw [ha] at h; linarith
      · right; rw [ha] at h; linarith
    have key : ∀ a b, (a = x ∨ a = L - x) → (b = y ∨ b = L - y) →
        shellIntegrand F p' a b = stripIntegrand F a b := by
      intro a b ha hb
      unfold shellIntegrand
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hcorner ⟨hside x a ha h1, hside y b hb h2⟩
    rw [hW1, hW2, key x y (Or.inl rfl) (Or.inl rfl), key (L - x) (L - y) (Or.inr rfl) (Or.inr rfl),
      key x (L - y) (Or.inl rfl) (Or.inr rfl), key (L - x) y (Or.inr rfl) (Or.inl rfl)]
    unfold stripIntegrand
    exact sharpQuadruple_ge hp hL hr3 hβ hx hy F

/-! ### The weight of the corner -/

/-- **The corner weight.** On `c < u, v ≤ η` the sharp folded weight is at most `(2 + η/2)/c + 1`:
the transformed surplus `k(u, v)(u − v)/(β + u)` is at most `(½ + η/4)/c`, and `4k₀(u + v) ≤ 4ω(u + v)
≤ 1/c + 1`. -/
theorem sharpFoldWeight_le_corner {p β c η u v : ℝ} (hp : 0 < p) (hβ : 0 < β) (hc : 0 < c)
    (hcu : c < u) (huη : u ≤ η) (hcv : c < v) :
    sharpFoldWeight p β u v ≤ (2 + η / 2) / c + 1 := by
  unfold sharpFoldWeight microFoldKernel
  have hu0 : 0 < u := hc.trans hcu
  have hv0 : 0 < v := hc.trans hcv
  have hβu : 0 < β + u := by linarith
  have h1 : surplusKernel u v * (1 - (β + v) / (β + u)) ≤ (1 / 2 + η / 4) / c := by
    have hq : 1 - (β + v) / (β + u) = (u - v) / (β + u) := by field_simp; ring
    have hR : 0 ≤ (1 / 2 + η / 4) / c := by
      have : 0 ≤ η := hu0.le.trans huη
      positivity
    rw [hq]
    rcases lt_trichotomy v u with hvu | hvu | hvu
    · have hd : 0 < u - v := by linarith
      have hk := (surplusKernel_le hu0 hv0).trans
        (archLevyDensity_le_inv (abs_pos.mpr (sub_ne_zero.mpr hvu.ne')))
      rw [abs_of_pos hd] at hk
      have hk0 := surplusKernel_nonneg hu0 hv0 hvu.ne'
      have e1 : surplusKernel u v * (u - v) ≤ 1 / 2 + η / 4 := by
        have h := mul_le_mul_of_nonneg_right hk hd.le
        have e : (1 / (2 * (u - v)) + 1 / 4) * (u - v) = 1 / 2 + (u - v) / 4 := by
          field_simp
        rw [e] at h
        linarith
      rw [mul_div_assoc', div_le_div_iff₀ hβu hc]
      nlinarith [mul_nonneg hk0 hd.le, mul_le_mul_of_nonneg_right e1 hc.le]
    · rw [hvu, sub_self, zero_div, mul_zero]; exact hR
    · have hk0 := surplusKernel_nonneg hu0 hv0 hvu.ne
      have : (u - v) / (β + u) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hβu.le
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hk0 this]
  have h2 : archLevyDensity (u + v) - archLevyDensity (2 * p) ≤ 1 / (4 * c) + 1 / 4 := by
    have hω := archLevyDensity_le_inv (show 0 < u + v by linarith)
    have hp0 := archLevyDensity_pos (show 0 < 2 * p by linarith)
    have hinv : 1 / (2 * (u + v)) ≤ 1 / (4 * c) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have e : (2 + η / 2) / c + 1 = 2 * ((1 / 2 + η / 4) / c) + 4 * (1 / (4 * c) + 1 / 4) := by
    field_simp; ring
  rw [e]
  linarith

/-- `∫_a^b (if c < y then φ y else 0) dy = ∫_c^b φ` for `a ≤ c ≤ b`. -/
theorem integral_ite_lt {φ : ℝ → ℝ} {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    (∫ y in a..b, if c < y then φ y else 0) = ∫ y in c..b, φ y := by
  have e : (fun y => if c < y then φ y else 0) = (Ioi c).indicator φ := by
    funext y; simp only [Set.indicator_apply, mem_Ioi]
  have hs : Ioc a b ∩ Ioi c = Ioc c b := by
    ext y
    simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
    constructor
    · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, h1⟩
  rw [e, intervalIntegral.integral_of_le (hac.trans hcb), intervalIntegral.integral_of_le hcb,
    setIntegral_indicator measurableSet_Ioi, hs]

/-- **The integrated shell weight.** For `0 < u ≤ η ≤ 1/12` and `0 < c ≤ η`:
`∫_{m−η}^{m+η} W̃(u, |y − m|) dy ≥ 2(λ₀ − (η − c)((2 + η/2)/c + 1))`, `λ₀ = 1.9 − η/p − 3η²`. -/
theorem integral_shellFoldWeight_ge {p η c u m : ℝ} (hp : 0 < p) (hη : 0 < η) (hη1 : η ≤ 1 / 12)
    (hc : 0 < c) (hcη : c ≤ η) (hu : 0 < u) (huη : u ≤ η) :
    2 * (19 / 10 - η / p - 3 * η ^ 2 - (η - c) * ((2 + η / 2) / c + 1)) ≤
      ∫ y in (m - η)..(m + η), shellFoldWeight p (η / 10) c u |y - m| := by
  have hB : 0 ≤ (η - c) * ((2 + η / 2) / c + 1) := by
    have : 0 ≤ η - c := by linarith
    positivity
  have hpot := sharpFold_potential_ge hp hη hη1 hu huη
  have hI := integral_sharpFoldWeight (p := p) (m := m) hη hu huη (by linarith)
  by_cases hcu : c < u
  · have hβ : 0 < η / 10 := by positivity
    set B := (2 + η / 2) / c + 1 with hBdef
    set W := sharpFoldWeight p (η / 10) u with hW
    have hwm : Measurable W := (measurable_sharpFoldWeight p (η / 10)).of_uncurry_left
    set M := 3 / (η / 10) + 4 * (archLevyDensity u + |archLevyDensity (2 * p)|) with hM
    have hwb : ∀ v ∈ Icc 0 η, |W v| ≤ M := fun v hv => by
      have := abs_sharpFoldWeight_le (p := p) hβ hu hv.1
        (by rw [abs_le]; constructor <;> linarith [hv.1, hv.2])
      have hmono : archLevyDensity (u + v) ≤ archLevyDensity u :=
        strictAntiOn_archLevyDensity.antitoneOn hu (show 0 < u + v by linarith [hv.1])
          (by linarith [hv.1])
      rw [hW, hM]; linarith
    have hwm' : Measurable fun v => if c < v then W v else 0 :=
      Measurable.ite (measurableSet_lt measurable_const measurable_id) hwm measurable_const
    have hwb' : ∀ v ∈ Icc 0 η, |if c < v then W v else 0| ≤ M := fun v hv => by
      split_ifs
      · exact hwb v hv
      · rw [abs_zero]; exact (abs_nonneg _).trans (hwb v hv)
    -- the shell weight is the full weight minus its corner
    have hsplit : (fun y => shellFoldWeight p (η / 10) c u |y - m|) =
        fun y => W |y - m| - (if c < |y - m| then W |y - m| else 0) := by
      funext y; unfold shellFoldWeight; rw [hW]
      by_cases hv : c < |y - m| <;> simp [hcu, hv]
    have hyb : ∀ y ∈ Icc (m - η) (m + η), |y - m| ∈ Icc 0 η := fun y hy =>
      ⟨abs_nonneg _, by rw [abs_le]; constructor <;> linarith [hy.1, hy.2]⟩
    have hiW : IntervalIntegrable (fun y => W |y - m|) volume (m - η) (m + η) :=
      intervalIntegrable_of_abs_le (by linarith) (hwm.comp (measurable_id.sub_const m).abs)
        fun y hy => hwb _ (hyb y hy)
    have hiC : IntervalIntegrable (fun y => if c < |y - m| then W |y - m| else 0) volume
        (m - η) (m + η) :=
      intervalIntegrable_of_abs_le (by linarith) (hwm'.comp (measurable_id.sub_const m).abs)
        fun y hy => hwb' _ (hyb y hy)
    rw [hsplit, intervalIntegral.integral_sub hiW hiC, hI,
      integral_abs_sub_symm (w := fun v => if c < v then W v else 0) hη.le hwm' hwb']
    -- the corner integral is at most `(η − c) B`
    have hcorner : (∫ v in (0 : ℝ)..η, if c < v then W v else 0) ≤ (η - c) * B := by
      have hiC' : IntervalIntegrable (fun v => if c < v then W v else 0) volume 0 η :=
        intervalIntegrable_of_abs_le hη.le hwm' hwb'
      have hiB : IntervalIntegrable (fun v => if c < v then B else (0 : ℝ)) volume 0 η :=
        intervalIntegrable_of_abs_le (C := |B|) hη.le
          (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
            measurable_const)
          fun v _ => by split_ifs <;> simp
      have hmono := intervalIntegral.integral_mono_on hη.le hiC' hiB fun v hv => by
        by_cases hv' : c < v
        · simp only [if_pos hv', hW]
          exact sharpFoldWeight_le_corner hp hβ hc hcu huη hv'
        · simp only [if_neg hv', le_refl]
      rw [integral_ite_lt (φ := fun _ => B) hc.le hcη, intervalIntegral.integral_const,
        smul_eq_mul] at hmono
      exact hmono
    linarith
  · have e : (fun y => shellFoldWeight p (η / 10) c u |y - m|) =
        fun y => sharpFoldWeight p (η / 10) u |y - m| := by
      funext y; unfold shellFoldWeight; rw [if_neg fun h => hcu h.1]
    rw [e, hI]
    linarith

/-! ### The shell micro-fold -/

section Shell

variable {F : ℝ → ℝ} {K p p' r L : ℝ} (hF : Continuous F) (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|)
  (hp : 0 < p) (hpr : p < r) (hL : p + r = L) (hr3 : r - p ≤ 2 * p) (hr6 : r - p ≤ 1 / 6)
  (hc : L / 2 < p') (hp'r : p' ≤ r)

include hF hFL hp hpr hL hr3 hr6 hc hp'r in
/-- **The shell micro-fold.** With `η = (r − p)/2`, `p + r = L` and an inner strip `[p', r]` right of
the centre, `c = p' − L/2 > 0`:
`T(p, r) − T(p', r) ≥ (1.9 − η/p − 3η² − (r − p')((2 + η/2)/c + 1)) ∫_p^r α²`. -/
theorem sharpMicroFold_shell_ge :
    (19 / 10 - (r - p) / 2 / p - 3 * ((r - p) / 2) ^ 2 -
        (r - p') * ((2 + (r - p) / 2 / 2) / (p' - L / 2) + 1)) *
        (∫ x in p..r, reflectedOddPart F L x ^ 2) ≤
      stripBoxEnergy F p r - stripBoxEnergy F p' r := by
  have hr1 : r - p ≤ 1 := by linarith
  set C : ℝ := 3 / 2 * K ^ 2 * (r - p) with hC
  have hpp' : p ≤ p' := by linarith
  have hshell := integral_shellIntegrand_eq hF hFL hp hpp' hp'r hr1
  have hbs : ∀ x ∈ Icc p r, ∀ y ∈ Icc p r, |shellIntegrand F p' x y| ≤ C := fun x hx y hy =>
    (abs_shellIntegrand_le F p' x y).trans (abs_strip_integrand_le hFL hp hr1 hx hy)
  have hms := measurable_shellIntegrand hF p'
  have hrefl : ∀ x, x ∈ Icc p r → L - x ∈ Icc p r := fun x hx =>
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  -- the four reflected shell copies
  have hsum := integral_quadruple_eq hpr.le hL hms hbs
  have hmq : Measurable (Function.uncurry fun x y => shellIntegrand F p' x y +
      shellIntegrand F p' (L - x) (L - y) + shellIntegrand F p' x (L - y) +
        shellIntegrand F p' (L - x) y) :=
    ((hms.add (measurable_uncurry_reflect_both hms L)).add
      (measurable_uncurry_reflect_snd hms L)).add (measurable_uncurry_reflect_fst hms L)
  obtain ⟨his, hos⟩ := intervalIntegrable_iterated (C := 4 * C) hpr.le hmq fun x hx y hy => by
    have h0 := hbs x hx y hy
    have h1 := hbs _ (hrefl x hx) _ (hrefl y hy)
    have h2 := hbs _ hx _ (hrefl y hy)
    have h3 := hbs _ (hrefl x hx) _ hy
    calc |shellIntegrand F p' x y + shellIntegrand F p' (L - x) (L - y) +
          shellIntegrand F p' x (L - y) + shellIntegrand F p' (L - x) y|
        ≤ |shellIntegrand F p' x y| + |shellIntegrand F p' (L - x) (L - y)| +
          |shellIntegrand F p' x (L - y)| + |shellIntegrand F p' (L - x) y| := by
          have := abs_add_le (shellIntegrand F p' x y + shellIntegrand F p' (L - x) (L - y) +
            shellIntegrand F p' x (L - y)) (shellIntegrand F p' (L - x) y)
          have := abs_add_le (shellIntegrand F p' x y + shellIntegrand F p' (L - x) (L - y))
            (shellIntegrand F p' x (L - y))
          have := abs_add_le (shellIntegrand F p' x y) (shellIntegrand F p' (L - x) (L - y))
          linarith
      _ ≤ 4 * C := by linarith
  -- the folded shell weight
  set η := (r - p) / 2 with hη
  set c := p' - L / 2 with hcdef
  have hη0 : 0 < η := by rw [hη]; linarith
  have hη12 : η ≤ 1 / 12 := by rw [hη]; linarith
  have hc0 : 0 < c := by rw [hcdef]; linarith
  have hcη : c ≤ η := by rw [hcdef, hη]; linarith
  have hηc : η - c = r - p' := by rw [hcdef, hη]; linarith
  have hmp : L / 2 - η = p := by rw [hη]; linarith
  have hmr : L / 2 + η = r := by rw [hη]; linarith
  have hβ : 0 < η / 10 := by positivity
  have hαc : Continuous fun x => reflectedOddPart F L x ^ 2 := by
    unfold reflectedOddPart; fun_prop
  set Cb := 30 * K ^ 2 * η + K ^ 2 * (2 * η + η ^ 2) + 4 * K ^ 2 * η ^ 2 * |archLevyDensity (2 * p)|
    with hCb
  have hΦm : Measurable (Function.uncurry fun x y =>
      reflectedOddPart F L x ^ 2 * shellFoldWeight p (η / 10) c |x - L / 2| |y - L / 2|) :=
    ((hαc.measurable.comp measurable_fst).mul
      (measurable_uncurry_abs_sub (measurable_shellFoldWeight p (η / 10) c) (L / 2)))
  have hΦb : ∀ x ∈ Icc p r, ∀ y ∈ Icc p r,
      abs (reflectedOddPart F L x ^ 2 * shellFoldWeight p (η / 10) c |x - L / 2| |y - L / 2|) ≤
        Cb := fun x hx y hy => by
    have h := abs_foldedWeight_le (p := p) hFL hη0 hη12
      (show |x - L / 2| ≤ η by rw [abs_le]; constructor <;> linarith [hx.1, hx.2])
      (show |y - L / 2| ≤ η by rw [abs_le]; constructor <;> linarith [hy.1, hy.2])
    have hCb0 : 0 ≤ Cb := by rw [hCb]; positivity
    unfold shellFoldWeight
    split_ifs
    · rw [mul_zero, abs_zero]; exact hCb0
    · exact h
  obtain ⟨hiΦ, hoΦ⟩ := intervalIntegrable_iterated hpr.le hΦm hΦb
  have hΦm' : Measurable (Function.uncurry fun x y =>
      reflectedOddPart F L y ^ 2 * shellFoldWeight p (η / 10) c |y - L / 2| |x - L / 2|) :=
    hΦm.comp measurable_swap
  obtain ⟨hiΦ', hoΦ'⟩ := intervalIntegrable_iterated hpr.le hΦm' fun x hx y hy => hΦb y hy x hx
  -- the pointwise inequality, integrated
  have hinner1 : ∀ x ∈ Icc p r,
      (∫ y in p..r, reflectedOddPart F L x ^ 2 *
          shellFoldWeight p (η / 10) c |x - L / 2| |y - L / 2|) +
        (∫ y in p..r, reflectedOddPart F L y ^ 2 *
          shellFoldWeight p (η / 10) c |y - L / 2| |x - L / 2|) ≤
      ∫ y in p..r, (shellIntegrand F p' x y + shellIntegrand F p' (L - x) (L - y) +
        shellIntegrand F p' x (L - y) + shellIntegrand F p' (L - x) y) := fun x hx => by
    rw [← intervalIntegral.integral_add (hiΦ x hx) (hiΦ' x hx)]
    exact intervalIntegral.integral_mono_on hpr.le ((hiΦ x hx).add (hiΦ' x hx)) (his x hx)
      fun y hy => shellQuadruple_ge hp hL hr3 hβ hx hy F
  have hint1 :
      (∫ x in p..r, ∫ y in p..r,
          reflectedOddPart F L x ^ 2 * shellFoldWeight p (η / 10) c |x - L / 2| |y - L / 2|) +
        (∫ x in p..r, ∫ y in p..r,
          reflectedOddPart F L y ^ 2 * shellFoldWeight p (η / 10) c |y - L / 2| |x - L / 2|) ≤
        4 * (stripBoxEnergy F p r - stripBoxEnergy F p' r) := by
    rw [← intervalIntegral.integral_add hoΦ hoΦ', ← hshell, ← hsum]
    exact intervalIntegral.integral_mono_on hpr.le (hoΦ.add hoΦ') hos fun x hx => hinner1 x hx
  have hswap := integral_integral_swap_box hpr.le hΦm hΦb
  -- the inner integral is at least twice the shell constant
  set lamS := 19 / 10 - η / p - 3 * η ^ 2 - (η - c) * ((2 + η / 2) / c + 1) with hlamS
  have hinner : ∀ x ∈ Icc p r, 2 * lamS * reflectedOddPart F L x ^ 2 ≤
      ∫ y in p..r, reflectedOddPart F L x ^ 2 *
        shellFoldWeight p (η / 10) c |x - L / 2| |y - L / 2| := by
    intro x hx
    have hu : |x - L / 2| ≤ η := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
    rcases eq_or_lt_of_le (abs_nonneg (x - L / 2)) with h0 | h0
    · have hα := abs_reflectedOddPart_le (L := L) hFL x
      have : reflectedOddPart F L x = 0 := by
        rw [← h0, mul_zero] at hα; exact abs_nonpos_iff.mp hα
      rw [this]; simp
    have hI := integral_shellFoldWeight_ge (m := L / 2) hp hη0 hη12 hc0 hcη h0 hu
    rw [hmp, hmr] at hI
    rw [intervalIntegral.integral_const_mul, mul_comm (2 * lamS)]
    exact mul_le_mul_of_nonneg_left hI (sq_nonneg _)
  have hmono := intervalIntegral.integral_mono_on hpr.le ((hαc.intervalIntegrable p r).const_mul
    (2 * lamS)) hoΦ fun x hx => hinner x hx
  rw [intervalIntegral.integral_const_mul] at hmono
  rw [hswap] at hint1
  have e : (19 / 10 - (r - p) / 2 / p - 3 * ((r - p) / 2) ^ 2 -
      (r - p') * ((2 + (r - p) / 2 / 2) / (p' - L / 2) + 1)) = lamS := by
    rw [hlamS, hηc]
  rw [e]
  linarith

end Shell

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
