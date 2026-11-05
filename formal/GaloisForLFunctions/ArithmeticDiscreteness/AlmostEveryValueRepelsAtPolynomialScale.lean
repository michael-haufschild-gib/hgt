import GaloisForLFunctions.ArithmeticDiscreteness.NearCoincidencesAreJointSmallValues
import GaloisForLFunctions.RHTower.ZetaVerticalStripPolynomialBound

/-!
# Almost every value repels at polynomial scale

Let `F` be holomorphic near a vertical strip with polynomial growth `|F| ≤ A (2 + |t|)^B`. Then for
Lebesgue-almost every `a ∈ ℂ` the `a`-points of `F` in the strip collide or repel at polynomial
scale: distinct `a`-points `s ≠ s'` with `|Im s| ≥ 3` satisfy `|s' − s| ≥ κ (2 + |Im s|)^{−(2B+1)}`
(`ae_collide_or_repel`). For `ζ` on the critical strip this holds with one exponent for almost
every `a` (`ae_riemannZeta_values_collide_or_repel`): B54 is a statement about the single value
`a = 0`, not about the arithmetic of `ζ`.

Mechanism. Two `a`-points at distance `d ∈ (2^{−k−1}, 2^{−k}]` make `F − a` and `F'` small at the
midpoint `c` (`|F(c) − a| ≲ M d²`, `|F'(c)| ≲ M d`), so `a` lies within `K/4^k` of `F(q)` for the
point `q` of the mesh-`2^{−k}` grid nearest to `c` (`mem_badValues`). The heights are capped at
`2^{⌊k/(2B+1)⌋}`; the `≲ 2^{k/(2B+1)} 4^k` grid discs of area `≲ K²/16^k` have total area
`≲ 2^{−k}` (`volume_badValues_le`), and Borel–Cantelli leaves almost every `a` in finitely many.
-/

open Complex Metric Set MeasureTheory Filter

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

/-- The height cap `2^{⌊k/D⌋}` at scale `2^{−k}`. -/
def heightCap (D k : ℕ) : ℕ := 2 ^ (k / D)

/-- The grid of mesh `2^{−k}` with corner `(α − 1) − i · 2^{⌊k/D⌋}`. -/
def gridPt (α : ℝ) (D k : ℕ) (p : ℕ × ℕ) : ℂ :=
  ((α - 1 + p.1 / 2 ^ k : ℝ) : ℂ) + ((-(heightCap D k : ℝ) + p.2 / 2 ^ k : ℝ) : ℂ) * I

/-- The grid indices covering `[α − 1, β + 1] × [−2^{⌊k/D⌋}, 2^{⌊k/D⌋}]`. -/
def gridIdx (α β : ℝ) (D k : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range (⌈2 ^ k * (β - α + 2)⌉₊ + 1) ×ˢ Finset.range (2 * heightCap D k * 2 ^ k + 1)

/-- The values `a` within `K_k/4^k` of `F` at a grid point, `K_k = 2000 A (2 + 2^{⌊k/D⌋})^B`. -/
def badValues (F : ℂ → ℂ) (α β A : ℝ) (B D k : ℕ) : Set ℂ :=
  ⋃ p ∈ gridIdx α β D k,
    closedBall (F (gridPt α D k p)) (2000 * A * (2 + (heightCap D k : ℝ)) ^ B / 4 ^ k)

theorem volume_closedBall_eq (w : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall w r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
  rw [Complex.volume_closedBall, ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_coe_nnreal,
    NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity), mul_comm]

/-- Every point of the box is within `2 · 2^{−k}` of a grid point. -/
theorem exists_gridPt_near {α β : ℝ} (D k : ℕ) {c : ℂ} (hre0 : α - 1 ≤ c.re) (hre1 : c.re ≤ β + 1)
    (him : |c.im| ≤ heightCap D k) :
    ∃ p ∈ gridIdx α β D k, ‖c - gridPt α D k p‖ ≤ 2 / 2 ^ k := by
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  set Y : ℝ := ((heightCap D k : ℕ) : ℝ) with hY
  obtain ⟨hi0, hi1⟩ := abs_le.mp him
  set x : ℝ := 2 ^ k * (c.re - α + 1) with hx
  set y : ℝ := 2 ^ k * (c.im + Y) with hy
  have hx0 : 0 ≤ x := by rw [hx]; nlinarith
  have hy0 : 0 ≤ y := by rw [hy]; nlinarith
  refine ⟨(⌊x⌋₊, ⌊y⌋₊), Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩,
    ?_⟩
  · have h1 : x ≤ 2 ^ k * (β - α + 2) := by rw [hx]; nlinarith
    have h2 : (⌊x⌋₊ : ℝ) ≤ ⌈2 ^ k * (β - α + 2)⌉₊ :=
      ((Nat.floor_le hx0).trans h1).trans (Nat.le_ceil _)
    have : ⌊x⌋₊ ≤ ⌈2 ^ k * (β - α + 2)⌉₊ := by exact_mod_cast h2
    omega
  · have h1 : y ≤ 2 * Y * 2 ^ k := by rw [hy]; nlinarith
    have h2 : (⌊y⌋₊ : ℝ) ≤ ((2 * heightCap D k * 2 ^ k : ℕ) : ℝ) := by
      push_cast; rw [← hY]; exact (Nat.floor_le hy0).trans h1
    have : ⌊y⌋₊ ≤ 2 * heightCap D k * 2 ^ k := by exact_mod_cast h2
    omega
  · have hre : (c - gridPt α D k (⌊x⌋₊, ⌊y⌋₊)).re = (x - ⌊x⌋₊) / 2 ^ k := by
      simp only [gridPt, sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
        mul_one, sub_zero]
      rw [hx]; field_simp; ring
    have him' : (c - gridPt α D k (⌊x⌋₊, ⌊y⌋₊)).im = (y - ⌊y⌋₊) / 2 ^ k := by
      simp only [gridPt, sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero,
        mul_one, zero_add]
      rw [hy, ← hY]; field_simp; ring
    have ex0 := Nat.floor_le hx0
    have ex1 := Nat.lt_floor_add_one x
    have ey0 := Nat.floor_le hy0
    have ey1 := Nat.lt_floor_add_one y
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [hre, him', abs_div, abs_div, abs_of_pos hk, abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith), ← add_div, div_le_div_iff_of_pos_right hk]
    linarith

/-- **Two close `a`-points put `a` in the bad set of their scale.** -/
theorem mem_badValues {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    {α β A : ℝ} {B : ℕ} (D k : ℕ)
    (hM : ∀ c : ℂ, α - 1 ≤ c.re → c.re ≤ β + 1 → 2 ≤ |c.im| →
      closedBall c (1 / 2) ⊆ U ∧ ∀ z ∈ closedBall c (1 / 2), ‖F z‖ ≤ A * (2 + |c.im|) ^ B)
    {a s s' : ℂ} (hs : F s = a) (hs' : F s' = a) (hne : s ≠ s')
    (hd0 : 1 / 2 ^ (k + 1) < ‖s' - s‖) (hd1 : ‖s' - s‖ ≤ 1 / 2 ^ k) (hd : ‖s' - s‖ ≤ 1 / 64)
    (hre0 : α - 1 ≤ ((s + s') / 2).re) (hre1 : ((s + s') / 2).re ≤ β + 1)
    (him0 : 2 ≤ |((s + s') / 2).im|) (him1 : |((s + s') / 2).im| ≤ heightCap D k) :
    a ∈ badValues F α β A B D k := by
  set c : ℂ := (s + s') / 2 with hc
  set h : ℂ := (s' - s) / 2 with hh
  set M : ℝ := A * (2 + |c.im|) ^ B with hMdef
  obtain ⟨hsub, hbd⟩ := hM c hre0 hre1 him0
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  have hcm : c - h = s := by rw [hc, hh]; ring
  have hcp : c + h = s' := by rw [hc, hh]; ring
  have hh0 : h ≠ 0 := by rw [hh]; exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hne)) two_ne_zero
  have hhn : ‖h‖ = ‖s' - s‖ / 2 := by rw [hh, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
  -- `f = F − a` is bounded by `2M` on the disc (`a = F(s)` with `s` in it)
  set f : ℂ → ℂ := fun z => F z - a with hf
  have hfd : DifferentiableOn ℂ f U := hF.sub_const a
  have hsmem : s ∈ closedBall c (1 / 2) := by
    rw [mem_closedBall, dist_eq_norm, ← hcm, sub_sub_cancel_left, norm_neg]; linarith
  have hfM : ∀ z ∈ closedBall c (2 * (1 / 4)), ‖f z‖ ≤ 2 * M := by
    intro z hz
    rw [show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num] at hz
    have h1 := hbd z hz
    have h2 := hbd s hsmem
    rw [hs] at h2
    calc ‖f z‖ ≤ ‖F z‖ + ‖a‖ := norm_sub_le _ _
      _ ≤ 2 * M := by linarith
  have hsub' : closedBall c (2 * (1 / 4)) ⊆ U := by
    rw [show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num]; exact hsub
  have h1 : f (c - h) = 0 := by rw [hcm, hf]; simp [hs]
  have h2 : f (c + h) = 0 := by rw [hcp, hf]; simp [hs']
  have hh8 : ‖h‖ ≤ (1 / 4) / 8 := by rw [hhn]; linarith
  have hv := norm_le_of_two_symmetric_zeros hU hfd (by norm_num : (0 : ℝ) < 1 / 4) hsub' hfM hh8
    h1 h2
  have hdv := norm_deriv_le_of_two_symmetric_zeros hU hfd (by norm_num : (0 : ℝ) < 1 / 4) hsub'
    hfM hh8 hh0 h1 h2
  -- the nearest grid point
  obtain ⟨p, hp, hq⟩ := exists_gridPt_near (β := β) D k hre0 hre1 (by exact_mod_cast him1)
  set q := gridPt α D k p with hqdef
  have h2k : (64 : ℝ) < 2 ^ (k + 1) := by
    have := hd0.trans_le hd
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)] at this; linarith
  have hk32 : 32 < (2 : ℝ) ^ k := by rw [pow_succ] at h2k; linarith
  have hqc : ‖q - c‖ ≤ 1 / 4 / 4 := by
    rw [norm_sub_rev]
    refine hq.trans ?_
    rw [div_le_iff₀ hk]; linarith
  have hball : closedBall c (1 / 4) ⊆ U := (closedBall_subset_closedBall (by norm_num)).trans hsub
  have hfM' : ∀ z ∈ closedBall c (1 / 4), ‖f z‖ ≤ 2 * M := fun z hz =>
    hfM z ((closedBall_subset_closedBall (by norm_num)) hz)
  have ht := norm_sub_taylor_le hU hfd (by norm_num : (0 : ℝ) < 1 / 4) hball hfM' hqc
  -- `|F(q) − a| ≤ 1984 M / 4^k`
  have hM0 : 0 ≤ M := by
    have := hbd s hsmem; exact (norm_nonneg _).trans this
  have hnh : ‖h‖ ≤ 1 / 2 / 2 ^ k := by rw [hhn]; rw [div_div, mul_comm, ← div_div]; linarith
  have hnq : ‖q - c‖ ≤ 2 / 2 ^ k := by rw [norm_sub_rev]; exact hq
  have hfq : ‖f q‖ ≤ 1984 * M / 4 ^ k := by
    have e : f q = (f q - f c - deriv f c * (q - c)) + f c + deriv f c * (q - c) := by ring
    have hnh0 : 0 ≤ ‖h‖ := norm_nonneg _
    have hnq0 : 0 ≤ ‖q - c‖ := norm_nonneg _
    have h4 : (4 : ℝ) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
    have hv' : ‖f c‖ ≤ 2 * M * 384 * ‖h‖ ^ 2 := by
      have : 24 * (2 * M) / (1 / 4) ^ 2 = 2 * M * 384 := by ring
      rw [this] at hv; exact hv
    have hdv' : ‖deriv f c‖ ≤ 2 * M * 384 * ‖h‖ := by
      have : 24 * (2 * M) / (1 / 4) ^ 2 = 2 * M * 384 := by ring
      rw [this] at hdv; exact hdv
    have ht' : ‖f q - f c - deriv f c * (q - c)‖ ≤ 2 * M * 128 * ‖q - c‖ ^ 2 := by
      have : 8 * (2 * M) / (1 / 4) ^ 2 = 2 * M * 128 := by ring
      rw [this] at ht; exact ht
    have hsq1 : ‖h‖ ^ 2 ≤ (1 / 2 / 2 ^ k) ^ 2 := pow_le_pow_left₀ hnh0 hnh 2
    have hsq2 : ‖q - c‖ ^ 2 ≤ (2 / 2 ^ k) ^ 2 := pow_le_pow_left₀ hnq0 hnq 2
    have hmul : ‖h‖ * ‖q - c‖ ≤ (1 / 2 / 2 ^ k) * (2 / 2 ^ k) :=
      mul_le_mul hnh hnq hnq0 (by positivity)
    calc ‖f q‖ ≤ ‖f q - f c - deriv f c * (q - c)‖ + ‖f c‖ + ‖deriv f c‖ * ‖q - c‖ := by
          have t1 := norm_add_le (f q - f c - deriv f c * (q - c) + f c) (deriv f c * (q - c))
          have t2 := norm_add_le (f q - f c - deriv f c * (q - c)) (f c)
          rw [norm_mul] at t1
          conv_lhs => rw [e]
          linarith
      _ ≤ 2 * M * 128 * ‖q - c‖ ^ 2 + 2 * M * 384 * ‖h‖ ^ 2 + 2 * M * 384 * ‖h‖ * ‖q - c‖ := by
          gcongr
      _ ≤ 2 * M * 128 * (2 / 2 ^ k) ^ 2 + 2 * M * 384 * (1 / 2 / 2 ^ k) ^ 2 +
            2 * M * 384 * ((1 / 2 / 2 ^ k) * (2 / 2 ^ k)) := by
          rw [mul_assoc (2 * M * 384) ‖h‖]
          gcongr
      _ = 1984 * M / 4 ^ k := by rw [h4]; field_simp; ring
  -- `M ≤ A (2 + 2^{⌊k/D⌋})^B`
  have hA0 : 0 ≤ A := by
    by_contra hneg
    push Not at hneg
    have : M < 0 := by rw [hMdef]; exact mul_neg_of_neg_of_pos hneg (by positivity)
    linarith
  have hMcap : M ≤ A * (2 + (heightCap D k : ℝ)) ^ B := by
    rw [hMdef]; gcongr
  refine mem_iUnion₂.mpr ⟨p, hp, ?_⟩
  rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
  have : ‖F q - a‖ = ‖f q‖ := rfl
  rw [this]
  refine hfq.trans ?_
  rw [div_le_div_iff_of_pos_right (by positivity)]
  linarith

/-- **The bad sets are summable.** With `D = 2B + 1`,
`vol(bad_k) ≤ W/2^k`, `W = 3π(β − α + 4)(2000 A 3^B)²`. -/
theorem volume_badValues_le (F : ℂ → ℂ) {α β A : ℝ} (hαβ : α ≤ β) (hA : 0 ≤ A) (B k : ℕ) :
    volume (badValues F α β A B (2 * B + 1) k) ≤
      ENNReal.ofReal (3 * Real.pi * (β - α + 4) * (2000 * A * 3 ^ B) ^ 2 / 2 ^ k) := by
  set D := 2 * B + 1 with hD
  set Y : ℝ := ((heightCap D k : ℕ) : ℝ) with hY
  set r : ℝ := 2000 * A * (2 + Y) ^ B / 4 ^ k with hr
  have hY1 : 1 ≤ Y := by rw [hY, heightCap]; push_cast; exact one_le_pow₀ (by norm_num)
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  -- cardinality of the grid
  have hcard : ((gridIdx α β D k).card : ℝ) ≤ (2 ^ k * (β - α + 4)) * (3 * Y * 2 ^ k) := by
    rw [gridIdx, Finset.card_product, Finset.card_range, Finset.card_range]
    push_cast
    have hc1 : (⌈2 ^ k * (β - α + 2)⌉₊ : ℝ) < 2 ^ k * (β - α + 2) + 1 :=
      Nat.ceil_lt_add_one (by nlinarith)
    have hk1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hA1 : (⌈2 ^ k * (β - α + 2)⌉₊ : ℝ) + 1 ≤ 2 ^ k * (β - α + 4) := by nlinarith
    have hA2 : 2 * (heightCap D k : ℝ) * 2 ^ k + 1 ≤ 3 * Y * 2 ^ k := by
      rw [← hY]; nlinarith
    exact mul_le_mul hA1 hA2 (by positivity) (by nlinarith)
  -- the height cap to the power `D` is at most `2^k`
  have hYD : Y ^ (2 * B + 1) ≤ 2 ^ k := by
    rw [hY, heightCap]; push_cast
    rw [← pow_mul]
    refine pow_le_pow_right₀ (by norm_num) ?_
    have h := Nat.div_mul_le_self k D
    rw [hD] at h ⊢
    linarith [mul_comm (k / (2 * B + 1)) (2 * B + 1)]
  have hYB : (2 + Y) ^ B ≤ 3 ^ B * Y ^ B := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) B
  calc volume (badValues F α β A B D k)
      ≤ ∑ p ∈ gridIdx α β D k, volume (closedBall (F (gridPt α D k p)) r) :=
        measure_biUnion_finset_le _ _
    _ = ∑ _p ∈ gridIdx α β D k, ENNReal.ofReal (Real.pi * r ^ 2) :=
        Finset.sum_congr rfl fun p _ => volume_closedBall_eq _ hr0
    _ = ENNReal.ofReal (∑ _p ∈ gridIdx α β D k, Real.pi * r ^ 2) :=
        (ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        have h16 : (4 : ℝ) ^ k * 4 ^ k = 2 ^ k * 2 ^ k * 2 ^ k * 2 ^ k := by
          rw [← mul_pow, ← mul_pow, ← mul_pow, ← mul_pow]; norm_num
        have hr2 : r ^ 2 ≤ (2000 * A * 3 ^ B) ^ 2 * Y ^ (2 * B) / (4 ^ k * 4 ^ k) := by
          rw [hr, div_pow, sq ((4 : ℝ) ^ k)]
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          rw [mul_pow, mul_pow (2000 * A) (3 ^ B), pow_mul, mul_assoc]
          gcongr
          calc ((2 + Y) ^ B) ^ 2 ≤ (3 ^ B * Y ^ B) ^ 2 := pow_le_pow_left₀ (by positivity) hYB 2
            _ = (3 ^ B) ^ 2 * (Y ^ B) ^ 2 := by ring
            _ = (3 ^ B) ^ 2 * (Y ^ 2) ^ B := by ring
        have hW0 : 0 ≤ (2000 * A * 3 ^ B) ^ 2 := sq_nonneg _
        calc ((gridIdx α β D k).card : ℝ) * (Real.pi * r ^ 2)
            ≤ (2 ^ k * (β - α + 4)) * (3 * Y * 2 ^ k) *
                (Real.pi * ((2000 * A * 3 ^ B) ^ 2 * Y ^ (2 * B) / (4 ^ k * 4 ^ k))) := by
              gcongr
          _ = 3 * Real.pi * (β - α + 4) * (2000 * A * 3 ^ B) ^ 2 * Y ^ (2 * B + 1) /
                (2 ^ k * 2 ^ k) := by
              rw [h16, pow_succ]; field_simp; ring
          _ ≤ 3 * Real.pi * (β - α + 4) * (2000 * A * 3 ^ B) ^ 2 * 2 ^ k / (2 ^ k * 2 ^ k) := by
              gcongr
          _ = 3 * Real.pi * (β - α + 4) * (2000 * A * 3 ^ B) ^ 2 / 2 ^ k := by
              field_simp

theorem tsum_volume_badValues_ne_top (F : ℂ → ℂ) {α β A : ℝ} (hαβ : α ≤ β) (hA : 0 ≤ A) (B : ℕ) :
    ∑' k, volume (badValues F α β A B (2 * B + 1) k) ≠ ⊤ := by
  set W : ℝ := 3 * Real.pi * (β - α + 4) * (2000 * A * 3 ^ B) ^ 2 with hW
  have hW0 : 0 ≤ W := by rw [hW]; have : 0 ≤ β - α + 4 := by linarith
                         positivity
  have hsum : Summable fun k : ℕ => W / 2 ^ k :=
    (summable_geometric_two.mul_left W).congr fun k => by rw [one_div_pow, mul_one_div]
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun k => volume_badValues_le F hαβ hA B k)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum]
  exact ENNReal.ofReal_ne_top

/-- **Almost every value collides or repels at polynomial scale.** If `F` is holomorphic on `U`,
which contains the discs of radius `1/2` around the box `[α − 1, β + 1] × {|t| ≥ 2}`, and
`|F| ≤ A (2 + |Im c|)^B` on the disc around `c`, then for almost every `a ∈ ℂ` there is `κ > 0`
with `κ / (2 + |Im s|)^{2B+1} ≤ |s' − s|` for all distinct `a`-points `s, s'` with
`α ≤ Re s ≤ β`, `|Im s| ≥ 3`. -/
theorem ae_collide_or_repel {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    {α β A : ℝ} {B : ℕ} (hαβ : α ≤ β) (hA : 0 ≤ A)
    (hM : ∀ c : ℂ, α - 1 ≤ c.re → c.re ≤ β + 1 → 2 ≤ |c.im| →
      closedBall c (1 / 2) ⊆ U ∧ ∀ z ∈ closedBall c (1 / 2), ‖F z‖ ≤ A * (2 + |c.im|) ^ B) :
    ∀ᵐ a : ℂ, ∃ κ > 0, ∀ s s' : ℂ, F s = a → F s' = a → s ≠ s' → α ≤ s.re → s.re ≤ β →
      3 ≤ |s.im| → κ / (2 + |s.im|) ^ (2 * B + 1) ≤ ‖s' - s‖ := by
  filter_upwards [ae_eventually_notMem (tsum_volume_badValues_ne_top F hαβ hA B)] with a ha
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp ha
  set D := 2 * B + 1 with hD
  refine ⟨min (1 / 64 : ℝ) (min (1 / 2 ^ k₀) (1 / 2 ^ D)), by positivity,
    fun s s' hs hs' hne hre0 hre1 him => ?_⟩
  set κ : ℝ := min (1 / 64 : ℝ) (min (1 / 2 ^ k₀) (1 / 2 ^ D)) with hκ
  set d := ‖s' - s‖ with hd
  have hd0 : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
  have hX1 : 1 ≤ (2 + |s.im|) ^ D := one_le_pow₀ (by linarith [abs_nonneg s.im])
  have hX0 : 0 < (2 + |s.im|) ^ D := by positivity
  have hκX : κ / (2 + |s.im|) ^ D ≤ κ := div_le_self (by positivity) hX1
  by_cases hfar : 1 / 64 < d
  · exact hκX.trans ((min_le_left _ _).trans hfar.le)
  push Not at hfar
  -- the dyadic scale `2^{−k−1} < d ≤ 2^{−k}`
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near (x := 1 / d) (y := (2 : ℝ))
    (by rw [le_div_iff₀ hd0]; linarith) (by norm_num)
  have hdk1 : d ≤ 1 / 2 ^ k := by
    rw [le_div_iff₀ hd0] at hk1
    rw [le_div_iff₀ (by positivity)]; linarith [mul_comm d (2 ^ k)]
  have hdk0 : 1 / 2 ^ (k + 1) < d := by
    rw [div_lt_iff₀ hd0] at hk2
    rw [div_lt_iff₀ (by positivity)]; linarith [mul_comm d (2 ^ (k + 1))]
  -- the midpoint stays within `1/128` of `s`
  have hn : ‖(s + s') / 2 - s‖ ≤ 1 / 128 := by
    rw [show (s + s') / 2 - s = (s' - s) / 2 by ring, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    linarith
  have hre' := (abs_re_le_norm _).trans hn
  have him' := (abs_im_le_norm _).trans hn
  rw [sub_re] at hre'
  rw [sub_im] at him'
  have hi1 := abs_sub_abs_le_abs_sub ((s + s') / 2).im s.im
  have hi2 := abs_sub_abs_le_abs_sub s.im ((s + s') / 2).im
  rw [abs_sub_comm] at hi2
  by_cases hcap : |((s + s') / 2).im| ≤ heightCap D k
  · have hmem := mem_badValues hU hF D k hM hs hs' hne hdk0 hdk1 hfar
      (by linarith [(abs_le.mp hre').1]) (by linarith [(abs_le.mp hre').2]) (by linarith) hcap
    have hkk : k < k₀ := by
      by_contra hcon
      push Not at hcon
      exact hk₀ k hcon hmem
    have : 1 / 2 ^ k₀ ≤ 1 / 2 ^ (k + 1) :=
      one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : k + 1 ≤ k₀))
    exact hκX.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (this.trans hdk0.le)))
  · push Not at hcap
    have hkD : k + 1 ≤ D * (k / D) + D := by
      have := Nat.lt_div_mul_add (a := k) (b := D) (by omega)
      linarith [mul_comm (k / D) D]
    have hcapD : ((heightCap D k : ℕ) : ℝ) ^ D = 2 ^ (D * (k / D)) := by
      rw [heightCap]; push_cast; rw [← pow_mul, mul_comm]
    have hcap0 : (0 : ℝ) ≤ ((heightCap D k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcapX : ((heightCap D k : ℕ) : ℝ) ≤ 2 + |s.im| := by linarith
    have h2pow : (2 : ℝ) ^ (k + 1) ≤ 2 ^ D * (2 + |s.im|) ^ D := by
      calc (2 : ℝ) ^ (k + 1) ≤ 2 ^ (D * (k / D) + D) := pow_le_pow_right₀ (by norm_num) hkD
        _ = 2 ^ D * ((heightCap D k : ℕ) : ℝ) ^ D := by rw [hcapD, pow_add, mul_comm]
        _ ≤ 2 ^ D * (2 + |s.im|) ^ D := by gcongr
    calc κ / (2 + |s.im|) ^ D ≤ (1 / 2 ^ D) / (2 + |s.im|) ^ D :=
          div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) hX0.le
      _ = 1 / (2 ^ D * (2 + |s.im|) ^ D) := by rw [div_div]
      _ ≤ 1 / 2 ^ (k + 1) := one_div_le_one_div_of_le (by positivity) h2pow
      _ ≤ d := hdk0.le

/-- **For `ζ`: almost every value collides or repels at polynomial scale.** There is one exponent
`C` such that for almost every `a ∈ ℂ`, distinct `a`-points `s ≠ s'` of `ζ` with `0 ≤ Re s ≤ 1`,
`|Im s| ≥ 3` satisfy `κ / (2 + |Im s|)^C ≤ |s' − s|`. B54 asks this for `a = 0`. -/
theorem ae_riemannZeta_values_collide_or_repel :
    ∃ C : ℕ, ∀ᵐ a : ℂ, ∃ κ > 0, ∀ s s' : ℂ, riemannZeta s = a → riemannZeta s' = a → s ≠ s' →
      0 ≤ s.re → s.re ≤ 1 → 3 ≤ |s.im| → κ / (2 + |s.im|) ^ C ≤ ‖s' - s‖ := by
  obtain ⟨A, N, hA, hbd⟩ := RHTower.exists_bound_norm_riemannZeta_strip 3
  have hfU : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} := fun s hs =>
    (differentiableAt_riemannZeta hs).differentiableWithinAt
  refine ⟨2 * N + 1, ae_collide_or_repel isOpen_ne hfU (by norm_num : (0 : ℝ) ≤ 1) hA ?_⟩
  intro c hc0 hc1 hc2
  have hz : ∀ z ∈ closedBall c (1 / 2), |z.re| ≤ 3 ∧ 1 ≤ |z.im| ∧ |z.im| ≤ 2 + |c.im| := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have hr := (abs_re_le_norm (z - c)).trans hz
    have hi := (abs_im_le_norm (z - c)).trans hz
    rw [sub_re] at hr
    rw [sub_im] at hi
    have a1 := abs_sub_abs_le_abs_sub z.im c.im
    have a2 := abs_sub_abs_le_abs_sub c.im z.im
    rw [abs_sub_comm] at a2
    refine ⟨abs_le.mpr ⟨by linarith [(abs_le.mp hr).1], by linarith [(abs_le.mp hr).2]⟩,
      by linarith, by linarith⟩
  refine ⟨fun z hzc h1 => ?_, fun z hzc => ?_⟩
  · obtain ⟨-, hi, -⟩ := hz z hzc
    rw [show z = 1 from h1, one_im, abs_zero] at hi
    linarith
  · obtain ⟨hr, hi, hi'⟩ := hz z hzc
    have h := hbd z.re z.im hr hi
    rw [Complex.re_add_im] at h
    refine h.trans ?_
    gcongr

end GaloisForLFunctions.ArithmeticDiscreteness
