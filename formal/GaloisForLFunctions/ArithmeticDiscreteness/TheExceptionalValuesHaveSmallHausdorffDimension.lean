import GaloisForLFunctions.ArithmeticDiscreteness.TheExceptionalValuesOfZetaAreResidual
import Mathlib.Topology.MetricSpace.HausdorffDimension
/-!
# Hausdorff dimension of nonrepelling zeta values

Values for which distinct equal-value points of ζ admit no polynomial separation law form a
set of Hausdorff dimension at most one. This includes the dense residual set of values with
exponentially close pairs at arbitrarily large heights.

Two nearby equal-value points make the value and derivative small at their midpoint. A mesh of
size `2⁻ᵏ` therefore covers their values by discs of radius `O(Yᴮ4⁻ᵏ)`, with `O(Y4ᵏ)` grid points
up to height `Y`. Choosing `Y = 2^⌊k/D⌋` with sufficiently large `D` makes the diameter powers
summable in every dimension greater than one. The strip growth bound for ζ supplies all analytic
inputs. The theorem does not determine whether zero belongs to the exceptional set.
-/

open Complex Metric Set MeasureTheory MeasureTheory.Measure Filter Topology
open scoped ENNReal
noncomputable section
namespace GaloisForLFunctions.ArithmeticDiscreteness

private theorem ediam_closedBall_le_ofReal (c : ℂ) (r : ℝ) :
    ediam (closedBall c r) ≤ ENNReal.ofReal (2 * r) := by
  apply Metric.ediam_le
  intro x hx y hy
  rw [edist_dist]
  apply ENNReal.ofReal_le_ofReal
  calc dist x y ≤ dist x c + dist y c := dist_triangle_right _ _ _
    _ ≤ r + r := add_le_add hx hy
    _ = 2 * r := by ring

/-- Summable diameter costs of shrinking tail covers force zero Hausdorff measure. -/
private theorem hausdorffMeasure_eq_zero_of_tail_covers
    {ι : Type*} [Countable ι] (S : Set ℂ) (G : ℕ → Finset ι) (c : ℕ → ι → ℂ)
    (r w : ℕ → ℝ) (s : ℝ) (hs : 0 < s)
    (hr : ∀ k, 0 ≤ r k) (hrmono : Antitone r) (hrlim : Tendsto r atTop (𝓝 0))
    (hw : ∀ k, 0 ≤ w k) (hwsum : Summable w)
    (hcost : ∀ k, (G k).card * (2 * r k) ^ s ≤ w k)
    (hcover : ∀ N, S ⊆ ⋃ k ≥ N, ⋃ i ∈ G k, closedBall (c k i) (r k)) :
    μH[s] S = 0 := by
  classical
  let J (N : ℕ) := (n : ℕ) × {i // i ∈ G (N + n)}
  let U (N : ℕ) (j : J N) := closedBall (c (N + j.1) j.2) (r (N + j.1))
  have hd : ∀ N (j : J N), ediam (U N j) ≤ ENNReal.ofReal (2 * r N) := by
    intro N j
    exact (ediam_closedBall_le_ofReal _ _).trans (ENNReal.ofReal_le_ofReal (by
      exact mul_le_mul_of_nonneg_left (hrmono (Nat.le_add_right N j.1)) (by norm_num)))
  have hc : ∀ N, S ⊆ ⋃ j : J N, U N j := by
    intro N a ha
    obtain ⟨k, hk, hak⟩ := mem_iUnion₂.mp (hcover N ha)
    obtain ⟨i, hi, hai⟩ := mem_iUnion₂.mp hak
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
    exact mem_iUnion.mpr ⟨⟨n, ⟨i, hi⟩⟩, hai⟩
  have hrlim' : Tendsto (fun N => ENNReal.ofReal (2 * r N)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (hrlim.const_mul 2)
  have hbound := hausdorffMeasure_le_liminf_tsum s S
    (fun N => ENNReal.ofReal (2 * r N)) hrlim' U
    (Eventually.of_forall hd) (Eventually.of_forall hc)
  have hsum : ∀ N, (∑' j : J N, ediam (U N j) ^ s) ≤
      (∑' n, ENNReal.ofReal (w (N + n))) := by
    intro N
    change (∑' j : (n : ℕ) × {i // i ∈ G (N + n)},
      ediam (U N j) ^ s) ≤ _
    rw [ENNReal.tsum_sigma (fun n i => ediam (U N ⟨n, i⟩) ^ s)]
    apply ENNReal.tsum_le_tsum
    intro n
    calc (∑' i : {i // i ∈ G (N + n)}, ediam (U N ⟨n, i⟩) ^ s)
        ≤ ∑' _i : {i // i ∈ G (N + n)},
            ENNReal.ofReal ((2 * r (N + n)) ^ s) := by
              apply ENNReal.tsum_le_tsum
              intro i
              rw [← ENNReal.ofReal_rpow_of_nonneg
                (mul_nonneg (by norm_num) (hr _)) hs.le]
              exact ENNReal.rpow_le_rpow (ediam_closedBall_le_ofReal _ _) hs.le
      _ = ENNReal.ofReal ((G (N + n)).card * (2 * r (N + n)) ^ s) := by
        simp [tsum_fintype, ENNReal.ofReal_mul, Nat.cast_nonneg]
      _ ≤ ENNReal.ofReal (w (N + n)) := ENNReal.ofReal_le_ofReal (hcost _)
  have hfinite : (∑' k, ENNReal.ofReal (w k)) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hw hwsum]
    exact ENNReal.ofReal_ne_top
  have hlim : Tendsto (fun N => ∑' n, ENNReal.ofReal (w (N + n))) atTop (𝓝 0) := by
    simpa only [Nat.add_comm] using
      ENNReal.tendsto_sum_nat_add (fun k => ENNReal.ofReal (w k)) hfinite
  have hz := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun N => bot_le) hsum
  exact le_antisymm (hbound.trans_eq hz.liminf_eq) bot_le

/-- Polynomial separation of distinct equal-value points in a fixed vertical strip. -/
def PolynomialValueRepulsion (F : ℂ → ℂ) (α β : ℝ) (a : ℂ) : Prop :=
  ∃ D : ℕ, ∃ κ > 0, ∀ s s' : ℂ, F s = a → F s' = a → s ≠ s' →
    α ≤ s.re → s.re ≤ β → 3 ≤ |s.im| → κ / (2 + |s.im|) ^ D ≤ ‖s' - s‖

/-- Avoiding the dyadic close-pair covers eventually gives polynomial separation. -/
theorem polynomialValueRepulsion_of_eventually_notMem_badValues
    {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    {α β A : ℝ} {B D : ℕ} (hD : 0 < D)
    (hM : ∀ c : ℂ, α - 1 ≤ c.re → c.re ≤ β + 1 → 2 ≤ |c.im| →
      closedBall c (1 / 2) ⊆ U ∧ ∀ z ∈ closedBall c (1 / 2), ‖F z‖ ≤ A * (2 + |c.im|) ^ B)
    {a : ℂ} (ha : ∀ᶠ k in atTop, a ∉ badValues F α β A B D k) :
    PolynomialValueRepulsion F α β a := by
  refine ⟨D, ?_⟩
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp ha
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
    have : (1 : ℝ) / 2 ^ k₀ ≤ 1 / 2 ^ (k + 1) :=
      one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : k + 1 ≤ k₀))
    exact hκX.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (this.trans hdk0.le)))
  · push Not at hcap
    have hkD : k + 1 ≤ D * (k / D) + D := by
      have := Nat.lt_div_mul_add (a := k) (b := D) (hD)
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

private theorem heightCap_le_exp (D k : ℕ) :
    (heightCap D k : ℝ) ≤ Real.exp (Real.log 2 / D * k) := by
  rw [heightCap, Nat.cast_pow, Nat.cast_ofNat]
  rw [show (2 : ℝ) ^ (k / D) = Real.exp ((k / D : ℕ) * Real.log 2) by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right (Nat.cast_div_le (m := k) (n := D) (α := ℝ))
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  calc ((k / D : ℕ) : ℝ) * Real.log 2 ≤ ((k : ℝ) / D) * Real.log 2 := h
    _ = Real.log 2 / D * k := by ring

/-- The rectangular mesh has quadratic scale growth and one additional height factor. -/
private theorem gridIdx_card_le_exp {α β : ℝ} (hαβ : α ≤ β) (D k : ℕ) :
    ((gridIdx α β D k).card : ℝ) ≤
      (3 * (β - α + 4)) * Real.exp ((2 * Real.log 2 + Real.log 2 / D) * k) := by
  have hk1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hY1 : (1 : ℝ) ≤ heightCap D k := by
    rw [heightCap]; push_cast; exact one_le_pow₀ (by norm_num)
  have hc1 : (⌈2 ^ k * (β - α + 2)⌉₊ : ℝ) < 2 ^ k * (β - α + 2) + 1 :=
    Nat.ceil_lt_add_one (by nlinarith)
  have hA1 : (⌈2 ^ k * (β - α + 2)⌉₊ : ℝ) + 1 ≤ 2 ^ k * (β - α + 4) := by
    nlinarith only [hc1, hk1]
  have hA2 : 2 * (heightCap D k : ℝ) * 2 ^ k + 1 ≤ 3 * (heightCap D k : ℝ) * 2 ^ k := by
    nlinarith only [mul_le_mul hk1 hY1 (by norm_num : (0 : ℝ) ≤ 1) (by positivity)]
  calc ((gridIdx α β D k).card : ℝ)
      ≤ (2 ^ k * (β - α + 4)) * (3 * (heightCap D k : ℝ) * 2 ^ k) := by
        rw [gridIdx, Finset.card_product, Finset.card_range, Finset.card_range]
        push_cast
        exact mul_le_mul hA1 hA2 (by positivity) (by nlinarith only [hαβ, hk1])
    _ ≤ (2 ^ k * (β - α + 4)) * (3 * Real.exp (Real.log 2 / D * k) * 2 ^ k) := by
        gcongr
        exact heightCap_le_exp D k
    _ = (3 * (β - α + 4)) * Real.exp ((2 * Real.log 2 + Real.log 2 / D) * k) := by
        rw [show (2 : ℝ) ^ k = Real.exp (k * Real.log 2) by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]]
        rw [show (2 * Real.log 2 + Real.log 2 / D) * (k : ℝ) =
          k * Real.log 2 + Real.log 2 / D * k + k * Real.log 2 by ring,
          Real.exp_add, Real.exp_add]
        ring

/-- Equal-value pairs give quadratic image radii, with only polynomial height loss. -/
private theorem badValues_radius_le_exp {A : ℝ} (hA : 0 ≤ A) (B D k : ℕ) :
    2000 * A * (2 + (heightCap D k : ℝ)) ^ B / 4 ^ k ≤
      (2000 * A * 3 ^ B) * Real.exp (-(2 * Real.log 2 - B * (Real.log 2 / D)) * k) := by
  have hY1 : (1 : ℝ) ≤ heightCap D k := by
    rw [heightCap]; push_cast; exact one_le_pow₀ (by norm_num)
  have hYB : (2 + (heightCap D k : ℝ)) ^ B ≤
      3 ^ B * Real.exp (Real.log 2 / D * k) ^ B := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    linarith [heightCap_le_exp D k]
  calc 2000 * A * (2 + (heightCap D k : ℝ)) ^ B / 4 ^ k
      ≤ (2000 * A * 3 ^ B) * Real.exp (Real.log 2 / D * k) ^ B / 4 ^ k := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        calc 2000 * A * (2 + (heightCap D k : ℝ)) ^ B
            ≤ 2000 * A * (3 ^ B * Real.exp (Real.log 2 / D * k) ^ B) :=
              mul_le_mul_of_nonneg_left hYB (by positivity)
          _ = _ := by ring
    _ = (2000 * A * 3 ^ B) *
        Real.exp (-(2 * Real.log 2 - B * (Real.log 2 / D)) * k) := by
        rw [← Real.exp_nat_mul,
          show (4 : ℝ) ^ k = Real.exp ((2 * Real.log 2) * k) by
            rw [mul_comm (2 * Real.log 2), Real.exp_nat_mul]
            congr 1
            rw [show 2 * Real.log 2 = Real.log 2 + Real.log 2 by ring,
              Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
            norm_num,
          div_eq_mul_inv, ← Real.exp_neg]
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        congr 1
        ring

/-- The values without polynomial separation have zero Hausdorff measure in every dimension
strictly greater than one. Varying the height cap makes the quadratic image cover summable. -/
theorem hausdorffMeasure_nonrepellingValues_eq_zero
    {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    {α β A : ℝ} {B : ℕ} (hαβ : α ≤ β) (hA : 0 ≤ A)
    (hM : ∀ c : ℂ, α - 1 ≤ c.re → c.re ≤ β + 1 → 2 ≤ |c.im| →
      closedBall c (1 / 2) ⊆ U ∧ ∀ z ∈ closedBall c (1 / 2), ‖F z‖ ≤ A * (2 + |c.im|) ^ B)
    {s : ℝ} (hs : 1 < s) :
    μH[s] {a | ¬ PolynomialValueRepulsion F α β a} = 0 := by
  classical
  -- The free height exponent pays the polynomial growth in every dimension above one.
  obtain ⟨D, hDlarge⟩ := exists_nat_gt (max 0 ((s * B + 1) / (2 * (s - 1))))
  have hDpos : (0 : ℝ) < D := (le_max_left _ _).trans_lt hDlarge
  have hD : 0 < D := by exact_mod_cast hDpos
  have hchoose : s * B + 1 < 2 * (s - 1) * D := by
    have := (le_max_right _ _).trans_lt hDlarge
    rw [div_lt_iff₀ (by linarith)] at this
    nlinarith only [this]
  let ell := Real.log 2
  let e := ell / D
  let a := 2 * ell + e
  let b := 2 * ell - B * e
  have hell : 0 < ell := Real.log_pos (by norm_num)
  have he : 0 < e := div_pos hell hDpos
  have hDe : (D : ℝ) * e = ell := by dsimp [e]; field_simp
  have hab : a < b * s := by
    have h := mul_lt_mul_of_pos_right hchoose he
    rw [mul_assoc (2 * (s - 1)), hDe] at h
    dsimp [a, b]
    nlinarith only [h]
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by nlinarith only [hab, ha, hs]
  let C := 3 * (β - α + 4)
  let R := 2000 * A * 3 ^ B
  let r : ℕ → ℝ := fun k => R * Real.exp (-b * k)
  let w : ℕ → ℝ := fun k => (C * (2 * R) ^ s) * Real.exp ((a - b * s) * k)
  have hC : 0 ≤ C := by dsimp [C]; linarith
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hrlim : Tendsto r atTop (𝓝 0) := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
      (Real.exp_pos (-b)).le (Real.exp_lt_one_iff.mpr (by linarith : -b < 0))
    simpa only [r, mul_comm (-b), Real.exp_nat_mul, mul_zero] using hpow.const_mul R
  have hsum : Summable w := by
    have h := (summable_geometric_of_lt_one (Real.exp_pos (a - b * s)).le
      (Real.exp_lt_one_iff.mpr (sub_neg.mpr hab))).mul_left (C * (2 * R) ^ s)
    simpa only [w, mul_comm (a - b * s), Real.exp_nat_mul] using h
  refine hausdorffMeasure_eq_zero_of_tail_covers _ (gridIdx α β D)
    (fun k p => F (gridPt α D k p)) r w s (by linarith)
    (fun k => mul_nonneg hR (Real.exp_pos _).le) ?_ hrlim
    (fun k => by dsimp [w]; positivity) hsum ?_ ?_
  · intro k j hkj
    apply mul_le_mul_of_nonneg_left _ hR
    apply Real.exp_le_exp.mpr
    have hkj' : (k : ℝ) ≤ j := by exact_mod_cast hkj
    nlinarith only [hkj', hb]
  · intro k
    have hc := gridIdx_card_le_exp hαβ D k
    change ((gridIdx α β D k).card : ℝ) ≤ C * Real.exp (a * k) at hc
    calc ((gridIdx α β D k).card : ℝ) * (2 * r k) ^ s
        ≤ (C * Real.exp (a * k)) * (2 * r k) ^ s :=
          mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by dsimp [r]; positivity) _)
      _ = w k := by
        dsimp [r, w]
        rw [show 2 * (R * Real.exp (-b * (k : ℝ))) =
          (2 * R) * Real.exp (-b * k) by ring,
          Real.mul_rpow (by positivity) (by positivity), ← Real.exp_mul]
        rw [show C * Real.exp (a * (k : ℝ)) *
            ((2 * R) ^ s * Real.exp (-b * k * s)) =
          (C * (2 * R) ^ s) * (Real.exp (a * k) * Real.exp (-b * k * s)) by ring,
          ← Real.exp_add, show a * (k : ℝ) + -b * k * s = (a - b * s) * k by ring]
  · intro N z hz
    obtain ⟨k, hk, hzk⟩ : ∃ k, N ≤ k ∧ z ∈ badValues F α β A B D k := by
      by_contra hnone
      apply hz
      apply polynomialValueRepulsion_of_eventually_notMem_badValues hU hF hD hM
      filter_upwards [eventually_ge_atTop N] with k hk
      exact fun hzk => hnone ⟨k, hk, hzk⟩
    obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.mp hzk
    refine mem_iUnion₂.mpr ⟨k, hk, mem_iUnion₂.mpr ⟨p, hp, ?_⟩⟩
    exact (closedBall_subset_closedBall (badValues_radius_le_exp hA B D k)) hzp

/-- Values of ζ which fail every polynomial separation law in the critical strip. -/
def zetaNonrepellingValues : Set ℂ :=
  {a | ¬ PolynomialValueRepulsion riemannZeta 0 1 a}

/-- The exceptional set for polynomial repulsion of ζ-values has Hausdorff dimension at most
one, although it contains a dense residual subset of the complex plane. -/
theorem dimH_zetaNonrepellingValues_le_one : dimH zetaNonrepellingValues ≤ 1 := by
  obtain ⟨A, N, hA, hbd⟩ := RHTower.exists_bound_norm_riemannZeta_strip 3
  have hfU : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} := fun s hs =>
    (differentiableAt_riemannZeta hs).differentiableWithinAt
  have hM : ∀ c : ℂ, (0 : ℝ) - 1 ≤ c.re → c.re ≤ 1 + 1 → 2 ≤ |c.im| →
      closedBall c (1 / 2) ⊆ {s : ℂ | s ≠ 1} ∧
        ∀ z ∈ closedBall c (1 / 2), ‖riemannZeta z‖ ≤ A * (2 + |c.im|) ^ N := by
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

  apply dimH_le
  intro d hd
  by_contra hle
  have hd1 : (1 : ℝ) < d := by
    have : (1 : ℝ≥0∞) < (d : ℝ≥0∞) := lt_of_not_ge hle
    exact_mod_cast this
  have hzero := hausdorffMeasure_nonrepellingValues_eq_zero isOpen_ne hfU
    (by norm_num : (0 : ℝ) ≤ 1) hA hM hd1
  exact ENNReal.zero_ne_top (hzero.symm.trans hd)

/-- The residual set of exponentially close ζ-values is at most one-dimensional. -/
theorem dimH_exceptional_values_of_riemannZeta_le_one :
    dimH (⋂ n, exceptionalSet n) ≤ 1 := by
  refine (dimH_mono ?_).trans dimH_zetaNonrepellingValues_le_one
  intro a ha
  rintro ⟨D, κ, hκ, hrep⟩
  obtain ⟨s, s', hs, hs', hne, hre0, hre1, him, hd⟩ :=
    exists_superpolynomial_pair ha hκ D
  exact (not_le.mpr hd) (hrep s s' hs hs' hne hre0 hre1 him)

#print axioms dimH_zetaNonrepellingValues_le_one
#print axioms dimH_exceptional_values_of_riemannZeta_le_one

end GaloisForLFunctions.ArithmeticDiscreteness
