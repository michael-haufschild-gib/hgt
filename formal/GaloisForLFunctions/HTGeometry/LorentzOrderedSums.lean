import Mathlib

/-!
# Lorentzian sums over ordered point sequences

Let `f_τ(u) = τ²/(τ² + u²)`.

* `sum_lorentz_lattice_le`: `Σ_{i=0}^{K} f_τ(iG) ≤ 1 + πτ/(2G)`, by comparing with `∫_0^∞ f_τ = πτ/2`.
* `sum_lorentz_sparse_le`: if a monotone sequence has gaps `≥ G` on `[a, b]`, then
  `Σ_{n ∈ [a,b]} f_τ(t − y_n) ≤ 2 + πτ/G`.
* `card_le_two_mul_sum_lorentz`: the points with `|t − y| ≤ τ` number at most `2 Σ f_τ(t − y)`.
* `card_near_ge_of_dense`: gaps `≤ g` covering `[t − τ, t + τ]` put at least `2τ/g − 1` points within `τ`.
* Comparisons: `f_τ ≤ f_{τ'}` for `τ ≤ τ'`; `f_τ(u) ≤ 3 f_τ(u + v)` for `|v| ≤ τ`;
  `f_{τ₁}(u) ≤ 2(τ₁/τ₂)² f_{τ₂}(u)` for `|u| ≥ τ₂`.
-/

noncomputable section

open Real MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- The Lorentzian `f_τ(u) = τ²/(τ² + u²)`. -/
def lorentzF (τ u : ℝ) : ℝ := τ ^ 2 / (τ ^ 2 + u ^ 2)

theorem lorentzF_nonneg (τ u : ℝ) : 0 ≤ lorentzF τ u := by unfold lorentzF; positivity

theorem lorentzF_le_one {τ : ℝ} (hτ : 0 < τ) (u : ℝ) : lorentzF τ u ≤ 1 := by
  unfold lorentzF
  rw [div_le_one (by positivity)]; nlinarith [sq_nonneg u]

theorem lorentzF_neg (τ u : ℝ) : lorentzF τ (-u) = lorentzF τ u := by unfold lorentzF; ring_nf

/-- `f_τ` is antitone on `[0, ∞)`. -/
theorem lorentzF_anti {τ : ℝ} (hτ : 0 < τ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    lorentzF τ v ≤ lorentzF τ u := by
  unfold lorentzF
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith

theorem lorentzF_abs (τ u : ℝ) : lorentzF τ |u| = lorentzF τ u := by
  unfold lorentzF; rw [sq_abs]

/-- `f_τ` is antitone in `|u|`. -/
theorem lorentzF_le_of_abs_le {τ : ℝ} (hτ : 0 < τ) {u v : ℝ} (h : |u| ≤ |v|) :
    lorentzF τ v ≤ lorentzF τ u := by
  rw [← lorentzF_abs τ v, ← lorentzF_abs τ u]
  exact lorentzF_anti hτ (abs_nonneg u) h

/-- `∫_a^b f_τ = τ (arctan(b/τ) − arctan(a/τ))`. -/
theorem integral_lorentzF {τ : ℝ} (hτ : 0 < τ) (a b : ℝ) :
    ∫ u in a..b, lorentzF τ u = τ * (Real.arctan (b / τ) - Real.arctan (a / τ)) := by
  have hd : ∀ u ∈ uIcc a b, HasDerivAt (fun u : ℝ => τ * Real.arctan (u / τ)) (lorentzF τ u) u := by
    intro u _
    have h := ((Real.hasDerivAt_arctan (u / τ)).comp u ((hasDerivAt_id u).div_const τ)).const_mul τ
    refine h.congr_deriv ?_
    unfold lorentzF
    field_simp
  have hint : IntervalIntegrable (lorentzF τ) volume a b := by
    apply Continuous.intervalIntegrable
    unfold lorentzF
    exact continuous_const.div (by fun_prop) fun u => by positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  ring

theorem integral_lorentzF_le {τ : ℝ} (hτ : 0 < τ) {a b : ℝ} (ha : 0 ≤ a) :
    ∫ u in a..b, lorentzF τ u ≤ Real.pi * τ / 2 := by
  rw [integral_lorentzF hτ]
  have h1 := Real.arctan_lt_pi_div_two (b / τ)
  have h2 : 0 ≤ Real.arctan (a / τ) := Real.arctan_nonneg.mpr (by positivity)
  nlinarith

/-- **Lorentzian lattice sums.** `Σ_{i=0}^{K} f_τ(iG) ≤ 1 + πτ/(2G)`. -/
theorem sum_lorentz_lattice_le {τ G : ℝ} (hτ : 0 < τ) (hG : 0 < G) (K : ℕ) :
    ∑ i ∈ Finset.range (K + 1), lorentzF τ (i * G) ≤ 1 + Real.pi * τ / (2 * G) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul]
  have h0 : lorentzF τ 0 = 1 := by
    unfold lorentzF; rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, div_self (by positivity)]
  rw [h0]
  -- each term is at most the average over the preceding cell
  have hcell : ∀ i ∈ Finset.range K, lorentzF τ (((i + 1 : ℕ) : ℝ) * G) ≤
      (1 / G) * ∫ u in (i * G)..((i + 1 : ℕ) * G), lorentzF τ u := by
    intro i _
    have hiG : (i : ℝ) * G ≤ ((i + 1 : ℕ) : ℝ) * G := by
      apply mul_le_mul_of_nonneg_right _ hG.le; push_cast; linarith
    have hle : ∀ u ∈ Icc ((i : ℝ) * G) (((i + 1 : ℕ) : ℝ) * G),
        (fun _ : ℝ => lorentzF τ (((i + 1 : ℕ) : ℝ) * G)) u ≤ lorentzF τ u := by
      intro u hu
      exact lorentzF_anti hτ (le_trans (by positivity) hu.1) hu.2
    have hcf : IntervalIntegrable (lorentzF τ) volume ((i : ℝ) * G) (((i + 1 : ℕ) : ℝ) * G) := by
      apply Continuous.intervalIntegrable; unfold lorentzF
      exact continuous_const.div (by fun_prop) fun u => by positivity
    have hcc : IntervalIntegrable (fun _ : ℝ => lorentzF τ (((i + 1 : ℕ) : ℝ) * G)) volume
        ((i : ℝ) * G) (((i + 1 : ℕ) : ℝ) * G) := intervalIntegrable_const
    have hint := intervalIntegral.integral_mono_on hiG hcc hcf hle
    rw [intervalIntegral.integral_const, smul_eq_mul] at hint
    have hlen : ((i + 1 : ℕ) : ℝ) * G - i * G = G := by push_cast; ring
    rw [hlen] at hint
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hG]
    linarith [mul_comm G (lorentzF τ (((i + 1 : ℕ) : ℝ) * G))]
  have hsum := Finset.sum_le_sum hcell
  rw [← Finset.mul_sum] at hsum
  have hadj : ∑ i ∈ Finset.range K, ∫ u in (i * G)..((i + 1 : ℕ) * G), lorentzF τ u =
      ∫ u in (0 : ℝ)..(K * G), lorentzF τ u := by
    have := intervalIntegral.sum_integral_adjacent_intervals (a := fun i : ℕ => (i : ℝ) * G)
      (f := lorentzF τ) (μ := volume) (n := K) (fun i _ => by
        apply Continuous.intervalIntegrable; unfold lorentzF
        exact continuous_const.div (by fun_prop) fun u => by positivity)
    simpa using this
  rw [hadj] at hsum
  have hI := integral_lorentzF_le hτ (a := 0) (b := K * G) le_rfl
  have hfin : (1 / G) * ∫ u in (0 : ℝ)..(K * G), lorentzF τ u ≤ Real.pi * τ / (2 * G) := by
    rw [one_div, ← div_eq_inv_mul, div_le_div_iff₀ hG (by positivity)]
    nlinarith
  simp only [Nat.cast_add, Nat.cast_one] at hsum ⊢
  linarith


/-- Gap chains: if every gap of `y` on `[a, b)` is `≥ G`, then `y m − y n ≥ (m − n) G` for
`a ≤ n ≤ m ≤ b`. -/
theorem sub_ge_of_gaps {y : ℕ → ℝ} {G : ℝ} {a b : ℕ}
    (hgap : ∀ n, a ≤ n → n < b → G ≤ y (n + 1) - y n) {n m : ℕ} (han : a ≤ n) (hnm : n ≤ m)
    (hmb : m ≤ b) : ((m - n : ℕ) : ℝ) * G ≤ y m - y n := by
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    have h1 := ih (by omega)
    have h2 := hgap m (by omega) (by omega)
    rw [show m + 1 - n = (m - n) + 1 by omega]
    push_cast
    linarith

/-- Gap chains from above: gaps `≤ g` give `y m − y n ≤ (m − n) g`. -/
theorem sub_le_of_gaps {y : ℕ → ℝ} {g : ℝ} {a b : ℕ}
    (hgap : ∀ n, a ≤ n → n < b → y (n + 1) - y n ≤ g) {n m : ℕ} (han : a ≤ n) (hnm : n ≤ m)
    (hmb : m ≤ b) : y m - y n ≤ ((m - n : ℕ) : ℝ) * g := by
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    have h1 := ih (by omega)
    have h2 := hgap m (by omega) (by omega)
    rw [show m + 1 - n = (m - n) + 1 by omega]
    push_cast
    linarith

/-- **Sparse sequences carry little Lorentzian mass.** If a monotone sequence has all gaps `≥ G`
on `[a, b]`, then `Σ_{n ∈ [a,b]} f_τ(t − y_n) ≤ 2 + πτ/G`. -/
theorem sum_lorentz_sparse_le {τ G : ℝ} (hτ : 0 < τ) (hG : 0 < G) {y : ℕ → ℝ} {a b : ℕ}
    (hgap : ∀ n, a ≤ n → n < b → G ≤ y (n + 1) - y n) (t : ℝ) :
    ∑ n ∈ Finset.Icc a b, lorentzF τ (t - y n) ≤ 2 + Real.pi * τ / G := by
  classical
  set R := (Finset.Icc a b).filter (fun n => t ≤ y n) with hR
  set L := (Finset.Icc a b).filter (fun n => ¬ t ≤ y n) with hL
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc a b) (fun n => t ≤ y n)]
  have hlat := sum_lorentz_lattice_le hτ hG b
  -- the right part
  have hRle : ∑ n ∈ R, lorentzF τ (t - y n) ≤ 1 + Real.pi * τ / (2 * G) := by
    rcases R.eq_empty_or_nonempty with hRe | hRne
    · rw [hRe, Finset.sum_empty]; positivity
    set n₀ := R.min' hRne with hn₀
    have hn₀R' := Finset.mem_filter.mp (R.min'_mem hRne)
    have hn₀R : (a ≤ n₀ ∧ n₀ ≤ b) ∧ t ≤ y n₀ := ⟨Finset.mem_Icc.mp hn₀R'.1, hn₀R'.2⟩
    have hpt : ∀ n ∈ R, lorentzF τ (t - y n) ≤ lorentzF τ (((n - n₀ : ℕ) : ℝ) * G) := by
      intro n hn
      have hle : n₀ ≤ n := R.min'_le n hn
      rw [hR, Finset.mem_filter, Finset.mem_Icc] at hn
      have hchain := sub_ge_of_gaps hgap hn₀R.1.1 hle hn.1.2
      apply lorentzF_le_of_abs_le hτ
      rw [abs_of_nonneg (by positivity), abs_of_nonpos (by linarith [hn₀R.2])]
      linarith [hn₀R.2]
    refine (Finset.sum_le_sum hpt).trans ?_
    have hinj : Set.InjOn (fun n => n - n₀) R := by
      intro n hn m hm h
      have h1 : n₀ ≤ n := R.min'_le n hn
      have h2 : n₀ ≤ m := R.min'_le m hm
      simp only at h; omega
    rw [← Finset.sum_image (f := fun i : ℕ => lorentzF τ ((i : ℝ) * G)) hinj]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => lorentzF_nonneg τ _) hlat
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨n, hn, rfl⟩ := hi
    rw [hR, Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Finset.mem_range]; omega
  -- the left part
  have hLle : ∑ n ∈ L, lorentzF τ (t - y n) ≤ 1 + Real.pi * τ / (2 * G) := by
    rcases L.eq_empty_or_nonempty with hLe | hLne
    · rw [hLe, Finset.sum_empty]; positivity
    set n₁ := L.max' hLne with hn₁
    have hn₁L' := Finset.mem_filter.mp (L.max'_mem hLne)
    have hn₁L : (a ≤ n₁ ∧ n₁ ≤ b) ∧ ¬ t ≤ y n₁ := ⟨Finset.mem_Icc.mp hn₁L'.1, hn₁L'.2⟩
    have hpt : ∀ n ∈ L, lorentzF τ (t - y n) ≤ lorentzF τ (((n₁ - n : ℕ) : ℝ) * G) := by
      intro n hn
      have hle : n ≤ n₁ := L.le_max' n hn
      rw [hL, Finset.mem_filter, Finset.mem_Icc] at hn
      have hchain := sub_ge_of_gaps hgap hn.1.1 hle hn₁L.1.2
      apply lorentzF_le_of_abs_le hτ
      push Not at hn hn₁L
      rw [abs_of_nonneg (by positivity), abs_of_pos (by linarith [hn.2])]
      linarith [hn₁L.2]
    refine (Finset.sum_le_sum hpt).trans ?_
    have hinj : Set.InjOn (fun n => n₁ - n) L := by
      intro n hn m hm h
      have h1 : n ≤ n₁ := L.le_max' n hn
      have h2 : m ≤ n₁ := L.le_max' m hm
      simp only at h; omega
    rw [← Finset.sum_image (f := fun i : ℕ => lorentzF τ ((i : ℝ) * G)) hinj]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => lorentzF_nonneg τ _) hlat
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨n, hn, rfl⟩ := hi
    rw [hL, Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Finset.mem_range]; omega
  have : Real.pi * τ / (2 * G) + Real.pi * τ / (2 * G) = Real.pi * τ / G := by
    field_simp; ring
  linarith

/-- Points within `τ` of `t` each carry Lorentzian weight `≥ ½`. -/
theorem card_le_two_mul_sum_lorentz {τ : ℝ} (hτ : 0 < τ) (S : Finset ℕ) (y : ℕ → ℝ) (t : ℝ) :
    ((S.filter (fun n => |t - y n| ≤ τ)).card : ℝ) ≤ 2 * ∑ n ∈ S, lorentzF τ (t - y n) := by
  classical
  calc ((S.filter (fun n => |t - y n| ≤ τ)).card : ℝ)
      = ∑ n ∈ S.filter (fun n => |t - y n| ≤ τ), (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ S.filter (fun n => |t - y n| ≤ τ), 2 * lorentzF τ (t - y n) := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [Finset.mem_filter] at hn
        unfold lorentzF
        rw [mul_div_assoc', le_div_iff₀ (by positivity)]
        have : (t - y n) ^ 2 ≤ τ ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hn.2 2
        nlinarith
    _ ≤ ∑ n ∈ S, 2 * lorentzF τ (t - y n) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun n _ _ => by have := lorentzF_nonneg τ (t - y n); positivity
    _ = 2 * ∑ n ∈ S, lorentzF τ (t - y n) := by rw [Finset.mul_sum]

/-- **Dense chains put many points near `t`.** If a monotone sequence has gaps `≤ g` on `[a, b]`
with `y_a ≤ t − τ` and `t + τ ≤ y_b`, then at least `2τ/g − 1` indices in `[a,b]` satisfy
`|t − y_n| ≤ τ`. -/
theorem card_near_ge_of_dense {τ g : ℝ} (hτ : 0 < τ) (hg : 0 < g) {y : ℕ → ℝ} (hy : Monotone y)
    {a b : ℕ} (hgap : ∀ n, a ≤ n → n < b → y (n + 1) - y n ≤ g) {t : ℝ} (ha : y a ≤ t - τ)
    (hb : t + τ ≤ y b) :
    2 * τ / g - 1 ≤ (((Finset.Icc a b).filter (fun n => |t - y n| ≤ τ)).card : ℝ) := by
  classical
  have hab : a ≤ b := by
    by_contra h; push Not at h
    have := hy h.le; linarith
  rcases lt_or_ge (2 * τ) g with hsmall | hbig
  · have : 2 * τ / g - 1 < 0 := by rw [div_sub_one hg.ne', div_neg_iff]; right; constructor <;> linarith
    exact this.le.trans (Nat.cast_nonneg _)
  -- the first index at or above `t − τ`
  have hex : ∃ n, a ≤ n ∧ n ≤ b ∧ t - τ ≤ y n := ⟨b, hab, le_rfl, by linarith⟩
  obtain ⟨hpa, hpb, hpy⟩ := Nat.find_spec hex
  set p := Nat.find hex with hp
  -- the last index at or below `t + τ`
  have hex' : ∃ k, k ≤ b - a ∧ y (b - k) ≤ t + τ := ⟨b - a, le_rfl, by
    rw [show b - (b - a) = a by omega]; linarith⟩
  obtain ⟨hkb, hky⟩ := Nat.find_spec hex'
  set k := Nat.find hex' with hk
  set q := b - k with hq
  -- `y p < t − τ + g` and `y q > t + τ − g`
  have hp_lt : y p < t - τ + g := by
    rcases eq_or_lt_of_le hpa with h | h
    · rw [← h]; linarith
    · have hpm : ¬ (a ≤ p - 1 ∧ p - 1 ≤ b ∧ t - τ ≤ y (p - 1)) :=
        Nat.find_min hex (show p - 1 < p by omega)
      have hlt : y (p - 1) < t - τ := by
        by_contra hc; push Not at hc; exact hpm ⟨by omega, by omega, hc⟩
      have := hgap (p - 1) (by omega) (by omega)
      rw [show p - 1 + 1 = p by omega] at this
      linarith
  have hq_gt : t + τ - g < y q := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [hq, h, Nat.sub_zero]; linarith
    · have hkm : ¬ (k - 1 ≤ b - a ∧ y (b - (k - 1)) ≤ t + τ) :=
        Nat.find_min hex' (show k - 1 < k by omega)
      have hgt : t + τ < y (b - (k - 1)) := by
        by_contra hc; push Not at hc; exact hkm ⟨by omega, hc⟩
      have := hgap q (by omega) (by omega)
      rw [show q + 1 = b - (k - 1) by omega] at this
      linarith
  have hpq : p ≤ q := by
    by_contra h; push Not at h
    have hqm : ¬ (a ≤ q ∧ q ≤ b ∧ t - τ ≤ y q) := Nat.find_min hex (by rw [← hp]; exact h)
    have hlt : y q < t - τ := by
      by_contra hc; push Not at hc; exact hqm ⟨by omega, by omega, hc⟩
    linarith
  -- all indices in `[p, q]` are near `t`
  have hsub : Finset.Icc p q ⊆ (Finset.Icc a b).filter (fun n => |t - y n| ≤ τ) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have h1 := hy hn.1
    have h2 := hy hn.2
    rw [abs_le]; constructor <;> linarith
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have hspan := sub_le_of_gaps hgap hpa hpq (by omega)
  have hqp : 2 * τ - 2 * g < ((q - p : ℕ) : ℝ) * g := by linarith
  have : 2 * τ / g - 1 ≤ ((q + 1 - p : ℕ) : ℝ) := by
    rw [div_sub_one hg.ne', div_le_iff₀ hg]
    rw [show q + 1 - p = (q - p) + 1 by omega]; push_cast; nlinarith
  exact this.trans (by exact_mod_cast hcard)


/-- `f_τ(u)` increases with the scale. -/
theorem lorentzF_mono_scale {τ τ' : ℝ} (hτ : 0 < τ) (hττ' : τ ≤ τ') (u : ℝ) :
    lorentzF τ u ≤ lorentzF τ' u := by
  unfold lorentzF
  rw [div_le_div_iff₀ (by positivity) (by nlinarith [sq_nonneg u])]
  have : τ ^ 2 ≤ τ' ^ 2 := pow_le_pow_left₀ hτ.le hττ' 2
  nlinarith [sq_nonneg u, mul_le_mul_of_nonneg_left this (sq_nonneg u)]

/-- **Shifts by at most the scale cost a factor `3`:** `f_τ(u) ≤ 3 f_τ(u + v)` for `|v| ≤ τ`. -/
theorem lorentzF_le_three_mul_shift {τ : ℝ} (hτ : 0 < τ) (u : ℝ) {v : ℝ} (hv : |v| ≤ τ) :
    lorentzF τ u ≤ 3 * lorentzF τ (u + v) := by
  unfold lorentzF
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have hv2 : v ^ 2 ≤ τ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hv 2
  have h1 : (u + v) ^ 2 ≤ 2 * u ^ 2 + 2 * v ^ 2 := by nlinarith [sq_nonneg (u - v)]
  have hτ2 : 0 < τ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 hτ2.le, mul_le_mul_of_nonneg_left hv2 hτ2.le]

/-- **Tails at a smaller scale:** `f_{τ₁}(u) ≤ 2(τ₁/τ₂)² f_{τ₂}(u)` for `|u| ≥ τ₂`. -/
theorem lorentzF_le_tail {τ₁ τ₂ u : ℝ} (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) (hu : τ₂ ≤ |u|) :
    lorentzF τ₁ u ≤ 2 * (τ₁ / τ₂) ^ 2 * lorentzF τ₂ u := by
  have hu2 : τ₂ ^ 2 ≤ u ^ 2 := by rw [← sq_abs u]; exact pow_le_pow_left₀ hτ₂.le hu 2
  unfold lorentzF
  have e : 2 * (τ₁ / τ₂) ^ 2 * (τ₂ ^ 2 / (τ₂ ^ 2 + u ^ 2)) = 2 * τ₁ ^ 2 / (τ₂ ^ 2 + u ^ 2) := by
    field_simp
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hu2 (sq_nonneg τ₁), sq_nonneg τ₁]

end GaloisForLFunctions.HTGeometry
