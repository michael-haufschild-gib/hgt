import GaloisForLFunctions.RHTower.JointAncestryConstantVectorEveryScale

/-!
# Constant-vector JAS tests detect a maximal off-line zero on every dyadic shell

The level-one constant-vector JAS test on the primes of a dyadic shell `(N, 2N]` is negative for
some `z ∈ ℂ` at every sufficiently large `N`, as soon as an off-line zero has the largest distance
from the critical line.  Hence RH holds iff the zeros approach the line and constant-vector
positivity holds on infinitely many dyadic shells.

On a shell, the main term of the prime sum `Σ_{N<p≤2N} p^{−s}` is `N^{1−s}(2^{1−s}−1)/((1−s) log N)`.
Zeros at the same distance from the line can therefore tie in size: the factor `|2^{1−s}−1|/|1−s|`
is not monotone in the height.  All ties are handled at once by a multi-point anti-alignment lemma.

**Anti-alignment of finitely many points** (`exists_multi_antiAligned`).  Let finitely many terms
`w_t e^{Y_t ζ_t + e_t}` be given, with `Y_t ∈ {Y, Ȳ}`, `‖ζ_t‖ ≤ 1`, `Re w_t ≥ c‖w_t‖`, and one point
`ζ_{t₀} = 1` of type `Y`.  Take a ladder `R₀ < R₁ < …` with `2L/R_{k+1} ≤ τ(R_k)²`, where
`τ(R) = c/(8(R + 4))`.
* The bands `[τ(R_k)², 2L/R_k)` of squared distances `‖ζ − 1‖²` are disjoint, so one of `|T| + 1`
  bands contains none of the `|T|` points.
* At that rung put `Y = R_k + iπ`.  Points below the band (near) satisfy `e^{Y_tζ_t} ≈ −e^R`, which
  is anti-aligned with every `w_t` of positive real part.  Points above the band (far) are
  `e^{−L}`-small relative to `e^R`.
-/

open Complex Filter
open scoped ComplexConjugate Topology BigOperators

namespace RHTower

noncomputable section

/-! ## Anti-alignment of finitely many points -/

/-- The near radius `τ(R) = c/(8(R + 4))`. -/
def nearRadius (c R : ℝ) : ℝ := c / (8 * (R + 4))

/-- The ladder `R_{k+1} = R_k + 1 + 2L/τ(R_k)²`. -/
def antiAlignLadder (c L R₀ : ℝ) : ℕ → ℝ
  | 0 => R₀
  | k + 1 => antiAlignLadder c L R₀ k + 1 + 2 * L / nearRadius c (antiAlignLadder c L R₀ k) ^ 2

theorem nearRadius_pos {c R : ℝ} (hc : 0 < c) (hR : 0 ≤ R) : 0 < nearRadius c R := by
  rw [nearRadius]; positivity

theorem antiAlignLadder_ge {c L R₀ : ℝ} (hL : 0 ≤ L) (k : ℕ) : R₀ ≤ antiAlignLadder c L R₀ k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [antiAlignLadder]
    have : 0 ≤ 2 * L / nearRadius c (antiAlignLadder c L R₀ k) ^ 2 := by positivity
    linarith

theorem antiAlignLadder_mono {c L R₀ : ℝ} (hL : 0 ≤ L) : Monotone (antiAlignLadder c L R₀) := by
  refine monotone_nat_of_le_succ fun k => ?_
  rw [antiAlignLadder]
  have : 0 ≤ 2 * L / nearRadius c (antiAlignLadder c L R₀ k) ^ 2 := by positivity
  linarith

/-- `2L/R_{k+1} ≤ τ(R_k)²`. -/
theorem two_mul_div_antiAlignLadder_succ_le {c L R₀ : ℝ} (hc : 0 < c) (hL : 0 ≤ L) (hR₀ : 0 ≤ R₀)
    (k : ℕ) :
    2 * L / antiAlignLadder c L R₀ (k + 1) ≤ nearRadius c (antiAlignLadder c L R₀ k) ^ 2 := by
  have hRk := hR₀.trans (antiAlignLadder_ge (c := c) hL k)
  have hτ := nearRadius_pos hc hRk
  have hτ2 : 0 < nearRadius c (antiAlignLadder c L R₀ k) ^ 2 := by positivity
  rw [antiAlignLadder]
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 2 * L / nearRadius c (antiAlignLadder c L R₀ k) ^ 2 := ⟨_, rfl⟩
  rw [← hA]
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hden : 0 < antiAlignLadder c L R₀ k + 1 + A := by linarith
  rw [div_le_iff₀ hden]
  have hAτ : A * nearRadius c (antiAlignLadder c L R₀ k) ^ 2 = 2 * L := by
    rw [hA]; field_simp
  nlinarith [mul_nonneg (show 0 ≤ antiAlignLadder c L R₀ k + 1 by linarith) hτ2.le]

/-- The bands `[τ(R_k)², 2L/R_k)` are pairwise disjoint. -/
theorem antiAlign_bands_disjoint {c L R₀ x : ℝ} (hc : 0 < c) (hL : 0 ≤ L) (hR₀ : 0 < R₀)
    {k k' : ℕ} (hkk' : k < k')
    (h1 : nearRadius c (antiAlignLadder c L R₀ k) ^ 2 ≤ x)
    (h2 : x < 2 * L / antiAlignLadder c L R₀ k') : False := by
  have hmono := antiAlignLadder_mono (c := c) (R₀ := R₀) hL (Nat.succ_le_of_lt hkk')
  have hpos : 0 < antiAlignLadder c L R₀ (k + 1) := hR₀.trans_le (antiAlignLadder_ge hL _)
  have h3 : 2 * L / antiAlignLadder c L R₀ k' ≤ 2 * L / antiAlignLadder c L R₀ (k + 1) :=
    div_le_div_of_nonneg_left (by linarith) hpos hmono
  have h4 := two_mul_div_antiAlignLadder_succ_le hc hL hR₀.le k
  linarith

/-- **Pigeonhole.**  Among `|T| + 1` disjoint bands one contains none of the `|T|` values. -/
theorem exists_antiAlign_rung {ι : Type*} (T : Finset ι) (d : ι → ℝ) {c L R₀ : ℝ} (hc : 0 < c)
    (hL : 0 ≤ L) (hR₀ : 0 < R₀) :
    ∃ k ≤ T.card, ∀ t ∈ T, ¬ (nearRadius c (antiAlignLadder c L R₀ k) ^ 2 ≤ d t ∧
      d t < 2 * L / antiAlignLadder c L R₀ k) := by
  classical
  by_contra hcon
  push Not at hcon
  have hmap : ∀ k ∈ Finset.range (T.card + 1), ∃ t ∈ T,
      nearRadius c (antiAlignLadder c L R₀ k) ^ 2 ≤ d t ∧ d t < 2 * L / antiAlignLadder c L R₀ k :=
    fun k hk => hcon k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  obtain ⟨t₁, ht₁, -⟩ := hmap 0 (by simp)
  haveI : Nonempty ι := ⟨t₁⟩
  choose! f hfT hfband using hmap
  obtain ⟨k, hk, k', hk', hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (T.card + 1)) (t := T) (by simp) (f := f) fun k hk => hfT k hk
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨h1, -⟩ := hfband k hk
    obtain ⟨-, h2⟩ := hfband k' hk'
    rw [heq] at h1
    exact antiAlign_bands_disjoint hc hL hR₀ hlt h1 h2
  · obtain ⟨h1, -⟩ := hfband k' hk'
    obtain ⟨-, h2⟩ := hfband k hk
    rw [← heq] at h1
    exact antiAlign_bands_disjoint hc hL hR₀ hgt h1 h2

/-- The exponent `Y ζ` or `Ȳ ζ`, `Y = R + iπ`. -/
def antiAlignExponent (R : ℝ) (b : Bool) (ζ : ℂ) : ℂ :=
  (if b then (R : ℂ) - (Real.pi : ℂ) * I else (R : ℂ) + (Real.pi : ℂ) * I) * ζ

theorem cexp_antiAlign_base (R : ℝ) (b : Bool) :
    cexp (if b then (R : ℂ) - (Real.pi : ℂ) * I else (R : ℂ) + (Real.pi : ℂ) * I) =
      -((Real.exp R : ℝ) : ℂ) := by
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rw [Complex.exp_add, Complex.exp_pi_mul_I, ← Complex.ofReal_exp]; ring
  · simp only [if_true]
    rw [Complex.exp_sub, Complex.exp_pi_mul_I, ← Complex.ofReal_exp]; field_simp

theorem norm_antiAlign_base_le {R : ℝ} (hR : 0 ≤ R) (b : Bool) :
    ‖(if b then (R : ℂ) - (Real.pi : ℂ) * I else (R : ℂ) + (Real.pi : ℂ) * I)‖ ≤ R + 4 := by
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_le_four
  cases b
  · simp only [Bool.false_eq_true, if_false]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hR, Real.norm_of_nonneg hpi.le]
    linarith
  · simp only [if_true]
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hR, Real.norm_of_nonneg hpi.le]
    linarith

/-- **A near point** is anti-aligned: `Re(w e^{Yζ+e}) ≤ −(Re w) e^R/2`. -/
theorem re_mul_cexp_antiAlign_near_le {w ζ e : ℂ} {c R : ℝ} (b : Bool) (hR : 0 ≤ R)
    (hc1 : c ≤ 1) (hcw : c * ‖w‖ ≤ w.re) (hnear : ‖ζ - 1‖ ≤ nearRadius c R)
    (he : ‖e‖ ≤ c / 8) :
    (w * cexp (antiAlignExponent R b ζ + e)).re ≤ -(w.re * Real.exp R) / 2 := by
  obtain ⟨B, hB⟩ : ∃ B : ℂ, B = if b then (R : ℂ) - (Real.pi : ℂ) * I
      else (R : ℂ) + (Real.pi : ℂ) * I := ⟨_, rfl⟩
  have hBn : ‖B‖ ≤ R + 4 := hB ▸ norm_antiAlign_base_le hR b
  have hexpB : cexp B = -((Real.exp R : ℝ) : ℂ) := hB ▸ cexp_antiAlign_base R b
  obtain ⟨x, hx⟩ : ∃ x : ℂ, x = B * (ζ - 1) + e := ⟨_, rfl⟩
  have hsplit : antiAlignExponent R b ζ + e = B + x := by
    rw [antiAlignExponent, ← hB, hx]; ring
  have hxn : ‖x‖ ≤ c / 4 := by
    rw [hx]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have h1 : ‖B‖ * ‖ζ - 1‖ ≤ (R + 4) * nearRadius c R :=
      mul_le_mul hBn hnear (norm_nonneg _) (by linarith)
    have h2 : (R + 4) * nearRadius c R = c / 8 := by rw [nearRadius]; field_simp
    linarith
  have hx1 : ‖x‖ ≤ 1 := by linarith
  have hge := re_mul_cexp_ge (w := w) hx1
  rw [hsplit, Complex.exp_add, hexpB]
  have e : w * (-((Real.exp R : ℝ) : ℂ) * cexp x) = -((Real.exp R : ℝ) : ℂ) * (w * cexp x) := by
    ring
  rw [e, neg_mul, Complex.neg_re, Complex.re_ofReal_mul]
  have h3 : 2 * ‖w‖ * ‖x‖ ≤ 2 * ‖w‖ * (c / 4) := mul_le_mul_of_nonneg_left hxn (by positivity)
  have h4 : w.re / 2 ≤ (w * cexp x).re := by nlinarith
  have hE := Real.exp_pos R
  nlinarith

/-- **A far point** is small: `‖w e^{Yζ+e}‖ ≤ ‖w‖ e^{R − L + 4}` when `‖ζ‖ ≤ 1`,
`R ‖ζ − 1‖² ≥ 2L` and `‖e‖ ≤ 1/8`. -/
theorem norm_mul_cexp_antiAlign_far_le {w ζ e : ℂ} {R L : ℝ} (b : Bool) (hR : 0 < R)
    (hζ : ‖ζ‖ ≤ 1) (hfar : 2 * L / R ≤ ‖ζ - 1‖ ^ 2) (he : ‖e‖ ≤ 1 / 8) :
    ‖w * cexp (antiAlignExponent R b ζ + e)‖ ≤ ‖w‖ * Real.exp (R - L + 4) := by
  rw [norm_mul, Complex.norm_exp]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  have hre_ζ : ζ.re ≤ 1 - ‖ζ - 1‖ ^ 2 / 2 := by
    have h1 : ‖ζ‖ ^ 2 = ζ.re * ζ.re + ζ.im * ζ.im := by
      rw [Complex.sq_norm, Complex.normSq_apply]
    have h2 : ‖ζ - 1‖ ^ 2 = (ζ.re - 1) * (ζ.re - 1) + ζ.im * ζ.im := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp
    have h3 : ‖ζ‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg ζ]
    nlinarith
  have hRL : R * (‖ζ - 1‖ ^ 2 / 2) ≥ L := by
    rw [div_le_iff₀ hR] at hfar; linarith
  have him : |ζ.im| ≤ 1 := (Complex.abs_im_le_norm ζ).trans hζ
  have he' : e.re ≤ 1 / 8 := (Complex.re_le_norm e).trans he
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_lt_d2
  rw [Complex.add_re, antiAlignExponent]
  have hRre : R * ζ.re ≤ R - L := by
    have := mul_le_mul_of_nonneg_left hre_ζ hR.le
    have e : R * (1 - ‖ζ - 1‖ ^ 2 / 2) = R - R * (‖ζ - 1‖ ^ 2 / 2) := by ring
    linarith
  have him1 : Real.pi * ζ.im ≤ Real.pi := by nlinarith [abs_le.mp him]
  have him2 : -(Real.pi * ζ.im) ≤ Real.pi := by nlinarith [abs_le.mp him]
  cases b
  · simp only [Bool.false_eq_true, if_false]
    have : (((R : ℂ) + (Real.pi : ℂ) * I) * ζ).re = R * ζ.re - Real.pi * ζ.im := by simp
    rw [this]
    linarith
  · simp only [if_true]
    have : (((R : ℂ) - (Real.pi : ℂ) * I) * ζ).re = R * ζ.re + Real.pi * ζ.im := by simp
    rw [this]
    linarith

/-- **Anti-alignment of finitely many points.**  Let `‖ζ_t‖ ≤ 1` on a finite set `T`, and let a
subset `T_g ⊆ T` carry `Re w_t ≥ c ‖w_t‖` (`0 < c ≤ 1`) and one point `ζ_{t₀} = 1`, while the points
outside `T_g` stay at squared distance `≥ 2L/R₀` from `1`.  If `Σ_T ‖w_t‖ ≤ B` and
`B e^{4 − L} ≤ c ‖w_{t₀}‖/4`, then at some rung `R = R_k`, `k ≤ |T_g|`, of the ladder,
`Re Σ_T w_t e^{Y_t ζ_t + e_t} ≤ −c ‖w_{t₀}‖ e^R/4` for all errors `‖e_t‖ ≤ c/8`, with
`Y_t ∈ {R + iπ, R − iπ}` chosen freely per point. -/
theorem exists_multi_antiAligned {ι : Type*} (T Tg : Finset ι) (w ζ : ι → ℂ) (b : ι → Bool)
    {c L R₀ B : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hcw : ∀ t ∈ Tg, c * ‖w t‖ ≤ (w t).re)
    (hζ : ∀ t ∈ T, ‖ζ t‖ ≤ 1) (hfar : ∀ t ∈ T, t ∉ Tg → 2 * L / R₀ ≤ ‖ζ t - 1‖ ^ 2)
    (hR₀ : 0 < R₀) (hL : 0 ≤ L) {t₀ : ι} (ht₀ : t₀ ∈ Tg) (hTg : Tg ⊆ T)
    (hζ₀ : ζ t₀ = 1) (hB : ∑ t ∈ T, ‖w t‖ ≤ B) (hLbig : B * Real.exp (4 - L) ≤ c * ‖w t₀‖ / 4) :
    ∃ k ≤ Tg.card, ∀ e : ι → ℂ, (∀ t ∈ T, ‖e t‖ ≤ c / 8) →
      (∑ t ∈ T, w t * cexp (antiAlignExponent (antiAlignLadder c L R₀ k) (b t) (ζ t) + e t)).re ≤
        -(c * ‖w t₀‖ * Real.exp (antiAlignLadder c L R₀ k)) / 4 := by
  classical
  obtain ⟨k, hk, hband⟩ := exists_antiAlign_rung Tg (fun t => ‖ζ t - 1‖ ^ 2) hc0 hL hR₀
  refine ⟨k, hk, fun e he => ?_⟩
  have hR₀k : R₀ ≤ antiAlignLadder c L R₀ k := antiAlignLadder_ge hL k
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = antiAlignLadder c L R₀ k := ⟨_, rfl⟩
  rw [← hR] at hband hR₀k ⊢
  have hRpos : 0 < R := hR₀.trans_le hR₀k
  have hτ := nearRadius_pos hc0 hRpos.le
  have hLR : 2 * L / R ≤ 2 * L / R₀ := div_le_div_of_nonneg_left (by linarith) hR₀ hR₀k
  -- every point is near (and in `T_g`) or far
  have hsplit : ∀ t ∈ T, (t ∈ Tg ∧ ‖ζ t - 1‖ ≤ nearRadius c R) ∨ 2 * L / R ≤ ‖ζ t - 1‖ ^ 2 := by
    intro t ht
    by_cases htg : t ∈ Tg
    · by_cases hn : nearRadius c R ^ 2 ≤ ‖ζ t - 1‖ ^ 2
      · right
        by_contra hf
        push Not at hf
        exact hband t htg ⟨hn, hf⟩
      · left
        push Not at hn
        exact ⟨htg, (lt_of_pow_lt_pow_left₀ 2 hτ.le hn).le⟩
    · exact Or.inr (hLR.trans (hfar t ht htg))
  have hE := Real.exp_pos R
  have he8 : ∀ t ∈ T, ‖e t‖ ≤ 1 / 8 := fun t ht => (he t ht).trans (by linarith)
  have hbound : ∀ t ∈ T, (w t * cexp (antiAlignExponent R (b t) (ζ t) + e t)).re ≤
      ‖w t‖ * Real.exp (R - L + 4) := by
    intro t ht
    rcases hsplit t ht with ⟨htg, hn⟩ | hf
    · have h1 := re_mul_cexp_antiAlign_near_le (b t) hRpos.le hc1 (hcw t htg) hn (he t ht)
      have h2 : 0 ≤ (w t).re * Real.exp R := mul_nonneg ((mul_nonneg hc0.le (norm_nonneg _)).trans
        (hcw t htg)) hE.le
      have h3 : 0 ≤ ‖w t‖ * Real.exp (R - L + 4) := by positivity
      linarith
    · exact (Complex.re_le_norm _).trans
        (norm_mul_cexp_antiAlign_far_le (b t) hRpos (hζ t ht) hf (he8 t ht))
  have ht₀T : t₀ ∈ T := hTg ht₀
  have hdom : (w t₀ * cexp (antiAlignExponent R (b t₀) (ζ t₀) + e t₀)).re ≤
      -(c * ‖w t₀‖ * Real.exp R) / 2 := by
    have hn : ‖ζ t₀ - 1‖ ≤ nearRadius c R := by rw [hζ₀, sub_self, norm_zero]; exact hτ.le
    have h1 := re_mul_cexp_antiAlign_near_le (b t₀) hRpos.le hc1 (hcw t₀ ht₀) hn (he t₀ ht₀T)
    have h2 := mul_le_mul_of_nonneg_right (hcw t₀ ht₀) hE.le
    linarith
  rw [Complex.re_sum, ← Finset.add_sum_erase T _ ht₀T]
  have hrest : ∑ t ∈ T.erase t₀, (w t * cexp (antiAlignExponent R (b t) (ζ t) + e t)).re ≤
      (∑ t ∈ T, ‖w t‖) * Real.exp (R - L + 4) := by
    calc ∑ t ∈ T.erase t₀, (w t * cexp (antiAlignExponent R (b t) (ζ t) + e t)).re
        ≤ ∑ t ∈ T.erase t₀, ‖w t‖ * Real.exp (R - L + 4) :=
          Finset.sum_le_sum fun t ht => hbound t (Finset.mem_of_mem_erase ht)
      _ ≤ ∑ t ∈ T, ‖w t‖ * Real.exp (R - L + 4) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun t _ _ => by positivity
      _ = (∑ t ∈ T, ‖w t‖) * Real.exp (R - L + 4) := by rw [Finset.sum_mul]
  have hexp : Real.exp (R - L + 4) = Real.exp R * Real.exp (4 - L) := by
    rw [← Real.exp_add]; ring_nf
  have hfin : (∑ t ∈ T, ‖w t‖) * Real.exp (R - L + 4) ≤ c * ‖w t₀‖ * Real.exp R / 4 := by
    rw [hexp]
    have h4 := mul_le_mul_of_nonneg_right hB (mul_pos hE (Real.exp_pos (4 - L))).le
    have h5 := mul_le_mul_of_nonneg_left hLbig hE.le
    nlinarith
  linarith

/-! ## Large and small prime sums of a zero -/

/-- The large prime sum of a zero: `W(σ − (s − ½))` right of the line, `W(σ + (s − ½))` left of
it. -/
def jasBigSum (P : Finset Nat.Primes) (σ : ℝ) (s : ℂ) : ℂ :=
  if 1 / 2 ≤ s.re then jasCpowSum P ((σ : ℂ) - (s - 1 / 2)) else jasCpowSum P ((σ : ℂ) + (s - 1 / 2))

/-- The other prime sum of a zero. -/
def jasSmallSum (P : Finset Nat.Primes) (σ : ℝ) (s : ℂ) : ℂ :=
  if 1 / 2 ≤ s.re then jasCpowSum P ((σ : ℂ) + (s - 1 / 2)) else jasCpowSum P ((σ : ℂ) - (s - 1 / 2))

/-- The small sum has exponents of real part at least `σ`. -/
theorem norm_jasSmallSum_le (P : Finset Nat.Primes) (σ : ℝ) (s : ℂ) :
    ‖jasSmallSum P σ s‖ ≤ ∑ p ∈ P, Real.exp (-σ * Real.log p) := by
  rw [jasSmallSum]
  split_ifs with h
  · refine (norm_jasCpowSum_le P _).trans (Finset.sum_le_sum fun p _ => ?_)
    exact exp_neg_mul_log_prime_anti (by simp; linarith) p
  · refine (norm_jasCpowSum_le P _).trans (Finset.sum_le_sum fun p _ => ?_)
    exact exp_neg_mul_log_prime_anti (by push Not at h; simp; linarith) p

/-- The large sum has exponents of real part `σ − |Re s − ½|`. -/
theorem norm_jasBigSum_le (P : Finset Nat.Primes) (σ : ℝ) (s : ℂ) :
    ‖jasBigSum P σ s‖ ≤ ∑ p ∈ P, Real.exp (-(σ - |s.re - 1 / 2|) * Real.log p) := by
  rw [jasBigSum]
  split_ifs with h
  · have hre : ((σ : ℂ) - (s - 1 / 2)).re = σ - |s.re - 1 / 2| := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ s.re - 1 / 2)]; simp
    refine (norm_jasCpowSum_le P _).trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_))
    rw [hre]
  · push Not at h
    have hre : ((σ : ℂ) + (s - 1 / 2)).re = σ - |s.re - 1 / 2| := by
      rw [abs_of_neg (by linarith : s.re - 1 / 2 < 0)]; simp; ring
    refine (norm_jasCpowSum_le P _).trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_))
    rw [hre]

/-- `Σ_p (u A_p + ū B_p) = c_big · W_big + c_small · W_small`, the big coefficient being `ū` right
of the line and `u` left of it. -/
theorem sum_jasConstFactor_sub_one_big (P : Finset Nat.Primes) (σ : ℝ) (u s : ℂ) :
    ∑ p ∈ P, (jasConstFactor σ u p s - 1) =
      (if 1 / 2 ≤ s.re then conj u else u) * jasBigSum P σ s +
        (if 1 / 2 ≤ s.re then u else conj u) * jasSmallSum P σ s := by
  rw [sum_jasConstFactor_sub_one, jasBigSum, jasSmallSum]
  split_ifs <;> ring

/-! ## One window, all ties at once -/

/-- The amplitude whose kernel carries a given type: `u` or `ū`, according to the side of the
line. -/
def jasTypeAmp (u : ℂ) (b : Bool) (s : ℂ) : ℂ := if b = decide (s.re < 1 / 2) then u else conj u

theorem jasTypeAmp_big_coeff (u : ℂ) (b : Bool) (s : ℂ) :
    (if 1 / 2 ≤ s.re then conj (jasTypeAmp u b s) else jasTypeAmp u b s) =
      if b then u else conj u := by
  rw [jasTypeAmp]
  by_cases hs : 1 / 2 ≤ s.re
  · have : decide (s.re < 1 / 2) = false := decide_eq_false (by linarith)
    rw [this, if_pos hs]
    try (cases b <;> simp)
  · have : decide (s.re < 1 / 2) = true := decide_eq_true (by push Not at hs; linarith)
    rw [this, if_neg hs]

theorem jasTypeAmp_small_coeff_norm (u : ℂ) (b : Bool) (s : ℂ) :
    ‖(if 1 / 2 ≤ s.re then jasTypeAmp u b s else conj (jasTypeAmp u b s))‖ = ‖u‖ := by
  rw [jasTypeAmp]
  split_ifs <;> simp

theorem norm_jasTypeAmp (u : ℂ) (b : Bool) (s : ℂ) : ‖jasTypeAmp u b s‖ = ‖u‖ := by
  rw [jasTypeAmp]; split_ifs <;> simp

/-- The two kernels of a zero are the two types: `K_u + K_ū = Σ_b K_{amp(b)}`. -/
theorem jasConstKernel_add_conj_eq_sum_type (P : Finset Nat.Primes) (σ : ℝ) (u s : ℂ) :
    jasConstKernel P σ u s + jasConstKernel P σ (conj u) s =
      jasConstKernel P σ (jasTypeAmp u false s) s + jasConstKernel P σ (jasTypeAmp u true s) s := by
  rw [jasTypeAmp, jasTypeAmp]
  by_cases hs : s.re < 1 / 2
  · have h1 : decide (s.re < 1 / 2) = true := decide_eq_true hs
    rw [h1]; simp; ring
  · have h1 : decide (s.re < 1 / 2) = false := decide_eq_false hs
    rw [h1]; simp

/-- **The kernel of a zero in anti-alignment form.**  With `z₀ = conj(Y/S)`, `u₀ = z₀/(1 + ‖z₀‖²)`,
`Y = R + iπ` and `ζ = W_big/S` (type `false`) or `W_big/S̄` (type `true`), the kernel of type `b`
is `exp(Y_b ζ + e)` with `‖e‖ ≤ ‖Y‖‖z₀‖² + ‖z₀‖ Σ_P p^{−σ} + Σ_p ‖x_p‖²`. -/
theorem exists_jasConstKernel_type_eq {P : Finset Nat.Primes} {σ R : ℝ} {S s : ℂ} (hS0 : S ≠ 0)
    (b : Bool) (hbigS : ‖jasBigSum P σ s‖ ≤ ‖S‖)
    (h : ∀ p ∈ P, ‖jasConstFactor σ (jasTypeAmp (conj ((R + Real.pi * I) / S) /
      ((1 + ‖conj ((R + Real.pi * I) / S)‖ ^ 2 : ℝ) : ℂ)) b s) p s - 1‖ ≤ 1 / 2) :
    ∃ e : ℂ, ‖e‖ ≤ ‖(R : ℂ) + Real.pi * I‖ * ‖conj (((R : ℂ) + Real.pi * I) / S)‖ ^ 2 +
        ‖conj (((R : ℂ) + Real.pi * I) / S)‖ * ∑ p ∈ P, Real.exp (-σ * Real.log p) +
        ∑ p ∈ P, ‖jasConstFactor σ (jasTypeAmp (conj ((R + Real.pi * I) / S) /
          ((1 + ‖conj ((R + Real.pi * I) / S)‖ ^ 2 : ℝ) : ℂ)) b s) p s - 1‖ ^ 2 ∧
      jasConstKernel P σ (jasTypeAmp (conj ((R + Real.pi * I) / S) /
          ((1 + ‖conj ((R + Real.pi * I) / S)‖ ^ 2 : ℝ) : ℂ)) b s) s =
        cexp (antiAlignExponent R b (if b then jasBigSum P σ s / conj S else jasBigSum P σ s / S)
          + e) := by
  obtain ⟨Y, hY⟩ : ∃ Y : ℂ, Y = (R : ℂ) + Real.pi * I := ⟨_, rfl⟩
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : ℂ, z₀ = conj (Y / S) := ⟨_, rfl⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = 1 + ‖z₀‖ ^ 2 := ⟨_, rfl⟩
  rw [← hY, ← hz₀, ← hc₀] at h ⊢
  have hc₀1 : 1 ≤ c₀ := by rw [hc₀]; nlinarith [norm_nonneg z₀]
  have hc₀c : (c₀ : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0 : ℝ) < c₀).ne'
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : ℂ, u₀ = z₀ / (c₀ : ℂ) := ⟨_, rfl⟩
  rw [← hu₀] at h ⊢
  have hu₀n : ‖u₀‖ ≤ ‖z₀‖ := by
    rw [hu₀, norm_div, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    exact div_le_self (norm_nonneg _) hc₀1
  obtain ⟨R', hR', hK⟩ := exists_jasConstKernel_eq_exp P σ (jasTypeAmp u₀ b s) s h
  rw [sum_jasConstFactor_sub_one_big, jasTypeAmp_big_coeff] at hK
  have hconjS : conj S ≠ 0 := by rwa [map_ne_zero]
  have hYconj : conj Y = (R : ℂ) - Real.pi * I := by
    rw [hY]; simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  -- the big coefficient times the big sum
  have hbig : (if b then u₀ else conj u₀) * jasBigSum P σ s =
      antiAlignExponent R b (if b then jasBigSum P σ s / conj S else jasBigSum P σ s / S) /
        (c₀ : ℂ) := by
    rw [antiAlignExponent]
    cases b
    · simp only [Bool.false_eq_true, if_false]
      rw [hu₀, map_div₀, Complex.conj_ofReal, hz₀, Complex.conj_conj, ← hY]
      field_simp
    · simp only [if_true]
      rw [hu₀, hz₀, map_div₀, ← hYconj]
      field_simp
  obtain ⟨E, hE⟩ : ∃ E : ℂ,
      E = antiAlignExponent R b (if b then jasBigSum P σ s / conj S else jasBigSum P σ s / S) :=
    ⟨_, rfl⟩
  rw [← hE] at hbig ⊢
  refine ⟨E / (c₀ : ℂ) - E + (if 1 / 2 ≤ s.re then jasTypeAmp u₀ b s else
    conj (jasTypeAmp u₀ b s)) * jasSmallSum P σ s + R', ?_, ?_⟩
  · have hSn : 0 < ‖S‖ := norm_pos_iff.mpr hS0
    have hζ : ‖(if b then jasBigSum P σ s / conj S else jasBigSum P σ s / S)‖ ≤ 1 := by
      split_ifs <;> rw [norm_div] <;>
        (try simp only [Complex.norm_conj]) <;> exact (div_le_one hSn).mpr hbigS
    have hYb : ‖(if b then (R : ℂ) - (Real.pi : ℂ) * I else (R : ℂ) + (Real.pi : ℂ) * I)‖ =
        ‖Y‖ := by
      split_ifs
      · rw [← hYconj, Complex.norm_conj]
      · rw [hY]
    have hEn : ‖E‖ ≤ ‖Y‖ := by
      rw [hE, antiAlignExponent, norm_mul, hYb]
      exact mul_le_of_le_one_right (norm_nonneg _) hζ
    have hshrink : ‖E / (c₀ : ℂ) - E‖ ≤ ‖Y‖ * ‖z₀‖ ^ 2 := by
      have e : E / (c₀ : ℂ) - E = -(E * (((c₀ - 1) / c₀ : ℝ) : ℂ)) := by
        push_cast; field_simp; ring
      rw [e, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by
        have : 0 ≤ c₀ - 1 := by linarith
        positivity)]
      have h1 : (c₀ - 1) / c₀ ≤ ‖z₀‖ ^ 2 := by
        rw [show c₀ - 1 = ‖z₀‖ ^ 2 by rw [hc₀]; ring]
        exact div_le_self (by positivity) hc₀1
      exact mul_le_mul hEn h1 (by
        have : 0 ≤ c₀ - 1 := by linarith
        positivity) (norm_nonneg _)
    have hsm : ‖(if 1 / 2 ≤ s.re then jasTypeAmp u₀ b s else conj (jasTypeAmp u₀ b s)) *
        jasSmallSum P σ s‖ ≤ ‖z₀‖ * ∑ p ∈ P, Real.exp (-σ * Real.log p) := by
      rw [norm_mul, jasTypeAmp_small_coeff_norm]
      exact mul_le_mul hu₀n (norm_jasSmallSum_le P σ s) (norm_nonneg _) (norm_nonneg _)
    calc ‖E / (c₀ : ℂ) - E + (if 1 / 2 ≤ s.re then jasTypeAmp u₀ b s else
          conj (jasTypeAmp u₀ b s)) * jasSmallSum P σ s + R'‖
        ≤ ‖E / (c₀ : ℂ) - E‖ + ‖(if 1 / 2 ≤ s.re then jasTypeAmp u₀ b s else
          conj (jasTypeAmp u₀ b s)) * jasSmallSum P σ s‖ + ‖R'‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ _ := by linarith
  · rw [hK, hbig]; ring_nf

/-- Factor bounds on an arbitrary prime set, at distance at most `δ` from the line. -/
theorem jasConst_set_bounds {P : Finset Nat.Primes} {σ δ : ℝ} (hα0 : 0 < σ - δ) (v : ℂ) {s : ℂ}
    (hs : |s.re - 1 / 2| ≤ δ) :
    (∀ p ∈ P, ‖jasConstFactor σ v p s - 1‖ ≤ 2 * ‖v‖) ∧
      ∑ p ∈ P, ‖jasConstFactor σ v p s - 1‖ ≤
        2 * ‖v‖ * ∑ p ∈ P, Real.exp (-(σ - δ) * Real.log p) := by
  have hβ : σ - δ ≤ σ - |s.re - 1 / 2| := by linarith
  refine ⟨fun p _ => (norm_jasConstFactor_sub_one_le σ v p s).trans ?_, ?_⟩
  · have h3 : Real.exp (-(σ - |s.re - 1 / 2|) * Real.log p) ≤ 1 :=
      (exp_neg_mul_log_prime_anti hβ p).trans (exp_neg_mul_log_prime_le_one hα0.le p)
    nlinarith [norm_nonneg v]
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p _ => (norm_jasConstFactor_sub_one_le σ v p s).trans
      (mul_le_mul_of_nonneg_left (exp_neg_mul_log_prime_anti hβ p) (by positivity))

/-- **One window, all ties at once.**  On a finite prime set `P`, let `G ⊆ F` be finite sets of
zeros, the large prime sums on `G` maximized by `q_m ∈ G`, and those on `F \ G` at most `ρ₂ < 1`
times the maximum `S`.  If the amplitude scale `a = (R* + 4)/‖S‖`, with `R*` the rung `2|G|` of the
ladder, is small enough and the zeros outside `F` carry little weight, some constant vector of norm
at most `a` gives a negative symmetrized aggregate on `P`. -/
theorem exists_jasConstPairTerm_tsum_neg {P : Finset Nat.Primes}
    {σ δ c L R₀ Λ₀ wmin a ρ₂ W : ℝ} {F G : Finset XiZeroCopy} {qm : XiZeroCopy} (hGF : G ⊆ F)
    (hqm : qm ∈ G) (hmaxG : ∀ q ∈ G, ‖jasBigSum P σ (q.1 : ℂ)‖ ≤ ‖jasBigSum P σ (qm.1 : ℂ)‖)
    (hcomp : ∀ q ∈ F, q ∉ G → ‖jasBigSum P σ (q.1 : ℂ)‖ ≤ ρ₂ * ‖jasBigSum P σ (qm.1 : ℂ)‖)
    (hρ₂1 : ρ₂ < 1) (hfarR : 2 * L / R₀ ≤ (1 - ρ₂) ^ 2)
    (hS0 : jasBigSum P σ (qm.1 : ℂ) ≠ 0)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ δ) (hα0 : 0 < σ - δ)
    (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hcw : ∀ q ∈ G, c * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤
      (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re)
    (hwmin : ∀ q ∈ G, wmin ≤ ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) (hwmin0 : 0 < wmin)
    (hR₀ : 0 < R₀) (hL : 0 ≤ L)
    (hW : ∑ q ∈ F, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤ W)
    (hLbig : 2 * W * Real.exp (4 - L) ≤ c * wmin / 4)
    (ha : a = (antiAlignLadder c L R₀ (2 * G.card) + 4) / ‖jasBigSum P σ (qm.1 : ℂ)‖)
    (ha1 : 2 * a ≤ 1 / 2)
    (hsq : 2 * a * (2 * a * ∑ p ∈ P, Real.exp (-(σ - δ) * Real.log p)) ≤ c / 24)
    (hsmall : a * ∑ p ∈ P, Real.exp (-σ * Real.log p) ≤ c / 24)
    (hYa : (antiAlignLadder c L R₀ (2 * G.card) + 4) * a ^ 2 ≤ c / 24)
    (hΛ : 2 * a * ∑ p ∈ P, Real.exp (-(σ - δ) * Real.log p) ≤ Λ₀)
    (hFtail : (∑' q : {x // x ∉ F}, ‖1 / ((q.1.1 : ℂ) * (1 - (q.1.1 : ℂ)))‖) *
      (2 * Real.exp Λ₀) ≤ c * wmin * Real.exp R₀ / 8) :
    ∃ z : ℂ, ‖z‖ ≤ a ∧ (∑' q : XiZeroCopy,
      jasConstPairTerm P σ (z / ((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) (q.1 : ℂ)).re < 0 := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : ℂ, S = jasBigSum P σ (qm.1 : ℂ) := ⟨_, rfl⟩
  rw [← hS] at hmaxG hcomp hS0 ha
  have hSn : 0 < ‖S‖ := norm_pos_iff.mpr hS0
  have hmaxF : ∀ q ∈ F, ‖jasBigSum P σ (q.1 : ℂ)‖ ≤ ‖S‖ := by
    intro q hq
    by_cases hqG : q ∈ G
    · exact hmaxG q hqG
    · exact (hcomp q hq hqG).trans (by nlinarith)
  obtain ⟨Rs, hRs⟩ : ∃ Rs : ℝ, Rs = antiAlignLadder c L R₀ (2 * G.card) := ⟨_, rfl⟩
  rw [← hRs] at ha hYa
  -- the points of the anti-alignment lemma
  obtain ⟨T, hT⟩ : ∃ T : Finset (XiZeroCopy × Bool), T = F ×ˢ (Finset.univ : Finset Bool) :=
    ⟨_, rfl⟩
  obtain ⟨Tg, hTg⟩ : ∃ Tg : Finset (XiZeroCopy × Bool),
      Tg = G ×ˢ (Finset.univ : Finset Bool) := ⟨_, rfl⟩
  have hTgcard : Tg.card = 2 * G.card := by rw [hTg, Finset.card_product]; simp [mul_comm]
  have hTgT : Tg ⊆ T := by rw [hTg, hT]; exact Finset.product_subset_product hGF le_rfl
  let wt : XiZeroCopy × Bool → ℂ := fun t => 1 / ((t.1.1 : ℂ) * (1 - (t.1.1 : ℂ)))
  let ζt : XiZeroCopy × Bool → ℂ := fun t =>
    if t.2 then jasBigSum P σ (t.1.1 : ℂ) / conj S else jasBigSum P σ (t.1.1 : ℂ) / S
  have hζtn : ∀ t : XiZeroCopy × Bool, ‖ζt t‖ = ‖jasBigSum P σ (t.1.1 : ℂ)‖ / ‖S‖ := by
    intro t
    simp only [ζt]
    split_ifs <;> simp only [norm_div, Complex.norm_conj]
  have hζt : ∀ t ∈ T, ‖ζt t‖ ≤ 1 := by
    intro t ht
    have htF : t.1 ∈ F := by rw [hT] at ht; exact (Finset.mem_product.mp ht).1
    rw [hζtn]
    exact (div_le_one hSn).mpr (hmaxF t.1 htF)
  have hfar : ∀ t ∈ T, t ∉ Tg → 2 * L / R₀ ≤ ‖ζt t - 1‖ ^ 2 := by
    intro t ht htg
    have htF : t.1 ∈ F := by rw [hT] at ht; exact (Finset.mem_product.mp ht).1
    have htG : t.1 ∉ G := fun h => htg (by rw [hTg]; exact Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩)
    have h1 : ‖ζt t‖ ≤ ρ₂ := by
      rw [hζtn, div_le_iff₀ hSn]; exact hcomp t.1 htF htG
    have h2 : 1 - ρ₂ ≤ ‖ζt t - 1‖ := by
      have := norm_sub_norm_le (1 : ℂ) (ζt t)
      rw [norm_one, norm_sub_rev] at this
      linarith
    have h3 : (1 - ρ₂) ^ 2 ≤ ‖ζt t - 1‖ ^ 2 := pow_le_pow_left₀ (by linarith) h2 2
    linarith
  have hcwt : ∀ t ∈ Tg, c * ‖wt t‖ ≤ (wt t).re := by
    intro t ht
    have htG : t.1 ∈ G := by rw [hTg] at ht; exact (Finset.mem_product.mp ht).1
    exact hcw t.1 htG
  have ht₀ : (qm, false) ∈ Tg := by
    rw [hTg]; exact Finset.mem_product.mpr ⟨hqm, Finset.mem_univ _⟩
  have hζ₀ : ζt (qm, false) = 1 := by
    simp only [ζt, Bool.false_eq_true, if_false]; rw [hS]; exact div_self (hS ▸ hS0)
  have hsumT : ∑ t ∈ T, ‖wt t‖ ≤ 2 * W := by
    have e : ∑ t ∈ T, ‖wt t‖ = 2 * ∑ q ∈ F, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by
      rw [hT, Finset.sum_product, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Fintype.sum_bool]
      simp only [wt]
      ring
    rw [e]; linarith
  have hLbig' : 2 * W * Real.exp (4 - L) ≤ c * ‖wt (qm, false)‖ / 4 := by
    have := hwmin qm hqm
    have h2 : c * wmin / 4 ≤ c * ‖wt (qm, false)‖ / 4 := by
      have := mul_le_mul_of_nonneg_left this hc0.le
      simp only [wt]; linarith
    linarith
  obtain ⟨k, hk, hanti⟩ := exists_multi_antiAligned T Tg wt ζt (fun t => t.2) hc0 hc1 hcwt hζt
    hfar hR₀ hL ht₀ hTgT hζ₀ hsumT hLbig'
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = antiAlignLadder c L R₀ k := ⟨_, rfl⟩
  rw [← hR] at hanti
  have hRRs : R ≤ Rs := by
    rw [hR, hRs]; exact antiAlignLadder_mono hL (hTgcard ▸ hk)
  have hR0 : 0 ≤ R := by rw [hR]; exact hR₀.le.trans (antiAlignLadder_ge hL k)
  -- the constant vector
  obtain ⟨Y, hY⟩ : ∃ Y : ℂ, Y = (R : ℂ) + Real.pi * I := ⟨_, rfl⟩
  have hYn : ‖Y‖ ≤ Rs + 4 := by
    rw [hY]; exact (norm_antiAlign_base_le hR0 false).trans (by linarith)
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : ℂ, z₀ = conj (Y / S) := ⟨_, rfl⟩
  have hz₀n : ‖z₀‖ ≤ a := by
    rw [hz₀, Complex.norm_conj, norm_div, ha]
    exact div_le_div_of_nonneg_right hYn hSn.le
  have ha0 : 0 ≤ a := (norm_nonneg _).trans hz₀n
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : ℂ, u₀ = z₀ / ((1 + ‖z₀‖ ^ 2 : ℝ) : ℂ) := ⟨_, rfl⟩
  have hu₀n : ‖u₀‖ ≤ a := by
    refine le_trans ?_ hz₀n
    rw [hu₀, norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact div_le_self (norm_nonneg _) (by nlinarith [norm_nonneg z₀])
  refine ⟨z₀, hz₀n, ?_⟩
  rw [← hu₀]
  -- bounds for every zero and every amplitude of norm at most `a`
  have hU : ∀ v : ℂ, ‖v‖ ≤ a → ∀ q : XiZeroCopy,
      (∀ p ∈ P, ‖jasConstFactor σ v p (q.1 : ℂ) - 1‖ ≤ 1 / 2) ∧
        ∑ p ∈ P, ‖jasConstFactor σ v p (q.1 : ℂ) - 1‖ ^ 2 ≤ c / 24 ∧
        ‖jasConstKernel P σ v (q.1 : ℂ)‖ ≤ Real.exp Λ₀ := by
    intro v hv q
    obtain ⟨hb1, hb2⟩ := jasConst_set_bounds (P := P) hα0 v (hmax q)
    have hsum0 : 0 ≤ ∑ p ∈ P, Real.exp (-(σ - δ) * Real.log p) :=
      Finset.sum_nonneg fun p _ => (Real.exp_pos _).le
    have hfac : ∀ p ∈ P, ‖jasConstFactor σ v p (q.1 : ℂ) - 1‖ ≤ 2 * a := fun p hp =>
      (hb1 p hp).trans (by linarith)
    have hsum : ∑ p ∈ P, ‖jasConstFactor σ v p (q.1 : ℂ) - 1‖ ≤
        2 * a * ∑ p ∈ P, Real.exp (-(σ - δ) * Real.log p) :=
      hb2.trans (mul_le_mul_of_nonneg_right (by linarith) hsum0)
    refine ⟨fun p hp => (hfac p hp).trans ha1, ?_, ?_⟩
    · refine (sum_sq_le_of_le P _ (fun p _ => norm_nonneg _) hfac).trans ?_
      exact (mul_le_mul_of_nonneg_left hsum (by linarith)).trans hsq
    · exact (norm_jasConstKernel_le_exp P σ v _).trans (Real.exp_le_exp.mpr (hsum.trans hΛ))
  -- the errors of the typed kernels on `F`
  have herr : ∀ t : XiZeroCopy × Bool, ∃ e : ℂ, t ∈ T →
      ‖e‖ ≤ c / 8 ∧ jasConstKernel P σ (jasTypeAmp u₀ t.2 (t.1.1 : ℂ)) (t.1.1 : ℂ) =
        cexp (antiAlignExponent R t.2 (ζt t) + e) := by
    intro t
    by_cases ht : t ∈ T
    · have htF : t.1 ∈ F := by rw [hT] at ht; exact (Finset.mem_product.mp ht).1
      have hampn : ‖jasTypeAmp u₀ t.2 (t.1.1 : ℂ)‖ ≤ a := by rw [norm_jasTypeAmp]; exact hu₀n
      obtain ⟨hf1, hf2, -⟩ := hU _ hampn t.1
      have hf1' := hf1
      rw [hu₀, hz₀, hY] at hf1'
      obtain ⟨e, he, hK⟩ := exists_jasConstKernel_type_eq (R := R) hS0 t.2 (hmaxF t.1 htF) hf1'
      refine ⟨e, fun _ => ⟨?_, ?_⟩⟩
      · rw [← hY, ← hz₀, ← hu₀] at he
        have h1 : ‖Y‖ * ‖z₀‖ ^ 2 ≤ (Rs + 4) * a ^ 2 :=
          mul_le_mul hYn (pow_le_pow_left₀ (norm_nonneg _) hz₀n 2) (by positivity) (by linarith)
        have h2 : ‖z₀‖ * ∑ p ∈ P, Real.exp (-σ * Real.log p) ≤
            a * ∑ p ∈ P, Real.exp (-σ * Real.log p) :=
          mul_le_mul_of_nonneg_right hz₀n (Finset.sum_nonneg fun p _ => (Real.exp_pos _).le)
        linarith
      · rw [← hY, ← hz₀, ← hu₀] at hK
        rw [hK]
    · exact ⟨0, fun h => absurd h ht⟩
  choose e he using herr
  -- the sum over `F`
  have hFsum : (∑ q ∈ F, jasConstPairTerm P σ u₀ (q.1 : ℂ)) =
      ∑ t ∈ T, wt t * cexp (antiAlignExponent R t.2 (ζt t) + e t) := by
    rw [hT, Finset.sum_product]
    refine Finset.sum_congr rfl fun q hq => ?_
    have htF : ∀ b : Bool, (q, b) ∈ T := fun b => by
      rw [hT]; exact Finset.mem_product.mpr ⟨hq, Finset.mem_univ _⟩
    rw [jasConstPairTerm, jasConstKernel_add_conj_eq_sum_type, Fintype.sum_bool,
      ← (he (q, true) (htF true)).2, ← (he (q, false) (htF false)).2]
    simp only [wt]
    ring
  have hFre : (∑ q ∈ F, jasConstPairTerm P σ u₀ (q.1 : ℂ)).re ≤
      -(c * wmin * Real.exp R₀) / 4 := by
    rw [hFsum]
    have h1 := hanti e fun t ht => (he t ht).1
    have h2 : c * wmin * Real.exp R₀ ≤ c * ‖wt (qm, false)‖ * Real.exp R := by
      have h3 := hwmin qm hqm
      have hRge : R₀ ≤ R := by rw [hR]; exact antiAlignLadder_ge hL k
      have h4 : Real.exp R₀ ≤ Real.exp R := Real.exp_le_exp.mpr hRge
      have h5 : c * wmin ≤ c * ‖wt (qm, false)‖ := mul_le_mul_of_nonneg_left h3 hc0.le
      exact mul_le_mul h5 h4 (Real.exp_pos _).le (by positivity)
    linarith
  -- the tail
  have hwsum : Summable fun q : XiZeroCopy => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ :=
    summable_inv_mul_one_sub.norm
  have hall : ∀ q : XiZeroCopy, ‖jasConstPairTerm P σ u₀ (q.1 : ℂ)‖ ≤
      2 * Real.exp Λ₀ * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := fun q =>
    norm_jasConstPairTerm_le P σ u₀ _ (hU u₀ hu₀n q).2.2
      (hU (conj u₀) (by rw [Complex.norm_conj]; exact hu₀n) q).2.2
  have hsumm := summable_jasConstPairTerm P σ u₀
  have htail : ‖∑' q : {x // x ∉ F}, jasConstPairTerm P σ u₀ (q.1.1 : ℂ)‖ ≤
      c * wmin * Real.exp R₀ / 8 := by
    have hs1 : Summable (fun q : {x // x ∉ F} => ‖jasConstPairTerm P σ u₀ (q.1.1 : ℂ)‖) :=
      hsumm.norm.subtype _
    have hs2 : Summable (fun q : {x // x ∉ F} =>
        2 * Real.exp Λ₀ * ‖1 / ((q.1.1 : ℂ) * (1 - (q.1.1 : ℂ)))‖) :=
      (hwsum.mul_left _).subtype _
    calc ‖∑' q : {x // x ∉ F}, jasConstPairTerm P σ u₀ (q.1.1 : ℂ)‖
        ≤ ∑' q : {x // x ∉ F}, ‖jasConstPairTerm P σ u₀ (q.1.1 : ℂ)‖ := norm_tsum_le_tsum_norm hs1
      _ ≤ ∑' q : {x // x ∉ F}, 2 * Real.exp Λ₀ * ‖1 / ((q.1.1 : ℂ) * (1 - (q.1.1 : ℂ)))‖ :=
          Summable.tsum_le_tsum (fun q => hall q.1) hs1 hs2
      _ = (∑' q : {x // x ∉ F}, ‖1 / ((q.1.1 : ℂ) * (1 - (q.1.1 : ℂ)))‖) *
          (2 * Real.exp Λ₀) := by rw [tsum_mul_left, mul_comm]
      _ ≤ c * wmin * Real.exp R₀ / 8 := hFtail
  rw [← hsumm.sum_add_tsum_subtype_compl F, Complex.add_re]
  have := Complex.re_le_norm (∑' q : {x // x ∉ F}, jasConstPairTerm P σ u₀ (q.1.1 : ℂ))
  have hpos : 0 < c * wmin * Real.exp R₀ := by positivity
  linarith

end

end RHTower
