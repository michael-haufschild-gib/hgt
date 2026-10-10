import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic

/-!
# Trace decay for diagonally dominant elliptic collar systems

A family of complex radial modes `u n`, `n ∈ ℤ`, on a collar `[-δ,δ]` with a
`C¹` transmission point at `0`, satisfying the nearest-neighbour coupled system

  `ü n = a n · u n + bm n · u (n-1) + bp n · u (n+1)`

with `Re a n ≥ κ n²` and `‖bm n‖ + ‖bp n‖ ≤ θ κ n²`, `θ ≤ 1/3`, at high grade, and
polynomially bounded uniformly on the collar, has interface values decaying
faster than every power of `n`.

The mechanism is a one-dimensional maximum principle for `‖u n‖²` across the
transmission point, compared with a `cosh` barrier. One barrier step halves the
bound on a subcollar of depth `log 16 / κ|n|`; iterating `⌊|n|/s⌋` steps costs one
grade of support per step, which the polynomial bound absorbs, and gives the
factor `2^{-⌊|n|/s⌋}`.
-/

open Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- One-dimensional maximum principle across a `C¹` transmission point.
If `g` is continuous on `[-d,d]`, has a continuous derivative inside, and its
derivative has positive derivative away from `0` wherever `g` is positive,
then `g` is bounded by its endpoint values and `0`. -/
theorem le_max_endpoints_of_pos_deriv2
    {d : ℝ} {g g' g'' : ℝ → ℝ}
    (hg : ContinuousOn g (Icc (-d) d))
    (hg' : ∀ t ∈ Ioo (-d) d, HasDerivAt g (g' t) t)
    (hg'c : ContinuousOn g' (Ioo (-d) d))
    (hg'' : ∀ t ∈ Ioo (-d) d, t ≠ 0 → HasDerivAt g' (g'' t) t)
    (hpos : ∀ t ∈ Ioo (-d) d, t ≠ 0 → 0 < g t → 0 < g'' t) :
    ∀ t ∈ Icc (-d) d, g t ≤ max (max (g (-d)) (g d)) 0 := by
  intro t₀ ht₀
  by_contra hcon'
  have hcon := not_le.mp hcon'
  obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨t₀, ht₀⟩ hg
  have hc0 : max (max (g (-d)) (g d)) 0 < g c := lt_of_lt_of_le hcon (hmax ht₀)
  have hgc : 0 < g c := lt_of_le_of_lt (le_max_right _ _) hc0
  have hcl : c ≠ -d := by
    rintro rfl
    exact absurd hc0 (not_lt.mpr ((le_max_left _ _).trans (le_max_left _ _)))
  have hcr : c ≠ d := by
    rintro rfl
    exact absurd hc0 (not_lt.mpr ((le_max_right _ _).trans (le_max_left _ _)))
  have hcI : c ∈ Ioo (-d) d :=
    ⟨lt_of_le_of_ne hc.1 (Ne.symm hcl), lt_of_le_of_ne hc.2 hcr⟩
  have hlocal : IsLocalMax g c := hmax.isLocalMax (Icc_mem_nhds hcI.1 hcI.2)
  have hg'0 : g' c = 0 := hlocal.hasDerivAt_eq_zero (hg' c hcI)
  have hev : ∀ᶠ s in 𝓝[>] c, s ∈ Ioo (-d) d ∧ s ≠ 0 ∧ 0 < g s := by
    have h1 : ∀ᶠ s in 𝓝[>] c, s ∈ Ioo (-d) d :=
      nhdsWithin_le_nhds (Ioo_mem_nhds hcI.1 hcI.2)
    have h2 : ∀ᶠ s in 𝓝[>] c, 0 < g s :=
      nhdsWithin_le_nhds ((hg' c hcI).continuousAt.eventually (lt_mem_nhds hgc))
    have h3 : ∀ᶠ s in 𝓝[>] c, s ≠ 0 := by
      rcases lt_or_ge c 0 with h | h
      · have h0 : ∀ᶠ s in 𝓝[>] c, s < 0 := nhdsWithin_le_nhds (gt_mem_nhds h)
        exact h0.mono fun s hs => hs.ne
      · exact eventually_nhdsWithin_of_forall fun s hs =>
          (lt_of_le_of_lt h (show c < s from hs)).ne'
    exact h1.and (h3.and h2)
  obtain ⟨e, hce', hS⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hce : c < e := hce'
  set b := (c + e) / 2 with hb
  have hcb : c < b := by rw [hb]; linarith [hce]
  have hbe : b < e := by rw [hb]; linarith [hce]
  have hsub : Icc c b ⊆ Ioo (-d) d := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · exact h ▸ hcI
    · exact (hS ⟨h, lt_of_le_of_lt hx.2 hbe⟩).1
  have hsub' : Icc c b ⊆ Icc (-d) d := fun x hx => Ioo_subset_Icc_self (hsub hx)
  have hmono' : StrictMonoOn g' (Icc c b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc c b) (hg'c.mono hsub)
    intro x hx
    rw [interior_Icc] at hx
    obtain ⟨hxI, hx0, hgx⟩ := hS ⟨hx.1, hx.2.trans hbe⟩
    rw [(hg'' x hxI hx0).deriv]
    exact hpos x hxI hx0 hgx
  have hmono : StrictMonoOn g (Icc c b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc c b) (hg.mono hsub')
    intro x hx
    rw [interior_Icc] at hx
    have hxI : x ∈ Ioo (-d) d := hsub (Ioo_subset_Icc_self hx)
    rw [(hg' x hxI).deriv]
    have := hmono' (left_mem_Icc.mpr hcb.le) (Ioo_subset_Icc_self hx) hx.1
    rw [hg'0] at this
    exact this
  have hlt : g c < g b := hmono (left_mem_Icc.mpr hcb.le) (right_mem_Icc.mpr hcb.le) hcb
  have hle : g b ≤ g c := hmax (hsub' (right_mem_Icc.mpr hcb.le))
  exact absurd hlt (not_lt.mpr hle)

/-- `cosh(κt)/cosh(κd)` is exponentially small at distance `Δ` inside the collar. -/
theorem cosh_div_cosh_le_two_exp {κ t d Δ : ℝ} (hκ : 0 ≤ κ) (ht : |t| ≤ d - Δ) :
    Real.cosh (κ * t) / Real.cosh (κ * d) ≤ 2 * Real.exp (-(κ * Δ)) := by
  have hcpos : 0 < Real.cosh (κ * d) := Real.cosh_pos _
  have hnum : Real.cosh (κ * t) ≤ Real.exp (κ * (d - Δ)) := by
    rw [Real.cosh_eq]
    have h1 : κ * t ≤ κ * (d - Δ) :=
      mul_le_mul_of_nonneg_left ((le_abs_self t).trans ht) hκ
    have h2 : -(κ * t) ≤ κ * (d - Δ) := by
      have : -t ≤ d - Δ := (neg_le_abs t).trans ht
      nlinarith [mul_le_mul_of_nonneg_left this hκ]
    have e1 := Real.exp_le_exp.mpr h1
    have e2 := Real.exp_le_exp.mpr h2
    linarith
  have hden : Real.exp (κ * d) / 2 ≤ Real.cosh (κ * d) := by
    rw [Real.cosh_eq]
    have := Real.exp_pos (-(κ * d))
    linarith
  rw [div_le_iff₀ hcpos]
  calc Real.cosh (κ * t) ≤ Real.exp (κ * (d - Δ)) := hnum
    _ = 2 * Real.exp (-(κ * Δ)) * (Real.exp (κ * d) / 2) := by
      rw [show κ * (d - Δ) = -(κ * Δ) + κ * d by ring, Real.exp_add]
      ring
    _ ≤ 2 * Real.exp (-(κ * Δ)) * Real.cosh (κ * d) :=
      mul_le_mul_of_nonneg_left hden (by positivity)

private theorem two_mul_le_young {κ X Y F : ℝ} (hκ : 0 < κ) (hY0 : 0 ≤ Y) (hYF : Y ≤ F) :
    2 * (X * Y) ≤ κ ^ 2 * X ^ 2 + F ^ 2 / κ ^ 2 := by
  have hκ2 : 0 < κ ^ 2 := by positivity
  have hYF2 : Y ^ 2 ≤ F ^ 2 := pow_le_pow_left₀ hY0 hYF 2
  rw [← sub_nonneg]
  have key : κ ^ 2 * X ^ 2 + F ^ 2 / κ ^ 2 - 2 * (X * Y) =
      ((κ ^ 2 * X - Y) ^ 2 + (F ^ 2 - Y ^ 2)) / κ ^ 2 := by
    field_simp
    ring
  rw [key]
  apply div_nonneg _ hκ2.le
  nlinarith [sq_nonneg (κ ^ 2 * X - Y)]

/-- Barrier estimate for one complex mode of a strongly elliptic collar equation
with a `C¹` transmission point at `0`: the squared modulus stays below the
`cosh` barrier fixed by the endpoint values plus the forcing level. -/
theorem normSq_le_coshBarrier
    {d κ F B : ℝ} (hκ : 0 < κ) {u u' u'' a f : ℝ → ℂ}
    (hu : ∀ t ∈ Icc (-d) d, HasDerivAt u (u' t) t)
    (hu'c : ContinuousOn u' (Icc (-d) d))
    (hu'' : ∀ t ∈ Ioo (-d) d, t ≠ 0 → HasDerivAt u' (u'' t) t)
    (heq : ∀ t ∈ Ioo (-d) d, t ≠ 0 → u'' t = a t * u t + f t)
    (ha : ∀ t ∈ Ioo (-d) d, t ≠ 0 → κ ^ 2 ≤ (a t).re)
    (hf : ∀ t ∈ Ioo (-d) d, t ≠ 0 → ‖f t‖ ≤ F)
    (hBl : ‖u (-d)‖ ≤ B) (hBr : ‖u d‖ ≤ B) :
    ∀ t ∈ Icc (-d) d,
      ‖u t‖ ^ 2 ≤ B ^ 2 * (Real.cosh (κ * t) / Real.cosh (κ * d)) + F ^ 2 / κ ^ 4 := by
  set c : ℝ := Real.cosh (κ * d) with hc
  have hcpos : 0 < c := Real.cosh_pos _
  have hlin : ∀ t, HasDerivAt (fun t : ℝ => κ * t) κ t := fun t => by
    simpa using (hasDerivAt_id t).const_mul κ
  set W : ℝ → ℝ := fun t => B ^ 2 * (Real.cosh (κ * t) / c) + F ^ 2 / κ ^ 4 with hWdef
  set W' : ℝ → ℝ := fun t => B ^ 2 * (Real.sinh (κ * t) * κ / c) with hW'def
  set W'' : ℝ → ℝ := fun t => B ^ 2 * (Real.cosh (κ * t) * κ * κ / c) with hW''def
  have hW : ∀ t, HasDerivAt W (W' t) t := fun t =>
    ((((Real.hasDerivAt_cosh (κ * t)).comp t (hlin t)).div_const c).const_mul (B ^ 2)).add_const _
  have hW' : ∀ t, HasDerivAt W' (W'' t) t := fun t =>
    ((((Real.hasDerivAt_sinh (κ * t)).comp t (hlin t)).mul_const κ).div_const c).const_mul (B ^ 2)
  set g : ℝ → ℝ := fun t => ‖u t‖ ^ 2 - W t with hgdef
  set g' : ℝ → ℝ := fun t => 2 * inner ℝ (u t) (u' t) - W' t with hg'def
  set g'' : ℝ → ℝ := fun t =>
    2 * (inner ℝ (u t) (u'' t) + inner ℝ (u' t) (u' t)) - W'' t with hg''def
  have hIoo : ∀ t ∈ Ioo (-d) d, t ∈ Icc (-d) d := fun t ht => Ioo_subset_Icc_self ht
  have hucont : ContinuousOn u (Icc (-d) d) := fun t ht =>
    (hu t ht).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Icc (-d) d) := by
    apply ContinuousOn.sub
    · exact (hucont.norm).pow 2
    · exact fun t _ => (hW t).continuousAt.continuousWithinAt
  have hg' : ∀ t ∈ Ioo (-d) d, HasDerivAt g (g' t) t := fun t ht =>
    ((hu t (hIoo t ht)).norm_sq).sub (hW t)
  have hg'c : ContinuousOn g' (Ioo (-d) d) := by
    apply ContinuousOn.sub
    · exact (continuousOn_const.mul ((hucont.mono fun t ht => hIoo t ht).inner
        (hu'c.mono fun t ht => hIoo t ht)))
    · exact fun t _ => (hW' t).continuousAt.continuousWithinAt
  have hg'' : ∀ t ∈ Ioo (-d) d, t ≠ 0 → HasDerivAt g' (g'' t) t := fun t ht ht0 =>
    ((((hu t (hIoo t ht)).inner ℝ (hu'' t ht ht0)).const_mul 2)).sub (hW' t)
  have hpos : ∀ t ∈ Ioo (-d) d, t ≠ 0 → 0 < g t → 0 < g'' t := by
    intro t ht ht0 hgt
    set X := ‖u t‖
    set Y := ‖f t‖
    set A := (a t).re
    set r := Real.cosh (κ * t) / c
    have hX0 : 0 ≤ X := norm_nonneg _
    have hY0 : 0 ≤ Y := norm_nonneg _
    have hA : κ ^ 2 ≤ A := ha t ht ht0
    have hYF : Y ≤ F := hf t ht ht0
    have hinner : inner ℝ (u t) (u'' t) =
        A * X ^ 2 + (f t * (starRingEnd ℂ) (u t)).re := by
      rw [Complex.inner, heq t ht ht0, add_mul, Complex.add_re, mul_assoc,
        Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, A, X]
    have hR : -(X * Y) ≤ (f t * (starRingEnd ℂ) (u t)).re := by
      have h1 := Complex.abs_re_le_norm (f t * (starRingEnd ℂ) (u t))
      rw [norm_mul, Complex.norm_conj] at h1
      have h2 := neg_abs_le (f t * (starRingEnd ℂ) (u t)).re
      nlinarith
    have hP : 0 ≤ inner ℝ (u' t) (u' t) := real_inner_self_nonneg
    have hW''t : W'' t = κ ^ 2 * (B ^ 2 * r) := by
      simp only [hW''def, r]; ring
    have hgt' : 0 < X ^ 2 - (B ^ 2 * r + F ^ 2 / κ ^ 4) := hgt
    have hyoung := two_mul_le_young (X := X) hκ hY0 hYF
    have hκ2 : 0 < κ ^ 2 := by positivity
    have hF4 : F ^ 2 / κ ^ 4 * κ ^ 2 = F ^ 2 / κ ^ 2 := by
      field_simp
    have hAX : κ ^ 2 * X ^ 2 ≤ A * X ^ 2 := mul_le_mul_of_nonneg_right hA (sq_nonneg X)
    show 0 < 2 * (inner ℝ (u t) (u'' t) + inner ℝ (u' t) (u' t)) - W'' t
    rw [hinner, hW''t]
    have hmain : κ ^ 2 * (X ^ 2 - (B ^ 2 * r + F ^ 2 / κ ^ 4)) ≤
        2 * (A * X ^ 2 + (f t * (starRingEnd ℂ) (u t)).re + inner ℝ (u' t) (u' t)) -
          κ ^ 2 * (B ^ 2 * r) := by
      nlinarith
    exact lt_of_lt_of_le (mul_pos hκ2 hgt') hmain
  have hmax := le_max_endpoints_of_pos_deriv2 hgc hg' hg'c hg'' hpos
  have hend : ∀ x, ‖u x‖ ≤ B → (x = -d ∨ x = d) → g x ≤ 0 := by
    intro x hx hxd
    have hcx : Real.cosh (κ * x) = c := by
      rcases hxd with rfl | rfl
      · rw [mul_neg, Real.cosh_neg]
      · rfl
    have hsq : ‖u x‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
    have hF : 0 ≤ F ^ 2 / κ ^ 4 := by positivity
    show ‖u x‖ ^ 2 - (B ^ 2 * (Real.cosh (κ * x) / c) + F ^ 2 / κ ^ 4) ≤ 0
    rw [hcx, div_self hcpos.ne', mul_one]
    linarith
  intro t ht
  have h := hmax t ht
  have hle : max (max (g (-d)) (g d)) 0 ≤ 0 :=
    max_le (max_le (hend _ hBl (Or.inl rfl)) (hend _ hBr (Or.inr rfl))) le_rfl
  have : g t ≤ 0 := h.trans hle
  simp only [hgdef, hWdef] at this
  linarith

/-- Contraction step: one strongly elliptic mode whose forcing is at most
`θκ²B` with `θ ≤ 1/3`, and whose endpoint values are at most `B`, is at most
`B/2` on the subcollar at depth `Δ` once `κΔ ≥ log 16`. -/
theorem norm_le_half_of_coshBarrier
    {d κ θ B Δ : ℝ} (hκ : 0 < κ) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 3) (hB0 : 0 ≤ B)
    (hΔ : Real.log 16 ≤ κ * Δ) {u u' u'' a f : ℝ → ℂ}
    (hu : ∀ t ∈ Icc (-d) d, HasDerivAt u (u' t) t)
    (hu'c : ContinuousOn u' (Icc (-d) d))
    (hu'' : ∀ t ∈ Ioo (-d) d, t ≠ 0 → HasDerivAt u' (u'' t) t)
    (heq : ∀ t ∈ Ioo (-d) d, t ≠ 0 → u'' t = a t * u t + f t)
    (ha : ∀ t ∈ Ioo (-d) d, t ≠ 0 → κ ^ 2 ≤ (a t).re)
    (hf : ∀ t ∈ Ioo (-d) d, t ≠ 0 → ‖f t‖ ≤ θ * κ ^ 2 * B)
    (hBl : ‖u (-d)‖ ≤ B) (hBr : ‖u d‖ ≤ B) :
    ∀ t, |t| ≤ d - Δ → ‖u t‖ ≤ B / 2 := by
  intro t ht
  have hlog : 0 < Real.log 16 := Real.log_pos (by norm_num)
  have hΔ0 : 0 ≤ Δ := by
    by_contra h
    have : κ * Δ < 0 := mul_neg_of_pos_of_neg hκ (lt_of_not_ge h)
    linarith
  have htI : t ∈ Icc (-d) d := abs_le.mp (ht.trans (by linarith))
  have hbar := normSq_le_coshBarrier hκ hu hu'c hu'' heq ha hf hBl hBr t htI
  have hcosh := cosh_div_cosh_le_two_exp (κ := κ) (t := t) (d := d) (Δ := Δ) hκ.le ht
  have hexp : Real.exp (-(κ * Δ)) ≤ 1 / 16 := by
    calc Real.exp (-(κ * Δ)) ≤ Real.exp (-Real.log 16) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / 16 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hκ4 : 0 < κ ^ 4 := by positivity
  have hFterm : (θ * κ ^ 2 * B) ^ 2 / κ ^ 4 = θ ^ 2 * B ^ 2 := by
    field_simp
  have hθ2 : θ ^ 2 ≤ 1 / 9 := by nlinarith
  have hB2 : 0 ≤ B ^ 2 := sq_nonneg B
  have hsq : ‖u t‖ ^ 2 ≤ (B / 2) ^ 2 := by
    rw [hFterm] at hbar
    have h1 : B ^ 2 * (Real.cosh (κ * t) / Real.cosh (κ * d)) ≤ B ^ 2 * (2 * (1 / 16)) :=
      mul_le_mul_of_nonneg_left (hcosh.trans (by linarith)) hB2
    have h2 : θ ^ 2 * B ^ 2 ≤ 1 / 9 * B ^ 2 := mul_le_mul_of_nonneg_right hθ2 hB2
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp hsq

/-- **Trace decay for a diagonally dominant elliptic collar system.**
Modes `u n` of a coupled second-order system on `[-δ,δ]` with a `C¹`
transmission point at `0`, uniformly strongly elliptic at high grade
(`Re a n ≥ κsq n²`) with nearest-neighbour coupling at most `θ κsq n²`,
`θ ≤ 1/3`, and polynomially bounded on the whole collar, have interface values
bounded by `C (1 + 2|n|)^N 2^{-⌊|n|/s⌋}`. The proof contracts the barrier
estimate `⌊|n|/s⌋` times on shrinking subcollars; each step loses one grade of
support, which the polynomial bound absorbs. -/
theorem dominantCollar_trace_le
    {δ κsq θ C : ℝ} {N n₀ s : ℕ} (hδ : 0 < δ) (hκ : 0 < κsq) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 3)
    (hs2 : 2 ≤ s) (hs : 8 * Real.log 16 ≤ Real.sqrt κsq * δ * s)
    {u u' u'' a bm bp : ℤ → ℝ → ℂ}
    (hu : ∀ n, ∀ t ∈ Icc (-δ) δ, HasDerivAt (u n) (u' n t) t)
    (hu'c : ∀ n, ContinuousOn (u' n) (Icc (-δ) δ))
    (hu'' : ∀ n, ∀ t ∈ Ioo (-δ) δ, t ≠ 0 → HasDerivAt (u' n) (u'' n t) t)
    (heq : ∀ n, ∀ t ∈ Ioo (-δ) δ, t ≠ 0 →
      u'' n t = a n t * u n t + (bm n t * u (n - 1) t + bp n t * u (n + 1) t))
    (ha : ∀ n : ℤ, (n₀ : ℝ) ≤ |(n : ℝ)| → ∀ t ∈ Ioo (-δ) δ, t ≠ 0 →
      κsq * (n : ℝ) ^ 2 ≤ (a n t).re)
    (hb : ∀ n : ℤ, (n₀ : ℝ) ≤ |(n : ℝ)| → ∀ t ∈ Ioo (-δ) δ, t ≠ 0 →
      ‖bm n t‖ + ‖bp n t‖ ≤ θ * κsq * (n : ℝ) ^ 2)
    (hpoly : ∀ n, ∀ t ∈ Icc (-δ) δ, ‖u n t‖ ≤ C * (1 + |(n : ℝ)|) ^ N)
    (n : ℤ) (hn : 2 * (n₀ : ℝ) + 2 ≤ |(n : ℝ)|) :
    ‖u n 0‖ ≤ C * (1 + 2 * |(n : ℝ)|) ^ N * (1 / 2) ^ (n.natAbs / s) := by
  have hcastAbs : ∀ z : ℤ, ((z.natAbs : ℕ) : ℝ) = |(z : ℝ)| := fun z => by
    rw [Nat.cast_natAbs, Int.cast_abs]
  set L : ℕ := n.natAbs with hLdef
  have hL : |(n : ℝ)| = (L : ℝ) := (hcastAbs n).symm
  set K : ℕ := L / s with hKdef
  have hKs : K * s ≤ L := Nat.div_mul_le_self L s
  have hK2 : K ≤ L / 2 := Nat.div_le_div_left hs2 (by norm_num)
  have h2K : 2 * K ≤ L := by
    have := Nat.div_mul_le_self L 2
    omega
  have hKR : 2 * (K : ℝ) ≤ L := by exact_mod_cast h2K
  have hC : 0 ≤ C := by
    have h := hpoly 0 0 ⟨by linarith, by linarith⟩
    simp only [Int.cast_zero, abs_zero, add_zero, one_pow, mul_one] at h
    linarith [norm_nonneg (u 0 0)]
  set B : ℝ := C * (1 + 2 * (L : ℝ)) ^ N with hBdef
  have hB0 : 0 ≤ B := mul_nonneg hC (by positivity)
  set Δ : ℝ := δ / (2 * ((K : ℝ) + 1)) with hΔdef
  have hK1 : 0 < (K : ℝ) + 1 := by positivity
  have hΔ0 : 0 ≤ Δ := by positivity
  have hKΔ : (K : ℝ) * Δ ≤ δ / 2 := by
    rw [hΔdef, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- every mode reached by the iteration has grade at least `L/2`
  have hreach : ∀ m : ℤ, (m - n).natAbs ≤ K →
      (L : ℝ) / 2 ≤ |(m : ℝ)| ∧ |(m : ℝ)| ≤ 2 * L := by
    intro m hm
    have hmR : |(m : ℝ) - n| ≤ K := by
      rw [← Int.cast_sub, ← hcastAbs]; exact_mod_cast hm
    have h1 := abs_sub_abs_le_abs_sub (n : ℝ) (m : ℝ)
    have h2 := abs_sub_abs_le_abs_sub (m : ℝ) (n : ℝ)
    rw [abs_sub_comm] at h1
    constructor <;> linarith
  have claim : ∀ j : ℕ, j ≤ K → ∀ m : ℤ, (m - n).natAbs + j ≤ K →
      ∀ t : ℝ, |t| ≤ δ - j * Δ → ‖u m t‖ ≤ B * (1 / 2) ^ j := by
    intro j
    induction j with
    | zero =>
      intro _ m hm t ht
      have hm' := (hreach m (by omega)).2
      have htI : t ∈ Icc (-δ) δ := abs_le.mp (by simpa using ht)
      calc ‖u m t‖ ≤ C * (1 + |(m : ℝ)|) ^ N := hpoly m t htI
        _ ≤ C * (1 + 2 * (L : ℝ)) ^ N := by
          apply mul_le_mul_of_nonneg_left _ hC
          exact pow_le_pow_left₀ (by positivity) (by linarith) N
        _ = B * (1 / 2) ^ 0 := by simp [hBdef]
    | succ j ih =>
      intro hjK m hm t ht
      have hK1' : 1 ≤ K := by omega
      set d : ℝ := δ - j * Δ with hddef
      have hjΔ : (j : ℝ) * Δ ≤ δ / 2 :=
        le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : j ≤ K)) hΔ0) hKΔ
      have hd0 : 0 ≤ d := by rw [hddef]; linarith
      have hdδ : d ≤ δ := by rw [hddef]; nlinarith [hΔ0, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      have hIcc : Icc (-d) d ⊆ Icc (-δ) δ := Icc_subset_Icc (by linarith) hdδ
      have hIoo : Ioo (-d) d ⊆ Ioo (-δ) δ := Ioo_subset_Ioo (by linarith) hdδ
      obtain ⟨hmlow, -⟩ := hreach m (by omega)
      have hLpos : (2 * (n₀ : ℝ) + 2) ≤ L := hL ▸ hn
      have hmn₀ : (n₀ : ℝ) ≤ |(m : ℝ)| := by linarith
      have hmpos : 0 < |(m : ℝ)| := by
        have : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
        linarith
      set κ : ℝ := Real.sqrt κsq * |(m : ℝ)| with hκdef
      have hsq : Real.sqrt κsq ^ 2 = κsq := Real.sq_sqrt hκ.le
      have hκpos : 0 < κ := mul_pos (Real.sqrt_pos.mpr hκ) hmpos
      have hκ2 : κ ^ 2 = κsq * (m : ℝ) ^ 2 := by
        rw [hκdef, mul_pow, hsq, sq_abs]
      have hΔκ : Real.log 16 ≤ κ * Δ := by
        have hsK : (s : ℝ) * ((K : ℝ) + 1) ≤ 4 * |(m : ℝ)| := by
          have hKs' : (K : ℝ) * s ≤ L := by exact_mod_cast hKs
          have hK1R : (1 : ℝ) ≤ K := by exact_mod_cast hK1'
          have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
          nlinarith
        have hsqrt0 : 0 ≤ Real.sqrt κsq := Real.sqrt_nonneg _
        have key : Real.sqrt κsq * δ * s / 8 ≤ κ * Δ := by
          rw [hκdef, hΔdef, div_le_iff₀ (by norm_num : (0 : ℝ) < 8)]
          rw [show Real.sqrt κsq * |(m : ℝ)| * (δ / (2 * ((K : ℝ) + 1))) * 8 =
              Real.sqrt κsq * δ * (4 * |(m : ℝ)|) / ((K : ℝ) + 1) by field_simp; ring]
          rw [le_div_iff₀ hK1]
          have := mul_le_mul_of_nonneg_left hsK (mul_nonneg hsqrt0 hδ.le)
          nlinarith
        linarith
      have hB'0 : 0 ≤ B * (1 / 2) ^ j := by positivity
      have hneigh : ∀ m' : ℤ, (m' - n).natAbs ≤ (m - n).natAbs + 1 →
          ∀ τ ∈ Icc (-d) d, ‖u m' τ‖ ≤ B * (1 / 2) ^ j := by
        intro m' hm' τ hτ
        exact ih (by omega) m' (by omega) τ (abs_le.mpr hτ)
      have hm1 : (m - 1 - n).natAbs ≤ (m - n).natAbs + 1 := by
        have := Int.natAbs_sub_le (m - n) 1
        rw [show m - 1 - n = m - n - 1 by ring]
        simpa using this
      have hm2 : (m + 1 - n).natAbs ≤ (m - n).natAbs + 1 := by
        have := Int.natAbs_add_le (m - n) 1
        rw [show m + 1 - n = m - n + 1 by ring]
        simpa using this
      have hstep := norm_le_half_of_coshBarrier (d := d) (u := u m) (u' := u' m)
        (u'' := u'' m) (a := a m)
        (f := fun τ => bm m τ * u (m - 1) τ + bp m τ * u (m + 1) τ)
        hκpos hθ0 hθ hB'0 hΔκ
        (fun τ hτ => hu m τ (hIcc hτ)) ((hu'c m).mono hIcc)
        (fun τ hτ hτ0 => hu'' m τ (hIoo hτ) hτ0)
        (fun τ hτ hτ0 => heq m τ (hIoo hτ) hτ0)
        (fun τ hτ hτ0 => by rw [hκ2]; exact ha m hmn₀ τ (hIoo hτ) hτ0)
        (fun τ hτ hτ0 => by
          have hτI : τ ∈ Icc (-d) d := Ioo_subset_Icc_self hτ
          have h1 := hneigh (m - 1) hm1 τ hτI
          have h2 := hneigh (m + 1) hm2 τ hτI
          have hbb := hb m hmn₀ τ (hIoo hτ) hτ0
          calc ‖bm m τ * u (m - 1) τ + bp m τ * u (m + 1) τ‖
              ≤ ‖bm m τ‖ * ‖u (m - 1) τ‖ + ‖bp m τ‖ * ‖u (m + 1) τ‖ := by
                refine (norm_add_le _ _).trans ?_
                rw [norm_mul, norm_mul]
            _ ≤ ‖bm m τ‖ * (B * (1 / 2) ^ j) + ‖bp m τ‖ * (B * (1 / 2) ^ j) := by
                gcongr
            _ = (‖bm m τ‖ + ‖bp m τ‖) * (B * (1 / 2) ^ j) := by ring
            _ ≤ θ * κsq * (m : ℝ) ^ 2 * (B * (1 / 2) ^ j) :=
                mul_le_mul_of_nonneg_right hbb hB'0
            _ = θ * κ ^ 2 * (B * (1 / 2) ^ j) := by rw [hκ2]; ring)
        (ih (by omega) m (by omega) (-d) (by rw [abs_neg, abs_of_nonneg hd0]))
        (ih (by omega) m (by omega) d (by rw [abs_of_nonneg hd0]))
      have ht' : |t| ≤ d - Δ := by
        rw [hddef]; push_cast at ht; linarith
      have := hstep t ht'
      calc ‖u m t‖ ≤ B * (1 / 2) ^ j / 2 := this
        _ = B * (1 / 2) ^ (j + 1) := by ring
  have hfinal := claim K le_rfl n (by simp) 0 (by
    rw [abs_zero]; linarith)
  calc ‖u n 0‖ ≤ B * (1 / 2) ^ K := hfinal
    _ = C * (1 + 2 * |(n : ℝ)|) ^ N * (1 / 2) ^ (n.natAbs / s) := by
      rw [hBdef, hL]

private theorem half_pow_div_le {s n : ℕ} (hs : 1 ≤ s) :
    (1 / 2 : ℝ) ^ (n / s) ≤ 2 * (1 - 1 / (2 * (s : ℝ))) ^ n := by
  set ρ : ℝ := 1 - 1 / (2 * (s : ℝ)) with hρ
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hρ0 : 0 ≤ ρ := by
    rw [hρ, sub_nonneg, div_le_one (by positivity)]; linarith
  have hρ1 : ρ ≤ 1 := by
    have : 0 ≤ 1 / (2 * (s : ℝ)) := by positivity
    rw [hρ]; linarith
  have hbern : (1 / 2 : ℝ) ≤ ρ ^ s := by
    have h := one_add_mul_le_pow (a := -(1 / (2 * (s : ℝ)))) (by
      have : 1 / (2 * (s : ℝ)) ≤ 1 / 2 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
      linarith) s
    have hsx : (s : ℝ) * -(1 / (2 * (s : ℝ))) = -(1 / 2) := by field_simp
    rw [hsx] at h
    rw [hρ, sub_eq_add_neg]
    linarith
  have hn : n ≤ s * (n / s + 1) := (Nat.lt_mul_div_succ n (by omega)).le
  calc (1 / 2 : ℝ) ^ (n / s) = 2 * (1 / 2) ^ (n / s + 1) := by ring
    _ ≤ 2 * (ρ ^ s) ^ (n / s + 1) := by
      gcongr
    _ = 2 * ρ ^ (s * (n / s + 1)) := by rw [pow_mul]
    _ ≤ 2 * ρ ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ0 hρ1 hn) (by norm_num)

/-- **Smooth interface trace.** The interface sideband values of a diagonally
dominant elliptic collar system that is polynomially bounded on the collar decay
faster than every power of the grade, in both directions. -/
theorem dominantCollar_trace_rapid_decay
    {δ κsq θ C : ℝ} {N n₀ : ℕ} (hδ : 0 < δ) (hκ : 0 < κsq) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 3)
    {u u' u'' a bm bp : ℤ → ℝ → ℂ}
    (hu : ∀ n, ∀ t ∈ Icc (-δ) δ, HasDerivAt (u n) (u' n t) t)
    (hu'c : ∀ n, ContinuousOn (u' n) (Icc (-δ) δ))
    (hu'' : ∀ n, ∀ t ∈ Ioo (-δ) δ, t ≠ 0 → HasDerivAt (u' n) (u'' n t) t)
    (heq : ∀ n, ∀ t ∈ Ioo (-δ) δ, t ≠ 0 →
      u'' n t = a n t * u n t + (bm n t * u (n - 1) t + bp n t * u (n + 1) t))
    (ha : ∀ n : ℤ, (n₀ : ℝ) ≤ |(n : ℝ)| → ∀ t ∈ Ioo (-δ) δ, t ≠ 0 →
      κsq * (n : ℝ) ^ 2 ≤ (a n t).re)
    (hb : ∀ n : ℤ, (n₀ : ℝ) ≤ |(n : ℝ)| → ∀ t ∈ Ioo (-δ) δ, t ≠ 0 →
      ‖bm n t‖ + ‖bp n t‖ ≤ θ * κsq * (n : ℝ) ^ 2)
    (hpoly : ∀ n, ∀ t ∈ Icc (-δ) δ, ‖u n t‖ ≤ C * (1 + |(n : ℝ)|) ^ N) (k : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ k * ‖u n 0‖) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => (n : ℝ) ^ k * ‖u (-(n : ℤ)) 0‖) atTop (𝓝 0) := by
  obtain ⟨s₁, hs₁⟩ := exists_nat_ge (8 * Real.log 16 / (Real.sqrt κsq * δ))
  set s : ℕ := max 2 s₁ with hsdef
  have hs2 : 2 ≤ s := le_max_left _ _
  have hsqδ : 0 < Real.sqrt κsq * δ := mul_pos (Real.sqrt_pos.mpr hκ) hδ
  have hs : 8 * Real.log 16 ≤ Real.sqrt κsq * δ * s := by
    have h1 : (s₁ : ℝ) ≤ s := by exact_mod_cast le_max_right 2 s₁
    rw [div_le_iff₀ hsqδ] at hs₁
    nlinarith
  have hC : 0 ≤ C := by
    have h := hpoly 0 0 ⟨by linarith, by linarith⟩
    simp only [Int.cast_zero, abs_zero, add_zero, one_pow, mul_one] at h
    linarith [norm_nonneg (u 0 0)]
  set ρ : ℝ := 1 - 1 / (2 * (s : ℝ)) with hρ
  have hs' : (2 : ℝ) ≤ s := by exact_mod_cast hs2
  have hρ0 : 0 ≤ ρ := by
    rw [hρ, sub_nonneg, div_le_one (by positivity)]; linarith
  have hρ1 : ρ < 1 := by
    have : 0 < 1 / (2 * (s : ℝ)) := by positivity
    rw [hρ]; linarith
  have hlim : Tendsto (fun n : ℕ => 2 * C * 3 ^ N * ((n : ℝ) ^ (k + N) * ρ ^ n)) atTop (𝓝 0) := by
    have := tendsto_pow_const_mul_const_pow_of_abs_lt_one (k + N) (r := ρ)
      (by rw [abs_of_nonneg hρ0]; exact hρ1)
    simpa using this.const_mul (2 * C * 3 ^ N)
  have hbound : ∀ z : ℤ, ∀ n : ℕ, |(z : ℝ)| = n → 2 * (n₀ : ℝ) + 2 ≤ n → 1 ≤ n →
      (n : ℝ) ^ k * ‖u z 0‖ ≤ 2 * C * 3 ^ N * ((n : ℝ) ^ (k + N) * ρ ^ n) := by
    intro z n hz hn hn1
    have hmain := dominantCollar_trace_le hδ hκ hθ0 hθ hs2 hs hu hu'c hu'' heq ha hb hpoly z
      (by rw [hz]; exact hn)
    have hnat : z.natAbs = n := by
      have : ((z.natAbs : ℕ) : ℝ) = n := by rw [Nat.cast_natAbs, Int.cast_abs]; exact hz
      exact_mod_cast this
    rw [hz, hnat] at hmain
    have hgeom := half_pow_div_le (s := s) (n := n) (by omega)
    have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have h3 : (1 + 2 * (n : ℝ)) ^ N ≤ (3 * n) ^ N :=
      pow_le_pow_left₀ (by positivity) (by linarith) N
    have hnk : 0 ≤ (n : ℝ) ^ k := by positivity
    calc (n : ℝ) ^ k * ‖u z 0‖
        ≤ (n : ℝ) ^ k * (C * (1 + 2 * (n : ℝ)) ^ N * (1 / 2) ^ (n / s)) :=
          mul_le_mul_of_nonneg_left hmain hnk
      _ ≤ (n : ℝ) ^ k * (C * (3 * n) ^ N * (2 * ρ ^ n)) := by
          gcongr
      _ = 2 * C * 3 ^ N * ((n : ℝ) ^ (k + N) * ρ ^ n) := by ring
  have hev : ∀ᶠ n : ℕ in atTop, 2 * (n₀ : ℝ) + 2 ≤ n ∧ 1 ≤ n := by
    filter_upwards [eventually_ge_atTop (2 * n₀ + 2)] with n hn
    exact ⟨by exact_mod_cast hn, by omega⟩
  constructor
  · apply squeeze_zero' (Eventually.of_forall fun n => by positivity) _ hlim
    filter_upwards [hev] with n hn
    exact hbound n n (by simp) hn.1 hn.2
  · apply squeeze_zero' (Eventually.of_forall fun n => by positivity) _ hlim
    filter_upwards [hev] with n hn
    exact hbound (-(n : ℤ)) n (by simp) hn.1 hn.2

end GaloisForLFunctions.HTGeometry
