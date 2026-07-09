import GaloisForLFunctions.RHTower.DictionarySign
import GaloisForLFunctions.RHTower.DeckCocycle
import GaloisForLFunctions.RHTower.RootExistence
import GaloisForLFunctions.RHTower.WindingXiCircle
import GaloisForLFunctions.RHTower.XiRealAnchorPositive
import GaloisForLFunctions.RHTower.CoherentTower
import GaloisForLFunctions.RHTower.WeldTowerLimit

/-!
# Dissolution of the seam-sign obstruction on symmetric regions

For a function with the real functional equation `f ∘ lineReflect = conj ∘ f` across
the critical line, the Schwarz-equivariant (Real) `n`-th root theory carries one bit
beyond the plain Kummer theory: the sign of `f` at a line anchor.  This module locates
that bit exactly.  On a line-symmetric preconnected open set, any plain analytic
`n`-th root `g` reflects to a second root `mirrorRoot g`, so the two differ by a
constant `n`-th root of unity `ζ = conj (g a)/g a` read at a line anchor `a`
(`mirrorRoot_ratio`).  An equivariant root is a rescaling `c·g` with `c ∈ μ_n` and
`conj c · ζ = c`; solvability is the square-class of `ζ` in `μ_n/μ_n²`, and the anchor
computes it: `f a > 0` makes `ζ` a square (the explicit unimodular scale
`c = conj (g a)/‖g a‖` works), `f a < 0` with `n` even makes it a non-square.

* `exists_equivariant_root_of_anchor_pos` — positive anchor: every plain root rescales
  to an equivariant one.  The seam-sign bit is invisible on symmetric regions with a
  positive line anchor.
* `anchor_pos_of_equivariant_root` — even `n`: an equivariant root is real at the
  anchor, so its even power is positive there; negativity obstructs.
* `exists_equivariant_root_of_odd` — odd `n`: no sign condition at all; the bit is
  `2`-adic.
* `exists_equivariant_root_iff_orders_dvd` — the regional dichotomy on a symmetric
  convex window: equivariant root (even `n`) ⟺ plain divisibility of all vanishing
  orders ∧ positive anchor.
* `xi_equivariant_root_iff_orders_dvd`, `xi_equivariant_root_iff_root` — for ξ the
  anchor clause is a theorem (`ξ(1/2) > 0`), so on every line-symmetric convex window
  containing the central anchor the Real tower obstruction of ξ **equals** the plain
  divisibility obstruction: regionally, the equivariant theory adds nothing.

Contrast with the boundary theory, where the anchor-sign bit is an independent
component of `π₀` alongside the winding: the sign is a *hole-detecting* invariant.
It obstructs roots on circles and annuli but never on symmetric simply-connected
regions with a positive anchor — precisely because a region sees the divisor
(per-zero orders), which already forces the line-sign bookkeeping that a boundary
loop can only sample.
-/

namespace RHTower

open Complex Set Metric

/-- A function with the real functional equation is real at critical-line points:
`lineReflect` fixes the line, so `f a = conj (f a)`. -/
theorem im_eq_zero_at_line_of_lineReflectFE {f : ℂ → ℂ}
    (hsym : ∀ s, f (lineReflect s) = (starRingEnd ℂ) (f s))
    {a : ℂ} (hare : a.re = 1 / 2) : (f a).im = 0 := by
  have h := hsym a
  rw [lineReflect_eq_self_iff.mpr hare] at h
  exact Complex.conj_eq_iff_im.mp h.symm

/-- **The reflection ratio.**  On a line-symmetric preconnected open set, the Schwarz
mirror of an analytic `n`-th root is again a root, hence differs from it by a constant
`n`-th root of unity — computed at any line anchor as `conj (g a)/g a`. -/
theorem mirrorRoot_ratio {f g : ℂ → ℂ} {U : Set ℂ} {n : ℕ} (hn : 0 < n)
    (hU : IsOpen U) (hUc : IsPreconnected U) (hUsym : lineReflect ⁻¹' U = U)
    (hsym : ∀ s, f (lineReflect s) = (starRingEnd ℂ) (f s))
    (hg : AnalyticOnNhd ℂ g U) (hpow : ∀ s ∈ U, g s ^ n = f s)
    {a : ℂ} (haU : a ∈ U) (hare : a.re = 1 / 2) (hfa : f a ≠ 0) :
    ((starRingEnd ℂ) (g a) / g a) ^ n = 1 ∧
      Set.EqOn (mirrorRoot g) (fun s => ((starRingEnd ℂ) (g a) / g a) * g s) U := by
  have hman : AnalyticOnNhd ℂ (mirrorRoot g) U := by
    have h := mirrorRoot_analyticOnNhd hU hg
    rwa [hUsym] at h
  have hmpow : ∀ s ∈ U, mirrorRoot g s ^ n = f s := by
    intro s hs
    exact mirrorRoot_pow hsym hpow s (by rwa [hUsym])
  have h := pow_root_ratio hn hU hUc hman hg hmpow hpow haU hfa
  rwa [mirrorRoot_apply_line hare] at h

/-- **The rescaling engine.**  If a unimodular `n`-th root of unity `c` transports the
reflection ratio to itself (`conj c · ζ = c`), then `c·g` is an equivariant `n`-th
root: the mirror of `c·g` is `conj c · ζ · g = c·g`. -/
theorem exists_equivariant_root_of_scale {f g : ℂ → ℂ} {U : Set ℂ} {n : ℕ} (hn : 0 < n)
    (hU : IsOpen U) (hUc : IsPreconnected U) (hUsym : lineReflect ⁻¹' U = U)
    (hsym : ∀ s, f (lineReflect s) = (starRingEnd ℂ) (f s))
    (hg : AnalyticOnNhd ℂ g U) (hpow : ∀ s ∈ U, g s ^ n = f s)
    {a : ℂ} (haU : a ∈ U) (hare : a.re = 1 / 2) (hfa : f a ≠ 0)
    {c : ℂ} (hcn : c ^ n = 1)
    (hkey : (starRingEnd ℂ) c * ((starRingEnd ℂ) (g a) / g a) = c) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h U ∧ (∀ s ∈ U, h s ^ n = f s) ∧
      ∀ s ∈ U, mirrorRoot h s = h s := by
  obtain ⟨-, hEq⟩ := mirrorRoot_ratio hn hU hUc hUsym hsym hg hpow haU hare hfa
  refine ⟨fun s => c * g s, fun z hz => analyticAt_const.mul (hg z hz), ?_, ?_⟩
  · intro s hs
    rw [mul_pow, hcn, one_mul]
    exact hpow s hs
  · intro s hs
    have hmr : mirrorRoot g s = ((starRingEnd ℂ) (g a) / g a) * g s := hEq hs
    show (starRingEnd ℂ) (c * g (lineReflect s)) = c * g s
    have hunfold : (starRingEnd ℂ) (g (lineReflect s)) = mirrorRoot g s := rfl
    rw [map_mul, hunfold, hmr, ← mul_assoc, hkey]

/-- **Dissolution at a positive anchor.**  A line-symmetric function positive at a
critical-line point rescales any plain analytic `n`-th root into a Schwarz-equivariant
one: the unimodular constant `conj (g a)/‖g a‖` is an `n`-th root of unity because
`‖g a‖ⁿ = f a`, and it transports the reflection ratio to itself.  The seam-sign bit
is therefore not a regional invariant — it cannot obstruct symmetric regions with a
positive line anchor. -/
theorem exists_equivariant_root_of_anchor_pos {f g : ℂ → ℂ} {U : Set ℂ} {n : ℕ}
    (hn : 0 < n) (hU : IsOpen U) (hUc : IsPreconnected U)
    (hUsym : lineReflect ⁻¹' U = U)
    (hsym : ∀ s, f (lineReflect s) = (starRingEnd ℂ) (f s))
    (hg : AnalyticOnNhd ℂ g U) (hpow : ∀ s ∈ U, g s ^ n = f s)
    {a : ℂ} (haU : a ∈ U) (hare : a.re = 1 / 2) (hfa : 0 < (f a).re) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h U ∧ (∀ s ∈ U, h s ^ n = f s) ∧
      ∀ s ∈ U, mirrorRoot h s = h s := by
  have him : (f a).im = 0 := im_eq_zero_at_line_of_lineReflectFE hsym hare
  have hfa0 : f a ≠ 0 := by
    intro h0
    rw [h0] at hfa
    simp at hfa
  have hfeq : f a = ((f a).re : ℂ) := Complex.ext (by simp) (by simpa using him)
  have hga : g a ≠ 0 := by
    intro h0
    apply hfa0
    rw [← hpow a haU, h0, zero_pow hn.ne']
  have hnrm : ‖g a‖ ^ n = (f a).re := by
    have h1 : ‖g a‖ ^ n = ‖g a ^ n‖ := (norm_pow _ _).symm
    rw [hpow a haU, hfeq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hfa] at h1
    exact h1
  have hNne : ((‖g a‖ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hga)
  have hcn : ((starRingEnd ℂ) (g a) / ((‖g a‖ : ℝ) : ℂ)) ^ n = 1 := by
    rw [div_pow, ← map_pow, ← Complex.ofReal_pow, hpow a haU, hnrm,
      Complex.conj_eq_iff_im.mpr him,
      div_eq_one_iff_eq (Complex.ofReal_ne_zero.mpr hfa.ne')]
    exact hfeq
  have hkey : (starRingEnd ℂ) ((starRingEnd ℂ) (g a) / ((‖g a‖ : ℝ) : ℂ)) *
      ((starRingEnd ℂ) (g a) / g a) = (starRingEnd ℂ) (g a) / ((‖g a‖ : ℝ) : ℂ) := by
    rw [map_div₀, Complex.conj_conj, Complex.conj_ofReal, div_mul_div_comm,
      mul_comm (g a) ((starRingEnd ℂ) (g a)), mul_div_mul_right _ _ hga]
  exact exists_equivariant_root_of_scale hn hU hUc hUsym hsym hg hpow haU hare hfa0
    hcn hkey

/-- **Necessity of the positive anchor for even `n`.**  An equivariant root is real at
a critical-line anchor (its mirror there is its conjugate), so for even `n` the rooted
function is a nonzero even power of a real number: positive.  A negative line value
obstructs every equivariant even root on any set containing the anchor — regardless
of the region's shape. -/
theorem anchor_pos_of_equivariant_root {f h : ℂ → ℂ} {U : Set ℂ} {n : ℕ}
    (hne : Even n) (hh : ∀ s ∈ U, mirrorRoot h s = h s)
    (hpow : ∀ s ∈ U, h s ^ n = f s)
    {a : ℂ} (haU : a ∈ U) (hare : a.re = 1 / 2) (hfa : f a ≠ 0) :
    0 < (f a).re := by
  have h1 := hh a haU
  rw [mirrorRoot_apply_line hare] at h1
  have him : (h a).im = 0 := Complex.conj_eq_iff_im.mp h1
  have hxeq : h a = ((h a).re : ℂ) := Complex.ext (by simp) (by simpa using him)
  have hfx : f a = (((h a).re ^ n : ℝ) : ℂ) := by
    rw [← hpow a haU, Complex.ofReal_pow]
    congr 1
  have hre : (f a).re = (h a).re ^ n := by rw [hfx, Complex.ofReal_re]
  rw [hre]
  refine lt_of_le_of_ne (hne.pow_nonneg _) ?_
  intro h0
  apply hfa
  rw [hfx, ← h0, Complex.ofReal_zero]

/-- **The even dichotomy** (given a plain root): a line-symmetric function with an
analytic `n`-th root (`n` even) on a line-symmetric preconnected open set admits an
*equivariant* `n`-th root exactly when its anchor value is positive.  The equivariant
theory's whole surplus over the plain Kummer theory is this one sign. -/
theorem exists_equivariant_root_iff_anchor_pos {f g : ℂ → ℂ} {U : Set ℂ} {n : ℕ}
    (hn : 0 < n) (hne : Even n) (hU : IsOpen U) (hUc : IsPreconnected U)
    (hUsym : lineReflect ⁻¹' U = U)
    (hsym : ∀ s, f (lineReflect s) = (starRingEnd ℂ) (f s))
    (hg : AnalyticOnNhd ℂ g U) (hpow : ∀ s ∈ U, g s ^ n = f s)
    {a : ℂ} (haU : a ∈ U) (hare : a.re = 1 / 2) (hfa : f a ≠ 0) :
    (∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h U ∧ (∀ s ∈ U, h s ^ n = f s) ∧
      ∀ s ∈ U, mirrorRoot h s = h s) ↔ 0 < (f a).re := by
  constructor
  · rintro ⟨h, -, hhp, hhe⟩
    exact anchor_pos_of_equivariant_root hne hhe hhp haU hare hfa
  · intro hpos
    exact exists_equivariant_root_of_anchor_pos hn hU hUc hUsym hsym hg hpow haU
      hare hpos

/-- **Odd levels are free.**  For odd `n` the sign clause disappears: any plain
`n`-th root of a line-symmetric function rescales to an equivariant one at either
anchor sign (`−1` is itself an odd root of unity, absorbing a negative anchor).
The seam-sign bit of the equivariant root theory is purely `2`-adic. -/
theorem exists_equivariant_root_of_odd {f g : ℂ → ℂ} {U : Set ℂ} {n : ℕ}
    (hodd : Odd n) (hU : IsOpen U) (hUc : IsPreconnected U)
    (hUsym : lineReflect ⁻¹' U = U)
    (hsym : ∀ s, f (lineReflect s) = (starRingEnd ℂ) (f s))
    (hg : AnalyticOnNhd ℂ g U) (hpow : ∀ s ∈ U, g s ^ n = f s)
    {a : ℂ} (haU : a ∈ U) (hare : a.re = 1 / 2) (hfa : f a ≠ 0) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h U ∧ (∀ s ∈ U, h s ^ n = f s) ∧
      ∀ s ∈ U, mirrorRoot h s = h s := by
  have hn : 0 < n := hodd.pos
  have him : (f a).im = 0 := im_eq_zero_at_line_of_lineReflectFE hsym hare
  have hfeq : f a = ((f a).re : ℂ) := Complex.ext (by simp) (by simpa using him)
  have hre0 : (f a).re ≠ 0 := by
    intro h0
    apply hfa
    rw [hfeq, h0, Complex.ofReal_zero]
  have hga : g a ≠ 0 := by
    intro h0
    apply hfa
    rw [← hpow a haU, h0, zero_pow hn.ne']
  have hNne : ((‖g a‖ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hga)
  rcases lt_or_gt_of_ne hre0 with hneg | hpos
  · -- negative anchor: the scale `−conj (g a)/‖g a‖` is an `n`-th root of unity
    have hnrm : ‖g a‖ ^ n = -(f a).re := by
      have h1 : ‖g a‖ ^ n = ‖g a ^ n‖ := (norm_pow _ _).symm
      rw [hpow a haU, hfeq, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hneg] at h1
      exact h1
    have hcn : (-((starRingEnd ℂ) (g a)) / ((‖g a‖ : ℝ) : ℂ)) ^ n = 1 := by
      rw [neg_div, neg_pow, hodd.neg_one_pow, neg_one_mul, div_pow, ← map_pow,
        ← Complex.ofReal_pow, hpow a haU, hnrm, Complex.conj_eq_iff_im.mpr him,
        Complex.ofReal_neg, div_neg, neg_neg,
        div_eq_one_iff_eq (Complex.ofReal_ne_zero.mpr hre0)]
      exact hfeq
    have hkey : (starRingEnd ℂ) (-((starRingEnd ℂ) (g a)) / ((‖g a‖ : ℝ) : ℂ)) *
        ((starRingEnd ℂ) (g a) / g a) =
        -((starRingEnd ℂ) (g a)) / ((‖g a‖ : ℝ) : ℂ) := by
      rw [map_div₀, map_neg, Complex.conj_conj, Complex.conj_ofReal, neg_div,
        neg_mul, div_mul_div_comm, mul_comm (g a) ((starRingEnd ℂ) (g a)),
        mul_div_mul_right _ _ hga, neg_div]
    exact exists_equivariant_root_of_scale hn hU hUc hUsym hsym hg hpow haU hare hfa
      hcn hkey
  · -- positive anchor: the even-case scale works verbatim
    exact exists_equivariant_root_of_anchor_pos hn hU hUc hUsym hsym hg hpow haU
      hare hpos

/-- **The regional dichotomy.**  On a line-symmetric convex window, a line-symmetric
function with locally finite zeros admits a Schwarz-equivariant `n`-th root (`n` even)
exactly when every vanishing order is divisible by `n` AND the anchor value is
positive.  Divisibility is the plain Kummer obstruction; the sign is the entire
equivariant surplus — one bit, read at one line point. -/
theorem exists_equivariant_root_iff_orders_dvd {f : ℂ → ℂ} {Ω : Set ℂ} {n : ℕ}
    (hn : 0 < n) (hne : Even n) (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hΩsym : lineReflect ⁻¹' Ω = Ω)
    (hsym : ∀ s, f (lineReflect s) = (starRingEnd ℂ) (f s))
    (hf : AnalyticOnNhd ℂ f Ω)
    {a : ℂ} (haU : a ∈ Ω) (hare : a.re = 1 / 2) (hfa : f a ≠ 0)
    (hZloc : ∀ R : ℕ, {s ∈ Ω ∩ ball a ((R : ℝ) + 1) | f s = 0}.Finite) :
    (∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h Ω ∧ (∀ s ∈ Ω, h s ^ n = f s) ∧
      ∀ s ∈ Ω, mirrorRoot h s = h s) ↔
      ((∀ ρ ∈ Ω, f ρ = 0 → (n : ℕ∞) ∣ analyticOrderAt f ρ) ∧ 0 < (f a).re) := by
  constructor
  · rintro ⟨h, hha, hhp, hhe⟩
    exact ⟨(exists_root_iff_orders_dvd hn hΩo hΩc haU hf hfa hZloc).mp ⟨h, hha, hhp⟩,
      anchor_pos_of_equivariant_root hne hhe hhp haU hare hfa⟩
  · rintro ⟨hdvd, hpos⟩
    obtain ⟨g, hga, hgp⟩ :=
      (exists_root_iff_orders_dvd hn hΩo hΩc haU hf hfa hZloc).mpr hdvd
    exact exists_equivariant_root_of_anchor_pos hn hΩo hΩc.isPreconnected hΩsym hsym
      hga hgp haU hare hpos

/-- **The regional Real tower of ξ is the plain tower.**  On every line-symmetric
convex window containing the central anchor `1/2`, the Schwarz-equivariant `n`-th
root of ξ (`n` even) exists exactly when the plain divisibility obstruction
vanishes: `ξ(1/2) > 0` discharges the sign clause unconditionally.  Regionally the
equivariant theory imposes nothing beyond the plain ladder — the seam-sign bit of
the boundary classification is a hole-detecting invariant, invisible to symmetric
simply-connected windows. -/
theorem xi_equivariant_root_iff_orders_dvd {Ω : Set ℂ} {n : ℕ}
    (hn : 0 < n) (hne : Even n) (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hΩsym : lineReflect ⁻¹' Ω = Ω) (hhalf : ((1 / 2 : ℝ) : ℂ) ∈ Ω) :
    (∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h Ω ∧ (∀ s ∈ Ω, h s ^ n = xi s) ∧
      ∀ s ∈ Ω, mirrorRoot h s = h s) ↔
      ∀ ρ ∈ Ω, xi ρ = 0 → (n : ℕ∞) ∣ analyticOrderAt xi ρ := by
  have hare : (((1 / 2 : ℝ) : ℂ)).re = 1 / 2 := Complex.ofReal_re _
  have hpos : 0 < (xi ((1 / 2 : ℝ) : ℂ)).re :=
    xi_pos_on_real_anchor (by norm_num) (by norm_num)
  have hfa : xi ((1 / 2 : ℝ) : ℂ) ≠ 0 := by
    intro h0
    rw [h0] at hpos
    simp at hpos
  have hZloc : ∀ R : ℕ,
      {s ∈ Ω ∩ ball ((1 / 2 : ℝ) : ℂ) ((R : ℝ) + 1) | xi s = 0}.Finite := fun R =>
    (xi_zeros_closedBall_finite ((1 / 2 : ℝ) : ℂ) ((R : ℝ) + 1)).subset
      fun s hs => ⟨ball_subset_closedBall hs.1.2, hs.2⟩
  rw [exists_equivariant_root_iff_orders_dvd hn hne hΩo hΩc hΩsym xi_lineReflect
    (xi_analyticOnNhd_univ.mono (Set.subset_univ Ω)) hhalf hare hfa hZloc]
  exact and_iff_left hpos

/-- On a line-symmetric convex window containing the central anchor, ξ admits an
equivariant even root exactly when it admits a plain one: the dissolution, stated
without mentioning orders. -/
theorem xi_equivariant_root_iff_root {Ω : Set ℂ} {n : ℕ}
    (hn : 0 < n) (hne : Even n) (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hΩsym : lineReflect ⁻¹' Ω = Ω) (hhalf : ((1 / 2 : ℝ) : ℂ) ∈ Ω) :
    (∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h Ω ∧ (∀ s ∈ Ω, h s ^ n = xi s) ∧
      ∀ s ∈ Ω, mirrorRoot h s = h s) ↔
      ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g Ω ∧ ∀ s ∈ Ω, g s ^ n = xi s := by
  have hare : (((1 / 2 : ℝ) : ℂ)).re = 1 / 2 := Complex.ofReal_re _
  have hpos : 0 < (xi ((1 / 2 : ℝ) : ℂ)).re :=
    xi_pos_on_real_anchor (by norm_num) (by norm_num)
  have hfa : xi ((1 / 2 : ℝ) : ℂ) ≠ 0 := by
    intro h0
    rw [h0] at hpos
    simp at hpos
  have hZloc : ∀ R : ℕ,
      {s ∈ Ω ∩ ball ((1 / 2 : ℝ) : ℂ) ((R : ℝ) + 1) | xi s = 0}.Finite := fun R =>
    (xi_zeros_closedBall_finite ((1 / 2 : ℝ) : ℂ) ((R : ℝ) + 1)).subset
      fun s hs => ⟨ball_subset_closedBall hs.1.2, hs.2⟩
  rw [xi_equivariant_root_iff_orders_dvd hn hne hΩo hΩc hΩsym hhalf]
  exact (exists_root_iff_orders_dvd hn hΩo hΩc hhalf
    (xi_analyticOnNhd_univ.mono (Set.subset_univ Ω)) hfa hZloc).symm

/-- **Equivariant continuation of the far germ.**  The rung `RH_{2^k}` propagates the
level-`k` root germ *equivariantly* into every line-symmetric convex window containing
the central anchor whose on-line orders are `2^k`-divisible: the rung supplies the
right-half divisibility, its mirror image (`xi_orderAt_lineReflect`) the left-half
divisibility, the hypothesis the line divisibility — and the anchor sign is free.
The equivariant continuation therefore costs exactly one surcharge over the plain
rung, and that surcharge is the *unconditional* line ledger, not a right-half
statement.  The converse direction is `root_orders_dvd`: an equivariant window root
returns divisibility only window-locally, and a window reaching a right-half zero
past a line zero of non-divisible order is inadmissible — the line ledger is
precisely what blocks the regional equivariant data from returning the rung
globally. -/
theorem rhLadder_xi_equivariant_window_root {k : ℕ} (hlad : RHLadder k)
    {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hΩsym : lineReflect ⁻¹' Ω = Ω) (hhalf : ((1 / 2 : ℝ) : ℂ) ∈ Ω)
    (hline : ∀ ρ ∈ Ω, ρ.re = 1 / 2 → xi ρ = 0 →
      ((2 ^ k : ℕ) : ℕ∞) ∣ analyticOrderAt xi ρ) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h Ω ∧ (∀ s ∈ Ω, h s ^ 2 ^ k = xi s) ∧
      ∀ s ∈ Ω, mirrorRoot h s = h s := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- level 0: ξ itself is its own equivariant first root
    refine ⟨xi, xi_analyticOnNhd_univ.mono (Set.subset_univ Ω),
      fun s _ => by rw [pow_zero, pow_one], fun s _ => ?_⟩
    show (starRingEnd ℂ) (xi (lineReflect s)) = xi s
    rw [xi_lineReflect, Complex.conj_conj]
  · refine (xi_equivariant_root_iff_orders_dvd (pow_pos two_pos k)
      ((Nat.even_pow).mpr ⟨even_two, hk.ne'⟩) hΩo hΩc hΩsym hhalf).mpr ?_
    intro ρ hρ hρ0
    rcases lt_trichotomy ρ.re (1 / 2) with hlt | heq | hgt
    · -- left of the line: transport the rung through the mirror
      have hmre : (1 / 2 : ℝ) < (lineReflect ρ).re := by
        rw [lineReflect_re]; linarith
      have hm0 : xi (lineReflect ρ) = 0 := by
        rw [xi_lineReflect, hρ0, map_zero]
      have hdvd := hlad (lineReflect ρ) (mem_rightHalf.mpr hmre) hm0
      rwa [xi_orderAt_lineReflect] at hdvd
    · exact hline ρ hρ heq hρ0
    · exact hlad ρ (mem_rightHalf.mpr hgt) hρ0

/-- **The rung is an off-line equivariant statement.**  `RH_{2^k}` holds exactly when
ξ admits a Schwarz-equivariant `2^k`-th root off the critical line.  The off-line
region is a mirror pair of open half-planes, and equivariant structure is free
there: the plain right-half root of the rung extends by its own Schwarz mirror on
the left half-plane, and the glued function is equivariant by construction.
Conversely the right-half restriction of an off-line equivariant root is a plain
rung root.  Together with the regional dissolution and the boundary classification
this completes the obstruction map of the Real tower: off the line it carries
exactly the rung, on symmetric regions it adds only the unconditional line ledger,
and on symmetric boundaries it adds exactly one sign bit. -/
theorem rhLadder_iff_equivariant_offline_root (k : ℕ) :
    RHLadder k ↔
      ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h {s : ℂ | s.re ≠ 1 / 2} ∧
        (∀ s ∈ {s : ℂ | s.re ≠ 1 / 2}, h s ^ 2 ^ k = xi s) ∧
        ∀ s ∈ {s : ℂ | s.re ≠ 1 / 2}, mirrorRoot h s = h s := by
  constructor
  · intro hlad
    obtain ⟨g, hga, hgp⟩ := (rhLadder_iff_root k).mp hlad
    refine ⟨fun s => if 1 / 2 < s.re then g s else mirrorRoot g s, ?_, ?_, ?_⟩
    · intro s hs
      rcases lt_or_gt_of_ne (Ne.symm hs) with hgt | hlt
      · -- right half: locally equal to `g`
        refine (hga s hgt).congr ?_
        refine Filter.eventually_of_mem (isOpen_rightHalf.mem_nhds hgt) fun z hz => ?_
        simp only [if_pos (mem_rightHalf.mp hz)]
      · -- left half: locally equal to the mirror root
        have hmem : s ∈ lineReflect ⁻¹' rightHalf := by
          show 1 / 2 < (lineReflect s).re
          rw [lineReflect_re]; linarith
        have hopen : IsOpen (lineReflect ⁻¹' rightHalf) :=
          isOpen_rightHalf.preimage continuous_lineReflect
        refine (mirrorRoot_analyticOnNhd isOpen_rightHalf hga s hmem).congr ?_
        refine Filter.eventually_of_mem (hopen.mem_nhds hmem) fun z hz => ?_
        have hzlt : ¬(1 / 2 < z.re) := by
          have : 1 / 2 < (lineReflect z).re := hz
          rw [lineReflect_re] at this; linarith
        simp only [if_neg hzlt]
    · intro s hs
      show (if 1 / 2 < s.re then g s else mirrorRoot g s) ^ 2 ^ k = xi s
      rcases lt_or_gt_of_ne (Ne.symm hs) with hgt | hlt
      · rw [if_pos hgt]
        exact hgp s (mem_rightHalf.mpr hgt)
      · rw [if_neg (by linarith : ¬(1 / 2 < s.re))]
        refine mirrorRoot_pow xi_lineReflect hgp s ?_
        show 1 / 2 < (lineReflect s).re
        rw [lineReflect_re]; linarith
    · intro s hs
      show (starRingEnd ℂ)
          (if 1 / 2 < (lineReflect s).re then g (lineReflect s)
            else mirrorRoot g (lineReflect s)) =
        (if 1 / 2 < s.re then g s else mirrorRoot g s)
      rcases lt_or_gt_of_ne (Ne.symm hs) with hgt | hlt
      · -- mirror of the glued root at a right-half point reads the left branch
        have hrefl : ¬(1 / 2 < (lineReflect s).re) := by
          rw [lineReflect_re]; linarith
        rw [if_neg hrefl, if_pos hgt]
        show (starRingEnd ℂ) ((starRingEnd ℂ) (g (lineReflect (lineReflect s)))) = g s
        rw [lineReflect_involutive, Complex.conj_conj]
      · have hrefl : 1 / 2 < (lineReflect s).re := by
          rw [lineReflect_re]; linarith
        rw [if_pos hrefl, if_neg (by linarith : ¬(1 / 2 < s.re))]
        rfl
  · rintro ⟨h, hha, hhp, -⟩
    refine (rhLadder_iff_root k).mpr
      ⟨h, hha.mono fun s hs => ?_, fun s hs => hhp s ?_⟩
    · exact ne_of_gt (mem_rightHalf.mp hs)
    · exact ne_of_gt (mem_rightHalf.mp hs)

/-! ### The pro level: coherent towers

The dissolution persists in the inverse limit.  The rescaling constants
`c_k = conj (g_k a)/‖g_k a‖` are *coherent* — `c_{k+1}² = c_k` is forced by the
tower's squaring law at the anchor — so symmetrizing a coherent tower level by
level yields an equivariant coherent tower: no new obstruction appears in the
limit on symmetric regions with a positive anchor.  Off the line, gluing a
right-half tower with its level-wise Schwarz mirror is coherent for the same
reason, which turns the banked criterion `RH ⟺ coherent tower on the right
half-plane` into a single equivariant pro-object statement. -/

/-- The Schwarz mirror gluing: a right-half function continued by its mirror to
the left half-plane. -/
noncomputable def mirrorGlue (g : ℂ → ℂ) : ℂ → ℂ :=
  fun s => if 1 / 2 < s.re then g s else mirrorRoot g s

theorem mirrorGlue_analyticOnNhd {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g rightHalf) :
    AnalyticOnNhd ℂ (mirrorGlue g) {s : ℂ | s.re ≠ 1 / 2} := by
  intro s hs
  rcases lt_or_gt_of_ne (Ne.symm hs) with hgt | hlt
  · refine (hg s hgt).congr ?_
    refine Filter.eventually_of_mem (isOpen_rightHalf.mem_nhds hgt) fun z hz => ?_
    simp only [mirrorGlue, if_pos (mem_rightHalf.mp hz)]
  · have hmem : s ∈ lineReflect ⁻¹' rightHalf := by
      show 1 / 2 < (lineReflect s).re
      rw [lineReflect_re]; linarith
    have hopen : IsOpen (lineReflect ⁻¹' rightHalf) :=
      isOpen_rightHalf.preimage continuous_lineReflect
    refine (mirrorRoot_analyticOnNhd isOpen_rightHalf hg s hmem).congr ?_
    refine Filter.eventually_of_mem (hopen.mem_nhds hmem) fun z hz => ?_
    have hzlt : ¬(1 / 2 < z.re) := by
      have h1 : 1 / 2 < (lineReflect z).re := hz
      rw [lineReflect_re] at h1; linarith
    simp only [mirrorGlue, if_neg hzlt]

/-- The mirror gluing is equivariant off the line, with no hypothesis on `g`. -/
theorem mirrorGlue_equivariant (g : ℂ → ℂ) :
    ∀ s ∈ {s : ℂ | s.re ≠ 1 / 2}, mirrorRoot (mirrorGlue g) s = mirrorGlue g s := by
  intro s hs
  show (starRingEnd ℂ)
      (if 1 / 2 < (lineReflect s).re then g (lineReflect s)
        else mirrorRoot g (lineReflect s)) =
    (if 1 / 2 < s.re then g s else mirrorRoot g s)
  rcases lt_or_gt_of_ne (Ne.symm hs) with hgt | hlt
  · have hrefl : ¬(1 / 2 < (lineReflect s).re) := by
      rw [lineReflect_re]; linarith
    rw [if_neg hrefl, if_pos hgt]
    show (starRingEnd ℂ) ((starRingEnd ℂ) (g (lineReflect (lineReflect s)))) = g s
    rw [lineReflect_involutive, Complex.conj_conj]
  · have hrefl : 1 / 2 < (lineReflect s).re := by
      rw [lineReflect_re]; linarith
    rw [if_pos hrefl, if_neg (by linarith : ¬(1 / 2 < s.re))]
    rfl

/-- The mirror gluing intertwines squaring: gluing the squares is squaring the
gluing. -/
theorem mirrorGlue_sq {g₁ g₂ : ℂ → ℂ} (h : ∀ s ∈ rightHalf, g₂ s ^ 2 = g₁ s) :
    ∀ s ∈ {s : ℂ | s.re ≠ 1 / 2}, mirrorGlue g₂ s ^ 2 = mirrorGlue g₁ s := by
  intro s hs
  show (if 1 / 2 < s.re then g₂ s else mirrorRoot g₂ s) ^ 2 =
    (if 1 / 2 < s.re then g₁ s else mirrorRoot g₁ s)
  rcases lt_or_gt_of_ne (Ne.symm hs) with hgt | hlt
  · rw [if_pos hgt, if_pos hgt]
    exact h s (mem_rightHalf.mpr hgt)
  · rw [if_neg (by linarith : ¬(1 / 2 < s.re)), if_neg (by linarith : ¬(1 / 2 < s.re))]
    show ((starRingEnd ℂ) (g₂ (lineReflect s))) ^ 2 = (starRingEnd ℂ) (g₁ (lineReflect s))
    rw [← map_pow]
    congr 1
    refine h _ ?_
    show 1 / 2 < (lineReflect s).re
    rw [lineReflect_re]; linarith

/-- The mirror gluing of a function agreeing with ξ on the right half-plane agrees
with ξ off the line: ξ's real functional equation supplies the left half. -/
theorem mirrorGlue_eq_xi {g : ℂ → ℂ} (h : ∀ s ∈ rightHalf, g s = xi s) :
    ∀ s ∈ {s : ℂ | s.re ≠ 1 / 2}, mirrorGlue g s = xi s := by
  intro s hs
  show (if 1 / 2 < s.re then g s else mirrorRoot g s) = xi s
  rcases lt_or_gt_of_ne (Ne.symm hs) with hgt | hlt
  · rw [if_pos hgt]
    exact h s (mem_rightHalf.mpr hgt)
  · rw [if_neg (by linarith : ¬(1 / 2 < s.re))]
    have hmem : lineReflect s ∈ rightHalf := by
      rw [mem_rightHalf, lineReflect_re]; linarith
    show (starRingEnd ℂ) (g (lineReflect s)) = xi s
    rw [h _ hmem, xi_lineReflect, Complex.conj_conj]

/-- **The pro-level dissolution.**  Symmetrizing a coherent tower level by level
with the canonical unimodular constants `c_k = conj (g_k a)/‖g_k a‖` yields an
*equivariant* coherent tower: the squaring law at the anchor forces
`c_{k+1}² = c_k`, and a positive anchor forces `c_0 = 1`.  The seam-sign
obstruction does not accumulate in the inverse limit on symmetric regions — the
one bit of every finite level is the same bit, discharged once by the anchor. -/
theorem exists_equivariant_coherentTower_of_anchor_pos {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hUsym : lineReflect ⁻¹' U = U)
    (hsym : ∀ s, f (lineReflect s) = (starRingEnd ℂ) (f s))
    (T : CoherentTower f U)
    {a : ℂ} (haU : a ∈ U) (hare : a.re = 1 / 2) (hfa : 0 < (f a).re) :
    ∃ S : CoherentTower f U, ∀ k, ∀ s ∈ U, mirrorRoot (S.level k) s = S.level k s := by
  have him : (f a).im = 0 := im_eq_zero_at_line_of_lineReflectFE hsym hare
  have hfa0 : f a ≠ 0 := by
    intro h0
    rw [h0] at hfa
    simp at hfa
  have hfeq : f a = ((f a).re : ℂ) := Complex.ext (by simp) (by simpa using him)
  -- level values at the anchor never vanish
  have hlvl0 : ∀ k, T.level k a ≠ 0 := by
    intro k h0
    apply hfa0
    rw [← T.pow_eq k a haU, h0, zero_pow (pow_ne_zero k two_ne_zero)]
  have hNne : ∀ k, ((‖T.level k a‖ : ℝ) : ℂ) ≠ 0 := fun k =>
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hlvl0 k))
  -- the canonical coherent rescaling constants
  set c : ℕ → ℂ := fun k => (starRingEnd ℂ) (T.level k a) / ((‖T.level k a‖ : ℝ) : ℂ)
    with hc
  have hcsq : ∀ k, c (k + 1) ^ 2 = c k := by
    intro k
    rw [hc]
    show ((starRingEnd ℂ) (T.level (k + 1) a) / ((‖T.level (k + 1) a‖ : ℝ) : ℂ)) ^ 2 =
      (starRingEnd ℂ) (T.level k a) / ((‖T.level k a‖ : ℝ) : ℂ)
    rw [div_pow, ← map_pow, ← Complex.ofReal_pow, ← norm_pow, T.sq k a haU]
  have hc0 : c 0 = 1 := by
    rw [hc]
    show (starRingEnd ℂ) (T.level 0 a) / ((‖T.level 0 a‖ : ℝ) : ℂ) = 1
    rw [T.level_zero a haU, Complex.conj_eq_iff_im.mpr him,
      div_eq_one_iff_eq (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hfa0)),
      hfeq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hfa]
  -- the per-level reflection ratios and the key transport identity
  have hkey : ∀ k, (starRingEnd ℂ) (c k) *
      ((starRingEnd ℂ) (T.level k a) / T.level k a) = c k := by
    intro k
    rw [hc]
    show (starRingEnd ℂ)
        ((starRingEnd ℂ) (T.level k a) / ((‖T.level k a‖ : ℝ) : ℂ)) *
        ((starRingEnd ℂ) (T.level k a) / T.level k a) = _
    rw [map_div₀, Complex.conj_conj, Complex.conj_ofReal, div_mul_div_comm,
      mul_comm (T.level k a) ((starRingEnd ℂ) (T.level k a)),
      mul_div_mul_right _ _ (hlvl0 k)]
  refine ⟨⟨fun k s => c k * T.level k s, ?_, ?_, ?_⟩, ?_⟩
  · intro s hs
    show c 0 * T.level 0 s = f s
    rw [hc0, one_mul]
    exact T.level_zero s hs
  · intro k
    exact fun z hz => analyticAt_const.mul (T.analytic k z hz)
  · intro k s hs
    show (c (k + 1) * T.level (k + 1) s) ^ 2 = c k * T.level k s
    rw [mul_pow, hcsq k, T.sq k s hs]
  · intro k s hs
    obtain ⟨-, hEq⟩ := mirrorRoot_ratio (n := 2 ^ k) (pow_pos two_pos k) hU hUc hUsym
      hsym (T.analytic k) (T.pow_eq k) haU hare hfa0
    have hmr : mirrorRoot (T.level k) s =
        ((starRingEnd ℂ) (T.level k a) / T.level k a) * T.level k s := hEq hs
    show (starRingEnd ℂ) (c k * T.level k (lineReflect s)) = c k * T.level k s
    have hunfold : (starRingEnd ℂ) (T.level k (lineReflect s)) =
        mirrorRoot (T.level k) s := rfl
    rw [map_mul, hunfold, hmr, ← mul_assoc, hkey k]

/-- **RH is an off-line equivariant pro-object statement.**  ξ carries a
Schwarz-equivariant coherent ℤ₂-tower off the critical line exactly when the
Riemann Hypothesis holds: a right-half coherent tower (the banked criterion)
glues with its level-wise mirror into an equivariant tower — coherently, since
the gluing intertwines squaring — and conversely the right-half restriction of
an off-line tower is a right-half tower.  The full dyadic pro-object, its
equivariance, and the rung ladder are one statement off the line. -/
theorem rh_iff_xi_equivariant_coherentTower_offline :
    RiemannHypothesis ↔
      ∃ S : CoherentTower xi {s : ℂ | s.re ≠ 1 / 2},
        ∀ k, ∀ s ∈ {s : ℂ | s.re ≠ 1 / 2}, mirrorRoot (S.level k) s = S.level k s := by
  constructor
  · intro hRH
    obtain ⟨T⟩ := rh_iff_xi_coherentTower_rightHalf.mp hRH
    exact ⟨⟨fun k => mirrorGlue (T.level k),
        mirrorGlue_eq_xi T.level_zero,
        fun k => mirrorGlue_analyticOnNhd (T.analytic k),
        fun k => mirrorGlue_sq (T.sq k)⟩,
      fun k => mirrorGlue_equivariant (T.level k)⟩
  · rintro ⟨S, -⟩
    refine rh_iff_xi_coherentTower_rightHalf.mpr ⟨⟨S.level, ?_, ?_, ?_⟩⟩
    · exact fun s hs => S.level_zero s (ne_of_gt (mem_rightHalf.mp hs))
    · exact fun k => (S.analytic k).mono fun s hs => ne_of_gt (mem_rightHalf.mp hs)
    · exact fun k s hs => S.sq k s (ne_of_gt (mem_rightHalf.mp hs))

end RHTower
