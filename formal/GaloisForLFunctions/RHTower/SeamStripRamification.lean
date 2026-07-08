/-
Where the off-line ramification can live: the prime-local and archimedean factors are zero-free in
the open critical strip, so the strip ramification divisor of the natural completed-zeta building
blocks is carried entirely by ζ itself.

The off-line correspondence sought by the seam program would need a ramified/fixed locus off the
critical line but *inside* the strip `0 < Re s < 1` (that is where the carrier residual — the
possible off-line zeros — lives).  The candidate raw materials are the canonical `𝓜⁺` factors of the
completed zeta: the archimedean factor `Γℝ`, and the prime-local Euler factors `1 − p^{−s}`.  This
file proves both are **zero-free and pole-free in the strip**:

* `euler_factor_ne_zero_of_re_pos` — `1 − p^{−s} ≠ 0` for `Re s > 0` (hence throughout the strip):
  `‖p^{−s}‖ = p^{−Re s} < 1`, so `p^{−s} ≠ 1`.  The prime shifts contribute **no** strip ramification.
* `gammaR_ne_zero_of_mem_strip` — `Γℝ s ≠ 0` in the strip (`Γ` never vanishes).
* `xi_zero_iff_zeta_zero_of_mem_strip` — in the strip, `ξ s = 0 ↔ ζ s = 0`: the entire completed
  zeta and the raw Dirichlet series share exactly their strip zeros, because the killed factors
  `s(s−1)/2` and `Γℝ` are non-vanishing there.

Consequence (constraint, not flow): any ramified locus of a correspondence assembled from these
factors that lands off the line but inside the strip must coincide with a zero of ζ.  Ramifying
there is the double cover `w² = ξ` — the `√ξ` flow the program forbids constructing.  The prime
shifts, being purely imaginary translations, cannot move a reflection centre off `Re = 1/2` either
(`reflection_center_re_eq_half_of_imaginary_offset`); so neither the fixed-locus route nor the
ramification route reaches off-line through the canonical factors.  What remains genuinely open is
whether a *non-factor* `𝓜⁺` object (a derivative in `∂_s`, a twist) can, which is the continuing
frontier, not something these factors settle.
-/
import GaloisForLFunctions.RHTower.SeamRealAxisGrowth

open Complex Real

namespace RHTower

/-! ### §1 The prime-local factor is zero-free in the right half-plane -/

/-- **The Euler factor carries no ramification in the right half-plane.**  For a prime (indeed any
integer `p ≥ 2`) and `Re s > 0`, `1 − p^{−s} ≠ 0`, because `‖p^{−s}‖ = p^{−Re s} < 1`.  The prime
shift `σ_p` thus contributes no zero — no ramification — anywhere in the open critical strip. -/
theorem euler_factor_ne_zero_of_re_pos {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    (1 : ℂ) - (p:ℂ)^(-s) ≠ 0 := by
  have hp0 : 0 < p := by omega
  have hp1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast hp
  have hnorm : ‖(p:ℂ)^(-s)‖ = (p:ℝ)^(-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos hp0]; simp [Complex.neg_re]
  have hlt : ‖(p:ℂ)^(-s)‖ < 1 := by
    rw [hnorm]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by simp [hs])
  intro h
  rw [sub_eq_zero] at h
  rw [← h] at hlt
  simp at hlt

/-! ### §2 The archimedean factor is zero-free in the strip -/

/-- `Γℝ` is non-vanishing in the open critical strip (indeed for `Re s > 0`): `Γ` has no zeros. -/
theorem gammaR_ne_zero_of_mem_strip {s : ℂ} (h0 : 0 < s.re) (_h1 : s.re < 1) :
    Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos h0

/-! ### §3 The strip ramification is carried by ζ -/

/-- **In the open strip, ξ and ζ share exactly their zeros.**  For `0 < Re s < 1`, `ξ s = 0 ↔
ζ s = 0`: the factors `s(s−1)/2` and `Γℝ s` that relate `ξ` to `ζ` are non-vanishing there (`s ≠ 0`,
`s ≠ 1`, and `Γℝ` zero-free), so the entire completed zeta and the raw Dirichlet series have the
same strip ramification divisor — all of it off the archimedean and prime-local factors. -/
theorem xi_zero_iff_zeta_zero_of_mem_strip {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    xi s = 0 ↔ riemannZeta s = 0 := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at h0; simp at h0
  have hs1 : s ≠ 1 := by intro h; rw [h] at h1; simp at h1
  have hgR : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos h0
  have hLam : completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
    rw [riemannZeta_def_of_ne_zero hs0]; field_simp
  have hpre : s * (s - 1) / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) (by norm_num)
  rw [xi_eq_half_mul_completed hs0 hs1, hLam]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hpre
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact h''
      · exact absurd h'' hgR
  · intro h
    rw [h]; ring

/-! ### §4 Prime shifts cannot move a reflection centre off the line -/

/-- **Imaginary offsets keep the reflection centre on the line.**  The functional equation is the
reflection `s ↦ 1 − s`, centred at `1/2`.  Twisting the offset by the purely-imaginary prime period
`iβ` gives `s ↦ (1 + iβ) − s`, whose centre `(1 + iβ)/2` still has real part `1/2`.  A prime shift,
being an imaginary translation, cannot produce an off-line fixed locus: it moves the centre
vertically along the critical line, never off it. -/
theorem reflection_center_re_eq_half_of_imaginary_offset (β : ℝ) :
    (((1 : ℂ) + (β:ℝ)*I) / 2).re = 1 / 2 := by
  rw [Complex.div_re]
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.normSq]

end RHTower
