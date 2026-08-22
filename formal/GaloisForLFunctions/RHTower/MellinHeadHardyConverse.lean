import GaloisForLFunctions.RHTower.MellinHardyClasses
import GaloisForLFunctions.HTGeometry.HalfPlaneHardyShift

/-!
# The head half of Burnol's Proposition 4.1

`MellinHardyClasses` shows that a datum `c·1_{(0,a)} + g` with `g ∈ L²(a,∞)` has renormalised
Mellin transform in the Hardy space, i.e. lies in Burnol's `s/(s-1)·A^s H²`.  This module proves
the converse: every element of `s/(s-1)·A^s H²` is such a transform.

The mechanism is a single partial-fraction identity.  Write `w = s - 1/2`, `u = w - 1/2 = s - 1`,
`v = w + 1/2 = s`, so `v - u = 1`, and let `G` be the Hardy representative, i.e.
`G(w) = (u/v)·a^w F(s)`.  With `κ := -G(1/2)` the function `Ψ(w) := G(w) + κ/v` is Hardy and
vanishes at `w = 1/2`, so `Q := Ψ/u` is Hardy as well (`exists_isHalfPlaneHardy_div_pow`).  Then

`G + Q + κ/v = G·(1 + 1/u) + (κ/v)(1 + 1/u) = (G + κ/v)·v/u = a^w F(s) + κ/u`,

so `a^w F(s)` differs from a Hardy function by the explicit simple pole `κ/(s-1)`.  Paley--Wiener
converts the Hardy part into a tail datum and the pole into the constant head.

## Main results

* `exists_head_tail_of_isMellinHeadHardy` — **Burnol's Proposition 4.1, head half**
-/

noncomputable section

open MeasureTheory Set

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- **Every element of `s/(s-1)·A^s H²` is the Mellin transform of a constant head plus a
square-integrable tail.** -/
theorem exists_head_tail_of_isMellinHeadHardy {a : ℝ} (ha : 0 < a) {F : ℂ → ℂ}
    (hF : IsMellinHeadHardy a F) :
    ∃ (c : ℂ) (g : ℝ → ℂ), MemLp g 2 (volume.restrict (Ioi a)) ∧
      ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 →
        F s = c * ((a : ℝ) : ℂ) ^ (1 - s) / (1 - s)
              + ∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-s) * g t := by
  obtain ⟨G, M, hGH, hGeq⟩ := hF
  set κ : ℂ := -G (1 / 2) with hκ
  have hhalf_re : (0 : ℝ) < ((1 : ℂ) / 2).re := by norm_num
  set Ψ : ℂ → ℂ := fun w => G w + κ * (w + 1 / 2)⁻¹ with hΨdef
  obtain ⟨MΨ, hΨH⟩ : ∃ N : ℝ, IsHalfPlaneHardy Ψ N :=
    ⟨_, isHalfPlaneHardy_add hGH
      (isHalfPlaneHardy_const_mul (isHalfPlaneHardy_inv_shift hhalf_re) κ)⟩
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hΨana : AnalyticAt ℂ Ψ (1 / 2) :=
    hΨH.holo.analyticAt (hopen.mem_nhds hhalf_re)
  have hΨzero : Ψ (1 / 2) = 0 := by
    rw [hΨdef, hκ]
    norm_num
  have hord : (1 : ℕ∞) ≤ analyticOrderAt Ψ (1 / 2) := by
    rw [Order.one_le_iff_ne_zero]
    intro h0
    exact (hΨana.analyticOrderAt_eq_zero.1 h0) hΨzero
  obtain ⟨Q, NQ, hQH, hQeq⟩ := exists_isHalfPlaneHardy_div_pow hΨH hΨana hord
  set D : ℂ → ℂ := fun w => G w + (Q w + κ * (w + 1 / 2)⁻¹) with hDdef
  obtain ⟨MD, hDH⟩ : ∃ N : ℝ, IsHalfPlaneHardy D N :=
    ⟨_, isHalfPlaneHardy_add hGH (isHalfPlaneHardy_add hQH
      (isHalfPlaneHardy_const_mul (isHalfPlaneHardy_inv_shift hhalf_re) κ))⟩
  obtain ⟨g, hg, hgeq⟩ := exists_tail_datum_of_isHalfPlaneHardy ha hDH
  refine ⟨κ * ((a : ℝ) : ℂ) ^ (-(1 / 2) : ℂ), g, hg, fun s hs hs1 => ?_⟩
  have hane : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  set w : ℂ := s - 1 / 2 with hwdef
  have hw : 0 < w.re := by
    rw [hwdef, Complex.sub_re]
    have : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
    rw [this]
    linarith
  have hwne : w ≠ 1 / 2 := by
    intro h
    exact hs1 (by rw [hwdef] at h; linear_combination h)
  have hws : w + 1 / 2 = s := by rw [hwdef]; ring
  have hwu : w - 1 / 2 = s - 1 := by rw [hwdef]; ring
  have hune : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  have hvne : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  -- the two structural identities
  have hG : G w = ((s - 1) / s) * (((a : ℝ) : ℂ) ^ w * F s) := by
    have := hGeq w hw hwne
    rwa [hws, hwu] at this
  have hQ : Q w * (s - 1) = G w + κ * s⁻¹ := by
    have := hQeq w hw hwne
    rw [pow_one, hwu] at this
    rw [this, hΨdef]
    simp only
    rw [hws]
  -- the partial-fraction collapse
  have hD : D w = ((a : ℝ) : ℂ) ^ w * F s + κ * (s - 1)⁻¹ := by
    have hQval : Q w = (G w + κ * s⁻¹) * (s - 1)⁻¹ := by
      field_simp at hQ ⊢
      linear_combination hQ
    rw [hDdef]
    simp only
    rw [hws, hQval, hG]
    field_simp
    ring
  -- solve for `F s`
  have hpow : ((a : ℝ) : ℂ) ^ w ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hane)
  have hFs : F s = (((a : ℝ) : ℂ) ^ w)⁻¹ * (D w - κ * (s - 1)⁻¹) := by
    rw [hD]
    field_simp
    ring
  have hinv : (((a : ℝ) : ℂ) ^ w)⁻¹ = ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s) := by
    rw [← Complex.cpow_neg]
    congr 1
    rw [hwdef]
    ring
  have htail : (∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-s) * g t)
      = ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s) * D w := by
    rw [hgeq s hs, hwdef]
  have hhead : κ * ((a : ℝ) : ℂ) ^ (-(1 / 2) : ℂ) * ((a : ℝ) : ℂ) ^ (1 - s) / (1 - s)
      = -(((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s) * (κ * (s - 1)⁻¹)) := by
    have hmul : ((a : ℝ) : ℂ) ^ (-(1 / 2) : ℂ) * ((a : ℝ) : ℂ) ^ (1 - s)
        = ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s) := by
      rw [← Complex.cpow_add _ _ hane]
      congr 1
      ring
    have hsub : (1 : ℂ) - s ≠ 0 := by
      intro h
      exact hs1 (by linear_combination -h)
    rw [mul_assoc, hmul]
    field_simp
    ring
  rw [hFs, hinv, htail, hhead]
  field_simp
  ring

end RHTower

end
