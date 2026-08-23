import GaloisForLFunctions.RHTower.MellinHeadHardyConverse
import GaloisForLFunctions.RHTower.MellinHeadHardy

/-!
# Burnol's Proposition 4.1, head half, as an equivalence

`MellinHeadHardy` produces the Hardy representative of the renormalised Mellin transform of a
datum `c·1_{(0,a)} + g`, and `MellinHeadHardyConverse` recovers such a datum from an arbitrary
element of `s/(s-1)·A^s H²`.  This module packages the two into a single equivalence, phrased
through the meromorphic continuation

`headTailMellin a c g s = c·a^{1-s}/(1-s) + ∫_a^∞ g(t) t^{-s} dt`,

which agrees with the honest Mellin integral on `Re s < 1` and continues it to the whole
half-plane `Re s > 1/2` minus the point `s = 1`.

## Main results

* `headTailMellin`, `headTailMellin_eq_mellin`
* `isMellinHeadHardy_headTailMellin`
* `isMellinHeadHardy_iff` — **Burnol's Proposition 4.1, head half**
-/

noncomputable section

open MeasureTheory Set

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The meromorphic continuation of the Mellin transform of a constant head plus an `L²` tail. -/
def headTailMellin (a : ℝ) (c : ℂ) (g : ℝ → ℂ) (s : ℂ) : ℂ :=
  c * ((a : ℝ) : ℂ) ^ (1 - s) / (1 - s) + ∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-s) * g t

/-- On `Re s < 1` the continuation is the honest Mellin integral. -/
theorem headTailMellin_eq_mellin {a : ℝ} (ha : 0 < a) (c : ℂ) (g : ℝ → ℂ) {s : ℂ}
    (hs : s.re < 1) :
    headTailMellin a c g s
      = (∫ t in Ioc (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * c)
        + ∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-s) * g t := by
  rw [headTailMellin, integral_head_cpow_Ioc ha hs c]

/-- **The forward half of Proposition 4.1.** -/
theorem isMellinHeadHardy_headTailMellin {a : ℝ} (ha : 0 < a) (c : ℂ) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (Ioi a))) :
    IsMellinHeadHardy a (headTailMellin a c g) := by
  obtain ⟨M, hM⟩ := isHalfPlaneHardy_renormalisedHeadTail ha c hg
  refine ⟨_, M, hM, fun w hw hwne => ?_⟩
  have hane : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  have hvne : w + 1 / 2 ≠ 0 := by
    intro h
    have hre : (w + 1 / 2).re = 0 := by rw [h]; simp
    rw [Complex.add_re] at hre
    have h2 : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
    rw [h2] at hre
    linarith
  have hune : w - 1 / 2 ≠ 0 := sub_ne_zero.2 hwne
  have hp1 : ((a : ℝ) : ℂ) ^ w * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - w)
      = ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2) := by
    rw [← Complex.cpow_add _ _ hane]
    congr 1
    ring
  have hp2 : ((a : ℝ) : ℂ) ^ w * ((a : ℝ) : ℂ) ^ (-w) = 1 := by
    rw [← Complex.cpow_add _ _ hane]
    rw [show w + -w = (0 : ℂ) from by ring, Complex.cpow_zero]
  have htail := mellinTail_eq_laplaceRay ha g (w + 1 / 2)
  have e1 : (1 : ℂ) - (w + 1 / 2) = 1 / 2 - w := by ring
  have e2 : (1 : ℂ) / 2 - (w + 1 / 2) = -w := by ring
  have e3 : (w + 1 / 2) - 1 / 2 = w := by ring
  rw [e2, e3] at htail
  have hexp : headTailMellin a c g (w + 1 / 2)
      = c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - w) / ((1 : ℂ) / 2 - w)
        + ((a : ℝ) : ℂ) ^ (-w) * laplaceRay (logChart a g) w := by
    rw [headTailMellin, e1, htail]
  rw [hexp]
  have hkey : ((a : ℝ) : ℂ) ^ w
      * (c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - w) / ((1 : ℂ) / 2 - w)
        + ((a : ℝ) : ℂ) ^ (-w) * laplaceRay (logChart a g) w)
      = c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2) / ((1 : ℂ) / 2 - w)
        + laplaceRay (logChart a g) w := by
    rw [mul_add]
    congr 1
    · rw [show ((a : ℝ) : ℂ) ^ w * (c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - w) / ((1 : ℂ) / 2 - w))
            = c * (((a : ℝ) : ℂ) ^ w * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - w)) / ((1 : ℂ) / 2 - w)
          from by ring, hp1]
    · rw [← mul_assoc, hp2, one_mul]
  have hhalfne : (1 : ℂ) / 2 - w ≠ 0 := by
    intro h
    exact hwne (by linear_combination -h)
  have hratio : (w - 1 / 2) / ((1 : ℂ) / 2 - w) = -1 := by
    rw [div_eq_iff hhalfne]
    ring
  rw [hkey, mul_add]
  congr 1
  rw [show (w - 1 / 2) / (w + 1 / 2) * (c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2) / ((1 : ℂ) / 2 - w))
        = ((w - 1 / 2) / ((1 : ℂ) / 2 - w))
          * (c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2) / (w + 1 / 2)) from by ring, hratio]
  ring

/-- **Burnol's Proposition 4.1, head half.**  A function lies in `s/(s-1)·A^s H²` exactly when it
is, on `Re s > 1/2` off the point `s = 1`, the continued Mellin transform of a constant head of
aperture `a` plus a square-integrable tail. -/
theorem isMellinHeadHardy_iff {a : ℝ} (ha : 0 < a) (F : ℂ → ℂ) :
    IsMellinHeadHardy a F ↔
      ∃ (c : ℂ) (g : ℝ → ℂ), MemLp g 2 (volume.restrict (Ioi a)) ∧
        ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → F s = headTailMellin a c g s := by
  constructor
  · intro hF
    obtain ⟨c, g, hg, heq⟩ := exists_head_tail_of_isMellinHeadHardy ha hF
    exact ⟨c, g, hg, fun s hs hs1 => by rw [heq s hs hs1, headTailMellin]⟩
  · rintro ⟨c, g, hg, heq⟩
    obtain ⟨H, M, hMH, hHeq⟩ := isMellinHeadHardy_headTailMellin ha c hg
    refine ⟨H, M, hMH, fun w hw hwne => ?_⟩
    have hs : 1 / 2 < (w + 1 / 2).re := by
      rw [Complex.add_re]
      have h2 : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
      rw [h2]
      linarith
    have hs1 : w + 1 / 2 ≠ 1 := by
      intro h
      exact hwne (by linear_combination h)
    rw [hHeq w hw hwne, heq (w + 1 / 2) hs hs1]

/-- `A^s H²` only sees the half-plane `Re s > 1/2`. -/
theorem IsMellinTailHardy.congr' {a : ℝ} {F G : ℂ → ℂ} (h : IsMellinTailHardy a F)
    (heq : ∀ s : ℂ, 1 / 2 < s.re → F s = G s) : IsMellinTailHardy a G := by
  obtain ⟨M, hM⟩ := h
  refine ⟨M, hM.congr (fun w hw => ?_)⟩
  have hs : 1 / 2 < (w + 1 / 2).re := by
    rw [Complex.add_re]
    have h2 : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
    rw [h2]
    linarith
  rw [heq (w + 1 / 2) hs]

/-- **The `K_a` companion of Proposition 4.1.**  A function lies in `A^s H²` exactly when it is,
on `Re s > 1/2`, the Mellin transform of a square-integrable tail datum of aperture `a`. -/
theorem isMellinTailHardy_iff {a : ℝ} (ha : 0 < a) (F : ℂ → ℂ) :
    IsMellinTailHardy a F ↔
      ∃ f : ℝ → ℂ, MemLp f 2 (volume.restrict (Ioi a)) ∧
        ∀ s : ℂ, 1 / 2 < s.re → F s = ∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-s) * f t := by
  constructor
  · intro hF
    obtain ⟨f, hf, heq⟩ := exists_memLp_of_isMellinTailHardy ha hF
    exact ⟨f, hf, fun s hs => (heq s hs).symm⟩
  · rintro ⟨f, hf, heq⟩
    exact (isMellinTailHardy_mellinTail ha hf).congr' (fun s hs => (heq s hs).symm)

end RHTower

end
