import GaloisForLFunctions.RHTower.MellinHeadHardy

/-!
# Burnol's Mellin Hardy classes

`A^s H²` is the space of right Mellin transforms of `L²(a,∞;dt)`, and `s/(s-1)A^sH²` the space of
right Mellin transforms of `ℂ·1_{(0,a)} + L²(a,∞;dt)`.  In the half-plane variable `w = s - 1/2`
membership is Hardy membership of `a^w F(w+1/2)`, respectively of `((w-1/2)/(w+1/2))·a^w F(w+1/2)`.
Because a function of the second class may have a pole at `s = 1`, the second class is defined
through a Hardy representative which agrees with the renormalised transform away from `s = 1`.

## Main results

* `IsMellinTailHardy`, `IsMellinHeadHardy`
* `isMellinTailHardy_mellinTail`
* `IsMellinTailHardy.div_id`, `IsMellinTailHardy.div_one_sub` — Burnol's Lemma 4.4
* `IsMellinTailHardy.div_sub` — Burnol's Proposition 4.3, `K_a` half
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Burnol's `A^s H²`.**  `a^{s-1/2}F(s)` is a Hardy function of `w = s - 1/2`. -/
def IsMellinTailHardy (a : ℝ) (F : ℂ → ℂ) : Prop :=
  ∃ M : ℝ, IsHalfPlaneHardy (fun w : ℂ => ((a : ℝ) : ℂ) ^ w * F (w + 1 / 2)) M

/-- **Burnol's `s/(s-1) A^s H²`.**  The renormalised transform `((s-1)/s)a^{s-1/2}F(s)` has a Hardy
representative, which it equals away from the possible pole at `s = 1`. -/
def IsMellinHeadHardy (a : ℝ) (F : ℂ → ℂ) : Prop :=
  ∃ (H : ℂ → ℂ) (M : ℝ), IsHalfPlaneHardy H M ∧
    ∀ w : ℂ, 0 < w.re → w ≠ 1 / 2 →
      H w = ((w - 1 / 2) / (w + 1 / 2)) * (((a : ℝ) : ℂ) ^ w * F (w + 1 / 2))

/-- The Mellin transform of a square-integrable tail datum lies in `A^s H²`. -/
theorem isMellinTailHardy_mellinTail {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioi a))) :
    IsMellinTailHardy a (fun s => ∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-s) * f t) := by
  have hane : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  refine ⟨_, (isHalfPlaneHardy_mellinTail ha hf).congr (fun w _ => ?_)⟩
  show laplaceRay (logChart a f) w
    = ((a : ℝ) : ℂ) ^ w * ∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-(w + 1 / 2)) * f t
  rw [mellinTail_eq_laplaceRay ha f (w + 1 / 2)]
  have hcancel : ((a : ℝ) : ℂ) ^ w * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - (w + 1 / 2)) = 1 := by
    rw [← Complex.cpow_add _ _ hane]
    have hzero : w + ((1 : ℂ) / 2 - (w + 1 / 2)) = 0 := by ring
    rw [hzero, Complex.cpow_zero]
  have hsub : (w + 1 / 2) - 1 / 2 = w := by ring
  rw [hsub]
  calc laplaceRay (logChart a f) w
      = (((a : ℝ) : ℂ) ^ w * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - (w + 1 / 2)))
        * laplaceRay (logChart a f) w := by rw [hcancel, one_mul]
    _ = ((a : ℝ) : ℂ) ^ w
        * (((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - (w + 1 / 2)) * laplaceRay (logChart a f) w) := by ring

theorem shiftHalf_ne_zero {w : ℂ} (hw : 0 < w.re) : w + 1 / 2 ≠ 0 := by
  intro hzero
  have h : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
  have hre : (w + 1 / 2).re = 0 := by rw [hzero]; simp
  rw [Complex.add_re, h] at hre
  linarith

/-- `A^s H²` sits inside `s/(s-1)A^sH²`. -/
theorem IsMellinTailHardy.isMellinHeadHardy {a : ℝ} {F : ℂ → ℂ} (h : IsMellinTailHardy a F) :
    IsMellinHeadHardy a F := by
  obtain ⟨M, hM⟩ := h
  refine ⟨_, _, isHalfPlaneHardy_mul_of_bounded hM differentiableOn_shift_ratio
    (C := 3) (fun w hw => norm_shift_ratio_le hw), fun w _ _ => ?_⟩
  ring

/-- **Burnol's Lemma 4.4, first half.**  Dividing by `s` stays in `A^s H²`. -/
theorem IsMellinTailHardy.div_id {a : ℝ} {F : ℂ → ℂ} (h : IsMellinTailHardy a F) :
    IsMellinTailHardy a (fun s => F s / s) := by
  obtain ⟨M, hM⟩ := h
  have hhalf : (0 : ℝ) < ((1 : ℂ) / 2).re := by norm_num
  refine ⟨_, (isHalfPlaneHardy_mul_inv_shift hM hhalf).congr (fun w hw => ?_)⟩
  have hne : w + 1 / 2 ≠ 0 := shiftHalf_ne_zero hw
  field_simp

/-- **Burnol's Lemma 4.4, second half.**  `G(s)/(1-s)` lands in `s/(s-1)A^sH²`. -/
theorem IsMellinTailHardy.div_one_sub {a : ℝ} {G : ℂ → ℂ} (h : IsMellinTailHardy a G) :
    IsMellinHeadHardy a (fun s => G s / (1 - s)) := by
  obtain ⟨M, hM⟩ := h
  have hhalf : (0 : ℝ) < ((1 : ℂ) / 2).re := by norm_num
  have h2 := isHalfPlaneHardy_mul_inv_shift hM hhalf
  have h3 := isHalfPlaneHardy_const_mul h2 (-1 : ℂ)
  refine ⟨_, _, h3, fun w hw hw1 => ?_⟩
  have hne : w + 1 / 2 ≠ 0 := shiftHalf_ne_zero hw
  have hne3 : w - (1 : ℂ) / 2 ≠ 0 := by
    intro hzero
    exact hw1 (by linear_combination hzero)
  have hval : (1 : ℂ) - (w + 1 / 2) = -(w - 1 / 2) := by ring
  show (-1 : ℂ) * (((a : ℝ) : ℂ) ^ w * G (w + 1 / 2) * (w + 1 / 2)⁻¹)
    = ((w - 1 / 2) / (w + 1 / 2)) * (((a : ℝ) : ℂ) ^ w * (G (w + 1 / 2) / (1 - (w + 1 / 2))))
  symm
  rw [hval]
  have h1 : G (w + 1 / 2) / (-(w - 1 / 2)) = -(G (w + 1 / 2) * (w - 1 / 2)⁻¹) := by
    rw [div_neg, div_eq_mul_inv]
  have h2 : (w - 1 / 2) * (w - 1 / 2)⁻¹ = 1 := mul_inv_cancel₀ hne3
  rw [h1, div_eq_mul_inv]
  calc ((w - 1 / 2) * (w + 1 / 2)⁻¹)
        * (((a : ℝ) : ℂ) ^ w * -(G (w + 1 / 2) * (w - 1 / 2)⁻¹))
      = -(((w - 1 / 2) * (w - 1 / 2)⁻¹)
          * (((a : ℝ) : ℂ) ^ w * G (w + 1 / 2) * (w + 1 / 2)⁻¹)) := by ring
    _ = -((1 : ℂ) * (((a : ℝ) : ℂ) ^ w * G (w + 1 / 2) * (w + 1 / 2)⁻¹)) := by rw [h2]
    _ = (-1 : ℂ) * (((a : ℝ) : ℂ) ^ w * G (w + 1 / 2) * (w + 1 / 2)⁻¹) := by ring

/-- **Burnol's Proposition 4.3, `K_a` half.**  Dividing by a zero of the required order stays in
`A^s H²`. -/
theorem IsMellinTailHardy.div_sub {a : ℝ} {G H : ℂ → ℂ} (hG : IsMellinTailHardy a G)
    {ρ : ℂ} {l : ℕ} {B δ : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B)
    (hHhol : DifferentiableOn ℂ (fun w : ℂ => ((a : ℝ) : ℂ) ^ w * H (w + 1 / 2))
      {w : ℂ | 0 < w.re})
    (hHB : ∀ w : ℂ, 0 < w.re → ‖w - (ρ - 1 / 2)‖ < δ →
      ‖((a : ℝ) : ℂ) ^ w * H (w + 1 / 2)‖ ≤ B)
    (hHeq : ∀ s : ℂ, 1 / 2 < s.re → s ≠ ρ → H s * (s - ρ) ^ l = G s) :
    IsMellinTailHardy a H := by
  obtain ⟨M, hM⟩ := hG
  refine isHalfPlaneHardy_of_div_pow_bounded (l := l) hM hHhol hB hδ hHB (fun w hw hwne => ?_)
  have hre : (1 : ℝ) / 2 < (w + 1 / 2).re := by
    have h : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
    rw [Complex.add_re, h]
    linarith
  have hne : w + 1 / 2 ≠ ρ := by
    intro hzero
    exact hwne (by linear_combination hzero)
  have hshift : w - (ρ - 1 / 2) = (w + 1 / 2) - ρ := by ring
  rw [hshift, mul_assoc, hHeq (w + 1 / 2) hre hne]

/-- **The Paley--Wiener identification, converse direction.**  Every element of `A^s H²` is the
right Mellin transform of a square-integrable tail datum. -/
theorem exists_memLp_of_isMellinTailHardy {a : ℝ} (ha : 0 < a) {F : ℂ → ℂ}
    (hF : IsMellinTailHardy a F) :
    ∃ f : ℝ → ℂ, MemLp f 2 (volume.restrict (Ioi a)) ∧
      ∀ s : ℂ, 1 / 2 < s.re → (∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-s) * f t) = F s := by
  have hane : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  obtain ⟨M, hM⟩ := hF
  obtain ⟨f, hf, hval⟩ := exists_tail_datum_of_isHalfPlaneHardy ha hM
  refine ⟨f, hf, fun s hs => ?_⟩
  rw [hval s hs]
  have hsub : s - 1 / 2 + 1 / 2 = s := by ring
  have hcancel : ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s) * ((a : ℝ) : ℂ) ^ (s - 1 / 2) = 1 := by
    rw [← Complex.cpow_add _ _ hane]
    have hzero : ((1 : ℂ) / 2 - s) + (s - 1 / 2) = 0 := by ring
    rw [hzero, Complex.cpow_zero]
  show ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s) * (((a : ℝ) : ℂ) ^ (s - 1 / 2) * F (s - 1 / 2 + 1 / 2))
    = F s
  rw [hsub, ← mul_assoc, hcancel, one_mul]


end

end RHTower
