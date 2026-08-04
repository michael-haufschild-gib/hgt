import Mathlib

/-!
# The image of a disc meets every circle below the maximum

If a continuous function vanishes at the centre of a disc, the image of the radius towards any point
is a connected set joining `0` to that point's value, so by the intermediate value theorem every
modulus between `0` and that value is attained inside the disc.

Composed with a lower bound for an outer function on a circle, this is the growth step behind
composition estimates: the outer function is evaluated somewhere on that circle, so the composition
inherits the outer function's minimum there.
-/

open Metric Set

namespace GaloisForLFunctions.HTGeometry

/-- **Every modulus below an attained one is attained.**  A continuous function vanishing at the
centre of a disc attains every modulus between `0` and `‖g z₀‖` for any `z₀` in the disc. -/
theorem exists_norm_eq_of_segment {g : ℂ → ℂ} {r : ℝ} {z₀ : ℂ}
    (hcont : ContinuousOn g (closedBall 0 r)) (hz₀ : z₀ ∈ closedBall 0 r)
    (hg0 : g 0 = 0) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ ‖g z₀‖) :
    ∃ z ∈ closedBall 0 r, ‖g z‖ = s := by
  have hz₀norm : ‖z₀‖ ≤ r := by
    simpa [mem_closedBall, dist_eq_norm] using hz₀
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, ((t : ℂ) * z₀) ∈ closedBall 0 r := by
    intro t ht
    have habs : ‖(t : ℂ) * z₀‖ = |t| * ‖z₀‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have habs' : |t| = t := abs_of_nonneg ht.1
    have : ‖(t : ℂ) * z₀‖ ≤ ‖z₀‖ := by
      rw [habs, habs']
      nlinarith [ht.1, ht.2, norm_nonneg z₀]
    simpa [mem_closedBall, dist_eq_norm] using le_trans this hz₀norm
  have hmap : ContinuousOn (fun t : ℝ => ((t : ℂ) * z₀)) (Icc (0 : ℝ) 1) := by
    fun_prop
  have hphi : ContinuousOn (fun t : ℝ => ‖g ((t : ℂ) * z₀)‖) (Icc (0 : ℝ) 1) :=
    ((hcont.comp hmap hseg)).norm
  have h0 : ‖g (((0 : ℝ) : ℂ) * z₀)‖ = 0 := by
    simp [hg0]
  have h1 : ‖g (((1 : ℝ) : ℂ) * z₀)‖ = ‖g z₀‖ := by
    simp
  have hsub := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hphi
  have hmem : s ∈ Icc (‖g (((0 : ℝ) : ℂ) * z₀)‖) (‖g (((1 : ℝ) : ℂ) * z₀)‖) := by
    rw [h0, h1]
    exact ⟨hs0, hs⟩
  obtain ⟨t, ht, hts⟩ := hsub hmem
  exact ⟨(t : ℂ) * z₀, hseg t ht, hts⟩

/-- **A composition inherits an outer lower bound on a circle.**  If the inner function vanishes at
the centre and reaches modulus at least `s` somewhere in the disc, and the outer function is at least
`L` on the circle of radius `s`, then the composition reaches `L` inside the disc. -/
theorem exists_le_norm_comp {f g : ℂ → ℂ} {r s L : ℝ} {z₀ : ℂ}
    (hcont : ContinuousOn g (closedBall 0 r)) (hz₀ : z₀ ∈ closedBall 0 r)
    (hg0 : g 0 = 0) (hs0 : 0 ≤ s) (hs : s ≤ ‖g z₀‖)
    (hL : ∀ w : ℂ, ‖w‖ = s → L ≤ ‖f w‖) :
    ∃ z ∈ closedBall 0 r, L ≤ ‖f (g z)‖ := by
  obtain ⟨z, hz, hzs⟩ := exists_norm_eq_of_segment hcont hz₀ hg0 hs0 hs
  exact ⟨z, hz, hL (g z) hzs⟩

/-! ## Pointwise separation -/

/-- **Pointwise composition separation.**  If the inner function is bounded by `Mg` on the disc and
reaches modulus `s`, and the outer function is at least `L` on the circle of radius `s`, then at some
point of the disc the composition's weight exceeds any prescribed multiple of the inner function's
weight — provided `L` beats that multiple of `Mg` logarithmically.

This is the form a growth-separation hypothesis takes when it is stated pointwise: no comparison
between the maximum modulus and the Nevanlinna characteristic is involved. -/
theorem exists_posLog_separation {f g : ℂ → ℂ} {r s L Mg C : ℝ} {z₀ : ℂ}
    (hcont : ContinuousOn g (closedBall 0 r)) (hz₀ : z₀ ∈ closedBall 0 r)
    (hg0 : g 0 = 0) (hs0 : 0 ≤ s) (hs : s ≤ ‖g z₀‖)
    (hL : ∀ w : ℂ, ‖w‖ = s → L ≤ ‖f w‖) (hL0 : 0 ≤ L)
    (hMg : ∀ z ∈ closedBall 0 r, ‖g z‖ ≤ Mg)
    (hC : 0 ≤ C) (hsep : C * Real.posLog Mg < Real.posLog L) :
    ∃ z ∈ closedBall 0 r, C * Real.posLog ‖g z‖ < Real.posLog ‖f (g z)‖ := by
  obtain ⟨z, hz, hzs⟩ := exists_norm_eq_of_segment hcont hz₀ hg0 hs0 hs
  refine ⟨z, hz, ?_⟩
  have hglow : Real.posLog ‖g z‖ ≤ Real.posLog Mg :=
    Real.posLog_le_posLog (norm_nonneg _) (hMg z hz)
  have hLle : L ≤ ‖f (g z)‖ := hL (g z) hzs
  have hLpos : Real.posLog L ≤ Real.posLog ‖f (g z)‖ :=
    Real.posLog_le_posLog hL0 hLle
  have hmul : C * Real.posLog ‖g z‖ ≤ C * Real.posLog Mg :=
    mul_le_mul_of_nonneg_left hglow hC
  linarith

/-- **Separation from a logarithmic floor.**  The same statement with the outer bound given as a
floor for `log ‖f‖` on the circle — the form the minimum-modulus theorem produces.  No positivity of
the outer function is needed: the positive logarithm dominates the logarithm in every case. -/
theorem exists_posLog_separation_of_log_floor {f g : ℂ → ℂ} {r s Λ Mg C : ℝ} {z₀ : ℂ}
    (hcont : ContinuousOn g (closedBall 0 r)) (hz₀ : z₀ ∈ closedBall 0 r)
    (hg0 : g 0 = 0) (hs0 : 0 ≤ s) (hs : s ≤ ‖g z₀‖)
    (hfloor : ∀ w : ℂ, ‖w‖ = s → Λ ≤ Real.log ‖f w‖)
    (hMg : ∀ z ∈ closedBall 0 r, ‖g z‖ ≤ Mg)
    (hC : 0 ≤ C) (hsep : C * Real.posLog Mg < Λ) :
    ∃ z ∈ closedBall 0 r, C * Real.posLog ‖g z‖ < Real.posLog ‖f (g z)‖ := by
  obtain ⟨z, hz, hzs⟩ := exists_norm_eq_of_segment hcont hz₀ hg0 hs0 hs
  refine ⟨z, hz, ?_⟩
  have hglow : Real.posLog ‖g z‖ ≤ Real.posLog Mg :=
    Real.posLog_le_posLog (norm_nonneg _) (hMg z hz)
  have hmul : C * Real.posLog ‖g z‖ ≤ C * Real.posLog Mg :=
    mul_le_mul_of_nonneg_left hglow hC
  have hfl : Λ ≤ Real.log ‖f (g z)‖ := hfloor (g z) hzs
  have hdom : Real.log ‖f (g z)‖ ≤ Real.posLog ‖f (g z)‖ := by
    rw [Real.posLog]
    exact le_max_right _ _
  linarith

/-- **Separation without the normalisation.**  The inner function need not vanish at the centre: it
is enough that the circle be measured from its value there, since translating the outer function
absorbs the shift. -/
theorem exists_posLog_separation_of_log_floor_shift {f g : ℂ → ℂ} {r s Λ Mg C : ℝ} {z₀ : ℂ}
    (hcont : ContinuousOn g (closedBall 0 r)) (hz₀ : z₀ ∈ closedBall 0 r)
    (hs0 : 0 ≤ s) (hs : s ≤ ‖g z₀ - g 0‖)
    (hfloor : ∀ w : ℂ, ‖w - g 0‖ = s → Λ ≤ Real.log ‖f w‖)
    (hMg : ∀ z ∈ closedBall 0 r, ‖g z‖ ≤ Mg)
    (hC : 0 ≤ C) (hsep : C * Real.posLog Mg < Λ) :
    ∃ z ∈ closedBall 0 r, C * Real.posLog ‖g z‖ < Real.posLog ‖f (g z)‖ := by
  have hcont' : ContinuousOn (fun z => g z - g 0) (closedBall 0 r) := hcont.sub continuousOn_const
  have hzero : (fun z => g z - g 0) 0 = 0 := by simp
  obtain ⟨z, hz, hzs⟩ :=
    exists_norm_eq_of_segment hcont' hz₀ hzero hs0 hs
  refine ⟨z, hz, ?_⟩
  have hglow : Real.posLog ‖g z‖ ≤ Real.posLog Mg :=
    Real.posLog_le_posLog (norm_nonneg _) (hMg z hz)
  have hmul : C * Real.posLog ‖g z‖ ≤ C * Real.posLog Mg :=
    mul_le_mul_of_nonneg_left hglow hC
  have hfl : Λ ≤ Real.log ‖f (g z)‖ := by
    have := hfloor (g z) (by simpa using hzs)
    exact this
  have hdom : Real.log ‖f (g z)‖ ≤ Real.posLog ‖f (g z)‖ := by
    rw [Real.posLog]
    exact le_max_right _ _
  linarith

/-- **Separation against the value at the selected point.**  At the point the segment argument
produces, the inner function's modulus is at most `s + ‖g 0‖`, so the separation criterion need only
beat *that* — not a supremum over the whole disc.  This is the sharp form: no bound on the inner
function anywhere else is required. -/
theorem exists_posLog_separation_sharp {f g : ℂ → ℂ} {r s Λ C : ℝ} {z₀ : ℂ}
    (hcont : ContinuousOn g (closedBall 0 r)) (hz₀ : z₀ ∈ closedBall 0 r)
    (hs0 : 0 ≤ s) (hs : s ≤ ‖g z₀ - g 0‖)
    (hfloor : ∀ w : ℂ, ‖w - g 0‖ = s → Λ ≤ Real.log ‖f w‖)
    (hC : 0 ≤ C) (hsep : C * Real.posLog (s + ‖g 0‖) < Λ) :
    ∃ z ∈ closedBall 0 r, C * Real.posLog ‖g z‖ < Real.posLog ‖f (g z)‖ := by
  have hcont' : ContinuousOn (fun z => g z - g 0) (closedBall 0 r) := hcont.sub continuousOn_const
  have hzero : (fun z => g z - g 0) 0 = 0 := by simp
  obtain ⟨z, hz, hzs⟩ := exists_norm_eq_of_segment hcont' hz₀ hzero hs0 hs
  refine ⟨z, hz, ?_⟩
  have hzs' : ‖g z - g 0‖ = s := hzs
  have hgz : ‖g z‖ ≤ s + ‖g 0‖ := by
    have h1 : ‖g z‖ ≤ ‖g z - g 0‖ + ‖g 0‖ := by
      simpa using norm_add_le (g z - g 0) (g 0)
    rw [hzs'] at h1
    exact h1
  have hglow : Real.posLog ‖g z‖ ≤ Real.posLog (s + ‖g 0‖) :=
    Real.posLog_le_posLog (norm_nonneg _) hgz
  have hmul : C * Real.posLog ‖g z‖ ≤ C * Real.posLog (s + ‖g 0‖) :=
    mul_le_mul_of_nonneg_left hglow hC
  have hfl : Λ ≤ Real.log ‖f (g z)‖ := hfloor (g z) hzs'
  have hdom : Real.log ‖f (g z)‖ ≤ Real.posLog ‖f (g z)‖ := by
    rw [Real.posLog]
    exact le_max_right _ _
  linarith

end GaloisForLFunctions.HTGeometry
