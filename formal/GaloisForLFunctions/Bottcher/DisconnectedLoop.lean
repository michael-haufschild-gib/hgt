/-
# The disconnected odd-winding loop — construction

The single open core of `hDisc` (unified across the deck and non-square routes): for disconnected `c`,
a closed loop `γ` in `{f^[n] ∈ escape}` whose `f^[n]`-image winds an ODD number of times around `0`
(equivalently, encircling an odd number of `f^[n]`-preimages of `0`).  This file builds it bottom-up
from the two-component split of `f^{-1}(disk)` in the disconnected regime.
-/
import GaloisForLFunctions.Bottcher.Dynamics
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsSepClosed

open Complex

namespace Bottcher

/-- **Preimages of a disk avoid the critical point `0` in the disconnected regime.**  For `R < ‖c‖`,
any `z` with `‖f_c z‖ ≤ R` has `‖z‖ ≥ √(‖c‖ − R) > 0`: from `‖z‖² = ‖z²‖ = ‖(z²+c) − c‖ ≥ ‖c‖ −
‖z²+c‖ ≥ ‖c‖ − R`.  So `f^{-1}(disk R)` is bounded away from `0` — the geometric reason the square-root
preimage SPLITS into two separated components (the disconnected two-lobe structure). -/
theorem quadratic_preimage_norm_lower_bound {c z : ℂ} {R : ℝ}
    (hz : ‖quadratic c z‖ ≤ R) :
    Real.sqrt (‖c‖ - R) ≤ ‖z‖ := by
  have hquad : ‖z ^ 2 + c‖ ≤ R := hz
  have h2 : ‖c‖ - ‖z ^ 2 + c‖ ≤ ‖z ^ 2‖ := by
    have h := norm_sub_norm_le c (z ^ 2 + c)
    have heq : ‖c - (z ^ 2 + c)‖ = ‖z ^ 2‖ := by
      rw [show c - (z ^ 2 + c) = -z ^ 2 by ring, norm_neg]
    rw [heq] at h; exact h
  have hge : ‖c‖ - R ≤ ‖z‖ ^ 2 := by
    rw [show ‖z‖ ^ 2 = ‖z ^ 2‖ from (norm_pow z 2).symm]; linarith
  calc Real.sqrt (‖c‖ - R) ≤ Real.sqrt (‖z‖ ^ 2) := Real.sqrt_le_sqrt hge
    _ = ‖z‖ := Real.sqrt_sq (norm_nonneg z)

/-- **The two `f`-preimages of a point are antipodal:** `f_c z = f_c z'` iff `z' = z` or `z' = -z`.
The fibre of `f_c(z) = z²+c` is `{z, -z}` (the deck of the squaring 2-cover), the algebraic backbone of
the two-component split. -/
theorem quadratic_fiber {c z z' : ℂ} : quadratic c z' = quadratic c z ↔ z' = z ∨ z' = -z := by
  simp only [quadratic_apply]
  constructor
  · intro h
    have hsq : z' ^ 2 = z ^ 2 := by linear_combination h
    have hfac : (z' - z) * (z' + z) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hfac with h1 | h1
    · left; exact sub_eq_zero.mp h1
    · right; exact eq_neg_of_add_eq_zero_left h1
  · rintro (rfl | rfl) <;> ring

/-- **`f_c` is injective on any open half-plane through `0`.**  The fibre `{z, -z}` is antipodal, and `z`
and `-z` lie on opposite sides of any half-plane `{w | 0 < Re(v̄·w)}` (since `Re(v̄·(-z)) = −Re(v̄·z)`).
So `f_c` is one-to-one on each such half-plane — the local sheet on which the inverse branch (one
component of `f^{-1}`) is single-valued.  This is the half that contains one of `±√(−c)` and maps
biholomorphically onto its image, the building block of the disconnected two-component split. -/
theorem quadratic_injOn_halfplane (c : ℂ) {v : ℂ} :
    Set.InjOn (quadratic c) {z : ℂ | 0 < (starRingEnd ℂ v * z).re} := by
  intro z₁ h₁ z₂ h₂ heq
  simp only [Set.mem_setOf_eq] at h₁ h₂
  rcases quadratic_fiber.mp heq with h | h
  · exact h
  · exfalso
    have hneg : (starRingEnd ℂ v * z₁).re = -(starRingEnd ℂ v * z₂).re := by
      rw [h, mul_neg, Complex.neg_re]
    rw [hneg] at h₁
    linarith

/-- **The preimage of `disk R` avoids the perpendicular line, splitting into two half-planes.**  For
`R < ‖c‖` and `v` a square root of `−c` (`v² = −c`), any `z` with `‖f_c z‖ ≤ R` has `Re(v̄·z) ≠ 0`:
on the line `Re(v̄·z) = 0` one computes `Re(c̄·z²) = (Im(v̄·z))² ≥ 0` (using `c̄ = −(v̄)²`), whence
`‖z²+c‖² = ‖z²‖² + ‖c‖² + 2Re(c̄·z²) ≥ ‖c‖²`, so `‖f_c z‖ ≥ ‖c‖ > R` — contradiction.  So
`f^{-1}(disk R)` lies in the two open half-planes `{Re(v̄·z) > 0} ⊔ {Re(v̄·z) < 0}`, each containing one
of `±√(−c)`, on each of which `f_c` is injective (`quadratic_injOn_halfplane`).  The disconnected
two-component split, made precise. -/
theorem quadratic_preimage_avoids_perp {c v z : ℂ} {R : ℝ}
    (hv : v ^ 2 = -c) (hR : R < ‖c‖) (hz : ‖quadratic c z‖ ≤ R) :
    (starRingEnd ℂ v * z).re ≠ 0 := by
  intro h0
  set w : ℂ := starRingEnd ℂ v * z with hw
  have hc : c = -v ^ 2 := by linear_combination hv
  -- c̄ = -(v̄)²
  have hconjc : starRingEnd ℂ c = -(starRingEnd ℂ v) ^ 2 := by
    rw [hc, map_neg, map_pow]
  -- Re(c̄·z²) = (Im w)² ≥ 0
  have hkey : (starRingEnd ℂ c * z ^ 2).re = w.im ^ 2 := by
    have hcz : starRingEnd ℂ c * z ^ 2 = -(w ^ 2) := by rw [hconjc, hw]; ring
    rw [hcz]
    simp only [Complex.neg_re, pow_two, Complex.mul_re, h0]
    ring
  have hkeynn : 0 ≤ (starRingEnd ℂ c * z ^ 2).re := by rw [hkey]; positivity
  -- ‖z²+c‖² ≥ ‖c‖²
  have hnormsq : Complex.normSq c ≤ Complex.normSq (z ^ 2 + c) := by
    rw [Complex.normSq_add]
    have hre : (z ^ 2 * starRingEnd ℂ c).re = (starRingEnd ℂ c * z ^ 2).re := by rw [mul_comm]
    rw [hre]
    nlinarith [Complex.normSq_nonneg (z ^ 2), hkeynn]
  have hge : ‖c‖ ≤ ‖z ^ 2 + c‖ := by
    have h1 : ‖c‖ ^ 2 ≤ ‖z ^ 2 + c‖ ^ 2 := by rw [Complex.sq_norm, Complex.sq_norm]; exact hnormsq
    nlinarith [norm_nonneg (z ^ 2 + c), norm_nonneg c, h1]
  have hqle : ‖z ^ 2 + c‖ ≤ R := hz
  linarith

/-- **`f_c` maps each half-plane piece ONTO the disk.**  For `R < ‖c‖`, `v² = −c`, and any `w` with
`‖w‖ ≤ R`, there is `z` in the open half-plane `{Re(v̄·z) > 0}` with `f_c z = w`: take a square root `s`
of `w − c` (so `f_c s = w`); by `quadratic_preimage_avoids_perp`, `Re(v̄·s) ≠ 0`, so exactly one of `±s`
lies in the half-plane, and `f_c(±s) = w`.  Combined with `quadratic_injOn_halfplane`, `f_c` is a
**bijection** from the half-plane piece `{Re(v̄·z) > 0} ∩ f^{-1}(disk R)` onto `disk R` — the degree-1
component (a topological disk) carrying the single-valued inverse branch.  This is the disconnected
two-component split with each component a univalent sheet. -/
theorem quadratic_surjOn_halfplane {c v : ℂ} {R : ℝ} (hv : v ^ 2 = -c) (hR : R < ‖c‖)
    {w : ℂ} (hw : ‖w‖ ≤ R) :
    ∃ z, 0 < (starRingEnd ℂ v * z).re ∧ quadratic c z = w := by
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s ^ 2 = w - c := IsSepClosed.exists_pow_nat_eq (w - c) 2
  have hfs : quadratic c s = w := by simp only [quadratic_apply]; rw [hs]; ring
  have hsne : (starRingEnd ℂ v * s).re ≠ 0 :=
    quadratic_preimage_avoids_perp hv hR (by rw [hfs]; exact hw)
  rcases lt_or_gt_of_ne hsne with h | h
  · refine ⟨-s, ?_, ?_⟩
    · rw [mul_neg, Complex.neg_re]; linarith
    · simp only [quadratic_apply]; rw [show (-s) ^ 2 = s ^ 2 by ring, hs]; ring
  · exact ⟨s, h, hfs⟩

/-- **`f_c` is a bijection from each half-plane piece onto the disk — the degree-1 univalent sheet.**
Combining `quadratic_injOn_halfplane` (injective) and `quadratic_surjOn_halfplane` (onto): for
`R < ‖c‖` and `v² = −c`, `f_c` maps `{Re(v̄·z) > 0} ∩ f^{-1}(disk R)` bijectively onto `disk R`.  So
`f^{-1}(disk R)` is the disjoint union of two such univalent sheets (one per half-plane,
`quadratic_preimage_avoids_perp` giving disjointness), each carrying a single-valued inverse branch —
the disconnected two-component split.  Iterating (`f^[n] = f∘⋯∘f`) gives the degree-1 deep components
whose boundary loops have `f^[n]`-image winding `1` (odd), the core of the cylinder loop. -/
theorem quadratic_bijOn_halfplane_disk {c v : ℂ} {R : ℝ} (hv : v ^ 2 = -c) (hR : R < ‖c‖) :
    Set.BijOn (quadratic c)
      ({z | 0 < (starRingEnd ℂ v * z).re} ∩ {z | ‖quadratic c z‖ ≤ R})
      {w | ‖w‖ ≤ R} := by
  refine ⟨fun z hz => hz.2, fun z₁ h₁ z₂ h₂ heq => quadratic_injOn_halfplane c h₁.1 h₂.1 heq, ?_⟩
  intro w hw
  obtain ⟨z, hzhalf, hzf⟩ := quadratic_surjOn_halfplane hv hR hw
  refine ⟨z, ⟨hzhalf, ?_⟩, hzf⟩
  show ‖quadratic c z‖ ≤ R
  rw [hzf]; exact hw

/-- The two half-plane pieces of `f^{-1}(disk R)` are disjoint. -/
theorem quadratic_preimage_pieces_disjoint (c v : ℂ) (R : ℝ) :
    Disjoint ({z : ℂ | 0 < (starRingEnd ℂ v * z).re} ∩ {z | ‖quadratic c z‖ ≤ R})
             ({z : ℂ | (starRingEnd ℂ v * z).re < 0} ∩ {z | ‖quadratic c z‖ ≤ R}) := by
  rw [Set.disjoint_left]
  rintro z ⟨hz1, _⟩ ⟨hz2, _⟩
  simp only [Set.mem_setOf_eq] at hz1 hz2
  linarith

/-- **`f^{-1}(disk R)` is the disjoint union of the two univalent sheets — the two-component split.**
Every preimage avoids the perpendicular line (`quadratic_preimage_avoids_perp`), so lies strictly in
one open half-plane; with `quadratic_bijOn_halfplane_disk` (each piece maps bijectively onto `disk R`)
and `quadratic_preimage_pieces_disjoint`, this exhibits `f^{-1}(disk R)` as exactly two disjoint
degree-1 sheets — the disconnected two-lobe structure, the base case of the depth-`n` split. -/
theorem quadratic_preimage_eq_union {c v : ℂ} {R : ℝ} (hv : v ^ 2 = -c) (hR : R < ‖c‖) :
    {z : ℂ | ‖quadratic c z‖ ≤ R}
      = ({z : ℂ | 0 < (starRingEnd ℂ v * z).re} ∩ {z | ‖quadratic c z‖ ≤ R})
        ∪ ({z : ℂ | (starRingEnd ℂ v * z).re < 0} ∩ {z | ‖quadratic c z‖ ≤ R}) := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff]
  constructor
  · intro hz
    have hne : (starRingEnd ℂ v * z).re ≠ 0 := quadratic_preimage_avoids_perp hv hR hz
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inr ⟨h, hz⟩
    · exact Or.inl ⟨h, hz⟩
  · rintro (⟨_, hz⟩ | ⟨_, hz⟩) <;> exact hz

end Bottcher
