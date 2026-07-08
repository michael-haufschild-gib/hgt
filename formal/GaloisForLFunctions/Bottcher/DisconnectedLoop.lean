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

/-- **Open one-step zero-disk sheet.**  If `0 < R < ρ < ‖c‖`, the positive half-plane component of
`f_c⁻¹(ball(0,ρ))` is an open injective sheet for `f_c`, contains no critical point, and maps onto a
set containing the smaller circle `C(0,R)`.  This is the open-sheet version of
`quadratic_bijOn_halfplane_disk` needed by the zero-circle branch route. -/
theorem quadratic_open_halfplane_sheet_circle {c v : ℂ} {R ρ : ℝ}
    (hv : v ^ 2 = -c) (hRpos : 0 < R) (hRρ : R < ρ) (hρc : ρ < ‖c‖) :
    ∃ A : Set ℂ,
      IsOpen A ∧
      Set.InjOn (quadratic c) A ∧
      (∀ z ∈ A, z ≠ 0) ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ quadratic c '' A) := by
  let A : Set ℂ :=
    {z : ℂ | 0 < (starRingEnd ℂ v * z).re} ∩ {z : ℂ | ‖quadratic c z‖ < ρ}
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · have hhalf : IsOpen {z : ℂ | 0 < (starRingEnd ℂ v * z).re} := by
      exact isOpen_lt continuous_const (by fun_prop)
    have hpre : IsOpen {z : ℂ | ‖quadratic c z‖ < ρ} := by
      exact isOpen_lt ((continuous_norm.comp (continuous_quadratic c))) continuous_const
    exact hhalf.inter hpre
  · intro z₁ hz₁ z₂ hz₂ heq
    exact quadratic_injOn_halfplane c hz₁.1 hz₂.1 heq
  · intro z hz hz0
    have hhalf : 0 < (starRingEnd ℂ v * z).re := hz.1
    simp [hz0] at hhalf
  · intro θ
    have hnorm : ‖circleMap (0 : ℂ) R θ‖ = R :=
      mem_sphere_zero_iff_norm.mp (circleMap_mem_sphere (0 : ℂ) hRpos.le θ)
    have hw : ‖circleMap (0 : ℂ) R θ‖ ≤ ρ := by
      rw [hnorm]
      exact le_of_lt hRρ
    obtain ⟨z, hzhalf, hzf⟩ :=
      quadratic_surjOn_halfplane (c := c) (v := v) (R := ρ) hv hρc hw
    refine ⟨z, ⟨hzhalf, ?_⟩, hzf⟩
    show ‖quadratic c z‖ < ρ
    rw [hzf, hnorm]
    exact hRρ

/-- Uniform interval form of the one-step zero-disk sheet: all circles with
radius `R ∈ (a,b)` have an open half-plane sheet as soon as
`0 < a < b < ρ < ‖c‖`. -/
theorem quadratic_uniform_open_halfplane_sheet_circle {c v : ℂ} {a b ρ : ℝ}
    (hv : v ^ 2 = -c) (ha : 0 < a) (hbρ : b < ρ) (hρc : ρ < ‖c‖) :
    ∀ R ∈ Set.Ioo a b, ∃ A : Set ℂ,
      IsOpen A ∧
      Set.InjOn (quadratic c) A ∧
      (∀ z ∈ A, z ≠ 0) ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ quadratic c '' A) := by
  intro R hR
  exact quadratic_open_halfplane_sheet_circle hv (lt_trans ha hR.1) (lt_trans hR.2 hbρ) hρc

/-- **Slit half-plane pullback sheet.**  If an open target `A` lies in the image of one chosen
half-plane, then the half-plane preimage `H ∩ f_c⁻¹(A)` is an open one-step univalent sheet over `A`.

This is the Lean-facing form of the moving-slit idea: the hard geometric choice is no longer
`A ⊆ ball(0,ρ)` but the existence of a half-plane whose omitted quadratic slit avoids `A`. -/
theorem quadratic_open_halfplane_preimage_sheet_of_image_subset {c v : ℂ} {A : Set ℂ}
    (hAo : IsOpen A)
    (hAcoveredHalf :
      A ⊆ quadratic c '' {z : ℂ | 0 < (starRingEnd ℂ v * z).re}) :
    ∃ B : Set ℂ,
      IsOpen B ∧
      B ⊆ {z : ℂ | 0 < (starRingEnd ℂ v * z).re} ∧
      (∀ z ∈ B, quadratic c z ∈ A) ∧
      A ⊆ quadratic c '' B ∧
      Set.InjOn (quadratic c) B ∧
      (∀ z ∈ B, z ≠ 0) := by
  let H : Set ℂ := {z : ℂ | 0 < (starRingEnd ℂ v * z).re}
  let B : Set ℂ := H ∩ (quadratic c ⁻¹' A)
  refine ⟨B, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hhalf : IsOpen H := by
      exact isOpen_lt continuous_const (by fun_prop)
    have hpre : IsOpen (quadratic c ⁻¹' A) :=
      hAo.preimage (continuous_quadratic c)
    exact hhalf.inter hpre
  · intro z hz
    exact hz.1
  · intro z hz
    exact hz.2
  · intro w hwA
    obtain ⟨z, hzhalf, hzf⟩ := hAcoveredHalf hwA
    refine ⟨z, ⟨hzhalf, ?_⟩, hzf⟩
    show quadratic c z ∈ A
    rw [hzf]
    exact hwA
  · intro z₁ hz₁ z₂ hz₂ heq
    exact quadratic_injOn_halfplane c hz₁.1 hz₂.1 heq
  · intro z hz hz0
    have hhalf : 0 < (starRingEnd ℂ v * z).re := hz.1
    simp [hz0] at hhalf

/-- If every preimage of `w` avoids the boundary line of the chosen half-plane, then exactly one
preimage lies in the positive half-plane.  This is the pointwise moving-slit selector. -/
theorem quadratic_surjOn_halfplane_of_boundary_avoid {c v w : ℂ}
    (hboundary :
      ∀ z : ℂ, quadratic c z = w → (starRingEnd ℂ v * z).re ≠ 0) :
    ∃ z, 0 < (starRingEnd ℂ v * z).re ∧ quadratic c z = w := by
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s ^ 2 = w - c := IsSepClosed.exists_pow_nat_eq (w - c) 2
  have hfs : quadratic c s = w := by simp only [quadratic_apply]; rw [hs]; ring
  have hsne : (starRingEnd ℂ v * s).re ≠ 0 := hboundary s hfs
  rcases lt_or_gt_of_ne hsne with h | h
  · refine ⟨-s, ?_, ?_⟩
    · rw [mul_neg, Complex.neg_re]; linarith
    · simp only [quadratic_apply]; rw [show (-s) ^ 2 = s ^ 2 by ring, hs]; ring
  · exact ⟨s, h, hfs⟩

/-- Boundary-avoidance form of the slit half-plane pullback sheet.  If all preimages of points of
`A` avoid the boundary line of a chosen half-plane, then `A` is covered by the positive half-plane
branch, and the open pullback sheet exists. -/
theorem quadratic_open_halfplane_preimage_sheet_of_boundary_avoid {c v : ℂ} {A : Set ℂ}
    (hAo : IsOpen A)
    (hboundary :
      ∀ w ∈ A, ∀ z : ℂ, quadratic c z = w → (starRingEnd ℂ v * z).re ≠ 0) :
    ∃ B : Set ℂ,
      IsOpen B ∧
      B ⊆ {z : ℂ | 0 < (starRingEnd ℂ v * z).re} ∧
      (∀ z ∈ B, quadratic c z ∈ A) ∧
      A ⊆ quadratic c '' B ∧
      Set.InjOn (quadratic c) B ∧
      (∀ z ∈ B, z ≠ 0) := by
  refine quadratic_open_halfplane_preimage_sheet_of_image_subset
    (c := c) (v := v) (A := A) hAo ?_
  intro w hwA
  exact quadratic_surjOn_halfplane_of_boundary_avoid
    (c := c) (v := v) (w := w) (hboundary w hwA)

/-- Boundary-avoidance gives a genuine degree-one side of the preimage: the positive half-plane
piece maps bijectively onto `A`. -/
theorem quadratic_bijOn_halfplane_preimage_of_boundary_avoid {c v : ℂ} {A : Set ℂ}
    (hboundary :
      ∀ w ∈ A, ∀ z : ℂ, quadratic c z = w → (starRingEnd ℂ v * z).re ≠ 0) :
    Set.BijOn (quadratic c)
      ({z : ℂ | 0 < (starRingEnd ℂ v * z).re} ∩ (quadratic c ⁻¹' A)) A := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact hz.2
  · intro z₁ hz₁ z₂ hz₂ heq
    exact quadratic_injOn_halfplane c hz₁.1 hz₂.1 heq
  · intro w hw
    obtain ⟨z, hzhalf, hzf⟩ :=
      quadratic_surjOn_halfplane_of_boundary_avoid
        (c := c) (v := v) (w := w) (hboundary w hw)
    refine ⟨z, ⟨hzhalf, ?_⟩, hzf⟩
    show quadratic c z ∈ A
    rw [hzf]
    exact hw

/-- If the preimage of `A` avoids the boundary line, it splits into the positive and negative
half-plane pieces. -/
theorem quadratic_preimage_eq_halfplane_union_of_boundary_avoid {c v : ℂ} {A : Set ℂ}
    (hboundary :
      ∀ z : ℂ, quadratic c z ∈ A → (starRingEnd ℂ v * z).re ≠ 0) :
    quadratic c ⁻¹' A =
      ({z : ℂ | 0 < (starRingEnd ℂ v * z).re} ∩ (quadratic c ⁻¹' A)) ∪
        ({z : ℂ | (starRingEnd ℂ v * z).re < 0} ∩ (quadratic c ⁻¹' A)) := by
  ext z
  simp only [Set.mem_preimage, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · intro hz
    have hne : (starRingEnd ℂ v * z).re ≠ 0 := hboundary z hz
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inr ⟨h, hz⟩
    · exact Or.inl ⟨h, hz⟩
  · rintro (⟨_, hz⟩ | ⟨_, hz⟩) <;> exact hz

/-- If `A` misses the quadratic image of the boundary line of a chosen half-plane, then all
preimages of points of `A` avoid that boundary line.  This is the set-theoretic "slit misses the
sheet" condition. -/
theorem quadratic_boundary_avoid_of_disjoint_boundary_image {c v : ℂ} {A : Set ℂ}
    (hdisj :
      Disjoint A (quadratic c '' {z : ℂ | (starRingEnd ℂ v * z).re = 0})) :
    ∀ w ∈ A, ∀ z : ℂ, quadratic c z = w → (starRingEnd ℂ v * z).re ≠ 0 := by
  intro w hwA z hzw hzline
  rw [Set.disjoint_left] at hdisj
  exact hdisj hwA ⟨z, hzline, hzw⟩

/-- Slit-disjoint form of the half-plane pullback sheet.  A chosen half-plane works as soon as the
old sheet avoids the quadratic image of its boundary line. -/
theorem quadratic_open_halfplane_preimage_sheet_of_disjoint_boundary_image {c v : ℂ}
    {A : Set ℂ}
    (hAo : IsOpen A)
    (hdisj :
      Disjoint A (quadratic c '' {z : ℂ | (starRingEnd ℂ v * z).re = 0})) :
    ∃ B : Set ℂ,
      IsOpen B ∧
      B ⊆ {z : ℂ | 0 < (starRingEnd ℂ v * z).re} ∧
      (∀ z ∈ B, quadratic c z ∈ A) ∧
      A ⊆ quadratic c '' B ∧
      Set.InjOn (quadratic c) B ∧
      (∀ z ∈ B, z ≠ 0) := by
  exact quadratic_open_halfplane_preimage_sheet_of_boundary_avoid
    (c := c) (v := v) (A := A) hAo
    (quadratic_boundary_avoid_of_disjoint_boundary_image (c := c) (v := v) (A := A) hdisj)

/-- Slit-disjoint form of the degree-one side statement. -/
theorem quadratic_bijOn_halfplane_preimage_of_disjoint_boundary_image {c v : ℂ} {A : Set ℂ}
    (hdisj :
      Disjoint A (quadratic c '' {z : ℂ | (starRingEnd ℂ v * z).re = 0})) :
    Set.BijOn (quadratic c)
      ({z : ℂ | 0 < (starRingEnd ℂ v * z).re} ∩ (quadratic c ⁻¹' A)) A := by
  exact quadratic_bijOn_halfplane_preimage_of_boundary_avoid
    (c := c) (v := v) (A := A)
    (quadratic_boundary_avoid_of_disjoint_boundary_image (c := c) (v := v) (A := A) hdisj)

/-- A point on the boundary line of the half-plane is a real multiple of `I * v`, when `v ≠ 0`. -/
theorem quadratic_boundaryLine_eq_param {v z : ℂ} (hv : v ≠ 0)
    (hz : ((starRingEnd ℂ v) * z).re = 0) :
    ∃ t : ℝ, z = (t : ℂ) * Complex.I * v := by
  let a : ℂ := (starRingEnd ℂ v) * z
  have ha : a = (a.im : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [a, hz]
    · simp
  have hnorm_ne_real : Complex.normSq v ≠ 0 := by
    exact mt Complex.normSq_eq_zero.mp hv
  have hnorm_ne : ((Complex.normSq v : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hnorm_ne_real
  refine ⟨a.im / Complex.normSq v, ?_⟩
  have hsolve : ((Complex.normSq v : ℝ) : ℂ) * z = v * a := by
    dsimp [a]
    rw [show v * ((starRingEnd ℂ v) * z) = (v * (starRingEnd ℂ v)) * z by ring]
    rw [Complex.mul_conj]
  have hsolve' : z = (((Complex.normSq v : ℝ) : ℂ)⁻¹) * (v * a) := by
    calc
      z = ((((Complex.normSq v : ℝ) : ℂ)⁻¹) *
          (((Complex.normSq v : ℝ) : ℂ))) * z := by
        field_simp [hnorm_ne]
      _ = (((Complex.normSq v : ℝ) : ℂ)⁻¹) *
          (((Complex.normSq v : ℝ) : ℂ) * z) := by ring
      _ = (((Complex.normSq v : ℝ) : ℂ)⁻¹) * (v * a) := by rw [hsolve]
  rw [hsolve']
  conv_lhs => rw [ha]
  rw [Complex.ofReal_div]
  ring

/-- The parametrized line `t ↦ t I v` lies in the boundary of the half-plane. -/
theorem quadratic_boundaryLine_param_mem (v : ℂ) (t : ℝ) :
    ((starRingEnd ℂ v) * ((t : ℂ) * Complex.I * v)).re = 0 := by
  have hmul : (starRingEnd ℂ v) * ((t : ℂ) * Complex.I * v)
      = (((t * Complex.normSq v : ℝ) : ℂ) * Complex.I) := by
    rw [show (starRingEnd ℂ v) * ((t : ℂ) * Complex.I * v)
        = (t : ℂ) * ((starRingEnd ℂ v) * v) * Complex.I by ring]
    rw [← Complex.normSq_eq_conj_mul_self]
    simp [mul_assoc]
  rw [hmul]
  simp

/-- The quadratic image of the boundary-line parametrization is the ray
`t ↦ c - t² v²`. -/
theorem quadratic_boundaryLine_param_apply (c v : ℂ) (t : ℝ) :
    quadratic c ((t : ℂ) * Complex.I * v) = c - (t : ℂ)^2 * v^2 := by
  simp only [quadratic_apply]
  rw [show ((t : ℂ) * Complex.I * v) ^ 2 = - (t : ℂ)^2 * v^2 by
    rw [show ((t : ℂ) * Complex.I * v) ^ 2 =
        (t : ℂ)^2 * Complex.I^2 * v^2 by ring]
    rw [Complex.I_sq]
    ring]
  ring

/-- The quadratic image of the boundary line is exactly the ray/slit from `c` in direction `-v²`. -/
theorem quadratic_boundaryLine_image_eq_ray {c v : ℂ} (hv : v ≠ 0) :
    quadratic c '' {z : ℂ | ((starRingEnd ℂ v) * z).re = 0}
      = {w : ℂ | ∃ t : ℝ, w = c - (t : ℂ)^2 * v^2} := by
  ext w
  constructor
  · rintro ⟨z, hzline, rfl⟩
    obtain ⟨t, rfl⟩ := quadratic_boundaryLine_eq_param hv hzline
    exact ⟨t, quadratic_boundaryLine_param_apply c v t⟩
  · rintro ⟨t, rfl⟩
    refine ⟨(t : ℂ) * Complex.I * v, quadratic_boundaryLine_param_mem v t, ?_⟩
    exact quadratic_boundaryLine_param_apply c v t

/-- Ray-disjoint form of boundary avoidance.  After parametrizing the boundary image, it is enough
for `A` to miss the explicit ray `c - t² v²`. -/
theorem quadratic_boundary_avoid_of_disjoint_boundary_ray {c v : ℂ} {A : Set ℂ}
    (hv : v ≠ 0)
    (hray : Disjoint A {w : ℂ | ∃ t : ℝ, w = c - (t : ℂ)^2 * v^2}) :
    ∀ w ∈ A, ∀ z : ℂ, quadratic c z = w → (starRingEnd ℂ v * z).re ≠ 0 := by
  apply quadratic_boundary_avoid_of_disjoint_boundary_image (c := c) (v := v) (A := A)
  rwa [quadratic_boundaryLine_image_eq_ray (c := c) (v := v) hv]

/-- Ray-disjoint form of the half-plane pullback sheet. -/
theorem quadratic_open_halfplane_preimage_sheet_of_disjoint_boundary_ray {c v : ℂ}
    {A : Set ℂ}
    (hv : v ≠ 0)
    (hAo : IsOpen A)
    (hray : Disjoint A {w : ℂ | ∃ t : ℝ, w = c - (t : ℂ)^2 * v^2}) :
    ∃ B : Set ℂ,
      IsOpen B ∧
      B ⊆ {z : ℂ | 0 < (starRingEnd ℂ v * z).re} ∧
      (∀ z ∈ B, quadratic c z ∈ A) ∧
      A ⊆ quadratic c '' B ∧
      Set.InjOn (quadratic c) B ∧
      (∀ z ∈ B, z ≠ 0) := by
  exact quadratic_open_halfplane_preimage_sheet_of_boundary_avoid
    (c := c) (v := v) (A := A) hAo
    (quadratic_boundary_avoid_of_disjoint_boundary_ray
      (c := c) (v := v) (A := A) hv hray)

/-- Along the boundary ray `c - t² v²`, the centered coordinate in direction `v²` is exactly
`-t²`. -/
theorem quadratic_boundaryRay_centeredCoord_eq_neg_sq {c v : ℂ} (hv : v ≠ 0) (t : ℝ) :
    (((v ^ 2)⁻¹) * ((c - (t : ℂ)^2 * v^2) - c)).re = -t^2 := by
  have hv2 : v ^ 2 ≠ 0 := pow_ne_zero 2 hv
  have hcomplex : ((v ^ 2)⁻¹) * ((c - (t : ℂ)^2 * v^2) - c)
      = - (t : ℂ)^2 := by
    field_simp [hv2]
    ring
  rw [hcomplex]
  simp [pow_two, Complex.mul_re]

/-- A set lying in the positive half-plane of the centered coordinate
`(v²)⁻¹ * (w - c)` is disjoint from the opposite quadratic boundary ray
`c - t² v²`. -/
theorem quadratic_disjoint_boundary_ray_of_centered_halfplane {c v : ℂ} {A : Set ℂ}
    (hv : v ≠ 0)
    (hAhalf : ∀ w ∈ A, 0 < (((v ^ 2)⁻¹) * (w - c)).re) :
    Disjoint A {w : ℂ | ∃ t : ℝ, w = c - (t : ℂ)^2 * v^2} := by
  rw [Set.disjoint_left]
  intro w hwA hwRay
  obtain ⟨t, rfl⟩ := hwRay
  have hpos := hAhalf (c - (t : ℂ)^2 * v^2) hwA
  rw [quadratic_boundaryRay_centeredCoord_eq_neg_sq (c := c) (v := v) hv t] at hpos
  nlinarith [sq_nonneg t]

/-- Centered-half-plane form of the half-plane pullback sheet.  This gives a purely algebraic
ray-avoidance certificate: put `A` on the side of the line through `c` opposite to the ray
`c - t² v²`. -/
theorem quadratic_open_halfplane_preimage_sheet_of_centered_halfplane {c v : ℂ}
    {A : Set ℂ}
    (hv : v ≠ 0)
    (hAo : IsOpen A)
    (hAhalf : ∀ w ∈ A, 0 < (((v ^ 2)⁻¹) * (w - c)).re) :
    ∃ B : Set ℂ,
      IsOpen B ∧
      B ⊆ {z : ℂ | 0 < (starRingEnd ℂ v * z).re} ∧
      (∀ z ∈ B, quadratic c z ∈ A) ∧
      A ⊆ quadratic c '' B ∧
      Set.InjOn (quadratic c) B ∧
      (∀ z ∈ B, z ≠ 0) := by
  exact quadratic_open_halfplane_preimage_sheet_of_disjoint_boundary_ray
    (c := c) (v := v) (A := A) hv hAo
    (quadratic_disjoint_boundary_ray_of_centered_halfplane
      (c := c) (v := v) (A := A) hv hAhalf)

/-- A ball whose radius is smaller than its center's distance from `0` lies in the open half-plane
defined by the inverse center.  This local copy avoids importing collar modules into the elementary
quadratic split file. -/
theorem centered_halfplane_pos_of_norm_sub_lt_norm {b w : ℂ}
    (hb : b ≠ 0) (hw : ‖w - b‖ < ‖b‖) :
    0 < (b⁻¹ * w).re := by
  let u : ℂ := b⁻¹ * (w - b)
  have hdecomp : b⁻¹ * w = 1 + u := by
    calc
      b⁻¹ * w = b⁻¹ * (b + (w - b)) := by ring
      _ = b⁻¹ * b + b⁻¹ * (w - b) := by ring
      _ = 1 + u := by
        rw [inv_mul_cancel₀ hb]
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hu_norm : ‖u‖ < 1 := by
    have hmul : ‖u‖ = ‖b‖⁻¹ * ‖w - b‖ := by
      simp [u, norm_inv]
    rw [hmul]
    exact (inv_mul_lt_iff₀ hbpos).mpr (by simpa using hw)
  have hre_lower : -‖u‖ ≤ u.re := (abs_le.mp (Complex.abs_re_le_norm u)).1
  rw [hdecomp]
  simp only [Complex.add_re, Complex.one_re]
  linarith

/-- Ball-separated form of ray avoidance.  If `A - c` lies in a ball centered at `v²` whose radius is
less than `‖v²‖`, then `A` lies in the centered half-plane opposite the boundary ray. -/
theorem quadratic_disjoint_boundary_ray_of_centered_ball {c v : ℂ} {A : Set ℂ}
    (hv : v ≠ 0)
    (hball : ∀ w ∈ A, ‖(w - c) - v^2‖ < ‖v^2‖) :
    Disjoint A {w : ℂ | ∃ t : ℝ, w = c - (t : ℂ)^2 * v^2} := by
  refine quadratic_disjoint_boundary_ray_of_centered_halfplane
    (c := c) (v := v) (A := A) hv ?_
  intro w hw
  exact centered_halfplane_pos_of_norm_sub_lt_norm
    (b := v^2) (w := w - c) (pow_ne_zero 2 hv) (hball w hw)

/-- Ball-separated form of the half-plane pullback sheet. -/
theorem quadratic_open_halfplane_preimage_sheet_of_centered_ball {c v : ℂ}
    {A : Set ℂ}
    (hv : v ≠ 0)
    (hAo : IsOpen A)
    (hball : ∀ w ∈ A, ‖(w - c) - v^2‖ < ‖v^2‖) :
    ∃ B : Set ℂ,
      IsOpen B ∧
      B ⊆ {z : ℂ | 0 < (starRingEnd ℂ v * z).re} ∧
      (∀ z ∈ B, quadratic c z ∈ A) ∧
      A ⊆ quadratic c '' B ∧
      Set.InjOn (quadratic c) B ∧
      (∀ z ∈ B, z ≠ 0) := by
  exact quadratic_open_halfplane_preimage_sheet_of_disjoint_boundary_ray
    (c := c) (v := v) (A := A) hv hAo
    (quadratic_disjoint_boundary_ray_of_centered_ball
      (c := c) (v := v) (A := A) hv hball)

/-- A ball around `q` whose radius is smaller than its distance from `c` supplies a square-root
direction `v` with `v² = q - c`, hence the centered-ball certificate used by the moving-slit route. -/
theorem exists_centered_ball_vector_of_ball_away_from_critical_value {c q : ℂ} {A : Set ℂ}
    (hq : q ≠ c)
    (hball : ∀ w ∈ A, ‖w - q‖ < ‖q - c‖) :
    ∃ v : ℂ,
      v ≠ 0 ∧
      (∀ w ∈ A, ‖(w - c) - v^2‖ < ‖v^2‖) := by
  obtain ⟨v, hv⟩ : ∃ v : ℂ, v ^ 2 = q - c :=
    IsSepClosed.exists_pow_nat_eq (q - c) 2
  have hvne : v ≠ 0 := by
    intro hv0
    have hqc0 : q - c = 0 := by
      rw [← hv, hv0]
      norm_num
    exact hq (sub_eq_zero.mp hqc0)
  refine ⟨v, hvne, ?_⟩
  intro w hw
  have hleft : (w - c) - v^2 = w - q := by
    rw [hv]
    ring
  have hright : ‖v^2‖ = ‖q - c‖ := by
    rw [hv]
  rw [hleft, hright]
  exact hball w hw

/-- Center-ball form of the half-plane pullback sheet.  This removes the explicit square-root choice
from the provider: it is enough to place `A` in a ball centered at `q` whose radius is below
`dist(q,c)`. -/
theorem quadratic_open_halfplane_preimage_sheet_of_ball_away_from_critical_value {c q : ℂ}
    {A : Set ℂ}
    (hq : q ≠ c)
    (hAo : IsOpen A)
    (hball : ∀ w ∈ A, ‖w - q‖ < ‖q - c‖) :
    ∃ B : Set ℂ,
      IsOpen B ∧
      (∀ z ∈ B, quadratic c z ∈ A) ∧
      A ⊆ quadratic c '' B ∧
      Set.InjOn (quadratic c) B ∧
      (∀ z ∈ B, z ≠ 0) := by
  obtain ⟨v, hvne, hcentered⟩ :=
    exists_centered_ball_vector_of_ball_away_from_critical_value
      (c := c) (q := q) (A := A) hq hball
  obtain ⟨B, hBo, _hBhalf, hBtoA, hAcovered, hinjB, hcritB⟩ :=
    quadratic_open_halfplane_preimage_sheet_of_centered_ball
      (c := c) (v := v) (A := A) hvne hAo hcentered
  exact ⟨B, hBo, hBtoA, hAcovered, hinjB, hcritB⟩

/-- Radius-ball form of the square-root direction certificate.  It is enough to know that `A` is
contained in a ball `ball(q,r)` whose radius is no larger than `‖q-c‖`. -/
theorem exists_centered_ball_vector_of_subset_ball_away_from_critical_value {c q : ℂ}
    {A : Set ℂ} {r : ℝ}
    (hq : q ≠ c) (hr : r ≤ ‖q - c‖)
    (hAq : A ⊆ Metric.ball q r) :
    ∃ v : ℂ,
      v ≠ 0 ∧
      (∀ w ∈ A, ‖(w - c) - v^2‖ < ‖v^2‖) := by
  refine exists_centered_ball_vector_of_ball_away_from_critical_value
    (c := c) (q := q) (A := A) hq ?_
  intro w hw
  have hwball := hAq hw
  have hdist : dist w q < r := by
    simpa [Metric.mem_ball] using hwball
  have hnorm : ‖w - q‖ < r := by
    simpa [dist_eq_norm] using hdist
  exact lt_of_lt_of_le hnorm hr

/-- Radius-ball form of the half-plane pullback sheet. -/
theorem quadratic_open_halfplane_preimage_sheet_of_subset_ball_away_from_critical_value
    {c q : ℂ} {A : Set ℂ} {r : ℝ}
    (hq : q ≠ c)
    (hAo : IsOpen A)
    (hr : r ≤ ‖q - c‖)
    (hAq : A ⊆ Metric.ball q r) :
    ∃ B : Set ℂ,
      IsOpen B ∧
      (∀ z ∈ B, quadratic c z ∈ A) ∧
      A ⊆ quadratic c '' B ∧
      Set.InjOn (quadratic c) B ∧
      (∀ z ∈ B, z ≠ 0) := by
  obtain ⟨v, hvne, hcentered⟩ :=
    exists_centered_ball_vector_of_subset_ball_away_from_critical_value
      (c := c) (q := q) (A := A) (r := r) hq hr hAq
  obtain ⟨B, hBo, _hBhalf, hBtoA, hAcovered, hinjB, hcritB⟩ :=
    quadratic_open_halfplane_preimage_sheet_of_centered_ball
      (c := c) (v := v) (A := A) hvne hAo hcentered
  exact ⟨B, hBo, hBtoA, hAcovered, hinjB, hcritB⟩

/-- On the selected half-plane, `z` and `v` point to the same side, so `z + v` cannot be shorter
than `v`.  This is the elementary denominator lower bound for the inverse-branch ball estimate. -/
theorem norm_le_norm_add_of_pos_conj_mul {v z : ℂ}
    (hhalf : 0 < (starRingEnd ℂ v * z).re) :
    ‖v‖ ≤ ‖z + v‖ := by
  have hsq : ‖v‖ ^ 2 ≤ ‖z + v‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_add]
    have hre : (z * starRingEnd ℂ v).re = (starRingEnd ℂ v * z).re := by
      rw [mul_comm]
    rw [hre]
    nlinarith [Complex.normSq_nonneg z, hhalf]
  nlinarith [norm_nonneg v, norm_nonneg (z + v), hsq]

/-- Ball containment for a chosen inverse branch.  If `A ⊆ ball(q,r)`, `v² = q-c`, and `B` is the
positive half-plane branch over `A`, then `B ⊆ ball(v, r / ‖v‖)`.  Algebraically:
`(z-v)(z+v)=f_c(z)-q`, while the half-plane condition gives `‖v‖ ≤ ‖z+v‖`. -/
theorem quadratic_halfplane_preimage_subset_ball_of_image_subset_ball {c v q : ℂ}
    {A B : Set ℂ} {r : ℝ}
    (hv : v ^ 2 = q - c)
    (hvne : v ≠ 0)
    (hBhalf : B ⊆ {z : ℂ | 0 < (starRingEnd ℂ v * z).re})
    (hBtoA : ∀ z ∈ B, quadratic c z ∈ A)
    (hAq : A ⊆ Metric.ball q r) :
    B ⊆ Metric.ball v (r / ‖v‖) := by
  intro z hzB
  rw [Metric.mem_ball, dist_eq_norm]
  have hqdist : ‖quadratic c z - q‖ < r := by
    have hzball := hAq (hBtoA z hzB)
    simpa [Metric.mem_ball, dist_eq_norm] using hzball
  have hfac : quadratic c z - q = (z - v) * (z + v) := by
    have hq : q = v ^ 2 + c := by
      rw [hv]
      ring
    simp only [quadratic_apply]
    rw [hq]
    ring
  have hprod_lt : ‖(z - v) * (z + v)‖ < r := by
    rw [← hfac]
    exact hqdist
  have hsum_ge : ‖v‖ ≤ ‖z + v‖ :=
    norm_le_norm_add_of_pos_conj_mul (v := v) (z := z) (hBhalf hzB)
  have hnormprod : ‖z - v‖ * ‖z + v‖ < r := by
    simpa [norm_mul] using hprod_lt
  have hmul_lt : ‖z - v‖ * ‖v‖ < r := by
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left hsum_ge (norm_nonneg (z - v))) hnormprod
  exact (lt_div_iff₀ (norm_pos_iff.mpr hvne)).mpr hmul_lt

/-- Radius-ball form of the half-plane pullback sheet, retaining a ball that contains the selected
inverse branch.  This is the ball-carrying version needed to propagate moving-slit data. -/
theorem quadratic_open_halfplane_preimage_sheet_of_subset_ball_with_preimage_ball
    {c q : ℂ} {A : Set ℂ} {r : ℝ}
    (hq : q ≠ c)
    (hAo : IsOpen A)
    (hr : r ≤ ‖q - c‖)
    (hAq : A ⊆ Metric.ball q r) :
    ∃ (v : ℂ) (B : Set ℂ),
      v ^ 2 = q - c ∧
      v ≠ 0 ∧
      IsOpen B ∧
      B ⊆ Metric.ball v (r / ‖v‖) ∧
      (∀ z ∈ B, quadratic c z ∈ A) ∧
      A ⊆ quadratic c '' B ∧
      Set.InjOn (quadratic c) B ∧
      (∀ z ∈ B, z ≠ 0) := by
  obtain ⟨v, hv⟩ : ∃ v : ℂ, v ^ 2 = q - c :=
    IsSepClosed.exists_pow_nat_eq (q - c) 2
  have hvne : v ≠ 0 := by
    intro hv0
    have hqc0 : q - c = 0 := by
      rw [← hv, hv0]
      norm_num
    exact hq (sub_eq_zero.mp hqc0)
  have hcentered : ∀ w ∈ A, ‖(w - c) - v^2‖ < ‖v^2‖ := by
    intro w hw
    have hwball := hAq hw
    have hdist : dist w q < r := by
      simpa [Metric.mem_ball] using hwball
    have hnorm : ‖w - q‖ < r := by
      simpa [dist_eq_norm] using hdist
    have hleft : (w - c) - v^2 = w - q := by
      rw [hv]
      ring
    have hright : ‖v^2‖ = ‖q - c‖ := by
      rw [hv]
    rw [hleft, hright]
    exact lt_of_lt_of_le hnorm hr
  obtain ⟨B, hBo, hBhalf, hBtoA, hAcovered, hinjB, hcritB⟩ :=
    quadratic_open_halfplane_preimage_sheet_of_centered_ball
      (c := c) (v := v) (A := A) hvne hAo hcentered
  have hBball : B ⊆ Metric.ball v (r / ‖v‖) :=
    quadratic_halfplane_preimage_subset_ball_of_image_subset_ball
      (c := c) (v := v) (q := q) (A := A) (B := B) (r := r)
      hv hvne hBhalf hBtoA hAq
  exact ⟨v, B, hv, hvne, hBo, hBball, hBtoA, hAcovered, hinjB, hcritB⟩

/-- Radial-budget form of inverse-branch propagation.  If `v² = q-c` and the incoming radius
spends at most the budget `‖q-c‖` after reserving `R‖v‖`, then the next radius satisfies
`r/‖v‖ + R ≤ ‖v‖`. -/
theorem branch_radius_add_le_norm_of_budget {c v q : ℂ} {r R : ℝ}
    (hv : v ^ 2 = q - c) (hvne : v ≠ 0)
    (hbudget : r + R * ‖v‖ ≤ ‖q - c‖) :
    r / ‖v‖ + R ≤ ‖v‖ := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  have hvnorm : ‖q - c‖ = ‖v‖ ^ 2 := by
    rw [← hv, norm_pow]
  have hmul : (r / ‖v‖ + R) * ‖v‖ ≤ ‖v‖ * ‖v‖ := by
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hvpos)]
    rw [hvnorm] at hbudget
    nlinarith
  exact le_of_mul_le_mul_right (by simpa [pow_two] using hmul) hvpos

/-- The radial budget with `R = ‖c‖` implies the branch-ball separation condition used by the
moving-slit induction. -/
theorem branch_radius_le_norm_sub_of_budget {c v q : ℂ} {r : ℝ}
    (hv : v ^ 2 = q - c) (hvne : v ≠ 0)
    (hbudget : r + ‖c‖ * ‖v‖ ≤ ‖q - c‖) :
    r / ‖v‖ ≤ ‖v - c‖ := by
  have hrad :
      r / ‖v‖ + ‖c‖ ≤ ‖v‖ :=
    branch_radius_add_le_norm_of_budget
      (c := c) (v := v) (q := q) (r := r) (R := ‖c‖) hv hvne hbudget
  have htri : ‖v‖ ≤ ‖v - c‖ + ‖c‖ := by
    calc
      ‖v‖ = ‖(v - c) + c‖ := by
        congr 1
        ring
      _ ≤ ‖v - c‖ + ‖c‖ := norm_add_le _ _
  linarith

/-- A ball centered far enough from `0` is entirely outside the radius-`R` disk. -/
theorem ball_subset_norm_gt_of_radius_add_le_norm {p : ℂ} {s R : ℝ}
    (hRs : R + s ≤ ‖p‖) :
    Metric.ball p s ⊆ {z : ℂ | R < ‖z‖} := by
  intro z hz
  have hdist : ‖z - p‖ < s := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have htri : ‖p‖ ≤ ‖z - p‖ + ‖z‖ := by
    calc
      ‖p‖ = ‖-(z - p) + z‖ := by
        congr 1
        ring
      _ ≤ ‖-(z - p)‖ + ‖z‖ := norm_add_le _ _
      _ = ‖z - p‖ + ‖z‖ := by rw [norm_neg]
  have hlt : ‖p‖ < s + ‖z‖ := by linarith
  have hRadd : R + s < ‖z‖ + s := by
    have hchain : R + s < s + ‖z‖ := lt_of_le_of_lt hRs hlt
    simpa [add_comm] using hchain
  exact (add_lt_add_iff_right s).mp hRadd

/-- Exterior consequence of the radial budget: the selected branch ball `ball(v,r/‖v‖)` lies outside
the radius-`R` disk. -/
theorem branch_ball_subset_norm_gt_of_budget {c v q : ℂ} {r R : ℝ}
    (hv : v ^ 2 = q - c) (hvne : v ≠ 0)
    (hbudget : r + R * ‖v‖ ≤ ‖q - c‖) :
    Metric.ball v (r / ‖v‖) ⊆ {z : ℂ | R < ‖z‖} := by
  exact ball_subset_norm_gt_of_radius_add_le_norm
    (p := v) (s := r / ‖v‖) (R := R)
    (by
      simpa [add_comm] using
        branch_radius_add_le_norm_of_budget
          (c := c) (v := v) (q := q) (r := r) (R := R) hv hvne hbudget)

/-- Elementary forward ball transport for the quadratic map.  If `z` is within radius `s` of `p`,
then `f_c z` is within radius `s * (2 * ‖p‖ + s)` of `f_c p`.  The estimate is just
`z² - p² = (z-p)(z+p)` and `‖z+p‖ ≤ ‖z-p‖ + 2‖p‖`. -/
theorem quadratic_image_ball_subset_ball {c p : ℂ} {s : ℝ} (hs : 0 < s) :
    (quadratic c) '' Metric.ball p s ⊆
      Metric.ball (quadratic c p) (s * (2 * ‖p‖ + s)) := by
  rintro w ⟨z, hzball, rfl⟩
  rw [Metric.mem_ball] at hzball ⊢
  have hzsub : ‖z - p‖ < s := by
    simpa [dist_eq_norm] using hzball
  have hsum : ‖z + p‖ < 2 * ‖p‖ + s := by
    calc
      ‖z + p‖ = ‖(z - p) + (2 : ℂ) * p‖ := by
        congr 1
        ring
      _ ≤ ‖z - p‖ + ‖(2 : ℂ) * p‖ := norm_add_le _ _
      _ = ‖z - p‖ + 2 * ‖p‖ := by
        rw [norm_mul, Complex.norm_two]
      _ < s + 2 * ‖p‖ := by linarith
      _ = 2 * ‖p‖ + s := by ring
  have hdist :
      dist (quadratic c z) (quadratic c p) = ‖(z - p) * (z + p)‖ := by
    rw [dist_eq_norm]
    congr 1
    simp only [quadratic_apply]
    ring
  have hprod : ‖z - p‖ * ‖z + p‖ < s * (2 * ‖p‖ + s) := by
    nlinarith [hzsub, hsum, hs, norm_nonneg (z - p), norm_nonneg (z + p), norm_nonneg p]
  rw [hdist, norm_mul]
  exact hprod

/-- Set version of `quadratic_image_ball_subset_ball`: a subset of `ball(p,s)` has quadratic image
inside the corresponding explicit image ball. -/
theorem quadratic_image_subset_ball_of_subset_ball {c p : ℂ} {A : Set ℂ} {s : ℝ}
    (hs : 0 < s) (hA : A ⊆ Metric.ball p s) :
    (quadratic c) '' A ⊆ Metric.ball (quadratic c p) (s * (2 * ‖p‖ + s)) := by
  rintro w ⟨z, hzA, rfl⟩
  exact quadratic_image_ball_subset_ball (c := c) (p := p) (s := s) hs
    ⟨z, hA hzA, rfl⟩

/-- Small-ball sufficient condition for the slit half-plane pullback sheet.  If `A` is contained in
`ball(0,ρ)` with `ρ < ‖c‖`, the half-plane through a square root of `-c` covers `A`, so the slit-sheet
lemma applies. -/
theorem quadratic_open_halfplane_preimage_sheet_of_subset_ball {c v : ℂ} {A : Set ℂ} {ρ : ℝ}
    (hv : v ^ 2 = -c) (hAo : IsOpen A) (hρc : ρ < ‖c‖)
    (hAρ : ∀ w ∈ A, ‖w‖ < ρ) :
    ∃ B : Set ℂ,
      IsOpen B ∧
      B ⊆ {z : ℂ | 0 < (starRingEnd ℂ v * z).re} ∧
      (∀ z ∈ B, quadratic c z ∈ A) ∧
      A ⊆ quadratic c '' B ∧
      Set.InjOn (quadratic c) B ∧
      (∀ z ∈ B, z ≠ 0) := by
  refine quadratic_open_halfplane_preimage_sheet_of_image_subset
    (c := c) (v := v) (A := A) hAo ?_
  intro w hwA
  obtain ⟨z, hzhalf, hzf⟩ :=
    quadratic_surjOn_halfplane (c := c) (v := v) (R := ρ) hv hρc
      (le_of_lt (hAρ w hwA))
  exact ⟨z, hzhalf, hzf⟩

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
