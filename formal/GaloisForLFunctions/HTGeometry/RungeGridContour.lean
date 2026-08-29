import GaloisForLFunctions.HTGeometry.RectangleResidue
import GaloisForLFunctions.RHTower.RectangleLocalCauchyFormula

/-!
# The grid contour of a compact set

Runge approximation starts from a contour built out of a square grid.  For a grid of mesh `s`, the
squares that meet a compact set `K` have boundaries whose contour integrals telescope: an edge
shared by two selected squares is traversed twice with opposite orientations and cancels.  The
surviving edges are exactly the edges of a selected square whose neighbour across that edge is not
selected — and such an edge cannot meet `K`, because a point of `K` on it would force both
neighbouring squares to be selected.

This module isolates that bookkeeping: the four-edge decomposition of `RHTower.rectIntegral` on a
grid square, the signed edge expansion of a finite sum of grid squares, and the geometric fact that
a surviving edge misses `K`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex intervalIntegral Set RHTower

noncomputable section

/-! ## Edge integrals -/

/-- Horizontal edge integral of `g` from `a` to `b` at height `y`. -/
def hEdge (g : ℂ → ℂ) (a b y : ℝ) : ℂ := ∫ x in a..b, g ((x : ℂ) + (y : ℂ) * I)

/-- Vertical edge integral of `g` at abscissa `x` from `c` to `d`, with the `I` weight. -/
def vEdge (g : ℂ → ℂ) (x c d : ℝ) : ℂ := I * ∫ t in c..d, g ((x : ℂ) + (t : ℂ) * I)

theorem cornerPt_re (a c : ℝ) : ((a : ℂ) + (c : ℂ) * I).re = a := by
  simp

theorem cornerPt_im (a c : ℝ) : ((a : ℂ) + (c : ℂ) * I).im = c := by
  simp

/-- The four-edge decomposition of the rectangle contour integral. -/
theorem rectIntegral_eq_edges (g : ℂ → ℂ) (a b c d : ℝ) :
    rectIntegral g ((a : ℂ) + (c : ℂ) * I) ((b : ℂ) + (d : ℂ) * I)
      = hEdge g a b c - hEdge g a b d + vEdge g b c d - vEdge g a c d := by
  unfold rectIntegral hEdge vEdge
  rw [cornerPt_re, cornerPt_im, cornerPt_re, cornerPt_im]
  simp only [smul_eq_mul]

/-! ## The grid -/

/-- The lower-left corner of the grid square `(m, n)` at mesh `s`. -/
def gridCorner (s : ℝ) (m n : ℤ) : ℂ := ((s * m : ℝ) : ℂ) + ((s * n : ℝ) : ℂ) * I

/-- The closed grid square `(m, n)` at mesh `s`. -/
def gridSquare (s : ℝ) (m n : ℤ) : Set ℂ :=
  (Set.Icc (s * m) (s * (m + 1))) ×ℂ (Set.Icc (s * n) (s * (n + 1)))

theorem mem_gridSquare {s : ℝ} {m n : ℤ} {z : ℂ} :
    z ∈ gridSquare s m n ↔
      (s * m ≤ z.re ∧ z.re ≤ s * (m + 1)) ∧ (s * n ≤ z.im ∧ z.im ≤ s * (n + 1)) := by
  simp [gridSquare, Complex.mem_reProdIm, Set.mem_Icc]

/-- Contour integral around one grid square. -/
def gridRect (g : ℂ → ℂ) (s : ℝ) (m n : ℤ) : ℂ :=
  rectIntegral g (gridCorner s m n) (gridCorner s (m + 1) (n + 1))

/-- Horizontal grid edge integral: the bottom edge of the square `(m, n)`. -/
def gridH (g : ℂ → ℂ) (s : ℝ) (m n : ℤ) : ℂ := hEdge g (s * m) (s * (m + 1)) (s * n)

/-- Vertical grid edge integral: the left edge of the square `(m, n)`. -/
def gridV (g : ℂ → ℂ) (s : ℝ) (m n : ℤ) : ℂ := vEdge g (s * m) (s * n) (s * (n + 1))

theorem gridRect_eq_edges (g : ℂ → ℂ) (s : ℝ) (m n : ℤ) :
    gridRect g s m n
      = gridH g s m n - gridH g s m (n + 1) + gridV g s (m + 1) n - gridV g s m n := by
  unfold gridRect gridCorner
  rw [rectIntegral_eq_edges]
  unfold gridH gridV
  push_cast
  ring_nf


/-! ## Signed edge expansion of a finite union of grid squares -/

/-- Shift a grid index up by one. -/
def shiftUp : ℤ × ℤ → ℤ × ℤ := fun p => (p.1, p.2 + 1)

/-- Shift a grid index right by one. -/
def shiftRight : ℤ × ℤ → ℤ × ℤ := fun p => (p.1 + 1, p.2)

theorem shiftUp_injective : Function.Injective shiftUp := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [shiftUp, Prod.mk.injEq] at h
  exact Prod.ext h.1 (by omega)

theorem shiftRight_injective : Function.Injective shiftRight := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [shiftRight, Prod.mk.injEq] at h
  exact Prod.ext (by omega) h.2

theorem mem_image_shiftUp {S : Finset (ℤ × ℤ)} {q : ℤ × ℤ} :
    q ∈ S.image shiftUp ↔ (q.1, q.2 - 1) ∈ S := by
  classical
  constructor
  · rintro hq
    obtain ⟨p, hp, hpq⟩ := Finset.mem_image.1 hq
    simp only [shiftUp] at hpq
    subst hpq
    simpa using hp
  · intro hq
    refine Finset.mem_image.2 ⟨(q.1, q.2 - 1), hq, ?_⟩
    simp only [shiftUp]
    exact Prod.ext rfl (by omega)

theorem mem_image_shiftRight {S : Finset (ℤ × ℤ)} {q : ℤ × ℤ} :
    q ∈ S.image shiftRight ↔ (q.1 - 1, q.2) ∈ S := by
  classical
  constructor
  · rintro hq
    obtain ⟨p, hp, hpq⟩ := Finset.mem_image.1 hq
    simp only [shiftRight] at hpq
    subst hpq
    simpa using hp
  · intro hq
    refine Finset.mem_image.2 ⟨(q.1 - 1, q.2), hq, ?_⟩
    simp only [shiftRight]
    exact Prod.ext (by omega) rfl

/-- Signed coefficient of the horizontal grid edge below the square `p`. -/
def hCoeff (S : Finset (ℤ × ℤ)) (p : ℤ × ℤ) : ℂ :=
  (if p ∈ S then (1 : ℂ) else 0) - (if (p.1, p.2 - 1) ∈ S then (1 : ℂ) else 0)

/-- Signed coefficient of the vertical grid edge left of the square `p`. -/
def vCoeff (S : Finset (ℤ × ℤ)) (p : ℤ × ℤ) : ℂ :=
  (if (p.1 - 1, p.2) ∈ S then (1 : ℂ) else 0) - (if p ∈ S then (1 : ℂ) else 0)

/-- **Edge cancellation.**  A finite sum of grid-square contour integrals is a signed sum of edge
integrals whose coefficients vanish on every edge shared by two selected squares. -/
theorem sum_gridRect_eq_edges (g : ℂ → ℂ) (s : ℝ) (S : Finset (ℤ × ℤ)) :
    ∑ p ∈ S, gridRect g s p.1 p.2
      = (∑ p ∈ S ∪ S.image shiftUp, hCoeff S p * gridH g s p.1 p.2)
        + ∑ p ∈ S ∪ S.image shiftRight, vCoeff S p * gridV g s p.1 p.2 := by
  classical
  have hsplit : ∑ p ∈ S, gridRect g s p.1 p.2
      = ((∑ p ∈ S, gridH g s p.1 p.2) - ∑ p ∈ S, gridH g s (shiftUp p).1 (shiftUp p).2)
        + ((∑ p ∈ S, gridV g s (shiftRight p).1 (shiftRight p).2) - ∑ p ∈ S, gridV g s p.1 p.2) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [gridRect_eq_edges]
    simp only [shiftUp, shiftRight]
    ring
  rw [hsplit]
  have hH : (∑ p ∈ S, gridH g s p.1 p.2) - ∑ p ∈ S, gridH g s (shiftUp p).1 (shiftUp p).2
      = ∑ p ∈ S ∪ S.image shiftUp, hCoeff S p * gridH g s p.1 p.2 := by
    have h1 : ∑ p ∈ S, gridH g s p.1 p.2
        = ∑ p ∈ S ∪ S.image shiftUp, (if p ∈ S then (1 : ℂ) else 0) * gridH g s p.1 p.2 := by
      have e1 : ∑ p ∈ S, gridH g s p.1 p.2
          = ∑ p ∈ S, (if p ∈ S then (1 : ℂ) else 0) * gridH g s p.1 p.2 :=
        Finset.sum_congr rfl fun p hp => by rw [if_pos hp, one_mul]
      rw [e1]
      exact Finset.sum_subset Finset.subset_union_left (fun p _ hp => by
        rw [if_neg hp, zero_mul])
    have h2 : ∑ p ∈ S, gridH g s (shiftUp p).1 (shiftUp p).2
        = ∑ p ∈ S ∪ S.image shiftUp,
            (if (p.1, p.2 - 1) ∈ S then (1 : ℂ) else 0) * gridH g s p.1 p.2 := by
      rw [← Finset.sum_image (f := fun q : ℤ × ℤ => gridH g s q.1 q.2)
        (g := shiftUp) (fun a _ b _ h => shiftUp_injective h)]
      have himg : ∑ q ∈ S.image shiftUp, gridH g s q.1 q.2
          = ∑ q ∈ S.image shiftUp,
              (if (q.1, q.2 - 1) ∈ S then (1 : ℂ) else 0) * gridH g s q.1 q.2 :=
        Finset.sum_congr rfl fun q hq => by
          rw [if_pos (mem_image_shiftUp.1 hq), one_mul]
      rw [himg]
      exact Finset.sum_subset Finset.subset_union_right (fun q _ hq => by
        rw [if_neg (fun hcon => hq (mem_image_shiftUp.2 hcon)), zero_mul])
    rw [h1, h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hCoeff]
    ring
  have hV : (∑ p ∈ S, gridV g s (shiftRight p).1 (shiftRight p).2) - ∑ p ∈ S, gridV g s p.1 p.2
      = ∑ p ∈ S ∪ S.image shiftRight, vCoeff S p * gridV g s p.1 p.2 := by
    have h1 : ∑ p ∈ S, gridV g s p.1 p.2
        = ∑ p ∈ S ∪ S.image shiftRight, (if p ∈ S then (1 : ℂ) else 0) * gridV g s p.1 p.2 := by
      have e1 : ∑ p ∈ S, gridV g s p.1 p.2
          = ∑ p ∈ S, (if p ∈ S then (1 : ℂ) else 0) * gridV g s p.1 p.2 :=
        Finset.sum_congr rfl fun p hp => by rw [if_pos hp, one_mul]
      rw [e1]
      exact Finset.sum_subset Finset.subset_union_left (fun p _ hp => by
        rw [if_neg hp, zero_mul])
    have h2 : ∑ p ∈ S, gridV g s (shiftRight p).1 (shiftRight p).2
        = ∑ p ∈ S ∪ S.image shiftRight,
            (if (p.1 - 1, p.2) ∈ S then (1 : ℂ) else 0) * gridV g s p.1 p.2 := by
      rw [← Finset.sum_image (f := fun q : ℤ × ℤ => gridV g s q.1 q.2)
        (g := shiftRight) (fun a _ b _ h => shiftRight_injective h)]
      have himg : ∑ q ∈ S.image shiftRight, gridV g s q.1 q.2
          = ∑ q ∈ S.image shiftRight,
              (if (q.1 - 1, q.2) ∈ S then (1 : ℂ) else 0) * gridV g s q.1 q.2 :=
        Finset.sum_congr rfl fun q hq => by
          rw [if_pos (mem_image_shiftRight.1 hq), one_mul]
      rw [himg]
      exact Finset.sum_subset Finset.subset_union_right (fun q _ hq => by
        rw [if_neg (fun hcon => hq (mem_image_shiftRight.2 hcon)), zero_mul])
    rw [h1, h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [vCoeff]
    ring
  rw [hH, hV]


/-! ## Surviving edges avoid the compact set -/

/-- The selection rule: every grid square meeting `K` is selected. -/
def GridSelects (S : Finset (ℤ × ℤ)) (s : ℝ) (K : Set ℂ) : Prop :=
  ∀ p : ℤ × ℤ, (gridSquare s p.1 p.2 ∩ K).Nonempty → p ∈ S

theorem hCoeff_eq_zero_of_mem {S : Finset (ℤ × ℤ)} {s : ℝ} (hs : 0 < s) {K : Set ℂ}
    (hS : GridSelects S s K) {p : ℤ × ℤ} {z : ℂ} (hzK : z ∈ K)
    (hre₁ : s * (p.1 : ℝ) ≤ z.re) (hre₂ : z.re ≤ s * ((p.1 : ℝ) + 1))
    (him : z.im = s * (p.2 : ℝ)) :
    hCoeff S p = 0 := by
  classical
  have hup : s * (p.2 : ℝ) ≤ s * ((p.2 : ℝ) + 1) := by nlinarith
  have h1 : p ∈ S := by
    refine hS p ⟨z, ?_, hzK⟩
    refine mem_gridSquare.2 ⟨⟨hre₁, ?_⟩, ⟨?_, ?_⟩⟩
    · simpa using hre₂
    · rw [him]
    · rw [him]
      simpa using hup
  have h2 : (p.1, p.2 - 1) ∈ S := by
    refine hS (p.1, p.2 - 1) ⟨z, ?_, hzK⟩
    refine mem_gridSquare.2 ⟨⟨hre₁, ?_⟩, ⟨?_, ?_⟩⟩
    · simpa using hre₂
    · rw [him]
      push_cast
      nlinarith
    · rw [him]
      push_cast
      nlinarith
  rw [hCoeff, if_pos h1, if_pos h2, sub_self]

theorem vCoeff_eq_zero_of_mem {S : Finset (ℤ × ℤ)} {s : ℝ} (hs : 0 < s) {K : Set ℂ}
    (hS : GridSelects S s K) {p : ℤ × ℤ} {z : ℂ} (hzK : z ∈ K)
    (hre : z.re = s * (p.1 : ℝ))
    (him₁ : s * (p.2 : ℝ) ≤ z.im) (him₂ : z.im ≤ s * ((p.2 : ℝ) + 1)) :
    vCoeff S p = 0 := by
  classical
  have h1 : p ∈ S := by
    refine hS p ⟨z, ?_, hzK⟩
    refine mem_gridSquare.2 ⟨⟨?_, ?_⟩, ⟨him₁, ?_⟩⟩
    · rw [hre]
    · rw [hre]
      nlinarith
    · simpa using him₂
  have h2 : (p.1 - 1, p.2) ∈ S := by
    refine hS (p.1 - 1, p.2) ⟨z, ?_, hzK⟩
    refine mem_gridSquare.2 ⟨⟨?_, ?_⟩, ⟨him₁, ?_⟩⟩
    · rw [hre]
      push_cast
      nlinarith
    · rw [hre]
      push_cast
      nlinarith
    · simpa using him₂
  rw [vCoeff, if_pos h2, if_pos h1, sub_self]

/-- A surviving horizontal edge misses `K`. -/
theorem hEdge_avoids_of_hCoeff_ne_zero {S : Finset (ℤ × ℤ)} {s : ℝ} (hs : 0 < s) {K : Set ℂ}
    (hS : GridSelects S s K) {p : ℤ × ℤ} (hne : hCoeff S p ≠ 0) {z : ℂ} (hzK : z ∈ K) :
    ¬ (s * (p.1 : ℝ) ≤ z.re ∧ z.re ≤ s * ((p.1 : ℝ) + 1) ∧ z.im = s * (p.2 : ℝ)) := by
  rintro ⟨h1, h2, h3⟩
  exact hne (hCoeff_eq_zero_of_mem hs hS hzK h1 h2 h3)

/-- A surviving vertical edge misses `K`. -/
theorem vEdge_avoids_of_vCoeff_ne_zero {S : Finset (ℤ × ℤ)} {s : ℝ} (hs : 0 < s) {K : Set ℂ}
    (hS : GridSelects S s K) {p : ℤ × ℤ} (hne : vCoeff S p ≠ 0) {z : ℂ} (hzK : z ∈ K) :
    ¬ (z.re = s * (p.1 : ℝ) ∧ s * (p.2 : ℝ) ≤ z.im ∧ z.im ≤ s * ((p.2 : ℝ) + 1)) := by
  rintro ⟨h1, h2, h3⟩
  exact hne (vCoeff_eq_zero_of_mem hs hS hzK h1 h2 h3)


/-! ## The Cauchy kernel on grid squares -/

theorem gridCorner_re (s : ℝ) (m n : ℤ) : (gridCorner s m n).re = s * (m : ℝ) := by
  simp [gridCorner]

theorem gridCorner_im (s : ℝ) (m n : ℤ) : (gridCorner s m n).im = s * (n : ℝ) := by
  simp [gridCorner]

theorem uIcc_reProdIm_gridSquare {s : ℝ} (hs : 0 < s) (m n : ℤ) :
    (uIcc (gridCorner s m n).re (gridCorner s (m + 1) (n + 1)).re) ×ℂ
      (uIcc (gridCorner s m n).im (gridCorner s (m + 1) (n + 1)).im) = gridSquare s m n := by
  have hm : s * (m : ℝ) ≤ s * (((m : ℝ)) + 1) := by nlinarith
  have hn : s * (n : ℝ) ≤ s * (((n : ℝ)) + 1) := by nlinarith
  rw [gridCorner_re, gridCorner_re, gridCorner_im, gridCorner_im]
  push_cast
  rw [uIcc_of_le hm, uIcc_of_le hn]
  rfl

theorem analyticOnNhd_cauchyKernelMul {Ω : Set ℂ} {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F Ω)
    (z : ℂ) : AnalyticOnNhd ℂ (fun w => F w * (w - z)⁻¹) (Ω \ {z}) := by
  intro w hw
  refine (hF w hw.1).mul ?_
  refine AnalyticAt.inv (analyticAt_id.sub analyticAt_const) ?_
  exact sub_ne_zero.2 (by simpa using hw.2)

/-- Off the square, the Cauchy-kernel contour integral vanishes. -/
theorem gridRect_cauchyKernel_eq_zero {Ω : Set ℂ} {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F Ω)
    {s : ℝ} (hs : 0 < s) {m n : ℤ} (hsub : gridSquare s m n ⊆ Ω) {z : ℂ}
    (hz : z ∉ gridSquare s m n) :
    gridRect (fun w => F w * (w - z)⁻¹) s m n = 0 := by
  refine rectIntegral_eq_zero_of_analyticOnNhd (U := Ω \ {z}) ?_
    (analyticOnNhd_cauchyKernelMul hF z)
  rw [uIcc_reProdIm_gridSquare hs]
  intro w hw
  refine ⟨hsub hw, ?_⟩
  simp only [Set.mem_singleton_iff]
  intro hcon
  exact hz (hcon ▸ hw)

/-- Strictly inside the square, the Cauchy-kernel contour integral is `2πi F z`. -/
theorem gridRect_cauchyKernel_eq_value {Ω : Set ℂ} {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F Ω)
    {s : ℝ} (hs : 0 < s) {m n : ℤ} (hsub : gridSquare s m n ⊆ Ω) {z : ℂ}
    (hre₁ : s * (m : ℝ) < z.re) (hre₂ : z.re < s * ((m : ℝ) + 1))
    (him₁ : s * (n : ℝ) < z.im) (him₂ : z.im < s * ((n : ℝ) + 1)) :
    gridRect (fun w => F w * (w - z)⁻¹) s m n = 2 * Real.pi * I * F z := by
  refine rectIntegral_cauchyFormula_of_analyticOnNhd (U := Ω) hF ?_ ?_ ?_ ?_ ?_
  · rw [uIcc_reProdIm_gridSquare hs]
    exact hsub
  · rw [gridCorner_re]
    exact hre₁
  · rw [gridCorner_re]
    push_cast
    exact hre₂
  · rw [gridCorner_im]
    exact him₁
  · rw [gridCorner_im]
    push_cast
    exact him₂


/-! ## The contour representation off the grid lines -/

theorem floor_grid_lt {s x : ℝ} (hs : 0 < s) (hx : ∀ k : ℤ, x ≠ s * k) :
    s * (⌊x / s⌋ : ℝ) < x ∧ x < s * ((⌊x / s⌋ : ℝ) + 1) := by
  have hfl : ((⌊x / s⌋ : ℤ) : ℝ) ≤ x / s := Int.floor_le (x / s)
  have hfu : x / s < ((⌊x / s⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one (x / s)
  have hkey : s * (x / s) = x := by field_simp
  have hle : s * ((⌊x / s⌋ : ℤ) : ℝ) ≤ x := by
    calc s * ((⌊x / s⌋ : ℤ) : ℝ) ≤ s * (x / s) := by nlinarith
      _ = x := hkey
  have hlt : x < s * (((⌊x / s⌋ : ℤ) : ℝ) + 1) := by
    calc x = s * (x / s) := hkey.symm
      _ < s * (((⌊x / s⌋ : ℤ) : ℝ) + 1) := by nlinarith
  exact ⟨lt_of_le_of_ne hle (Ne.symm (hx ⌊x / s⌋)), hlt⟩

theorem grid_index_unique {s x : ℝ} {m k : ℤ} (hs : 0 < s)
    (hm₁ : s * (m : ℝ) < x) (hm₂ : x < s * ((m : ℝ) + 1))
    (hk₁ : s * (k : ℝ) ≤ x) (hk₂ : x ≤ s * ((k : ℝ) + 1)) : k = m := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : (k : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast Int.add_one_le_iff.2 hlt
    nlinarith
  · have h1 : (m : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast Int.add_one_le_iff.2 hgt
    nlinarith

/-- **The grid contour representation.**  For a point of `K` off the grid lines, the sum of the
Cauchy-kernel contour integrals over the selected squares is `2πi` times the value. -/
theorem sum_gridRect_cauchyKernel {Ω : Set ℂ} {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F Ω)
    {s : ℝ} (hs : 0 < s) {S : Finset (ℤ × ℤ)}
    (hSsub : ∀ p ∈ S, gridSquare s p.1 p.2 ⊆ Ω)
    {z : ℂ} (hzre : ∀ k : ℤ, z.re ≠ s * k) (hzim : ∀ k : ℤ, z.im ≠ s * k)
    (hmemS : (⌊z.re / s⌋, ⌊z.im / s⌋) ∈ S) :
    ∑ p ∈ S, gridRect (fun w => F w * (w - z)⁻¹) s p.1 p.2 = 2 * Real.pi * I * F z := by
  classical
  set m : ℤ := ⌊z.re / s⌋ with hmdef
  set n : ℤ := ⌊z.im / s⌋ with hndef
  obtain ⟨hm₁, hm₂⟩ := floor_grid_lt hs hzre
  obtain ⟨hn₁, hn₂⟩ := floor_grid_lt hs hzim
  have hother : ∀ p ∈ S, p ≠ (m, n) → gridRect (fun w => F w * (w - z)⁻¹) s p.1 p.2 = 0 := by
    intro p hp hpne
    refine gridRect_cauchyKernel_eq_zero hF hs (hSsub p hp) ?_
    intro hzp
    obtain ⟨⟨hre₁, hre₂⟩, ⟨him₁, him₂⟩⟩ := mem_gridSquare.1 hzp
    have h1 : p.1 = m := grid_index_unique hs hm₁ hm₂ hre₁ hre₂
    have h2 : p.2 = n := grid_index_unique hs hn₁ hn₂ him₁ him₂
    exact hpne (Prod.ext h1 h2)
  rw [Finset.sum_eq_single (m, n) hother (fun h => absurd hmemS h)]
  exact gridRect_cauchyKernel_eq_value hF hs (hSsub (m, n) hmemS) hm₁ hm₂ hn₁ hn₂


/-! ## Choosing a grid adapted to a compact subset -/

theorem dist_le_two_mul_of_mem_gridSquare {s : ℝ} (_hs : 0 < s) {m n : ℤ} {w q : ℂ}
    (hw : w ∈ gridSquare s m n) (hq : q ∈ gridSquare s m n) : dist w q ≤ 2 * s := by
  obtain ⟨⟨hw1, hw2⟩, ⟨hw3, hw4⟩⟩ := mem_gridSquare.1 hw
  obtain ⟨⟨hq1, hq2⟩, ⟨hq3, hq4⟩⟩ := mem_gridSquare.1 hq
  have hre : |w.re - q.re| ≤ s := by
    rw [abs_le]
    constructor <;> nlinarith
  have him : |w.im - q.im| ≤ s := by
    rw [abs_le]
    constructor <;> nlinarith
  have hnorm : dist w q ≤ |(w - q).re| + |(w - q).im| := by
    rw [dist_eq_norm]
    exact Complex.norm_le_abs_re_add_abs_im _
  simp only [Complex.sub_re, Complex.sub_im] at hnorm
  linarith

/-- A grid mesh adapted to a compact subset of an open set: every square meeting `K` lies in `Ω`,
and the squares meeting `K` form a finite set. -/
theorem exists_gridSelection {Ω K : Set ℂ} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {s₀ : ℝ} (hs₀ : 0 < s₀) :
    ∃ (s : ℝ) (S : Finset (ℤ × ℤ)), 0 < s ∧ s < s₀ ∧ GridSelects S s K ∧
      (∀ p ∈ S, gridSquare s p.1 p.2 ⊆ Ω) := by
  classical
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open hΩ hKΩ
  set s : ℝ := min (δ / 3) (s₀ / 2) with hsdef
  have hs : 0 < s := lt_min (by positivity) (by positivity)
  have hss₀ : s < s₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hsδ : 2 * s ≤ 2 * (δ / 3) := by
    have := min_le_left (δ / 3) (s₀ / 2)
    linarith
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  set N : ℤ := ⌈R / s⌉ + 1 with hNdef
  set S : Finset (ℤ × ℤ) :=
    ((Finset.Icc (-N) N) ×ˢ (Finset.Icc (-N) N)).filter
      (fun p => (gridSquare s p.1 p.2 ∩ K).Nonempty) with hSdef
  have hbound : ∀ (k : ℤ) (x : ℝ), |x| ≤ R → s * (k : ℝ) ≤ x → x ≤ s * ((k : ℝ) + 1) →
      k ∈ Finset.Icc (-N) N := by
    intro k x hx h1 h2
    have hxR : -R ≤ x ∧ x ≤ R := abs_le.1 hx
    have hkle : (k : ℝ) ≤ R / s := by
      rw [le_div_iff₀ hs]
      nlinarith [hxR.2]
    have hkge : -(R / s) - 1 ≤ (k : ℝ) := by
      have hx1 : -R ≤ s * ((k : ℝ) + 1) := le_trans hxR.1 h2
      have hdiv : (-R) / s ≤ (k : ℝ) + 1 := by
        rw [div_le_iff₀ hs]
        linarith
      rw [neg_div] at hdiv
      linarith
    have hceil : R / s ≤ (⌈R / s⌉ : ℝ) := Int.le_ceil _
    refine Finset.mem_Icc.2 ⟨?_, ?_⟩
    · have : ((-N : ℤ) : ℝ) ≤ (k : ℝ) := by
        push_cast [hNdef]
        linarith
      exact_mod_cast this
    · have : (k : ℝ) ≤ ((N : ℤ) : ℝ) := by
        push_cast [hNdef]
        linarith
      exact_mod_cast this
  refine ⟨s, S, hs, hss₀, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, hqsq, hqK⟩ := hp
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := mem_gridSquare.1 hqsq
    have hqR : ‖q‖ ≤ R := by simpa [Complex.dist_eq] using hR hqK
    have hre : |q.re| ≤ R := le_trans (Complex.abs_re_le_norm q) hqR
    have him : |q.im| ≤ R := le_trans (Complex.abs_im_le_norm q) hqR
    refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hbound p.1 q.re hre h1 h2,
      hbound p.2 q.im him h3 h4⟩, ⟨q, hqsq, hqK⟩⟩
  · intro p hp w hw
    obtain ⟨q, hqsq, hqK⟩ := (Finset.mem_filter.1 hp).2
    refine hthick (Metric.mem_thickening_iff.2 ⟨q, hqK, ?_⟩)
    have := dist_le_two_mul_of_mem_gridSquare hs hw hqsq
    linarith

end

end GaloisForLFunctions.HTGeometry
