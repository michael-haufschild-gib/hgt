import Mathlib

/-!
# Unit windows around an arithmetic lattice cover a compact interval

A valuation coset of a single visible prime is an arithmetic progression of centers with spacing
`log p`.  When the spacing is smaller than the window radius doubled, the open windows around those
centers cover the line, and compactness selects a finite subcover of any closed interval.  The
weight inequality `r ^ (1 - 2 sigma) >= 1` on `(0,1)` for `sigma > 1/2` is the other elementary
input: a negative exponent only increases a number below one.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-! ## The weight inequality -/

/-- For an exponent above one half the chart weight is at least one on the unit window. -/
theorem one_le_rpow_one_sub_two_mul {r σ : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hσ : 1 / 2 < σ) :
    1 ≤ r ^ (1 - 2 * σ) :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr0 hr1 (by linarith)

/-- Hence the weighted chart integrand dominates the unweighted one. -/
theorem le_rpow_mul {r σ c : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hσ : 1 / 2 < σ) (hc : 0 ≤ c) :
    c ≤ r ^ (1 - 2 * σ) * c := by
  nlinarith [one_le_rpow_one_sub_two_mul hr0 hr1 hσ]

/-! ## The lattice of valuation centers -/

/-- The centers of one valuation coset: an arithmetic progression anchored at `a` with spacing
`s`. -/
def latticeCenter (a s : ℝ) (k : ℤ) : ℝ := a - k * s

theorem latticeCenter_zero (a s : ℝ) : latticeCenter a s 0 = a := by
  simp [latticeCenter]

/-- Consecutive centers are exactly one spacing apart. -/
theorem latticeCenter_sub_succ (a s : ℝ) (k : ℤ) :
    latticeCenter a s k - latticeCenter a s (k + 1) = s := by
  simp only [latticeCenter]
  push_cast
  ring

/-- Every real point lies within half a spacing of some center. -/
theorem exists_latticeCenter_close {s : ℝ} (hs : 0 < s) (a x : ℝ) :
    ∃ k : ℤ, |x - latticeCenter a s k| ≤ s / 2 := by
  refine ⟨round ((a - x) / s), ?_⟩
  have hround : |(a - x) / s - (round ((a - x) / s) : ℤ)| ≤ 1 / 2 := abs_sub_round _
  have hx : x - latticeCenter a s (round ((a - x) / s)) =
      -(((a - x) / s - (round ((a - x) / s) : ℤ)) * s) := by
    simp only [latticeCenter]
    field_simp
    ring
  rw [hx, abs_neg, abs_mul, abs_of_pos hs]
  calc |(a - x) / s - (round ((a - x) / s) : ℤ)| * s ≤ (1 / 2) * s :=
        mul_le_mul_of_nonneg_right hround hs.le
    _ = s / 2 := by ring

/-- The open windows of radius `w` around the centers cover the line as soon as the spacing is
below `2 w`. -/
theorem iUnion_latticeWindow_eq_univ {s w : ℝ} (hs : 0 < s) (hw : s / 2 < w) (a : ℝ) :
    (⋃ k : ℤ, Ioo (latticeCenter a s k - w) (latticeCenter a s k + w)) = univ := by
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨k, hk⟩ := exists_latticeCenter_close hs a x
  refine mem_iUnion.mpr ⟨k, ?_⟩
  have h1 : |x - latticeCenter a s k| < w := lt_of_le_of_lt hk hw
  rw [abs_lt] at h1
  exact ⟨by linarith [h1.1], by linarith [h1.2]⟩

/-- **Finite chart cover.**  A closed interval is covered by finitely many unit windows of one
valuation coset whenever the coset spacing is below twice the window radius. -/
theorem exists_finset_latticeWindow_cover {s w : ℝ} (hs : 0 < s) (hw : s / 2 < w) (a b c : ℝ) :
    ∃ t : Finset ℤ,
      Icc b c ⊆ ⋃ k ∈ t, Ioo (latticeCenter a s k - w) (latticeCenter a s k + w) := by
  have hcompact : IsCompact (Icc b c) := isCompact_Icc
  have hopen : ∀ k : ℤ, IsOpen (Ioo (latticeCenter a s k - w) (latticeCenter a s k + w)) :=
    fun _ => isOpen_Ioo
  have hcover : Icc b c ⊆ ⋃ k : ℤ, Ioo (latticeCenter a s k - w) (latticeCenter a s k + w) := by
    rw [iUnion_latticeWindow_eq_univ hs hw a]
    exact subset_univ _
  obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover _ hopen hcover
  exact ⟨t, ht⟩

/-- **Small-aperture window.**  When the aperture is shorter than half a unit, the single window of
radius one at the right endpoint already contains the whole open interval. -/
theorem Ioo_subset_endpointWindow {a : ℝ} (ha : 2 * a ≤ 1) :
    Ioo (-a) a ⊆ Ioo (a - 1) a := fun _ hx => ⟨by linarith [hx.1], hx.2⟩

/-! ## The dyadic instance -/

/-- The dyadic valuation centers `a - k log 2`. -/
noncomputable def dyadicCenter (a : ℝ) (k : ℤ) : ℝ := latticeCenter a (Real.log 2) k

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem log_two_lt_one : Real.log 2 < 1 := by
  have h := Real.log_two_lt_d9
  norm_num at h ⊢
  linarith

/-- Consecutive dyadic centers are `log 2 < 1` apart. -/
theorem dyadicCenter_spacing (a : ℝ) (k : ℤ) :
    dyadicCenter a k - dyadicCenter a (k + 1) = Real.log 2 :=
  latticeCenter_sub_succ a (Real.log 2) k

/-- Every point is within `log 2 / 2 < 1` of a dyadic center. -/
theorem exists_dyadicCenter_close (a x : ℝ) :
    ∃ k : ℤ, |x - dyadicCenter a k| ≤ Real.log 2 / 2 :=
  exists_latticeCenter_close log_two_pos a x

/-- **Dyadic unit-chart cover.**  Finitely many unit windows around dyadic valuation centers cover
any compact aperture. -/
theorem exists_finset_dyadicWindow_cover (a b c : ℝ) :
    ∃ t : Finset ℤ, Icc b c ⊆ ⋃ k ∈ t, Ioo (dyadicCenter a k - 1) (dyadicCenter a k + 1) :=
  exists_finset_latticeWindow_cover log_two_pos
    (by linarith [log_two_lt_one, log_two_pos]) a b c

/-- When the prime `2` is invisible — the aperture is shorter than `log 2` — the aperture is inside
one unit window at its right endpoint. -/
theorem Ioo_subset_endpointWindow_of_invisible_two {a : ℝ} (ha : 2 * a < Real.log 2) :
    Ioo (-a) a ⊆ Ioo (a - 1) a :=
  Ioo_subset_endpointWindow (le_of_lt (lt_trans ha log_two_lt_one))

end GaloisForLFunctions.HTGeometry
