import GaloisForLFunctions.HTGeometry.ShiftLatticeRadiusLaw

/-!
# Nearest-neighbour spacing in the standard-twist spectrum

The spectral locations `d (m/q)^(1/d)` are strictly increasing in the source index.  Therefore the
distance from a supported location to every other supported location is bounded below by the
smaller adjacent full-lattice gap.  When both adjacent coefficients are nonzero, this lower bound
is exact.
-/

namespace GaloisForLFunctions.HTGeometry

open Topology

noncomputable section

/-- The full standard-twist spectral lattice before deleting zero coefficients. -/
def shiftSpectrumValue (d q : ℝ) (m : ℕ) : ℝ :=
  d * ((m : ℝ) / q) ^ (1 / d)

/-- Positive degree and conductor make the full spectral lattice strictly increasing. -/
theorem strictMono_shiftSpectrumValue {d q : ℝ} (hd : 0 < d) (hq : 0 < q) :
    StrictMono (shiftSpectrumValue d q) := by
  intro m n hmn
  have hcast : (m : ℝ) / q < (n : ℝ) / q := by
    exact div_lt_div_of_pos_right (by exact_mod_cast hmn) hq
  have hrpow : ((m : ℝ) / q) ^ (1 / d) < ((n : ℝ) / q) ^ (1 / d) :=
    Real.rpow_lt_rpow (by positivity) hcast (by positivity)
  exact mul_lt_mul_of_pos_left hrpow hd

/-- Membership in the standard-twist spectrum is membership of a supported full-lattice value. -/
theorem shiftSpectrumValue_mem {a : ℕ → ℂ} {d q : ℝ} {m : ℕ}
    (hm : 0 < m) (ha : a m ≠ 0) :
    shiftSpectrumValue d q m ∈ shiftSpectrum a d q :=
  ⟨m, hm, ha, rfl⟩

/-- Every other supported spectral point is at least one adjacent full-lattice gap away. -/
theorem min_adjacent_gap_le_dist_of_mem_shiftSpectrum_ne
    {a : ℕ → ℂ} {d q : ℝ} (hd : 0 < d) (hq : 0 < q)
    {m : ℕ} {y : ℝ}
    (hy : y ∈ shiftSpectrum a d q) (hne : y ≠ shiftSpectrumValue d q m) :
    min
        (shiftSpectrumValue d q m - shiftSpectrumValue d q (m - 1))
        (shiftSpectrumValue d q (m + 1) - shiftSpectrumValue d q m)
      ≤ dist (shiftSpectrumValue d q m) y := by
  obtain ⟨n, hn, -, rfl⟩ := hy
  have hmono := strictMono_shiftSpectrumValue hd hq
  have hnm : n ≠ m := by
    intro h
    exact hne (congrArg (shiftSpectrumValue d q) h)
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · have hnm1 : n ≤ m - 1 := Nat.le_sub_one_of_lt hlt
    have hval_le : shiftSpectrumValue d q n ≤ shiftSpectrumValue d q (m - 1) :=
      hmono.monotone hnm1
    have hval_lt : shiftSpectrumValue d q n < shiftSpectrumValue d q m := hmono hlt
    change min
        (shiftSpectrumValue d q m - shiftSpectrumValue d q (m - 1))
        (shiftSpectrumValue d q (m + 1) - shiftSpectrumValue d q m) ≤
      dist (shiftSpectrumValue d q m) (shiftSpectrumValue d q n)
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hval_lt.le)]
    exact (min_le_left _ _).trans (sub_le_sub_left hval_le _)
  · have hm1n : m + 1 ≤ n := Nat.lt_iff_add_one_le.mp hgt
    have hval_le : shiftSpectrumValue d q (m + 1) ≤ shiftSpectrumValue d q n :=
      hmono.monotone hm1n
    have hval_lt : shiftSpectrumValue d q m < shiftSpectrumValue d q n := hmono hgt
    change min
        (shiftSpectrumValue d q m - shiftSpectrumValue d q (m - 1))
        (shiftSpectrumValue d q (m + 1) - shiftSpectrumValue d q m) ≤
      dist (shiftSpectrumValue d q m) (shiftSpectrumValue d q n)
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hval_lt.le), neg_sub]
    exact (min_le_right _ _).trans (sub_le_sub_right hval_le _)

/-- If both adjacent indices are supported, the nearest-other-spectrum distance is exactly the
smaller adjacent full-lattice gap. -/
theorem infDist_shiftSpectrum_diff_eq_min_adjacent
    {a : ℕ → ℂ} {d q : ℝ} (hd : 0 < d) (hq : 0 < q)
    {m : ℕ} (hm : 1 < m) (hprev : a (m - 1) ≠ 0) (hnext : a (m + 1) ≠ 0) :
    Metric.infDist (shiftSpectrumValue d q m)
        (shiftSpectrum a d q \ {shiftSpectrumValue d q m}) =
      min
        (shiftSpectrumValue d q m - shiftSpectrumValue d q (m - 1))
        (shiftSpectrumValue d q (m + 1) - shiftSpectrumValue d q m) := by
  let x := shiftSpectrumValue d q m
  let xprev := shiftSpectrumValue d q (m - 1)
  let xnext := shiftSpectrumValue d q (m + 1)
  have hmono := strictMono_shiftSpectrumValue hd hq
  have hmPrev : 0 < m - 1 := Nat.sub_pos_of_lt hm
  have hprev_lt : xprev < x := hmono (Nat.sub_lt (by omega) (by omega))
  have hnext_gt : x < xnext := hmono (Nat.lt_succ_self m)
  have hprevMem : xprev ∈ shiftSpectrum a d q \ {x} := by
    refine ⟨shiftSpectrumValue_mem hmPrev hprev, ?_⟩
    simpa using hprev_lt.ne
  have hnextMem : xnext ∈ shiftSpectrum a d q \ {x} := by
    refine ⟨shiftSpectrumValue_mem (by omega) hnext, ?_⟩
    simpa using hnext_gt.ne'
  have hnonempty : (shiftSpectrum a d q \ {x}).Nonempty := ⟨xnext, hnextMem⟩
  apply le_antisymm
  · apply le_min
    · have hle := Metric.infDist_le_dist_of_mem (x := x) hprevMem
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hprev_lt.le)] at hle
      exact hle
    · have hle := Metric.infDist_le_dist_of_mem (x := x) hnextMem
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hnext_gt.le), neg_sub] at hle
      exact hle
  · apply (Metric.le_infDist hnonempty).mpr
    intro y hy
    exact min_adjacent_gap_le_dist_of_mem_shiftSpectrum_ne hd hq hy.1
      (by simpa [x] using hy.2)

end

end GaloisForLFunctions.HTGeometry
