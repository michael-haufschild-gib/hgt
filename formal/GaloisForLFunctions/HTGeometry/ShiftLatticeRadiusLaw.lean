import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Order.Filter.ENNReal
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The shift-lattice radius law

A power series whose coefficients are a fixed geometric factor times a
factorially normalized family has a Cauchy--Hadamard growth functional that
scales by exactly the modulus of that factor.  Knowing the radius of convergence
of the series therefore pins the growth of the normalized family, and conversely.

This is the analytic bridge in the cusp--spectrum radius law: the shift-lattice
expansion of a degree-`d` theta function has coefficients
`(2πi)^k F(s - k/d) / k!`, so its radius `R` is equivalent to
`limsup_k |F(s-k/d)/k!|^{1/k} = 1/(2π R)`.

The arithmetic side is the standard-twist spectrum
`{ d(m/q)^{1/d} : a(m) ≠ 0 }`.  It lies in the positive reals, so the distance
from the cusp to it is its infimum, and normalization `a(1) = 1` makes that
infimum exactly `d q^{-1/d}`.  Combining the two gives the cusp constant
`q^{1/d}/(2πd)`.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

section Hadamard

/-- The Cauchy--Hadamard growth functional of a coefficient sequence. -/
noncomputable def hadamardLimsup (c : ℕ → ℂ) : ℝ≥0∞ :=
  limsup (fun n : ℕ => ((‖c n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)) atTop

theorem nnnorm_ofScalars (c : ℕ → ℂ) (n : ℕ) :
    ‖(FormalMultilinearSeries.ofScalars ℂ c) n‖₊ = ‖c n‖₊ := by
  ext
  exact FormalMultilinearSeries.ofScalars_norm ℂ c n

/-- **Cauchy--Hadamard.**  The radius of convergence is the inverse of the growth
functional. -/
theorem radius_ofScalars_eq_inv_hadamardLimsup (c : ℕ → ℂ) :
    (FormalMultilinearSeries.ofScalars ℂ c).radius = (hadamardLimsup c)⁻¹ := by
  rw [FormalMultilinearSeries.radius_eq_liminf, hadamardLimsup, ENNReal.inv_limsup]
  refine liminf_congr (Filter.Eventually.of_forall fun n => ?_)
  rw [nnnorm_ofScalars, one_div ((‖c n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)]

/-- The growth functional scales by the modulus of a geometric factor. -/
theorem hadamardLimsup_geometric (A : ℂ) (c : ℕ → ℂ) :
    hadamardLimsup (fun k => A ^ k * c k)
      = ((‖A‖₊ : ℝ≥0∞)) * hadamardLimsup c := by
  rw [hadamardLimsup, hadamardLimsup,
    ← ENNReal.limsup_const_mul_of_ne_top (ENNReal.coe_ne_top (r := ‖A‖₊))]
  refine limsup_congr ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [nnnorm_mul, nnnorm_pow, NNReal.mul_rpow, ← NNReal.rpow_natCast ‖A‖₊ n,
    ← NNReal.rpow_mul, mul_one_div, div_self hn0, NNReal.rpow_one, ENNReal.coe_mul]

/-- **The shift-lattice radius law.**  A radius of convergence `R` for the
geometrically weighted series is exactly the growth statement
`limsup ‖c k‖^{1/k} = 1/(‖A‖R)` for the normalized family. -/
theorem hadamardLimsup_of_radius {A : ℂ} (hA : A ≠ 0) (c : ℕ → ℂ) {R : ℝ}
    (hR : 0 < R)
    (hrad : (FormalMultilinearSeries.ofScalars ℂ (fun k => A ^ k * c k)).radius
      = ENNReal.ofReal R) :
    hadamardLimsup c = ENNReal.ofReal (1 / (‖A‖ * R)) := by
  have hAnorm : (0 : ℝ) < ‖A‖ := norm_pos_iff.mpr hA
  have hAnn : ((‖A‖₊ : ℝ≥0∞)) ≠ 0 := by
    simpa using hAnorm.ne'
  have hAtop : ((‖A‖₊ : ℝ≥0∞)) ≠ ⊤ := ENNReal.coe_ne_top
  rw [radius_ofScalars_eq_inv_hadamardLimsup, hadamardLimsup_geometric] at hrad
  have hkey : ((‖A‖₊ : ℝ≥0∞)) * hadamardLimsup c = (ENNReal.ofReal R)⁻¹ := by
    rw [← hrad, inv_inv]
  have hinv : (ENNReal.ofReal R)⁻¹ = ENNReal.ofReal R⁻¹ :=
    (ENNReal.ofReal_inv_of_pos hR).symm
  rw [hinv] at hkey
  have hcoe : ((‖A‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖A‖ := by
    rw [ENNReal.ofReal_eq_coe_nnreal hAnorm.le]
    rfl
  rw [hcoe] at hkey
  have := (ENNReal.eq_div_iff (by rwa [← hcoe]) (by rwa [← hcoe])).mpr hkey
  rw [this, ← ENNReal.ofReal_div_of_pos hAnorm]
  congr 1
  field_simp

end Hadamard

section Spectrum

/-- The standard-twist spectrum of a coefficient sequence of degree `d` and
conductor `q`. -/
def shiftSpectrum (a : ℕ → ℂ) (d q : ℝ) : Set ℝ :=
  {x | ∃ m : ℕ, 0 < m ∧ a m ≠ 0 ∧ x = d * ((m : ℝ) / q) ^ (1 / d)}

theorem shiftSpectrum_pos {a : ℕ → ℂ} {d q : ℝ} (hd : 0 < d) (hq : 0 < q)
    {x : ℝ} (hx : x ∈ shiftSpectrum a d q) : 0 < x := by
  obtain ⟨m, hm, -, rfl⟩ := hx
  have hmq : (0 : ℝ) < (m : ℝ) / q := by
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    positivity
  have := Real.rpow_pos_of_pos hmq (1 / d)
  positivity

theorem zero_notMem_shiftSpectrum {a : ℕ → ℂ} {d q : ℝ} (hd : 0 < d) (hq : 0 < q) :
    (0 : ℝ) ∉ shiftSpectrum a d q := fun h =>
  absurd (shiftSpectrum_pos hd hq h) (lt_irrefl 0)

/-- Deleting the cusp from the spectrum changes nothing: the spectrum is
positive. -/
theorem shiftSpectrum_diff_zero {a : ℕ → ℂ} {d q : ℝ} (hd : 0 < d) (hq : 0 < q) :
    shiftSpectrum a d q \ {(0 : ℝ)} = shiftSpectrum a d q := by
  refine Set.eq_of_subset_of_subset Set.sdiff_subset fun x hx => ⟨hx, ?_⟩
  exact fun h => absurd (h ▸ shiftSpectrum_pos hd hq hx) (lt_irrefl 0)

/-- The normalized first coefficient puts `d q^{-1/d}` in the spectrum. -/
theorem base_mem_shiftSpectrum {a : ℕ → ℂ} (ha : a 1 ≠ 0) {d q : ℝ} (hq : 0 < q) :
    d * q ^ (-(1 / d)) ∈ shiftSpectrum a d q := by
  refine ⟨1, one_pos, ha, ?_⟩
  rw [Nat.cast_one, one_div q, Real.inv_rpow hq.le, ← Real.rpow_neg hq.le]

/-- **The cusp gap.**  With a normalized first coefficient, the distance from the
cusp to the standard-twist spectrum is `d q^{-1/d}`. -/
theorem infDist_zero_shiftSpectrum {a : ℕ → ℂ} (ha : a 1 ≠ 0) {d q : ℝ}
    (hd : 0 < d) (hq : 0 < q) :
    Metric.infDist 0 (shiftSpectrum a d q) = d * q ^ (-(1 / d)) := by
  have hmem := base_mem_shiftSpectrum (d := d) ha hq
  have hne : (shiftSpectrum a d q).Nonempty := ⟨_, hmem⟩
  refine le_antisymm ?_ ?_
  · have hle := Metric.infDist_le_dist_of_mem (x := (0 : ℝ)) hmem
    rwa [Real.dist_eq, zero_sub, abs_neg,
      abs_of_pos (shiftSpectrum_pos hd hq hmem)] at hle
  · refine (Metric.le_infDist hne).mpr fun y hy => ?_
    obtain ⟨m, hm, -, rfl⟩ := hy
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hstep : q ^ (-(1 / d)) ≤ ((m : ℝ) / q) ^ (1 / d) := by
      have hbase : (1 : ℝ) / q ≤ (m : ℝ) / q := by
        gcongr
      have := Real.rpow_le_rpow (by positivity) hbase (by positivity : (0:ℝ) ≤ 1 / d)
      rwa [one_div q, Real.inv_rpow hq.le, ← Real.rpow_neg hq.le] at this
    have hpos : (0 : ℝ) < d * ((m : ℝ) / q) ^ (1 / d) := by
      have hmq : (0 : ℝ) < (m : ℝ) / q := by
        have : (0 : ℝ) < (m : ℝ) := by linarith
        positivity
      have := Real.rpow_pos_of_pos hmq (1 / d)
      positivity
    rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos hpos]
    exact mul_le_mul_of_nonneg_left hstep hd.le

end Spectrum

section CuspConstant

/-- The cusp constant identity: the reciprocal of `2π` times the cusp gap is
`q^{1/d}/(2πd)`. -/
theorem cusp_constant_eq {d q : ℝ} (hd : 0 < d) (hq : 0 < q) :
    1 / ((2 * Real.pi) * (d * q ^ (-(1 / d))))
      = q ^ (1 / d) / (2 * Real.pi * d) := by
  have hqd : (0 : ℝ) < q ^ (1 / d) := Real.rpow_pos_of_pos hq _
  rw [Real.rpow_neg hq.le]
  field_simp

/-- **The cusp--spectrum radius law, analytic form.**  If the shift-lattice
expansion at the cusp has radius the cusp gap `d q^{-1/d}`, then the factorially
normalized standard twist grows exactly like `q^{1/d}/(2πd)`. -/
theorem hadamardLimsup_cusp {A : ℂ} (hA : ‖A‖ = 2 * Real.pi) (c : ℕ → ℂ)
    {d q : ℝ} (hd : 0 < d) (hq : 0 < q)
    (hrad : (FormalMultilinearSeries.ofScalars ℂ (fun k => A ^ k * c k)).radius
      = ENNReal.ofReal (d * q ^ (-(1 / d)))) :
    hadamardLimsup c = ENNReal.ofReal (q ^ (1 / d) / (2 * Real.pi * d)) := by
  have hAne : A ≠ 0 := by
    intro h
    rw [h, norm_zero] at hA
    have := Real.pi_pos
    linarith
  have hgap : (0 : ℝ) < d * q ^ (-(1 / d)) := by
    have := Real.rpow_pos_of_pos hq (-(1 / d))
    positivity
  rw [hadamardLimsup_of_radius hAne c hgap hrad, hA, cusp_constant_eq hd hq]

end CuspConstant

end GaloisForLFunctions.HTGeometry
