import GaloisForLFunctions.HTGeometry.ShiftLatticeRadiusLaw
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Spacing of the standard-twist spectrum

The spectrum `{ d(m/q)^{1/d} : a(m) ≠ 0 }` is the image of the integers under a
concave power map, so its consecutive gaps are the derivative of that map at an
interior point: `q^{-1}(ξ/q)^{1/d - 1}`.  Above degree one the exponent is
negative, so the gaps tend to zero — the spectrum accumulates.

This is the quantitative reason the standard twist's bounds must degrade in the
twist parameter: the local spectral spacing shrinks, and the radius of the
shift-lattice expansion at a spectral point is that spacing.

The companion statement is that the degree-one lattice, whose spacing stays
equal to one, is useless above degree one: its coefficients grow like
`(d^d k^{d-1})^k`, so the corresponding expansion has radius zero.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

section Decay

/-- A negative power tends to zero at infinity. -/
theorem tendsto_rpow_neg_nhds_zero {c : ℝ} (hc : c < 0) :
    Tendsto (fun x : ℝ => x ^ c) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => x ^ (-c)) atTop atTop :=
    tendsto_rpow_atTop (by linarith)
  refine (h1.inv_tendsto_atTop).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [Pi.inv_apply]
  rw [← Real.rpow_neg hx.le, neg_neg]

end Decay

section Spacing

variable {d q : ℝ}

/-- The `m`-th point of the standard-twist spectrum. -/
noncomputable def shiftSpectrumPoint (d q : ℝ) (m : ℕ) : ℝ :=
  d * ((m : ℝ) / q) ^ (1 / d)

/-- The spectral map, as a function of a real argument. -/
noncomputable def shiftSpectrumMap (d q : ℝ) (x : ℝ) : ℝ := d * (x / q) ^ (1 / d)

/-- The derivative of the spectral map. -/
noncomputable def shiftSpectrumSlope (d q : ℝ) (x : ℝ) : ℝ :=
  q⁻¹ * (x / q) ^ (1 / d - 1)

theorem shiftSpectrumMap_natCast (d q : ℝ) (m : ℕ) :
    shiftSpectrumMap d q m = shiftSpectrumPoint d q m := rfl

theorem hasDerivAt_shiftSpectrumMap (hd : 0 < d) (hq : 0 < q) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (shiftSpectrumMap d q) (shiftSpectrumSlope d q x) x := by
  have hxq : x / q ≠ 0 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => y / q) q⁻¹ x := by
    simpa [one_div] using (hasDerivAt_id x).div_const q
  have h2 : HasDerivAt (fun y : ℝ => y ^ (1 / d))
      ((1 / d) * (x / q) ^ (1 / d - 1)) (x / q) :=
    Real.hasDerivAt_rpow_const (Or.inl hxq)
  have h3 := (h2.comp x h1).const_mul d
  refine h3.congr_deriv ?_
  rw [shiftSpectrumSlope]
  field_simp

/-- The consecutive spacing of the spectrum. -/
noncomputable def shiftSpectrumGap (d q : ℝ) (m : ℕ) : ℝ :=
  shiftSpectrumPoint d q (m + 1) - shiftSpectrumPoint d q m

/-- **The spacing is a derivative at an interior point.** -/
theorem exists_shiftSpectrumGap_eq (hd : 0 < d) (hq : 0 < q) {m : ℕ} (hm : 0 < m) :
    ∃ ξ : ℝ, (m : ℝ) < ξ ∧ ξ < (m : ℝ) + 1 ∧
      shiftSpectrumGap d q m = shiftSpectrumSlope d q ξ := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hlt : (m : ℝ) < (m : ℝ) + 1 := by linarith
  have hderiv : ∀ x ∈ Set.Ioo (m : ℝ) ((m : ℝ) + 1),
      HasDerivAt (shiftSpectrumMap d q) (shiftSpectrumSlope d q x) x := by
    intro x hx
    exact hasDerivAt_shiftSpectrumMap hd hq (lt_trans hmR hx.1)
  have hcont : ContinuousOn (shiftSpectrumMap d q) (Set.Icc (m : ℝ) ((m : ℝ) + 1)) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hmR hx.1
    exact ((hasDerivAt_shiftSpectrumMap hd hq hx0).continuousAt).continuousWithinAt
  obtain ⟨ξ, hξ, hslope⟩ :=
    exists_hasDerivAt_eq_slope (shiftSpectrumMap d q) (shiftSpectrumSlope d q) hlt
      hcont hderiv
  refine ⟨ξ, hξ.1, hξ.2, ?_⟩
  rw [shiftSpectrumGap, hslope]
  have hden : ((m : ℝ) + 1) - (m : ℝ) = 1 := by ring
  rw [hden, div_one]
  have hcast : shiftSpectrumMap d q ((m : ℝ) + 1)
      = shiftSpectrumPoint d q (m + 1) := by
    rw [shiftSpectrumMap, shiftSpectrumPoint]
    norm_num
  rw [hcast, shiftSpectrumMap_natCast]

/-- The spacing is bounded by the slope at the left endpoint. -/
theorem shiftSpectrumGap_le (hd : 1 < d) (hq : 0 < q) {m : ℕ} (hm : 0 < m) :
    shiftSpectrumGap d q m ≤ q⁻¹ * ((m : ℝ) / q) ^ (1 / d - 1) := by
  have hd0 : 0 < d := by linarith
  obtain ⟨ξ, hξ1, -, hgap⟩ := exists_shiftSpectrumGap_eq hd0 hq hm
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hexp : 1 / d - 1 ≤ 0 := by
    have : 1 / d < 1 := by
      rw [div_lt_one (by linarith)]
      exact hd
    linarith
  have hmono : (ξ / q) ^ (1 / d - 1) ≤ ((m : ℝ) / q) ^ (1 / d - 1) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by gcongr) hexp
  rw [hgap, shiftSpectrumSlope]
  exact mul_le_mul_of_nonneg_left hmono (by positivity)

theorem shiftSpectrumGap_nonneg (hd : 0 < d) (hq : 0 < q) (m : ℕ) :
    0 ≤ shiftSpectrumGap d q m := by
  rw [shiftSpectrumGap, sub_nonneg, shiftSpectrumPoint, shiftSpectrumPoint]
  refine mul_le_mul_of_nonneg_left ?_ hd.le
  refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
  gcongr
  exact_mod_cast Nat.le_succ m

/-- **The spectrum accumulates above degree one.**  Its consecutive spacings tend
to zero, so the local spectral gap — which is the radius of the shift-lattice
expansion at a spectral point — degrades without bound. -/
theorem tendsto_shiftSpectrumGap_nhds_zero (hd : 1 < d) (hq : 0 < q) :
    Tendsto (fun m : ℕ => shiftSpectrumGap d q m) atTop (𝓝 0) := by
  have hd0 : 0 < d := by linarith
  have hexp : 1 / d - 1 < 0 := by
    have : 1 / d < 1 := by
      rw [div_lt_one (by linarith)]
      exact hd
    linarith
  have hdiv : Tendsto (fun m : ℕ => (m : ℝ) / q) atTop atTop :=
    Filter.Tendsto.atTop_div_const hq tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun m : ℕ => ((m : ℝ) / q) ^ (1 / d - 1)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_nhds_zero hexp).comp hdiv
  have hbound : Tendsto (fun m : ℕ => q⁻¹ * ((m : ℝ) / q) ^ (1 / d - 1)) atTop (𝓝 0) := by
    simpa using hpow.const_mul q⁻¹
  refine squeeze_zero' ?_ ?_ hbound
  · filter_upwards with m using shiftSpectrumGap_nonneg hd0 hq m
  · filter_upwards [eventually_gt_atTop 0] with m hm
    exact shiftSpectrumGap_le hd hq hm

/-- **The spectral gap at a base point**: the distance from `α₀` to the rest of
the standard-twist spectrum. -/
noncomputable def spectralGap (a : ℕ → ℂ) (d q : ℝ) (α₀ : ℝ) : ℝ :=
  Metric.infDist α₀ (shiftSpectrum a d q \ {α₀})

/-- **The cusp gap.**  At the cusp the deleted point is absent from the spectrum,
so the gap is the distance to the whole spectrum, namely `d q^{-1/d}`. -/
theorem spectralGap_zero {a : ℕ → ℂ} (ha : a 1 ≠ 0) (hd : 0 < d) (hq : 0 < q) :
    spectralGap a d q 0 = d * q ^ (-(1 / d)) := by
  rw [spectralGap, shiftSpectrum_diff_zero hd hq, infDist_zero_shiftSpectrum ha hd hq]

/-- The gap at a spectral point is at most the distance to the next one. -/
theorem spectralGap_le_shiftSpectrumGap {a : ℕ → ℂ} {m : ℕ}
    (hm : 0 < m) (hnext : a (m + 1) ≠ 0) (hd : 0 < d) (hq : 0 < q) :
    spectralGap a d q (shiftSpectrumPoint d q m) ≤ shiftSpectrumGap d q m := by
  have hmem : shiftSpectrumPoint d q (m + 1)
      ∈ shiftSpectrum a d q \ {shiftSpectrumPoint d q m} := by
    refine ⟨⟨m + 1, Nat.succ_pos m, hnext, rfl⟩, ?_⟩
    intro hcon
    have hlt : shiftSpectrumPoint d q m < shiftSpectrumPoint d q (m + 1) := by
      rw [shiftSpectrumPoint, shiftSpectrumPoint]
      have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      refine mul_lt_mul_of_pos_left ?_ hd
      refine Real.rpow_lt_rpow (by positivity) ?_ (by positivity)
      gcongr
      exact_mod_cast Nat.lt_succ_self m
    rw [Set.mem_singleton_iff] at hcon
    exact absurd hcon.symm (ne_of_lt hlt)
  have hle : spectralGap a d q (shiftSpectrumPoint d q m)
      ≤ dist (shiftSpectrumPoint d q m) (shiftSpectrumPoint d q (m + 1)) :=
    Metric.infDist_le_dist_of_mem hmem
  rwa [Real.dist_eq, abs_sub_comm,
    abs_of_nonneg (by
      rw [← shiftSpectrumGap]
      exact shiftSpectrumGap_nonneg hd hq m), ← shiftSpectrumGap] at hle

end Spacing

section DegreeOneLattice

/-- **The degree-one lattice is useless above degree one.**  With spacing one the
`k`-th coefficient of the shift-lattice expansion grows like `(d^d k^{d-1})^k`,
whose `k`-th root diverges, so the expansion has radius zero. -/
theorem tendsto_degreeOneLatticeRoot_atTop {d : ℕ} (hd : 2 ≤ d) {c : ℝ}
    (hc : 0 < c) :
    Tendsto (fun k : ℕ => (d : ℝ) ^ d * (k : ℝ) ^ (d - 1) * c) atTop atTop := by
  have hd1 : 1 ≤ d - 1 := by omega
  have hk : Tendsto (fun k : ℕ => (k : ℝ) ^ (d - 1)) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_) tendsto_natCast_atTop_atTop
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp [zero_pow (show d - 1 ≠ 0 by omega)]
    · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkpos
      exact le_self_pow₀ hk1 (by omega)
  have hconst : (0 : ℝ) < (d : ℝ) ^ d := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    positivity
  exact ((hk.const_mul_atTop hconst).atTop_mul_const hc)

end DegreeOneLattice

end GaloisForLFunctions.HTGeometry
