import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FirstClockIndex.ClockScales

/-! # Exponential decay of the time-mesh union bound -/

open Set Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons
noncomputable section

/-- With d+3 energy levels, the cost of testing a b^(-(d+3)) window
is absorbed by the smaller base y of the one-test probability. -/
theorem grid_count_decay {y b δ : ℝ} (hy : 0 < y) (hyb : y < b) (hb : b < 1) (hd : 0 < δ) :
    ∃ c∈Ioo (0:ℝ) 1, ∀ᶠ d : ℕ in atTop,
      ((⌈(1/b)^(d+3)/δ⌉₊:ℝ)+1)*((d:ℝ)+2)*y^d < c^d := by
  have hbp := hy.trans hyb
  let u := (1/b)*y
  have hu : 0 < u := mul_pos (one_div_pos.mpr hbp) hy
  have hu1 : u < 1 := by rw [show u=y/b by dsimp only [u]; ring]; exact (div_lt_one hbp).mpr hyb
  obtain ⟨c,huc,hc⟩ := exists_between hu1
  let C := (1/δ+2)*(1/b)^3
  have hC : 0 ≤ C := mul_nonneg (add_nonneg (one_div_nonneg.mpr hd.le) zero_le_two)
    (pow_nonneg (one_div_nonneg.mpr hbp.le) _)
  refine ⟨c,⟨hu.trans huc,hc⟩,?_⟩
  filter_upwards [FirstClockIndex.linear_mul_pow_eventually_lt (2*C) hu huc] with d hlim
  let H := (1/b)^(d+3)
  have hH : 1 ≤ H := one_le_pow₀ ((one_le_div hbp).mpr hb.le)
  have hround : (⌈H/δ⌉₊:ℝ)+1 ≤ (1/δ+2)*H := by
    have hh := Nat.ceil_lt_add_one (div_nonneg (zero_le_one.trans hH) hd.le)
    rw [add_mul,one_div_mul_eq_div]
    linarith only [hh,hH]
  calc ((⌈H/δ⌉₊:ℝ)+1)*((d:ℝ)+2)*y^d ≤ ((1/δ+2)*H)*((d:ℝ)+2)*y^d :=
         mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hround (by positivity)) (pow_nonneg hy.le _)
       _ = C*((d:ℝ)+2)*u^d := by dsimp only [C,H,u]; rw [pow_add,mul_pow]; ring
       _ ≤ (2*C)*((d:ℝ)+1)*u^d := by
         apply mul_le_mul_of_nonneg_right _ (pow_nonneg hu.le _)
         nlinarith only [mul_nonneg hC (Nat.cast_nonneg (α:=ℝ) d)]
       _ < c^d := hlim

#print axioms grid_count_decay
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons
