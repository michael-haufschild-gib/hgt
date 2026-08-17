import GaloisForLFunctions.RHTower.SuzukiLatticeShellSummability
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Almost every aperture has finite logarithmic type

An aperture resonates with a valuation label when the clock offset `2a - ℓ(ν)` is small but
nonzero, and the depth of the resonance is measured against the logarithm of the label size.  The
apertures whose resonance at `ν` is deeper than the polynomial scale `(2 + |ν|₁)^{-q}` form an
interval of length exactly that scale, so the total bad measure is the lattice power series
`∑_ν (2 + |ν|₁)^{-q}`, convergent for `q > d`.

Borel–Cantelli then leaves only a finite exceptional set of labels for almost every aperture, and
outside that set the defect obeys the logarithmic bound

`-log |2a - ℓ(ν)| ≤ q log (2 + |ν|₁)`,

which is finiteness of the logarithmic type.
-/

open MeasureTheory Filter Set

noncomputable section

namespace RHTower

variable {d : ℕ} {q : ℝ}

/-! ## The bad window at one label -/

/-- The apertures resonating with a valuation label below the polynomial scale. -/
def badAperture (ℓ : (Fin d → ℤ) → ℝ) (q : ℝ) (ν : Fin d → ℤ) : Set ℝ :=
  {a : ℝ | 0 < |2 * a - ℓ ν| ∧ |2 * a - ℓ ν| < (2 + (latticeL1 ν : ℝ)) ^ (-q)}

/-- **`(26)`: the bad window is an interval of the polynomial scale.** -/
theorem badAperture_subset (ℓ : (Fin d → ℤ) → ℝ) (q : ℝ) (ν : Fin d → ℤ) :
    badAperture ℓ q ν ⊆
      Ioo ((ℓ ν - (2 + (latticeL1 ν : ℝ)) ^ (-q)) / 2)
        ((ℓ ν + (2 + (latticeL1 ν : ℝ)) ^ (-q)) / 2) := by
  intro a ha
  obtain ⟨-, h2⟩ := ha
  rw [abs_lt] at h2
  exact ⟨by linarith [h2.1], by linarith [h2.2]⟩

/-- **`(26)`: the bad window has at most the polynomial length.** -/
theorem measure_badAperture_le (ℓ : (Fin d → ℤ) → ℝ) (q : ℝ) (ν : Fin d → ℤ) :
    volume (badAperture ℓ q ν) ≤ ENNReal.ofReal ((2 + (latticeL1 ν : ℝ)) ^ (-q)) := by
  refine le_trans (measure_mono (badAperture_subset ℓ q ν)) ?_
  rw [Real.volume_Ioo]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  ring

/-! ## The total bad measure -/

/-- **`(27)`: the bad windows have summable lengths above the lattice dimension.** -/
theorem summable_badAperture_length (hd : 0 < d) (hq : (d : ℝ) < q) :
    Summable (fun ν : Fin d → ℤ => (2 + (latticeL1 ν : ℝ)) ^ (-q)) := by
  have hq0 : 0 < q := lt_of_le_of_lt (Nat.cast_nonneg d) hq
  refine Summable.of_nonneg_of_le (fun ν => Real.rpow_nonneg (by positivity) _)
    (fun ν => ?_) (summable_polyDecay_fin hd hq)
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)

theorem tsum_measure_badAperture_ne_top (ℓ : (Fin d → ℤ) → ℝ) (hd : 0 < d) (hq : (d : ℝ) < q) :
    ∑' ν : Fin d → ℤ, volume (badAperture ℓ q ν) ≠ ⊤ := by
  have hsum := summable_badAperture_length (q := q) hd hq
  have hnn : ∀ ν : Fin d → ℤ, 0 ≤ (2 + (latticeL1 ν : ℝ)) ^ (-q) :=
    fun ν => Real.rpow_nonneg (by positivity) _
  have hle : ∑' ν : Fin d → ℤ, volume (badAperture ℓ q ν)
      ≤ ∑' ν : Fin d → ℤ, ENNReal.ofReal ((2 + (latticeL1 ν : ℝ)) ^ (-q)) :=
    ENNReal.tsum_le_tsum fun ν => measure_badAperture_le ℓ q ν
  refine ne_top_of_le_ne_top ?_ hle
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum]
  exact ENNReal.ofReal_ne_top

/-! ## The Borel–Cantelli conclusion -/

/-- Almost every aperture is resonant below the polynomial scale at only finitely many labels. -/
theorem ae_finite_badAperture (ℓ : (Fin d → ℤ) → ℝ) (hd : 0 < d) (hq : (d : ℝ) < q) :
    ∀ᵐ a : ℝ, {ν : Fin d → ℤ | a ∈ badAperture ℓ q ν}.Finite := by
  have h0 := measure_limsup_cofinite_eq_zero (μ := (volume : Measure ℝ))
    (tsum_measure_badAperture_ne_top ℓ hd hq)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with a ha
  rw [Filter.mem_limsup_iff_frequently_mem, Filter.frequently_cofinite_iff_infinite] at ha
  exact Set.not_infinite.mp ha

/-- Off the bad window the resonance depth is logarithmic in the label size. -/
theorem log_defect_le_of_not_mem {ℓ : (Fin d → ℤ) → ℝ} {a : ℝ} {ν : Fin d → ℤ}
    (hpos : 0 < |2 * a - ℓ ν|) (hnot : a ∉ badAperture ℓ q ν) :
    -Real.log |2 * a - ℓ ν| ≤ q * Real.log (2 + (latticeL1 ν : ℝ)) := by
  have hb : (0 : ℝ) < 2 + (latticeL1 ν : ℝ) := by positivity
  have hge : (2 + (latticeL1 ν : ℝ)) ^ (-q) ≤ |2 * a - ℓ ν| := by
    by_contra h
    exact hnot ⟨hpos, not_le.mp h⟩
  have hlog : Real.log ((2 + (latticeL1 ν : ℝ)) ^ (-q)) ≤ Real.log |2 * a - ℓ ν| :=
    Real.log_le_log (Real.rpow_pos_of_pos hb _) hge
  rw [Real.log_rpow hb] at hlog
  linarith

/-- **`(28)`: the logarithmic type is finite for almost every aperture.**  Outside a finite set of
valuation labels, every nonresonant defect is at least the polynomial scale, so its logarithm is
bounded by the logarithm of the label size. -/
theorem ae_finite_logType (ℓ : (Fin d → ℤ) → ℝ) (hd : 0 < d) (hq : (d : ℝ) < q) :
    ∀ᵐ a : ℝ, ∃ F : Finset (Fin d → ℤ), ∀ ν ∉ F, 0 < |2 * a - ℓ ν| →
      -Real.log |2 * a - ℓ ν| ≤ q * Real.log (2 + (latticeL1 ν : ℝ)) := by
  filter_upwards [ae_finite_badAperture ℓ hd hq] with a ha
  refine ⟨ha.toFinset, fun ν hν hpos => ?_⟩
  refine log_defect_le_of_not_mem hpos fun hmem => hν ?_
  exact ha.mem_toFinset.mpr hmem

end RHTower
