import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Summable failure probabilities over prefixes and mode packets -/
open Filter MeasureTheory Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SpectralJets.AllHeights

/-- At most finitely many prefixes have an exception at any packet index.
The exception sets may be nonmeasurable, since all bounds use outer measure. -/
theorem eventually_no_packet {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (F : ℕ → ℕ → Set Ω)
    (hm : ∀ k j, μ (F k j) ≤ (1/2:ℝ≥0∞)^(k+j+1)) :
    ∀ᵐ ω ∂μ, ∀ᶠ k : ℕ in atTop, ∀ j, ω ∉ F k j := by
  let b := (1/2:ℝ≥0∞)
  have hgeo : ∑' j : ℕ, b^j=2 := by
    simpa only [b,one_div] using ENNReal.tsum_geometric_two
  have hprefix (k : ℕ) : μ (⋃ j, F k j) ≤ b^k := by
    apply (measure_iUnion_le _).trans
    apply (ENNReal.tsum_le_tsum (hm k)).trans
    have hs (j : ℕ) : b^(k+j+1)=b^k*b*b^j := by rw [pow_succ,pow_add]; ac_rfl
    change (∑' j : ℕ, b^(k+j+1)) ≤ _
    simp_rw [hs]
    have hb : b*2=1 := by
      rw [show b=(2:ℝ≥0∞)⁻¹ from one_div _]
      exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
    rw [ENNReal.tsum_mul_left,hgeo,mul_assoc,hb,mul_one]
  have hev : ∀ᵐ ω ∂μ, ∀ᶠ k : ℕ in atTop, ω ∉ ⋃ j, F k j :=
    ae_eventually_notMem (ne_top_of_le_ne_top (show (∑' j : ℕ, b^j) ≠ ⊤ by rw [hgeo]; norm_num)
      (ENNReal.tsum_le_tsum hprefix))
  filter_upwards [hev] with ω hw
  filter_upwards [hw] with k hk j
  exact fun h => hk (mem_iUnion.mpr ⟨j,h⟩)

end GaloisForLFunctions.HTGeometry.SpectralJets.AllHeights
