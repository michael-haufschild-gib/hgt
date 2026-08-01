import GaloisForLFunctions.RHTower.SoninStrictApertureCurvature
import GaloisForLFunctions.RHTower.SoninCouplingSoninCompression

/-!
# The compressed dilation is not block-diagonal on the aperture tower

Inside one Sonin space the coupling is the compression of the dilation sum cut between two
orthogonal layers.  That cut is nonzero, so the compressed dilation has a genuine off-diagonal
block against the aperture tower and cannot be brought to block-diagonal form by it.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- **Nonzero off-diagonal block.**  At an actual dilation scale the Sonin-compressed dilation has
a nonvanishing block between the two aperture layers. -/
theorem exists_scale_soninCompressedDilation_layer_block_ne_zero
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b) :
    ∃ (r : ℝ) (hr : 1 < r), c < r * a ∧
      evenSoninApertureLayer a b * evenSoninCompressedDilation b r hr *
        evenSoninApertureLayer b c ≠ 0 := by
  obtain ⟨r, hr, hcr, hne⟩ := exists_scale_soninApertureCoupling_ne_zero a b c ha hb hab hbc q
    haq hqb
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans hr
  have hba : r⁻¹ * b ≤ a := by
    have hbr : b < r * a := hbc.trans hcr
    rw [inv_mul_le_iff₀ hr0]
    linarith
  refine ⟨r, hr, hcr, ?_⟩
  intro hzero
  exact hne
    ((evenSoninApertureSuccessiveLayerTransition_eq_zero_iff_compression_orthogonal
      hb.le hab.le hbc.le hr hba).mpr hzero)

end RHTower
