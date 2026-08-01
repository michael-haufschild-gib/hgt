import GaloisForLFunctions.RHTower.SoninStrictApertureCurvature
import GaloisForLFunctions.RHTower.SoninCouplingLayerOrthogonality

/-!
# The dilation sum does not separate two Sonin layers

The coupling vanishes exactly when the dilation sum carries the inner aperture layer into the
orthogonal complement of the outer one.  It does not vanish, so that separation fails: there are
explicit layer vectors with nonzero pairing across the dilation.

This is the negative answer to the orthogonality criterion, stated on the geometry rather than on
the operator.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

/-- **Layers are not dilation-orthogonal.**  At an actual scale some pair of layer vectors pairs
nontrivially across the dilation sum. -/
theorem exists_scale_soninApertureLayers_not_orthogonal
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b) :
    ∃ (r : ℝ) (hr : 1 < r), c < r * a ∧
      ∃ u v : evenSubspace,
        ⟪evenSoninApertureLayer a b u,
          evenDilationSum r hr (evenSoninApertureLayer b c v)⟫_ℂ ≠ 0 := by
  obtain ⟨r, hr, hcr, hne⟩ := exists_scale_soninApertureCoupling_ne_zero a b c ha hb hab hbc q
    haq hqb
  refine ⟨r, hr, hcr, ?_⟩
  by_contra hcon
  push Not at hcon
  exact hne
    ((evenSoninApertureSuccessiveLayerTransition_eq_zero_iff_layers_orthogonal a b c r hr).mpr
      fun u v => hcon u v)

end RHTower
