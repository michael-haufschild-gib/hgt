import GaloisForLFunctions.RHTower.SuzukiAperturePositionOperator
import GaloisForLFunctions.RHTower.SuzukiTaCovarianceReflection

/-!
# Position is odd under Suzuki reflection

Physical reflection reverses the literal bounded aperture coordinate.  The proof remains in the
actual interval/whole-line unitary: zero extension intertwines interval reflection with whole-line
reflection and intertwines aperture position with multiplication by `x`.
-/

open Complex MeasureTheory

noncomputable section
namespace RHTower

/-- Exact anticommutation `Jₐ Xₐ = -Xₐ Jₐ` on the literal Suzuki interval. -/
theorem suzukiWeilIntervalReflection_position_anticommute
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    suzukiWeilIntervalReflection a (suzukiAperturePosition a f) =
      -suzukiAperturePosition a (suzukiWeilIntervalReflection a f) := by
  apply suzukiApertureZeroExtendL2_injective
  rw [suzukiApertureZeroExtendL2_intervalReflection]
  have hneg :
      suzukiApertureZeroExtendL2
          (-suzukiAperturePosition a (suzukiWeilIntervalReflection a f)) =
        -suzukiApertureZeroExtendL2
          (suzukiAperturePosition a (suzukiWeilIntervalReflection a f)) := by
    simpa only [neg_one_smul] using
      suzukiApertureZeroExtendL2_smul (-1 : ℂ)
        (suzukiAperturePosition a (suzukiWeilIntervalReflection a f))
  rw [hneg]
  apply Lp.ext
  have hposNeg := (suzukiApertureZeroExtendL2_position_ae a f).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  have hrefEq :
      suzukiApertureZeroExtendL2 (suzukiWeilIntervalReflection a f) =
        l2Reflection (suzukiApertureZeroExtendL2 f) :=
    suzukiApertureZeroExtendL2_intervalReflection a f
  have hrefAe :
      (suzukiApertureZeroExtendL2 (suzukiWeilIntervalReflection a f) : ℝ → ℂ) =ᵐ[volume]
        (l2Reflection (suzukiApertureZeroExtendL2 f) : ℝ → ℂ) := by
    rw [hrefEq]
  filter_upwards [l2Reflection_ae
      (suzukiApertureZeroExtendL2 (suzukiAperturePosition a f)),
    hposNeg,
    Lp.coeFn_neg (suzukiApertureZeroExtendL2
      (suzukiAperturePosition a (suzukiWeilIntervalReflection a f))),
    suzukiApertureZeroExtendL2_position_ae a (suzukiWeilIntervalReflection a f),
    hrefAe,
    l2Reflection_ae (suzukiApertureZeroExtendL2 f)] with
      x hleft hpos hright hposRight href hrefPoint
  rw [hleft, hright]
  change (suzukiApertureZeroExtendL2
      (suzukiAperturePosition a f) : ℝ → ℂ) (-x) =
    -(suzukiApertureZeroExtendL2
      (suzukiAperturePosition a (suzukiWeilIntervalReflection a f)) : ℝ → ℂ) x
  rw [hposRight, href, hrefPoint]
  simp only [Function.comp_apply] at hpos
  rw [hpos]
  push_cast
  ring

end RHTower
end
