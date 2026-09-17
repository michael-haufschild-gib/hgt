import GaloisForLFunctions.HTGeometry.LiteralSourceHorizonLogCubicJet

/-! Third derivative of the literal source horizon height. -/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

def horizonLogHeightThirdCore (z : ℝ) : ℝ :=
  -(3 / 8 : ℝ) * (1 - z) ^ (-(5 / 2 : ℝ))

theorem literalSourceHorizonHeightSecond_hasDerivAt (z : ℝ) (hz : z < 1) :
    HasDerivAt literalSourceHorizonHeightSecond (horizonLogHeightThirdCore z) z := by
  have hpos : 0 < 1 - z := by linarith
  have hins : HasDerivAt (fun x : ℝ => 1 - x) (-1) z := by
    change HasDerivAt ((fun _ : ℝ => 1) - id) (-1) z
    simpa using (hasDerivAt_const z (1 : ℝ)).sub (hasDerivAt_id z)
  have hp := Real.hasDerivAt_rpow_const (x := 1 - z) (p := (-3 / 2 : ℝ)) (Or.inl hpos.ne')
  have ht := (hp.comp z hins).const_mul (-(1 / 4 : ℝ))
  have he : literalSourceHorizonHeightSecond = fun x : ℝ => -(1 / 4 : ℝ) *
      ((fun y : ℝ => y ^ (-3 / 2 : ℝ)) ∘ (fun y : ℝ => 1 - y)) x := by
    funext x
    simp only [literalSourceHorizonHeightSecond, Function.comp_apply]
    congr 2
    ring
  rw [he]
  apply ht.congr_deriv
  dsimp [horizonLogHeightThirdCore]
  ring

end
end GaloisForLFunctions.HTGeometry
