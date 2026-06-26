/-
# The quartic defect vanishes at the cusp `i∞`

`F = θ₃⁴ − θ₂⁴ − θ₄⁴ → 1 − 0 − 1 = 0` as `im τ → ∞`, from the nullwert cusp limits
(`tendsto_thetaThree/Four_atImInfty → 1`, `tendsto_thetaTwo_atImInfty → 0`).

With the weight-2 transformation laws `quarticDefect_add_one`/`_S` (`QuarticDefect.lean`) transporting
this vanishing to the cusps `0` and `1`, `F` is a holomorphic weight-2 `Γ(2)` **cusp form**. The
Jacobi quartic identity `F ≡ 0` (⟹ `λ` omits `1`, hence `λ : ℍ → ℂ∖{0,1}`) is now reduced to the
single absent input `dim S₂(Γ(2)) = 0` (genus-0 compactified modular curve `X(Γ(2))` / the `Γ(2)`
valence formula — mathlib has only the level-one version).

Consumes `QuarticDefect` + `CuspLimits`. Mathlib only otherwise.
-/
import GaloisForLFunctions.Bottcher.QuarticDefect
import GaloisForLFunctions.Bottcher.CuspLimits
open Complex Filter Topology
open scoped Real
namespace Bottcher

theorem tendsto_quarticDefect_atImInfty :
    Tendsto quarticDefect (comap Complex.im atTop) (𝓝 0) := by
  have h := ((tendsto_thetaThree_atImInfty.pow 4).sub
    (tendsto_thetaTwo_atImInfty.pow 4)).sub (tendsto_thetaFour_atImInfty.pow 4)
  simpa [quarticDefect] using h

end Bottcher
