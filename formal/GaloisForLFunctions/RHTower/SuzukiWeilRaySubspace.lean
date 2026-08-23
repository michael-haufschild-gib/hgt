import GaloisForLFunctions.RHTower.SuzukiDeBrangesSubspace
import GaloisForLFunctions.RHTower.SuzukiModelWeilIsomorphism

noncomputable section

/-!
# `H_W(t)` inside the Weil space

The de Branges subspace `E 𝖥(V(t))` corresponds under the map of Theorem 1.1 to a closed subspace of
the Weil Hilbert space, and the correspondence is isometric up to the constant `π` that separates the
two normalisations — the same constant as for the whole space.
-/

open MeasureTheory Set Complex Filter Topology

namespace RHTower

section

variable [hRH : Fact RiemannHypothesis]

/-- `𝖥(V(t))` as a subspace of the model space. -/
def suzukiModelRaySub (t : ℝ) :
    Submodule ℂ ↥(suzukiModelSpace : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))) :=
  Submodule.comap (suzukiModelSpace : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))).subtype
    (suzukiModelRay t)

/-- `H_W(t)`: the image of `𝖥(V(t))` in the Weil space under the map of Theorem 1.1. -/
def suzukiWeilRay (t : ℝ) : Submodule ℂ SuzukiHW :=
  Submodule.map (suzukiModelWeilEquiv : _ ≃ₗ[ℂ] SuzukiHW).toLinearMap (suzukiModelRaySub t)

/-- **Suzuki, Theorem 5.3, second half.**  The map of Theorem 1.1 carries `𝖥(V(t))` onto `H_W(t)`
isometrically up to the constant `π`. -/
theorem norm_sq_suzukiWeilRay {t : ℝ} (G : ↥(suzukiModelRaySub t)) :
    ‖((G : ↥(suzukiModelSpace : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)))) :
        Lp ℂ 2 (volume : Measure ℝ))‖ ^ 2
      = Real.pi * ‖suzukiModelWeilEquiv (G : _)‖ ^ 2 :=
  norm_sq_suzukiModelWeilEquiv _

theorem suzukiWeilRay_eq_map (t : ℝ) :
    suzukiWeilRay t
      = Submodule.map (suzukiModelWeilEquiv : _ ≃ₗ[ℂ] SuzukiHW).toLinearMap
        (suzukiModelRaySub t) := rfl

omit hRH in
theorem mem_suzukiModelRaySub_iff (t : ℝ)
    (G : ↥(suzukiModelSpace : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)))) :
    G ∈ suzukiModelRaySub t ↔ (G : Lp ℂ 2 (volume : Measure ℝ)) ∈ suzukiModelRay t := Iff.rfl

end

end RHTower
