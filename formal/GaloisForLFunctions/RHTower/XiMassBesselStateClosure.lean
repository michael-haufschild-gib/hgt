import GaloisForLFunctions.RHTower.XiMassBesselHeightSystem

/-!
# Closure of the Bessel height states

A *Bessel state* is a function of the height of the form

`S(w) = A(w)·K₀(aZ(w)) + B(w)·K₁(aZ(w))`,  `Z(w)² = τ² + w²`.

The height system closes the states under differentiation: the derivative of a state is the state
with coefficient pair

`(A′ − a(w/Z)·B ,  B′ − a(w/Z)·A − (w/Z²)·B)`.

The mass profile itself is the state `(0, 2aτ/Z)`, so every iterated height derivative of the
profile — in particular every application of a caustic-null jet operator `4a⁴ − ∂_w²` — is again a
state, with coefficients obtained from a two-term recursion in rational functions of `w` and `Z`.
-/

open Complex

namespace RHTower

noncomputable section

/-- The state attached to a coefficient pair. -/
def xiMassBesselState (a : ℝ) (τ : ℂ) (Af Bf : ℂ → ℂ) (w : ℂ) : ℂ :=
  Af w * xiMassHeightK0 a τ w + Bf w * xiMassHeightK1 a τ w

/-- **The height states are closed under differentiation.**  The coefficient pair transforms by the
first-order system of the Bessel pair. -/
theorem hasDerivAt_xiMassBesselState {a : ℝ} {τ w : ℂ} {A' B' : ℂ} {Af Bf : ℂ → ℂ}
    (ha : 0 < a) (hw : 0 < (τ ^ 2 + w ^ 2).re)
    (hA : HasDerivAt Af A' w) (hB : HasDerivAt Bf B' w) :
    HasDerivAt (xiMassBesselState a τ Af Bf)
      ((A' - (a : ℂ) * (w / xiMassHeightRadius τ w) * Bf w) * xiMassHeightK0 a τ w
        + (B' - (a : ℂ) * (w / xiMassHeightRadius τ w) * Af w
            - w / xiMassHeightRadius τ w ^ 2 * Bf w) * xiMassHeightK1 a τ w) w := by
  have h0 := hA.mul (hasDerivAt_xiMassHeightK0 ha hw)
  have h1 := hB.mul (hasDerivAt_xiMassHeightK1 ha hw)
  have hsum := h0.add h1
  have hgoal : HasDerivAt (xiMassBesselState a τ Af Bf)
      (A' * xiMassHeightK0 a τ w
          + Af w * (-((a : ℂ) * (w / xiMassHeightRadius τ w)) * xiMassHeightK1 a τ w)
        + (B' * xiMassHeightK1 a τ w
          + Bf w * (-((a : ℂ) * (w / xiMassHeightRadius τ w)) * xiMassHeightK0 a τ w
            - w / xiMassHeightRadius τ w ^ 2 * xiMassHeightK1 a τ w))) w := hsum
  convert hgoal using 1
  ring

/-- The mass profile is the state with coefficient pair `(0, 2aτ/Z)`. -/
theorem xiMassBesselHeightSide_eq_state (a : ℝ) (τ : ℂ) :
    xiMassBesselHeightSide a τ
      = xiMassBesselState a τ (fun _ => 0)
          (fun v => 2 * (a : ℂ) * τ / xiMassHeightRadius τ v) := by
  funext w
  rw [xiMassBesselHeightSide, xiMassBesselState, xiMassHeightK1, xiMassHeightRadius]
  ring

end

end RHTower
