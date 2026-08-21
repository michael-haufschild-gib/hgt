import GaloisForLFunctions.HTGeometry.SeibergWitten.Connections

/-!
# Section-level Abelian gauge transformations and flows

Gauge transformations are pointwise maps to `U(1) = Circle`; they act on arbitrary complex spinor
sections by pointwise scalar multiplication.  `U1GaugeFlow` records the exact one-parameter group
law.  Smoothness of the gauge transformation itself and its induced action on a connection are
kept separate, because the current mathematical interface does not yet package smooth maps into
the manifold `Circle` with the required bundle gauge-action theorem.
-/

namespace GaloisForLFunctions.HTGeometry.SeibergWitten

/-- Abelian gauge transformations over a base space. -/
abbrev U1GaugeTransformation (M : Type*) := M → Circle

/-- Pointwise Abelian action on a complex spinor section. -/
def U1GaugeTransformation.actOnSpinor
    {M : Type u} {SPlus : M → Type v}
    [∀ x, AddCommGroup (SPlus x)] [∀ x, Module ℂ (SPlus x)]
    (gauge : U1GaugeTransformation M) (sigma : ∀ x, SPlus x) : ∀ x, SPlus x :=
  fun x => (gauge x : ℂ) • sigma x

/-- A one-parameter Abelian gauge flow on a base space. -/
structure U1GaugeFlow (M : Type*) where
  phase : ℝ → U1GaugeTransformation M
  phase_zero : phase 0 = 1
  phase_add : ∀ s t, phase (s + t) = phase s * phase t

/-- Time-`t` pointwise action of an Abelian gauge flow on a spinor section. -/
def U1GaugeFlow.actOnSpinor
    {M : Type u} {SPlus : M → Type v}
    [∀ x, AddCommGroup (SPlus x)] [∀ x, Module ℂ (SPlus x)]
    (flow : U1GaugeFlow M) (t : ℝ) (sigma : ∀ x, SPlus x) : ∀ x, SPlus x :=
  (flow.phase t).actOnSpinor sigma

/-- Time zero of every Abelian gauge flow acts identically on every spinor section. -/
theorem U1GaugeFlow.actOnSpinor_zero
    {M : Type u} {SPlus : M → Type v}
    [∀ x, AddCommGroup (SPlus x)] [∀ x, Module ℂ (SPlus x)]
    (flow : U1GaugeFlow M) (sigma : ∀ x, SPlus x) :
    flow.actOnSpinor 0 sigma = sigma := by
  funext x
  have hzero := congrFun flow.phase_zero x
  change ((flow.phase 0 x : Circle) : ℂ) • sigma x = sigma x
  rw [hzero]
  exact one_smul ℂ (sigma x)

/-- Every gauge-flow time acts through the corresponding exact `U(1)` phase. -/
theorem U1GaugeFlow.actOnSpinor_apply
    {M : Type u} {SPlus : M → Type v}
    [∀ x, AddCommGroup (SPlus x)] [∀ x, Module ℂ (SPlus x)]
    (flow : U1GaugeFlow M) (t : ℝ) (sigma : ∀ x, SPlus x) (x : M) :
    flow.actOnSpinor t sigma x = (flow.phase t x : ℂ) • sigma x :=
  rfl

end GaloisForLFunctions.HTGeometry.SeibergWitten
