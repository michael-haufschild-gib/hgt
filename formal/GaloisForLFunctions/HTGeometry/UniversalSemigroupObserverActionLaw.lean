import GaloisForLFunctions.HTGeometry.UniversalSpectralSemigroupWallCrossingLaw

/-!
# Universal observer-action law for contractive semigroups

For open or dissipative evolution, the scalar observable is no longer a
unitary phase character.  Nevertheless the same dimensionless object
controls observation: clock length times complex spectral mode.

The normalized forward-time average is exactly the universal exponential
window kernel evaluated at that action.  Hence convergence of the observed
mode is equivalent to convergence of its action kernel for every clock and
every approach filter.  Finite action gives the kernel at that action;
unbounded contractive action is erased.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Complex dimensionless action seen by a forward-time observer. -/
def semigroupObserverAction
    {α : Type*} (clock : α → ℝ)
    (mode : α → ℂ) (x : α) : ℂ :=
  (clock x : ℂ) * mode x

/-- **Exact semigroup observer-action equivalence.** Provided the
observation window is eventually nonzero, a forward-mode average converges
to a value if and only if the universal window kernel of its dimensionless
action converges to that value. -/
theorem forwardModeAverage_tendsto_iff_actionKernel
    {α : Type*} {l : Filter α}
    (clock : α → ℝ) (mode : α → ℂ)
    (hclock : ∀ᶠ x in l, clock x ≠ 0)
    (c : ℂ) :
    Tendsto
        (fun x => forwardModeAverage (clock x) (mode x))
        l (𝓝 c) ↔
      Tendsto
        (fun x =>
          forwardWindowKernel
            (semigroupObserverAction clock mode x))
        l (𝓝 c) := by
  apply tendsto_congr'
  filter_upwards [hclock] with x hx
  rw [forwardModeAverage_eq_kernel _ _ hx]
  rfl

/-- Convergent asymptotic regimes of a contractive semigroup action. -/
inductive SemigroupObserverActionRegime where
  | finite (z : ℂ)
  | dephased
  deriving DecidableEq

/-- Universal forward-window coefficient of one semigroup action regime. -/
def semigroupObserverActionRegimeCoefficient :
    SemigroupObserverActionRegime → ℂ
  | .finite z => forwardWindowKernel z
  | .dephased => 0

/-- A complex action realizes a finite limit, or escapes in norm through
the closed contractive half-plane. -/
def HasSemigroupObserverActionRegime
    {α : Type*} (l : Filter α) (action : α → ℂ) :
    SemigroupObserverActionRegime → Prop
  | .finite z => Tendsto action l (𝓝 z)
  | .dephased =>
      Tendsto (fun x => ‖action x‖) l atTop ∧
        ∀ᶠ x in l, (action x).re ≤ 0

/-- Every finite or dephased contractive action has its universal
forward-window limit. -/
theorem tendsto_forwardWindowKernel_of_semigroupObserverActionRegime
    {α : Type*} {l : Filter α}
    {action : α → ℂ}
    {regime : SemigroupObserverActionRegime}
    (hregime :
      HasSemigroupObserverActionRegime l action regime) :
    Tendsto
      (fun x => forwardWindowKernel (action x))
      l
      (𝓝
        (semigroupObserverActionRegimeCoefficient regime)) := by
  cases regime with
  | finite z =>
      exact
        continuous_forwardWindowKernel.continuousAt.tendsto.comp
          hregime
  | dephased =>
      exact
        tendsto_forwardWindowKernel_zero_of_norm_atTop
          hregime.1 hregime.2

/-- **Arbitrary-clock contractive observer-action law.** A finite complex
action survives through the exponential window kernel; an unbounded
contractive action is completely averaged away.  No analytic parameter or
inverse-power clock is required. -/
theorem forwardModeAverage_tendsto_of_semigroupObserverActionRegime
    {α : Type*} {l : Filter α}
    (clock : α → ℝ) (mode : α → ℂ)
    (hclock : ∀ᶠ x in l, clock x ≠ 0)
    (regime : SemigroupObserverActionRegime)
    (hregime :
      HasSemigroupObserverActionRegime l
        (semigroupObserverAction clock mode) regime) :
    Tendsto
      (fun x => forwardModeAverage (clock x) (mode x))
      l
      (𝓝
        (semigroupObserverActionRegimeCoefficient regime)) := by
  rw [forwardModeAverage_tendsto_iff_actionKernel
    clock mode hclock]
  exact
    tendsto_forwardWindowKernel_of_semigroupObserverActionRegime
      hregime

end

end GaloisForLFunctions.HTGeometry
