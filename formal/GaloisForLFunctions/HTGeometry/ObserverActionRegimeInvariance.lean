import GaloisForLFunctions.HTGeometry.UniversalObserverActionLaw
import GaloisForLFunctions.HTGeometry.UniversalSemigroupObserverActionLaw

/-!
# Observer-action regimes: attained, unique, and one law

Both observer-action laws are stated for an action family that *realizes* a regime — a finite
limit or a dephasing escape — and neither hypothesis was ever produced.  Each is attained by an
explicit family, and each is an invariant: along a nontrivial filter an action cannot realize two
regimes, because a convergent family has bounded magnitude and a dephasing one does not.

The two interfaces are also not independent.  A real character action becomes a contractive
semigroup action after multiplication by `i`: the resulting action has zero real part, so it lies
in the closed contractive half-plane, and its magnitude is the magnitude of the original.  The
character law is therefore the purely imaginary case of the semigroup law at the level of regimes.
-/

open Filter Topology Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The character regime -/

/-- A constant action realizes the corresponding finite regime. -/
theorem hasObserverActionRegime_const {α : Type*} (l : Filter α) (a : ℝ) :
    HasObserverActionRegime l (fun _ => a) (.finite a) :=
  tendsto_const_nhds

/-- The identity action dephases along `atTop`. -/
theorem hasObserverActionRegime_id_dephased :
    HasObserverActionRegime (atTop : Filter ℝ) id .dephased := by
  change Tendsto (fun x : ℝ => |x|) atTop atTop
  exact tendsto_abs_atTop_atTop

/-- Eventual equality preserves the realized regime. -/
theorem hasObserverActionRegime_congr {α : Type*} {l : Filter α}
    {action action' : α → ℝ} {r : ObserverActionRegime}
    (h : HasObserverActionRegime l action r) (heq : action =ᶠ[l] action') :
    HasObserverActionRegime l action' r := by
  cases r with
  | finite a => exact h.congr' heq
  | dephased => exact h.congr' (heq.mono fun x hx => by rw [hx])

/-- **The character regime is an invariant.**  Along a nontrivial filter an action realizes at
most one observer-action regime. -/
theorem HasObserverActionRegime.unique {α : Type*} {l : Filter α} [l.NeBot]
    {action : α → ℝ} {r r' : ObserverActionRegime}
    (h : HasObserverActionRegime l action r) (h' : HasObserverActionRegime l action r') :
    r = r' := by
  cases r with
  | finite a =>
      cases r' with
      | finite a' => rw [tendsto_nhds_unique h h']
      | dephased => exact absurd h.abs (not_tendsto_nhds_of_tendsto_atTop h' |a|)
  | dephased =>
      cases r' with
      | finite a' => exact absurd h'.abs (not_tendsto_nhds_of_tendsto_atTop h |a'|)
      | dephased => rfl

/-! ## The contractive semigroup regime -/

/-- A constant contractive action realizes the corresponding finite regime. -/
theorem hasSemigroupObserverActionRegime_const {α : Type*} (l : Filter α) (z : ℂ) :
    HasSemigroupObserverActionRegime l (fun _ => z) (.finite z) :=
  tendsto_const_nhds

/-- **The contractive regime is an invariant.** -/
theorem HasSemigroupObserverActionRegime.unique {α : Type*} {l : Filter α} [l.NeBot]
    {action : α → ℂ} {r r' : SemigroupObserverActionRegime}
    (h : HasSemigroupObserverActionRegime l action r)
    (h' : HasSemigroupObserverActionRegime l action r') :
    r = r' := by
  cases r with
  | finite z =>
      cases r' with
      | finite z' => rw [tendsto_nhds_unique h h']
      | dephased => exact absurd h.norm (not_tendsto_nhds_of_tendsto_atTop h'.1 ‖z‖)
  | dephased =>
      cases r' with
      | finite z' => exact absurd h'.norm (not_tendsto_nhds_of_tendsto_atTop h.1 ‖z'‖)
      | dephased => rfl

/-! ## The character law is the purely imaginary semigroup law -/

/-- Multiplying a real action by `i` produces a contractive action with the same magnitude. -/
theorem hasSemigroupObserverActionRegime_mul_I_finite {α : Type*} {l : Filter α}
    {action : α → ℝ} {a : ℝ}
    (h : HasObserverActionRegime l action (.finite a)) :
    HasSemigroupObserverActionRegime l (fun x => I * (action x : ℂ)) (.finite (I * a)) := by
  change Tendsto (fun x => I * ((action x : ℝ) : ℂ)) l (𝓝 (I * (a : ℂ)))
  exact tendsto_const_nhds.mul (Complex.continuous_ofReal.tendsto a |>.comp h)

/-- The dephased character regime is the dephased contractive regime of the imaginary action. -/
theorem hasSemigroupObserverActionRegime_mul_I_dephased {α : Type*} {l : Filter α}
    {action : α → ℝ}
    (h : HasObserverActionRegime l action .dephased) :
    HasSemigroupObserverActionRegime l (fun x => I * (action x : ℂ)) .dephased := by
  refine ⟨?_, Filter.Eventually.of_forall fun x => ?_⟩
  · have hnorm : ∀ x, ‖I * ((action x : ℝ) : ℂ)‖ = |action x| := by
      intro x
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (h.congr fun x => (hnorm x).symm)
  · simp

end

end GaloisForLFunctions.HTGeometry
