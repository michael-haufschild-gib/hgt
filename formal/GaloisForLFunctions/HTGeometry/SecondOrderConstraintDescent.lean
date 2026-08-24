import GaloisForLFunctions.HTGeometry.ClockDescentAnomaly

/-!
# Second-order coherence of constraint descent

Strict intertwining is stronger than needed to transport a square-zero constraint.  For a source
law `d`, observation `π`, and observed law `D`, let

`A = D π - π d`

be the first-order descent anomaly.  Its covariant second-order defect is

`D A + A d = D² π - π d²`.

Consequently a square-zero source and a surjective observation force `D² = 0` as soon as the
first-order anomaly is coherent.  The anomaly itself need not vanish.  This is the linear
two-cell form of constraint descent: the RH-bearing datum may live in coherence of a comparison,
not in equality of its two edges.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K V O : Type*}
  [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup O] [Module K O]

/-- Covariant failure of the first-order descent anomaly to be a coherent two-cell. -/
def secondOrderConstraintDescentDefect
    (source : Module.End K V) (observe : V →ₗ[K] O) (shadow : Module.End K O) :
    V →ₗ[K] O :=
  shadow.comp (clockDescentAnomaly source observe shadow) +
    (clockDescentAnomaly source observe shadow).comp source

/-- A possibly nonzero first-order anomaly is admissible when its covariant boundary vanishes. -/
def SecondOrderConstraintDescentCoherent
    (source : Module.End K V) (observe : V →ₗ[K] O) (shadow : Module.End K O) : Prop :=
  secondOrderConstraintDescentDefect source observe shadow = 0

/-- Two-cell defect is exactly mismatch between observed target curvature and source curvature. -/
theorem secondOrderConstraintDescentDefect_eq
    (source : Module.End K V) (observe : V →ₗ[K] O) (shadow : Module.End K O) :
    secondOrderConstraintDescentDefect source observe shadow =
      clockDescentAnomaly (source.comp source) observe (shadow.comp shadow) := by
  exact (clockDescentAnomaly_comp_constraint source source observe shadow shadow).symm

/-- For a square-zero source, every second-order defect is target curvature seen by observation. -/
theorem secondOrderConstraintDescentDefect_eq_targetCurvature_comp
    (source : Module.End K V) (observe : V →ₗ[K] O) (shadow : Module.End K O)
    (hsource : source.comp source = 0) :
    secondOrderConstraintDescentDefect source observe shadow =
      (shadow.comp shadow).comp observe := by
  rw [secondOrderConstraintDescentDefect_eq, hsource]
  ext v
  simp [clockDescentAnomaly, LinearMap.comp_apply]

/-- Surjective two-cell descent transports the master equation without requiring strict
first-order intertwining. -/
theorem secondOrderConstraintDescentCoherent_iff_target_sq_zero
    (source : Module.End K V) (observe : V →ₗ[K] O) (shadow : Module.End K O)
    (hsource : source.comp source = 0)
    (hsurjective : Function.Surjective observe) :
    SecondOrderConstraintDescentCoherent source observe shadow ↔
      shadow.comp shadow = 0 := by
  rw [SecondOrderConstraintDescentCoherent,
    secondOrderConstraintDescentDefect_eq_targetCurvature_comp source observe shadow hsource]
  constructor
  · intro h
    apply LinearMap.ext
    intro o
    obtain ⟨v, rfl⟩ := hsurjective o
    exact LinearMap.congr_fun h v
  · intro h
    rw [h]
    simp

end

end GaloisForLFunctions.HTGeometry
