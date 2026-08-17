import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaCompletedXiDivisorShorting
import GaloisForLFunctions.RHTower.SourceHorizontalWoldPrimeClockCubic
import GaloisForLFunctions.RHTower.HedenmalmThetaXiHardySymmetricSquareWeld

/-!
# Wold-cubic regularization of the completed Gamma--Julia orientation orbit

P-G207 transports one coefficient- and multiplicity-faithful conormal coordinate to every Xi
divisor copy, but its rank-one environment block has zero Schur short.  Keeping the complete
FE--Schwarz--Krein orientation orbit changes that conclusion.  The four coordinates

`c, star c, -star c, -c`

share one environment pivot.  Their cross terms cancel, so the environment becomes an orthogonal
summand and the Schur short is the full positive corner `4 * normSq c`.  Thus the common pivot can
no longer erase the landed coordinate.

The source-horizontal Wold residual supplies the independent cubic normalization.  On a
strict-right copy with centered rate `2a`, its limiting response is `-(2/3)(2a)^3`, while the
Route-P conormal diagonal is `1/(4a^3)`.  Their product is exactly `-4/3`; after the four-orientation
orbit the positive quantum is `16/3 * normSq c`, independent of the zero's distance from the
critical line.  The correspondingly normalized primitive Euler source budget is strictly smaller
for every nonzero coefficient.

These are unconditional source and divisor identities.  The last theorem records the hostile
boundary: asserting that the regularized orbit quantum is bounded by that smaller source budget
on every retained copy is equivalent to RH.  Hence the new orbit removes environment erasure and
the inverse-cubic blow-up, but an actual completed-source order transport is still the bearing
producer; it is not smuggled in here.
-/

open Complex Matrix Filter Topology
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- Four FE--Schwarz--Krein orientations of one completed Julia coordinate, sharing rather than
duplicating the environment direction. -/
def routePJuliaSharedOrientationOrbitBlock
    (c : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  routePJuliaEnvironmentHermitianBlock c +
    routePJuliaEnvironmentHermitianBlock (star c) +
    routePJuliaEnvironmentHermitianBlock (-star c) +
    routePJuliaEnvironmentHermitianBlock (-c)

/-- Orbit symmetrization makes the physical corner and environment pivot orthogonal. -/
theorem routePJuliaSharedOrientationOrbitBlock_eq_diagonal (c : ℂ) :
    routePJuliaSharedOrientationOrbitBlock c =
      !![((4 : ℝ) * Complex.normSq c : ℂ), 0; 0, 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [routePJuliaSharedOrientationOrbitBlock,
      routePJuliaEnvironmentHermitianBlock,
      routePJuliaEnvironmentBilinearBlock,
      Complex.normSq_eq_conj_mul_self] <;> ring_nf

/-- Positivity survives the complete orientation orbit. -/
theorem routePJuliaSharedOrientationOrbitBlock_posSemidef (c : ℂ) :
    (routePJuliaSharedOrientationOrbitBlock c).PosSemidef := by
  exact (((routePJuliaEnvironmentHermitianBlock_posSemidef c).add
      (routePJuliaEnvironmentHermitianBlock_posSemidef (star c))).add
      (routePJuliaEnvironmentHermitianBlock_posSemidef (-star c))).add
      (routePJuliaEnvironmentHermitianBlock_posSemidef (-c))

/-- Unlike one rank-one block, the shared-orbit block retains its entire positive corner after
shorting through the environment pivot. -/
theorem routePJuliaSharedOrientationOrbitBlock_short (c : ℂ) :
    let B := routePJuliaSharedOrientationOrbitBlock c
    B 0 0 - B 0 1 * (B 1 1)⁻¹ * B 1 0 =
      (((4 : ℝ) * Complex.normSq c : ℝ) : ℂ) := by
  rw [routePJuliaSharedOrientationOrbitBlock_eq_diagonal]
  simp

/-- Actual P-G207 copy coordinate placed in its complete shared orientation orbit.  Prime-source
parameters, support, radial coordinate, and analytic-multiplicity copy remain explicit. -/
def routePPrimitiveGammaJuliaXiCopySharedOrientationBlock
    (x u : ℝ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) : Matrix (Fin 2) (Fin 2) ℂ :=
  routePJuliaSharedOrientationOrbitBlock
    (routePPrimitiveGammaJuliaXiCopyForwardCoordinate x u rho r j)

/-- P-G207's copywise descent inherits the pivot-resistant short exactly. -/
theorem routePPrimitiveGammaJuliaXiCopySharedOrientationBlock_short
    (x u : ℝ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) :
    let B := routePPrimitiveGammaJuliaXiCopySharedOrientationBlock x u rho r j
    B 0 0 - B 0 1 * (B 1 1)⁻¹ * B 1 0 =
      (((4 : ℝ) * Complex.normSq
        (routePPrimitiveGammaJuliaXiCopyForwardCoordinate x u rho r j) : ℝ) : ℂ) := by
  exact routePJuliaSharedOrientationOrbitBlock_short _

/-- The shared-orbit short is genuinely nonzero whenever the source coupling and radial
coordinate are nonzero; environment shorting no longer hides P-G207's nonannihilation. -/
theorem routePPrimitiveGammaJuliaXiCopySharedOrientationBlock_short_ne_zero
    {x u r : ℝ} (rho : XiDivisorSupport)
    (j : Fin (xiSupportMultiplicity rho))
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0)
    (hr : r ≠ 0) :
    let B := routePPrimitiveGammaJuliaXiCopySharedOrientationBlock x u rho r j
    B 0 0 - B 0 1 * (B 1 1)⁻¹ * B 1 0 ≠ 0 := by
  dsimp only
  rw [routePPrimitiveGammaJuliaXiCopySharedOrientationBlock_short]
  exact Complex.ofReal_ne_zero.mpr (mul_ne_zero (by norm_num)
    ((Complex.normSq_pos.mpr
      (routePPrimitiveGammaJuliaXiCopyForwardCoordinate_ne_zero
        rho j hkappa hr)).ne'))

/-- One strict-right conormal diagonal multiplied by the negative finite Wold cubic response. -/
def sourceZeroHorizontalWoldRegularizedRoutePConormalResponse
    (q : XiRightZeroCopy) (N : ℕ) : ℝ :=
  -sourceZeroHorizontalWoldPrimeClockCubicResponse q.1 N *
    (1 / (4 * (xiRightCenteredZero q).re ^ 3))

/-- Exact cancellation of the horizontal cubic scale: every retained copy has limiting quantum
`4/3`, independently of its distance from the critical line and of its ordinate. -/
theorem tendsto_sourceZeroHorizontalWoldRegularizedRoutePConormalResponse
    (q : XiRightZeroCopy) :
    Tendsto (sourceZeroHorizontalWoldRegularizedRoutePConormalResponse q)
      atTop (nhds (4 / 3 : ℝ)) := by
  have h := (tendsto_sourceZeroHorizontalWoldPrimeClockCubicResponse q.1).neg.mul_const
    (1 / (4 * (xiRightCenteredZero q).re ^ 3))
  convert h using 1
  · rfl
  · rw [HedenmalmThetaSource.primeDepthBVWoldXiCenteredRate_right_eq_two_mul_re]
    have ha : (xiRightCenteredZero q).re ≠ 0 :=
      (xiRightCenteredZero_re_pos q).ne'
    field_simp [ha]
    ring_nf

/-- Finite Wold-cubic response of the pivot-resistant four-orientation corner. -/
def sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) : ℝ :=
  4 * Complex.normSq c *
    sourceZeroHorizontalWoldRegularizedRoutePConormalResponse q N

/-- The completed Julia orbit has a location-independent positive quantum. -/
theorem tendsto_sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse
    (c : ℂ) (q : XiRightZeroCopy) :
    Tendsto (sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse c q)
      atTop (nhds ((16 / 3 : ℝ) * Complex.normSq c)) := by
  have h :=
    (tendsto_sourceZeroHorizontalWoldRegularizedRoutePConormalResponse q).const_mul
      (4 * Complex.normSq c)
  convert h using 1
  · rfl
  · ring_nf

/-- Primitive Euler budget in the same four-orientation Wold normalization.  The factor is the
universal Wold coefficient `2/3` times four retained orientations. -/
def sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget (c : ℂ) : ℝ :=
  (8 / 3 : ℝ) * Complex.normSq c *
    routePPrimitiveBaseCauchyCubicTraceBudget

/-- The completed primitive source budget is strictly below one nonzero regularized orbit
quantum. -/
theorem sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget_lt_quantum
    {c : ℂ} (hc : c ≠ 0) :
    sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c <
      (16 / 3 : ℝ) * Complex.normSq c := by
  have hnorm : 0 < Complex.normSq c := Complex.normSq_pos.mpr hc
  have hbudget := routePPrimitiveBaseCauchyCubicTraceBudget_lt_quantum
  rw [sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget]
  nlinarith

/-- Strong finite-stage form: on every retained copy and for every nonzero source coefficient,
the regularized physical orbit eventually overspends the complete normalized primitive budget. -/
theorem eventually_sourceBudget_lt_sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse
    {c : ℂ} (hc : c ≠ 0) (q : XiRightZeroCopy) :
    ∀ᶠ N : ℕ in atTop,
      sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c <
        sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse c q N := by
  exact
    (tendsto_sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse c q).eventually_const_lt
      (sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget_lt_quantum hc)

/-- Exact remaining completed-source order statement.  It asks the smaller source budget to
dominate the pivot-resistant orbit quantum on every retained copy. -/
def WoldRegularizedJuliaOrbitCompletedSourceOrderLaw : Prop :=
  ∀ (_q : XiRightZeroCopy) (c : ℂ), c ≠ 0 →
    (16 / 3 : ℝ) * Complex.normSq c ≤
      sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c

/-- Hostile audit: after environment erasure and inverse-cubic singularity are both removed, the
remaining completed-source order transport is precisely RH-strength. -/
theorem woldRegularizedJuliaOrbitCompletedSourceOrderLaw_iff_riemannHypothesis :
    WoldRegularizedJuliaOrbitCompletedSourceOrderLaw ↔ RiemannHypothesis := by
  constructor
  · intro hlaw
    by_contra hRH
    obtain ⟨q⟩ := nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH
    have hle := hlaw q 1 one_ne_zero
    have hlt := sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget_lt_quantum
      (c := (1 : ℂ)) one_ne_zero
    linarith
  · intro hRH q
    haveI : IsEmpty XiRightZeroCopy := isEmpty_xiRightZeroCopy_of_riemannHypothesis hRH
    exact isEmptyElim q

end

end RHTower
