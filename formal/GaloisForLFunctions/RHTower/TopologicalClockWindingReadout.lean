import GaloisForLFunctions.RHTower.PrimeAFCircleOperatorKOne
import GaloisForLFunctions.RHTower.WindingArgumentPrinciple

/-!
# Topological clock winding readout

The forward/backward readout of arXiv:2608.27650 squares a phase loop: common dynamical phase
cancels, geometric phase doubles, and the measured winding is therefore even.  If a second band is
scanned in the opposite momentum direction, its winding is subtracted.  This file realizes that
calculus on the corpus's literal scalar-circle `K₁` model.

The results are topological and contain no Rice--Mele or adiabatic assumption.  They apply to every
bundled nonvanishing complex loop, hence to every scalar determinant or Wilson loop that lands in
this `K₁` layer.
-/

open Complex

noncomputable section

namespace PrimeQuasiLocalCharge

/-- Reverse traversal of a scalar circle loop. -/
def scalarCircleLoopReverse (gamma : ScalarCircleLoop) : ScalarCircleLoop where
  toFun := fun t => gamma (2 * Real.pi - t)
  isLoop := by
    refine ⟨gamma.isLoop.continuous.comp (continuous_const.sub continuous_id),
      fun t => gamma.isLoop.nonzero (2 * Real.pi - t), ?_⟩
    simpa using gamma.isLoop.closed.symm

/-- Reversing the traversal reverses integer winding. -/
theorem scalarCircleLoopReverse_winding (gamma : ScalarCircleLoop) :
    scalarCircleLoopWinding (scalarCircleLoopReverse gamma) =
      -scalarCircleLoopWinding gamma := by
  obtain ⟨hLogContinuous, hLogExp⟩ :=
    RHTower.contLog_spec gamma.isLoop.continuous gamma.isLoop.nonzero
  let reverseLog : ℝ → ℂ := fun t => RHTower.contLog gamma.toFun (2 * Real.pi - t)
  have hReverseLogContinuous : Continuous reverseLog :=
    hLogContinuous.comp (continuous_const.sub continuous_id)
  have hReverseLogExp : ∀ t, Complex.exp (reverseLog t) = scalarCircleLoopReverse gamma t := by
    intro t
    exact hLogExp (2 * Real.pi - t)
  have hForward := RHTower.contLog_increment gamma.isLoop hLogContinuous hLogExp
  have hReverse := RHTower.contLog_increment (scalarCircleLoopReverse gamma).isLoop
    hReverseLogContinuous hReverseLogExp
  have hPeriod : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Complex.I_ne_zero, Real.pi_ne_zero]
  have hCast :
      (scalarCircleLoopWinding (scalarCircleLoopReverse gamma) : ℂ) =
        -(scalarCircleLoopWinding gamma : ℂ) := by
    change
      (RHTower.windingNumber (scalarCircleLoopReverse gamma).toFun 0 (2 * Real.pi) : ℂ) =
        -(RHTower.windingNumber gamma.toFun 0 (2 * Real.pi) : ℂ)
    apply mul_right_cancel₀ hPeriod
    rw [← hReverse]
    dsimp [reverseLog]
    simp only [sub_self, sub_zero]
    rw [show RHTower.contLog gamma.toFun 0 -
        RHTower.contLog gamma.toFun (2 * Real.pi) =
      -(RHTower.contLog gamma.toFun (2 * Real.pi) -
        RHTower.contLog gamma.toFun 0) by ring, hForward]
    ring
  exact_mod_cast hCast

/-- Forward/backward fringe loop: relative phase is twice the original phase. -/
def scalarCircleLoopFringe (gamma : ScalarCircleLoop) : ScalarCircleLoop where
  toFun := fun t => gamma t ^ (2 : ℕ)
  isLoop := by
    refine ⟨gamma.isLoop.continuous.pow 2,
      fun t => pow_ne_zero 2 (gamma.isLoop.nonzero t), ?_⟩
    simp only [gamma.isLoop.closed]

/-- Forward/backward readout doubles winding. -/
theorem scalarCircleLoopFringe_winding (gamma : ScalarCircleLoop) :
    scalarCircleLoopWinding (scalarCircleLoopFringe gamma) =
      2 * scalarCircleLoopWinding gamma := by
  exact RHTower.windingNumber_pow gamma.isLoop 2

/-- Every ideal forward/backward readout lies in the even winding sector. -/
theorem scalarCircleLoopFringe_winding_even (gamma : ScalarCircleLoop) :
    Even (scalarCircleLoopWinding (scalarCircleLoopFringe gamma)) := by
  rw [scalarCircleLoopFringe_winding]
  exact even_two_mul _

/-- Differential fringe of a clock loop and a counter-oriented system loop. -/
def scalarCircleLoopDifferentialFringe
    (clock system : ScalarCircleLoop) : ScalarCircleLoop where
  toFun := fun t => clock t ^ (2 : ℕ) * scalarCircleLoopReverse system t ^ (2 : ℕ)
  isLoop := by
    refine ⟨(clock.isLoop.continuous.pow 2).mul
        ((scalarCircleLoopReverse system).isLoop.continuous.pow 2),
      fun t => mul_ne_zero (pow_ne_zero 2 (clock.isLoop.nonzero t))
        (pow_ne_zero 2 ((scalarCircleLoopReverse system).isLoop.nonzero t)), ?_⟩
    simp only [clock.isLoop.closed, (scalarCircleLoopReverse system).isLoop.closed]

/-- Counter-oriented two-band readout measures twice the difference of windings. -/
theorem scalarCircleLoopDifferentialFringe_winding (clock system : ScalarCircleLoop) :
    scalarCircleLoopWinding (scalarCircleLoopDifferentialFringe clock system) =
      2 * (scalarCircleLoopWinding clock - scalarCircleLoopWinding system) := by
  calc
    scalarCircleLoopWinding (scalarCircleLoopDifferentialFringe clock system) =
        scalarCircleLoopWinding (scalarCircleLoopFringe clock) +
          scalarCircleLoopWinding
            (scalarCircleLoopFringe (scalarCircleLoopReverse system)) :=
      RHTower.windingNumber_mul
        (scalarCircleLoopFringe clock).isLoop
        (scalarCircleLoopFringe (scalarCircleLoopReverse system)).isLoop
    _ = 2 * (scalarCircleLoopWinding clock - scalarCircleLoopWinding system) := by
      rw [scalarCircleLoopFringe_winding, scalarCircleLoopFringe_winding,
        scalarCircleLoopReverse_winding]
      ring

/-- Differential readout is always even, including imperfectly separated two-band clocks. -/
theorem scalarCircleLoopDifferentialFringe_winding_even
    (clock system : ScalarCircleLoop) :
    Even (scalarCircleLoopWinding (scalarCircleLoopDifferentialFringe clock system)) := by
  rw [scalarCircleLoopDifferentialFringe_winding]
  exact even_two_mul _

/-- Differential readout vanishes exactly when the two scalar `K₁` charges agree. -/
theorem scalarCircleLoopDifferentialFringe_winding_eq_zero_iff
    (clock system : ScalarCircleLoop) :
    scalarCircleLoopWinding (scalarCircleLoopDifferentialFringe clock system) = 0 ↔
      scalarCircleLoopWinding clock = scalarCircleLoopWinding system := by
  rw [scalarCircleLoopDifferentialFringe_winding]
  omega

/-- A continuous real phase whose endpoints agree; exponentiation gives a zero-winding residual. -/
structure ClosedRealPhase where
  toFun : ℝ → ℝ
  continuous : Continuous toFun
  closed : toFun 0 = toFun (2 * Real.pi)

instance : CoeFun ClosedRealPhase (fun _ => ℝ → ℝ) := ⟨ClosedRealPhase.toFun⟩

/-- Unit-complex loop generated by a closed real phase. -/
def ClosedRealPhase.toScalarCircleLoop (phase : ClosedRealPhase) : ScalarCircleLoop where
  toFun := fun t => Complex.exp (Complex.I * (phase t : ℂ))
  isLoop := by
    refine ⟨Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp phase.continuous)),
      fun t => Complex.exp_ne_zero _, ?_⟩
    rw [phase.closed]

/-- Every single-valued periodic phase residual has zero winding. -/
theorem ClosedRealPhase.winding_eq_zero (phase : ClosedRealPhase) :
    scalarCircleLoopWinding phase.toScalarCircleLoop = 0 := by
  let phaseLog : ℝ → ℂ := fun t => Complex.I * (phase t : ℂ)
  have hContinuous : Continuous phaseLog :=
    continuous_const.mul (Complex.continuous_ofReal.comp phase.continuous)
  have hExp : ∀ t, Complex.exp (phaseLog t) = phase.toScalarCircleLoop t := fun _ => rfl
  apply (RHTower.windingNumber_eq_zero_iff phase.toScalarCircleLoop.isLoop hContinuous hExp).2
  dsimp [phaseLog]
  rw [phase.closed]

/-- Multiply a charged loop by an arbitrary closed, single-valued phase residual. -/
def scalarCircleLoopWithResidual
    (gamma : ScalarCircleLoop) (phase : ClosedRealPhase) : ScalarCircleLoop where
  toFun := fun t => gamma t * phase.toScalarCircleLoop t
  isLoop := by
    refine ⟨gamma.isLoop.continuous.mul phase.toScalarCircleLoop.isLoop.continuous,
      fun t => mul_ne_zero (gamma.isLoop.nonzero t) (phase.toScalarCircleLoop.isLoop.nonzero t), ?_⟩
    simp only [gamma.isLoop.closed, phase.toScalarCircleLoop.isLoop.closed]

/-- A periodic dynamical or fabrication residual spends phase margin but cannot change winding. -/
theorem scalarCircleLoopWithResidual_winding
    (gamma : ScalarCircleLoop) (phase : ClosedRealPhase) :
    scalarCircleLoopWinding (scalarCircleLoopWithResidual gamma phase) =
      scalarCircleLoopWinding gamma := by
  change RHTower.windingNumber
      (fun t => gamma t * phase.toScalarCircleLoop t) 0 (2 * Real.pi) =
    RHTower.windingNumber gamma.toFun 0 (2 * Real.pi)
  rw [RHTower.windingNumber_mul gamma.isLoop phase.toScalarCircleLoop.isLoop]
  have hzero := phase.winding_eq_zero
  change RHTower.windingNumber phase.toScalarCircleLoop.toFun 0 (2 * Real.pi) = 0 at hzero
  rw [hzero, add_zero]

/-- Explicit constant-plus-first-Fourier-mode residual phase. -/
def trigonometricClosedRealPhase (a b c : ℝ) : ClosedRealPhase where
  toFun := fun t => a * Real.cos t + b * Real.sin t + c
  continuous := (continuous_const.mul Real.continuous_cos).add
    (continuous_const.mul Real.continuous_sin) |>.add continuous_const
  closed := by simp

/-- Smooth first-Fourier-mode mismatch cannot alter any scalar winding readout. -/
theorem scalarCircleLoop_trigonometricResidual_winding
    (gamma : ScalarCircleLoop) (a b c : ℝ) :
    scalarCircleLoopWinding
        (scalarCircleLoopWithResidual gamma (trigonometricClosedRealPhase a b c)) =
      scalarCircleLoopWinding gamma :=
  scalarCircleLoopWithResidual_winding gamma _

/-- Integer clock sector: ideal readout returns exactly twice the encoded charge. -/
theorem scalarCircleLoopOfInt_fringe_winding (z : ℤ) :
    scalarCircleLoopWinding (scalarCircleLoopFringe (scalarCircleLoopOfInt z)) = 2 * z := by
  rw [scalarCircleLoopFringe_winding, scalarCircleLoopOfInt_winding]

/-- Integer two-band sectors: counter-oriented scan returns twice their charge difference. -/
theorem scalarCircleLoopOfInt_differentialFringe_winding (clock system : ℤ) :
    scalarCircleLoopWinding
        (scalarCircleLoopDifferentialFringe
          (scalarCircleLoopOfInt clock) (scalarCircleLoopOfInt system)) =
      2 * (clock - system) := by
  rw [scalarCircleLoopDifferentialFringe_winding,
    scalarCircleLoopOfInt_winding, scalarCircleLoopOfInt_winding]

/-- Fundamental unit-winding sector produces the paper's doubled winding `2`. -/
theorem fundamentalClockFringe_winding :
    scalarCircleLoopWinding (scalarCircleLoopFringe (scalarCircleLoopOfInt 1)) = 2 := by
  simpa using scalarCircleLoopOfInt_fringe_winding 1

/-- K₁-level readout map: multiplication by two. -/
def topologicalClockReadoutKOne (q : CircleOperatorKOne) : CircleOperatorKOne :=
  circleOperatorKOneEquivInt.symm (2 * circleOperatorKOneEquivInt q)

/-- K₁ winding coordinate of the readout is doubled. -/
theorem circleOperatorKOneWinding_topologicalClockReadout (q : CircleOperatorKOne) :
    circleOperatorKOneWinding (topologicalClockReadoutKOne q) =
      2 * circleOperatorKOneWinding q := by
  change circleOperatorKOneEquivInt
      (circleOperatorKOneEquivInt.symm (2 * circleOperatorKOneEquivInt q)) =
    2 * circleOperatorKOneEquivInt q
  exact circleOperatorKOneEquivInt.apply_symm_apply _

/-- Doubling loses no scalar-circle K₁ information. -/
theorem topologicalClockReadoutKOne_injective : Function.Injective topologicalClockReadoutKOne := by
  intro q r hqr
  apply circleOperatorKOneEquivInt.injective
  have h := congrArg circleOperatorKOneWinding hqr
  rw [circleOperatorKOneWinding_topologicalClockReadout,
    circleOperatorKOneWinding_topologicalClockReadout] at h
  change circleOperatorKOneWinding q = circleOperatorKOneWinding r
  omega

/-- Odd winding can never be an ideal forward/backward readout. -/
theorem topologicalClockReadoutKOne_ne_of_odd_winding
    (q r : CircleOperatorKOne) (hodd : Odd (circleOperatorKOneWinding r)) :
    topologicalClockReadoutKOne q ≠ r := by
  intro h
  have hr := congrArg circleOperatorKOneWinding h
  rw [circleOperatorKOneWinding_topologicalClockReadout] at hr
  obtain ⟨k, hk⟩ := hodd
  omega

end PrimeQuasiLocalCharge

end
