import GaloisForLFunctions.HTGeometry.FokasLenellsOrbitDecay

/-!
# A correction exposing the second spectral power

For c = off-diagonal coefficient, d = diagonal coefficient, and
λ = -iω, set w = λ off + c(0) rowDiagonal - exp(-iωx)c diagonal.
The initial value is zero. Its differential equation has diagonal transport,
an oscillatory source with Schwartz coefficient 2dc-c′, and terms already
controlled by the first spectral-power estimate. At the two infinite
endpoints, the c(0) terms cancel in the actual scattering matrix.
-/

open Complex Matrix Set MeasureTheory Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

theorem offOrbitDiagonal_opposite (f g h : SchwartzMap ℝ ℂ) (left upper : Bool) (x : ℝ) :
    offOrbitDiagonal f g h left (!upper) x = -offOrbitDiagonal f g h left upper x := by
  cases left <;> cases upper <;>
    simp [offOrbitDiagonal,orientedSchwartzEntry_apply,effectiveSchwartzEntries] <;> ring

theorem offOrbitFrequency_opposite (z : ℝ) (left upper : Bool) :
    offOrbitFrequency z left (!upper) = -offOrbitFrequency z left upper := by
  cases left <;> cases upper <;> simp [offOrbitFrequency]

/-- The companion diagonal equation has the opposite phase and opposite diagonal transport. -/
theorem diagonalOrbitRate_eq (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) :
    diagonalOrbitRate f g h z left upper x =
      -offOrbitDiagonal f g h left upper x*diagonalOrbit f g h z left upper x+
      FDNLS.staggerPhase (-offOrbitFrequency z left upper) x*
        (offOrbitCoefficient f g h left (!upper) x*offOrbit f g h z left upper x) := by
  cases left <;> cases upper <;>
    simp [diagonalOrbitRate,offOrbitDiagonal,offOrbit,diagonalOrbit,offOrbitCoefficient,
      orientedSchwartzEntry_apply,uniformizedOrbitDerivative,uniformizedOrbit,
      uniformizedInteractionRate,effectiveOperator,rotatingFrame_pairOperator,offOrbitFrequency,
      staggerPhase_neg_time,neg_mul,effectiveSchwartzEntries] <;> ring

/-- The diagonal entry in the same row as the off-diagonal entry comes from the other normalized column. -/
theorem rowDiagonalOrbitRate_eq (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) :
    diagonalOrbitRate f g h z left (!upper) x =
      offOrbitDiagonal f g h left upper x*diagonalOrbit f g h z left (!upper) x+
      FDNLS.staggerPhase (offOrbitFrequency z left upper) x*
        (offOrbitCoefficient f g h left upper x*offOrbit f g h z left (!upper) x) := by
  rw [diagonalOrbitRate_eq,offOrbitDiagonal_opposite,offOrbitFrequency_opposite,neg_neg,neg_neg]
  simp only [Bool.not_not]

/-- The next oscillatory coefficient remains a genuine Schwartz function. -/
def correctedOffCoefficient (f g h : SchwartzMap ℝ ℂ) (left upper : Bool) : SchwartzMap ℝ ℂ :=
  (2 : ℂ) • mulS (offOrbitDiagonal f g h left upper) (offOrbitCoefficient f g h left upper)-
    SchwartzMap.derivCLM ℂ ℂ (offOrbitCoefficient f g h left upper)

theorem correctedOffCoefficient_apply (f g h : SchwartzMap ℝ ℂ) (left upper : Bool) (x : ℝ) :
    correctedOffCoefficient f g h left upper x =
      2*offOrbitDiagonal f g h left upper x*offOrbitCoefficient f g h left upper x-
        SchwartzMap.derivCLM ℂ ℂ (offOrbitCoefficient f g h left upper) x := by
  simp [correctedOffCoefficient]
  ring

def correctedOffOrbit (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) : ℂ :=
  -(I*(offOrbitFrequency z left upper : ℂ))*offOrbit f g h z left upper x+
    offOrbitCoefficient f g h left upper 0*diagonalOrbit f g h z left (!upper) x-
    FDNLS.staggerPhase (offOrbitFrequency z left upper) x*
      (offOrbitCoefficient f g h left upper x*diagonalOrbit f g h z left upper x)

def correctedOffRate (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) : ℂ :=
  offOrbitDiagonal f g h left upper x*correctedOffOrbit f g h z left upper x+
    FDNLS.staggerPhase (offOrbitFrequency z left upper) x*
      (correctedOffCoefficient f g h left upper x*diagonalOrbit f g h z left upper x)-
    (offOrbitCoefficient f g h left upper x*offOrbitCoefficient f g h left (!upper) x)*offOrbit f g h z left upper x+
    offOrbitCoefficient f g h left upper 0*FDNLS.staggerPhase (offOrbitFrequency z left upper) x*
      (offOrbitCoefficient f g h left upper x*offOrbit f g h z left (!upper) x)

/-- The leading endpoint correction has exactly zero initial value. -/
theorem correctedOffOrbit_initial (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) :
    correctedOffOrbit f g h z left upper 0 = 0 := by
  simp [correctedOffOrbit,offOrbit_initial,diagonalOrbit_initial,FDNLS.staggerPhase]

/-- The corrected equation exposes one oscillatory Schwartz source and two already-decaying off-diagonal terms. -/
theorem correctedOffOrbit_hasDerivAt (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) :
    HasDerivAt (correctedOffOrbit f g h z left upper) (correctedOffRate f g h z left upper x) x := by
  have h1 := (offOrbit_hasDerivAt f g h z left upper x).const_mul (-(I*(offOrbitFrequency z left upper : ℂ)))
  have h2 := (diagonalOrbit_hasDerivAt f g h z left (!upper) x).const_mul (offOrbitCoefficient f g h left upper 0)
  have h3 := (FDNLS.hasDerivAt_staggerPhase (offOrbitFrequency z left upper) x).fun_mul
    ((offOrbitCoefficient f g h left upper).hasDerivAt x |>.fun_mul (diagonalOrbit_hasDerivAt f g h z left upper x))
  have hp := staggerPhase_mul_opposite (offOrbitFrequency z left upper) x
  convert! (h1.fun_add h2).fun_sub h3 using 1
  rw [offOrbitRate_eq,rowDiagonalOrbitRate_eq,diagonalOrbitRate_eq]
  simp only [correctedOffRate,correctedOffOrbit,correctedOffCoefficient_apply,SchwartzMap.derivCLM_apply]
  linear_combination (offOrbitCoefficient f g h left upper x*offOrbitCoefficient f g h left (!upper) x*
    offOrbit f g h z left upper x)*hp

theorem correctedOffOrbit_continuous (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) :
    Continuous (correctedOffOrbit f g h z left upper) :=
  continuous_iff_continuousAt.mpr fun x => (correctedOffOrbit_hasDerivAt f g h z left upper x).continuousAt

theorem correctedOffRate_continuous (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) :
    Continuous (correctedOffRate f g h z left upper) := by
  have hp : Continuous (FDNLS.staggerPhase (offOrbitFrequency z left upper)) := by unfold FDNLS.staggerPhase; fun_prop
  exact ((((offOrbitDiagonal f g h left upper).continuous.mul (correctedOffOrbit_continuous f g h z left upper)).add
    (hp.mul ((correctedOffCoefficient f g h left upper).continuous.mul (diagonalOrbit_continuous f g h z left upper)))).sub
      (((offOrbitCoefficient f g h left upper).continuous.mul (offOrbitCoefficient f g h left (!upper)).continuous).mul
        (offOrbit_continuous f g h z left upper))).add
          ((continuous_const.mul hp).mul ((offOrbitCoefficient f g h left upper).continuous.mul
            (offOrbit_continuous f g h z left (!upper))))

end
end GaloisForLFunctions.HTGeometry.FokasLenells
