import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberFiniteCoreBridge
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberCurrent

/-!
# Seam-preserving finite-core moment bridge

The moment packet of one arithmetic density atom is moved to the first canonical atom without
discarding the positive-half-line endpoint.  After the move, the completion multiplier, the
constant seam, both finite phase channels, and both finite translation top edges remain in one
value--derivative pair.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- Joint two-phase value produced by translating the finite core through a logarithmic shift.
The argument `a` is the positive endpoint; the core itself is translated by `-a`. -/
def finiteCoreArithmeticTwoPhaseValue
    (d : ℕ) (z : ℂ) (u a : ℝ) : ℂ :=
  (z ^ 2 + 1 / 4) *
      (((finitePositivePhasePolynomial (d + 1) u *
            finitePositivePhasePolynomial (d + 1) (-a) -
          finitePositivePhaseTranslationTopEdge (d + 1) u (-a)).eval z) +
        ((finiteNegativePhasePolynomial (d + 1) u *
            finiteNegativePhasePolynomial (d + 1) (-a) -
          finiteNegativePhaseTranslationTopEdge (d + 1) u (-a)).eval z)) -
    1 / 2

/-- Derivative vector paired with `finiteCoreArithmeticTwoPhaseValue`. -/
def finiteCoreArithmeticTwoPhaseDerivative
    (d : ℕ) (z : ℂ) (u a : ℝ) : ℂ :=
  (z ^ 2 + 1 / 4) *
      ((finitePositivePhasePolynomial (d + 1) u *
            finitePositivePhasePolynomial (d + 1) (-a) -
          finitePositivePhaseTranslationTopEdge (d + 1) u (-a)).derivative.eval z +
        (finiteNegativePhasePolynomial (d + 1) u *
            finiteNegativePhasePolynomial (d + 1) (-a) -
          finiteNegativePhaseTranslationTopEdge (d + 1) u (-a)).derivative.eval z) +
    2 * z *
      (((finitePositivePhasePolynomial (d + 1) u *
            finitePositivePhasePolynomial (d + 1) (-a) -
          finitePositivePhaseTranslationTopEdge (d + 1) u (-a)).eval z) +
        ((finiteNegativePhasePolynomial (d + 1) u *
            finiteNegativePhasePolynomial (d + 1) (-a) -
          finiteNegativePhaseTranslationTopEdge (d + 1) u (-a)).eval z))

theorem finiteCoreArithmeticTwoPhaseValue_eq
    (d : ℕ) (z : ℂ) (u a : ℝ) :
    finiteCoreArithmeticTwoPhaseValue d z u a =
      2 * (z ^ 2 * thetaCuspTailSecondCoreAtom d z (u - a)) := by
  rw [show u - a = u + (-a) by ring]
  exact (two_mul_sq_mul_thetaCuspTailSecondCoreAtom_add_eq_twoPhase
    d z u (-a)).symm

theorem finiteCoreArithmeticTwoPhaseDerivative_eq
    (d : ℕ) (z : ℂ) (u a : ℝ) :
    finiteCoreArithmeticTwoPhaseDerivative d z u a =
      2 * (z ^ 2 * thetaCuspTailSecondCoreAtomDerivative d z (u - a) +
        2 * z * thetaCuspTailSecondCoreAtom d z (u - a)) := by
  rw [show u - a = u + (-a) by ring]
  exact (two_mul_sq_mul_thetaCuspTailSecondCoreAtomDerivative_add_eq_twoPhase
    d z u (-a)).symm

/-- **Exact arithmetic value bridge.**  The completion-scaled finite moment packet of one
positive square index is the first-atom tail integral of the complete two-phase packet. -/
theorem two_mul_sq_mul_thetaCuspTailSecondDensityAtomCoreValueMomentPacket_eq_twoPhase
    (d : ℕ) (z : ℂ) (n : ℕ) :
    2 * (z ^ 2 * thetaCuspTailSecondDensityAtomCoreValueMomentPacket d z n) =
      ((((n + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∫ u : ℝ in Ioi (Real.log (n + 1 : ℕ)),
          (thetaCuspTailSecondDensityAtom 1 u : ℂ) *
            finiteCoreArithmeticTwoPhaseValue d z u (Real.log (n + 1 : ℕ)) := by
  rw [← integral_thetaCuspTailSecondDensityAtom_mul_coreAtom]
  have htranslate := integral_densityAtom_mul_eq_rpow_mul_integral_translate
    (fun x : ℝ => 2 * (z ^ 2 * thetaCuspTailSecondCoreAtom d z x))
    (show 0 < n + 1 by omega)
  rw [show (fun x : ℝ =>
      (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
        (2 * (z ^ 2 * thetaCuspTailSecondCoreAtom d z x))) =
      fun x : ℝ => 2 * z ^ 2 *
        ((thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
          thetaCuspTailSecondCoreAtom d z x) by
    funext x
    ring,
    integral_const_mul] at htranslate
  calc
    2 * (z ^ 2 *
        ∫ x : ℝ in Ioi 0,
          (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
            thetaCuspTailSecondCoreAtom d z x) =
      2 * z ^ 2 *
        (∫ x : ℝ in Ioi 0,
          (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
            thetaCuspTailSecondCoreAtom d z x) := by ring
    _ = ((((n + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∫ u : ℝ in Ioi (Real.log (n + 1 : ℕ)),
          (thetaCuspTailSecondDensityAtom 1 u : ℂ) *
            (2 * (z ^ 2 * thetaCuspTailSecondCoreAtom d z
              (u - Real.log (n + 1 : ℕ)))) := htranslate
    _ = _ := by
      congr 2
      funext u
      rw [finiteCoreArithmeticTwoPhaseValue_eq]

/-- **Exact arithmetic derivative bridge.**  The derivative of the completion-scaled packet is
transported with the same endpoint, phase channels, top edges, and constant seam as its value. -/
theorem two_mul_sq_mul_thetaCuspTailSecondDensityAtomCoreDerivativePacket_eq_twoPhase
    (d : ℕ) (z : ℂ) (n : ℕ) :
    2 * (z ^ 2 * thetaCuspTailSecondDensityAtomCoreDerivativeMomentPacket d z n +
        2 * z * thetaCuspTailSecondDensityAtomCoreValueMomentPacket d z n) =
      ((((n + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∫ u : ℝ in Ioi (Real.log (n + 1 : ℕ)),
          (thetaCuspTailSecondDensityAtom 1 u : ℂ) *
            finiteCoreArithmeticTwoPhaseDerivative d z u (Real.log (n + 1 : ℕ)) := by
  rw [← integral_thetaCuspTailSecondDensityAtom_mul_coreAtomDerivative,
    ← integral_thetaCuspTailSecondDensityAtom_mul_coreAtom]
  let K : ℝ → ℂ := fun x =>
    2 * (z ^ 2 * thetaCuspTailSecondCoreAtomDerivative d z x +
      2 * z * thetaCuspTailSecondCoreAtom d z x)
  have htranslate := integral_densityAtom_mul_eq_rpow_mul_integral_translate
    K (show 0 < n + 1 by omega)
  have hDint := integrableOn_thetaCuspTailSecondDensityAtom_mul_coreAtomDerivative d z n
  have hVint := integrableOn_thetaCuspTailSecondDensityAtom_mul_coreAtom d z n
  have hleft :
      (∫ x : ℝ in Ioi 0,
        (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) * K x) =
      2 * (z ^ 2 *
          (∫ x : ℝ in Ioi 0,
            (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
              thetaCuspTailSecondCoreAtomDerivative d z x) +
        2 * z *
          (∫ x : ℝ in Ioi 0,
            (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
              thetaCuspTailSecondCoreAtom d z x)) := by
    rw [show (fun x : ℝ =>
        (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) * K x) =
      fun x : ℝ =>
        (2 * z ^ 2) *
          ((thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
            thetaCuspTailSecondCoreAtomDerivative d z x) +
        (4 * z) *
          ((thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
            thetaCuspTailSecondCoreAtom d z x) by
      funext x
      dsimp [K]
      ring,
      integral_add (hDint.const_mul (2 * z ^ 2)) (hVint.const_mul (4 * z)),
      integral_const_mul, integral_const_mul]
    ring
  rw [hleft] at htranslate
  calc
    2 * (z ^ 2 *
          (∫ x : ℝ in Ioi 0,
            (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
              thetaCuspTailSecondCoreAtomDerivative d z x) +
        2 * z *
          (∫ x : ℝ in Ioi 0,
            (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
              thetaCuspTailSecondCoreAtom d z x)) =
      ((((n + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∫ u : ℝ in Ioi (Real.log (n + 1 : ℕ)),
          (thetaCuspTailSecondDensityAtom 1 u : ℂ) *
            K (u - Real.log (n + 1 : ℕ)) := htranslate
    _ = _ := by
      congr 2
      funext u
      rw [finiteCoreArithmeticTwoPhaseDerivative_eq]

end

end RHTower
