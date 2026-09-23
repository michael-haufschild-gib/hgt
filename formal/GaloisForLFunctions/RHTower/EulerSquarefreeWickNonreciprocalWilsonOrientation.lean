import GaloisForLFunctions.HTGeometry.DirectionalWilsonReciprocity
import GaloisForLFunctions.RHTower.EulerSquarefreeWickCompletedJetBundleLanding
import GaloisForLFunctions.RHTower.EulerSquarefreeWickHedenmalmReflectionCrossing

/-!
# Nonreciprocal Wilson orientation for the completed Euler--Wick interaction

The directional non-Hermitian Wilson mechanism is transplanted into the exact EWQ--Hedenmalm
channel.  Four Pauli links ordered as `Y · iI · zX · Z` clockwise and `iI · Y · Z · zX`
counterclockwise have traces `2z` and `-2z`.  Their signed contrast is therefore `4z`, while their
trace magnitudes are identical.  The contrast is nonzero exactly when reverse-adjoint reciprocity
fails.

For the actual Hedenmalm covariant amplitude this signed contrast vanishes exactly on the critical
line, and the EWQ reflected crossing is its negative square with the literal prime-logarithmic
weight.  Multiplication by the complete pre-divisor EWQ jet family never erases this criterion:
the function-valued completed contrast is zero exactly when the amplitude is zero.

This closes a landing/non-erasure subproblem but not the source producer.  The imported passive
reciprocity theorem shows that PSD/Hermitian block-kernel positivity cannot force this active
contrast: reverse-adjoint links make its real and absolute directional contrasts vanish before any
RH information enters.  A successful route must therefore derive active non-Hermitian reciprocity
breaking from an independent arithmetic source law; magnitude-only Wilson measurement is also
insufficient for this Pauli embedding.
-/

open scoped BigOperators Matrix

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Pauli `Y` link. -/
def ewqDirectionalPauliY : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), -Complex.I; Complex.I, 0]

/-- Central quarter-turn link `iI`. -/
def ewqDirectionalPhaseI : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.I, 0; 0, Complex.I]

/-- Source amplitude placed on a Pauli `X` link. -/
def ewqDirectionalScaledX (z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), z; z, 0]

/-- Pauli `Z` link. -/
def ewqDirectionalPauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 : ℂ), 0; 0, -1]

/-- Clockwise ordered active Wilson word. -/
def ewqDirectionalWilsonCW (z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ewqDirectionalPauliY * ewqDirectionalPhaseI * ewqDirectionalScaledX z *
    ewqDirectionalPauliZ

/-- Counterclockwise word using independently programmed directional links. -/
def ewqDirectionalWilsonCCW (z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ewqDirectionalPhaseI * ewqDirectionalPauliY * ewqDirectionalPauliZ *
    ewqDirectionalScaledX z

theorem ewqDirectionalWilsonCW_eq (z : ℝ) :
    ewqDirectionalWilsonCW z = (z : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ewqDirectionalWilsonCW, ewqDirectionalPauliY, ewqDirectionalPhaseI,
      ewqDirectionalScaledX, ewqDirectionalPauliZ, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem ewqDirectionalWilsonCCW_eq (z : ℝ) :
    ewqDirectionalWilsonCCW z = (-z : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ewqDirectionalWilsonCCW, ewqDirectionalPauliY, ewqDirectionalPhaseI,
      ewqDirectionalScaledX, ewqDirectionalPauliZ, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem trace_ewqDirectionalWilsonCW (z : ℝ) :
    Matrix.trace (ewqDirectionalWilsonCW z) = 2 * z := by
  simp [ewqDirectionalWilsonCW_eq, Matrix.trace]

theorem trace_ewqDirectionalWilsonCCW (z : ℝ) :
    Matrix.trace (ewqDirectionalWilsonCCW z) = -2 * z := by
  simp [ewqDirectionalWilsonCCW_eq, Matrix.trace]

/-- Signed real clockwise/counterclockwise Wilson contrast. -/
def ewqDirectionalWilsonSignedContrast (z : ℝ) : ℝ :=
  (Matrix.trace (ewqDirectionalWilsonCW z)).re -
    (Matrix.trace (ewqDirectionalWilsonCCW z)).re

/-- Absolute Wilson contrast, matching a magnitude-only measurement protocol. -/
def ewqDirectionalWilsonMagnitudeContrast (z : ℝ) : ℝ :=
  ‖Matrix.trace (ewqDirectionalWilsonCW z)‖ -
    ‖Matrix.trace (ewqDirectionalWilsonCCW z)‖

/-- The active signed Wilson word is a linear orientation lift. -/
theorem ewqDirectionalWilsonSignedContrast_eq (z : ℝ) :
    ewqDirectionalWilsonSignedContrast z = 4 * z := by
  rw [ewqDirectionalWilsonSignedContrast, trace_ewqDirectionalWilsonCW,
    trace_ewqDirectionalWilsonCCW]
  norm_num
  ring

/-- Magnitude-only observation erases this exact orientation lift. -/
theorem ewqDirectionalWilsonMagnitudeContrast_eq_zero (z : ℝ) :
    ewqDirectionalWilsonMagnitudeContrast z = 0 := by
  rw [ewqDirectionalWilsonMagnitudeContrast, trace_ewqDirectionalWilsonCW,
    trace_ewqDirectionalWilsonCCW]
  norm_num

/-- Reverse-adjoint reciprocity holds for the active words exactly at zero source amplitude. -/
theorem ewqDirectionalWilsonCCW_eq_conjTranspose_CW_iff (z : ℝ) :
    ewqDirectionalWilsonCCW z = (ewqDirectionalWilsonCW z)ᴴ ↔ z = 0 := by
  rw [ewqDirectionalWilsonCCW_eq, ewqDirectionalWilsonCW_eq]
  constructor
  · intro h
    have h00 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
    simp at h00
    apply_fun Complex.re at h00
    norm_num at h00
    linarith
  · rintro rfl
    simp

/-- Actual EWQ--Hedenmalm amplitude read by the active directional Wilson word. -/
def ewqHedenmalmDirectionalWilsonContrast
    (p : Nat.Primes) (q : _root_.RHTower.XiZeroCopy) : ℝ :=
  ewqDirectionalWilsonSignedContrast (ewqHedenmalmCovariantAmplitude p q)

theorem ewqHedenmalmDirectionalWilsonContrast_eq
    (p : Nat.Primes) (q : _root_.RHTower.XiZeroCopy) :
    ewqHedenmalmDirectionalWilsonContrast p q =
      4 * ewqHedenmalmCovariantAmplitude p q := by
  rw [ewqHedenmalmDirectionalWilsonContrast,
    ewqDirectionalWilsonSignedContrast_eq]

theorem ewqHedenmalmCovariantAmplitude_eq_zero_iff
    (p : Nat.Primes) (q : _root_.RHTower.XiZeroCopy) :
    ewqHedenmalmCovariantAmplitude p q = 0 ↔ (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hamp
    by_contra hline
    have hrate : _root_.RHTower.primeDepthBVWoldXiCenteredRate q.1 ≠ 0 :=
      fun hzero => hline
        ((_root_.RHTower.primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).1 hzero)
    exact ((ewqHedenmalmCovariantAmplitude_ne_zero_iff p q).2 hrate) hamp
  · intro hline
    have hrate :=
      (_root_.RHTower.primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).2 hline
    rw [ewqHedenmalmCovariantAmplitude,
      _root_.RHTower.HedenmalmThetaSource.thetaMovingHorizonConnection_eq_centeredRate_mul,
      hrate, zero_mul]

/-- The active signed Wilson contrast vanishes exactly on the critical line. -/
theorem ewqHedenmalmDirectionalWilsonContrast_eq_zero_iff
    (p : Nat.Primes) (q : _root_.RHTower.XiZeroCopy) :
    ewqHedenmalmDirectionalWilsonContrast p q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [ewqHedenmalmDirectionalWilsonContrast_eq, mul_eq_zero]
  norm_num
  exact ewqHedenmalmCovariantAmplitude_eq_zero_iff p q

/-- **Directional square-root law.**  The exact reflected EWQ crossing is the negative square of
the signed Wilson orientation lift, with its literal prime-logarithmic coefficient. -/
theorem ewqHedenmalm_reflectedCrossing_eq_neg_directionalWilsonContrast_sq
    (p : Nat.Primes) (q : _root_.RHTower.XiZeroCopy) (x y : Fin 2) :
    eulerPrimeQuadraticResidueOppositeBilinearCrossing p
        (ewqHedenmalmCovariantAmplitude p q)
        (ewqHedenmalmCovariantAmplitude p (_root_.RHTower.xiZeroCopyReflectEquiv q)) x y =
      -(Real.log (p : ℝ) / 4) *
        ewqHedenmalmDirectionalWilsonContrast p q ^ (2 : ℕ) := by
  rw [ewqHedenmalm_reflectedCrossing_eq_neg_self,
    eulerPrimeQuadraticResidueOppositeCrossing_eq,
    ewqHedenmalmDirectionalWilsonContrast_eq]
  ring

/-- Completed pre-divisor EWQ jet weight applied to the active contrast. -/
def eulerWickCompletedJetDirectionalWilsonContrast
    (s : ℂ) (n : ℕ) (z : ℝ) : ℝ :=
  Complex.normSq
      (iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction s) *
    ewqDirectionalWilsonSignedContrast z

/-- Some completed jet coordinate is a faithful directional contrast channel at every point. -/
theorem exists_eulerWickCompletedJetDirectionalWilsonContrast_eq_zero_iff
    (s : ℂ) (z : ℝ) :
    ∃ n : ℕ, eulerWickCompletedJetDirectionalWilsonContrast s n z = 0 ↔ z = 0 := by
  have hjet := eulerWickPrimitiveCompletedInteractionJet_ne_zero s
  obtain ⟨n, hn⟩ : ∃ n : ℕ,
      iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction s ≠ 0 := by
    simpa [eulerWickPrimitiveCompletedInteractionJet, funext_iff] using hjet
  refine ⟨n, ?_⟩
  rw [eulerWickCompletedJetDirectionalWilsonContrast,
    ewqDirectionalWilsonSignedContrast_eq, mul_eq_zero]
  have hnorm : Complex.normSq
      (iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction s) ≠ 0 := by
    intro hzero
    exact hn (Complex.normSq_eq_zero.mp hzero)
  simp [hnorm]

/-- Full completed-jet directional contrast, formed before selecting any divisor coordinate. -/
def eulerWickCompletedJetDirectionalWilsonContrastFamily
    (s : ℂ) (z : ℝ) : ℕ → ℝ :=
  fun n => eulerWickCompletedJetDirectionalWilsonContrast s n z

/-- **Completed-jet non-erasure.**  The full pre-divisor family is zero exactly at zero amplitude. -/
theorem eulerWickCompletedJetDirectionalWilsonContrastFamily_eq_zero_iff
    (s : ℂ) (z : ℝ) :
    eulerWickCompletedJetDirectionalWilsonContrastFamily s z = 0 ↔ z = 0 := by
  constructor
  · intro hfamily
    obtain ⟨n, hn⟩ :=
      exists_eulerWickCompletedJetDirectionalWilsonContrast_eq_zero_iff s z
    apply hn.mp
    simpa [eulerWickCompletedJetDirectionalWilsonContrastFamily] using congrFun hfamily n
  · rintro rfl
    funext n
    simp [eulerWickCompletedJetDirectionalWilsonContrastFamily,
      eulerWickCompletedJetDirectionalWilsonContrast,
      ewqDirectionalWilsonSignedContrast_eq]

/-- Completed pre-divisor jet family carrying the actual Hedenmalm amplitude at a Xi copy. -/
def ewqCompletedJetHedenmalmDirectionalWilsonContrastFamily
    (p : Nat.Primes) (q : _root_.RHTower.XiZeroCopy) : ℕ → ℝ :=
  eulerWickCompletedJetDirectionalWilsonContrastFamily q.1
    (ewqHedenmalmCovariantAmplitude p q)

/-- Completed-jet active contrast is zero exactly on the critical line. -/
theorem ewqCompletedJetHedenmalmDirectionalWilsonContrastFamily_eq_zero_iff
    (p : Nat.Primes) (q : _root_.RHTower.XiZeroCopy) :
    ewqCompletedJetHedenmalmDirectionalWilsonContrastFamily p q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [ewqCompletedJetHedenmalmDirectionalWilsonContrastFamily,
    eulerWickCompletedJetDirectionalWilsonContrastFamily_eq_zero_iff,
    ewqHedenmalmCovariantAmplitude_eq_zero_iff]

/-- Global active directional-source target at one fixed prime. -/
def EveryXiEWQDirectionalWilsonContrastZeroAt (p : Nat.Primes) : Prop :=
  ∀ q : _root_.RHTower.XiZeroCopy,
    ewqHedenmalmDirectionalWilsonContrast p q = 0

/-- Global vanishing of the unweighted active contrast is exactly RH. -/
theorem everyXiEWQDirectionalWilsonContrastZeroAt_iff_rh (p : Nat.Primes) :
    EveryXiEWQDirectionalWilsonContrastZeroAt p ↔ _root_.RiemannHypothesis := by
  constructor
  · intro h
    apply _root_.RHTower.riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    intro rho
    let q := _root_.RHTower.xiFirstZeroCopy rho
    have hq := (ewqHedenmalmDirectionalWilsonContrast_eq_zero_iff p q).1 (h q)
    simpa [q] using hq
  · intro hRH q
    exact (ewqHedenmalmDirectionalWilsonContrast_eq_zero_iff p q).2
      (_root_.RHTower.xi_divisor_support_re_eq_half_of_rh hRH q.1)

/-- Global completed-jet active-source target at one fixed prime. -/
def EveryXiEWQCompletedJetDirectionalWilsonContrastFamilyZeroAt
    (p : Nat.Primes) : Prop :=
  ∀ q : _root_.RHTower.XiZeroCopy,
    ewqCompletedJetHedenmalmDirectionalWilsonContrastFamily p q = 0

/-- Global vanishing of the coefficient-faithful completed active contrast is exactly RH. -/
theorem everyXiEWQCompletedJetDirectionalWilsonContrastFamilyZeroAt_iff_rh
    (p : Nat.Primes) :
    EveryXiEWQCompletedJetDirectionalWilsonContrastFamilyZeroAt p ↔
      _root_.RiemannHypothesis := by
  constructor
  · intro h
    apply _root_.RHTower.riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    intro rho
    let q := _root_.RHTower.xiFirstZeroCopy rho
    have hq :=
      (ewqCompletedJetHedenmalmDirectionalWilsonContrastFamily_eq_zero_iff p q).1 (h q)
    simpa [q] using hq
  · intro hRH q
    exact (ewqCompletedJetHedenmalmDirectionalWilsonContrastFamily_eq_zero_iff p q).2
      (_root_.RHTower.xi_divisor_support_re_eq_half_of_rh hRH q.1)

end GaloisForLFunctions.RHTower
