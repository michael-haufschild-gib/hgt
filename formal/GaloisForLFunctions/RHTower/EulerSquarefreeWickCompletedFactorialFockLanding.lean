import GaloisForLFunctions.HTGeometry.OrderOneFactorialFockLanding
import GaloisForLFunctions.HTGeometry.WeightedAtomHilbert
import GaloisForLFunctions.RHTower.DirichletCompletedLOrderOne
import GaloisForLFunctions.RHTower.EulerSquarefreeWickCompletedJetOrientationRigidity

/-!
# Completed EWQ factorial-Fock landing

Order-one growth upgrades the countable primitive completed EWQ jet from a product-valued detector
to an honest vector in `ℓ²(ℕ)`: the `n`-th derivative is divided by `√(n!)`.  The vector is
nonzero at every basepoint and the functional equation is represented by a fixed diagonal unitary
carrying root number and derivative parity.

This also identifies an exact obstruction.  The Hilbert norm is invariant under `s ↦ 1-s` for
every complex `s`, not only on the critical line.  Therefore factorial-Fock landing solves the
completed Hilbert-space realization problem but cannot itself supply the missing orientation
producer; any surviving fusion must retain phase-sensitive comparison with Schwarz conjugation.
-/

open Complex
open scoped ENNReal InnerProductSpace

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem eulerWickQuadraticPrimitiveCompletedInteraction_orderOneEnvelope :
    OrderOneEnvelope eulerWickQuadraticPrimitiveCompletedInteraction := by
  have hpow0 := (orderOneEnvelope_natCast_cpow_neg (n := 12) (by norm_num)).comp_affine
    (-(1 / 2 : ℂ)) 0
  have hpow : OrderOneEnvelope (fun s : ℂ => (12 : ℂ) ^ (s / 2)) :=
    hpow0.congr fun s => by
      congr 1
      ring
  have hL : OrderOneEnvelope
      (DirichletCharacter.completedLFunction quadraticCharacterTwelve) :=
    _root_.RHTower.completedLFunction_orderOneEnvelope quadraticCharacterTwelve_ne_one
  exact (hpow.mul hL).congr fun s => by
    rfl

theorem summable_eulerWickPrimitiveCompletedInteraction_rawJetFactorialFockEnergy
    (s : ℂ) :
    Summable (fun n : ℕ =>
      ‖iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction s‖ ^ 2 /
        n.factorial) :=
  eulerWickQuadraticPrimitiveCompletedInteraction_orderOneEnvelope
    |>.summable_rawJetFactorialFockEnergy
      eulerWickQuadraticPrimitiveCompletedInteraction_differentiable s

/-- Factorial normalization of the full primitive completed EWQ jet. -/
def eulerWickPrimitiveCompletedInteractionFockCoord (s : ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction s /
    (Real.sqrt (n.factorial : ℝ) : ℂ)

theorem summable_norm_sq_eulerWickPrimitiveCompletedInteractionFockCoord (s : ℂ) :
    Summable (fun n : ℕ =>
      ‖eulerWickPrimitiveCompletedInteractionFockCoord s n‖ ^ 2) := by
  refine (summable_eulerWickPrimitiveCompletedInteraction_rawJetFactorialFockEnergy s).congr
    fun n => ?_
  rw [eulerWickPrimitiveCompletedInteractionFockCoord, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), div_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]

/-- Honest factorial-Fock Hilbert landing of the full completed EWQ jet. -/
def eulerWickPrimitiveCompletedInteractionFockVector (s : ℂ) :
    lp (fun _ : ℕ => ℂ) 2 :=
  ⟨eulerWickPrimitiveCompletedInteractionFockCoord s,
    HilbertSchmidt.memℓp_of_sq
      (summable_norm_sq_eulerWickPrimitiveCompletedInteractionFockCoord s)⟩

@[simp] theorem eulerWickPrimitiveCompletedInteractionFockVector_apply
    (s : ℂ) (n : ℕ) :
    eulerWickPrimitiveCompletedInteractionFockVector s n =
      eulerWickPrimitiveCompletedInteractionFockCoord s n := rfl

theorem eulerWickPrimitiveCompletedInteractionFockVector_ne_zero (s : ℂ) :
    eulerWickPrimitiveCompletedInteractionFockVector s ≠ 0 := by
  intro hzero
  apply eulerWickPrimitiveCompletedInteractionJet_ne_zero s
  funext n
  have hn := congrArg (fun v : lp (fun _ : ℕ => ℂ) 2 => v n) hzero
  simp only [eulerWickPrimitiveCompletedInteractionFockVector_apply,
    eulerWickPrimitiveCompletedInteractionFockCoord] at hn
  have hfac : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
  exact (div_eq_zero_iff.mp hn).resolve_right hfac

def eulerWickPrimitiveCompletedInteractionFockPhase (n : ℕ) : ℂ :=
  quadraticCharacterTwelve.rootNumber * (-1 : ℂ) ^ n

theorem norm_eulerWickPrimitiveCompletedInteractionFockPhase (n : ℕ) :
    ‖eulerWickPrimitiveCompletedInteractionFockPhase n‖ = 1 := by
  rcases quadraticCharacterTwelve_rootNumber_eq_one_or_neg_one with h | h
  · simp [eulerWickPrimitiveCompletedInteractionFockPhase, h]
  · simp [eulerWickPrimitiveCompletedInteractionFockPhase, h]

/-- Root-number/parity reflection is a unitary on the factorial-Fock jet space. -/
def eulerWickPrimitiveCompletedInteractionFockReflectionUnitary :
    lp (fun _ : ℕ => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  lpPhaseUnitary eulerWickPrimitiveCompletedInteractionFockPhase
    norm_eulerWickPrimitiveCompletedInteractionFockPhase

theorem eulerWickPrimitiveCompletedInteractionFockVector_one_sub (s : ℂ) :
    eulerWickPrimitiveCompletedInteractionFockVector (1 - s) =
      eulerWickPrimitiveCompletedInteractionFockReflectionUnitary
        (eulerWickPrimitiveCompletedInteractionFockVector s) := by
  refine lp.ext (funext fun n => ?_)
  simp only [eulerWickPrimitiveCompletedInteractionFockVector_apply,
    eulerWickPrimitiveCompletedInteractionFockCoord,
    eulerWickPrimitiveCompletedInteractionFockReflectionUnitary,
    lpPhaseUnitary_apply, eulerWickPrimitiveCompletedInteractionFockPhase]
  rw [eulerWickPrimitiveCompletedInteraction_iteratedDeriv_one_sub]
  ring

/-- The natural factorial-Fock norm is reflection-blind at every complex point. -/
theorem norm_eulerWickPrimitiveCompletedInteractionFockVector_one_sub (s : ℂ) :
    ‖eulerWickPrimitiveCompletedInteractionFockVector (1 - s)‖ =
      ‖eulerWickPrimitiveCompletedInteractionFockVector s‖ := by
  rw [eulerWickPrimitiveCompletedInteractionFockVector_one_sub]
  exact LinearIsometryEquiv.norm_map _ _

/-- Schwarz reflection is coordinatewise conjugation on the factorial-Fock jet. -/
theorem eulerWickPrimitiveCompletedInteractionFockCoord_conj
    (s : ℂ) (n : ℕ) :
    eulerWickPrimitiveCompletedInteractionFockCoord ((starRingEnd ℂ) s) n =
      (starRingEnd ℂ) (eulerWickPrimitiveCompletedInteractionFockCoord s n) := by
  rw [eulerWickPrimitiveCompletedInteractionFockCoord,
    eulerWickPrimitiveCompletedInteractionFockCoord,
    eulerWickPrimitiveCompletedInteraction_iteratedDeriv_conj]
  simp

/-- Schwarz conjugation preserves the factorial-Fock mass. -/
theorem norm_eulerWickPrimitiveCompletedInteractionFockVector_conj (s : ℂ) :
    ‖eulerWickPrimitiveCompletedInteractionFockVector ((starRingEnd ℂ) s)‖ =
      ‖eulerWickPrimitiveCompletedInteractionFockVector s‖ := by
  have hsq :
      ‖eulerWickPrimitiveCompletedInteractionFockVector ((starRingEnd ℂ) s)‖ ^ 2 =
        ‖eulerWickPrimitiveCompletedInteractionFockVector s‖ ^ 2 := by
    rw [lp_two_norm_sq_eq_tsum, lp_two_norm_sq_eq_tsum]
    apply tsum_congr
    intro n
    rw [eulerWickPrimitiveCompletedInteractionFockVector_apply,
      eulerWickPrimitiveCompletedInteractionFockVector_apply,
      eulerWickPrimitiveCompletedInteractionFockCoord_conj, RCLike.norm_conj]
  nlinarith [norm_nonneg
    (eulerWickPrimitiveCompletedInteractionFockVector ((starRingEnd ℂ) s)),
    norm_nonneg (eulerWickPrimitiveCompletedInteractionFockVector s)]

end

end GaloisForLFunctions.RHTower
