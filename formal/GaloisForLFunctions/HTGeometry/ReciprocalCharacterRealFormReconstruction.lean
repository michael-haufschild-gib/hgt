import GaloisForLFunctions.HTGeometry.ReciprocalCharacterRealFormMechanics
import GaloisForLFunctions.HTGeometry.PrimeBooleanMassHankelQuantumFusion

/-!
# Reciprocal-character real-form reconstruction

The even reciprocal-character packet has positive Prony data

`x_i = lambda_i^2`, `b_i = a_i * lambda_i^2`.

This module certifies the reconstruction part of the real-form fusion law: the first `2r`
moments determine the unordered squared-clock spectrum and every later moment; once clock labels
are fixed, the first `r` moments determine all positive source weights.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Positive node underlying the even reciprocal-character jet packet. -/
def reciprocalMomentNode {r : ℕ} (lambda : Fin r → ℝ) (i : Fin r) : ℝ :=
  lambda i ^ 2

/-- Positive weight underlying the even reciprocal-character jet packet. -/
def reciprocalMomentWeight {r : ℕ} (a lambda : Fin r → ℝ) (i : Fin r) : ℝ :=
  a i * lambda i ^ 2

/-- Moment packet reconstructed from even split-real jets. -/
def reciprocalCharacterMoment {r : ℕ} (a lambda : Fin r → ℝ) (n : ℕ) : ℂ :=
  _root_.HTGeometry.realClockMoment (reciprocalMomentNode lambda)
    (reciprocalMomentWeight a lambda) n

theorem reciprocalMomentNode_injective {r : ℕ} {lambda : Fin r → ℝ}
    (hlambda : ∀ i, 0 < lambda i) (hinj : Function.Injective lambda) :
    Function.Injective (reciprocalMomentNode lambda) := by
  intro i j hij
  apply hinj
  simp only [reciprocalMomentNode] at hij
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hij with h | h
  · exact h
  · nlinarith [hlambda i, hlambda j]

theorem reciprocalMomentWeight_pos {r : ℕ} {a lambda : Fin r → ℝ}
    (ha : ∀ i, 0 < a i) (hlambda : ∀ i, 0 < lambda i) (i : Fin r) :
    0 < reciprocalMomentWeight a lambda i := by
  rw [reciprocalMomentWeight]
  exact mul_pos (ha i) (pow_pos (hlambda i) 2)

/-- First `2r` reciprocal moments determine the unordered squared-clock spectrum. -/
theorem reciprocalSpectrumPoly_eq_of_moments_eq {r : ℕ}
    (a a' lambda lambda' : Fin r → ℝ)
    (ha : ∀ i, 0 < a i) (hlambda : ∀ i, 0 < lambda i)
    (hinj : Function.Injective lambda)
    (h : ∀ n, n < 2 * r →
      reciprocalCharacterMoment a lambda n = reciprocalCharacterMoment a' lambda' n) :
    spectrumPoly (fun i => (reciprocalMomentNode lambda i : ℂ)) =
      spectrumPoly (fun i => (reciprocalMomentNode lambda' i : ℂ)) := by
  apply _root_.HTGeometry.realClockSpectrumPoly_eq_of_moments_eq
    (reciprocalMomentNode lambda) (reciprocalMomentNode lambda')
    (reciprocalMomentWeight a lambda) (reciprocalMomentWeight a' lambda')
  · exact reciprocalMomentNode_injective hlambda hinj
  · exact reciprocalMomentWeight_pos ha hlambda
  · exact h

/-- First `2r` reciprocal moments determine every later moment. -/
theorem reciprocalCharacterMoment_eq_of_eq_below {r : ℕ}
    (a a' lambda lambda' : Fin r → ℝ)
    (ha : ∀ i, 0 < a i) (hlambda : ∀ i, 0 < lambda i)
    (hinj : Function.Injective lambda)
    (h : ∀ n, n < 2 * r →
      reciprocalCharacterMoment a lambda n = reciprocalCharacterMoment a' lambda' n)
    (n : ℕ) :
    reciprocalCharacterMoment a lambda n = reciprocalCharacterMoment a' lambda' n := by
  exact processMoment_eq_of_eq_below
    (fun i => (reciprocalMomentNode lambda i : ℂ))
    (fun i => (reciprocalMomentNode lambda' i : ℂ))
    (reciprocalMomentWeight a lambda) (reciprocalMomentWeight a' lambda')
    (Complex.ofReal_injective.comp (reciprocalMomentNode_injective hlambda hinj))
    (reciprocalMomentWeight_pos ha hlambda) h n

/-- With fixed positive distinct clocks, the first `r` moments determine every source weight. -/
theorem reciprocalWeights_eq_of_moments_eq {r : ℕ}
    (a a' lambda : Fin r → ℝ)
    (hlambda : ∀ i, 0 < lambda i) (hinj : Function.Injective lambda)
    (h : ∀ n, n < r →
      reciprocalCharacterMoment a lambda n = reciprocalCharacterMoment a' lambda n) :
    a = a' := by
  have hb : reciprocalMomentWeight a lambda = reciprocalMomentWeight a' lambda := by
    apply _root_.HTGeometry.realClockWeights_eq_of_moments_eq
      (reciprocalMomentNode lambda)
      (reciprocalMomentWeight a lambda) (reciprocalMomentWeight a' lambda)
    · exact reciprocalMomentNode_injective hlambda hinj
    · exact h
  funext i
  have hi := congrFun hb i
  rw [reciprocalMomentWeight, reciprocalMomentWeight] at hi
  exact mul_right_cancel₀ (pow_pos (hlambda i) 2).ne' hi

/-! ## Prime-clock compact execution -/

/-- The same marked prime clocks admit arbitrarily late compact-phase returns.  The unbounded
lower bound `T` records openness of the lifted clock history while observed phases recur. -/
theorem reciprocalPrimeCharacter_exists_large_phase_return (F : Finset Nat.Primes) {ε T : ℝ}
    (hε : 0 < ε) (hT : 0 < T) :
    ∃ t : ℝ, T ≤ t ∧ ∀ p : F,
      ‖_root_.HTGeometry.ConstraintFrameRelativity.shellFlow 1 t p - 1‖ < ε :=
  _root_.HTGeometry.primeBooleanFusion_exists_large_return F hε hT

end

end GaloisForLFunctions.HTGeometry
