import GaloisForLFunctions.HTGeometry.ChannelInverseRigidity
import GaloisForLFunctions.HTGeometry.MarkovianReturnRecovery

/-!
# Exact Markovian recurrence is unitary and palindromic

Corollary C of the Markovian return law.  If the full channel returns exactly at time `R`, then
every intermediate channel has a channel inverse, hence is a unitary conjugation; the semigroup is
periodic with period `R`; and the radius-interlacing inequalities of Theorem B become equalities
under `t ↦ R − t`.

Genuine dissipation and exact full-channel recurrence are therefore mutually exclusive.
-/

open Matrix
open scoped Matrix ComplexOrder MatrixOrder BigOperators NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace DynamicalSemigroup

variable (S : DynamicalSemigroup n)

/-- A vanishing return defect is an exact return. -/
theorem ch_eq_one_of_dist_eq_zero {R : ℝ≥0} (h : dist (S.ch R) 1 = 0) : S.ch R = 1 :=
  dist_eq_zero.mp h

/-- **Exact return makes every intermediate channel invertible.** -/
theorem inverse_of_exact_return {t R : ℝ≥0} (h : t ≤ R) (hzero : dist (S.ch R) 1 = 0) :
    (∀ X, (S.ch (R - t)).map ((S.ch t).map X) = X)
      ∧ (∀ X, (S.ch t).map ((S.ch (R - t)).map X) = X) := by
  have hR : S.ch R = 1 := S.ch_eq_one_of_dist_eq_zero hzero
  have h1 : S.ch (R - t) * S.ch t = 1 := by rw [S.recovery_left h, hR]
  have h2 : S.ch t * S.ch (R - t) = 1 := by rw [S.recovery_right h, hR]
  constructor
  · intro X
    have := congrArg (fun c : QuantumChannel n => c.map X) h1
    simpa using this
  · intro X
    have := congrArg (fun c : QuantumChannel n => c.map X) h2
    simpa using this

/-- **Corollary C.**  An exact full-channel return forces every intermediate channel of the
semigroup to be a unitary conjugation. -/
theorem exists_unitary_of_exact_return {t R : ℝ≥0} (h : t ≤ R)
    (hzero : dist (S.ch R) 1 = 0) :
    ∃ U : Matrix n n ℂ, U ∈ unitary (Matrix n n ℂ) ∧
      ∀ X, (S.ch t).map X = U * X * star U := by
  obtain ⟨h1, h2⟩ := S.inverse_of_exact_return h hzero
  exact QuantumChannel.exists_unitary_of_channel_inverse (S.ch t) (S.ch (R - t)) h1 h2

/-- **The semigroup is periodic.** -/
theorem periodic_of_exact_return {R : ℝ≥0} (hzero : dist (S.ch R) 1 = 0) (t : ℝ≥0) :
    S.ch (t + R) = S.ch t := by
  rw [S.ch_add, S.ch_eq_one_of_dist_eq_zero hzero, mul_one]

/-- **The incidence counts are exactly palindromic under an exact return.** -/
theorem card_reflect_eq {W : Type*} [Fintype W] [DecidableEq W] (D : UnitaryDictionary n W)
    {t R : ℝ≥0} (h : t ≤ R) (hzero : dist (S.ch R) 1 = 0) (ε : ℝ) :
    (Finset.univ.filter fun w : W => dist (D.word w) (S.ch t) ≤ ε).card
      = (Finset.univ.filter fun w : W => dist (D.word w) (S.ch (R - t)) ≤ ε).card := by
  have hle₁ := D.card_reflect_word (S := S.ch (R - t)) (T := S.ch t) (δ := 0) (ε := ε)
    (by rw [S.recovery_left h]; exact le_of_eq hzero)
  have hle₂ := D.card_reflect_word (S := S.ch t) (T := S.ch (R - t)) (δ := 0) (ε := ε)
    (by
      rw [S.recovery_right h]
      exact le_of_eq hzero)
  rw [add_zero] at hle₁ hle₂
  exact le_antisymm hle₁ hle₂

end DynamicalSemigroup

end

end GaloisForLFunctions.HTGeometry
