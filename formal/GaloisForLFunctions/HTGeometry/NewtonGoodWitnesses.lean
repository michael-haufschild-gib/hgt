import GaloisForLFunctions.HTGeometry.NewtonFibreLift

/-!
# The Newton iteration has a starting point

A Newton datum is good when its two correction polynomials have bounded degree and ideal
coefficients and the residual absorbs the inversion error to the required order.  The zero
correction is good exactly when the uncorrected pair already inverts to that order, which is the
Hensel starting congruence; and the unit pair satisfies it outright.

So the advancing step has something to advance, and the iteration is not conditional on an
unexhibited seed.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {S : Type*} [CommRing S]

/-- **The zero correction is good exactly under the starting congruence.** -/
theorem newtonGood_zero {I : Ideal S} {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A B Γ Γ' : S[X]) (k : ℕ)
    (hstart : (X : S[X]) ^ (m + n) ∣ inversionError (A + Γ) (B + Γ')) :
    NewtonGood I m n A B Γ Γ' k (0, 0, 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hm
  · simpa using hn
  · intro i; simp
  · intro i; simp
  · simpa using Nat.add_pos_left hm n
  · intro i; simp
  · simpa using hstart

/-- The unit pair starts the iteration with no correction at all. -/
theorem newtonGood_one {I : Ideal S} {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (k : ℕ) :
    NewtonGood I m n (1 : S[X]) 1 0 0 k (0, 0, 0) := by
  refine newtonGood_zero hm hn 1 1 0 0 k ?_
  rw [inversionError]
  simp

end GaloisForLFunctions.HTGeometry
