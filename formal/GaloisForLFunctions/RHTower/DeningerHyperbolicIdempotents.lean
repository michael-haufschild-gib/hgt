import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.Invertible.Basic

/-!
# The rank and signature idempotents of an involutive orientation class

Once `2` is invertible, an element `ε` with `ε² = 1` splits the ring into a rank part and a
signature part: `e₊ = (1 + ε)/2` and `e₋ = (1 - ε)/2` are orthogonal idempotents summing to one,
`ε` acts as `+1` on the first and `-1` on the second, and the hyperbolic class is `h = 2 e₊`.

Inverting `h` therefore keeps the rank summand and kills the signature summand, which is why
hyperbolic localization is the rank channel rather than a choice between two characters.

* `deningerRankIdem`, `deningerSignIdem` are the two idempotents.
* `deningerHyperbolic_eq_two_mul_rankIdem` is `h = 2 e₊`.
* `deningerSignIdem_mul_hyperbolic` is `e₋ h = 0`, the reason localizing at `h` annihilates the
  signature summand.
-/

namespace RHTower

section HyperbolicIdempotents

variable {A : Type*} [CommRing A] [Invertible (2 : A)] {ε : A}

/-- The rank idempotent `(1 + ε)/2`. -/
def deningerRankIdem (ε : A) : A := ⅟(2 : A) * (1 + ε)

/-- The signature idempotent `(1 - ε)/2`. -/
def deningerSignIdem (ε : A) : A := ⅟(2 : A) * (1 - ε)

theorem deningerRankIdem_add_signIdem (ε : A) :
    deningerRankIdem ε + deningerSignIdem ε = 1 := by
  rw [deningerRankIdem, deningerSignIdem, ← mul_add]
  have h : (1 + ε) + (1 - ε) = 2 * 1 := by ring
  rw [h, ← mul_assoc, invOf_mul_self, one_mul]

theorem deningerRankIdem_sq (hε : ε ^ (2 : ℕ) = 1) :
    deningerRankIdem ε * deningerRankIdem ε = deningerRankIdem ε := by
  rw [deningerRankIdem]
  have hexp : (1 + ε) * (1 + ε) = 2 * (1 + ε) + (ε ^ (2 : ℕ) - 1) := by ring
  calc ⅟(2 : A) * (1 + ε) * (⅟(2 : A) * (1 + ε))
      = ⅟(2 : A) * (⅟(2 : A) * ((1 + ε) * (1 + ε))) := by ring
    _ = ⅟(2 : A) * (⅟(2 : A) * (2 * (1 + ε))) := by rw [hexp, hε]; ring
    _ = ⅟(2 : A) * (1 + ε) := by
        rw [← mul_assoc ⅟(2 : A) 2 (1 + ε), invOf_mul_self, one_mul]

theorem deningerSignIdem_sq (hε : ε ^ (2 : ℕ) = 1) :
    deningerSignIdem ε * deningerSignIdem ε = deningerSignIdem ε := by
  rw [deningerSignIdem]
  have hexp : (1 - ε) * (1 - ε) = 2 * (1 - ε) + (ε ^ (2 : ℕ) - 1) := by ring
  calc ⅟(2 : A) * (1 - ε) * (⅟(2 : A) * (1 - ε))
      = ⅟(2 : A) * (⅟(2 : A) * ((1 - ε) * (1 - ε))) := by ring
    _ = ⅟(2 : A) * (⅟(2 : A) * (2 * (1 - ε))) := by rw [hexp, hε]; ring
    _ = ⅟(2 : A) * (1 - ε) := by
        rw [← mul_assoc ⅟(2 : A) 2 (1 - ε), invOf_mul_self, one_mul]

/-- The two idempotents are orthogonal. -/
theorem deningerRankIdem_mul_signIdem (hε : ε ^ (2 : ℕ) = 1) :
    deningerRankIdem ε * deningerSignIdem ε = 0 := by
  rw [deningerRankIdem, deningerSignIdem]
  have hexp : (1 + ε) * (1 - ε) = 1 - ε ^ (2 : ℕ) := by ring
  calc ⅟(2 : A) * (1 + ε) * (⅟(2 : A) * (1 - ε))
      = ⅟(2 : A) * (⅟(2 : A) * ((1 + ε) * (1 - ε))) := by ring
    _ = 0 := by rw [hexp, hε]; ring

/-- The orientation class acts as `+1` on the rank summand. -/
theorem deningerEpsilon_mul_rankIdem (hε : ε ^ (2 : ℕ) = 1) :
    ε * deningerRankIdem ε = deningerRankIdem ε := by
  rw [deningerRankIdem]
  have hexp : ε * (1 + ε) = (1 + ε) + (ε ^ (2 : ℕ) - 1) := by ring
  calc ε * (⅟(2 : A) * (1 + ε)) = ⅟(2 : A) * (ε * (1 + ε)) := by ring
    _ = ⅟(2 : A) * (1 + ε) := by rw [hexp, hε]; ring

/-- The orientation class acts as `-1` on the signature summand. -/
theorem deningerEpsilon_mul_signIdem (hε : ε ^ (2 : ℕ) = 1) :
    ε * deningerSignIdem ε = -deningerSignIdem ε := by
  rw [deningerSignIdem]
  have hexp : ε * (1 - ε) = -(1 - ε) + (1 - ε ^ (2 : ℕ)) := by ring
  calc ε * (⅟(2 : A) * (1 - ε)) = ⅟(2 : A) * (ε * (1 - ε)) := by ring
    _ = -(⅟(2 : A) * (1 - ε)) := by rw [hexp, hε]; ring

/-- **The hyperbolic class is twice the rank idempotent.** -/
theorem deningerHyperbolic_eq_two_mul_rankIdem (ε : A) :
    1 + ε = 2 * deningerRankIdem ε := by
  rw [deningerRankIdem, ← mul_assoc, mul_invOf_self, one_mul]

/-- **The signature summand is annihilated by the hyperbolic class.**  This is why inverting `h`
kills it. -/
theorem deningerSignIdem_mul_hyperbolic (hε : ε ^ (2 : ℕ) = 1) :
    deningerSignIdem ε * (1 + ε) = 0 := by
  rw [deningerSignIdem]
  have hexp : (1 - ε) * (1 + ε) = 1 - ε ^ (2 : ℕ) := by ring
  calc ⅟(2 : A) * (1 - ε) * (1 + ε) = ⅟(2 : A) * ((1 - ε) * (1 + ε)) := by ring
    _ = 0 := by rw [hexp, hε]; ring

end HyperbolicIdempotents

end RHTower
