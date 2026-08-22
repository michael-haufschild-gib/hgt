import GaloisForLFunctions.HTGeometry.Octonion.Basic

namespace GaloisForLFunctions.HTGeometry.Octonion.RealOctonion

noncomputable section

/-- Pointwise left multiplication. -/
def leftAction (q x : RealOctonion) : RealOctonion := q * x

/-- Pointwise right multiplication. -/
def rightAction (s x : RealOctonion) : RealOctonion := x * s

/-- The pointwise commutator `[L_q, R_s]`. -/
def leftRightCommutator (q s x : RealOctonion) : RealOctonion :=
  leftAction q (rightAction s x) - rightAction s (leftAction q x)

/-- The real-coefficient quadratic `Q_s(q)` of arXiv:2605.07183. -/
def quadratic (s q : RealOctonion) : RealOctonion :=
  q * q - scalarEmbed (2 * s.1.re) * q + scalarEmbed (normSq s)

/-- Lemma 8.4 of arXiv:2605.07183, evaluated at an arbitrary octonion.

This is the corrected Riesz--Dunford resolvent factorization in the real division octonions. -/
theorem quadratic_leftAction_eq_resolvent_factorization (s q x : RealOctonion) :
    rightAction s (rightAction (star s) x - leftAction q x)
        - leftAction q (rightAction (star s) x - leftAction q x)
        + leftRightCommutator q (star s) x =
      leftAction (quadratic s q) x := by
  have hnorm : (x * star s) * s = x * scalarEmbed (normSq s) := by
    rw [mul_star_associates, star_mul_self_eq_scalarEmbed]
  have hsq : q * (q * x) = (q * q) * x :=
    IsAlternative.mul_alternative_left q x
  have htrace : (q * x) * (s + star s) =
      (scalarEmbed (2 * s.1.re) * q) * x := by
    rw [add_star_eq_scalarEmbed]
    calc
      (q * x) * scalarEmbed (2 * s.1.re) = (2 * s.1.re) • (q * x) :=
        mul_scalarEmbed _ _
      _ = scalarEmbed (2 * s.1.re) * (q * x) :=
        (scalarEmbed_mul _ _).symm
      _ = (scalarEmbed (2 * s.1.re) * q) * x :=
        (scalarEmbed_associates _ _ _).symm
  simp only [leftAction, rightAction, leftRightCommutator, quadratic, mul_sub, sub_mul]
  calc
    (x * star s) * s - (q * x) * s - (q * (x * star s) - q * (q * x)) +
        (q * (x * star s) - (q * x) * star s) =
      (x * star s) * s + q * (q * x) - (q * x) * (s + star s) := by
        noncomm_ring
    _ = x * scalarEmbed (normSq s) + (q * q) * x -
        (scalarEmbed (2 * s.1.re) * q) * x := by rw [hnorm, hsq, htrace]
    _ = (q * q - scalarEmbed (2 * s.1.re) * q + scalarEmbed (normSq s)) * x := by
      rw [add_mul, sub_mul]
      have hnorm_comm : x * scalarEmbed (normSq s) = scalarEmbed (normSq s) * x := by
        rw [mul_scalarEmbed, scalarEmbed_mul]
      rw [hnorm_comm]
      abel

/-- Operator form of Lemma 8.4 of arXiv:2605.07183. -/
theorem quadratic_leftAction_eq_resolvent_factorization_operator (s q : RealOctonion) :
    leftAction (quadratic s q) = fun x =>
      rightAction s (rightAction (star s) x - leftAction q x)
        - leftAction q (rightAction (star s) x - leftAction q x)
        + leftRightCommutator q (star s) x := by
  funext x
  exact (quadratic_leftAction_eq_resolvent_factorization s q x).symm

end
end GaloisForLFunctions.HTGeometry.Octonion.RealOctonion
