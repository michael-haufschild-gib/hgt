import GaloisForLFunctions.HTGeometry.HolderDifferenceBricks

/-!
# A rational function with constant unit-shift defect is affine

Subtracting the linear function with the same defect turns a constant shift defect into shift
periodicity, and a shift-periodic rational function is constant.  Hence the only rational solutions
of `R(z+1) = R(z) + c` are `R(z) = cz + d`.

This is the parabolic half of the translation-stabilizer argument: a translation of an affine
observation curve which is realized by a Möbius reparametrization of its normalization forces the
curve to be a line.

* `GaloisForLFunctions.HTGeometry.shift_const_quotient_affine`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- **A rational function whose unit shift changes it by a constant is affine.**  In terms of a
coprime representation `p/q`, the shift relation `p(X+1)·q = (p + c·q)·q(X+1)` forces the
denominator to be a nonzero constant `b` and the numerator to be `c·b·X + a`. -/
theorem shift_const_quotient_affine {p q : ℂ[X]} {c : ℂ} (hq : q ≠ 0)
    (hco : IsCoprime p q)
    (h : p.comp (X + C 1) * q = (p + C c * q) * q.comp (X + C 1)) :
    ∃ a b : ℂ, b ≠ 0 ∧ q = C b ∧ p = C (c * b) * X + C a := by
  set P : ℂ[X] := p - C c * X * q with hP
  have hcoP : IsCoprime P q := by
    have hstep : IsCoprime (p + q * (-(C c * X))) q := hco.add_mul_left_left _
    have hrw : p + q * (-(C c * X)) = P := by
      rw [hP]; ring
    rwa [hrw] at hstep
  have hcomp : P.comp (X + C 1)
      = p.comp (X + C 1) - C c * (X + C 1) * q.comp (X + C 1) := by
    rw [hP, sub_comp, mul_comp, mul_comp, C_comp, X_comp]
  have hshift : P.comp (X + C 1) * q = P * q.comp (X + C 1) := by
    rw [hcomp, sub_mul, h, hP]
    simp only [map_one]
    ring
  obtain ⟨a, b, hPa, hqb⟩ := shift_periodic_quotient_constant hcoP hshift
  have hb : b ≠ 0 := by
    intro hb0
    exact hq (by rw [hqb, hb0, map_zero])
  refine ⟨a, b, hb, hqb, ?_⟩
  have hpe : p = P + C c * X * q := by rw [hP]; ring
  rw [hpe, hPa, hqb, map_mul]
  ring

end GaloisForLFunctions.HTGeometry
