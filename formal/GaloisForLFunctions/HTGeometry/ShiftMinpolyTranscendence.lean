import GaloisForLFunctions.HTGeometry.ShiftDefectDescent
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Tactic

/-!
# Transcendence from an unattainable shift defect

Let `K` carry an automorphism `sigma`, let `E` be a subfield preserved by `sigma`, and let `y` be an
element of `K` with

`sigma y = y + c`,   `c` in `E`.

If `y` were algebraic over `E`, its minimal polynomial would be fixed by the twist
`shiftTwist sigmaE c`, because the twist sends annihilators of `y` to annihilators of `y` and
preserves monicity and degree.  A twist-fixed monic polynomial of degree `e` forces the
`sigma`-defect `-(e * c)` to be realised inside `E`.  Hence a base field in which `c` has no such
defect cannot have `y` algebraic over it.

Together with `descentStep`, which propagates the defect hypothesis through a simple transcendental
extension, this is the engine of a Hölder-style descent: the step lifts the hypothesis up a tower of
jets, and this file converts the hypothesis at each level into transcendence of the next jet.
-/

open Polynomial

namespace HTGeometry

variable {Cst E K : Type*} [Field Cst] [Field E] [Field K] [Algebra Cst E] [Algebra E K]

variable {sigma : K ≃+* K} {sigmaE : E ≃+* E} {y : K} {c : E}

/-- The twist sends annihilating polynomials of `y` to annihilating polynomials of `y`. -/
theorem shiftTwist_aeval_eq_zero
    (hcompat : ∀ a : E, sigma (algebraMap E K a) = algebraMap E K (sigmaE a))
    (hsy : sigma y = y + algebraMap E K c) {P : E[X]} (hP : aeval y P = 0) :
    aeval y (shiftTwist sigmaE c P) = 0 := by
  rw [← sigma_aeval_eq (sigma := sigma) hcompat hsy P, hP, map_zero]

/-- **The minimal polynomial is twist-fixed.** -/
theorem shiftTwist_minpoly
    (hcompat : ∀ a : E, sigma (algebraMap E K a) = algebraMap E K (sigmaE a))
    (hsy : sigma y = y + algebraMap E K c) (halg : IsAlgebraic E y) :
    shiftTwist sigmaE c (minpoly E y) = minpoly E y := by
  have hint : IsIntegral E y := halg.isIntegral
  have hmon : (minpoly E y).Monic := minpoly.monic hint
  have hann : aeval y (minpoly E y) = 0 := minpoly.aeval E y
  have htw : aeval y (shiftTwist sigmaE c (minpoly E y)) = 0 :=
    shiftTwist_aeval_eq_zero (sigma := sigma) hcompat hsy hann
  have hdvd : minpoly E y ∣ shiftTwist sigmaE c (minpoly E y) := minpoly.dvd E y htw
  obtain ⟨Q, hQ⟩ := hdvd
  have htwm : (shiftTwist sigmaE c (minpoly E y)).Monic := shiftTwist_monic hmon
  have hQne : Q ≠ 0 := by
    intro h
    rw [h, mul_zero] at hQ
    exact htwm.ne_zero hQ
  have hdeg : (shiftTwist sigmaE c (minpoly E y)).natDegree = (minpoly E y).natDegree :=
    shiftTwist_natDegree _ _ _
  have hQdeg : Q.natDegree = 0 := by
    rw [hQ, Polynomial.natDegree_mul hmon.ne_zero hQne] at hdeg
    omega
  have hQC : Q = Polynomial.C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hQdeg
  have hlead : Q.coeff 0 = 1 := by
    have h1 : (shiftTwist sigmaE c (minpoly E y)).leadingCoeff = 1 := htwm
    rw [hQ, Polynomial.leadingCoeff_mul, hmon.leadingCoeff, one_mul,
      Polynomial.leadingCoeff, hQdeg] at h1
    exact h1
  rw [hQ, hQC, hlead, Polynomial.C_1, mul_one]

/-- **Transcendence from an unattainable defect.**  If no element of `E` has `sigma`-defect equal to
a nonzero constant multiple of `c` — expressed by the admissible span `T` collapsing into `W` while
`c` avoids `W` — then `y` is transcendental over `E`. -/
theorem transcendental_of_defect_unattainable [CharZero Cst]
    (hcompat : ∀ a : E, sigma (algebraMap E K a) = algebraMap E K (sigmaE a))
    (hsy : sigma y = y + algebraMap E K c)
    {T W : Submodule Cst E}
    (hdefect : ∀ u : E, ∀ v ∈ T, sigmaE u - u = v → v ∈ W)
    (hcT : c ∈ T) (hcW : c ∉ W) :
    Transcendental E y := by
  intro halg
  have hmon : (minpoly E y).Monic := minpoly.monic halg.isIntegral
  have hfix : shiftTwist sigmaE c (minpoly E y) = minpoly E y :=
    shiftTwist_minpoly (sigma := sigma) hcompat hsy halg
  have hpos : 0 < (minpoly E y).natDegree := minpoly.natDegree_pos halg.isIntegral
  have hcoeff := defect_coeff_of_shiftTwist_eq hmon hfix rfl hpos
  set e : ℕ := (minpoly E y).natDegree with he
  have hcast : (e : E) * c = algebraMap Cst E (e : Cst) * c := by rw [map_natCast]
  have hmemT : -((e : E) * c) ∈ T := by
    rw [hcast]
    exact T.neg_mem (by simpa [Algebra.smul_def] using T.smul_mem ((e : Cst)) hcT)
  have hmemW := hdefect _ _ hmemT hcoeff
  have hmemW' : algebraMap Cst E (e : Cst) * c ∈ W := by
    have h := W.neg_mem hmemW
    rw [hcast] at h
    simpa using h
  refine hcW ?_
  have heC : (e : Cst) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hc : c = ((e : Cst))⁻¹ • (algebraMap Cst E (e : Cst) * c) := by
    rw [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ heC, map_one, one_mul]
  rw [hc]
  exact W.smul_mem _ hmemW'

end HTGeometry
