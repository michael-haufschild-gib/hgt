import GaloisForLFunctions.KodairaParshinAbc.DegreeZeroClassesHaveVanishingTateHeight
import GaloisForLFunctions.KodairaParshinAbc.TheFreyLocalFactorTricklesDown
import GaloisForLFunctions.KodairaParshinAbc.TheQuinticCurveCalibratesTheEffectivityCalculus
import GaloisForLFunctions.ArithmeticEffectivityTheory.NaiveHeightsAreTraces

/-!
# Rosati degrees of degree zero

On a curve datum `D` the integral Rosati form `P ↦ Tr(P(F) P(F)′)` on `ℤ[F]`
(`ArithmeticEffectivityTheory.intRosatiDeg`) is homogeneous of degree two, and it is nonnegative
exactly when the datum is unitary.  The height principles for classes on a curve give:

* **negative degree** — a Rosati form bounded above is `≤ 0`; for a unitary datum it then
  vanishes identically (`intRosatiDeg_eq_zero_of_unitary_of_bounded_above`), which applies to the
  Frey data at good primes and to the data of the quintic curve `y² + y = x⁵`;
* **degree zero** — if `|q_D - c q_{D'}| ≤ ε q_{D'} + B_ε` for every `ε > 0`, then `q_D = c q_{D'}`
  (`intRosatiDeg_eq_smul_of_degree_zero`).
-/

noncomputable section

open Polynomial

namespace GaloisForLFunctions.KodairaParshinAbc

open ArithmeticEffectivityTheory ArithmeticCastelnuovoSeveri

variable {ι ι' : Type*} [Fintype ι] [Fintype ι']

theorem intRosatiDeg_two_nsmul (D : CurveDatum ι) (P : ℤ[X]) :
    intRosatiDeg D (2 • P) = 4 * intRosatiDeg D P := by
  rw [intRosatiDeg_nsmul]
  norm_num

/-- **Negative degree**: a Rosati form bounded above is nonpositive. -/
theorem intRosatiDeg_nonpos_of_bounded_above (D : CurveDatum ι) {B : ℝ}
    (hB : ∀ P : ℤ[X], intRosatiDeg D P ≤ B) (P : ℤ[X]) : intRosatiDeg D P ≤ 0 :=
  nonpos_of_two_nsmul_of_bounded_above (q := intRosatiDeg D) (intRosatiDeg_two_nsmul D) hB P

/-- For a unitary datum a Rosati form bounded above vanishes identically. -/
theorem intRosatiDeg_eq_zero_of_unitary_of_bounded_above (D : CurveDatum ι)
    (hU : ∀ i, ‖D.β i‖ = 1) {B : ℝ} (hB : ∀ P : ℤ[X], intRosatiDeg D P ≤ B) (P : ℤ[X]) :
    intRosatiDeg D P = 0 :=
  le_antisymm (intRosatiDeg_nonpos_of_bounded_above D hB P)
    ((intRosatiDeg_nonneg_iff_unitary D).mpr hU P)

/-- **Degree zero**: Rosati forms whose difference has degree zero are proportional. -/
theorem intRosatiDeg_eq_smul_of_degree_zero (D : CurveDatum ι) (D' : CurveDatum ι') (c : ℝ)
    (hcor : ∀ ε > 0, ∃ B, ∀ P : ℤ[X],
      |intRosatiDeg D P - c * intRosatiDeg D' P| ≤ ε * intRosatiDeg D' P + B) (P : ℤ[X]) :
    intRosatiDeg D P = c * intRosatiDeg D' P := by
  have h := eq_zero_of_two_nsmul_of_degree_zero
    (q := fun Q => intRosatiDeg D Q - c * intRosatiDeg D' Q) (qM := intRosatiDeg D')
    (fun Q => by simp only [intRosatiDeg_two_nsmul]; ring) (intRosatiDeg_two_nsmul D') hcor P
  linarith

/-- The Rosati form of a Frey datum at a good prime is never bounded above unless it vanishes. -/
theorem freyDatum_intRosatiDeg_eq_zero_of_bounded_above {p : ℕ} [Fact p.Prime] {a b : ℤ}
    (hp2 : p ≠ 2) (habc : ¬ (p : ℤ) ∣ a * b * (a + b)) {B : ℝ}
    (hB : ∀ P : ℤ[X], intRosatiDeg (freyDatum hp2 habc) P ≤ B) (P : ℤ[X]) :
    intRosatiDeg (freyDatum hp2 habc) P = 0 :=
  intRosatiDeg_eq_zero_of_unitary_of_bounded_above _
    (ArithmeticLorentzianGeometry.ramanujanDatum_unitary _ _) hB P

/-- The Rosati form of the quintic curve `y² + y = x⁵` is never bounded above unless it
vanishes. -/
theorem quinticDatum_intRosatiDeg_eq_zero_of_bounded_above {F : Type*} [Field F] [Fintype F]
    (h2 : ringChar F ≠ 2) (h5 : (5 : F) ≠ 0) {B : ℝ}
    (hB : ∀ P : ℤ[X], intRosatiDeg (quinticDatum h2 h5) P ≤ B) (P : ℤ[X]) :
    intRosatiDeg (quinticDatum h2 h5) P = 0 :=
  intRosatiDeg_eq_zero_of_unitary_of_bounded_above _ (quinticDatum_unitary h2 h5) hB P

end GaloisForLFunctions.KodairaParshinAbc
