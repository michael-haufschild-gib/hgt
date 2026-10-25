import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WittIntegralityIsNotPurity
import GaloisForLFunctions.HTGeometry.PowerSeriesAbsoluteEvaluation
import Mathlib.Algebra.Polynomial.Div

/-!
# Extracting one geometric pole without separating the remaining poles

Subtract the primary geometric term by evaluating its numerator at the
reciprocal root. Polynomial division removes that factor exactly. The
remaining double pole at one and secondary geometric factor may coincide;
their product is still absolutely summable inside both convergence disks.
-/

noncomputable section
open PowerSeries
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The denominator retained after removing the primary geometric pole. -/
def secondaryPolePolynomial (b : ℂ) : Polynomial ℂ :=
  (1 - Polynomial.X) ^ 2 * (1 - Polynomial.C b * Polynomial.X)

/-- The coefficient of the primary geometric term. -/
def primaryPoleCoefficient (P : Polynomial ℂ) (a b : ℂ) : ℂ :=
  P.eval a⁻¹ / (secondaryPolePolynomial b).eval a⁻¹

/-- The polynomial quotient after subtracting the primary residue. -/
def geometricPoleRemainderPolynomial (P : Polynomial ℂ) (a b : ℂ) : Polynomial ℂ :=
  Polynomial.C (-a⁻¹) *
    ((P - Polynomial.C (primaryPoleCoefficient P a b) * secondaryPolePolynomial b) /ₘ
      (Polynomial.X - Polynomial.C a⁻¹))

theorem secondaryPolePolynomial_eval (b u : ℂ) :
    (secondaryPolePolynomial b).eval u = (1 - u) ^ 2 * (1 - b * u) := by
  simp only [secondaryPolePolynomial, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_C]

private theorem secondaryPolePolynomial_eval_ne_zero {a b : ℂ}
    (ha : a ≠ 0) (ha1 : a ≠ 1) (hab : a ≠ b) :
    (secondaryPolePolynomial b).eval a⁻¹ ≠ 0 := by
  rw [secondaryPolePolynomial_eval]
  apply mul_ne_zero
  · apply pow_ne_zero
    intro h
    have hi : a⁻¹ = 1 := (sub_eq_zero.mp h).symm
    apply ha1
    calc
      a = (a⁻¹)⁻¹ := (inv_inv a).symm
      _ = 1 := by rw [hi, inv_one]
  · intro h
    have hi : b * a⁻¹ = 1 := (sub_eq_zero.mp h).symm
    apply hab
    symm
    calc
      b = (b * a⁻¹) * a := by rw [mul_assoc, inv_mul_cancel₀ ha, mul_one]
      _ = a := by rw [hi, one_mul]

/-- Subtracting the reciprocal evaluation makes the numerator divisible by the primary factor. -/
theorem geometricPoleRemainderPolynomial_factorization (P : Polynomial ℂ) {a b : ℂ}
    (ha : a ≠ 0) (ha1 : a ≠ 1) (hab : a ≠ b) :
    (1 - Polynomial.C a * Polynomial.X) * geometricPoleRemainderPolynomial P a b =
      P - Polynomial.C (primaryPoleCoefficient P a b) * secondaryPolePolynomial b := by
  let F := P - Polynomial.C (primaryPoleCoefficient P a b) * secondaryPolePolynomial b
  have hF : F.IsRoot a⁻¹ := by
    change F.eval a⁻¹ = 0
    dsimp only [F]
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      primaryPoleCoefficient, div_mul_cancel₀ _ (secondaryPolePolynomial_eval_ne_zero ha ha1 hab),
      sub_self]
  have hlin : (1 - Polynomial.C a * Polynomial.X) * Polynomial.C (-a⁻¹) =
      Polynomial.X - Polynomial.C a⁻¹ := by
    calc
      _ = Polynomial.C (a * a⁻¹) * Polynomial.X - Polynomial.C a⁻¹ := by
        simp only [map_mul, map_neg]
        ring
      _ = _ := by rw [mul_inv_cancel₀ ha, map_one, one_mul]
  rw [geometricPoleRemainderPolynomial, ← mul_assoc, hlin]
  exact Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hF

private theorem secondaryPolePolynomial_natDegree_le (b : ℂ) :
    (secondaryPolePolynomial b).natDegree ≤ 3 := by
  have hlin (c : ℂ) : (1 - Polynomial.C c * Polynomial.X : Polynomial ℂ).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · simp
    · exact (Polynomial.natDegree_C_mul_le c Polynomial.X).trans (by simp)
  have hone : (1 - Polynomial.X : Polynomial ℂ).natDegree ≤ 1 := by
    simpa only [map_one, one_mul] using hlin 1
  have hsq : ((1 - Polynomial.X : Polynomial ℂ) ^ 2).natDegree ≤ 2 := by
    exact Polynomial.natDegree_pow_le.trans (by omega)
  exact Polynomial.natDegree_mul_le.trans (by
    have hb := hlin b
    omega)

/-- A numerator of degree at most three leaves a polynomial of degree at most two. -/
theorem geometricPoleRemainderPolynomial_natDegree_le (P : Polynomial ℂ) (a b : ℂ)
    (hP : P.natDegree ≤ 3) :
    (geometricPoleRemainderPolynomial P a b).natDegree ≤ 2 := by
  have hF : (P - Polynomial.C (primaryPoleCoefficient P a b) *
      secondaryPolePolynomial b).natDegree ≤ 3 :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le hP
      ((Polynomial.natDegree_C_mul_le _ _).trans (secondaryPolePolynomial_natDegree_le b)))
  unfold geometricPoleRemainderPolynomial
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  rw [Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C _),
    Polynomial.natDegree_X_sub_C]
  omega

private theorem secondaryPolePolynomial_geometric_inverse (b : ℂ) :
    (secondaryPolePolynomial b : ℂ⟦X⟧) * (geom 1 ^ 2 * geom b) = 1 := by
  have h1 : (1 - X : ℂ⟦X⟧) * geom 1 = 1 := by
    simpa only [map_one, one_mul] using one_sub_mul_geom 1
  simp only [secondaryPolePolynomial, Polynomial.coe_mul, Polynomial.coe_pow,
    Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_C, Polynomial.coe_X]
  calc
    _ = ((1 - X) * geom 1) ^ 2 * ((1 - C b * X) * geom b) := by ring
    _ = 1 := by rw [h1, one_sub_mul_geom]; ring

/-- The exact remainder retains both secondary factors, including their possible collision. -/
theorem geometricPole_extraction (P : Polynomial ℂ) {a b : ℂ}
    (ha : a ≠ 0) (ha1 : a ≠ 1) (hab : a ≠ b) :
    (P : ℂ⟦X⟧) * geom 1 ^ 2 * (geom a * geom b) -
      C (primaryPoleCoefficient P a b) * geom a =
        (geometricPoleRemainderPolynomial P a b : ℂ⟦X⟧) * geom 1 ^ 2 * geom b := by
  have hf := congrArg (fun Q : Polynomial ℂ => (Q : ℂ⟦X⟧))
    (geometricPoleRemainderPolynomial_factorization P ha ha1 hab)
  simp only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_one,
    Polynomial.coe_C, Polynomial.coe_X] at hf
  have hinv := secondaryPolePolynomial_geometric_inverse b
  calc
    _ = ((P : ℂ⟦X⟧) - C (primaryPoleCoefficient P a b) *
        (secondaryPolePolynomial b : ℂ⟦X⟧)) * (geom 1 ^ 2 * geom b) * geom a := by
      rw [sub_mul, sub_mul]
      rw [mul_assoc (C (primaryPoleCoefficient P a b)), hinv, mul_one]
      ring
    _ = ((1 - C a * X) * geom a) *
        ((geometricPoleRemainderPolynomial P a b : ℂ⟦X⟧) * geom 1 ^ 2 * geom b) := by
      rw [← hf]
      ring
    _ = _ := by rw [one_sub_mul_geom, one_mul]

/-- A geometric formal series converges absolutely throughout its open convergence disk. -/
theorem geom_absoluteSummableAt {a u : ℂ} (h : ‖a * u‖ < 1) :
    (geom a).AbsoluteSummableAt u := by
  simp only [PowerSeries.AbsoluteSummableAt, geom, coeff_mk, ← mul_pow, norm_pow]
  exact summable_geometric_of_lt_one (norm_nonneg _) h

/-- Removing the primary pole leaves an absolutely summable coefficient remainder. -/
theorem geometricPole_remainder_absoluteSummableAt (P : Polynomial ℂ) {a b u : ℂ}
    (ha : a ≠ 0) (ha1 : a ≠ 1) (hab : a ≠ b)
    (hu : ‖u‖ < 1) (hbu : ‖b * u‖ < 1) :
    ((P : ℂ⟦X⟧) * geom 1 ^ 2 * (geom a * geom b) -
      C (primaryPoleCoefficient P a b) * geom a).AbsoluteSummableAt u := by
  rw [geometricPole_extraction P ha ha1 hab]
  exact ((PowerSeries.coe_absoluteSummableAt _ u).mul
    ((geom_absoluteSummableAt (by simpa only [one_mul] using hu)).pow 2)).mul
      (geom_absoluteSummableAt hbu)

end GaloisForLFunctions.BiarithmeticGeometry

