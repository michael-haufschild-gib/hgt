import GaloisForLFunctions.HTGeometry.Arithmetic.IntegralPolynomialValuation
import GaloisForLFunctions.HTGeometry.Arithmetic.IntegralTests

/-!
# Denominator laws for monic separated-variable curves

On `f(x)=g(y)` with monic integer polynomials of positive degrees, the two
coordinates are integral at the same primes. At poles the degrees give
the exact ratio of pole orders, hence an exact identity of reduced
denominator powers. Odd-degree monic hyperelliptic equations have square
x-denominators without any assumption that their polynomial splits.
-/

namespace GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic

open Polynomial HTGeometry.Arithmetic

variable {p : ℕ} [Fact p.Prime]

/-- Monic separated-variable equations identify the local integrality
conditions on their two coordinates. -/
theorem monic_curve_integral_iff (f g : ℤ[X]) (hf : f.Monic) (hg : g.Monic)
    (hdf : 0 < f.natDegree) (hdg : 0 < g.natDegree) {x y : ℚ}
    (hcurve : f.eval₂ (Int.castRingHom ℚ) x = g.eval₂ (Int.castRingHom ℚ) y) :
    0 ≤ padicValRat p x ↔ 0 ≤ padicValRat p y := by
  rw [← monic_integerPolynomial_integral_iff f hf hdf x, hcurve,
    monic_integerPolynomial_integral_iff g hg hdg y]

/-- At a pole the degrees give the exact weighted pole-order relation. -/
theorem monic_curve_pole_orders (f g : ℤ[X]) (hf : f.Monic) (hg : g.Monic)
    (hdf : 0 < f.natDegree) (hdg : 0 < g.natDegree) {x y : ℚ}
    (hcurve : f.eval₂ (Int.castRingHom ℚ) x = g.eval₂ (Int.castRingHom ℚ) y)
    (hx : padicValRat p x < 0) :
    padicValRat p y < 0 ∧
      (f.natDegree : ℤ) * padicValRat p x = (g.natDegree : ℤ) * padicValRat p y := by
  have hy : padicValRat p y < 0 := by
    by_contra hy
    have h := (monic_curve_integral_iff f g hf hg hdf hdg hcurve).mpr (le_of_not_gt hy)
    omega
  refine ⟨hy, ?_⟩
  have h := congrArg (padicValRat p) hcurve
  rwa [(monic_integerPolynomial_eval_of_neg f hf hx).2,
    (monic_integerPolynomial_eval_of_neg g hg hy).2] at h

/-- The weighted local pole law is an exact global denominator identity. -/
theorem monic_curve_denominator_identity (f g : ℤ[X]) (hf : f.Monic) (hg : g.Monic)
    (hdf : 0 < f.natDegree) (hdg : 0 < g.natDegree) {x y : ℚ}
    (hcurve : f.eval₂ (Int.castRingHom ℚ) x = g.eval₂ (Int.castRingHom ℚ) y) :
    x.den ^ f.natDegree = y.den ^ g.natDegree := by
  apply (Nat.eq_iff_prime_padicValNat_eq _ _ (pow_ne_zero _ x.den_nz)
    (pow_ne_zero _ y.den_nz)).mpr
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  rw [padicValNat.pow, padicValNat.pow]
  have hxden := den_valuation_eq_negative_part p x
  have hyden := den_valuation_eq_negative_part p y
  by_cases hx : 0 ≤ padicValRat p x
  · have hy := (monic_curve_integral_iff f g hf hg hdf hdg hcurve).mp hx
    rw [max_eq_right (by omega)] at hxden hyden
    have hx0 : padicValNat p x.den = 0 := by omega
    have hy0 : padicValNat p y.den = 0 := by omega
    simp [hx0, hy0]
  · obtain ⟨hy, horders⟩ := monic_curve_pole_orders f g hf hg hdf hdg hcurve (lt_of_not_ge hx)
    rw [max_eq_left (by omega)] at hxden hyden
    have hZ : (f.natDegree : ℤ) * (padicValNat p x.den : ℤ) =
        (g.natDegree : ℤ) * (padicValNat p y.den : ℤ) := by
      rw [hxden, hyden]
      nlinarith only [horders]
    exact_mod_cast hZ

/-- For an odd-degree monic quadratic twist, negative x-valuations have
exactly the parity of the twisting parameter. -/
theorem odd_monic_curve_negative_parity (f : ℤ[X]) (hf : f.Monic)
    (hdeg : Odd f.natDegree) {d x y : ℚ} (hd : d ≠ 0)
    (hx : padicValRat p x < 0)
    (hcurve : y ^ 2 = d * f.eval₂ (Int.castRingHom ℚ) x) :
    Even (padicValRat p x) ↔ Even (padicValRat p d) := by
  obtain ⟨hne, hval⟩ := monic_integerPolynomial_eval_of_neg f hf hx
  have h := congrArg (padicValRat p) hcurve
  rw [padicValRat.pow, padicValRat.mul hd hne, hval] at h
  obtain ⟨k, hk⟩ := hdeg
  rw [hk] at h
  push_cast at h
  ring_nf at h
  rw [Int.even_iff, Int.even_iff]
  omega

/-- Every rational point on an odd-degree monic integer hyperelliptic
equation has square reduced x-denominator. -/
theorem squareDenominator_of_odd_monic_curve (f : ℤ[X]) (hf : f.Monic)
    (hdeg : Odd f.natDegree) {x y : ℚ}
    (hcurve : y ^ 2 = f.eval₂ (Int.castRingHom ℚ) x) : SquareDenominator x := by
  apply (squareDenominator_iff x).mpr
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hx : 0 ≤ padicValRat p x
  · exact Or.inl hx
  · right
    apply (odd_monic_curve_negative_parity f hf hdeg (d := 1) one_ne_zero
      (lt_of_not_ge hx) (by simpa only [one_mul] using hcurve)).mpr
    simp

#print axioms monic_curve_denominator_identity
#print axioms squareDenominator_of_odd_monic_curve

end GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic
