import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Ring

/-!
# Integral logarithmic jet congruences

For the invariant derivative `D=(1+X)d/dX`, the ideal
`(n,(1+X)^n-1)` of integral formal power series is differential.
The unit `1+((1+X)^n-1)g` therefore has every positive logarithmic
jet divisible by `n`. This proves the formal-algebraic congruence
mechanism in Goto–Ishii, Lemma 5.3, for arbitrary power series.
Logarithmic derivatives are defined integrally using the unit inverse;
no rational logarithm or analytic convergence is required.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Coleman
namespace Formal
open PowerSeries
variable {R : Type*} [CommRing R]

/-- Invariant differentiation on formal multiplicative coordinates. -/
def invariantDerivative (f : R⟦X⟧) : R⟦X⟧ := (1 + X) * d⁄dX R f

/-- The formal multiplication-by-`n` coordinate. -/
def divisionSeries (n : ℕ) : R⟦X⟧ := (1 + X) ^ n - 1

/-- Invariant jets are constant coefficients of iterated invariant derivatives. -/
def jet (k : ℕ) (f : R⟦X⟧) : R :=
  constantCoeff ((invariantDerivative^[k]) f)

theorem invariantDerivative_add (f g : R⟦X⟧) :
    invariantDerivative (f + g) = invariantDerivative f + invariantDerivative g := by
  simp only [invariantDerivative, map_add, mul_add]

theorem invariantDerivative_mul (f g : R⟦X⟧) :
    invariantDerivative (f * g) = invariantDerivative f * g + f * invariantDerivative g := by
  simp only [invariantDerivative, Derivation.leibniz, smul_eq_mul]
  ring

theorem invariantDerivative_nat_mul (n : ℕ) (f : R⟦X⟧) :
    invariantDerivative ((n : R⟦X⟧) * f) = (n : R⟦X⟧) * invariantDerivative f := by
  have hn : d⁄dX R (n : R⟦X⟧) = 0 := by
    rw [← map_natCast (C : R →+* R⟦X⟧) n, derivative_C]
  simp only [invariantDerivative, Derivation.leibniz, hn,
    smul_eq_mul, mul_zero, add_zero]
  ring

theorem invariantDerivative_divisionSeries (n : ℕ) :
    invariantDerivative (divisionSeries (R := R) n) = (n : R⟦X⟧) * (1 + X) ^ n := by
  cases n with
  | zero => simp [invariantDerivative, divisionSeries]
  | succ n =>
    simp only [invariantDerivative, divisionSeries, map_sub, PowerSeries.derivative_pow,
      map_add, Derivation.map_one_eq_zero, derivative_X, zero_add, mul_one, sub_zero,
      Nat.add_sub_cancel]
    rw [pow_succ]
    ring

/-- Differentiation preserves both generators of the congruence ideal. -/
theorem iterate_congruence_ideal (n k : ℕ) (f g : R⟦X⟧) :
    ∃ a b : R⟦X⟧,
      (invariantDerivative^[k]) (divisionSeries n * f + (n : R⟦X⟧) * g) =
        divisionSeries n * a + (n : R⟦X⟧) * b := by
  induction k with
  | zero => exact ⟨f, g, rfl⟩
  | succ k ih =>
    obtain ⟨a, b, hab⟩ := ih
    refine ⟨invariantDerivative a, (1 + X) ^ n * a + invariantDerivative b, ?_⟩
    rw [Function.iterate_succ_apply', hab, invariantDerivative_add,
      invariantDerivative_mul, invariantDerivative_divisionSeries,
      invariantDerivative_nat_mul]
    ring

/-- Every jet of an element of `(n,(1+X)^n-1)` vanishes modulo `n`. -/
theorem dvd_jet_congruence_ideal (n k : ℕ) (f g : R⟦X⟧) :
    (n : R) ∣ jet k (divisionSeries n * f + (n : R⟦X⟧) * g) := by
  obtain ⟨a, b, hab⟩ := iterate_congruence_ideal n k f g
  refine ⟨constantCoeff b, ?_⟩
  unfold jet
  rw [hab]
  simp [divisionSeries]

private theorem congruence_isUnit (n : ℕ) (g : R⟦X⟧) :
    IsUnit (1 + divisionSeries n * g) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  simp [divisionSeries]

/-- Canonical formal unit congruent to one modulo the division series. -/
def congruenceUnit (n : ℕ) (g : R⟦X⟧) : R⟦X⟧ˣ :=
  (congruence_isUnit n g).unit

@[simp] theorem coe_congruenceUnit (n : ℕ) (g : R⟦X⟧) :
    (congruenceUnit n g : R⟦X⟧) = 1 + divisionSeries n * g :=
  (congruence_isUnit n g).unit_spec

/-- The logarithmic derivative is integral for every formal unit. -/
def logarithmicDerivative (u : R⟦X⟧ˣ) : R⟦X⟧ :=
  invariantDerivative (u : R⟦X⟧) * (u⁻¹ : R⟦X⟧ˣ)

/-- The `(k+1)`st logarithmic jet, without constructing a logarithm series. -/
def logarithmicJet (k : ℕ) (u : R⟦X⟧ˣ) : R := jet k (logarithmicDerivative u)

/-- Division-series congruence forces every positive logarithmic jet to be divisible by `n`. -/
theorem dvd_logarithmicJet_congruenceUnit (n k : ℕ) (g : R⟦X⟧) :
    (n : R) ∣ logarithmicJet k (congruenceUnit n g) := by
  let v : R⟦X⟧ := ((congruenceUnit n g)⁻¹ : R⟦X⟧ˣ)
  have hlog : logarithmicDerivative (congruenceUnit n g) =
      divisionSeries n * (invariantDerivative g * v) + (n : R⟦X⟧) * ((1 + X) ^ n * g * v) := by
    rw [logarithmicDerivative, coe_congruenceUnit, invariantDerivative_add,
      invariantDerivative_mul, invariantDerivative_divisionSeries]
    have hone : invariantDerivative (1 : R⟦X⟧) = 0 := by
      simp [invariantDerivative]
    rw [hone, zero_add]
    change (_ + _) * v = _
    ring
  unfold logarithmicJet
  rw [hlog]
  exact dvd_jet_congruence_ideal n k _ _

/-- Every invariant jet is linear over integral constants. -/
theorem jet_nat_mul (n k : ℕ) (f : R⟦X⟧) :
    jet k ((n : R⟦X⟧) * f) = (n : R) * jet k f := by
  have hi : (invariantDerivative^[k]) ((n : R⟦X⟧) * f) =
      (n : R⟦X⟧) * (invariantDerivative^[k]) f := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, invariantDerivative_nat_mul,
        Function.iterate_succ_apply']
  simp only [jet, hi, map_mul, map_natCast]

/-- Congruence survives arbitrary differentiation in a second formal variable. -/
theorem dvd_mixed_logarithmicJet (n i j : ℕ) (g : (R⟦X⟧)⟦X⟧) :
    (n : R) ∣ jet j (logarithmicJet i (congruenceUnit n g)) := by
  obtain ⟨h, hh⟩ := dvd_logarithmicJet_congruenceUnit n i g
  rw [hh, jet_nat_mul]
  exact dvd_mul_right _ _

/-- The full prime-power logarithmic congruence holds for every integral formal series. -/
theorem primePower_dvd_logarithmicJet (p m k : ℕ) (g : ℤ⟦X⟧) :
    (p : ℤ) ^ m ∣ logarithmicJet k (congruenceUnit (p ^ m) g) := by
  simpa only [Nat.cast_pow] using dvd_logarithmicJet_congruenceUnit (p ^ m) k g

end Formal
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Coleman

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.Coleman.Formal.primePower_dvd_logarithmicJet

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.Coleman.Formal.dvd_mixed_logarithmicJet
