import GaloisForLFunctions.HTGeometry.NegativeBinomialShell
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FrobeniusTraceHasseJets
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Rational Hasse jets of Frobenius traces

Taylor substitution at the generic coordinate extends from polynomials to rational functions
as a homomorphism into power series. Congruence modulo a power of the series variable survives
inversion. Applied to Frobenius traces, this gives every negative-power Hasse jet below the
first nonlinear Frobenius exponent, in arbitrary prime characteristic.
-/

open Polynomial PowerSeries
open scoped nonZeroDivisors
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
noncomputable section
variable {K : Type*} [Field K]

/-- Polynomial Taylor substitution at the generic rational-function coordinate. -/
def rationalTaylorPoly : K[X] →+* PowerSeries (RatFunc K) :=
  Polynomial.eval₂RingHom (PowerSeries.C.comp (algebraMap K (RatFunc K)))
    (PowerSeries.C RatFunc.X + PowerSeries.X)

private theorem rationalTaylorPoly_constant (P : K[X]) :
    PowerSeries.constantCoeff (rationalTaylorPoly P) = algebraMap K[X] (RatFunc K) P := by
  have h : PowerSeries.constantCoeff.comp (rationalTaylorPoly (K := K)) =
      algebraMap K[X] (RatFunc K) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [rationalTaylorPoly]
    · simp [rationalTaylorPoly, RatFunc.algebraMap_X]
  exact congrArg (fun f : K[X] →+* RatFunc K => f P) h

private theorem rationalTaylorPoly_unit (P : K[X]⁰) :
    IsUnit (rationalTaylorPoly (P : K[X])) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, rationalTaylorPoly_constant, isUnit_iff_ne_zero]
  simpa only [map_zero] using (IsFractionRing.injective K[X] (RatFunc K)).ne
    (mem_nonZeroDivisors_iff_ne_zero.mp P.property)

/-- Rational Taylor expansion takes values in power series, since a generic nonzero denominator
has nonzero constant term. This constructs the rational Hasse derivatives in every characteristic. -/
def rationalTaylor : RatFunc K →+* PowerSeries (RatFunc K) :=
  IsLocalization.lift (M := K[X]⁰) (S := RatFunc K) rationalTaylorPoly_unit

@[simp] theorem rationalTaylor_polynomial (P : K[X]) :
    rationalTaylor (algebraMap K[X] (RatFunc K) P) = rationalTaylorPoly P :=
  IsLocalization.lift_eq rationalTaylorPoly_unit P

/-- Coefficients of the rational Taylor homomorphism are Hasse derivatives. -/
def rationalHasse (n : ℕ) (f : RatFunc K) : RatFunc K :=
  PowerSeries.coeff n (rationalTaylor f)


private theorem rationalTaylorPoly_eq_taylor (P : K[X]) :
    rationalTaylorPoly P = (Polynomial.taylor (RatFunc.X : RatFunc K)
      (P.map (algebraMap K (RatFunc K))) : PowerSeries (RatFunc K)) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp [Polynomial.map_add, hP, hQ]
  | monomial n a =>
    simp [rationalTaylorPoly, Polynomial.taylor_monomial, add_comm]


private theorem map_hasse (n : ℕ) (P : K[X]) :
    Polynomial.hasseDeriv n (P.map (algebraMap K (RatFunc K))) =
      (Polynomial.hasseDeriv n P).map (algebraMap K (RatFunc K)) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp [Polynomial.map_add, hP, hQ]
  | monomial k a => simp only [Polynomial.map_monomial, Polynomial.hasseDeriv_monomial,
      map_mul, map_natCast]

/-- The rational extension agrees with polynomial Hasse differentiation. -/
theorem rationalHasse_polynomial (n : ℕ) (P : K[X]) :
    rationalHasse n (algebraMap K[X] (RatFunc K) P) =
      algebraMap K[X] (RatFunc K) (Polynomial.hasseDeriv n P) := by
  rw [rationalHasse, rationalTaylor_polynomial, rationalTaylorPoly_eq_taylor,
    Polynomial.coeff_coe, Polynomial.taylor_coeff]
  have he : Polynomial.eval₂RingHom (algebraMap K (RatFunc K)) RatFunc.X =
      algebraMap K[X] (RatFunc K) := by
    apply Polynomial.ringHom_ext
    · intro a; simp
    · simp [RatFunc.algebraMap_X]
  rw [map_hasse, Polynomial.eval_map]
  exact congrArg (fun f : K[X] →+* RatFunc K => f (Polynomial.hasseDeriv n P)) he

/-- The coefficient operators satisfy the Hasse product law, including for quotients. -/
theorem rationalHasse_mul (n : ℕ) (f g : RatFunc K) :
    rationalHasse n (f * g) = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      rationalHasse ij.1 f * rationalHasse ij.2 g := by
  simp only [rationalHasse, map_mul, PowerSeries.coeff_mul]


private def inverseAffineSeries {L : Type*} [Field L] (a : L) (m : ℕ) : PowerSeries L :=
  PowerSeries.C (a⁻¹ ^ m) * GaloisForLFunctions.HTGeometry.shellSeries (a⁻¹) m

private theorem inverseAffineSeries_mul {L : Type*} [Field L] (a : L) (ha : a ≠ 0) (m : ℕ) :
    inverseAffineSeries a m * (PowerSeries.C a + PowerSeries.X) ^ m = 1 := by
  have hf : (PowerSeries.C a + PowerSeries.X : PowerSeries L) =
      PowerSeries.C a * (1 + PowerSeries.C (a⁻¹) * PowerSeries.X) := by
    rw [mul_add, mul_one, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]
  rw [hf, mul_pow, inverseAffineSeries]
  calc
    _ = (PowerSeries.C (a⁻¹ ^ m) * (PowerSeries.C a) ^ m) *
        (GaloisForLFunctions.HTGeometry.shellSeries (a⁻¹) m *
          (1 + PowerSeries.C (a⁻¹) * PowerSeries.X) ^ m) := by ring
    _ = 1 := by
      rw [GaloisForLFunctions.HTGeometry.shellSeries_mul, mul_one, ← map_pow,
        ← map_mul, ← mul_pow, inv_mul_cancel₀ ha, one_pow, map_one]

private theorem inverse_congruence {L : Type*} [Field L]
    (A B U V : PowerSeries L) (n m : ℕ) (h : PowerSeries.X ^ n ∣ A - B)
    (hU : U * A ^ m = 1) (hV : V * B ^ m = 1) :
    PowerSeries.X ^ n ∣ U - V := by
  have hp : PowerSeries.X ^ n ∣ B ^ m - A ^ m :=
    (dvd_neg.mpr h).trans (by simpa only [neg_sub] using sub_dvd_pow_sub_pow B A m)
  have he : U - V = U * V * (B ^ m - A ^ m) := by
    calc
      U - V = U * (V * B ^ m) - V * (U * A ^ m) := by rw [hU, hV, mul_one, mul_one]
      _ = _ := by ring
  rw [he]
  exact dvd_mul_of_dvd_right hp _

variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- Negative powers of a Frobenius trace have the same low Hasse jets as an affine function.
The binomial coefficients are interpreted in the original characteristic. -/
theorem frobeniusTraceSum_inverse_power_low_hasse (d m N : ℕ) (j : Fin (p ^ (d + 1))) :
    rationalHasse j.val
      ((algebraMap K[X] (RatFunc K)
        (frobeniusTraceSum p (d + 1) (m + 1) (Polynomial.X : K[X])))⁻¹ ^ (N + 1)) =
      (-1 : RatFunc K) ^ j.val * ((N + j.val).choose N : RatFunc K) *
        (algebraMap K[X] (RatFunc K)
          (frobeniusTraceSum p (d + 1) (m + 1) (Polynomial.X : K[X])))⁻¹ ^
            (N + 1 + j.val) := by
  let P := frobeniusTraceSum p (d + 1) (m + 1) (Polynomial.X : K[X])
  let f : RatFunc K := algebraMap K[X] (RatFunc K) P
  have hf : f ≠ 0 := by
    simpa only [f, P, map_zero] using (IsFractionRing.injective K[X] (RatFunc K)).ne
      (frobeniusTraceSum_polynomial_monic (K := K) p d m).ne_zero
  have hd : (PowerSeries.X : PowerSeries (RatFunc K)) ^ (p ^ (d + 1)) ∣
      rationalTaylor f - (PowerSeries.C f + PowerSeries.X) := by
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro k hk
    rw [map_sub]
    change rationalHasse k (algebraMap K[X] (RatFunc K) P) - _ = 0
    rw [rationalHasse_polynomial]
    have hj := frobeniusTraceSum_low_hasse (K := K) p d m ⟨k, hk⟩
    change Polynomial.hasseDeriv k P = _ at hj
    rw [hj]
    by_cases hk0 : k = 0
    · subst k; simp [f, P]
    by_cases hk1 : k = 1
    · subst k; simp
    · simp [hk0, hk1, PowerSeries.coeff_X, PowerSeries.coeff_C]
  have hu : rationalTaylor (f⁻¹ ^ (N + 1)) * rationalTaylor f ^ (N + 1) = 1 := by
    rw [← map_pow, ← map_mul, ← mul_pow, inv_mul_cancel₀ hf, one_pow, map_one]
  have hc := inverse_congruence (rationalTaylor f) (PowerSeries.C f + PowerSeries.X)
    (rationalTaylor (f⁻¹ ^ (N + 1))) (inverseAffineSeries f (N + 1))
    (p ^ (d + 1)) (N + 1) hd hu (inverseAffineSeries_mul f hf (N + 1))
  have he := PowerSeries.X_pow_dvd_iff.mp hc j.val j.isLt
  rw [map_sub] at he
  have he' := sub_eq_zero.mp he
  change rationalHasse j.val (f⁻¹ ^ (N + 1)) = _
  rw [rationalHasse, he', inverseAffineSeries, PowerSeries.coeff_C_mul,
    GaloisForLFunctions.HTGeometry.coeff_shellSeries _ (Nat.succ_pos N),
    Nat.succ_sub_one, neg_pow, pow_add]
  dsimp only [f, P]
  ring

#print axioms rationalTaylor
#print axioms rationalHasse_polynomial
#print axioms rationalHasse_mul
#print axioms frobeniusTraceSum_inverse_power_low_hasse

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
