import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticAnalyticEulerProduct
import GaloisForLFunctions.RHTower.Sieve.IntervalMultiples

/-!+# Lower bounds from positive Euler factors

The product `(1 - T)⁻¹ (1 - T^d)⁻¹` has degree-`n` coefficient
`⌊n/d⌋ + 1`. The degree-one infinity factor and any actual affine place
therefore give a quantitative lower bound for the elliptic zeta coefficients.
In particular, none of those coefficients vanishes.
-/

noncomputable section
open PowerSeries _root_.RHTower
open scoped BigOperators

namespace GaloisForLFunctions.ArithmeticEffectivityTheory

/-- Two geometric Euler factors count the possible multiples of the second degree. -/
theorem geometricPair_coeff {R : Type*} [CommRing R] (d n : ℕ) :
    PowerSeries.coeff n
      (deningerBigWittGeom (1 : R) 1 * deningerBigWittGeom 1 d) =
        ((n / d + 1 : ℕ) : R) := by
  rw [mul_comm, PowerSeries.coeff_mul]
  simp only [deningerBigWittGeom_coeff, one_pow, one_dvd, if_true, mul_one]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i _ => if d ∣ i then (1 : R) else 0) n]
  have hrange : Finset.range (n + 1) = insert 0 (Finset.Ioc 0 n) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
    omega
  rw [hrange, Finset.sum_insert (by simp), if_pos (dvd_zero d),
    ← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one,
    Sieve.card_filter_dvd_Ioc d 0 n (Nat.zero_le n)]
  simp only [Nat.zero_div, Nat.sub_zero, Nat.cast_add, Nat.cast_one]
  exact add_comm _ _

namespace FiniteFieldEllipticBase
open IsDedekindDomain

/-- Infinity alone contributes one to every coefficient. -/
theorem one_le_norm_zeta_coeff (n : ℕ) : 1 ≤ ‖PowerSeries.coeff n zeta‖ := by
  have h := ellipticZetaFinite_coeff_norm_le ∅ n
  simpa only [ellipticZetaFinite, Finset.prod_empty, mul_one,
    deningerBigWittGeom_coeff, one_dvd, if_true, one_pow, norm_one] using h

/-- Each affine place gives an explicit linear lower bound at its residue degree. -/
theorem floor_placeDegree_le_norm_zeta_coeff (v : HeightOneSpectrum A) (n : ℕ) :
    ((n / affinePlaceDegree v + 1 : ℕ) : ℝ) ≤ ‖PowerSeries.coeff n zeta‖ := by
  have h := ellipticZetaFinite_coeff_norm_le {v} n
  simpa only [ellipticZetaFinite, Finset.prod_singleton, geometricPair_coeff,
    Complex.norm_natCast] using h

/-- The positive infinity factor rules out every coefficient zero. -/
theorem zeta_coeff_ne_zero (n : ℕ) : PowerSeries.coeff n zeta ≠ 0 := by
  intro hzero
  have h := one_le_norm_zeta_coeff n
  rw [hzero, norm_zero] at h
  norm_num at h

#print axioms one_le_norm_zeta_coeff
#print axioms floor_placeDegree_le_norm_zeta_coeff
#print axioms zeta_coeff_ne_zero
end FiniteFieldEllipticBase

#print axioms geometricPair_coeff
end GaloisForLFunctions.ArithmeticEffectivityTheory
