import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerClosedPointDegrees
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Zeta.PolynomialOrderEulerProduct
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Zeta.KummerPointCountZeta

/-!
# The Kummer zeta series is the closed-prime Euler product

Multiply the coefficientwise inverse Euler product of the fixed affine
normalization by the degree-one factor at infinity. Its logarithmic ghost
is the actual extension-count sequence. Inverting therefore gives the
previously determined rational zeta series.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open IsDedekindDomain PolynomialOrderClosedPoints _root_.RHTower PowerSeries
open scoped PowerSeries.WithPiTopology Topology
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
local notation "K" => SquareConstantField p (kummerSquareIndex d n)
local notation "A" => PrimePowerKummerThreePointAffineNormalization p d n r

/-- The inverse Euler product over all affine closed primes and the unique rational infinity place. -/
def primePowerKummerInverseEulerProduct : PowerSeries ℂ :=
  deningerBigWittFactor 1 1 * inverseEulerProduct K A p

theorem primePowerKummerInverseEulerProduct_constantCoeff :
    constantCoeff (primePowerKummerInverseEulerProduct p d n r) = 1 := by
  rw [primePowerKummerInverseEulerProduct, map_mul,
    deningerBigWittFactor_constantCoeff 1 1 (by omega), inverseEulerProduct_constantCoeff, one_mul]

/-- The local factors recover exactly the intrinsic projective point-count ghost. -/
theorem primePowerKummerInverseEulerProduct_logGhost :
    deningerBigWittLogGhost (primePowerKummerInverseEulerProduct p d n r)
      (primePowerKummerInverseEulerProduct_constantCoeff p d n r) =
        primePowerKummerPointCountGhost p d n r := by
  apply PowerSeries.ext
  intro e
  by_cases he : e = 0
  · subst e
    rw [coeff_zero_eq_constantCoeff, deningerBigWittLogGhost_constantCoeff]
    change 0 = (primePowerKummerExtensionPointCount p d n r 0 : ℂ)
    rw [primePowerKummerExtensionPointCount_zero, Nat.cast_zero]
  · letI : NeZero e := ⟨he⟩
    unfold primePowerKummerInverseEulerProduct
    rw [deningerBigWittLogGhost_mul _ _
        (deningerBigWittFactor_constantCoeff 1 1 (by omega))
        (inverseEulerProduct_constantCoeff K A p), map_add,
      deningerBigWittLogGhost_factor_coeff 1 (by omega) (Nat.pos_of_ne_zero he),
      inverseEulerProduct_ghost_coeff K A p e]
    simp only [one_dvd, ite_true, Nat.cast_one, one_pow, one_mul,
      primePowerKummerPointCountGhost, coeff_mk,
      primePowerKummerExtensionPointCount_eq_algHom, Nat.cast_add]
    exact add_comm _ _

/-- Inversion of the actual closed-prime product gives the Kummer zeta series. -/
theorem primePowerKummerInverseEulerProduct_inv_eq_zeta :
    invOfUnit (primePowerKummerInverseEulerProduct p d n r) 1 =
      primePowerKummerZeta p d n r := by
  let P := primePowerKummerInverseEulerProduct p d n r
  let Z := invOfUnit P 1
  have hP : constantCoeff P = 1 := primePowerKummerInverseEulerProduct_constantCoeff p d n r
  have hZP : Z * P = 1 := invOfUnit_mul P 1 hP
  have hZ : constantCoeff Z = 1 := by
    have h := congrArg constantCoeff hZP
    simpa only [map_mul, hP, mul_one, map_one] using h
  have hG := deningerBigWittLogGhost_mul Z P hZ hP
  have hleft : deningerBigWittLogGhost (Z * P) (by simp only [map_mul, hZ, hP, mul_one]) = 0 := by
    have he := deningerBigWittLogGhost_congr
      (by simp only [map_mul, hZ, hP, mul_one]) (by exact map_one _) hZP
    exact he.trans (by simp only [deningerBigWittLogGhost, Derivation.map_one_eq_zero,
      mul_zero, zero_mul, neg_zero])
  have hGZ : deningerBigWittLogGhost Z hZ = -primePowerKummerPointCountGhost p d n r := by
    rw [hleft, primePowerKummerInverseEulerProduct_logGhost] at hG
    exact eq_neg_of_add_eq_zero_left hG.symm
  apply primePowerKummerZeta_unique p d n r Z hZ
  have hself := deningerBigWittLogGhost_mul_self Z hZ
  rw [hGZ, neg_mul] at hself
  unfold HasGhost
  exact (neg_injective hself).symm.trans (mul_comm _ _)

/-- The projective zeta series is the affine Euler series multiplied by the geometric factor at infinity. -/
theorem primePowerKummerZeta_eq_affineEuler :
    primePowerKummerZeta p d n r =
      deningerBigWittGeom 1 1 * invOfUnit (inverseEulerProduct K A p) 1 := by
  let P := primePowerKummerInverseEulerProduct p d n r
  let Z := deningerBigWittGeom (1 : ℂ) 1 * invOfUnit (inverseEulerProduct K A p) 1
  have hZP : Z * P = 1 := by
    dsimp only [Z, P, primePowerKummerInverseEulerProduct]
    rw [mul_mul_mul_comm, deningerBigWittGeom_mul_factor 1 (by omega : 0 < 1),
      invOfUnit_mul _ _ (inverseEulerProduct_constantCoeff K A p), one_mul]
  have hi : invOfUnit P 1 * P = 1 :=
    invOfUnit_mul P 1 (primePowerKummerInverseEulerProduct_constantCoeff p d n r)
  rw [← primePowerKummerInverseEulerProduct_inv_eq_zeta]
  change invOfUnit P 1 = Z
  calc
    _ = invOfUnit P 1 * (Z * P) := by rw [hZP, mul_one]
    _ = Z * (invOfUnit P 1 * P) := by ring
    _ = Z := by rw [hi, mul_one]

/-- Finite products of reciprocal local factors over the degree cutoff, including rational infinity. -/
def primePowerKummerEulerPartial (N : ℕ) : PowerSeries ℂ :=
  deningerBigWittGeom 1 1 * eulerPartial K A p N

/-- Each coefficient of the actual Euler product stabilizes at the coefficient of the rational zeta series. -/
theorem primePowerKummerEulerPartial_coeff_stable {e N : ℕ} (heN : e ≤ N) :
    coeff e (primePowerKummerEulerPartial p d n r N) = coeff e (primePowerKummerZeta p d n r) := by
  rw [primePowerKummerZeta_eq_affineEuler, primePowerKummerEulerPartial, coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.HasAntidiagonal.mem_antidiagonal.mp hj
  rw [eulerPartial_coeff_stable K A p (show j.2 ≤ N by omega)]

/-- The reciprocal local-factor products converge coefficientwise to the Kummer zeta series. -/
theorem tendsto_primePowerKummerEulerPartial :
    Filter.Tendsto (primePowerKummerEulerPartial p d n r) Filter.atTop
      (𝓝 (primePowerKummerZeta p d n r)) := by
  rw [primePowerKummerZeta_eq_affineEuler]
  exact tendsto_const_nhds.mul (tendsto_eulerPartial K A p)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
