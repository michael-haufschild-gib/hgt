import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinRamanujanDirichletSeries
import GaloisForLFunctions.RHTower.EHKoszulDuality
import GaloisForLFunctions.HTGeometry.LSeriesPowerTwist
import GaloisForLFunctions.RHTower.MFreeLadder
import GaloisForLFunctions.RHTower.EulerTruncationRigidity
import GaloisForLFunctions.RHTower.Sieve.DivisorSquareSummability
import GaloisForLFunctions.RHTower.Sieve.VaughanTypeIICoefficients

/-!
# Two-shift Ramanujan divisor-product Dirichlet series

The actual nonconstant Eisenstein-by-Eisenstein unfolding produces the pointwise coefficient
product

`sigma_a(n) * sigma_b(n)`,  where  `sigma_a = zeta * (n ↦ n^a)`.

The earlier BM Ramanujan module proves the one-coefficient reduced-residue series.  The missing
family-level arithmetic weld was the two-shift product.  This module proves its local Euler
identity in `ℂ⟦X⟧`, globalizes it through multiplicativity, proves absolute convergence directly
from the corpus divisor-square majorant, and obtains

`L(sigma_a · sigma_b, w) =
  zeta(w) zeta(w-a) zeta(w-b) zeta(w-a-b) / zeta(2w-a-b)`

for negative-real-part shifts and `Re(w) > 1`.  Chamber conditions are carried as data, so the
final theorem has no hypotheses.

This discharges C-A.9x-a in the actual meromorphic RSZ normalization audit.  Full contribution
chain:

`two-shift Ramanujan product -> literal nonzero Fourier unfolding -> classical four-Lambda
regularized family -> compare with canonical four-Xi family -> factor-10 normalization mismatch
at s=t=2 -> kill unmodified HB scalar landing`.

`[NEW-TO-CORPUS] [PAPER-PROVED] [LEAN-PROVED] [HB] [C-A.9x-a]`
-/

open scoped BigOperators
open PowerSeries

namespace RHTower
noncomputable section

def localAFSeries (f : ArithmeticFunction ℂ) (p : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun e => f (p ^ e)

lemma sum_nat_antidiagonal_eq_range (F : ℕ × ℕ → ℂ) (k : ℕ) :
    (∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, F x) =
      ∑ j ∈ Finset.range (k + 1), F (j, k - j) := by
  let e : ℕ ↪ ℕ × ℕ :=
    ⟨fun j => (j, k - j), fun a b h => by simpa using congrArg Prod.fst h⟩
  have heq : Finset.HasAntidiagonal.antidiagonal k = (Finset.range (k + 1)).map e := by
    ext x
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    simp only [Finset.mem_map, Finset.mem_range]
    constructor
    · intro hx
      refine ⟨x.1, by omega, ?_⟩
      apply Prod.ext
      · rfl
      · dsimp [e]
        omega
    · rintro ⟨j, hj, rfl⟩
      dsimp [e]
      omega
  rw [heq, Finset.sum_map]
  rfl

theorem localAFSeries_mul (f g : ArithmeticFunction ℂ) {p : ℕ} (hp : p.Prime) :
    localAFSeries (f * g) p = localAFSeries f p * localAFSeries g p := by
  ext k
  rw [PowerSeries.coeff_mul]
  simp only [localAFSeries, PowerSeries.coeff_mk]
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => f a * g b),
    Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  rw [sum_nat_antidiagonal_eq_range]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [Nat.pow_div (by omega) hp.pos]

def geomSumCoeff (r : ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1), r ^ j

def geomSeries (r : ℂ) : PowerSeries ℂ := PowerSeries.mk fun n => r ^ n

def divisorPairSeries (A B : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => geomSumCoeff A n * geomSumCoeff B n

lemma one_sub_mul_geomSumCoeff (r : ℂ) (n : ℕ) :
    (1 - r) * geomSumCoeff r n = 1 - r ^ (n + 1) := by
  induction n with
  | zero => simp [geomSumCoeff]
  | succ n ih =>
      rw [geomSumCoeff, Finset.sum_range_succ]
      rw [show ∑ x ∈ Finset.range (n + 1), r ^ x = geomSumCoeff r n by rfl]
      rw [mul_add, ih]
      ring_nf

lemma scaled_divisorPairSeries_eq (A B : ℂ) :
    PowerSeries.C ((1 - A) * (1 - B)) * divisorPairSeries A B =
      geomSeries 1 - PowerSeries.C A * geomSeries A -
        PowerSeries.C B * geomSeries B + PowerSeries.C (A * B) * geomSeries (A * B) := by
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, divisorPairSeries,
    geomSeries, PowerSeries.coeff_mk]
  rw [show ((1 - A) * (1 - B)) *
        (geomSumCoeff A n * geomSumCoeff B n) =
      ((1 - A) * geomSumCoeff A n) * ((1 - B) * geomSumCoeff B n) by ring]
  rw [one_sub_mul_geomSumCoeff, one_sub_mul_geomSumCoeff]
  rw [pow_succ A n, pow_succ B n, one_pow, mul_pow]
  ring

lemma simple_geom_combination_eq_scaled_fourGeom (A B : ℂ) :
    geomSeries 1 - PowerSeries.C A * geomSeries A -
        PowerSeries.C B * geomSeries B + PowerSeries.C (A * B) * geomSeries (A * B) =
      PowerSeries.C ((1 - A) * (1 - B)) *
        (1 - PowerSeries.C (A * B) * PowerSeries.X ^ 2) *
          (geomSeries 1 * geomSeries A * geomSeries B * geomSeries (A * B)) := by
  let L : ℂ → PowerSeries ℂ := fun r => 1 - PowerSeries.C r * PowerSeries.X
  let G : ℂ → PowerSeries ℂ := geomSeries
  let F : PowerSeries ℂ := G 1 * G A * G B * G (A * B)
  have h1 : L 1 * G 1 = 1 := by
    simpa [L, G, geomSeries] using GaloisForLFunctions.geometric_localFactor_inv 1
  have hA : L A * G A = 1 := by
    simpa [L, G, geomSeries] using GaloisForLFunctions.geometric_localFactor_inv A
  have hB : L B * G B = 1 := by
    simpa [L, G, geomSeries] using GaloisForLFunctions.geometric_localFactor_inv B
  have hAB : L (A * B) * G (A * B) = 1 := by
    simpa [L, G, geomSeries] using GaloisForLFunctions.geometric_localFactor_inv (A * B)
  have t1 : (L A * L B * L (A * B)) * F = G 1 := by
    rw [show (L A * L B * L (A * B)) * F =
      G 1 * (L A * G A) * (L B * G B) * (L (A * B) * G (A * B)) by
        dsimp [F]; ring]
    rw [hA, hB, hAB]
    ring
  have tA : (L 1 * L B * L (A * B)) * F = G A := by
    rw [show (L 1 * L B * L (A * B)) * F =
      G A * (L 1 * G 1) * (L B * G B) * (L (A * B) * G (A * B)) by
        dsimp [F]; ring]
    rw [h1, hB, hAB]
    ring
  have tB : (L 1 * L A * L (A * B)) * F = G B := by
    rw [show (L 1 * L A * L (A * B)) * F =
      G B * (L 1 * G 1) * (L A * G A) * (L (A * B) * G (A * B)) by
        dsimp [F]; ring]
    rw [h1, hA, hAB]
    ring
  have tAB : (L 1 * L A * L B) * F = G (A * B) := by
    rw [show (L 1 * L A * L B) * F =
      G (A * B) * (L 1 * G 1) * (L A * G A) * (L B * G B) by
        dsimp [F]; ring]
    rw [h1, hA, hB]
    ring
  have hpoly :
      L A * L B * L (A * B) -
          PowerSeries.C A * (L 1 * L B * L (A * B)) -
          PowerSeries.C B * (L 1 * L A * L (A * B)) +
          PowerSeries.C (A * B) * (L 1 * L A * L B) =
        PowerSeries.C ((1 - A) * (1 - B)) *
          (1 - PowerSeries.C (A * B) * PowerSeries.X ^ 2) := by
    dsimp [L]
    simp only [map_sub, map_mul, map_one]
    ring
  change G 1 - PowerSeries.C A * G A - PowerSeries.C B * G B +
      PowerSeries.C (A * B) * G (A * B) = _
  rw [← t1, ← tA, ← tB, ← tAB]
  rw [show
      (L A * L B * L (A * B)) * F -
          PowerSeries.C A * ((L 1 * L B * L (A * B)) * F) -
          PowerSeries.C B * ((L 1 * L A * L (A * B)) * F) +
          PowerSeries.C (A * B) * ((L 1 * L A * L B) * F) =
        (L A * L B * L (A * B) -
          PowerSeries.C A * (L 1 * L B * L (A * B)) -
          PowerSeries.C B * (L 1 * L A * L (A * B)) +
          PowerSeries.C (A * B) * (L 1 * L A * L B)) * F by ring]
  rw [hpoly]

lemma divisorPairSeries_eq_polarFactor_mul_fourGeom
    (A B : ℂ) (hA : A ≠ 1) (hB : B ≠ 1) :
    divisorPairSeries A B =
      (1 - PowerSeries.C (A * B) * PowerSeries.X ^ 2) *
        (geomSeries 1 * geomSeries A * geomSeries B * geomSeries (A * B)) := by
  have hscaled := (scaled_divisorPairSeries_eq A B).trans
    (simple_geom_combination_eq_scaled_fourGeom A B)
  have hcscalar : (1 - A) * (1 - B) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hA.symm) (sub_ne_zero.mpr hB.symm)
  have hc : PowerSeries.C ((1 - A) * (1 - B)) ≠ 0 :=
    by simpa using PowerSeries.C_injective.ne hcscalar
  apply mul_left_cancel₀ hc
  simpa only [mul_assoc] using hscaled

def squareGeomCoeff (C : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => 0
  | n + 2 => C * squareGeomCoeff C n

def squareGeomSeries (C : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (squareGeomCoeff C)

lemma polarFactor_mul_squareGeomSeries (C : ℂ) :
    (1 - PowerSeries.C C * PowerSeries.X ^ 2) * squareGeomSeries C = 1 := by
  ext n
  rw [show (1 - PowerSeries.C C * PowerSeries.X ^ 2) * squareGeomSeries C =
      squareGeomSeries C - PowerSeries.C C *
        (PowerSeries.X ^ 2 * squareGeomSeries C) by ring]
  rcases n with _ | _ | d
  · norm_num [squareGeomSeries, squareGeomCoeff, PowerSeries.coeff_mul,
      Finset.HasAntidiagonal.antidiagonal]
  · norm_num [squareGeomSeries, squareGeomCoeff, PowerSeries.coeff_mul,
      Finset.HasAntidiagonal.antidiagonal]
  · simp only [map_sub, PowerSeries.coeff_mk, squareGeomSeries,
      PowerSeries.coeff_C_mul, squareGeomCoeff]
    rw [show d + 2 = d + 2 by rfl, PowerSeries.coeff_X_pow_mul]
    simp

lemma divisorPairSeries_mul_squareGeomSeries
    (A B : ℂ) (hA : A ≠ 1) (hB : B ≠ 1) :
    divisorPairSeries A B * squareGeomSeries (A * B) =
      geomSeries 1 * geomSeries A * geomSeries B * geomSeries (A * B) := by
  rw [divisorPairSeries_eq_polarFactor_mul_fourGeom A B hA hB]
  rw [show
      (1 - PowerSeries.C (A * B) * PowerSeries.X ^ 2) *
          (geomSeries 1 * geomSeries A * geomSeries B * geomSeries (A * B)) *
          squareGeomSeries (A * B) =
        (geomSeries 1 * geomSeries A * geomSeries B * geomSeries (A * B)) *
          ((1 - PowerSeries.C (A * B) * PowerSeries.X ^ 2) *
            squareGeomSeries (A * B)) by ring]
  rw [polarFactor_mul_squareGeomSeries]
  ring

lemma sum_range_reverse (F : ℕ → ℂ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), F (n - j)) =
      ∑ j ∈ Finset.range (n + 1), F j := by
  simpa using Finset.sum_range_reflect F (n + 1)

def d4BMPowerArithmetic (a : ℂ) : ArithmeticFunction ℂ where
  toFun := GaloisForLFunctions.lseriesPowerTwistCoeff
    (fun n => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) a
  map_zero' := by simp [GaloisForLFunctions.lseriesPowerTwistCoeff]

@[simp] lemma d4BMPowerArithmetic_apply (a : ℂ) (n : ℕ) :
    d4BMPowerArithmetic a n =
      (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n * (n : ℂ) ^ a := rfl

private lemma d4BM_natCast_mul_cpow (m n : ℕ) (a : ℂ) :
    ((m * n : ℕ) : ℂ) ^ a = (m : ℂ) ^ a * (n : ℂ) ^ a := by
  rw [show ((m * n : ℕ) : ℂ) = (((m : ℝ)) : ℂ) * (((n : ℝ)) : ℂ) by
      push_cast; ring,
    show (m : ℂ) = (((m : ℝ)) : ℂ) by push_cast; ring,
    show (n : ℂ) = (((n : ℝ)) : ℂ) by push_cast; ring,
    Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

lemma d4BMPowerArithmetic_isMultiplicative (a : ℂ) :
    (d4BMPowerArithmetic a).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [d4BMPowerArithmetic_apply, ArithmeticFunction.zeta_apply]
  · intro m n hm hn hcop
    rw [d4BMPowerArithmetic_apply, d4BMPowerArithmetic_apply,
      d4BMPowerArithmetic_apply, d4BM_natCast_mul_cpow]
    simp [ArithmeticFunction.zeta_apply, hm, hn, mul_ne_zero hm hn]

lemma d4BMPowerArithmetic_prime_pow
    (a : ℂ) {p e : ℕ} (hp : p.Prime) :
    d4BMPowerArithmetic a (p ^ e) = ((p : ℂ) ^ a) ^ e := by
  rw [d4BMPowerArithmetic_apply]
  simp only [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
    pow_ne_zero e hp.ne_zero, if_false, Nat.cast_one, one_mul, Nat.cast_pow]
  exact (Complex.natCast_cpow_natCast_mul p e a).symm.trans
    (Complex.cpow_nat_mul (p : ℂ) e a)

lemma localAFSeries_d4BMPowerArithmetic
    (a : ℂ) {p : ℕ} (hp : p.Prime) :
    localAFSeries (d4BMPowerArithmetic a) p = geomSeries ((p : ℂ) ^ a) := by
  ext e
  simp [localAFSeries, geomSeries, d4BMPowerArithmetic_prime_pow a hp]

def d4BMGeneralizedDivisorArithmetic (a : ℂ) : ArithmeticFunction ℂ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℂ) * d4BMPowerArithmetic a

lemma d4BMGeneralizedDivisorArithmetic_isMultiplicative (a : ℂ) :
    (d4BMGeneralizedDivisorArithmetic a).IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_zeta.natCast.mul
    (d4BMPowerArithmetic_isMultiplicative a)

lemma localAFSeries_zeta {p : ℕ} (hp : p.Prime) :
    localAFSeries (ArithmeticFunction.zeta : ArithmeticFunction ℂ) p = geomSeries 1 := by
  ext e
  simp only [localAFSeries, geomSeries, PowerSeries.coeff_mk,
    ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, one_pow]
  rw [if_neg (pow_ne_zero e hp.ne_zero)]
  norm_num

lemma localAFSeries_d4BMGeneralizedDivisorArithmetic
    (a : ℂ) {p : ℕ} (hp : p.Prime) :
    localAFSeries (d4BMGeneralizedDivisorArithmetic a) p =
      geomSeries 1 * geomSeries ((p : ℂ) ^ a) := by
  rw [d4BMGeneralizedDivisorArithmetic, localAFSeries_mul _ _ hp,
    localAFSeries_zeta hp, localAFSeries_d4BMPowerArithmetic a hp]

lemma coeff_geomSeries_one_mul_geomSeries (A : ℂ) (n : ℕ) :
    PowerSeries.coeff n (geomSeries 1 * geomSeries A) = geomSumCoeff A n := by
  rw [PowerSeries.coeff_mul, sum_nat_antidiagonal_eq_range]
  simp only [geomSeries, PowerSeries.coeff_mk, one_pow, one_mul]
  exact sum_range_reverse (fun j => A ^ j) n

lemma d4BMGeneralizedDivisorArithmetic_prime_pow
    (a : ℂ) {p e : ℕ} (hp : p.Prime) :
    d4BMGeneralizedDivisorArithmetic a (p ^ e) =
      geomSumCoeff ((p : ℂ) ^ a) e := by
  have h := congrArg (PowerSeries.coeff e)
    (localAFSeries_d4BMGeneralizedDivisorArithmetic a hp)
  simpa [localAFSeries, PowerSeries.coeff_mk,
    coeff_geomSeries_one_mul_geomSeries] using h

def d4BMDivisorProductArithmetic (a b : ℂ) : ArithmeticFunction ℂ where
  toFun n := d4BMGeneralizedDivisorArithmetic a n *
    d4BMGeneralizedDivisorArithmetic b n
  map_zero' := by simp [d4BMGeneralizedDivisorArithmetic]

@[simp] lemma d4BMDivisorProductArithmetic_apply (a b : ℂ) (n : ℕ) :
    d4BMDivisorProductArithmetic a b n =
      d4BMGeneralizedDivisorArithmetic a n *
        d4BMGeneralizedDivisorArithmetic b n := rfl

lemma d4BMDivisorProductArithmetic_isMultiplicative (a b : ℂ) :
    (d4BMDivisorProductArithmetic a b).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [d4BMDivisorProductArithmetic_apply,
      (d4BMGeneralizedDivisorArithmetic_isMultiplicative a).map_one,
      (d4BMGeneralizedDivisorArithmetic_isMultiplicative b).map_one]
  · intro m n hm hn hcop
    rw [d4BMDivisorProductArithmetic_apply, d4BMDivisorProductArithmetic_apply,
      d4BMDivisorProductArithmetic_apply,
      (d4BMGeneralizedDivisorArithmetic_isMultiplicative a).map_mul_of_coprime hcop,
      (d4BMGeneralizedDivisorArithmetic_isMultiplicative b).map_mul_of_coprime hcop]
    ring

lemma localAFSeries_d4BMDivisorProductArithmetic
    (a b : ℂ) {p : ℕ} (hp : p.Prime) :
    localAFSeries (d4BMDivisorProductArithmetic a b) p =
      divisorPairSeries ((p : ℂ) ^ a) ((p : ℂ) ^ b) := by
  ext e
  simp [localAFSeries, divisorPairSeries, d4BMDivisorProductArithmetic_apply,
    d4BMGeneralizedDivisorArithmetic_prime_pow a hp,
    d4BMGeneralizedDivisorArithmetic_prime_pow b hp]

lemma squareGeomCoeff_even (C : ℂ) (k : ℕ) :
    squareGeomCoeff C (2 * k) = C ^ k := by
  induction k with
  | zero => simp [squareGeomCoeff]
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, squareGeomCoeff, ih]
      ring

lemma squareGeomCoeff_odd (C : ℂ) (k : ℕ) :
    squareGeomCoeff C (2 * k + 1) = 0 := by
  induction k with
  | zero => simp [squareGeomCoeff]
  | succ k ih =>
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
        squareGeomCoeff, ih, mul_zero]

def d4BMSquarePowerArithmetic (a b : ℂ) : ArithmeticFunction ℂ :=
  mPart 2 (d4BMPowerArithmetic (a + b))

lemma d4BMSquarePowerArithmetic_isMultiplicative (a b : ℂ) :
    (d4BMSquarePowerArithmetic a b).IsMultiplicative :=
  isMultiplicative_mPart two_ne_zero (d4BMPowerArithmetic_isMultiplicative (a + b))

lemma d4BMSquarePowerArithmetic_prime_pow
    (a b : ℂ) {p e : ℕ} (hp : p.Prime) :
    d4BMSquarePowerArithmetic a b (p ^ e) =
      squareGeomCoeff ((p : ℂ) ^ a * (p : ℂ) ^ b) e := by
  rcases Nat.even_or_odd' e with ⟨k, rfl | rfl⟩
  · rw [squareGeomCoeff_even]
    change mPart 2 (d4BMPowerArithmetic (a + b)) (p ^ (2 * k)) = _
    rw [show p ^ (2 * k) = (p ^ k) ^ 2 by rw [← pow_mul]; congr 1; omega,
      mPart_apply_pow two_ne_zero,
      d4BMPowerArithmetic_prime_pow (a + b) hp,
      Complex.cpow_add a b (Nat.cast_ne_zero.mpr hp.ne_zero)]
  · rw [squareGeomCoeff_odd]
    change mPart 2 (d4BMPowerArithmetic (a + b)) (p ^ (2 * k + 1)) = 0
    rw [mPart_two_eq_sqrtPart,
      sqrtPart_apply_of_not_isSquare _
        (not_isSquare_prime_pow_odd hp ⟨k, by omega⟩)]

lemma localAFSeries_d4BMSquarePowerArithmetic
    (a b : ℂ) {p : ℕ} (hp : p.Prime) :
    localAFSeries (d4BMSquarePowerArithmetic a b) p =
      squareGeomSeries ((p : ℂ) ^ a * (p : ℂ) ^ b) := by
  ext e
  simp [localAFSeries, squareGeomSeries,
    d4BMSquarePowerArithmetic_prime_pow a b hp]

structure D4BMNegativeDivisorShift where
  value : ℂ
  re_neg : value.re < 0

instance : Coe D4BMNegativeDivisorShift ℂ := ⟨D4BMNegativeDivisorShift.value⟩

lemma D4BMNegativeDivisorShift.natCast_cpow_ne_one
    (a : D4BMNegativeDivisorShift) {p : ℕ} (hp : p.Prime) :
    (p : ℂ) ^ (a : ℂ) ≠ 1 := by
  have hpos : 0 < (-((a : ℂ))).re := by
    simpa using neg_pos.mpr a.re_neg
  have hnorm := norm_natCast_cpow_neg_lt_one hp.two_le hpos
  intro h
  rw [neg_neg] at hnorm
  rw [h, norm_one] at hnorm
  exact lt_irrefl 1 hnorm

def d4BMRamanujanCorrectedArithmetic
    (a b : D4BMNegativeDivisorShift) : ArithmeticFunction ℂ :=
  d4BMDivisorProductArithmetic (a : ℂ) (b : ℂ) *
    d4BMSquarePowerArithmetic (a : ℂ) (b : ℂ)

def d4BMFourZetaArithmetic
    (a b : D4BMNegativeDivisorShift) : ArithmeticFunction ℂ :=
  (((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * d4BMPowerArithmetic (a : ℂ)) *
      d4BMPowerArithmetic (b : ℂ)) *
    d4BMPowerArithmetic ((a : ℂ) + (b : ℂ))

lemma d4BMRamanujanCorrectedArithmetic_isMultiplicative
    (a b : D4BMNegativeDivisorShift) :
    (d4BMRamanujanCorrectedArithmetic a b).IsMultiplicative :=
  (d4BMDivisorProductArithmetic_isMultiplicative (a : ℂ) (b : ℂ)).mul
    (d4BMSquarePowerArithmetic_isMultiplicative (a : ℂ) (b : ℂ))

lemma d4BMFourZetaArithmetic_isMultiplicative
    (a b : D4BMNegativeDivisorShift) :
    (d4BMFourZetaArithmetic a b).IsMultiplicative :=
  ((ArithmeticFunction.isMultiplicative_zeta.natCast.mul
    (d4BMPowerArithmetic_isMultiplicative (a : ℂ))).mul
    (d4BMPowerArithmetic_isMultiplicative (b : ℂ))).mul
    (d4BMPowerArithmetic_isMultiplicative ((a : ℂ) + (b : ℂ)))

lemma localAFSeries_d4BMRamanujanCorrectedArithmetic
    (a b : D4BMNegativeDivisorShift) {p : ℕ} (hp : p.Prime) :
    localAFSeries (d4BMRamanujanCorrectedArithmetic a b) p =
      geomSeries 1 * geomSeries ((p : ℂ) ^ (a : ℂ)) *
        geomSeries ((p : ℂ) ^ (b : ℂ)) *
          geomSeries (((p : ℂ) ^ (a : ℂ)) * ((p : ℂ) ^ (b : ℂ))) := by
  rw [d4BMRamanujanCorrectedArithmetic, localAFSeries_mul _ _ hp,
    localAFSeries_d4BMDivisorProductArithmetic (a : ℂ) (b : ℂ) hp,
    localAFSeries_d4BMSquarePowerArithmetic (a : ℂ) (b : ℂ) hp,
    divisorPairSeries_mul_squareGeomSeries _ _
      (a.natCast_cpow_ne_one hp) (b.natCast_cpow_ne_one hp)]

lemma localAFSeries_d4BMFourZetaArithmetic
    (a b : D4BMNegativeDivisorShift) {p : ℕ} (hp : p.Prime) :
    localAFSeries (d4BMFourZetaArithmetic a b) p =
      geomSeries 1 * geomSeries ((p : ℂ) ^ (a : ℂ)) *
        geomSeries ((p : ℂ) ^ (b : ℂ)) *
          geomSeries (((p : ℂ) ^ (a : ℂ)) * ((p : ℂ) ^ (b : ℂ))) := by
  rw [d4BMFourZetaArithmetic,
    localAFSeries_mul _ _ hp, localAFSeries_mul _ _ hp,
    localAFSeries_mul _ _ hp, localAFSeries_zeta hp,
    localAFSeries_d4BMPowerArithmetic (a : ℂ) hp,
    localAFSeries_d4BMPowerArithmetic (b : ℂ) hp,
    localAFSeries_d4BMPowerArithmetic ((a : ℂ) + (b : ℂ)) hp,
    Complex.cpow_add (a : ℂ) (b : ℂ) (Nat.cast_ne_zero.mpr hp.ne_zero)]

theorem d4BMRamanujanCorrectedArithmetic_eq_fourZetaArithmetic
    (a b : D4BMNegativeDivisorShift) :
    d4BMRamanujanCorrectedArithmetic a b = d4BMFourZetaArithmetic a b := by
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
    (d4BMRamanujanCorrectedArithmetic a b)
    (d4BMRamanujanCorrectedArithmetic_isMultiplicative a b)
    (d4BMFourZetaArithmetic a b)
    (d4BMFourZetaArithmetic_isMultiplicative a b)]
  intro p e hp
  have hlocal := (localAFSeries_d4BMRamanujanCorrectedArithmetic a b hp).trans
    (localAFSeries_d4BMFourZetaArithmetic a b hp).symm
  have hcoeff := congrArg (PowerSeries.coeff e) hlocal
  simpa [localAFSeries, PowerSeries.coeff_mk] using hcoeff

lemma D4BMNegativeDivisorShift.norm_powerArithmetic_le_one
    (a : D4BMNegativeDivisorShift) {n : ℕ} (hn : n ≠ 0) :
    ‖d4BMPowerArithmetic (a : ℂ) n‖ ≤ 1 := by
  rw [d4BMPowerArithmetic_apply]
  simp only [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
    if_neg hn, Nat.cast_one, one_mul]
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  calc
    (n : ℝ) ^ (a : ℂ).re ≤ (n : ℝ) ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)) (le_of_lt a.re_neg)
    _ = 1 := by simp

lemma D4BMNegativeDivisorShift.norm_generalizedDivisorArithmetic_le_card
    (a : D4BMNegativeDivisorShift) {n : ℕ} (hn : n ≠ 0) :
    ‖d4BMGeneralizedDivisorArithmetic (a : ℂ) n‖ ≤ n.divisors.card := by
  rw [d4BMGeneralizedDivisorArithmetic, ArithmeticFunction.mul_apply]
  calc
    ‖∑ x ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.zeta : ArithmeticFunction ℂ) x.1 *
          d4BMPowerArithmetic (a : ℂ) x.2‖
        ≤ ∑ _x ∈ n.divisorsAntidiagonal, (1 : ℝ) := by
          apply norm_sum_le_of_le
          intro x hx
          rw [Nat.mem_divisorsAntidiagonal] at hx
          have hx1 : x.1 ≠ 0 := by
            intro h
            rw [h, zero_mul] at hx
            exact hn hx.1.symm
          have hx2 : x.2 ≠ 0 := by
            intro h
            rw [h, mul_zero] at hx
            exact hn hx.1.symm
          rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
            if_neg hx1, Nat.cast_one, one_mul]
          exact a.norm_powerArithmetic_le_one hx2
    _ = n.divisors.card := by
      simp [RHTower.Sieve.card_divisorsAntidiagonal]

lemma norm_d4BMDivisorProductArithmetic_le_divisorSquare
    (a b : D4BMNegativeDivisorShift) (n : ℕ) :
    ‖d4BMDivisorProductArithmetic (a : ℂ) (b : ℂ) n‖ ≤
      ‖((n.divisors.card ^ 2 : ℕ) : ℂ)‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero, norm_zero]
    exact norm_nonneg _
  · rw [d4BMDivisorProductArithmetic_apply, norm_mul, Complex.norm_natCast]
    calc
      ‖d4BMGeneralizedDivisorArithmetic (a : ℂ) n‖ *
            ‖d4BMGeneralizedDivisorArithmetic (b : ℂ) n‖
          ≤ (n.divisors.card : ℝ) * (n.divisors.card : ℝ) :=
        mul_le_mul
          (a.norm_generalizedDivisorArithmetic_le_card hn)
          (b.norm_generalizedDivisorArithmetic_le_card hn)
          (norm_nonneg _) (Nat.cast_nonneg _)
      _ = ((n.divisors.card ^ 2 : ℕ) : ℝ) := by norm_num [pow_two]

theorem d4BMDivisorProductArithmetic_LSeriesSummable
    (a b : D4BMNegativeDivisorShift) {w : ℂ} (hw : 1 < w.re) :
    LSeriesSummable (d4BMDivisorProductArithmetic (a : ℂ) (b : ℂ)) w := by
  have hmajor := RHTower.Sieve.divisorSquareLSeriesSummable hw
  apply summable_norm_iff.mp
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => LSeries.norm_term_le w
      (norm_d4BMDivisorProductArithmetic_le_divisorSquare a b n))
    (summable_norm_iff.mpr hmajor)

private theorem d4BMPowerArithmetic_LSeriesSummable_of_one_lt_re
    (a w : ℂ) (h : 1 < (w - a).re) :
    LSeriesSummable (d4BMPowerArithmetic a) w := by
  change LSeriesSummable
    (GaloisForLFunctions.lseriesPowerTwistCoeff
      (fun n => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) a) w
  rw [GaloisForLFunctions.LSeriesSummable_powerTwist]
  exact ArithmeticFunction.LSeriesSummable_zeta_iff.mpr h

private theorem LSeries_d4BMPowerArithmetic_eq_riemannZeta
    (a w : ℂ) (h : 1 < (w - a).re) :
    LSeries (d4BMPowerArithmetic a) w = riemannZeta (w - a) := by
  change LSeries
    (GaloisForLFunctions.lseriesPowerTwistCoeff
      (fun n => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) a) w = _
  rw [GaloisForLFunctions.LSeries_powerTwist]
  exact ArithmeticFunction.LSeries_zeta_eq_riemannZeta h

private theorem d4BMPowerArithmetic_LSeriesHasSum_of_one_lt_re
    (a w : ℂ) (h : 1 < (w - a).re) :
    LSeriesHasSum (d4BMPowerArithmetic a) w (riemannZeta (w - a)) := by
  have hsum := (d4BMPowerArithmetic_LSeriesSummable_of_one_lt_re a w h).LSeriesHasSum
  rw [LSeries_d4BMPowerArithmetic_eq_riemannZeta a w h] at hsum
  exact hsum

structure D4BMRamanujanProductChamber where
  a : D4BMNegativeDivisorShift
  b : D4BMNegativeDivisorShift
  w : ℂ
  w_re_gt_one : 1 < w.re

lemma D4BMRamanujanProductChamber.w_sub_a_re_gt_one
    (P : D4BMRamanujanProductChamber) :
    1 < (P.w - (P.a : ℂ)).re := by
  simp only [Complex.sub_re]
  linarith [P.a.re_neg, P.w_re_gt_one]

lemma D4BMRamanujanProductChamber.w_sub_b_re_gt_one
    (P : D4BMRamanujanProductChamber) :
    1 < (P.w - (P.b : ℂ)).re := by
  simp only [Complex.sub_re]
  linarith [P.b.re_neg, P.w_re_gt_one]

lemma D4BMRamanujanProductChamber.w_sub_a_sub_b_re_gt_one
    (P : D4BMRamanujanProductChamber) :
    1 < (P.w - (P.a : ℂ) - (P.b : ℂ)).re := by
  simp only [Complex.sub_re]
  linarith [P.a.re_neg, P.b.re_neg, P.w_re_gt_one]

lemma D4BMRamanujanProductChamber.two_w_sub_a_sub_b_re_gt_one
    (P : D4BMRamanujanProductChamber) :
    1 < (2 * P.w - (P.a : ℂ) - (P.b : ℂ)).re := by
  norm_num [Complex.mul_re, Complex.sub_re]
  linarith [P.a.re_neg, P.b.re_neg, P.w_re_gt_one]

lemma d4BMSquarePowerArithmetic_LSeriesHasSum
    (P : D4BMRamanujanProductChamber) :
    LSeriesHasSum
      (d4BMSquarePowerArithmetic (P.a : ℂ) (P.b : ℂ)) P.w
      (riemannZeta (2 * P.w - (P.a : ℂ) - (P.b : ℂ))) := by
  have hshift :
      1 < (((2 : ℕ) : ℂ) * P.w - ((P.a : ℂ) + (P.b : ℂ))).re := by
    norm_num [Complex.mul_re, Complex.sub_re]
    linarith [P.a.re_neg, P.b.re_neg, P.w_re_gt_one]
  have hpower := d4BMPowerArithmetic_LSeriesHasSum_of_one_lt_re
    ((P.a : ℂ) + (P.b : ℂ)) (((2 : ℕ) : ℂ) * P.w) hshift
  have hsummable :
      LSeriesSummable
        (d4BMSquarePowerArithmetic (P.a : ℂ) (P.b : ℂ)) P.w := by
    rw [d4BMSquarePowerArithmetic,
      LSeriesSummable_mPart_iff two_ne_zero]
    exact hpower.LSeriesSummable
  have hsum := hsummable.LSeriesHasSum
  rw [d4BMSquarePowerArithmetic, LSeries_mPart two_ne_zero] at hsum
  rw [hpower.LSeries_eq] at hsum
  convert hsum using 1
  · rfl
  · congr 1
    ring

lemma D4BMRamanujanProductChamber.w_sub_add_re_gt_one
    (P : D4BMRamanujanProductChamber) :
    1 < (P.w - ((P.a : ℂ) + (P.b : ℂ))).re := by
  simp only [Complex.sub_re, Complex.add_re]
  linarith [P.a.re_neg, P.b.re_neg, P.w_re_gt_one]

def d4BMRamanujanFourZetaValue (P : D4BMRamanujanProductChamber) : ℂ :=
  riemannZeta P.w * riemannZeta (P.w - (P.a : ℂ)) *
    riemannZeta (P.w - (P.b : ℂ)) *
      riemannZeta (P.w - ((P.a : ℂ) + (P.b : ℂ)))

def d4BMRamanujanPolarZetaValue (P : D4BMRamanujanProductChamber) : ℂ :=
  riemannZeta (2 * P.w - (P.a : ℂ) - (P.b : ℂ))

lemma d4BMRamanujanCorrectedArithmetic_LSeriesHasSum
    (P : D4BMRamanujanProductChamber) :
    LSeriesHasSum (d4BMRamanujanCorrectedArithmetic P.a P.b) P.w
      (LSeries (d4BMDivisorProductArithmetic (P.a : ℂ) (P.b : ℂ)) P.w *
        d4BMRamanujanPolarZetaValue P) := by
  have hdiv :=
    (d4BMDivisorProductArithmetic_LSeriesSummable P.a P.b P.w_re_gt_one).LSeriesHasSum
  have hsquare := d4BMSquarePowerArithmetic_LSeriesHasSum P
  have hleft := ArithmeticFunction.LSeriesHasSum_mul hdiv hsquare
  simpa only [d4BMRamanujanCorrectedArithmetic,
    d4BMRamanujanPolarZetaValue] using hleft

lemma d4BMFourZetaArithmetic_LSeriesSummable
    (P : D4BMRamanujanProductChamber) :
    LSeriesSummable (d4BMFourZetaArithmetic P.a P.b) P.w := by
  have hzeta : LSeriesSummable
      (ArithmeticFunction.zeta : ArithmeticFunction ℂ) P.w :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr P.w_re_gt_one
  have ha := d4BMPowerArithmetic_LSeriesSummable_of_one_lt_re
    (P.a : ℂ) P.w P.w_sub_a_re_gt_one
  have hb := d4BMPowerArithmetic_LSeriesSummable_of_one_lt_re
    (P.b : ℂ) P.w P.w_sub_b_re_gt_one
  have hab := d4BMPowerArithmetic_LSeriesSummable_of_one_lt_re
    ((P.a : ℂ) + (P.b : ℂ)) P.w P.w_sub_add_re_gt_one
  exact ArithmeticFunction.LSeriesSummable_mul
    (ArithmeticFunction.LSeriesSummable_mul
      (ArithmeticFunction.LSeriesSummable_mul hzeta ha) hb) hab

lemma LSeries_d4BMFourZetaArithmetic_eq_value
    (P : D4BMRamanujanProductChamber) :
    LSeries (d4BMFourZetaArithmetic P.a P.b) P.w =
      d4BMRamanujanFourZetaValue P := by
  have hzeta : LSeriesSummable
      (ArithmeticFunction.zeta : ArithmeticFunction ℂ) P.w :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr P.w_re_gt_one
  have ha := d4BMPowerArithmetic_LSeriesSummable_of_one_lt_re
    (P.a : ℂ) P.w P.w_sub_a_re_gt_one
  have hb := d4BMPowerArithmetic_LSeriesSummable_of_one_lt_re
    (P.b : ℂ) P.w P.w_sub_b_re_gt_one
  have hab := d4BMPowerArithmetic_LSeriesSummable_of_one_lt_re
    ((P.a : ℂ) + (P.b : ℂ)) P.w P.w_sub_add_re_gt_one
  have hzetaValue :
      LSeries (ArithmeticFunction.zeta : ArithmeticFunction ℂ) P.w =
        riemannZeta P.w := by
    change LSeries (fun n => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) P.w = _
    rw [show (fun n => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) =
        (fun n => ((ArithmeticFunction.zeta n : ℕ) : ℂ)) by
      funext n
      simp [ArithmeticFunction.zeta_apply]]
    exact ArithmeticFunction.LSeries_zeta_eq_riemannZeta P.w_re_gt_one
  rw [d4BMFourZetaArithmetic,
    ArithmeticFunction.LSeries_mul'
      (ArithmeticFunction.LSeriesSummable_mul
        (ArithmeticFunction.LSeriesSummable_mul hzeta ha) hb) hab,
    ArithmeticFunction.LSeries_mul'
      (ArithmeticFunction.LSeriesSummable_mul hzeta ha) hb,
    ArithmeticFunction.LSeries_mul' hzeta ha,
    hzetaValue,
    LSeries_d4BMPowerArithmetic_eq_riemannZeta
      (P.a : ℂ) P.w P.w_sub_a_re_gt_one,
    LSeries_d4BMPowerArithmetic_eq_riemannZeta
      (P.b : ℂ) P.w P.w_sub_b_re_gt_one,
    LSeries_d4BMPowerArithmetic_eq_riemannZeta
      ((P.a : ℂ) + (P.b : ℂ)) P.w P.w_sub_add_re_gt_one]
  rfl

lemma d4BMFourZetaArithmetic_LSeriesHasSum
    (P : D4BMRamanujanProductChamber) :
    LSeriesHasSum (d4BMFourZetaArithmetic P.a P.b) P.w
      (d4BMRamanujanFourZetaValue P) := by
  have hsum := (d4BMFourZetaArithmetic_LSeriesSummable P).LSeriesHasSum
  rw [LSeries_d4BMFourZetaArithmetic_eq_value P] at hsum
  exact hsum

theorem d4BMDivisorProductArithmetic_LSeries_mul_polarZeta
    (P : D4BMRamanujanProductChamber) :
    LSeries (d4BMDivisorProductArithmetic (P.a : ℂ) (P.b : ℂ)) P.w *
      d4BMRamanujanPolarZetaValue P = d4BMRamanujanFourZetaValue P := by
  have hleft := d4BMRamanujanCorrectedArithmetic_LSeriesHasSum P
  rw [d4BMRamanujanCorrectedArithmetic_eq_fourZetaArithmetic P.a P.b] at hleft
  exact hleft.unique (d4BMFourZetaArithmetic_LSeriesHasSum P)

theorem LSeries_d4BMDivisorProductArithmetic_eq_fourZetaQuotient
    (P : D4BMRamanujanProductChamber) :
    LSeries (d4BMDivisorProductArithmetic (P.a : ℂ) (P.b : ℂ)) P.w =
      d4BMRamanujanFourZetaValue P / d4BMRamanujanPolarZetaValue P := by
  have hden : d4BMRamanujanPolarZetaValue P ≠ 0 := by
    exact riemannZeta_ne_zero_of_one_lt_re P.two_w_sub_a_sub_b_re_gt_one
  exact (eq_div_iff hden).2 (d4BMDivisorProductArithmetic_LSeries_mul_polarZeta P)

end
end RHTower

