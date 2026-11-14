import GaloisForLFunctions.KodairaParshinAbc.Legendre.BranchPolynomials
import GaloisForLFunctions.HTGeometry.Polynomial.MonicDegreeIndependence
import Mathlib.Data.ZMod.Basic

/-!
# Coefficient recovery through the Legendre map

The polynomials `L^(3k) D^(d-k)` are monic of distinct degrees `4d+2k`. Their
coefficient map is therefore injective over every nonzero commutative ring, including
rings modulo prime powers. Restoring the factors `256^k` gives the ordinary
denominator-cleared pullback through `j = 256 L³/D` whenever `256` is a unit,
in particular modulo every power of an odd modulus.
-/

noncomputable section

namespace GaloisForLFunctions.KodairaParshinAbc.Legendre

open Polynomial

variable {R : Type*} [CommRing R] [Nontrivial R]

theorem quadratic_natDegree : (quadratic : R[X]).natDegree = 2 := by
  simpa only [map_one, map_neg, neg_mul, one_mul, sub_eq_add_neg, quadratic] using
    (Polynomial.natDegree_quadratic (a := (1 : R)) (b := -1) (c := 1) one_ne_zero)

theorem quadratic_monic : (quadratic : R[X]).Monic := by
  change (quadratic : R[X]).leadingCoeff = 1
  simpa only [map_one, map_neg, neg_mul, one_mul, sub_eq_add_neg, quadratic] using
    (Polynomial.leadingCoeff_quadratic (a := (1 : R)) (b := -1) (c := 1) one_ne_zero)

omit [Nontrivial R] in
theorem denominator_monic : (denominator : R[X]).Monic := by
  exact (monic_X.pow 2).mul (by simpa only [map_one] using (monic_X_sub_C (1 : R)).pow 2)

theorem denominator_natDegree : (denominator : R[X]).natDegree = 4 := by
  have h : (X - (1 : R[X])).Monic := by simpa only [map_one] using monic_X_sub_C (1 : R)
  rw [denominator, (monic_X.pow 2).natDegree_mul (h.pow 2), monic_X.natDegree_pow,
    h.natDegree_pow, natDegree_X]
  have hx : (X - (1 : R[X])).natDegree = 1 := by
    simpa only [map_one] using natDegree_X_sub_C (1 : R)
  rw [hx]

/-- Normalized denominator-cleared monomials of degree at most `d`. -/
def descentBasis (d : ℕ) (k : Fin (d + 1)) : R[X] :=
  quadratic ^ (3 * (k : ℕ)) * denominator ^ (d - (k : ℕ))

theorem descentBasis_monic (d : ℕ) (k : Fin (d + 1)) :
    (descentBasis d k : R[X]).Monic :=
  (quadratic_monic.pow _).mul (denominator_monic.pow _)

/-- The two-degree spacing is the source of exact coefficient recovery. -/
theorem descentBasis_natDegree (d : ℕ) (k : Fin (d + 1)) :
    (descentBasis d k : R[X]).natDegree = 4 * d + 2 * (k : ℕ) := by
  rw [descentBasis, ((quadratic_monic (R := R)).pow _).natDegree_mul
    ((denominator_monic (R := R)).pow _), quadratic_monic.natDegree_pow,
    denominator_monic.natDegree_pow, quadratic_natDegree, denominator_natDegree]
  have hk := k.isLt
  omega

/-- Independence holds over rings with zero divisors as well as fields. -/
theorem descentBasis_linearIndependent (d : ℕ) :
    LinearIndependent R (descentBasis (R := R) d) := by
  apply linearIndependent_monic_of_natDegree_injective (descentBasis_monic d)
  intro i j h
  change (descentBasis d i : R[X]).natDegree = (descentBasis d j : R[X]).natDegree at h
  rw [descentBasis_natDegree, descentBasis_natDegree] at h
  apply Fin.ext
  omega

def descentPolynomial (d : ℕ) (c : Fin (d + 1) → R) : R[X] :=
  ∑ k, c k • descentBasis d k

/-- The polynomial on the Legendre cover uniquely determines every normalized coefficient. -/
theorem descentPolynomial_injective (d : ℕ) :
    Function.Injective (descentPolynomial (R := R) d) := by
  intro c b h
  have hz : ∑ k, (c k - b k) • (descentBasis d k : R[X]) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr h
  have hc := (Fintype.linearIndependent_iff.mp (descentBasis_linearIndependent (R := R) d))
    (fun k => c k - b k) hz
  funext k
  exact sub_eq_zero.mp (hc k)

/-- The actual coefficient map for `D^d Q(256 L³/D)`. -/
def invariantPullback (d : ℕ) (c : Fin (d + 1) → R) : R[X] :=
  descentPolynomial d (fun k => c k * 256 ^ (k : ℕ))

omit [Nontrivial R] in
/-- The normalized basis is exactly the denominator-cleared polynomial substitution. -/
theorem invariantPullback_eq_sum (d : ℕ) (c : Fin (d + 1) → R) :
    invariantPullback d c =
      ∑ k, C (c k) * numerator ^ (k : ℕ) * denominator ^ (d - (k : ℕ)) := by
  rw [invariantPullback, descentPolynomial]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [descentBasis, smul_eq_C_mul,
    map_mul, map_pow, map_ofNat, numerator, mul_pow, pow_mul]
  ring

/-- An invertible leading scalar preserves coefficient recovery over arbitrary rings. -/
theorem invariantPullback_injective_of_isUnit (h256 : IsUnit (256 : R)) (d : ℕ) :
    Function.Injective (invariantPullback (R := R) d) := by
  intro c b h
  have hc := descentPolynomial_injective d h
  obtain ⟨u, hu⟩ := h256
  funext k
  have hinv : (256 : R) ^ (k : ℕ) * (↑(u⁻¹) : R) ^ (k : ℕ) = 1 := by
    rw [← hu, ← mul_pow]
    simp only [Units.mul_inv, one_pow]
  calc
    c k = c k * ((256 : R) ^ (k : ℕ) * (↑(u⁻¹) : R) ^ (k : ℕ)) := by rw [hinv, mul_one]
    _ = b k * ((256 : R) ^ (k : ℕ) * (↑(u⁻¹) : R) ^ (k : ℕ)) := by
      rw [← mul_assoc, congrFun hc k, mul_assoc]
    _ = b k := by rw [hinv, mul_one]

section Field

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- Evaluation recovers `D^d Q(j)` at every nonsingular Legendre parameter. -/
theorem invariantPullback_eval (d : ℕ) (c : Fin (d + 1) → K) (t : K)
    (ht : (denominator : K[X]).eval t ≠ 0) :
    (invariantPullback d c).eval t =
      (denominator.eval t) ^ d *
        ∑ k, c k * (numerator.eval t / denominator.eval t) ^ (k : ℕ) := by
  rw [invariantPullback_eq_sum, eval_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [eval_mul, eval_C, eval_pow, div_pow]
  have hd : d - (k : ℕ) + (k : ℕ) = d := by omega
  have hp := pow_add (denominator.eval t) (d - (k : ℕ)) (k : ℕ)
  rw [hd] at hp
  rw [hp]
  field_simp [ht]

/-- Pullback through the degree-six invariant loses no polynomial coefficient. -/
theorem invariantPullback_injective (d : ℕ) :
    Function.Injective (invariantPullback (R := K) d) :=
  invariantPullback_injective_of_isUnit (isUnit_iff_ne_zero.mpr (by norm_num)) d

end Field

/-- Coefficient recovery survives arbitrary precision modulo every odd modulus. -/
theorem invariantPullback_oddPower_injective (q s d : ℕ) :
    Function.Injective (invariantPullback (R := ZMod ((2 * q + 1) ^ s)) d) := by
  nontriviality (ZMod ((2 * q + 1) ^ s))
  have ho : Odd ((2 * q + 1) ^ s) :=
    (show Odd (2 * q + 1) from ⟨q, by omega⟩).pow
  obtain ⟨r, hr⟩ := ho
  have hm : (2 : ZMod ((2 * q + 1) ^ s)) * r + 1 = 0 := by
    have h := ZMod.natCast_self ((2 * q + 1) ^ s)
    have hc := congrArg (fun m : ℕ => (m : ZMod ((2 * q + 1) ^ s))) hr
    push_cast at h hc
    linear_combination h - hc
  have hi : (2 : ZMod ((2 * q + 1) ^ s)) * (-(r : ZMod ((2 * q + 1) ^ s))) = 1 := by
    linear_combination -hm
  have hu : IsUnit (2 : ZMod ((2 * q + 1) ^ s)) :=
    ⟨⟨2, -r, hi, by simpa only [mul_comm] using hi⟩, rfl⟩
  apply invariantPullback_injective_of_isUnit
  convert hu.pow 8 using 1
  norm_num

end GaloisForLFunctions.KodairaParshinAbc.Legendre
