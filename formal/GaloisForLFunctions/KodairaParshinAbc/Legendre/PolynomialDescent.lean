import GaloisForLFunctions.KodairaParshinAbc.Legendre.BranchPolynomials
import GaloisForLFunctions.HTGeometry.Polynomial.MonicDegreeIndependence

/-!
# Coefficient recovery through the Legendre map

The polynomials `L^(3k) D^(d-k)` are monic of distinct degrees `4d+2k`. Their
coefficient map is therefore injective over every nonzero commutative ring, including
rings modulo prime powers. Restoring the factors `256^k` gives the ordinary
denominator-cleared pullback through `j = 256 L³/D` in characteristic-zero fields.
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

/-- Pullback through the degree-six invariant loses no polynomial coefficient. -/
theorem invariantPullback_injective (d : ℕ) :
    Function.Injective (invariantPullback (R := K) d) :=
  invariantPullback_injective_of_isUnit (isUnit_iff_ne_zero.mpr (by norm_num)) d

end Field

end GaloisForLFunctions.KodairaParshinAbc.Legendre
