import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.SquarefreeDivisorCounts
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticFormalEulerProduct
import GaloisForLFunctions.ArithmeticCompensationTheory.TheReceiverOfACurveIsAdmittedAboveTheZeroWidth

/-!
# Square-root cancellation of actual elliptic divisor counts

The closed places of the elliptic curve over the three-element field define
finite sets of squarefree divisors, with infinity retained. Their even and
odd support counts differ by the inverse Euler coefficient. Actual curve
rationality and the proved Frobenius root bound give square-root exponential
bounds both in each degree and through every degree cutoff.
-/

noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open Finset PowerSeries
open GaloisForLFunctions
open ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open ArithmeticCompensationTheory

/-- The reciprocal series comes from the actual closed-place product. -/
theorem ellipticEulerProduct_eq_inverseRoots :
    ellipticEulerProduct = (1 - X) * (1 - C 3 * X) * curvePinv datum.alpha := by
  have hZE : zeta * ellipticEulerProduct = 1 := by
    rw [← ellipticEulerProduct_inv_eq_zeta]
    exact invOfUnit_mul ellipticEulerProduct 1 ellipticEulerProduct_constantCoeff
  have hPI : (numerator : PowerSeries ℂ) * curvePinv datum.alpha = 1 := by
    rw [numeratorSeries_eq]
    change (∏ i : FrobeniusIndex, (1 - C (datum.alpha i) * X)) *
      (∏ i : FrobeniusIndex, geomSeries (datum.alpha i)) = 1
    rw [← prod_mul_distrib]
    exact prod_eq_one fun i _ => one_sub_mul_geomSeries (datum.alpha i)
  calc
    ellipticEulerProduct = ((numerator : PowerSeries ℂ) * curvePinv datum.alpha) * ellipticEulerProduct := by rw [hPI, one_mul]
    _ = ((1 - X) * (1 - C 3 * X) * zeta) * curvePinv datum.alpha * ellipticEulerProduct := by rw [zeta_rational]
    _ = ((1 - X) * (1 - C 3 * X) * curvePinv datum.alpha) * (zeta * ellipticEulerProduct) := by ring
    _ = (1 - X) * (1 - C 3 * X) * curvePinv datum.alpha := by rw [hZE, mul_one]

/-- The actual inverse Euler coefficients have square-root exponential scale. -/
theorem norm_coeff_ellipticEulerProduct_le (n : ℕ) :
    ‖coeff n ellipticEulerProduct‖ ≤ 8 * ((n : ℝ) + 1) ^ 2 * (Real.sqrt 3) ^ n := by
  have ht : (1 : ℝ) ≤ Real.sqrt 3 := by
    exact (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hm : (RHTower.Hyperelliptic.lRoots cubic).toList.length = 2 := by
    simpa only [FrobeniusIndex, Fintype.card_fin] using card_frobeniusIndex
  have hp (k : ℕ) : ‖coeff k (curvePinv datum.alpha)‖ ≤
      1 * ((k : ℝ) + 1) ^ 2 * (Real.sqrt 3) ^ k := by
    simpa only [hm, one_mul] using
      norm_coeff_curvePinv_le datum.alpha (Real.sqrt_nonneg 3) (fun i => (norm_alpha i).le) k
  have h3 (k : ℕ) : ‖coeff k ((1 - C (3 : ℂ) * X) * curvePinv datum.alpha)‖ ≤
      4 * ((k : ℝ) + 1) ^ 2 * (Real.sqrt 3) ^ k := by
    convert norm_coeff_one_sub_mul_le (m := 2) (K := 1) (c := 3)
      (by norm_num) ht (by norm_num) hp k using 1 <;> norm_num
  have h1 := norm_coeff_one_sub_mul_le (m := 2) (K := 4) (c := 1) (by norm_num) ht (by norm_num) h3 n
  rw [ellipticEulerProduct_eq_inverseRoots, mul_assoc]
  norm_num only [Complex.ofReal_one, map_one, one_mul] at h1
  convert h1 using 1

#print axioms ellipticEulerProduct_eq_inverseRoots
#print axioms norm_coeff_ellipticEulerProduct_le
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open Finset PowerSeries IsDedekindDomain
open GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open _root_.RHTower

/-- Actual affine closed places with the unique point at infinity. -/
abbrev EllipticPlace := Option (HeightOneSpectrum A)

/-- Residue degree, with degree one at infinity. -/
def ellipticPlaceDegree : EllipticPlace → ℕ
  | none => 1
  | some v => affinePlaceDegree v

/-- Every place capable of contributing to degree n, together with infinity. -/
def ellipticPlaceCutoff (n : ℕ) : Finset EllipticPlace := by
  classical
  exact insert none ((affinePlacesDegreeLe n).image some)

/-- Every place in a divisor lies below its total degree. -/
theorem elliptic_divisor_support_subset (T : Finset EllipticPlace) (n : ℕ)
    (h : ∑ v ∈ T, ellipticPlaceDegree v ≤ n) : T ⊆ ellipticPlaceCutoff n := by
  classical
  intro v hv
  cases v with
  | none => exact mem_insert_self _ _
  | some v =>
    apply mem_insert_of_mem
    apply mem_image.mpr
    refine ⟨v, ?_, rfl⟩
    rw [mem_affinePlacesDegreeLe]
    exact (single_le_sum (fun w _ => Nat.zero_le (ellipticPlaceDegree w)) hv).trans h

/-- The cutoff omits no squarefree divisor of the prescribed degree. -/
theorem mem_ellipticDegreeSubsets_iff (T : Finset EllipticPlace) (n : ℕ) :
    T ∈ squarefreeDegreeSubsets (ellipticPlaceCutoff n) ellipticPlaceDegree n ↔
      ∑ v ∈ T, ellipticPlaceDegree v = n := by
  classical
  rw [squarefreeDegreeSubsets, mem_filter, mem_powerset]
  exact ⟨And.right, fun h => ⟨elliptic_divisor_support_subset T n h.le, h⟩⟩

/-- The literal finite place product retains the infinity factor. -/
theorem ellipticPlace_product (n : ℕ) :
    (∏ v ∈ ellipticPlaceCutoff n, (1 - (X : PowerSeries ℂ) ^ ellipticPlaceDegree v)) =
      ellipticEulerPartial n := by
  classical
  rw [ellipticPlaceCutoff, prod_insert (by simp)]
  rw [prod_image (by intro a _ b _ h; exact Option.some.inj h)]
  simp only [ellipticPlaceDegree, pow_one, ellipticEulerPartial,
    affineEulerFactor, deningerBigWittFactor, map_one, one_mul]

/-- Actual even-support divisors of degree n on the elliptic curve. -/
def ellipticEvenDivisorCount (n : ℕ) : ℕ := by
  classical
  exact evenSquarefreeDivisorCount (ellipticPlaceCutoff n) ellipticPlaceDegree n

/-- Actual odd-support divisors of degree n on the elliptic curve. -/
def ellipticOddDivisorCount (n : ℕ) : ℕ := by
  classical
  exact oddSquarefreeDivisorCount (ellipticPlaceCutoff n) ellipticPlaceDegree n

/-- The Euler coefficient is obtained by counting actual finite subsets of closed places. -/
theorem coeff_ellipticEulerProduct_eq_counts (n : ℕ) :
    coeff n ellipticEulerProduct =
      (ellipticEvenDivisorCount n : ℂ) - ellipticOddDivisorCount n := by
  classical
  rw [ellipticEulerProduct_coeff, ← ellipticPlace_product,
    coeff_squarefreeEuler_eq_counts]
  rfl

/-- Signed cancellation of actual arithmetic counts at square-root exponential scale. -/
theorem elliptic_signed_divisor_count_bound (n : ℕ) :
    |(ellipticEvenDivisorCount n : ℝ) - ellipticOddDivisorCount n| ≤
      8 * ((n : ℝ) + 1) ^ 2 * (Real.sqrt 3) ^ n := by
  have h := norm_coeff_ellipticEulerProduct_le n
  rw [coeff_ellipticEulerProduct_eq_counts] at h
  have he : (ellipticEvenDivisorCount n : ℂ) - ellipticOddDivisorCount n =
      (((ellipticEvenDivisorCount n : ℝ) - ellipticOddDivisorCount n : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- Cancellation persists for the actual divisor cutoff, after summing degree strata. -/
theorem elliptic_signed_divisor_prefix_bound (n : ℕ) :
    |∑ k ∈ range (n + 1),
      ((ellipticEvenDivisorCount k : ℝ) - ellipticOddDivisorCount k)| ≤
      24 * ((n : ℝ) + 1) ^ 2 * (Real.sqrt 3) ^ n := by
  have ht : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg 3
  have h3 : (3 : ℝ) ≤ 2 * Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hg (m : ℕ) : ∑ k ∈ range (m + 1), (Real.sqrt 3) ^ k ≤ 3 * (Real.sqrt 3) ^ m := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hm := mul_nonneg (sub_nonneg.mpr h3) (pow_nonneg ht m)
      simp only [pow_succ]
      nlinarith only [ih, hm]
  calc
    _ ≤ ∑ k ∈ range (n + 1),
        |(ellipticEvenDivisorCount k : ℝ) - ellipticOddDivisorCount k| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range (n + 1), 8 * ((n : ℝ) + 1) ^ 2 * (Real.sqrt 3) ^ k := by
      apply sum_le_sum
      intro k hk
      have hkn : k ≤ n := Nat.le_of_lt_succ (mem_range.mp hk)
      have hp : ((k : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hkn 1) 2
      exact (elliptic_signed_divisor_count_bound k).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num))
          (pow_nonneg ht k))
    _ = 8 * ((n : ℝ) + 1) ^ 2 * ∑ k ∈ range (n + 1), (Real.sqrt 3) ^ k := by rw [mul_sum]
    _ ≤ 8 * ((n : ℝ) + 1) ^ 2 * (3 * (Real.sqrt 3) ^ n) :=
      mul_le_mul_of_nonneg_left (hg n) (by positivity)
    _ = 24 * ((n : ℝ) + 1) ^ 2 * (Real.sqrt 3) ^ n := by ring

#print axioms elliptic_signed_divisor_prefix_bound
#print axioms elliptic_divisor_support_subset
#print axioms mem_ellipticDegreeSubsets_iff
#print axioms ellipticPlace_product
#print axioms coeff_ellipticEulerProduct_eq_counts
#print axioms elliptic_signed_divisor_count_bound

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
