import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricDivisorDegree
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricPolynomialSections

/-!
# Common homogeneous denominators for prescribed Hermitian poles

For an effective Frobenius-invariant geometric divisor `D` of degree
`d<Q`, the explicit tangent product has divisor `(Q+1)D-d(Q+1)[infinity]`.
Multiplication by this function takes every function with poles bounded
by `(Q+1)D` into the proved bounded-pole polynomial expansion.

One homogeneous denominator of degree `d` therefore works for every such
nonzero function. The denominator and numerators have the literal section
divisors `(Q+1)D` and `(Q+1)D+div(f)`, respectively. Degree zero is allowed.
All divisors use the actual normalization primes and the infinity valuation.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open IsDedekindDomain

private theorem valuation_log_bound_iff {K : Type*} [Field K]
    (v : Valuation K (WithZero (Multiplicative ℤ))) (f : K) (hf : f ≠ 0) (m : ℤ) :
    0 ≤ -WithZero.log (v f) + m ↔ v f ≤ WithZero.exp m := by
  have hv : v f ≠ 0 := (map_ne_zero _).mpr hf
  calc
    0 ≤ -WithZero.log (v f) + m ↔ WithZero.log (v f) ≤ m := by omega
    _ ↔ v f ≤ WithZero.exp m := by
      rw [← WithZero.exp_le_exp, WithZero.exp_log hv]

variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "E" => HermitianGeometricConstants p s
local notation "H" => HermitianGeometricField p s
local notation "B" => HermitianGeometricNormalization p s
local notation "Div" => HermitianGeometricPlaceDivisor p s

/-- Each geometric point, including infinity, gives an effective divisor. -/
theorem hermitianGeometricPointDivisor_nonneg (P : HermitianGeometricPoint p s) :
    0 ≤ hermitianGeometricPointDivisor p s P := by
  classical
  cases P with
  | none =>
    change (0 : Div) ≤ (0, 1)
    exact ⟨le_refl 0, by norm_num⟩
  | some P =>
    constructor
    · intro w
      change 0 ≤ Finsupp.single (hermitianGeometricPointPrime p s P) (1 : ℤ) w
      simp only [Finsupp.single_apply]
      split_ifs <;> norm_num
    · exact le_refl 0

/-- Nonnegative geometric multiplicities give an effective divisor on the actual places. -/
theorem hermitianGeometricDivisorOfPoints_nonneg (D : HermitianGeometricPoint p s →₀ ℤ)
    (hD : ∀ P, 0 ≤ D P) : 0 ≤ hermitianGeometricDivisorOfPoints p s D := by
  unfold hermitianGeometricDivisorOfPoints Finsupp.sum
  apply Finset.sum_nonneg
  intro P _
  exact smul_nonneg (hD P) (hermitianGeometricPointDivisor_nonneg p s P)

/-- An effective geometric divisor has nonnegative degree. -/
theorem hermitianGeometricDivisorDegree_nonneg (D : HermitianGeometricPoint p s →₀ ℤ)
    (hD : ∀ P, 0 ≤ D P) : 0 ≤ hermitianGeometricDivisorDegree p s D := by
  unfold hermitianGeometricDivisorDegree Finsupp.sum
  exact Finset.sum_nonneg fun P _ => hD P

/-- Effectivity after adding an infinity divisor is exactly the corresponding pole bound. -/
theorem hermitianGeometricZeroPoleDivisor_add_infinity_nonneg_iff
    (f : H) (hf : f ≠ 0) (m : ℤ) :
    0 ≤ hermitianGeometricZeroPoleDivisor p s f + m • (0, 1) ↔
      (∀ w : HeightOneSpectrum B, w.valuation H f ≤ 1) ∧
        hermitianGeometricInfinityValuation p s f ≤ WithZero.exp m := by
  constructor
  · intro h
    constructor
    · intro w
      have hw : 0 ≤ -WithZero.log (w.valuation H f) + 0 := by
        simpa [hermitianGeometricZeroPoleDivisor, finiteValuationDivisor_apply] using h.1 w
      simpa only [WithZero.exp_zero] using (valuation_log_bound_iff (w.valuation H) f hf 0).mp hw
    · apply (valuation_log_bound_iff (hermitianGeometricInfinityValuation p s) f hf m).mp
      simpa [hermitianGeometricZeroPoleDivisor, smul_eq_mul] using h.2
  · intro h
    constructor
    · intro w
      have hw := (valuation_log_bound_iff (w.valuation H) f hf 0).mpr
        (by simpa only [WithZero.exp_zero] using h.1 w)
      simpa [hermitianGeometricZeroPoleDivisor, finiteValuationDivisor_apply] using hw
    · have hi := (valuation_log_bound_iff (hermitianGeometricInfinityValuation p s) f hf m).mpr h.2
      simpa [hermitianGeometricZeroPoleDivisor, smul_eq_mul] using hi

/-- The zero divisor of a section of degree `d`, including its contribution at infinity. -/
def hermitianGeometricSectionDivisor (d : ℕ) (F : MvPolynomial (Option Bool) E) : Div :=
  hermitianGeometricZeroPoleDivisor p s (hermitianGeometricSectionValue p s F) +
    ((d * (Q + 1) : ℕ) : ℤ) • (0, 1)

/-- A single degree-`d` denominator represents every nonzero function with poles bounded by `(Q+1)D`.
Its section divisor is `(Q+1)D`; each numerator has section divisor `(Q+1)D+div(f)`. -/
theorem hermitianGeometric_exists_common_homogeneousSections
    (D : HermitianGeometricPoint p s →₀ ℤ) (hD : ∀ P, 0 ≤ D P)
    (hFr : hermitianGeometricFrobeniusDivisor p s D = D)
    (d : ℕ) (hdeg : hermitianGeometricDivisorDegree p s D = (d : ℤ)) (hd : d < Q) :
    ∃ F₀ : MvPolynomial (Option Bool) E,
      F₀ ≠ 0 ∧ F₀.IsHomogeneous d ∧ hermitianGeometricSectionValue p s F₀ ≠ 0 ∧
        hermitianGeometricSectionDivisor p s d F₀ =
          ((Q + 1 : ℕ) : ℤ) • hermitianGeometricDivisorOfPoints p s D ∧
        ∀ f : H, f ≠ 0 →
          0 ≤ hermitianGeometricZeroPoleDivisor p s f +
            ((Q + 1 : ℕ) : ℤ) • hermitianGeometricDivisorOfPoints p s D →
          ∃ F : MvPolynomial (Option Bool) E, F ≠ 0 ∧ F.IsHomogeneous d ∧
            f = hermitianGeometricSectionValue p s F / hermitianGeometricSectionValue p s F₀ ∧
            hermitianGeometricSectionDivisor p s d F =
              ((Q + 1 : ℕ) : ℤ) • hermitianGeometricDivisorOfPoints p s D +
                hermitianGeometricZeroPoleDivisor p s f := by
  let t : H := (hermitianGeometricTangentProduct p s D : H)
  have ht : t ≠ 0 := Units.ne_zero (hermitianGeometricTangentProduct p s D)
  have hdiv := hermitianGeometricTangentProduct_divisor_degree p s D hFr
  change hermitianGeometricZeroPoleDivisor p s t = _ at hdiv
  have hdegree : ((Q + 1 : ℕ) : ℤ) * hermitianGeometricDivisorDegree p s D =
      ((d * (Q + 1) : ℕ) : ℤ) := by
    rw [hdeg, Nat.cast_mul]
    ring
  rw [hdegree] at hdiv
  have hpositive : 0 ≤ ((Q + 1 : ℕ) : ℤ) • hermitianGeometricDivisorOfPoints p s D :=
    smul_nonneg (by exact_mod_cast Nat.zero_le (Q + 1))
      (hermitianGeometricDivisorOfPoints_nonneg p s D hD)
  have htbound : 0 ≤ hermitianGeometricZeroPoleDivisor p s t +
      ((d * (Q + 1) : ℕ) : ℤ) • (0, 1) := by
    rw [hdiv, sub_add_cancel]
    exact hpositive
  obtain ⟨htfinite, htinfinity⟩ :=
    (hermitianGeometricZeroPoleDivisor_add_infinity_nonneg_iff p s t ht _).mp htbound
  obtain ⟨F₀, hF₀, hhom₀, heval₀⟩ :=
    hermitianGeometric_exists_nonzero_homogeneousSection p s t ht d hd htfinite htinfinity
  refine ⟨F₀, hF₀, hhom₀, ?_, ?_, ?_⟩
  · rw [heval₀]
    exact ht
  · rw [hermitianGeometricSectionDivisor, heval₀, hdiv, sub_add_cancel]
  · intro f hf hbound
    have htf : t * f ≠ 0 := mul_ne_zero ht hf
    have htfdiv : hermitianGeometricZeroPoleDivisor p s (t * f) +
        ((d * (Q + 1) : ℕ) : ℤ) • (0, 1) =
        hermitianGeometricZeroPoleDivisor p s f +
          ((Q + 1 : ℕ) : ℤ) • hermitianGeometricDivisorOfPoints p s D := by
      rw [hermitianGeometricZeroPoleDivisor_mul p s t f ht hf, hdiv]
      abel
    have htfbound : 0 ≤ hermitianGeometricZeroPoleDivisor p s (t * f) +
        ((d * (Q + 1) : ℕ) : ℤ) • (0, 1) := by
      rw [htfdiv]
      exact hbound
    obtain ⟨hfinite, hinfinity⟩ :=
      (hermitianGeometricZeroPoleDivisor_add_infinity_nonneg_iff p s (t * f) htf _).mp htfbound
    obtain ⟨F, hF, hhom, heval⟩ :=
      hermitianGeometric_exists_nonzero_homogeneousSection p s (t * f) htf d hd hfinite hinfinity
    refine ⟨F, hF, hhom, ?_, ?_⟩
    · rw [heval, heval₀]
      exact (eq_div_iff ht).mpr (mul_comm f t)
    · rw [hermitianGeometricSectionDivisor, heval, htfdiv]
      exact add_comm _ _

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
