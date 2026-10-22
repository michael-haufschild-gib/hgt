import GaloisForLFunctions.RHTower.Artin.ArtinFiniteOrderLocalPolynomialBound
import GaloisForLFunctions.RHTower.Artin.ArtinNumberFieldLocalEulerFactor
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Finite-place control of Artin Euler denominators

The canonical Artin polynomial at a finite place is evaluated at its genuine norm power.  Finite
image makes the polynomial root-free in the unit disk, and every finite prime norm power lies in
that disk for positive real part.  It also supplies a uniform difference-from-one bound on
`Re(s) ≥ 1`.  This is local absolute-convergence infrastructure only; it does not construct an
infinite Euler product or any continuation.
-/

open scoped NumberField Pointwise

noncomputable section

universe u

namespace GaloisForLFunctions

variable {K L G V : Type u}
variable [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable [Group G] [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L]
variable [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The canonical finite-place Artin Euler denominator is nonzero at its genuine Euler argument
whenever the real part of the complex parameter is positive. -/
theorem numberFieldFinitePlaceLocalEulerPolynomial_eval_ne_zero_of_re_pos
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (ρ : Representation ℂ G V) {s : ℂ} (hs : 0 < s.re) :
    (numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v ρ).eval
        ((v.asIdeal.absNorm : ℂ) ^ (-s)) ≠ 0 := by
  have hv : 1 < v.asIdeal.absNorm :=
    NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hz : ‖((v.asIdeal.absNorm : ℂ) ^ (-s))‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos (Nat.zero_lt_of_lt hv), Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hv) (neg_lt_zero.mpr hs)
  let Q := chosenMaximalPrimeAbove (A := 𝓞 K) (B := 𝓞 L)
    { asIdeal := v.asIdeal, isMaximal := v.isMaximal }
  letI : Q.IsMaximal := chosenMaximalPrimeAbove_isMaximal (A := 𝓞 K) (B := 𝓞 L)
    { asIdeal := v.asIdeal, isMaximal := v.isMaximal }
  letI : Q.IsPrime := (inferInstance : Q.IsMaximal).isPrime
  letI : Q.LiesOver v.asIdeal := chosenMaximalPrimeAbove_liesOver (A := 𝓞 K) (B := 𝓞 L)
    { asIdeal := v.asIdeal, isMaximal := v.isMaximal }
  letI : Finite ((𝓞 L) ⧸ Q) := inferInstance
  rw [← frobeniusInertiaEulerPolynomial_eq_numberFieldFinitePlaceLocalEulerPolynomial
    (K := K) (L := L) v Q ρ]
  exact frobeniusInertiaEulerPolynomial_eval_ne_zero_of_norm_lt_one
    (R := 𝓞 K) Q ρ hz

/-- At a genuine number-field finite place, the local Artin reciprocal has the finite-image norm
bound in the positive real half-plane. -/
theorem numberFieldFinitePlaceLocalEulerPolynomial_eval_norm_inv_le_of_re_pos
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (ρ : Representation ℂ G V) {s : ℂ} (hs : 0 < s.re) :
    ‖((numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v ρ).eval
      ((v.asIdeal.absNorm : ℂ) ^ (-s)))⁻¹‖ ≤
      (1 - ‖((v.asIdeal.absNorm : ℂ) ^ (-s))‖)⁻¹ ^ Module.finrank ℂ V := by
  have hv : 1 < v.asIdeal.absNorm :=
    NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hz : ‖((v.asIdeal.absNorm : ℂ) ^ (-s))‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos (Nat.zero_lt_of_lt hv), Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hv) (neg_lt_zero.mpr hs)
  let Q := chosenMaximalPrimeAbove (A := 𝓞 K) (B := 𝓞 L)
    { asIdeal := v.asIdeal, isMaximal := v.isMaximal }
  letI : Q.IsMaximal := chosenMaximalPrimeAbove_isMaximal (A := 𝓞 K) (B := 𝓞 L)
    { asIdeal := v.asIdeal, isMaximal := v.isMaximal }
  letI : Q.IsPrime := (inferInstance : Q.IsMaximal).isPrime
  letI : Q.LiesOver v.asIdeal := chosenMaximalPrimeAbove_liesOver (A := 𝓞 K) (B := 𝓞 L)
    { asIdeal := v.asIdeal, isMaximal := v.isMaximal }
  letI : Finite ((𝓞 L) ⧸ Q) := inferInstance
  rw [← frobeniusInertiaEulerPolynomial_eq_numberFieldFinitePlaceLocalEulerPolynomial
    (K := K) (L := L) v Q ρ]
  exact frobeniusInertiaEulerPolynomial_eval_norm_inv_le_of_norm_lt_one_finrank
    (R := 𝓞 K) Q ρ hz

/-- The preceding finite-place reciprocal bound expressed through the real norm power. -/
theorem numberFieldFinitePlaceLocalEulerPolynomial_eval_norm_inv_le_of_re_pos_real
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (ρ : Representation ℂ G V) {s : ℂ} (hs : 0 < s.re) :
    ‖((numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v ρ).eval
      ((v.asIdeal.absNorm : ℂ) ^ (-s)))⁻¹‖ ≤
      (1 - (v.asIdeal.absNorm : ℝ) ^ (-s.re))⁻¹ ^ Module.finrank ℂ V := by
  simpa only [Complex.norm_natCast_cpow_of_pos
    (Nat.zero_lt_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm v)), Complex.neg_re] using
    (numberFieldFinitePlaceLocalEulerPolynomial_eval_norm_inv_le_of_re_pos v ρ hs)

/-- On the closed half-plane `1 ≤ Re(s)`, every actual finite-place Artin reciprocal differs
from one by a uniform constant times its genuine norm power. -/
theorem numberFieldFinitePlaceLocalEulerPolynomial_eval_inv_sub_one_norm_le_of_re_one_le
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (ρ : Representation ℂ G V) {s : ℂ} (hs : (1 : ℝ) ≤ s.re) :
    ‖((numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v ρ).eval
      ((v.asIdeal.absNorm : ℂ) ^ (-s)))⁻¹ - 1‖ ≤
      (4 : ℝ) ^ Module.finrank ℂ V * ‖((v.asIdeal.absNorm : ℂ) ^ (-s))‖ := by
  have hv : 1 < v.asIdeal.absNorm :=
    NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hhalf : ‖((v.asIdeal.absNorm : ℂ) ^ (-s))‖ ≤ (2 : ℝ)⁻¹ := by
    rw [Complex.norm_natCast_cpow_of_pos (Nat.zero_lt_of_lt hv), Complex.neg_re]
    refine (Real.rpow_le_rpow_of_nonpos zero_lt_two ?_ (by linarith)).trans ?_
    · exact_mod_cast (Nat.succ_le_iff.mpr hv)
    · rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le one_le_two (neg_le_neg hs)
  let Q := chosenMaximalPrimeAbove (A := 𝓞 K) (B := 𝓞 L)
    { asIdeal := v.asIdeal, isMaximal := v.isMaximal }
  letI : Q.IsMaximal := chosenMaximalPrimeAbove_isMaximal (A := 𝓞 K) (B := 𝓞 L)
    { asIdeal := v.asIdeal, isMaximal := v.isMaximal }
  letI : Q.IsPrime := (inferInstance : Q.IsMaximal).isPrime
  letI : Q.LiesOver v.asIdeal := chosenMaximalPrimeAbove_liesOver (A := 𝓞 K) (B := 𝓞 L)
    { asIdeal := v.asIdeal, isMaximal := v.isMaximal }
  letI : Finite ((𝓞 L) ⧸ Q) := inferInstance
  rw [← frobeniusInertiaEulerPolynomial_eq_numberFieldFinitePlaceLocalEulerPolynomial
    (K := K) (L := L) v Q ρ]
  exact frobeniusInertiaEulerPolynomial_eval_inv_sub_one_norm_le_of_norm_le_half_finrank
    (R := 𝓞 K) Q ρ hhalf

/-- The preceding uniform finite-place difference estimate with its real norm-power majorant. -/
theorem numberFieldFinitePlaceLocalEulerPolynomial_eval_inv_sub_one_norm_le_of_re_one_le_real
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (ρ : Representation ℂ G V) {s : ℂ} (hs : (1 : ℝ) ≤ s.re) :
    ‖((numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v ρ).eval
      ((v.asIdeal.absNorm : ℂ) ^ (-s)))⁻¹ - 1‖ ≤
      (4 : ℝ) ^ Module.finrank ℂ V * (v.asIdeal.absNorm : ℝ) ^ (-s.re) := by
  simpa only [Complex.norm_natCast_cpow_of_pos
    (Nat.zero_lt_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm v)), Complex.neg_re] using
    (numberFieldFinitePlaceLocalEulerPolynomial_eval_inv_sub_one_norm_le_of_re_one_le v ρ hs)

end GaloisForLFunctions
