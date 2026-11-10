import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.CharacterPrimeLogContinuation
import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.ArithmeticPhaseMixture
import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.QuadraticResidueScaling

/-!
# Exact Euler expansion of the arithmetic phase mixture

Absolute Taylor expansion separates the polynomial principal-character
part from the bounded nonprincipal character part. The ramified prime
two contributes one explicit finite correction. Exponentiating the two
principal logarithms gives the exact rational moving divisor, with
endpoint unit equal to `ζ(2)`.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.ArithmeticGaugeTheory
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open _root_.RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations


/-- Width of a bounded horizontal continuation of the nonprincipal prime logarithm. -/
def mixtureCharacterWidth : ℝ :=
  Classical.choose (exists_bounded_characterPrimeLog_tube ArithmeticGaugeTheory.chiFour_ne_one)

theorem mixtureCharacterWidth_pos : 0 < mixtureCharacterWidth :=
  (Classical.choose_spec (exists_bounded_characterPrimeLog_tube ArithmeticGaugeTheory.chiFour_ne_one)).1

/-- The character prime logarithm, with its actual right-half-plane values. -/
def mixtureCharacterLog : ℂ → ℂ :=
  Classical.choose ((Classical.choose_spec (exists_bounded_characterPrimeLog_tube ArithmeticGaugeTheory.chiFour_ne_one)).2)

theorem mixtureCharacterLog_properties :
    ∃ C : ℝ, 0 ≤ C ∧
      AnalyticOnNhd ℂ mixtureCharacterLog
        {s : ℂ | 1 - mixtureCharacterWidth < s.re ∧ |s.im| < mixtureCharacterWidth} ∧
      (∀ s : ℂ, 1 - mixtureCharacterWidth < s.re → |s.im| < mixtureCharacterWidth →
        ‖mixtureCharacterLog s‖ ≤ C) ∧
      (∀ s : ℂ, 1 < s.re → mixtureCharacterLog s = characterPrimeLog ArithmeticGaugeTheory.chiFour s) :=
  Classical.choose_spec ((Classical.choose_spec (exists_bounded_characterPrimeLog_tube ArithmeticGaugeTheory.chiFour_ne_one)).2)

/-- Exact finite correction for the ramified prime. -/
def mixtureFiniteCorrection (t : ℝ) (s : ℂ) : ℂ :=
  Complex.I * mixtureSkew (Complex.exp (-(t : ℂ) * (Real.log 2 : ℂ))) * (2 : ℂ) ^ (-s)

/-- Regular part after extracting the two principal-character shifts. -/
def mixtureRegularExponent (t : ℝ) (s : ℂ) : ℂ :=
  -4 * primeLogRegularPart (s + 2 * (t : ℂ)) + 2 * primeLogRegularPart (s + 4 * (t : ℂ)) +
      Complex.I * characterShiftSeries mixtureSkewCoefficient mixtureCharacterLog t s +
      mixtureFiniteCorrection t s + mixtureHigherPrimeLog t s - hullRem s (twist 0)

/-- Nonvanishing factor accompanying the exact shifted divisor. -/
def mixtureDivisorUnit (t : ℝ) (s : ℂ) : ℂ :=
  zetaResidueFactor s * Complex.exp (mixtureRegularExponent t s)

/-- Meromorphic continuation of the regularized arithmetic Euler product near one. -/
def mixtureContinuation (t : ℝ) (s : ℂ) : ℂ :=
  mixtureDivisorUnit t s * (s - (1 - 2 * (t : ℂ))) ^ 4 / (s - (1 - 4 * (t : ℂ))) ^ 2

/-- The rational nearby profile. -/
def mixtureScalingProfile (w : ℂ) : ℂ := riemannZeta 2 * (w + 2) ^ 4 / (w + 4) ^ 2

private theorem mixture_prime_decay (p : Nat.Primes) (s : ℂ) :
    Complex.exp (-s * (Real.log (p : ℝ) : ℂ)) = ((p : ℕ) : ℂ) ^ (-s) := by
  simpa only [primeFrequency, neg_mul] using prime_cexp_decay p s

private theorem mixture_prime_shift (p : Nat.Primes) (s : ℂ) (t : ℝ) (n : ℕ) :
    ((p : ℕ) : ℂ) ^ (-(s + (n : ℂ) * (t : ℂ))) =
      Complex.exp (-(t : ℂ) * (Real.log (p : ℝ) : ℂ)) ^ n * ((p : ℕ) : ℂ) ^ (-s) := by
  rw [← mixture_prime_decay p (s + (n : ℂ) * (t : ℂ)), ← mixture_prime_decay p s,
    ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  ring

private def mixtureCharacterTerm (t : ℝ) (s : ℂ) (p : Nat.Primes) (n : ℕ) : ℂ :=
  mixtureSkewCoefficient n * (ArithmeticGaugeTheory.chiFour p * ((p : ℕ) : ℂ) ^ (-(s + (n : ℂ) * (t : ℂ))))

private theorem summable_mixtureCharacterTerm {t : ℝ} (ht : 0 ≤ t) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun pn : Nat.Primes × ℕ => mixtureCharacterTerm t s pn.1 pn.2) := by
  have hp : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-s.re)) :=
    Nat.Primes.summable_rpow.mpr (by linarith only [hs])
  have hprod := Summable.mul_of_nonneg hp summable_norm_mixtureSkewCoefficient
    (fun p => by positivity) (fun n => norm_nonneg _)
  apply Summable.of_norm_bounded hprod
  rintro ⟨p, n⟩
  rw [mixtureCharacterTerm, norm_mul]
  have hn : s.re ≤ (s + (n : ℂ) * (t : ℂ)).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.ofReal_re,
      Complex.natCast_im, Complex.ofReal_im, mul_zero, sub_zero]
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) ht)
  have hm := (norm_char_prime_cpow_le ArithmeticGaugeTheory.chiFour (w := s + (n : ℂ) * (t : ℂ)) p).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_le) (neg_le_neg hn))
  exact (mul_le_mul_of_nonneg_left hm (norm_nonneg (mixtureSkewCoefficient n))).trans_eq (mul_comm _ _)

private theorem mixtureCharacterTerm_tsum {t : ℝ} (ht : 0 ≤ t) (s : ℂ) (p : Nat.Primes) :
    (∑' n, mixtureCharacterTerm t s p n) = ArithmeticGaugeTheory.chiFour p *
      mixtureSkew (Complex.exp (-(t : ℂ) * (Real.log (p : ℝ) : ℂ))) * ((p : ℕ) : ℂ) ^ (-s) := by
  have hz : ‖Complex.exp (-(t : ℂ) * (Real.log (p : ℝ) : ℂ))‖ ≤ 1 := by
    rw [norm_exponentialPrime_damping, Complex.ofReal_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast p.2.one_le) (neg_nonpos.mpr ht)
  have hh := ((mixtureSkewCoefficient_hasSum hz).mul_left (ArithmeticGaugeTheory.chiFour p)).mul_right
    (((p : ℕ) : ℂ) ^ (-s))
  rw [← hh.tsum_eq]
  apply tsum_congr
  intro n
  rw [mixtureCharacterTerm, mixture_prime_shift]
  ring

/-- Absolute Fubini identifies the actual character-weighted Euler contribution. -/
theorem mixture_character_prime_sum {t : ℝ} (ht : 0 ≤ t) {s : ℂ} (hs : 1 < s.re) :
    (∑' p : Nat.Primes, ArithmeticGaugeTheory.chiFour p *
      mixtureSkew (Complex.exp (-(t : ℂ) * (Real.log (p : ℝ) : ℂ))) * ((p : ℕ) : ℂ) ^ (-s)) =
      ∑' n, mixtureSkewCoefficient n * characterPrimeLog ArithmeticGaugeTheory.chiFour (s + (n : ℂ) * (t : ℂ)) := by
  calc
    _ = ∑' p : Nat.Primes, ∑' n, mixtureCharacterTerm t s p n :=
      tsum_congr (fun p => (mixtureCharacterTerm_tsum ht s p).symm)
    _ = ∑' n, ∑' p : Nat.Primes, mixtureCharacterTerm t s p n :=
      (Summable.tsum_comm (f := fun p n => mixtureCharacterTerm t s p n)
        (summable_mixtureCharacterTerm ht hs)).symm
    _ = _ := by
      apply tsum_congr
      intro n
      simp only [mixtureCharacterTerm, characterPrimeLog, tsum_mul_left]

private theorem summable_mixture_character_skew {t : ℝ} (ht : 0 ≤ t) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => ArithmeticGaugeTheory.chiFour p *
      mixtureSkew (Complex.exp (-(t : ℂ) * (Real.log (p : ℝ) : ℂ))) * ((p : ℕ) : ℂ) ^ (-s)) := by
  have hp : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-s.re)) :=
    Nat.Primes.summable_rpow.mpr (by linarith only [hs])
  apply Summable.of_norm_bounded (hp.mul_left (∑' n, ‖mixtureSkewCoefficient n‖))
  intro p
  have hz : ‖Complex.exp (-(t : ℂ) * (Real.log (p : ℝ) : ℂ))‖ ≤ 1 := by
    rw [norm_exponentialPrime_damping, Complex.ofReal_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast p.2.one_le) (neg_nonpos.mpr ht)
  rw [show ArithmeticGaugeTheory.chiFour p * mixtureSkew (Complex.exp (-(t : ℂ) * (Real.log (p : ℝ) : ℂ))) *
      ((p : ℕ) : ℂ) ^ (-s) = (ArithmeticGaugeTheory.chiFour p * ((p : ℕ) : ℂ) ^ (-s)) *
      mixtureSkew (Complex.exp (-(t : ℂ) * (Real.log (p : ℝ) : ℂ))) by ring, norm_mul]
  exact (mul_le_mul (norm_char_prime_cpow_le ArithmeticGaugeTheory.chiFour p) (norm_mixtureSkew_le_tsum hz)
    (norm_nonneg _) (by positivity)).trans_eq (mul_comm _ _)

private theorem mixture_prime_deviation (t : ℝ) (s : ℂ) (p : Nat.Primes) :
    (mixturePrimeValue t p - 1) * ((p : ℕ) : ℂ) ^ (-s) =
      (-4 * ((p : ℕ) : ℂ) ^ (-(s + 2 * (t : ℂ))) +
        2 * ((p : ℕ) : ℂ) ^ (-(s + 4 * (t : ℂ)))) +
      Complex.I * (ArithmeticGaugeTheory.chiFour p * mixtureSkew (Complex.exp (-(t : ℂ) * (Real.log (p : ℝ) : ℂ))) *
        ((p : ℕ) : ℂ) ^ (-s)) +
      (if p = (⟨2, Nat.prime_two⟩ : Nat.Primes) then mixtureFiniteCorrection t s else 0) := by
  have h2 := mixture_prime_shift p s t 2
  have h4 := mixture_prime_shift p s t 4
  simp only [Nat.cast_ofNat] at h2 h4
  rw [h2, h4,
    mixturePrimeValue, mixtureProfile, mixturePrimeSign_correction, mixtureMean]
  by_cases hp : p = (⟨2, Nat.prime_two⟩ : Nat.Primes)
  · subst p
    simp only [Nat.cast_ofNat, if_true, mixtureFiniteCorrection]
    ring
  · have hp2 : (p : ℕ) ≠ 2 := fun he => hp (Subtype.ext he)
    simp only [if_neg hp, if_neg hp2, add_zero]
    ring

/-- The arithmetic prime sum has exactly two principal shifts and a bounded
nonprincipal Taylor contribution, plus the ramified Euler correction. -/
theorem deformationPrimeSum_mixture {t : ℝ} (ht : 0 ≤ t) {s : ℂ} (hs : 1 < s.re) :
    deformationPrimeSum (mixturePhaseGauge t) s =
      -4 * coronaPrimeZeta (s + 2 * (t : ℂ)) + 2 * coronaPrimeZeta (s + 4 * (t : ℂ)) +
        Complex.I * characterShiftSeries mixtureSkewCoefficient mixtureCharacterLog t s +
        mixtureFiniteCorrection t s := by
  have hshift (n : ℕ) : 1 < (s + (n : ℂ) * (t : ℂ)).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.ofReal_re,
      Complex.natCast_im, Complex.ofReal_im, mul_zero, sub_zero]
    exact hs.trans_le (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) ht))
  have hs2 := hshift 2
  have hs4 := hshift 4
  simp only [Nat.cast_ofNat] at hs2 hs4
  have h2 := (summable_coronaPrimeEigenvalue hs2).mul_left (-4 : ℂ)
  have h4 := (summable_coronaPrimeEigenvalue hs4).mul_left (2 : ℂ)
  have hχ := (summable_mixture_character_skew ht hs).mul_left Complex.I
  have hfinite : HasSum (fun p : Nat.Primes =>
      if p = (⟨2, Nat.prime_two⟩ : Nat.Primes) then mixtureFiniteCorrection t s else 0)
      (mixtureFiniteCorrection t s) := hasSum_ite_eq _ _
  have hF : (∑' n, mixtureSkewCoefficient n * characterPrimeLog ArithmeticGaugeTheory.chiFour (s + (n : ℂ) * (t : ℂ))) =
      characterShiftSeries mixtureSkewCoefficient mixtureCharacterLog t s := by
    obtain ⟨C, hC, ha, hb, he⟩ := mixtureCharacterLog_properties
    unfold characterShiftSeries
    apply tsum_congr
    intro n
    rw [he _ (hshift n)]
  calc
    _ = ∑' p : Nat.Primes,
        (((-4 : ℂ) * coronaPrimeEigenvalue (s + 2 * (t : ℂ)) p +
          2 * coronaPrimeEigenvalue (s + 4 * (t : ℂ)) p) +
        Complex.I * (ArithmeticGaugeTheory.chiFour p * mixtureSkew (Complex.exp (-(t : ℂ) * (Real.log (p : ℝ) : ℂ))) *
          ((p : ℕ) : ℂ) ^ (-s)) +
        (if p = (⟨2, Nat.prime_two⟩ : Nat.Primes) then mixtureFiniteCorrection t s else 0)) := by
      unfold deformationPrimeSum
      apply tsum_congr
      intro p
      rw [← mixturePrimeValue_eq_twist ht p]
      exact mixture_prime_deviation t s p
    _ = _ := by
      rw [((h2.add h4).add hχ).tsum_add hfinite.summable,
        (h2.add h4).tsum_add hχ, h2.tsum_add h4, hfinite.tsum_eq]
      simp only [tsum_mul_left, coronaPrimeZeta]
      rw [mixture_character_prime_sum ht hs, hF]

/-- Primewise equality identifies the direct higher-power sum with the gauge sum. -/
theorem mixtureHigherPrimeLog_eq_gauge {t : ℝ} (ht : 0 ≤ t) (s : ℂ) :
    mixtureHigherPrimeLog t s = hullRem s (twist (mixturePhaseGauge t)) := by
  unfold mixtureHigherPrimeLog hullRem
  apply tsum_congr
  intro p
  simp only [localRem, eulerVar, mixturePrimeValue_eq_twist ht p]

@[simp] theorem mixtureFiniteCorrection_zero (s : ℂ) : mixtureFiniteCorrection 0 s = 0 := by
  simp [mixtureFiniteCorrection]

theorem mixtureDivisorUnit_endpoint : mixtureDivisorUnit 0 1 = riemannZeta 2 := by
  simp only [mixtureDivisorUnit, mixtureRegularExponent, zetaResidueFactor_one, one_mul,
    Complex.ofReal_zero, mul_zero, add_zero, primeLogRegularPart_one,
    characterShiftSeries_zero mixtureCharacterLog mixtureSkewCoefficient_tsum,
    mixtureFiniteCorrection_zero, mixtureHigherPrimeLog_zero]
  convert exp_liouville_hullRem_pair using 1
  congr 1
  ring


theorem mixture_ball_in_tube {e r : ℝ} (hre : r ≤ e) {s : ℂ}
    (hs : s ∈ ball (1 : ℂ) r) : 1 - e < s.re ∧ |s.im| < e := by
  have hn : ‖s - 1‖ < r := by simpa only [mem_ball, dist_eq_norm] using hs
  have hRe := Complex.re_le_norm (1 - s)
  rw [norm_sub_rev] at hRe
  simp only [Complex.sub_re, Complex.one_re] at hRe
  have hIm := Complex.abs_im_le_norm (s - 1)
  simp only [Complex.sub_im, Complex.one_im, sub_zero] at hIm
  exact ⟨by linarith only [hRe, hn, hre], hIm.trans_lt (hn.trans_le hre)⟩

theorem mixture_small_shift_mem {r R t : ℝ} (hr : 0 < r) (hrR : r ≤ R / 4)
    (ht : 0 ≤ t) (htsmall : t < r / 8) {s : ℂ} (hs : s ∈ ball (1 : ℂ) r)
    (n : ℕ) (hn : n ≤ 4) : s + (n : ℂ) * (t : ℂ) ∈ ball (1 : ℂ) R := by
  have hsr : ‖s - 1‖ < r := by simpa only [mem_ball, dist_eq_norm] using hs
  have hnt : (n : ℝ) * t ≤ 4 * t := mul_le_mul_of_nonneg_right (by exact_mod_cast hn) ht
  rw [mem_ball, dist_eq_norm,
    show s + (n : ℂ) * (t : ℂ) - 1 = (s - 1) + (n : ℂ) * (t : ℂ) by ring]
  apply (norm_add_le _ _).trans_lt
  rw [norm_mul, Complex.norm_natCast, norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  linarith only [hr, hrR, htsmall, hsr, hnt]

/-- The actual Euler product agrees with the rational shifted divisor on its
half-plane of absolute convergence. -/
theorem mixtureEuler_factorization :
    ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, 0 ≤ t → ∀ s : ℂ,
      s + 2 * (t : ℂ) ∈ ball 1 R → s + 4 * (t : ℂ) ∈ ball 1 R → 1 < s.re →
      (s - 1) * gaugeFibre (mixturePhaseGauge t) s = mixtureContinuation t s := by
  obtain ⟨R, hR, hE, he⟩ := exists_primeLogRegularPart_germ
  refine ⟨R, hR, ?_⟩
  intro t ht s hs2 hs4 hs
  have hshift (n : ℕ) : 1 < (s + (n : ℂ) * (t : ℂ)).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.ofReal_re,
      Complex.natCast_im, Complex.ofReal_im, mul_zero, sub_zero]
    exact hs.trans_le (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) ht))
  have hre2 := hshift 2
  have hre4 := hshift 4
  simp only [Nat.cast_ofNat] at hre2 hre4
  have hd2 : s - (1 - 2 * (t : ℂ)) ≠ 0 := by
    have hh : 0 < (s - (1 - 2 * (t : ℂ))).re := by
      have heq : s - (1 - 2 * (t : ℂ)) = s + 2 * (t : ℂ) - 1 := by ring
      rw [heq, Complex.sub_re, Complex.one_re]
      linarith only [hre2]
    exact fun h => (ne_of_gt hh) (by rw [h]; rfl)
  have hd4 : s - (1 - 4 * (t : ℂ)) ≠ 0 := by
    have hh : 0 < (s - (1 - 4 * (t : ℂ))).re := by
      have heq : s - (1 - 4 * (t : ℂ)) = s + 4 * (t : ℂ) - 1 := by ring
      rw [heq, Complex.sub_re, Complex.one_re]
      linarith only [hre4]
    exact fun h => (ne_of_gt hh) (by rw [h]; rfl)
  have hE2 := he _ hs2 hre2
  have hE4 := he _ hs4 hre4
  rw [show s + 2 * (t : ℂ) - 1 = s - (1 - 2 * (t : ℂ)) by ring] at hE2
  rw [show s + 4 * (t : ℂ) - 1 = s - (1 - 4 * (t : ℂ)) by ring] at hE4
  have hexp : deformationExponent (mixturePhaseGauge t) s = mixtureRegularExponent t s +
      4 * Complex.log (s - (1 - 2 * (t : ℂ))) - 2 * Complex.log (s - (1 - 4 * (t : ℂ))) := by
    rw [deformationExponent, deformationPrimeSum_mixture ht hs,
      ← mixtureHigherPrimeLog_eq_gauge ht, mixtureRegularExponent, ← hE2, ← hE4]
    ring
  have hpow4 : Complex.exp (4 * Complex.log (s - (1 - 2 * (t : ℂ)))) =
      (s - (1 - 2 * (t : ℂ))) ^ 4 := by
    calc
      _ = Complex.exp (Complex.log (s - (1 - 2 * (t : ℂ)))) ^ 4 := by
        simpa only [Nat.cast_ofNat] using Complex.exp_nat_mul (Complex.log (s - (1 - 2 * (t : ℂ)))) 4
      _ = _ := by rw [Complex.exp_log hd2]
  have hpow2 : Complex.exp (2 * Complex.log (s - (1 - 4 * (t : ℂ)))) =
      (s - (1 - 4 * (t : ℂ))) ^ 2 := by
    calc
      _ = Complex.exp (Complex.log (s - (1 - 4 * (t : ℂ)))) ^ 2 := by
        simpa only [Nat.cast_ofNat] using Complex.exp_nat_mul (Complex.log (s - (1 - 4 * (t : ℂ)))) 2
      _ = _ := by rw [Complex.exp_log hd4]
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  rw [gaugeFibre_eq_zeta_mul_exp _ hs, hexp, Complex.exp_sub, Complex.exp_add, hpow4, hpow2,
    mixtureContinuation, mixtureDivisorUnit, zetaResidueFactor_of_ne hs1]
  ring

#print axioms deformationPrimeSum_mixture
#print axioms mixtureDivisorUnit_endpoint
#print axioms mixtureEuler_factorization
end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
