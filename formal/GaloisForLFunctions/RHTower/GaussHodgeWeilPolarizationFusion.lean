import GaloisForLFunctions.RHTower.GaussHodgePencilSourcing
import GaloisForLFunctions.RHTower.XiWeilPolarization

/-!
# Fusion of the Hodge mass loop with the Weil polarization interface

The corpus's `xiWeilPolarization` is the multiplicity-exact zero-side Weil form — the
holomorphic (explicit-formula) channel, whose nonnegativity is RH.  The Hodge mass loop lives
in the Hermitian channel.  This module fuses the two, unconditionally and pointwise, with no
summability hypotheses.

In centered spectral coordinates the prime exponential test `e^{z·i·log p}` evaluates on the
divisor to the Burnol character, and its sharp involution to the character at the FE-reflected
argument.  Three exact laws follow.  First, blindness: every Weil pair summand of the prime
test is the constant `1` — the polarization cannot see the divisor through the prime test,
which is the information-gap theorem landing inside the polarization interface.  Second, the
pointwise pair-square law: over each reflection pair the polarization summands equal the
Hermitian pair energy minus the sharp-difference square, for every test function.  Third, at
the prime test that sharp-difference square is exactly the centered cosh defect, so **the
Hodge/seam mass density at a copy is precisely the gap between the Hermitian pair energy and
the Weil polarization pair value** — and RH holds exactly when that gap closes at every copy
for the prime-2 test.

Finally, the conjugate-pair support law for the canonical eigenfunctions: without any
hypothesis, the polarization couples the Hedenmalm eigenfunction at `alpha` only to the one at
`conj alpha`, with Gram value `multiplicity × XiC'(alpha) × conj XiC'(conj alpha)`.  The
module's RH-conditional orthogonality is the collapse of this unconditional conjugate-pair
Gram onto the diagonal.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## The prime exponential test in spectral coordinates -/

/-- The prime exponential Weil test in centered spectral coordinates. -/
def xiWeilPrimeTest (p : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (z * Complex.I * Real.log p)

/-- On the divisor the prime test evaluates to the Burnol character. -/
theorem xiWeilPrimeTest_spectralPoint {p : ℝ} (hp : 0 < p) (q : XiZeroCopy) :
    xiWeilPrimeTest p (xiSpectralPoint q) = burnolPrimeCharacter p ((q.1 : ℂ)) := by
  rw [xiWeilPrimeTest, burnolPrimeCharacter_eq_exp p hp, xiSpectralPoint]
  congr 1
  have hI : (-Complex.I) * Complex.I = 1 := by
    rw [neg_mul, Complex.I_mul_I]
    ring
  linear_combination ((q.1 : ℂ) - 1 / 2) * ((Real.log p : ℝ) : ℂ) * hI

/-- The sharp involution sends the prime test to its reciprocal-mode companion. -/
theorem xiWeilSharp_primeTest (p : ℝ) (z : ℂ) :
    xiWeilSharp (xiWeilPrimeTest p) z =
      Complex.exp (-(z * Complex.I * Real.log p)) := by
  rw [xiWeilSharp, xiWeilPrimeTest, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_conj, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- On the divisor the sharp prime test is the Burnol character at the FE-reflected
argument. -/
theorem xiWeilSharp_primeTest_spectralPoint {p : ℝ} (hp : 0 < p) (q : XiZeroCopy) :
    xiWeilSharp (xiWeilPrimeTest p) (xiSpectralPoint q) =
      burnolPrimeCharacter p (1 - (q.1 : ℂ)) := by
  rw [xiWeilSharp_primeTest, burnolPrimeCharacter_eq_exp p hp, xiSpectralPoint]
  congr 1
  have hI : (-Complex.I) * Complex.I = 1 := by
    rw [neg_mul, Complex.I_mul_I]
    ring
  linear_combination (-((q.1 : ℂ) - 1 / 2)) * ((Real.log p : ℝ) : ℂ) * hI

/-! ## The Weil pair summand and the blindness law -/

/-- The Weil pair summand of a test function at one copy. -/
def xiWeilPairTerm (F : ℂ → ℂ) (q : XiZeroCopy) : ℂ :=
  F (xiSpectralPoint q) * xiWeilSharp F (xiSpectralPoint q)

/-- The polarization diagonal is the sum of the pair summands. -/
theorem xiWeilPolarization_eq_tsum_pairTerm (F : ℂ → ℂ) :
    xiWeilPolarization F F = ∑' q : XiZeroCopy, xiWeilPairTerm F q := rfl

/-- **Divisor blindness of the polarization at the prime test.**  Every Weil pair summand of
the prime exponential test is the constant `1`. -/
theorem xiWeilPairTerm_primeTest {p : ℝ} (hp : 0 < p) (q : XiZeroCopy) :
    xiWeilPairTerm (xiWeilPrimeTest p) q = 1 := by
  rw [xiWeilPairTerm, xiWeilPrimeTest_spectralPoint hp,
    xiWeilSharp_primeTest_spectralPoint hp]
  exact burnolPrimeCharacter_mul_one_sub hp _

/-! ## The pointwise pair-square law -/

/-- **Pair-square law.**  Over a reflection pair the polarization summands equal the Hermitian
pair energy minus the sharp-difference square — unconditionally, for every test function. -/
theorem xiWeilPairTerm_add_lineConj (F : ℂ → ℂ) (q : XiZeroCopy) :
    xiWeilPairTerm F q + xiWeilPairTerm F (xiZeroCopyLineConjEquiv q) =
      ((‖F (xiSpectralPoint q)‖ ^ 2 +
        ‖F (xiSpectralPoint (xiZeroCopyLineConjEquiv q))‖ ^ 2 -
        ‖F (xiSpectralPoint q) -
          F (xiSpectralPoint (xiZeroCopyLineConjEquiv q))‖ ^ 2 : ℝ) : ℂ) := by
  have hpt : xiSpectralPoint (xiZeroCopyLineConjEquiv q) =
      (starRingEnd ℂ) (xiSpectralPoint q) := xiSpectralPoint_lineConj q
  rw [xiWeilPairTerm, xiWeilPairTerm, xiWeilSharp, xiWeilSharp, hpt, Complex.conj_conj]
  set a := F (xiSpectralPoint q) with ha
  set b := F ((starRingEnd ℂ) (xiSpectralPoint q)) with hb
  have h1 : a * (starRingEnd ℂ) b + b * (starRingEnd ℂ) a =
      ((2 * (a * (starRingEnd ℂ) b).re : ℝ) : ℂ) := by
    have hadd := Complex.add_conj (a * (starRingEnd ℂ) b)
    rw [map_mul, Complex.conj_conj] at hadd
    linear_combination hadd
  have h2 : ‖a - b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 - 2 * (a * (starRingEnd ℂ) b).re := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
  rw [h1, h2]
  push_cast
  ring

/-! ## The mass-gap fusion at the prime test -/

/-- The conjugate of the reflected-argument character is the FE-partner character. -/
theorem conj_burnolPrimeCharacter_one_sub_conj {p : ℝ} (hp : 0 < p) (s : ℂ) :
    (starRingEnd ℂ) (burnolPrimeCharacter p (1 - (starRingEnd ℂ) s)) =
      burnolPrimeCharacter p (1 - s) := by
  rw [burnolPrimeCharacter_eq_exp p hp, burnolPrimeCharacter_eq_exp p hp,
    ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_sub, map_one, Complex.conj_conj, Complex.conj_ofReal]
  congr 1
  rw [show (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) from by norm_num, Complex.conj_ofReal]]

/-- **The sharp-difference square of the prime test across a reflection pair is the centered
cosh defect** — the Hodge/seam mass density at the copy. -/
theorem norm_sq_primeTest_sub_lineConj {p : ℝ} (hp : 1 < p) (q : XiZeroCopy) :
    ‖xiWeilPrimeTest p (xiSpectralPoint q) -
      xiWeilPrimeTest p (xiSpectralPoint (xiZeroCopyLineConjEquiv q))‖ ^ 2 =
      (p : ℝ) ^ (2 * ((q.1 : ℂ)).re - 1) + (p : ℝ) ^ (1 - 2 * ((q.1 : ℂ)).re) - 2 := by
  have hp0 : (0 : ℝ) < p := lt_trans one_pos hp
  rw [xiWeilPrimeTest_spectralPoint hp0, xiWeilPrimeTest_spectralPoint hp0,
    GaloisForLFunctions.RHTower.xiZeroCopyLineConj_support]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq]
  have hA : ‖burnolPrimeCharacter p ((q.1 : ℂ))‖ ^ 2 =
      (p : ℝ) ^ (2 * ((q.1 : ℂ)).re - 1) := by
    rw [norm_burnolPrimeCharacter hp0, sq, ← Real.rpow_add hp0]
    congr 1
    ring
  have hB : ‖burnolPrimeCharacter p (1 - (starRingEnd ℂ) ((q.1 : ℂ)))‖ ^ 2 =
      (p : ℝ) ^ (1 - 2 * ((q.1 : ℂ)).re) := by
    rw [norm_burnolPrimeCharacter hp0, sq, ← Real.rpow_add hp0]
    congr 1
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    ring
  have hcross : burnolPrimeCharacter p ((q.1 : ℂ)) *
      (starRingEnd ℂ) (burnolPrimeCharacter p (1 - (starRingEnd ℂ) ((q.1 : ℂ)))) = 1 := by
    rw [conj_burnolPrimeCharacter_one_sub_conj hp0]
    exact burnolPrimeCharacter_mul_one_sub hp0 _
  rw [hA, hB, hcross]
  norm_num

/-- **The mass-gap fusion law.**  At every copy the Hodge/seam mass density equals the gap
between the Hermitian pair energy and twice the real Weil pair value of the prime test: the
H-mass is exactly the per-pair Hermitian defect of `xiWeilPolarization`. -/
theorem massDensity_eq_hermitianPair_sub_weilPair {p : ℝ} (hp : 1 < p) (q : XiZeroCopy) :
    (p : ℝ) ^ (2 * ((q.1 : ℂ)).re - 1) + (p : ℝ) ^ (1 - 2 * ((q.1 : ℂ)).re) - 2 =
      (‖xiWeilPrimeTest p (xiSpectralPoint q)‖ ^ 2 +
        ‖xiWeilPrimeTest p (xiSpectralPoint (xiZeroCopyLineConjEquiv q))‖ ^ 2) -
        2 * (xiWeilPairTerm (xiWeilPrimeTest p) q).re := by
  have hp0 : (0 : ℝ) < p := lt_trans one_pos hp
  have hpair := xiWeilPairTerm_add_lineConj (xiWeilPrimeTest p) q
  rw [xiWeilPairTerm_primeTest hp0, xiWeilPairTerm_primeTest hp0] at hpair
  have hre := congrArg Complex.re hpair
  simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re] at hre
  have hdef := norm_sq_primeTest_sub_lineConj hp q
  have hone : (xiWeilPairTerm (xiWeilPrimeTest p) q).re = 1 := by
    rw [xiWeilPairTerm_primeTest hp0]
    norm_num
  rw [hone]
  linarith [hre, hdef]

/-- **RH at the polarization interface.**  RH holds exactly when, at every copy, the Hermitian
pair energy of the prime-2 test equals twice the real part of its Weil pair value: the loop's
mass current is the exact obstruction to the Weil polarization agreeing with its Hermitian
majorant at the prime test. -/
theorem riemannHypothesis_iff_hermitianPair_eq_weilPair :
    RiemannHypothesis ↔
      ∀ q : XiZeroCopy,
        ‖xiWeilPrimeTest 2 (xiSpectralPoint q)‖ ^ 2 +
          ‖xiWeilPrimeTest 2 (xiSpectralPoint (xiZeroCopyLineConjEquiv q))‖ ^ 2 =
        2 * (xiWeilPairTerm (xiWeilPrimeTest 2) q).re := by
  rw [riemannHypothesis_iff_forall_seamCharge_eq_zero]
  refine forall_congr' fun q => ?_
  rw [orbitwiseNatSeamCharge_eq_zero_iff (q.1 : ℂ) one_lt_two]
  have hgap := massDensity_eq_hermitianPair_sub_weilPair
    (by norm_num : (1 : ℝ) < 2) q
  constructor
  · intro h
    have hdef : (2 : ℝ) ^ (2 * ((q.1 : ℂ)).re - 1) +
        (2 : ℝ) ^ (1 - 2 * ((q.1 : ℂ)).re) - 2 = 0 := by
      rw [h, show 2 * (1 / 2 : ℝ) - 1 = 0 from by norm_num,
        show 1 - 2 * (1 / 2 : ℝ) = 0 from by norm_num, Real.rpow_zero]
      norm_num
    linarith [hgap, hdef]
  · intro h
    have hdef : (2 : ℝ) ^ (2 * ((q.1 : ℂ)).re - 1) +
        (2 : ℝ) ^ (1 - 2 * ((q.1 : ℂ)).re) - 2 = 0 := by
      linarith [hgap, h]
    rw [show (1 - 2 * ((q.1 : ℂ)).re : ℝ) = -(2 * ((q.1 : ℂ)).re - 1) from by ring] at hdef
    have ht := (HTGeometry.rpow_add_rpow_neg_sub_two_eq_zero_iff
      (by norm_num : (1 : ℝ) < 2) _).mp hdef
    linarith

/-! ## The unconditional conjugate-pair eigen-Gram -/

/-- **Conjugate-pair support of the eigen-Gram.**  Without any hypothesis, the Weil
polarization couples the Hedenmalm eigenfunction at `alpha` only to the one at
`conj alpha`. -/
theorem xiWeilPolarization_thetaEigen_conjPair_vanishing
    {alpha beta : ℂ} (halpha : XiC alpha = 0) (hbeta : XiC beta = 0)
    (hne : beta ≠ (starRingEnd ℂ) alpha) :
    xiWeilPolarization (xiThetaEigenFourier alpha) (xiThetaEigenFourier beta) = 0 := by
  unfold xiWeilPolarization
  have hterm : ∀ q : XiZeroCopy,
      xiThetaEigenFourier alpha (xiSpectralPoint q) *
        xiWeilSharp (xiThetaEigenFourier beta) (xiSpectralPoint q) = 0 := by
    intro q
    by_cases hqa : xiSpectralPoint q = alpha
    · have hzero : xiThetaEigenFourier beta
          ((starRingEnd ℂ) (xiSpectralPoint q)) = 0 := by
        rw [← xiSpectralPoint_lineConj]
        apply xiThetaEigenFourier_spectralPoint_eq_zero hbeta
        rw [xiSpectralPoint_lineConj, hqa]
        exact fun hcontra => hne hcontra.symm
      rw [xiWeilSharp, hzero]
      simp
    · rw [xiThetaEigenFourier_spectralPoint_eq_zero halpha q hqa]
      simp
  calc (∑' q : XiZeroCopy,
      xiThetaEigenFourier alpha (xiSpectralPoint q) *
        xiWeilSharp (xiThetaEigenFourier beta) (xiSpectralPoint q)) =
      ∑' _q : XiZeroCopy, (0 : ℂ) := tsum_congr hterm
    _ = 0 := tsum_zero

/-- **The conjugate-pair Gram value**: multiplicity times the paired derivative product.  The
RH-conditional diagonal law of the polarization module is the collapse of this unconditional
conjugate-pair Gram onto the diagonal. -/
theorem xiWeilPolarization_thetaEigen_conjPair_value
    {alpha : ℂ} (halpha : XiC alpha = 0) :
    xiWeilPolarization (xiThetaEigenFourier alpha)
        (xiThetaEigenFourier ((starRingEnd ℂ) alpha)) =
      (xiSpectralMultiplicity alpha : ℂ) *
        (deriv XiC alpha * (starRingEnd ℂ) (deriv XiC ((starRingEnd ℂ) alpha))) := by
  unfold xiWeilPolarization
  let c : ℂ := deriv XiC alpha * (starRingEnd ℂ) (deriv XiC ((starRingEnd ℂ) alpha))
  have hterm : ∀ q : XiZeroCopy,
      xiThetaEigenFourier alpha (xiSpectralPoint q) *
        xiWeilSharp (xiThetaEigenFourier ((starRingEnd ℂ) alpha))
          (xiSpectralPoint q) =
      if xiSpectralPoint q = alpha then c else 0 := by
    intro q
    by_cases hqa : xiSpectralPoint q = alpha
    · rw [if_pos hqa, xiWeilSharp, hqa, xiThetaEigenFourier_self,
        xiThetaEigenFourier_self]
      simp only [c, map_mul, Complex.conj_I]
      ring_nf
      rw [Complex.I_sq]
      ring
    · rw [if_neg hqa, xiThetaEigenFourier_spectralPoint_eq_zero halpha q hqa]
      simp
  let T : Finset XiZeroCopy := (finite_xiSpectralPoint_fiber alpha).toFinset
  calc (∑' q : XiZeroCopy,
      xiThetaEigenFourier alpha (xiSpectralPoint q) *
        xiWeilSharp (xiThetaEigenFourier ((starRingEnd ℂ) alpha))
          (xiSpectralPoint q)) =
      ∑' q : XiZeroCopy, (if xiSpectralPoint q = alpha then c else 0) :=
        tsum_congr hterm
    _ = ∑ q ∈ T, (if xiSpectralPoint q = alpha then c else 0) := by
        apply tsum_eq_sum
        intro q hqT
        rw [if_neg]
        intro hqa
        apply hqT
        simpa only [T, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hqa
    _ = ∑ _q ∈ T, c := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [if_pos]
        simpa only [T, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hq
    _ = (T.card : ℂ) * c := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (xiSpectralMultiplicity alpha : ℂ) * c := by
        rfl

end

end RHTower
