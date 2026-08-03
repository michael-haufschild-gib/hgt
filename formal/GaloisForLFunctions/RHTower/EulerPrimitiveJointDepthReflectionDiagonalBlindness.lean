import GaloisForLFunctions.RHTower.EulerPrimitiveJointDepthBiorthogonalCommonTest

/-!
# Reflection-diagonal blindness of the joint-depth primitive source

The primitive-promoted source and reciprocal-promotion co-source retain
different amplitudes on every `(prime, valuation-depth)` label.  This file
adds the common Hardy half-line before pairing those legs and then performs
the functional-equation reflection sewing.

For centered spectral displacement `a` and positive Hardy regularization
`eps`, the reflected parameters are

`w = eps + a`,  `v = eps - conj a`.

Their sum in the sesquilinear pairing is `w + conj v = 2 eps`.  The
horizontal displacement therefore cancels at every prime-depth-time
coordinate, before integration or summation.  In contrast, simultaneous
Hilbert admission of the two unresolved legs holds exactly when

`|re a| < eps`.

Thus the complete diagonal reflected common test is blind to horizontal
displacement throughout its Hilbert chamber; only the chamber wall remembers
the displacement.  A Route-J annihilator built from this source must use a
singular wall value, genuinely off-diagonal label incidence, or an additional
divisor-coupled differential.
-/

open Complex MeasureTheory Set
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

/-- Source-side Hardy parameter at centered displacement `a`. -/
def xiGammaEulerPrimitiveReflectedHardySourceParameter
    (eps : ℝ) (a : ℂ) : ℂ :=
  (eps : ℂ) + a

/-- Co-source parameter at the functional-equation reflection of `a`. -/
def xiGammaEulerPrimitiveReflectedHardyCoSourceParameter
    (eps : ℝ) (a : ℂ) : ℂ :=
  (eps : ℂ) - star a

/-- Reflection sewing cancels centered displacement in the sesquilinear
parameter before any source label is summed. -/
theorem xiGammaEulerPrimitiveReflectedHardyParameter_add_star
    (eps : ℝ) (a : ℂ) :
    xiGammaEulerPrimitiveReflectedHardySourceParameter eps a +
        star (xiGammaEulerPrimitiveReflectedHardyCoSourceParameter eps a) =
      (2 * eps : ℝ) := by
  simp [xiGammaEulerPrimitiveReflectedHardySourceParameter,
    xiGammaEulerPrimitiveReflectedHardyCoSourceParameter]
  ring

/-- Both reflected Hardy legs lie in their open right half-planes exactly
above the absolute horizontal displacement. -/
theorem xiGammaEulerPrimitiveReflectedHardy_jointAdmissible_iff
    (eps : ℝ) (a : ℂ) :
    0 < (xiGammaEulerPrimitiveReflectedHardySourceParameter eps a).re ∧
        0 < (xiGammaEulerPrimitiveReflectedHardyCoSourceParameter eps a).re ↔
      |a.re| < eps := by
  change (0 < eps + a.re ∧ 0 < eps - a.re) ↔ |a.re| < eps
  rw [abs_lt]
  constructor
  · rintro ⟨hleft, hright⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hleft, hright⟩
    exact ⟨by linarith, by linarith⟩

/-! ## Sharp Hilbert chamber for both unresolved legs -/

/-- Nonpositive displacement already makes the depth-zero prime face of the
reciprocal-promotion co-source nonsummable. -/
theorem not_summable_sq_xiGammaEulerPrimitiveDescentTestAmplitude_of_nonpos
    {u : ℝ} (hu : u ≤ 0) :
    ¬ Summable (fun pe : Nat.Primes × ℕ =>
      xiGammaEulerPrimitiveDescentTestAmplitude u pe ^ 2) := by
  intro hsum
  have hzero : Summable (fun p : Nat.Primes =>
      xiGammaEulerPrimitiveDescentTestAmplitude u (p, 0) ^ 2) :=
    hsum.comp_injective fun p q h => congrArg Prod.fst h
  apply Nat.Primes.not_summable_one_div
  refine Summable.of_nonneg_of_le
    (fun p => (by positivity : 0 ≤ (1 / (p : ℝ)))) (fun p => ?_) hzero
  rw [xiGammaEulerPrimitiveDescentTestAmplitude_sq_eq_valuation]
  simp only [xiGammaEulerValuationNat, zero_add, pow_one]
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    (Real.log_pos (by exact_mod_cast p.property.one_lt)).le
  have hexp : 1 ≤ Real.exp (-u * Real.log (p : ℝ)) :=
    Real.one_le_exp (mul_nonneg (neg_nonneg.mpr hu) hlog)
  have hmul := mul_le_mul_of_nonneg_left hexp
    (inv_nonneg.mpr (by positivity : 0 ≤ (p : ℝ)))
  simpa only [one_div, mul_one] using hmul

/-- The reciprocal-promotion co-source has the same sharp open Hilbert
chamber as the promoted source. -/
theorem summable_sq_xiGammaEulerPrimitiveDescentTestAmplitude_iff
    (u : ℝ) :
    Summable (fun pe : Nat.Primes × ℕ =>
      xiGammaEulerPrimitiveDescentTestAmplitude u pe ^ 2) ↔
      0 < u := by
  constructor
  · intro hsum
    exact lt_of_not_ge fun hu =>
      not_summable_sq_xiGammaEulerPrimitiveDescentTestAmplitude_of_nonpos hu hsum
  · exact summable_sq_xiGammaEulerPrimitiveDescentTestAmplitude_of_pos

/-- Exact complex Hardy chamber of the primitive-promoted source leg. -/
theorem summable_norm_sq_xiGammaEulerPrimitiveCommonTestSourceCoeff_iff
    (w : ℂ) :
    Summable (fun pe : Nat.Primes × ℕ =>
      ‖xiGammaEulerPrimitiveCommonTestSourceCoeff w pe‖ ^ 2) ↔
      0 < w.re := by
  rw [show (fun pe : Nat.Primes × ℕ =>
      ‖xiGammaEulerPrimitiveCommonTestSourceCoeff w pe‖ ^ 2) =
      fun pe => xiGammaEulerPrimitiveBoundaryAmplitude (2 * w.re) pe ^ 2 by
        funext pe
        rw [xiGammaEulerPrimitiveCommonTestSourceCoeff_norm_sq],
    summable_sq_xiGammaEulerPrimitiveBoundaryAmplitude_iff]
  constructor <;> intro h <;> linarith

/-- Exact complex Hardy chamber of the reciprocal-promotion co-source leg. -/
theorem summable_norm_sq_xiGammaEulerPrimitiveCommonTestCoSourceCoeff_iff
    (w : ℂ) :
    Summable (fun pe : Nat.Primes × ℕ =>
      ‖xiGammaEulerPrimitiveCommonTestCoSourceCoeff w pe‖ ^ 2) ↔
      0 < w.re := by
  rw [show (fun pe : Nat.Primes × ℕ =>
      ‖xiGammaEulerPrimitiveCommonTestCoSourceCoeff w pe‖ ^ 2) =
      fun pe => xiGammaEulerPrimitiveDescentTestAmplitude (2 * w.re) pe ^ 2 by
        funext pe
        rw [xiGammaEulerPrimitiveCommonTestCoSourceCoeff_norm_sq],
    summable_sq_xiGammaEulerPrimitiveDescentTestAmplitude_iff]
  constructor <;> intro h <;> linarith

/-! ## Literal biorthogonal prime-depth-time source -/

/-- Primitive-promoted joint-depth leg with its common Hardy half-line
coordinate retained. -/
def xiGammaEulerPrimitiveBiorthogonalCommonTestSourceFeature
    (w : ℂ) (pe : Nat.Primes × ℕ) (t : ℝ) : ℂ :=
  xiGammaEulerPrimitiveCommonTestSourceCoeff w pe *
    Complex.exp (-w * (t : ℂ))

/-- Reciprocal-promotion joint-depth leg on the same retained Hardy
coordinate. -/
def xiGammaEulerPrimitiveBiorthogonalCommonTestCoSourceFeature
    (v : ℂ) (pe : Nat.Primes × ℕ) (t : ℝ) : ℂ :=
  xiGammaEulerPrimitiveCommonTestCoSourceCoeff v pe *
    Complex.exp (-v * (t : ℂ))

private theorem star_exp_neg_mul_ofReal
    (v : ℂ) (t : ℝ) :
    star (Complex.exp (-v * (t : ℂ))) =
      Complex.exp (-(star v) * (t : ℂ)) := by
  change (starRingEnd ℂ) (Complex.exp (-v * (t : ℂ))) = _
  rw [← Complex.exp_conj]
  congr 1
  simp

/-- Each retained prime-depth coefficient of the reflected pairing is
already independent of centered displacement. -/
theorem xiGammaEulerPrimitiveReflectedCommonTestCoeff_product_eq
    (eps : ℝ) (a : ℂ) (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveCommonTestSourceCoeff
          (xiGammaEulerPrimitiveReflectedHardySourceParameter eps a) pe *
        star (xiGammaEulerPrimitiveCommonTestCoSourceCoeff
          (xiGammaEulerPrimitiveReflectedHardyCoSourceParameter eps a) pe) =
      LSeries.term
        (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
        ((2 * eps : ℝ) + 1) (xiGammaEulerValuationNat pe) := by
  rw [xiGammaEulerPrimitiveCommonTestSourceCoeff_mul_star_coSourceCoeff_eq_term]
  rw [xiGammaEulerPrimitiveReflectedHardyParameter_add_star]

private theorem eulerPrimeCurrentMass_one_add_two_mul_eq_gammaBoundary_sq
    (eps : ℝ) (p : Nat.Primes) :
    eulerPrimeCurrentMass (1 + 2 * eps) (p : ℕ) =
      vonMangoldtGammaRenormalizedBoundaryCoordinate (2 * eps) (p : ℕ) ^ 2 := by
  have hnonneg : 0 ≤
      ArithmeticFunction.vonMangoldt (p : ℕ) / (p : ℝ) *
        Real.exp (-(2 * eps) * Real.log (p : ℝ)) := by
    exact mul_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
      (Real.exp_pos _).le
  rw [vonMangoldtGammaRenormalizedBoundaryCoordinate_eq p.property.two_le,
    Real.sq_sqrt hnonneg]
  rw [eulerPrimeCurrentMass]
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.property.pos
  rw [Real.rpow_def_of_pos hp]
  rw [show Real.log (p : ℝ) * -(1 + 2 * eps) =
      -Real.log (p : ℝ) + (-2 * eps * Real.log (p : ℝ)) by ring,
    Real.exp_add, Real.exp_neg, Real.exp_log hp]
  ring_nf

/-- The maximal regular reflected codiagonal has the sharp chamber
`eps > 0`, independent of horizontal displacement.  This chamber is larger
than simultaneous Hilbert admission of its two unresolved legs. -/
theorem summable_xiGammaEulerPrimitiveReflectedPairedCodiagonal_iff
    (eps : ℝ) (a : ℂ) :
    Summable (fun pe : Nat.Primes × ℕ =>
      xiGammaEulerPrimitiveCommonTestSourceCoeff
          (xiGammaEulerPrimitiveReflectedHardySourceParameter eps a) pe *
        star (xiGammaEulerPrimitiveCommonTestCoSourceCoeff
          (xiGammaEulerPrimitiveReflectedHardyCoSourceParameter eps a) pe)) ↔
      0 < eps := by
  constructor
  · intro hsum
    have hpComplex : Summable (fun p : Nat.Primes =>
        xiGammaEulerPrimitiveCommonTestSourceCoeff
            (xiGammaEulerPrimitiveReflectedHardySourceParameter eps a) (p, 0) *
          star (xiGammaEulerPrimitiveCommonTestCoSourceCoeff
            (xiGammaEulerPrimitiveReflectedHardyCoSourceParameter eps a) (p, 0))) :=
      hsum.comp_injective fun p q h => congrArg Prod.fst h
    have hpReal : Summable (fun p : Nat.Primes =>
        vonMangoldtGammaRenormalizedBoundaryCoordinate (2 * eps) (p : ℕ) ^ 2) := by
      have hre := Complex.reCLM.summable hpComplex
      exact hre.congr fun p => by
        rw [xiGammaEulerPrimitiveReflectedCommonTestCoeff_product_eq]
        simp only [xiGammaEulerValuationNat, zero_add, pow_one]
        rw [show ((2 * eps : ℝ) : ℂ) + 1 = ((1 + 2 * eps : ℝ) : ℂ) by
          push_cast
          ring]
        rw [← ofReal_eulerPrimeCurrentMass_eq]
        rw [Complex.reCLM_apply, Complex.ofReal_re,
          eulerPrimeCurrentMass_one_add_two_mul_eq_gammaBoundary_sq]
    have hpos :=
      (summable_sq_vonMangoldtGammaRenormalizedBoundaryCoordinate_prime_iff
        (2 * eps)).mp hpReal
    linarith
  · intro heps
    apply summable_xiGammaEulerPrimitiveJointDepthPairedCodiagonal_of_re_add_pos
    simp [xiGammaEulerPrimitiveReflectedHardySourceParameter,
      xiGammaEulerPrimitiveReflectedHardyCoSourceParameter]
    linarith

/-- On its maximal regular chamber the reflected codiagonal is the universal
real-displacement von Mangoldt channel and is independent of `a`. -/
theorem xiGammaEulerPrimitiveReflectedPairedCodiagonal_eq
    {eps : ℝ} (a : ℂ) (heps : 0 < eps) :
    xiGammaEulerPrimitiveJointDepthPairedCodiagonal
        (xiGammaEulerPrimitiveReflectedHardySourceParameter eps a)
        (xiGammaEulerPrimitiveReflectedHardyCoSourceParameter eps a) =
      vonMangoldtPrimeLaplaceChannelComplex (2 * eps : ℝ) := by
  rw [xiGammaEulerPrimitiveJointDepthPairedCodiagonal_eq]
  · rw [xiGammaEulerPrimitiveReflectedHardyParameter_add_star]
  · simp [xiGammaEulerPrimitiveReflectedHardySourceParameter,
      xiGammaEulerPrimitiveReflectedHardyCoSourceParameter]
    linarith

/-- **Pointwise reflection-diagonal blindness.**  Horizontal displacement
cancels before the common Hardy coordinate is integrated and before any
prime or valuation-depth label is summed. -/
theorem xiGammaEulerPrimitiveReflectedBiorthogonalCommonTestFeature_product_eq
    (eps : ℝ) (a : ℂ) (pe : Nat.Primes × ℕ) (t : ℝ) :
    xiGammaEulerPrimitiveBiorthogonalCommonTestSourceFeature
          (xiGammaEulerPrimitiveReflectedHardySourceParameter eps a) pe t *
        star (xiGammaEulerPrimitiveBiorthogonalCommonTestCoSourceFeature
          (xiGammaEulerPrimitiveReflectedHardyCoSourceParameter eps a) pe t) =
      LSeries.term
          (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
          ((2 * eps : ℝ) + 1) (xiGammaEulerValuationNat pe) *
        Complex.exp (-(2 * eps : ℝ) * (t : ℂ)) := by
  rw [xiGammaEulerPrimitiveBiorthogonalCommonTestSourceFeature,
    xiGammaEulerPrimitiveBiorthogonalCommonTestCoSourceFeature,
    show star (_ * _) = star (_ : ℂ) * star (_ : ℂ) by
      exact map_mul (starRingEnd ℂ) _ _,
    star_exp_neg_mul_ofReal]
  rw [show
      xiGammaEulerPrimitiveCommonTestSourceCoeff
            (xiGammaEulerPrimitiveReflectedHardySourceParameter eps a) pe *
          Complex.exp
            (-xiGammaEulerPrimitiveReflectedHardySourceParameter eps a * (t : ℂ)) *
        (star (xiGammaEulerPrimitiveCommonTestCoSourceCoeff
            (xiGammaEulerPrimitiveReflectedHardyCoSourceParameter eps a) pe) *
          Complex.exp
            (-star (xiGammaEulerPrimitiveReflectedHardyCoSourceParameter eps a) *
              (t : ℂ))) =
      (xiGammaEulerPrimitiveCommonTestSourceCoeff
            (xiGammaEulerPrimitiveReflectedHardySourceParameter eps a) pe *
          star (xiGammaEulerPrimitiveCommonTestCoSourceCoeff
            (xiGammaEulerPrimitiveReflectedHardyCoSourceParameter eps a) pe)) *
        (Complex.exp
            (-xiGammaEulerPrimitiveReflectedHardySourceParameter eps a * (t : ℂ)) *
          Complex.exp
            (-star (xiGammaEulerPrimitiveReflectedHardyCoSourceParameter eps a) *
              (t : ℂ))) by ring,
    xiGammaEulerPrimitiveReflectedCommonTestCoeff_product_eq,
    ← Complex.exp_add]
  congr 1
  rw [show
      -xiGammaEulerPrimitiveReflectedHardySourceParameter eps a * (t : ℂ) +
          -star (xiGammaEulerPrimitiveReflectedHardyCoSourceParameter eps a) *
            (t : ℂ) =
        -(xiGammaEulerPrimitiveReflectedHardySourceParameter eps a +
            star (xiGammaEulerPrimitiveReflectedHardyCoSourceParameter eps a)) *
          (t : ℂ) by ring,
    xiGammaEulerPrimitiveReflectedHardyParameter_add_star]

/-- The literal biorthogonal common-test fibre integrates to its von
Mangoldt Dirichlet coefficient times the common Hardy Cauchy factor. -/
theorem integral_xiGammaEulerPrimitiveBiorthogonalCommonTestFeature
    {w v : ℂ} (hw : 0 < w.re) (hv : 0 < v.re)
    (pe : Nat.Primes × ℕ) :
    (∫ t : ℝ in Ioi 0,
      xiGammaEulerPrimitiveBiorthogonalCommonTestSourceFeature w pe t *
        star (xiGammaEulerPrimitiveBiorthogonalCommonTestCoSourceFeature v pe t)) =
      LSeries.term
          (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
          (w + star v + 1) (xiGammaEulerValuationNat pe) *
        (1 / (w + star v)) := by
  have hrate : 0 < (w + star v).re := by
    change 0 < w.re + v.re
    linarith
  have hfun :
      (fun t : ℝ =>
        xiGammaEulerPrimitiveBiorthogonalCommonTestSourceFeature w pe t *
          star (xiGammaEulerPrimitiveBiorthogonalCommonTestCoSourceFeature v pe t)) =
      fun t : ℝ =>
        (xiGammaEulerPrimitiveCommonTestSourceCoeff w pe *
          star (xiGammaEulerPrimitiveCommonTestCoSourceCoeff v pe)) *
          Complex.exp (-(w + star v) * (t : ℂ)) := by
    funext t
    rw [xiGammaEulerPrimitiveBiorthogonalCommonTestSourceFeature,
      xiGammaEulerPrimitiveBiorthogonalCommonTestCoSourceFeature,
      show star (_ * _) = star (_ : ℂ) * star (_ : ℂ) by
        exact map_mul (starRingEnd ℂ) _ _,
      star_exp_neg_mul_ofReal]
    rw [show
        xiGammaEulerPrimitiveCommonTestSourceCoeff w pe *
              Complex.exp (-w * (t : ℂ)) *
            (star (xiGammaEulerPrimitiveCommonTestCoSourceCoeff v pe) *
              Complex.exp (-(star v) * (t : ℂ))) =
          (xiGammaEulerPrimitiveCommonTestSourceCoeff w pe *
            star (xiGammaEulerPrimitiveCommonTestCoSourceCoeff v pe)) *
            (Complex.exp (-w * (t : ℂ)) *
              Complex.exp (-(star v) * (t : ℂ))) by ring,
      ← Complex.exp_add]
    congr 1
    ring_nf
  rw [hfun, integral_const_mul, integral_cauchyFeaturePair hrate,
    xiGammaEulerPrimitiveCommonTestSourceCoeff_mul_star_coSourceCoeff_eq_term]

/-! ## Full diagonal pairing and sharp wall -/

/-- The full joint-depth Hilbert pairing after reflection sewing is the
universal real-displacement von Mangoldt channel. -/
theorem inner_xiGammaEulerPrimitiveReflectedCommonTest_eq
    (eps : ℝ) (a : ℂ)
    (hS : 0 < (xiGammaEulerPrimitiveReflectedHardySourceParameter eps a).re)
    (hC : 0 < (xiGammaEulerPrimitiveReflectedHardyCoSourceParameter eps a).re) :
    inner ℂ
        (xiGammaEulerPrimitiveCommonTestCoSourceLp
          (xiGammaEulerPrimitiveReflectedHardyCoSourceParameter eps a) hC)
        (xiGammaEulerPrimitiveCommonTestSourceLp
          (xiGammaEulerPrimitiveReflectedHardySourceParameter eps a) hS) =
      vonMangoldtPrimeLaplaceChannelComplex (2 * eps : ℝ) := by
  rw [inner_xiGammaEulerPrimitiveCommonTestCoSource_source_eq]
  rw [xiGammaEulerPrimitiveReflectedHardyParameter_add_star]

/-- Reflected diagonal common-test pairing with proofs of joint Hilbert
admission retained in its type. -/
def xiGammaEulerPrimitiveReflectedJointDepthCommonTestPairing
    (eps : ℝ) (a : ℂ)
    (hS : 0 < (xiGammaEulerPrimitiveReflectedHardySourceParameter eps a).re)
    (hC : 0 < (xiGammaEulerPrimitiveReflectedHardyCoSourceParameter eps a).re) : ℂ :=
  xiGammaEulerPrimitiveJointDepthCommonTestPairing
    (xiGammaEulerPrimitiveReflectedHardySourceParameter eps a)
    (xiGammaEulerPrimitiveReflectedHardyCoSourceParameter eps a) hS hC

/-- **Global reflection-diagonal blindness.**  The complete common-test
value depends only on regularization depth `eps`, not on `a`. -/
theorem xiGammaEulerPrimitiveReflectedJointDepthCommonTestPairing_eq
    (eps : ℝ) (a : ℂ)
    (hS : 0 < (xiGammaEulerPrimitiveReflectedHardySourceParameter eps a).re)
    (hC : 0 < (xiGammaEulerPrimitiveReflectedHardyCoSourceParameter eps a).re) :
    xiGammaEulerPrimitiveReflectedJointDepthCommonTestPairing eps a hS hC =
      vonMangoldtPrimeLaplaceChannelComplex (2 * eps : ℝ) *
        (1 / (2 * eps : ℝ)) := by
  rw [xiGammaEulerPrimitiveReflectedJointDepthCommonTestPairing,
    xiGammaEulerPrimitiveJointDepthCommonTestPairing_eq,
    eulerPrimitiveCommonTestKernel,
    xiGammaEulerPrimitiveReflectedHardyParameter_add_star]

/-- Sharp joint Hilbert-admission threshold of the unresolved reflected
source/co-source pair. -/
theorem xiGammaEulerPrimitiveReflectedCommonTest_jointSummable_iff
    (eps : ℝ) (a : ℂ) :
    (Summable (fun pe : Nat.Primes × ℕ =>
        ‖xiGammaEulerPrimitiveCommonTestSourceCoeff
          (xiGammaEulerPrimitiveReflectedHardySourceParameter eps a) pe‖ ^ 2) ∧
      Summable (fun pe : Nat.Primes × ℕ =>
        ‖xiGammaEulerPrimitiveCommonTestCoSourceCoeff
          (xiGammaEulerPrimitiveReflectedHardyCoSourceParameter eps a) pe‖ ^ 2)) ↔
      |a.re| < eps := by
  rw [summable_norm_sq_xiGammaEulerPrimitiveCommonTestSourceCoeff_iff,
    summable_norm_sq_xiGammaEulerPrimitiveCommonTestCoSourceCoeff_iff,
    xiGammaEulerPrimitiveReflectedHardy_jointAdmissible_iff]

/-- Between the paired wall and the individual-leg wall, the complete
codiagonal is absolutely summable although no two-vector Hilbert pairing
exists.  This is the exact regular-but-non-Hilbert reflection chamber. -/
theorem xiGammaEulerPrimitiveReflectedCommonTest_paired_not_joint
    {eps : ℝ} {a : ℂ} (heps : 0 < eps) (hwall : eps ≤ |a.re|) :
    Summable (fun pe : Nat.Primes × ℕ =>
        xiGammaEulerPrimitiveCommonTestSourceCoeff
            (xiGammaEulerPrimitiveReflectedHardySourceParameter eps a) pe *
          star (xiGammaEulerPrimitiveCommonTestCoSourceCoeff
            (xiGammaEulerPrimitiveReflectedHardyCoSourceParameter eps a) pe)) ∧
      ¬(Summable (fun pe : Nat.Primes × ℕ =>
          ‖xiGammaEulerPrimitiveCommonTestSourceCoeff
            (xiGammaEulerPrimitiveReflectedHardySourceParameter eps a) pe‖ ^ 2) ∧
        Summable (fun pe : Nat.Primes × ℕ =>
          ‖xiGammaEulerPrimitiveCommonTestCoSourceCoeff
            (xiGammaEulerPrimitiveReflectedHardyCoSourceParameter eps a) pe‖ ^ 2)) := by
  constructor
  · exact
      (summable_xiGammaEulerPrimitiveReflectedPairedCodiagonal_iff eps a).2 heps
  · rw [xiGammaEulerPrimitiveReflectedCommonTest_jointSummable_iff]
    exact not_lt_of_ge hwall

/-- At the minimal regularization depth the unresolved reflected pair is
never jointly Hilbert. -/
theorem xiGammaEulerPrimitiveReflectedCommonTest_not_jointSummable_at_threshold
    (a : ℂ) :
    ¬(Summable (fun pe : Nat.Primes × ℕ =>
        ‖xiGammaEulerPrimitiveCommonTestSourceCoeff
          (xiGammaEulerPrimitiveReflectedHardySourceParameter |a.re| a) pe‖ ^ 2) ∧
      Summable (fun pe : Nat.Primes × ℕ =>
        ‖xiGammaEulerPrimitiveCommonTestCoSourceCoeff
          (xiGammaEulerPrimitiveReflectedHardyCoSourceParameter |a.re| a) pe‖ ^ 2)) := by
  rw [xiGammaEulerPrimitiveReflectedCommonTest_jointSummable_iff]
  exact lt_irrefl _

/-- At an actual centered spectral coordinate `rho - 1/2`, the chamber wall
is exactly absolute horizontal displacement from the critical line. -/
theorem xiGammaEulerPrimitiveReflectedCommonTest_rho_jointSummable_iff
    (eps : ℝ) (rho : ℂ) :
    (Summable (fun pe : Nat.Primes × ℕ =>
        ‖xiGammaEulerPrimitiveCommonTestSourceCoeff
          (xiGammaEulerPrimitiveReflectedHardySourceParameter
            eps (rho - 1 / 2)) pe‖ ^ 2) ∧
      Summable (fun pe : Nat.Primes × ℕ =>
        ‖xiGammaEulerPrimitiveCommonTestCoSourceCoeff
          (xiGammaEulerPrimitiveReflectedHardyCoSourceParameter
            eps (rho - 1 / 2)) pe‖ ^ 2)) ↔
      |rho.re - 1 / 2| < eps := by
  rw [xiGammaEulerPrimitiveReflectedCommonTest_jointSummable_iff]
  norm_num

end

end RHTower
