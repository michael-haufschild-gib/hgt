import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryKreinCrossing
import GaloisForLFunctions.RHTower.XiShiftedReciprocalHankelTailCriterion
import GaloisForLFunctions.RHTower.Suzuki.SuzukiSafeShiftResponseChargeCancellation
import GaloisForLFunctions.RHTower.XiSquaredEulerAllDegreeChargeCriterion

/-!
# Shifted Xi null faces as Hilbert--charge saturation flow

The all-degree squared-Euler decomposition is extended from the central reciprocal-square divisor
to every positive Möbius mass shift.  Both its positive sheared-evaluation channel and its
transverse channel are summable.  Their difference is the actual shifted trace-Hankel form.
Line conjugation makes the longitudinal feature even and the transverse feature odd, so every
mixed polynomial correlation vanishes and the two complete Hilbert channels are orthogonal.

Consequently a polynomial selected by a singular shifted Hankel face exactly saturates the two
nonnegative channels and defines an isometric lightlike polynomial flag.  The first variation of
this saturated equality is the intrinsic terminal/first-omitted Krein crossing flux.  In the
negative-binomial window this crossing is exactly a zero-free prime--Gamma moment pairing; on the
whole Euler ray its derivative is the completed-source boundary jet.  This identifies the exact
remaining source task: strict decay of the longitudinal-minus-transverse gap at completed-source
null incidence.
-/

open Complex Polynomial Filter Topology Matrix Set
open scoped BigOperators

namespace HTGeometry

noncomputable section

/-- Polarized positive channel behind the oriented complex-square decomposition. -/
def orientedComplexBilinearHilbertTerm (lam u v : ℂ) : ℝ :=
  lam.re *
    (u.re - lam.im / lam.re * u.im) *
    (v.re - lam.im / lam.re * v.im)

/-- Polarized transverse channel behind the oriented complex-square decomposition. -/
def orientedComplexBilinearTransverseTerm (lam u v : ℂ) : ℝ :=
  Complex.normSq lam / lam.re * u.im * v.im

/-- Exact polarized longitudinal-minus-transverse law. -/
theorem re_mul_mul_eq_orientedBilinearHilbert_sub_transverse
    (lam u v : ℂ) (hlam : lam.re ≠ 0) :
    (lam * u * v).re =
      orientedComplexBilinearHilbertTerm lam u v -
        orientedComplexBilinearTransverseTerm lam u v := by
  unfold orientedComplexBilinearHilbertTerm orientedComplexBilinearTransverseTerm
  rw [Complex.mul_re, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  field_simp [hlam]
  ring

/-- Polarization identity for every real moment bilinear form. -/
theorem momentInner_polarization (s : ℕ → ℝ) (p r : Polynomial ℝ) :
    (momentInner s (p + r) (p + r) -
        momentInner s (p - r) (p - r)) / 4 =
      momentInner s p r := by
  have hnegRight : momentInner s p (-r) = -momentInner s p r := by
    rw [show -r = (-1 : ℝ) • r by simp, momentInner_smul_right]
    ring
  have hnegSelf : momentInner s (-r) (-r) = momentInner s r r := by
    rw [show -r = (-1 : ℝ) • r by simp,
      momentInner_smul_left, momentInner_smul_right]
    ring
  simp only [sub_eq_add_neg, momentInner_add_right, momentInner_comm]
  rw [hnegRight, hnegSelf]
  ring

end


end HTGeometry

namespace RHTower

noncomputable section

/-- Sheared real evaluation in the positive channel of a shifted reciprocal-square atom. -/
def xiShiftedApertureShearedEvaluation
    (y : ℝ) (p : Polynomial ℝ) (q : XiZeroCopy) : ℝ :=
  let lam := xiShiftedReciprocalSquare y q
  let w := evalRealPolynomial p lam
  w.re - lam.im / lam.re * w.im

/-- Critical-line conjugation conjugates the central reciprocal-square atom. -/
theorem xiZeroCopyReciprocalSquare_lineConj (q : XiZeroCopy) :
    xiZeroCopyReciprocalSquare (xiZeroCopyLineConjEquiv q) =
      (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q) := by
  simp [xiZeroCopyReciprocalSquare, xiSpectralPoint_lineConj, map_inv₀]

/-- Every real mass shift commutes with critical-line conjugation. -/
theorem xiShiftedReciprocalSquare_lineConj (y : ℝ) (q : XiZeroCopy) :
    xiShiftedReciprocalSquare y (xiZeroCopyLineConjEquiv q) =
      (starRingEnd ℂ) (xiShiftedReciprocalSquare y q) := by
  simp [xiShiftedReciprocalSquare, xiZeroCopyReciprocalSquare_lineConj]

/-- The longitudinal feature of a real polynomial is even under line conjugation. -/
theorem xiShiftedApertureShearedEvaluation_lineConj
    (y : ℝ) (p : Polynomial ℝ) (q : XiZeroCopy) :
    xiShiftedApertureShearedEvaluation y p (xiZeroCopyLineConjEquiv q) =
      xiShiftedApertureShearedEvaluation y p q := by
  rw [xiShiftedApertureShearedEvaluation, xiShiftedApertureShearedEvaluation,
    xiShiftedReciprocalSquare_lineConj, evalRealPolynomial_conj]
  simp
  ring

/-- Positive Hilbert channel of one shifted reciprocal-square atom. -/
def xiShiftedApertureHilbertTerm
    (y : ℝ) (p : Polynomial ℝ) (q : XiZeroCopy) : ℝ :=
  let lam := xiShiftedReciprocalSquare y q
  lam.re * (xiShiftedApertureShearedEvaluation y p q) ^ (2 : ℕ)

/-- Transverse charge channel of one shifted reciprocal-square atom. -/
def xiShiftedApertureTransverseTerm
    (y : ℝ) (p : Polynomial ℝ) (q : XiZeroCopy) : ℝ :=
  let lam := xiShiftedReciprocalSquare y q
  Complex.normSq lam / lam.re * (evalRealPolynomial p lam).im ^ (2 : ℕ)

/-- Mixed longitudinal/transverse feature product for two real polynomial probes. -/
def xiShiftedApertureMixedPairTerm
    (y : ℝ) (p r : Polynomial ℝ) (q : XiZeroCopy) : ℝ :=
  xiShiftedApertureShearedEvaluation y p q *
    ‖xiShiftedReciprocalSquare y q‖ *
    (evalRealPolynomial r (xiShiftedReciprocalSquare y q)).im

/-- Mixed longitudinal/transverse feature products are odd under line conjugation. -/
theorem xiShiftedApertureMixedPairTerm_lineConj
    (y : ℝ) (p r : Polynomial ℝ) (q : XiZeroCopy) :
    xiShiftedApertureMixedPairTerm y p r (xiZeroCopyLineConjEquiv q) =
      -xiShiftedApertureMixedPairTerm y p r q := by
  simp only [xiShiftedApertureMixedPairTerm,
    xiShiftedApertureShearedEvaluation_lineConj,
    xiShiftedReciprocalSquare_lineConj, Complex.norm_conj,
    evalRealPolynomial_conj, Complex.conj_im]
  ring

/-- Real trace-Hankel contribution of one shifted reciprocal-square atom. -/
def xiShiftedApertureHankelTerm
    (y : ℝ) (p : Polynomial ℝ) (q : XiZeroCopy) : ℝ :=
  (xiShiftedReciprocalTraceHankelTerm y p q).re

/-- Longitudinal cross-channel contribution of two polynomial probes at one shifted atom. -/
def xiShiftedApertureHilbertPairTerm
    (y : ℝ) (p r : Polynomial ℝ) (q : XiZeroCopy) : ℝ :=
  HTGeometry.orientedComplexBilinearHilbertTerm
    (xiShiftedReciprocalSquare y q)
    (evalRealPolynomial p (xiShiftedReciprocalSquare y q))
    (evalRealPolynomial r (xiShiftedReciprocalSquare y q))

/-- Transverse cross-channel contribution of two polynomial probes at one shifted atom. -/
def xiShiftedApertureTransversePairTerm
    (y : ℝ) (p r : Polynomial ℝ) (q : XiZeroCopy) : ℝ :=
  HTGeometry.orientedComplexBilinearTransverseTerm
    (xiShiftedReciprocalSquare y q)
    (evalRealPolynomial p (xiShiftedReciprocalSquare y q))
    (evalRealPolynomial r (xiShiftedReciprocalSquare y q))

/-- Real polarized trace-Hankel contribution of two polynomial probes at one shifted atom. -/
def xiShiftedApertureHankelPairTerm
    (y : ℝ) (p r : Polynomial ℝ) (q : XiZeroCopy) : ℝ :=
  (xiShiftedReciprocalSquare y q *
    evalRealPolynomial p (xiShiftedReciprocalSquare y q) *
    evalRealPolynomial r (xiShiftedReciprocalSquare y q)).re

/-- Positive longitudinal transport created by multiplication by `X`.  The coefficient is
strictly positive at every positive mass shift because shifted reciprocal-square atoms lie in the
open sector `|Im lam| < Re lam`. -/
def xiShiftedApertureLorentzLongitudinalTerm
    (y : ℝ) (p : Polynomial ℝ) (q : XiZeroCopy) : ℝ :=
  let lam := xiShiftedReciprocalSquare y q
  (lam.re ^ (2 : ℕ) - lam.im ^ (2 : ℕ)) *
    (xiShiftedApertureShearedEvaluation y p q) ^ (2 : ℕ)

/-- Phase-weighted shear created by multiplication by `X`.  Unlike the unweighted mixed channel,
this term is even under line conjugation and therefore survives orbit summation. -/
def xiShiftedApertureLorentzShearTerm
    (y : ℝ) (p : Polynomial ℝ) (q : XiZeroCopy) : ℝ :=
  let lam := xiShiftedReciprocalSquare y q
  2 * lam.im * Complex.normSq lam / lam.re *
    xiShiftedApertureShearedEvaluation y p q *
      (evalRealPolynomial p lam).im

/-- Positive transverse transport created by multiplication by `X`. -/
def xiShiftedApertureLorentzTransverseTerm
    (y : ℝ) (p : Polynomial ℝ) (q : XiZeroCopy) : ℝ :=
  let lam := xiShiftedReciprocalSquare y q
  (Complex.normSq lam / lam.re) ^ (2 : ℕ) *
    (evalRealPolynomial p lam).im ^ (2 : ℕ)

/-- Multiplication by `X` acts on the sheared longitudinal and imaginary coordinates by an exact
Lorentz-type transfer.  Its oriented crossing is longitudinal transport minus the phase-weighted
shear and transverse transport. -/
theorem xiShiftedApertureHankelPairTerm_X_mul_eq_lorentzTransport
    {y : ℝ} (hy : 0 < y) (p : Polynomial ℝ) (q : XiZeroCopy) :
    xiShiftedApertureHankelPairTerm y p (X * p) q =
      xiShiftedApertureLorentzLongitudinalTerm y p q -
        xiShiftedApertureLorentzShearTerm y p q -
          xiShiftedApertureLorentzTransverseTerm y p q := by
  let lam := xiShiftedReciprocalSquare y q
  let w := evalRealPolynomial p lam
  have hlam : lam.re ≠ 0 := by
    simpa only [lam, xiShiftedResponseMass, pow_one] using
      (xiShiftedResponseMass_pos hy q).ne'
  have hX : evalRealPolynomial (X * p) lam = lam * w := by
    rw [evalRealPolynomial_mul]
    have hx : evalRealPolynomial X lam = lam := by
      simp [evalRealPolynomial]
    rw [hx]
  rw [xiShiftedApertureHankelPairTerm, hX]
  change (lam * w * (lam * w)).re =
    (lam.re ^ (2 : ℕ) - lam.im ^ (2 : ℕ)) *
          (w.re - lam.im / lam.re * w.im) ^ (2 : ℕ) -
        2 * lam.im * Complex.normSq lam / lam.re *
          (w.re - lam.im / lam.re * w.im) * w.im -
      (Complex.normSq lam / lam.re) ^ (2 : ℕ) * w.im ^ (2 : ℕ)
  rw [Complex.mul_re, Complex.mul_re, Complex.mul_im,
    Complex.normSq_apply]
  field_simp [hlam]
  ring

/-- The longitudinal Lorentz transport coefficient is strictly positive. -/
theorem xiShiftedApertureLorentzLongitudinalTerm_nonneg
    {y : ℝ} (hy : 0 < y) (p : Polynomial ℝ) (q : XiZeroCopy) :
    0 ≤ xiShiftedApertureLorentzLongitudinalTerm y p q := by
  unfold xiShiftedApertureLorentzLongitudinalTerm
  exact mul_nonneg
    (sub_nonneg.mpr
      (le_of_lt (xiShiftedReciprocalSquare_im_sq_lt_re_sq hy q)))
    (sq_nonneg _)

/-- The transverse Lorentz transport is nonnegative. -/
theorem xiShiftedApertureLorentzTransverseTerm_nonneg
    (y : ℝ) (p : Polynomial ℝ) (q : XiZeroCopy) :
    0 ≤ xiShiftedApertureLorentzTransverseTerm y p q := by
  unfold xiShiftedApertureLorentzTransverseTerm
  positivity

/-- Longitudinal Lorentz transport is response slope times the original Hilbert energy. -/
theorem xiShiftedApertureLorentzLongitudinalTerm_eq_slope_mul_hilbert
    {y : ℝ} (hy : 0 < y) (p : Polynomial ℝ) (q : XiZeroCopy) :
    xiShiftedApertureLorentzLongitudinalTerm y p q =
      xiShiftedResponseSlope y q * xiShiftedApertureHilbertTerm y p q := by
  let lam := xiShiftedReciprocalSquare y q
  have hlam : lam.re ≠ 0 := by
    simpa only [lam, xiShiftedResponseMass] using
      (xiShiftedResponseMass_pos hy q).ne'
  unfold xiShiftedApertureLorentzLongitudinalTerm xiShiftedResponseSlope
    xiShiftedResponseMass xiShiftedApertureHilbertTerm
  change (lam.re ^ (2 : ℕ) - lam.im ^ (2 : ℕ)) * _ = (lam ^ (2 : ℕ)).re / lam.re * (lam.re * _)
  have hsquare : (lam ^ (2 : ℕ)).re = lam.re ^ (2 : ℕ) - lam.im ^ (2 : ℕ) := by
    rw [show lam ^ (2 : ℕ) = lam * lam by ring, Complex.mul_re]
    ring
  rw [hsquare]
  field_simp [hlam]

/-- Transverse Lorentz transport is the shifted transverse coefficient times the original
transverse energy. -/
theorem xiShiftedApertureLorentzTransverseTerm_eq_weight_mul_transverse
    {y : ℝ} (hy : 0 < y) (p : Polynomial ℝ) (q : XiZeroCopy) :
    xiShiftedApertureLorentzTransverseTerm y p q =
      (Complex.normSq (xiShiftedReciprocalSquare y q) /
          (xiShiftedReciprocalSquare y q).re) *
        xiShiftedApertureTransverseTerm y p q := by
  have hlam : (xiShiftedReciprocalSquare y q).re ≠ 0 := by
    simpa only [xiShiftedResponseMass] using
      (xiShiftedResponseMass_pos hy q).ne'
  unfold xiShiftedApertureLorentzTransverseTerm
    xiShiftedApertureTransverseTerm
  field_simp [hlam]

/-- The surviving Lorentz shear is a phase weight times the mixed feature whose unweighted sum
vanishes.  Variation of this weight across zero orbits is the precise obstruction to using channel
orthogonality alone. -/
theorem xiShiftedApertureLorentzShearTerm_eq_phaseWeight_mul_mixed
    {y : ℝ} (hy : 0 < y) (p : Polynomial ℝ) (q : XiZeroCopy) :
    xiShiftedApertureLorentzShearTerm y p q =
      (2 * (xiShiftedReciprocalSquare y q).im *
          ‖xiShiftedReciprocalSquare y q‖ /
            (xiShiftedReciprocalSquare y q).re) *
        xiShiftedApertureMixedPairTerm y p p q := by
  let lam := xiShiftedReciprocalSquare y q
  have hlam : lam.re ≠ 0 := by
    simpa only [lam, xiShiftedResponseMass] using
      (xiShiftedResponseMass_pos hy q).ne'
  unfold xiShiftedApertureLorentzShearTerm xiShiftedApertureMixedPairTerm
  change 2 * lam.im * Complex.normSq lam / lam.re * _ * _ =
    (2 * lam.im * ‖lam‖ / lam.re) * (_ * ‖lam‖ * _)
  rw [Complex.normSq_eq_norm_sq]
  field_simp [hlam]

/-- The phase-weighted shear is even under critical-line conjugation.  Thus the conjugation that
kills ordinary mixed covariance cannot remove the shear governing marked `X`-crossing. -/
theorem xiShiftedApertureLorentzShearTerm_lineConj
    (y : ℝ) (p : Polynomial ℝ) (q : XiZeroCopy) :
    xiShiftedApertureLorentzShearTerm y p (xiZeroCopyLineConjEquiv q) =
      xiShiftedApertureLorentzShearTerm y p q := by
  simp only [xiShiftedApertureLorentzShearTerm,
    xiShiftedReciprocalSquare_lineConj,
    xiShiftedApertureShearedEvaluation_lineConj,
    evalRealPolynomial_conj, Complex.conj_re, Complex.conj_im,
    Complex.normSq_conj]
  ring

/-- Exact atomwise polarized Hilbert-minus-transverse decomposition. -/
theorem xiShiftedApertureHankelPairTerm_eq_hilbert_sub_transverse
    {y : ℝ} (hy : 0 < y) (p r : Polynomial ℝ) (q : XiZeroCopy) :
    xiShiftedApertureHankelPairTerm y p r q =
      xiShiftedApertureHilbertPairTerm y p r q -
        xiShiftedApertureTransversePairTerm y p r q := by
  have hlam : (xiShiftedReciprocalSquare y q).re ≠ 0 := by
    simpa only [xiShiftedResponseMass, pow_one] using
      (xiShiftedResponseMass_pos hy q).ne'
  exact HTGeometry.re_mul_mul_eq_orientedBilinearHilbert_sub_transverse
    (xiShiftedReciprocalSquare y q)
    (evalRealPolynomial p (xiShiftedReciprocalSquare y q))
    (evalRealPolynomial r (xiShiftedReciprocalSquare y q)) hlam

/-- Exact shifted atomwise Hilbert-minus-transverse decomposition. -/
theorem xiShiftedApertureHankelTerm_eq_hilbert_sub_transverse
    {y : ℝ} (hy : 0 < y) (p : Polynomial ℝ) (q : XiZeroCopy) :
    xiShiftedApertureHankelTerm y p q =
      xiShiftedApertureHilbertTerm y p q -
        xiShiftedApertureTransverseTerm y p q := by
  let lam := xiShiftedReciprocalSquare y q
  let w := evalRealPolynomial p lam
  have hlam : lam.re ≠ 0 := by
    have hpos := xiShiftedResponseMass_pos hy q
    simpa only [xiShiftedResponseMass, pow_one, lam] using hpos.ne'
  simpa only [xiShiftedApertureHankelTerm,
    xiShiftedReciprocalTraceHankelTerm,
    xiShiftedApertureHilbertTerm,
    xiShiftedApertureShearedEvaluation,
    xiShiftedApertureTransverseTerm, lam, w,
    HTGeometry.orientedComplexSquareHilbertTerm,
    HTGeometry.orientedComplexSquareTransverseTerm] using
      HTGeometry.re_mul_sq_eq_orientedHilbert_sub_transverse lam w hlam

/-- Shifted transverse coefficient is bounded by twice the positive real mass. -/
theorem xiShiftedReciprocalSquare_normSq_div_re_lt_two_mul_re
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    Complex.normSq (xiShiftedReciprocalSquare y q) /
        (xiShiftedReciprocalSquare y q).re <
      2 * (xiShiftedReciprocalSquare y q).re := by
  let z := xiShiftedReciprocalSquare y q
  have hz : 0 < z.re := by
    simpa only [z, xiShiftedResponseMass, pow_one] using
      xiShiftedResponseMass_pos hy q
  have hsector : z.im ^ (2 : ℕ) < z.re ^ (2 : ℕ) := by
    simpa only [z] using xiShiftedReciprocalSquare_im_sq_lt_re_sq hy q
  apply (div_lt_iff₀ hz).2
  rw [Complex.normSq_apply]
  nlinarith

/-- Shifted Hilbert atom is nonnegative. -/
theorem xiShiftedApertureHilbertTerm_nonneg
    {y : ℝ} (hy : 0 < y) (p : Polynomial ℝ) (q : XiZeroCopy) :
    0 ≤ xiShiftedApertureHilbertTerm y p q := by
  unfold xiShiftedApertureHilbertTerm
  exact mul_nonneg
    (by
      simpa only [xiShiftedResponseMass, pow_one] using
        (xiShiftedResponseMass_pos hy q).le)
    (sq_nonneg _)

/-- Shifted transverse-charge atom is nonnegative. -/
theorem xiShiftedApertureTransverseTerm_nonneg
    {y : ℝ} (hy : 0 < y) (p : Polynomial ℝ) (q : XiZeroCopy) :
    0 ≤ xiShiftedApertureTransverseTerm y p q := by
  unfold xiShiftedApertureTransverseTerm
  have hre : 0 ≤ (xiShiftedReciprocalSquare y q).re := by
    simpa only [xiShiftedResponseMass, pow_one] using
      (xiShiftedResponseMass_pos hy q).le
  exact mul_nonneg (div_nonneg (Complex.normSq_nonneg _) hre) (sq_nonneg _)

/-- Complete shifted transverse charge is summable at every polynomial degree. -/
theorem summable_xiShiftedApertureTransverseTerm
    {y : ℝ} (hy : 0 < y) (p : Polynomial ℝ) :
    Summable (xiShiftedApertureTransverseTerm y p) := by
  obtain ⟨M, hMone, hM⟩ := exists_xi_central_reciprocal_square_norm_bound
  let C := evalRealPolynomialNormBound p M
  have hC : 0 ≤ C :=
    evalRealPolynomialNormBound_nonneg p (le_trans zero_le_one hMone)
  have hre : Summable (fun q : XiZeroCopy =>
      (xiShiftedReciprocalSquare y q).re) := by
    have hs := Complex.reCLM.summable
      (summable_xiShiftedReciprocalSquare_pow hy.le 0)
    exact hs.congr (fun q => by simp)
  have hbound : Summable (fun q : XiZeroCopy =>
      (2 * C ^ (2 : ℕ)) * (xiShiftedReciprocalSquare y q).re) :=
    hre.mul_left (2 * C ^ (2 : ℕ))
  apply Summable.of_nonneg_of_le
    (fun q => xiShiftedApertureTransverseTerm_nonneg hy p q)
    (fun q => ?_) hbound
  let z := xiShiftedReciprocalSquare y q
  let w := evalRealPolynomial p z
  have hw : ‖w‖ ≤ C := by
    apply norm_evalRealPolynomial_le p
    exact (norm_xiShiftedReciprocalSquare_le hy.le q).trans (by
      simpa only [xiZeroCopyReciprocalSquare_eq] using hM q.1)
  have him : w.im ^ (2 : ℕ) ≤ C ^ (2 : ℕ) := by
    have hi := Complex.abs_im_le_norm w
    have habs : |w.im| ≤ C := hi.trans hw
    have hprod : 0 ≤ (C - |w.im|) * (C + |w.im|) :=
      mul_nonneg (sub_nonneg.mpr habs) (add_nonneg hC (abs_nonneg _))
    nlinarith [sq_abs w.im]
  have hratio := xiShiftedReciprocalSquare_normSq_div_re_lt_two_mul_re hy q
  have hratio0 : 0 ≤ Complex.normSq z / z.re := by
    exact div_nonneg (Complex.normSq_nonneg z)
      (by
        simpa only [z, xiShiftedResponseMass, pow_one] using
          (xiShiftedResponseMass_pos hy q).le)
  unfold xiShiftedApertureTransverseTerm
  change Complex.normSq z / z.re * w.im ^ (2 : ℕ) ≤ (2 * C ^ (2 : ℕ)) * z.re
  calc
    Complex.normSq z / z.re * w.im ^ (2 : ℕ) ≤
        Complex.normSq z / z.re * C ^ (2 : ℕ) := by gcongr
    _ ≤ (2 * z.re) * C ^ (2 : ℕ) := by gcongr
    _ = (2 * C ^ (2 : ℕ)) * z.re := by ring

/-- Real shifted trace-Hankel atoms are summable. -/
theorem summable_xiShiftedApertureHankelTerm
    {y : ℝ} (hy : 0 < y) (p : Polynomial ℝ) :
    Summable (xiShiftedApertureHankelTerm y p) := by
  have hs := Complex.reCLM.summable
    (summable_xiShiftedReciprocalTraceHankelTerm hy.le p)
  exact hs.congr (fun q => rfl)

/-- Complete shifted positive Hilbert channel is summable at every polynomial degree. -/
theorem summable_xiShiftedApertureHilbertTerm
    {y : ℝ} (hy : 0 < y) (p : Polynomial ℝ) :
    Summable (xiShiftedApertureHilbertTerm y p) := by
  have hh := summable_xiShiftedApertureHankelTerm hy p
  have ht := summable_xiShiftedApertureTransverseTerm hy p
  apply (hh.add ht).congr
  intro q
  have hsplit := xiShiftedApertureHankelTerm_eq_hilbert_sub_transverse hy p q
  linarith

/-- Mixed feature product is pointwise dominated by half the sum of its two channel energies. -/
theorem norm_xiShiftedApertureMixedPairTerm_le
    {y : ℝ} (hy : 0 < y) (p r : Polynomial ℝ) (q : XiZeroCopy) :
    ‖xiShiftedApertureMixedPairTerm y p r q‖ ≤
      (xiShiftedApertureHilbertTerm y p q +
        xiShiftedApertureTransverseTerm y r q) / 2 := by
  let lam := xiShiftedReciprocalSquare y q
  let s := xiShiftedApertureShearedEvaluation y p q
  let v := (evalRealPolynomial r lam).im
  let n := ‖lam‖
  have ha : 0 < lam.re := by
    simpa only [lam, xiShiftedResponseMass] using xiShiftedResponseMass_pos hy q
  have hn : 0 ≤ n := norm_nonneg _
  have hsquare : 0 ≤ (lam.re * |s| - n * |v|) ^ (2 : ℕ) := sq_nonneg _
  have hnormsq : Complex.normSq lam = n ^ (2 : ℕ) := Complex.normSq_eq_norm_sq lam
  unfold xiShiftedApertureMixedPairTerm xiShiftedApertureHilbertTerm
    xiShiftedApertureTransverseTerm
  change |s * n * v| ≤ (lam.re * s ^ (2 : ℕ) + Complex.normSq lam / lam.re * v ^ (2 : ℕ)) / 2
  rw [abs_mul, abs_mul, abs_of_nonneg hn, hnormsq]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  rw [show lam.re * s ^ (2 : ℕ) + n ^ (2 : ℕ) / lam.re * v ^ (2 : ℕ) =
      (lam.re ^ (2 : ℕ) * s ^ (2 : ℕ) + n ^ (2 : ℕ) * v ^ (2 : ℕ)) / lam.re by
    field_simp]
  apply (le_div_iff₀ ha).2
  nlinarith [sq_abs s, sq_abs v]

/-- Every mixed longitudinal/transverse polynomial feature product is absolutely summable. -/
theorem summable_xiShiftedApertureMixedPairTerm
    {y : ℝ} (hy : 0 < y) (p r : Polynomial ℝ) :
    Summable (xiShiftedApertureMixedPairTerm y p r) := by
  have hmajor := ((summable_xiShiftedApertureHilbertTerm hy p).add
    (summable_xiShiftedApertureTransverseTerm hy r)).mul_left ((2 : ℝ)⁻¹)
  apply Summable.of_norm_bounded hmajor
  intro q
  simpa [div_eq_inv_mul] using
    norm_xiShiftedApertureMixedPairTerm_le hy p r q

/-- Pointwise polarization of the shifted Hilbert channel. -/
theorem xiShiftedApertureHilbertPairTerm_eq_polarization
    (y : ℝ) (p r : Polynomial ℝ) (q : XiZeroCopy) :
    xiShiftedApertureHilbertPairTerm y p r q =
      (xiShiftedApertureHilbertTerm y (p + r) q -
        xiShiftedApertureHilbertTerm y (p - r) q) / 4 := by
  simp [xiShiftedApertureHilbertPairTerm,
    xiShiftedApertureHilbertTerm,
    xiShiftedApertureShearedEvaluation,
    HTGeometry.orientedComplexBilinearHilbertTerm,
    evalRealPolynomial]
  ring

/-- Pointwise polarization of the shifted transverse channel. -/
theorem xiShiftedApertureTransversePairTerm_eq_polarization
    (y : ℝ) (p r : Polynomial ℝ) (q : XiZeroCopy) :
    xiShiftedApertureTransversePairTerm y p r q =
      (xiShiftedApertureTransverseTerm y (p + r) q -
        xiShiftedApertureTransverseTerm y (p - r) q) / 4 := by
  simp [xiShiftedApertureTransversePairTerm,
    xiShiftedApertureTransverseTerm,
    HTGeometry.orientedComplexBilinearTransverseTerm,
    evalRealPolynomial]
  ring

/-- Every shifted longitudinal cross-channel is summable. -/
theorem summable_xiShiftedApertureHilbertPairTerm
    {y : ℝ} (hy : 0 < y) (p r : Polynomial ℝ) :
    Summable (xiShiftedApertureHilbertPairTerm y p r) := by
  have h := (summable_xiShiftedApertureHilbertTerm hy (p + r)).sub
    (summable_xiShiftedApertureHilbertTerm hy (p - r))
  have hquarter := h.mul_left ((4 : ℝ)⁻¹)
  exact hquarter.congr (fun q => by
    rw [xiShiftedApertureHilbertPairTerm_eq_polarization]
    ring)

/-- Every shifted transverse cross-channel is summable. -/
theorem summable_xiShiftedApertureTransversePairTerm
    {y : ℝ} (hy : 0 < y) (p r : Polynomial ℝ) :
    Summable (xiShiftedApertureTransversePairTerm y p r) := by
  have h := (summable_xiShiftedApertureTransverseTerm hy (p + r)).sub
    (summable_xiShiftedApertureTransverseTerm hy (p - r))
  have hquarter := h.mul_left ((4 : ℝ)⁻¹)
  exact hquarter.congr (fun q => by
    rw [xiShiftedApertureTransversePairTerm_eq_polarization]
    ring)

/-- Complete positive Hilbert energy at shift `y`. -/
def xiShiftedApertureHilbertEnergy (y : ℝ) (p : Polynomial ℝ) : ℝ :=
  ∑' q : XiZeroCopy, xiShiftedApertureHilbertTerm y p q

/-- Complete transverse charge at shift `y`. -/
def xiShiftedApertureTransverseEnergy (y : ℝ) (p : Polynomial ℝ) : ℝ :=
  ∑' q : XiZeroCopy, xiShiftedApertureTransverseTerm y p q

/-- Complete mixed longitudinal/transverse correlation of two polynomial probes. -/
def xiShiftedApertureMixedPairEnergy
    (y : ℝ) (p r : Polynomial ℝ) : ℝ :=
  ∑' q : XiZeroCopy, xiShiftedApertureMixedPairTerm y p r q

/-- **Channel orthogonality.** Every longitudinal real-polynomial feature is orthogonal to every
transverse real-polynomial feature at every positive shift. -/
theorem xiShiftedApertureMixedPairEnergy_eq_zero
    {y : ℝ} (hy : 0 < y) (p r : Polynomial ℝ) :
    xiShiftedApertureMixedPairEnergy y p r = 0 := by
  have _hs := summable_xiShiftedApertureMixedPairTerm hy p r
  have hEq : (∑' q : XiZeroCopy, xiShiftedApertureMixedPairTerm y p r q) =
      ∑' q : XiZeroCopy,
        xiShiftedApertureMixedPairTerm y p r (xiZeroCopyLineConjEquiv q) := by
    exact (xiZeroCopyLineConjEquiv.tsum_eq
      (xiShiftedApertureMixedPairTerm y p r)).symm
  simp_rw [xiShiftedApertureMixedPairTerm_lineConj] at hEq
  rw [tsum_neg] at hEq
  unfold xiShiftedApertureMixedPairEnergy
  linarith

/-- Longitudinal-minus-transverse shifted aperture gap. -/
def xiShiftedApertureEnergyGap (y : ℝ) (p : Polynomial ℝ) : ℝ :=
  xiShiftedApertureHilbertEnergy y p -
    xiShiftedApertureTransverseEnergy y p

/-- Polarized longitudinal cross-correlation of two polynomial probes. -/
def xiShiftedApertureHilbertPairEnergy
    (y : ℝ) (p r : Polynomial ℝ) : ℝ :=
  (xiShiftedApertureHilbertEnergy y (p + r) -
    xiShiftedApertureHilbertEnergy y (p - r)) / 4

/-- Polarized transverse cross-correlation of two polynomial probes. -/
def xiShiftedApertureTransversePairEnergy
    (y : ℝ) (p r : Polynomial ℝ) : ℝ :=
  (xiShiftedApertureTransverseEnergy y (p + r) -
    xiShiftedApertureTransverseEnergy y (p - r)) / 4

/-- Polarized longitudinal-minus-transverse cross-correlation. -/
def xiShiftedAperturePairGap
    (y : ℝ) (p r : Polynomial ℝ) : ℝ :=
  xiShiftedApertureHilbertPairEnergy y p r -
    xiShiftedApertureTransversePairEnergy y p r

/-- Archimedean source channel paired against two polynomial probes on the Euler ray. -/
def xiShiftedApertureArchimedeanSourcePair
    (w : ℝ) (p r : Polynomial ℝ) : ℝ :=
  HTGeometry.momentInner
    (fun k => normalizedArchimedeanSourceMoment k w) p r

/-- Cancellation-preserving Chebyshev-discrepancy source channel paired against two polynomial
probes on the Euler ray. -/
def xiShiftedApertureDiscrepancySourcePair
    (w : ℝ) (p r : Polynomial ℝ) : ℝ :=
  HTGeometry.momentInner
    (fun k => normalizedChebyshevDiscrepancyMoment k w) p r

/-- Complete marked-`X` Lorentz transport: positive longitudinal transport minus the surviving
phase-weighted shear and positive transverse transport. -/
def xiShiftedApertureLorentzCrossingEnergy
    (y : ℝ) (p : Polynomial ℝ) : ℝ :=
  ∑' q : XiZeroCopy,
    (xiShiftedApertureLorentzLongitudinalTerm y p q -
      xiShiftedApertureLorentzShearTerm y p q -
        xiShiftedApertureLorentzTransverseTerm y p q)

/-- Polarized Hilbert energy is the sum of the actual atomwise longitudinal cross-channel. -/
theorem xiShiftedApertureHilbertPairEnergy_eq_tsum
    {y : ℝ} (hy : 0 < y) (p r : Polynomial ℝ) :
    xiShiftedApertureHilbertPairEnergy y p r =
      ∑' q : XiZeroCopy, xiShiftedApertureHilbertPairTerm y p r q := by
  simp only [xiShiftedApertureHilbertPairEnergy,
    xiShiftedApertureHilbertEnergy]
  rw [← (summable_xiShiftedApertureHilbertTerm hy (p + r)).tsum_sub
      (summable_xiShiftedApertureHilbertTerm hy (p - r)),
    div_eq_inv_mul, ← tsum_mul_left]
  apply tsum_congr
  intro q
  rw [xiShiftedApertureHilbertPairTerm_eq_polarization, div_eq_inv_mul]

/-- Polarized transverse energy is the sum of the actual atomwise transverse cross-channel. -/
theorem xiShiftedApertureTransversePairEnergy_eq_tsum
    {y : ℝ} (hy : 0 < y) (p r : Polynomial ℝ) :
    xiShiftedApertureTransversePairEnergy y p r =
      ∑' q : XiZeroCopy, xiShiftedApertureTransversePairTerm y p r q := by
  simp only [xiShiftedApertureTransversePairEnergy,
    xiShiftedApertureTransverseEnergy]
  rw [← (summable_xiShiftedApertureTransverseTerm hy (p + r)).tsum_sub
      (summable_xiShiftedApertureTransverseTerm hy (p - r)),
    div_eq_inv_mul, ← tsum_mul_left]
  apply tsum_congr
  intro q
  rw [xiShiftedApertureTransversePairTerm_eq_polarization, div_eq_inv_mul]

/-- The global pair gap is the sum of the actual polarized trace-Hankel atoms. -/
theorem xiShiftedAperturePairGap_eq_tsum_hankelPairTerm
    {y : ℝ} (hy : 0 < y) (p r : Polynomial ℝ) :
    xiShiftedAperturePairGap y p r =
      ∑' q : XiZeroCopy, xiShiftedApertureHankelPairTerm y p r q := by
  rw [xiShiftedAperturePairGap,
    xiShiftedApertureHilbertPairEnergy_eq_tsum hy,
    xiShiftedApertureTransversePairEnergy_eq_tsum hy,
    ← (summable_xiShiftedApertureHilbertPairTerm hy p r).tsum_sub
      (summable_xiShiftedApertureTransversePairTerm hy p r)]
  apply tsum_congr
  intro q
  exact (xiShiftedApertureHankelPairTerm_eq_hilbert_sub_transverse hy p r q).symm

/-- **Global Lorentz transport law.**  The marked multiplication crossing is exactly the complete
longitudinal-minus-shear-minus-transverse transport. -/
theorem xiShiftedAperturePairGap_X_mul_eq_lorentzCrossingEnergy
    {y : ℝ} (hy : 0 < y) (p : Polynomial ℝ) :
    xiShiftedAperturePairGap y p (X * p) =
      xiShiftedApertureLorentzCrossingEnergy y p := by
  rw [xiShiftedAperturePairGap_eq_tsum_hankelPairTerm hy,
    xiShiftedApertureLorentzCrossingEnergy]
  apply tsum_congr
  intro q
  exact xiShiftedApertureHankelPairTerm_X_mul_eq_lorentzTransport hy p q

/-- Global shifted Hilbert-minus-charge decomposition. -/
theorem xiShiftedApertureEnergyGap_eq_traceHankel_re
    {y : ℝ} (hy : 0 < y) (p : Polynomial ℝ) :
    xiShiftedApertureEnergyGap y p =
      (xiShiftedReciprocalTraceHankel y p).re := by
  rw [xiShiftedApertureEnergyGap,
    xiShiftedApertureHilbertEnergy,
    xiShiftedApertureTransverseEnergy,
    ← (summable_xiShiftedApertureHilbertTerm hy p).tsum_sub
      (summable_xiShiftedApertureTransverseTerm hy p),
    xiShiftedReciprocalTraceHankel,
    Complex.re_tsum (summable_xiShiftedReciprocalTraceHankelTerm hy.le p)]
  apply tsum_congr
  intro q
  exact (xiShiftedApertureHankelTerm_eq_hilbert_sub_transverse hy p q).symm

/-- The channel gap on a coefficient polynomial is exactly its shifted Hankel quadratic. -/
theorem xiShiftedApertureEnergyGap_ofFn_eq_hankelQuadratic
    {y : ℝ} (hy : 0 < y) (n : ℕ) (c : Fin n → ℝ) :
    xiShiftedApertureEnergyGap y (Polynomial.ofFn n c) =
      xiShiftedMomentHankelQuadratic y n c := by
  rw [xiShiftedApertureEnergyGap_eq_traceHankel_re hy,
    ← one_mul (Polynomial.ofFn n c),
    ← pow_zero (Polynomial.X : Polynomial ℝ),
    xiShiftedReciprocalTraceHankel_X_pow_mul_ofFn hy.le 0 n c,
    xiShiftedMomentHankelQuadratic_eq]
  simp only [zero_mul, zero_add, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Nat.mul_zero, xiShiftedReciprocalHankelQuadratic]

/-- At every positive shift, the complete energy gap is exactly the shifted moment form on every
real polynomial, independently of a coordinate cutoff. -/
theorem xiShiftedApertureEnergyGap_eq_momentInner
    {y : ℝ} (hy : 0 < y) (p : Polynomial ℝ) :
    xiShiftedApertureEnergyGap y p =
      HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment y k).re) p p := by
  let n := p.natDegree + 1
  let c : Fin n → ℝ := Polynomial.toFn n p
  have hp : Polynomial.ofFn n c = p := by
    exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_self _)
  rw [← hp, xiShiftedApertureEnergyGap_ofFn_eq_hankelQuadratic hy]
  exact (HTGeometry.momentInner_ofFn_ofFn
    (fun k => (xiShiftedReciprocalMoment y k).re) n c c).symm

/-- **Global polarized channel law.** The longitudinal-minus-transverse cross-correlation of two
polynomial probes is exactly their shifted Xi moment pairing. -/
theorem xiShiftedAperturePairGap_eq_momentInner
    {y : ℝ} (hy : 0 < y) (p r : Polynomial ℝ) :
    xiShiftedAperturePairGap y p r =
      HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment y k).re) p r := by
  rw [xiShiftedAperturePairGap,
    xiShiftedApertureHilbertPairEnergy,
    xiShiftedApertureTransversePairEnergy]
  have hplus := xiShiftedApertureEnergyGap_eq_momentInner hy (p + r)
  have hminus := xiShiftedApertureEnergyGap_eq_momentInner hy (p - r)
  rw [xiShiftedApertureEnergyGap] at hplus hminus
  rw [← HTGeometry.momentInner_polarization
    (fun k => (xiShiftedReciprocalMoment y k).re) p r]
  linarith

/-- **Joint source realization of every polarized shifted-Xi pairing.**  On the Euler ray, the
longitudinal-minus-transverse pair gap is the sum of the fixed archimedean and
Chebyshev-discrepancy source pairings.  This is a pairing-level strengthening of the terminal
source-jet split: it retains every probe in the polynomial flag. -/
theorem xiShiftedAperturePairGap_eq_archimedeanSourcePair_add_discrepancySourcePair
    {w : ℝ} (hw : 1 / 2 < w) (p r : Polynomial ℝ) :
    xiShiftedAperturePairGap (w ^ (2 : ℕ)) p r =
      xiShiftedApertureArchimedeanSourcePair w p r +
        xiShiftedApertureDiscrepancySourcePair w p r := by
  rw [xiShiftedAperturePairGap_eq_momentInner
    (sq_pos_of_pos (by linarith : 0 < w))]
  have hseq : ∀ k : ℕ,
      (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re =
        normalizedArchimedeanSourceMoment k w +
          normalizedChebyshevDiscrepancyMoment k w := by
    intro k
    rw [← normalizedCompletedSourceMoment_eq k (by linarith : 0 < w)]
    exact normalizedCompletedSourceMoment_eq_archimedean_add_discrepancy k hw
  simp only [xiShiftedApertureArchimedeanSourcePair,
    xiShiftedApertureDiscrepancySourcePair, HTGeometry.momentInner_def,
    HTGeometry.momentFunctional_eq_support_sum]
  simp_rw [hseq]
  simp only [mul_add, Finset.sum_add_distrib]

/-- **First-extension source law.**  Multiplication by `X` leaves the null flag and turns the same
two source channels into the exact marked Lorentz crossing. -/
theorem xiShiftedApertureLorentzCrossingEnergy_eq_archimedeanSourcePair_add_discrepancySourcePair
    {w : ℝ} (hw : 1 / 2 < w) (p : Polynomial ℝ) :
    xiShiftedApertureLorentzCrossingEnergy (w ^ (2 : ℕ)) p =
      xiShiftedApertureArchimedeanSourcePair w p (X * p) +
        xiShiftedApertureDiscrepancySourcePair w p (X * p) := by
  rw [← xiShiftedAperturePairGap_X_mul_eq_lorentzCrossingEnergy
    (sq_pos_of_pos (by linarith : 0 < w))]
  exact xiShiftedAperturePairGap_eq_archimedeanSourcePair_add_discrepancySourcePair hw p (X * p)

/-- The polarized channel gap retains the marked sign of its second probe.  In particular, an
unmarked rank-one covariance target cannot determine Krein-crossing orientation. -/
theorem xiShiftedAperturePairGap_neg_right
    {y : ℝ} (hy : 0 < y) (p r : Polynomial ℝ) :
    xiShiftedAperturePairGap y p (-r) =
      -xiShiftedAperturePairGap y p r := by
  rw [xiShiftedAperturePairGap_eq_momentInner hy,
    xiShiftedAperturePairGap_eq_momentInner hy]
  rw [show -r = (-1 : ℝ) • r by simp, HTGeometry.momentInner_smul_right]
  ring

/-- **Zero-free source realization.** In the convergent negative-binomial window, every polarized
longitudinal-minus-transverse Xi correlation is exactly the prime--Gamma source moment pairing. -/
theorem xiShiftedAperturePairGap_eq_primeArchMomentInner
    {y : ℝ} (hy : 0 < y) (hymax : y < 41 / 2)
    (p r : Polynomial ℝ) :
    xiShiftedAperturePairGap y p r =
      HTGeometry.momentInner
        (fun k => (primeArchShiftedReciprocalMoment y k).re) p r := by
  rw [xiShiftedAperturePairGap_eq_momentInner hy]
  congr 1
  funext k
  exact congrArg Complex.re
    (xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment hy.le hymax k)

/-- In the zero-free convergence window, marked Lorentz transport is itself an exact prime--Gamma
source pairing.  This is the phase-retaining source intertwiner absent from unmarked covariance
models. -/
theorem xiShiftedApertureLorentzCrossingEnergy_eq_primeArchMomentInner
    {y : ℝ} (hy : 0 < y) (hymax : y < 41 / 2) (p : Polynomial ℝ) :
    xiShiftedApertureLorentzCrossingEnergy y p =
      HTGeometry.momentInner
        (fun k => (primeArchShiftedReciprocalMoment y k).re) p (X * p) := by
  rw [← xiShiftedAperturePairGap_X_mul_eq_lorentzCrossingEnergy hy,
    xiShiftedAperturePairGap_eq_primeArchMomentInner hy hymax]

/-- A shifted Hankel null polynomial has zero channel gap against every probe in the completed
finite polynomial flag. -/
theorem xiShiftedHankelNull_aperturePairGap_eq_zero_of_natDegree_lt
    {y : ℝ} (hy : 0 < y) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    {r : Polynomial ℝ} (hr : r.natDegree < n + 1) :
    xiShiftedAperturePairGap y
      (HTGeometry.finiteHankelNullMonicPolynomial c) r = 0 := by
  rw [xiShiftedAperturePairGap_eq_momentInner hy]
  have hmat : GaloisForLFunctions.HTGeometry.finiteHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1) =
      HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1) := rfl
  have hc' : HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1) *ᵥ c = 0 := by
    rw [← hmat]
    exact hc
  exact HTGeometry.momentInner_finiteHankelNullMonicPolynomial_eq_zero_of_kernel hc' hr

/-- **Source-conditioned null-flag cancellation.**  At a singular shifted-Xi face, the
archimedean and cancellation-preserving Chebyshev-discrepancy source pairings are exact negatives
against every probe in the completed finite flag.  Hence none of the visible flag coordinates can
orient the face; the first transverse extension is the only remaining source coordinate. -/
theorem xiShiftedHankelNull_archimedeanSourcePair_eq_neg_discrepancySourcePair_of_natDegree_lt
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 1) *ᵥ c = 0)
    {r : Polynomial ℝ} (hr : r.natDegree < n + 1) :
    xiShiftedApertureArchimedeanSourcePair w
        (HTGeometry.finiteHankelNullMonicPolynomial c) r =
      -xiShiftedApertureDiscrepancySourcePair w
        (HTGeometry.finiteHankelNullMonicPolynomial c) r := by
  have hgap := xiShiftedHankelNull_aperturePairGap_eq_zero_of_natDegree_lt
    (sq_pos_of_pos (by linarith : 0 < w)) c hc hr
  rw [xiShiftedAperturePairGap_eq_archimedeanSourcePair_add_discrepancySourcePair
    hw] at hgap
  linarith

/-- **Null-flag channel isometry.** Along the whole finite flag below a singular face,
longitudinal and transverse correlations with the null polynomial agree exactly. -/
theorem xiShiftedHankelNull_hilbertPairEnergy_eq_transversePairEnergy_of_natDegree_lt
    {y : ℝ} (hy : 0 < y) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    {r : Polynomial ℝ} (hr : r.natDegree < n + 1) :
    xiShiftedApertureHilbertPairEnergy y
        (HTGeometry.finiteHankelNullMonicPolynomial c) r =
      xiShiftedApertureTransversePairEnergy y
        (HTGeometry.finiteHankelNullMonicPolynomial c) r := by
  have hgap :=
    xiShiftedHankelNull_aperturePairGap_eq_zero_of_natDegree_lt hy c hc hr
  rw [xiShiftedAperturePairGap] at hgap
  linarith

/-- **Null-face cross-channel law.** On a singular face, the intrinsic Krein orientation is exactly
longitudinal cross-correlation minus transverse cross-correlation between the monic null polynomial
and its multiplication-by-`X` image. -/
theorem xiShiftedHankelBoundaryNullCrossingForm_eq_aperturePairGap
    {y : ℝ} (hy : 0 < y) {n : ℕ} (c : Fin (n + 1) → ℝ) :
    xiShiftedHankelBoundaryNullCrossingForm y c =
      xiShiftedAperturePairGap y
        (HTGeometry.finiteHankelNullMonicPolynomial c)
        (X * HTGeometry.finiteHankelNullMonicPolynomial c) := by
  rw [xiShiftedAperturePairGap_eq_momentInner hy]
  rfl

/-- **Null-face Lorentz crossing law.**  At completed Hankel incidence, the exact remaining
orientation is the net Lorentz transport of the canonical monic null polynomial.  Ordinary mixed
channel orthogonality does not erase its phase-weighted shear term. -/
theorem xiShiftedHankelBoundaryNullCrossingForm_eq_lorentzCrossingEnergy
    {y : ℝ} (hy : 0 < y) {n : ℕ} (c : Fin (n + 1) → ℝ) :
    xiShiftedHankelBoundaryNullCrossingForm y c =
      xiShiftedApertureLorentzCrossingEnergy y
        (HTGeometry.finiteHankelNullMonicPolynomial c) := by
  rw [xiShiftedHankelBoundaryNullCrossingForm_eq_aperturePairGap hy,
    xiShiftedAperturePairGap_X_mul_eq_lorentzCrossingEnergy hy]

/-- **Completed-source/Lorentz incidence law.**  On a singular face, terminal orientation times
the net Lorentz transport is exactly the normalized completed prime--Gamma boundary jet. -/
theorem xiShiftedHankel_terminal_mul_lorentzCrossingEnergy_eq_sourceJet
    {w : ℝ} (hw : 0 < w) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    c (Fin.last n) *
        xiShiftedApertureLorentzCrossingEnergy (w ^ (2 : ℕ))
          (HTGeometry.finiteHankelNullMonicPolynomial c) =
      xiShiftedHankelBoundarySourceJet w (n + 1) c := by
  rw [← xiShiftedHankelBoundaryNullCrossingForm_eq_lorentzCrossingEnergy
    (sq_pos_of_pos hw) c,
    xiShiftedHankelBoundaryNullCrossingForm_eq_inv_mul_sourceJet hw c hc hlast]
  field_simp

/-- **Completed-source joint-incidence law.**  Terminal orientation times the first source
extension beyond the cancelling null flag is exactly the completed boundary source jet.  The two
source channels are therefore not independent marginals: their marked transverse sum is the
intrinsic face coordinate. -/
theorem xiShiftedHankel_terminal_mul_sourcePairExtension_eq_sourceJet
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    c (Fin.last n) *
        (xiShiftedApertureArchimedeanSourcePair w
            (HTGeometry.finiteHankelNullMonicPolynomial c)
            (X * HTGeometry.finiteHankelNullMonicPolynomial c) +
          xiShiftedApertureDiscrepancySourcePair w
            (HTGeometry.finiteHankelNullMonicPolynomial c)
            (X * HTGeometry.finiteHankelNullMonicPolynomial c)) =
      xiShiftedHankelBoundarySourceJet w (n + 1) c := by
  rw [← xiShiftedApertureLorentzCrossingEnergy_eq_archimedeanSourcePair_add_discrepancySourcePair
    hw]
  exact xiShiftedHankel_terminal_mul_lorentzCrossingEnergy_eq_sourceJet
    (by linarith : 0 < w) c hc hlast

/-- In the source convergence window, the Krein crossing itself is the prime--Gamma
longitudinal-minus-transverse cross-correlation of the null polynomial with its `X`-image. -/
theorem xiShiftedHankelBoundaryNullCrossingForm_eq_primeArchMomentInner
    {y : ℝ} (hy : 0 < y) (hymax : y < 41 / 2)
    {n : ℕ} (c : Fin (n + 1) → ℝ) :
    xiShiftedHankelBoundaryNullCrossingForm y c =
      HTGeometry.momentInner
        (fun k => (primeArchShiftedReciprocalMoment y k).re)
        (HTGeometry.finiteHankelNullMonicPolynomial c)
        (X * HTGeometry.finiteHankelNullMonicPolynomial c) := by
  rw [xiShiftedHankelBoundaryNullCrossingForm_eq_aperturePairGap hy,
    xiShiftedAperturePairGap_eq_primeArchMomentInner hy hymax]

/-- **Null-face saturation.** On a singular shifted Xi Hankel face, the positive Hilbert energy
and transverse charge of its raw null polynomial are exactly equal. -/
theorem xiShiftedHankelNull_hilbertEnergy_eq_transverseEnergy
    {y : ℝ} (hy : 0 < y) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0) :
    xiShiftedApertureHilbertEnergy y (Polynomial.ofFn (n + 1) c) =
      xiShiftedApertureTransverseEnergy y (Polynomial.ofFn (n + 1) c) := by
  have hq : xiShiftedMomentHankelQuadratic y (n + 1) c = 0 := by
    rw [xiShiftedMomentHankelQuadratic]
    rw [hc]
    simp
  have hgap := xiShiftedApertureEnergyGap_ofFn_eq_hankelQuadratic hy (n + 1) c
  rw [xiShiftedApertureEnergyGap, hq] at hgap
  linarith

/-- **Null-face channel isotropy.** At a singular face the raw null polynomial has equal
longitudinal and transverse squared norms, while their mixed covariance vanishes. -/
theorem xiShiftedHankelNull_channelIsotropy
    {y : ℝ} (hy : 0 < y) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0) :
    xiShiftedApertureHilbertEnergy y (Polynomial.ofFn (n + 1) c) =
        xiShiftedApertureTransverseEnergy y (Polynomial.ofFn (n + 1) c) ∧
      xiShiftedApertureMixedPairEnergy y
        (Polynomial.ofFn (n + 1) c) (Polynomial.ofFn (n + 1) c) = 0 := by
  exact ⟨xiShiftedHankelNull_hilbertEnergy_eq_transverseEnergy hy c hc,
    xiShiftedApertureMixedPairEnergy_eq_zero hy _ _⟩

/-- **Saturated-channel boundary flow.** The derivative of the longitudinal-minus-transverse
equality gap at a singular face is exactly the terminal/first-omitted crossing flux. -/
theorem hasDerivAt_xiShiftedApertureEnergyGap_ofFn_of_kernel
    {y : ℝ} (hy : 0 < y) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0) :
    HasDerivAt
      (fun t => xiShiftedApertureEnergyGap t (Polynomial.ofFn (n + 1) c))
      (-(2 * (n : ℝ) + 1) * c (Fin.last n) *
        xiShiftedHankelFirstOmittedCoupling y (n + 1) c) y := by
  have hbase :=
    hasDerivAt_xiShiftedMomentHankelQuadratic_of_kernel_succ hy n c hc
  apply hbase.congr_of_eventuallyEq
  filter_upwards [tendsto_id.eventually_const_lt hy] with t ht
  simpa using xiShiftedApertureEnergyGap_ofFn_eq_hankelQuadratic ht (n + 1) c

/-- **Completed-source saturation flow.** On the whole positive Euler ray, the derivative of the
null channel gap is the terminal coefficient paired with the exact completed prime--Gamma jet. -/
theorem hasDerivAt_xiShiftedApertureEnergyGap_ofFn_eq_sourceJet
    {w : ℝ} (hw : 0 < w) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hc : xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 1) *ᵥ c = 0) :
    HasDerivAt
      (fun t => xiShiftedApertureEnergyGap t (Polynomial.ofFn (n + 1) c))
      (-(2 * (n : ℝ) + 1) * c (Fin.last n) *
        xiShiftedHankelBoundarySourceJet w (n + 1) c) (w ^ (2 : ℕ)) := by
  have hd := hasDerivAt_xiShiftedApertureEnergyGap_ofFn_of_kernel
    (sq_pos_of_pos hw) n c hc
  rw [xiShiftedHankelBoundarySourceJet_eq hw]
  exact hd

/-- In canonical projective coordinates, the saturated-channel derivative is a negative positive
factor times the intrinsic Krein crossing class. -/
theorem hasDerivAt_xiShiftedApertureEnergyGap_ofFn_eq_kreinCrossing
    {y : ℝ} (hy : 0 < y) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    HasDerivAt
      (fun t => xiShiftedApertureEnergyGap t (Polynomial.ofFn (n + 1) c))
      (-(2 * (n : ℝ) + 1) * c (Fin.last n) ^ (2 : ℕ) *
        xiShiftedHankelBoundaryNullCrossingForm y c) y := by
  have hd := hasDerivAt_xiShiftedApertureEnergyGap_ofFn_of_kernel hy n c hc
  apply hd.congr_deriv
  rw [xiShiftedHankelBoundaryNullCrossingForm_eq_monicRemainder c hc hlast]
  have hflux :=
    xiShiftedHankel_terminal_mul_coupling_eq_sq_mul_monicRemainder y c hlast
  nlinarith

/-- At a right-hand first crossing, the saturated Hilbert-minus-transverse gap can only have
nonnegative outgoing derivative; equivalently its canonical Krein crossing is nonpositive. -/
theorem xiShiftedHankelFirstCrossing_energyGap_deriv_nonneg
    {y : ℝ} (hy : 0 < y) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hcne : c ≠ 0)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hmin : IsLocalMinOn
      (fun t => xiShiftedMomentHankelQuadratic t (n + 1) c) (Ici y) y) :
    0 ≤ -(2 * (n : ℝ) + 1) * c (Fin.last n) ^ (2 : ℕ) *
      xiShiftedHankelBoundaryNullCrossingForm y c := by
  have hcross := xiShiftedHankelFirstCrossing_nullCrossingForm_nonpos
    hy n c hhead hcne hc hmin
  have hfactor : 0 < (2 * (n : ℝ) + 1) * c (Fin.last n) ^ (2 : ℕ) := by
    have hlast := xiShiftedHankelNullVector_terminal_ne_zero_of_head_posDef
      y n c hhead hcne hc
    positivity
  nlinarith

/-- Strict decay of the saturated channel gap is exactly strict positive Krein crossing type. -/
theorem xiShiftedHankelNull_energyGapSlope_neg_iff_nullCrossingForm_pos
    {y : ℝ} {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) :
    -(2 * (n : ℝ) + 1) * c (Fin.last n) ^ (2 : ℕ) *
          xiShiftedHankelBoundaryNullCrossingForm y c < 0 ↔
      0 < xiShiftedHankelBoundaryNullCrossingForm y c := by
  have hfactor : 0 < (2 * (n : ℝ) + 1) * c (Fin.last n) ^ (2 : ℕ) := by
    positivity
  constructor <;> intro h <;> nlinarith

/-- **Exact zero-free source obligation.** In the negative-binomial window, strict decay of the
saturated channel gap is equivalent to strict positivity of one prime--Gamma source pairing. -/
theorem xiShiftedHankelNull_energyGapSlope_neg_iff_primeArchPair_pos
    {y : ℝ} (hy : 0 < y) (hymax : y < 41 / 2)
    {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) :
    -(2 * (n : ℝ) + 1) * c (Fin.last n) ^ (2 : ℕ) *
          xiShiftedHankelBoundaryNullCrossingForm y c < 0 ↔
      0 < HTGeometry.momentInner
        (fun k => (primeArchShiftedReciprocalMoment y k).re)
        (HTGeometry.finiteHankelNullMonicPolynomial c)
        (X * HTGeometry.finiteHankelNullMonicPolynomial c) := by
  rw [xiShiftedHankelNull_energyGapSlope_neg_iff_nullCrossingForm_pos c hlast,
    xiShiftedHankelBoundaryNullCrossingForm_eq_primeArchMomentInner hy hymax]

/-- On the whole Euler ray, strict decay of the completed-source channel-flow coefficient is
exactly projective archimedean dominance over the oriented prime discrepancy. -/
theorem xiShiftedHankelNull_sourceSlope_neg_iff_projectiveSourceDominance
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (c : Fin (n + 1) → ℝ) :
    -(2 * (n : ℝ) + 1) * c (Fin.last n) *
          xiShiftedHankelBoundarySourceJet w (n + 1) c < 0 ↔
      -(c (Fin.last n) *
          xiShiftedHankelBoundaryDiscrepancyJet w (n + 1) c) <
        c (Fin.last n) *
          xiShiftedHankelBoundaryArchimedeanJet w (n + 1) c := by
  rw [xiShiftedHankelBoundarySourceJet_eq_archimedean_add_discrepancy hw]
  have hfactor : 0 < 2 * (n : ℝ) + 1 := by positivity
  constructor <;> intro h <;> nlinarith

/-- **Exact first-crossing consumer.** Any proof of strict decay of the saturated
Hilbert-minus-transverse equality excludes a right-hand first crossing. -/
theorem not_xiShiftedHankelFirstCrossing_of_energyGapSlope_neg
    {y : ℝ} (hy : 0 < y) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hcne : c ≠ 0)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hdecay :
      -(2 * (n : ℝ) + 1) * c (Fin.last n) ^ (2 : ℕ) *
        xiShiftedHankelBoundaryNullCrossingForm y c < 0) :
    ¬ IsLocalMinOn
      (fun t => xiShiftedMomentHankelQuadratic t (n + 1) c) (Ici y) y := by
  intro hmin
  have hnonneg := xiShiftedHankelFirstCrossing_energyGap_deriv_nonneg
    hy n c hhead hcne hc hmin
  linarith

/-- A strict positive zero-free prime--Gamma source pairing on the null line excludes the
corresponding right-hand first crossing. -/
theorem not_xiShiftedHankelFirstCrossing_of_primeArchPair_pos
    {y : ℝ} (hy : 0 < y) (hymax : y < 41 / 2)
    (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hcne : c ≠ 0)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hsource : 0 < HTGeometry.momentInner
      (fun k => (primeArchShiftedReciprocalMoment y k).re)
      (HTGeometry.finiteHankelNullMonicPolynomial c)
      (X * HTGeometry.finiteHankelNullMonicPolynomial c)) :
    ¬ IsLocalMinOn
      (fun t => xiShiftedMomentHankelQuadratic t (n + 1) c) (Ici y) y := by
  have hlast := xiShiftedHankelNullVector_terminal_ne_zero_of_head_posDef
    y n c hhead hcne hc
  have hdecay :=
    (xiShiftedHankelNull_energyGapSlope_neg_iff_primeArchPair_pos
      hy hymax c hlast).2 hsource
  exact not_xiShiftedHankelFirstCrossing_of_energyGapSlope_neg
    hy n c hhead hcne hc hdecay

end

end RHTower
