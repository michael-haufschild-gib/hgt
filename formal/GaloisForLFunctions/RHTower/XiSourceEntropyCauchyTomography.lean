import GaloisForLFunctions.RHTower.XiSourceEntropySeparatedSourceReconstruction
import GaloisForLFunctions.RHTower.XiReciprocalSquareFixedCauchySource
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap
import GaloisForLFunctions.HTGeometry.ReflectionBoostPolarizationLaw

/-!
# Cauchy tomography of the conserved Xi source-orientation measure

The squared reciprocal-square orientation coordinate defines one canonical positive atomic
mass on the multiplicity-exact Xi divisor.  Its total mass is the conserved source-entropy
energy, while the Xi--Weil quadratic form reads its negative.

Every regular off-axis continued-Cauchy probe reads the same mass through an explicit strictly
positive weight.  Thus the global source energy, the negative Weil direction, the quartet
variance, and the one-pole orientation defect are not separate criteria: they are different
tomograms of one conserved source-orientation object.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Atomic mass of the canonical Xi source-orientation measure. -/
def xiSourceEntropyOrientationMassAtom (q : XiZeroCopy) : ℝ :=
  (xiZeroCopyReciprocalSquare q).im ^ (2 : ℕ)

/-- Total mass of the canonical Xi source-orientation measure. -/
def xiSourceEntropyOrientationMeasureMass : ℝ :=
  ∑' q : XiZeroCopy, xiSourceEntropyOrientationMassAtom q

/-- Local metric curvature of the balanced reciprocal double attached to one Xi spectral point.
The unit diagonal form is the positive cup--Hodge normalization. -/
def xiSourceEntropyPolarizationCurvatureAtom (q : XiZeroCopy) : ℝ :=
  GaloisForLFunctions.HTGeometry.balancedReflectionBoostEnergyAcceleration 1
    (GaloisForLFunctions.HTGeometry.reciprocalSquareTangentialAmplitude
      (xiSpectralPoint q))
    (GaloisForLFunctions.HTGeometry.reflectionTransverseRate
      (xiSpectralPoint q)) 0

/-- Total curvature of the balanced reciprocal Xi polarization. -/
def xiSourceEntropyPolarizationCurvatureMass : ℝ :=
  ∑' q : XiZeroCopy, xiSourceEntropyPolarizationCurvatureAtom q

/-- Tangentially weighted Fisher information of the reflected Xi character at one zero copy. -/
def xiSourceEntropyReflectionFisherAtom (q : XiZeroCopy) : ℝ :=
  GaloisForLFunctions.HTGeometry.reciprocalSquareTangentialAmplitude
      (xiSpectralPoint q) ^ (2 : ℕ) *
    GaloisForLFunctions.HTGeometry.reflectedBernoulliFisherAtZero
      (GaloisForLFunctions.HTGeometry.reflectionTransverseRate
        (xiSpectralPoint q))

/-- Total weighted Fisher information of the reflected Xi source character. -/
def xiSourceEntropyReflectionFisherMass : ℝ :=
  ∑' q : XiZeroCopy, xiSourceEntropyReflectionFisherAtom q

/-- The reciprocal-character rate in the rotated spectral plane is exactly the horizontal
reflected source entropy.  In particular, the Fisher family above is the arithmetic source
character, not an auxiliary height deformation. -/
theorem reflectionTransverseRate_xiSpectralPoint_eq_sourceEntropy
    (q : XiZeroCopy) :
    GaloisForLFunctions.HTGeometry.reflectionTransverseRate
        (xiSpectralPoint q) =
      riemannReflectedSourceEntropy (q.1 : ℂ) := by
  rw [riemannReflectedSourceEntropy_eq_neg_sourceCayleyRate]
  simp only [GaloisForLFunctions.HTGeometry.reflectionTransverseRate,
    GaloisForLFunctions.HTGeometry.sourceCayleyTransverseRate,
    xiSpectralPoint, mul_im, sub_re, sub_im, one_re,
    neg_re, neg_im, I_re, I_im]
  norm_num
  ring

/-- **Xi orientation-curvature law.**  The source-orientation atom is exactly one eighth of
the positive metric curvature of its minimal balanced reciprocal double. -/
theorem xiSourceEntropyPolarizationCurvatureAtom_eq_eight_mul_orientationMassAtom
    (q : XiZeroCopy) :
    xiSourceEntropyPolarizationCurvatureAtom q =
      8 * xiSourceEntropyOrientationMassAtom q := by
  simpa only [xiSourceEntropyPolarizationCurvatureAtom,
    xiSourceEntropyOrientationMassAtom, xiZeroCopyReciprocalSquare,
    one_mul, mul_one] using
      GaloisForLFunctions.HTGeometry.reciprocalSquareOrientation_eq_boostEnergyCurvature
        1 (xiSpectralPoint q)

/-- **Xi orientation--Fisher law.**  Every source-orientation atom is exactly the weighted Fisher
information of its balanced reflected character. -/
theorem xiSourceEntropyReflectionFisherAtom_eq_orientationMassAtom
    (q : XiZeroCopy) :
    xiSourceEntropyReflectionFisherAtom q =
      xiSourceEntropyOrientationMassAtom q := by
  symm
  simpa only [xiSourceEntropyReflectionFisherAtom,
    xiSourceEntropyOrientationMassAtom, xiZeroCopyReciprocalSquare] using
      GaloisForLFunctions.HTGeometry.reciprocalSquareOrientation_sq_eq_tangentialFisher
        (xiSpectralPoint q)

/-- **Local Xi reflection-information identity.**  At every multiplicity copy, the negative
conservative cross square, weighted Fisher information of the actual source character, positive
reciprocal-polarization curvature, and squared divisor orientation are one atom. -/
theorem xiSourceEntropyLocalReflectionInformationIdentity
    (q : XiZeroCopy) :
    -(GaloisForLFunctions.HTGeometry.binaryReflectionForm 0 1
        (GaloisForLFunctions.HTGeometry.balancedReflectionScore
          (GaloisForLFunctions.HTGeometry.reciprocalSquareTangentialAmplitude
            (xiSpectralPoint q))
          (GaloisForLFunctions.HTGeometry.reflectionTransverseRate
            (xiSpectralPoint q)))) / 2 =
        xiSourceEntropyOrientationMassAtom q ∧
      xiSourceEntropyOrientationMassAtom q =
        xiSourceEntropyPolarizationCurvatureAtom q / 8 := by
  simpa only [xiSourceEntropyOrientationMassAtom,
    xiSourceEntropyPolarizationCurvatureAtom, xiZeroCopyReciprocalSquare] using
      GaloisForLFunctions.HTGeometry.reciprocalSquareReflectionInformationIdentity
        (xiSpectralPoint q)

/--
**Off-line positive-conservative exclusion.**  At an Xi divisor copy away from the critical
line, every positive semidefinite, reflection-symmetric quadratic form conserved by the actual
reciprocal source character is zero.  Thus an off-line reflected pair can retain its signed
first-order source charge only in an indefinite form, or in a positive realization which changes
order or topology.
-/
theorem xiSourceEntropy_no_nonzero_positive_conservative_reflectionForm
    (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {α β : ℝ}
    (hinv : ∀ t v,
      GaloisForLFunctions.HTGeometry.binaryReflectionForm α β
          (GaloisForLFunctions.HTGeometry.reflectionBoost
            (GaloisForLFunctions.HTGeometry.reflectionTransverseRate
              (xiSpectralPoint q)) t v) =
        GaloisForLFunctions.HTGeometry.binaryReflectionForm α β v)
    (hpos : ∀ v,
      0 ≤ GaloisForLFunctions.HTGeometry.binaryReflectionForm α β v) :
    α = 0 ∧ β = 0 := by
  have hrate :
      GaloisForLFunctions.HTGeometry.reflectionTransverseRate
          (xiSpectralPoint q) ≠ 0 := by
    rw [reflectionTransverseRate_xiSpectralPoint_eq_sourceEntropy,
      riemannReflectedSourceEntropy_eq_neg_sourceCayleyRate]
    simp only [GaloisForLFunctions.HTGeometry.sourceCayleyTransverseRate,
      Complex.sub_re, Complex.one_re]
    intro hzero
    apply hoff
    linarith
  exact
    GaloisForLFunctions.HTGeometry.no_nonzero_positive_boostInvariant_reflectionForm
      hrate hinv hpos

/-- Global polarization curvature is exactly eight times conserved Xi source-orientation mass. -/
theorem xiSourceEntropyPolarizationCurvatureMass_eq_eight_mul_measureMass :
    xiSourceEntropyPolarizationCurvatureMass =
      8 * xiSourceEntropyOrientationMeasureMass := by
  unfold xiSourceEntropyPolarizationCurvatureMass
    xiSourceEntropyOrientationMeasureMass
  calc
    (∑' q : XiZeroCopy, xiSourceEntropyPolarizationCurvatureAtom q) =
        ∑' q : XiZeroCopy, 8 * xiSourceEntropyOrientationMassAtom q :=
      tsum_congr
        xiSourceEntropyPolarizationCurvatureAtom_eq_eight_mul_orientationMassAtom
    _ = 8 * ∑' q : XiZeroCopy, xiSourceEntropyOrientationMassAtom q :=
      tsum_mul_left

/-- The complete reflected-character Fisher mass is exactly conserved Xi source-orientation
mass. -/
theorem xiSourceEntropyReflectionFisherMass_eq_measureMass :
    xiSourceEntropyReflectionFisherMass =
      xiSourceEntropyOrientationMeasureMass := by
  unfold xiSourceEntropyReflectionFisherMass
    xiSourceEntropyOrientationMeasureMass
  exact tsum_congr xiSourceEntropyReflectionFisherAtom_eq_orientationMassAtom

/-- Positive Cauchy tomography weight.  Multiplying this weight by the squared
reciprocal-square orientation coordinate gives the quartet variance. -/
def xiSourceEntropyCauchyTomographyWeight (z a : ℂ) : ℝ :=
  (Complex.normSq a ^ (2 : ℕ) *
      (Complex.normSq a + Complex.normSq z)) /
    (4 *
      Complex.normSq (a - z) *
      Complex.normSq ((starRingEnd ℂ) a - z) *
      Complex.normSq (a + z) *
      Complex.normSq ((starRingEnd ℂ) a + z))

/-- Total Cauchy tomogram of the canonical Xi source-orientation measure. -/
def xiSourceEntropyCauchyTomography
    (z : XiContinuedCauchyPoint) : ℝ :=
  ∑' q : XiZeroCopy,
    xiSourceEntropyCauchyTomographyWeight (z : ℂ) (xiSpectralPoint q) *
      xiSourceEntropyOrientationMassAtom q

private theorem reciprocalSquare_im
    (a : ℂ) :
    (a⁻¹ ^ (2 : ℕ)).im =
      -2 * a.re * a.im / Complex.normSq a ^ (2 : ℕ) := by
  rw [pow_two, mul_im, Complex.inv_re, Complex.inv_im]
  ring

/-- Local tomography factorization: quartet variance is a positive geometric weight times the
squared signed source-orientation coordinate. -/
theorem cauchyQuartetVariance_eq_tomographyWeight_mul_orientationMass
    (z a : ℂ)
    (ha : a ≠ 0) (haz : a - z ≠ 0)
    (hcaz : (starRingEnd ℂ) a - z ≠ 0)
    (hapz : a + z ≠ 0)
    (hcapz : (starRingEnd ℂ) a + z ≠ 0) :
    xiReciprocalSquareCauchyQuartetVariance z a =
      xiSourceEntropyCauchyTomographyWeight z a * (a⁻¹ ^ (2 : ℕ)).im ^ (2 : ℕ) := by
  have hna : Complex.normSq a ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr ha)
  have hnaz : Complex.normSq (a - z) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr haz)
  have hncaz : Complex.normSq ((starRingEnd ℂ) a - z) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr hcaz)
  have hnapz : Complex.normSq (a + z) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr hapz)
  have hncapz : Complex.normSq ((starRingEnd ℂ) a + z) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr hcapz)
  rw [reciprocalSquare_im]
  unfold xiReciprocalSquareCauchyQuartetVariance
    xiSourceEntropyCauchyTomographyWeight
  field_simp [hna, hnaz, hncaz, hnapz, hncapz]
  ring

/-- The tomography weight is strictly positive at every regular spectral point. -/
theorem xiSourceEntropyCauchyTomographyWeight_pos
    (z a : ℂ)
    (ha : a ≠ 0) (haz : a - z ≠ 0)
    (hcaz : (starRingEnd ℂ) a - z ≠ 0)
    (hapz : a + z ≠ 0)
    (hcapz : (starRingEnd ℂ) a + z ≠ 0) :
    0 < xiSourceEntropyCauchyTomographyWeight z a := by
  unfold xiSourceEntropyCauchyTomographyWeight
  have hna : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha
  have hnaz : 0 < Complex.normSq (a - z) := Complex.normSq_pos.mpr haz
  have hncaz : 0 < Complex.normSq ((starRingEnd ℂ) a - z) :=
    Complex.normSq_pos.mpr hcaz
  have hnapz : 0 < Complex.normSq (a + z) := Complex.normSq_pos.mpr hapz
  have hncapz : 0 < Complex.normSq ((starRingEnd ℂ) a + z) :=
    Complex.normSq_pos.mpr hcapz
  exact div_pos
    (mul_pos (pow_pos hna 2)
      (add_pos_of_pos_of_nonneg hna (Complex.normSq_nonneg z)))
    (mul_pos
      (mul_pos
        (mul_pos
          (mul_pos (by norm_num) hnaz)
          hncaz)
      hnapz)
      hncapz)

set_option maxHeartbeats 1000000 in
/-- **Universal reflection-tomography law.**  On any multiplicity-exact countable divisor
carrying conjugation and negation symmetries, the signed reciprocal-square Cauchy defect is one
quadrant scalar times a positive tomogram of the squared orientation coordinate.  The result is
independent of Xi; the Xi law below is its arithmetic specialization. -/
theorem reciprocalSquareQuartetSymmetricCauchyTomographyLaw
    {ι : Type*} (point : ι → ℂ)
    (lineConj reflect : Equiv ι ι) (z : ℂ)
    (hlineConj : ∀ q, point (lineConj q) = (starRingEnd ℂ) (point q))
    (hreflect : ∀ q, point (reflect q) = -point q)
    (hregular : ∀ q,
      point q ≠ 0 ∧
      point q - z ≠ 0 ∧
      (starRingEnd ℂ) (point q) - z ≠ 0 ∧
      point q + z ≠ 0 ∧
      (starRingEnd ℂ) (point q) + z ≠ 0)
    (hterm : Summable (fun q =>
      xiReciprocalSquareCauchySpectralTerm z (point q)))
    (hzre : z.re ≠ 0) (hzim : z.im ≠ 0) :
    Summable (fun q =>
      xiSourceEntropyCauchyTomographyWeight z (point q) *
        ((point q)⁻¹ ^ (2 : ℕ)).im ^ (2 : ℕ)) ∧
      (∑' q, xiReciprocalSquareCauchySpectralTerm z (point q)) =
        16 * z.re * z.im *
          ∑' q, xiSourceEntropyCauchyTomographyWeight z (point q) *
            ((point q)⁻¹ ^ (2 : ℕ)).im ^ (2 : ℕ) := by
  let t : ι → ℝ := fun q =>
    xiReciprocalSquareCauchySpectralTerm z (point q)
  let w : ι → ℝ := fun q =>
    xiSourceEntropyCauchyTomographyWeight z (point q) *
      ((point q)⁻¹ ^ (2 : ℕ)).im ^ (2 : ℕ)
  let c : ℝ := 64 * z.re * z.im
  have hc : c ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hzre) hzim
  have ht : Summable t := hterm
  have hline : Summable (fun q => t (lineConj q)) :=
    (lineConj.summable_iff).mpr ht
  have href : Summable (fun q => t (reflect q)) :=
    (reflect.summable_iff).mpr ht
  have hboth : Summable (fun q => t (lineConj (reflect q))) :=
    (reflect.summable_iff).mpr ((lineConj.summable_iff).mpr ht)
  let quartet : ι → ℝ := fun q =>
    t q + t (lineConj q) + t (reflect q) + t (lineConj (reflect q))
  have hquartet : Summable quartet := by
    change Summable (fun q =>
      ((t q + t (lineConj q)) + t (reflect q)) +
        t (lineConj (reflect q)))
    exact ((ht.add hline).add href).add hboth
  have hlocal (q : ι) : quartet q = c * w q := by
    rcases hregular q with ⟨ha, haz, hcaz, hapz, hcapz⟩
    have horbit :=
      xiReciprocalSquareCauchySpectralTerm_quartet
        z (point q) ha haz hcaz hapz hcapz
    have hfactor :=
      cauchyQuartetVariance_eq_tomographyWeight_mul_orientationMass
        z (point q) ha haz hcaz hapz hcapz
    dsimp only [quartet, t, c, w]
    rw [hlineConj q, hreflect q, hlineConj (reflect q), hreflect q,
      map_neg]
    calc
      xiReciprocalSquareCauchySpectralTerm z (point q) +
            xiReciprocalSquareCauchySpectralTerm z
              ((starRingEnd ℂ) (point q)) +
          xiReciprocalSquareCauchySpectralTerm z (-point q) +
        xiReciprocalSquareCauchySpectralTerm z
          (-(starRingEnd ℂ) (point q)) =
          64 * z.re * z.im *
            xiReciprocalSquareCauchyQuartetVariance z (point q) := by
              unfold xiReciprocalSquareCauchyQuartetVariance
              convert horbit using 1
              ring
      _ = 64 * z.re * z.im *
          (xiSourceEntropyCauchyTomographyWeight z (point q) *
            ((point q)⁻¹ ^ (2 : ℕ)).im ^ (2 : ℕ)) := by rw [hfactor]
  have hscaled : Summable (fun q => c * w q) :=
    hquartet.congr hlocal
  have hw : Summable w := by
    exact (hscaled.mul_left c⁻¹).congr (fun q => by
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul])
  have hlineSum : (∑' q, t (lineConj q)) = ∑' q, t q :=
    lineConj.tsum_eq t
  have hrefSum : (∑' q, t (reflect q)) = ∑' q, t q :=
    reflect.tsum_eq t
  have hbothSum :
      (∑' q, t (lineConj (reflect q))) = ∑' q, t q :=
    (reflect.trans lineConj).tsum_eq t
  have hquartetSum : (∑' q, quartet q) = 4 * ∑' q, t q := by
    change (∑' q,
      (t q + t (lineConj q) + t (reflect q) +
        t (lineConj (reflect q)))) = _
    rw [((ht.add hline).add href).tsum_add hboth,
      (ht.add hline).tsum_add href,
      ht.tsum_add hline,
      hlineSum, hrefSum, hbothSum]
    ring
  have htomogramSum :
      (∑' q, quartet q) = c * ∑' q, w q := by
    calc
      (∑' q, quartet q) = ∑' q, c * w q := tsum_congr hlocal
      _ = c * ∑' q, w q := tsum_mul_left
  refine ⟨?_, ?_⟩
  · simpa only [w] using hw
  · change (∑' q, t q) =
      16 * z.re * z.im * ∑' q, w q
    dsimp only [c] at htomogramSum
    nlinarith [hquartetSum, htomogramSum]

/-- The reflection pairing of the signed reciprocal-square coordinate is the negative total
orientation mass on every conjugation-symmetric countable divisor. -/
theorem reciprocalSquareOrientationReflectionPairing_eq_neg_mass
    {ι : Type*} (point : ι → ℂ) (lineConj : Equiv ι ι)
    (hlineConj : ∀ q, point (lineConj q) = (starRingEnd ℂ) (point q)) :
    (∑' q,
      ((point (lineConj q))⁻¹ ^ (2 : ℕ)).im * ((point q)⁻¹ ^ (2 : ℕ)).im) =
      -∑' q, ((point q)⁻¹ ^ (2 : ℕ)).im ^ (2 : ℕ) := by
  rw [← tsum_neg]
  apply tsum_congr
  intro q
  rw [hlineConj q]
  simp only [← map_inv₀, ← map_pow, conj_im]
  ring

private theorem fixedCauchyTomography_numerator_lt_denominator
    (x y : ℝ)
    (hx : (41 / 2 : ℝ) < x ^ (2 : ℕ))
    (hy : y ^ (2 : ℕ) < (1 / 4 : ℝ)) :
    16 * (x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ (2 : ℕ) *
          (x ^ (2 : ℕ) + y ^ (2 : ℕ) + 1 / 8) <
      ((x - 1 / 4) ^ (2 : ℕ) + (y - 1 / 4) ^ (2 : ℕ)) *
      ((x - 1 / 4) ^ (2 : ℕ) + (-y - 1 / 4) ^ (2 : ℕ)) *
      ((x + 1 / 4) ^ (2 : ℕ) + (y + 1 / 4) ^ (2 : ℕ)) *
      ((x + 1 / 4) ^ (2 : ℕ) + (-y + 1 / 4) ^ (2 : ℕ)) := by
  let X : ℝ := x ^ (2 : ℕ)
  let N : ℝ := x ^ (2 : ℕ) + y ^ (2 : ℕ)
  let c : ℝ := (33 / 32 : ℝ) * X
  let d : ℝ := (31 / 32 : ℝ) * X
  have hX : 0 < X := by
    dsimp [X]
    nlinarith
  have hN : 0 ≤ N := by
    dsimp [N]
    positivity
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hNlt : N < c := by
    dsimp [N, c, X]
    nlinarith
  have hNzlt : N + 1 / 8 < c := by
    dsimp [N, c, X]
    nlinarith
  have hnum : N ^ (2 : ℕ) * (N + 1 / 8) < c ^ (3 : ℕ) := by
    calc
      N ^ (2 : ℕ) * (N + 1 / 8) < c ^ (2 : ℕ) * c := by
        gcongr
      _ = c ^ (3 : ℕ) := by ring
  have hdbase : d < X - 1 / 16 := by
    dsimp [d]
    nlinarith
  have hdpow : d ^ (4 : ℕ) < (X - 1 / 16) ^ (4 : ℕ) := by
    gcongr
  have hconstant : 16 * c ^ (3 : ℕ) < d ^ (4 : ℕ) := by
    dsimp [c, d]
    have hcoeff :
        16 * (33 / 32 : ℝ) ^ (3 : ℕ) <
          (31 / 32 : ℝ) ^ (4 : ℕ) * X := by
      nlinarith
    have hmul :=
      mul_lt_mul_of_pos_right hcoeff (pow_pos hX 3)
    calc
      16 * ((33 / 32 : ℝ) * X) ^ (3 : ℕ) =
          (16 * (33 / 32 : ℝ) ^ (3 : ℕ)) * X ^ (3 : ℕ) := by ring
      _ < ((31 / 32 : ℝ) ^ (4 : ℕ) * X) * X ^ (3 : ℕ) := hmul
      _ = ((31 / 32 : ℝ) * X) ^ (4 : ℕ) := by ring
  have hcore :
      16 * N ^ (2 : ℕ) * (N + 1 / 8) <
        (X - 1 / 16) ^ (4 : ℕ) := by
    calc
      16 * N ^ (2 : ℕ) * (N + 1 / 8) =
          16 * (N ^ (2 : ℕ) * (N + 1 / 8)) := by ring
      _ < 16 * c ^ (3 : ℕ) := by gcongr
      _ < d ^ (4 : ℕ) := hconstant
      _ < (X - 1 / 16) ^ (4 : ℕ) := hdpow
  have hxm : 0 ≤ (x - 1 / 4) ^ (2 : ℕ) := sq_nonneg _
  have hxp : 0 ≤ (x + 1 / 4) ^ (2 : ℕ) := sq_nonneg _
  have h1 :
      (x - 1 / 4) ^ (2 : ℕ) ≤
        (x - 1 / 4) ^ (2 : ℕ) + (y - 1 / 4) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (y - 1 / 4)]
  have h2 :
      (x - 1 / 4) ^ (2 : ℕ) ≤
        (x - 1 / 4) ^ (2 : ℕ) + (-y - 1 / 4) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (-y - 1 / 4)]
  have h3 :
      (x + 1 / 4) ^ (2 : ℕ) ≤
        (x + 1 / 4) ^ (2 : ℕ) + (y + 1 / 4) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (y + 1 / 4)]
  have h4 :
      (x + 1 / 4) ^ (2 : ℕ) ≤
        (x + 1 / 4) ^ (2 : ℕ) + (-y + 1 / 4) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (-y + 1 / 4)]
  have h12 :
      (x - 1 / 4) ^ (2 : ℕ) * (x - 1 / 4) ^ (2 : ℕ) ≤
        ((x - 1 / 4) ^ (2 : ℕ) + (y - 1 / 4) ^ (2 : ℕ)) *
        ((x - 1 / 4) ^ (2 : ℕ) + (-y - 1 / 4) ^ (2 : ℕ)) :=
    mul_le_mul h1 h2 hxm
      (add_nonneg hxm (sq_nonneg (y - 1 / 4)))
  have h34 :
      (x + 1 / 4) ^ (2 : ℕ) * (x + 1 / 4) ^ (2 : ℕ) ≤
        ((x + 1 / 4) ^ (2 : ℕ) + (y + 1 / 4) ^ (2 : ℕ)) *
        ((x + 1 / 4) ^ (2 : ℕ) + (-y + 1 / 4) ^ (2 : ℕ)) :=
    mul_le_mul h3 h4 hxp
      (add_nonneg hxp (sq_nonneg (y + 1 / 4)))
  have hprod :
      ((x - 1 / 4) ^ (2 : ℕ) * (x - 1 / 4) ^ (2 : ℕ)) *
          ((x + 1 / 4) ^ (2 : ℕ) * (x + 1 / 4) ^ (2 : ℕ)) ≤
        (((x - 1 / 4) ^ (2 : ℕ) + (y - 1 / 4) ^ (2 : ℕ)) *
          ((x - 1 / 4) ^ (2 : ℕ) + (-y - 1 / 4) ^ (2 : ℕ))) *
        (((x + 1 / 4) ^ (2 : ℕ) + (y + 1 / 4) ^ (2 : ℕ)) *
          ((x + 1 / 4) ^ (2 : ℕ) + (-y + 1 / 4) ^ (2 : ℕ))) :=
    mul_le_mul h12 h34
      (mul_nonneg hxp hxp)
      (mul_nonneg
        (add_nonneg hxm (sq_nonneg (y - 1 / 4)))
        (add_nonneg hxm (sq_nonneg (-y - 1 / 4))))
  have hfactor :
      (X - 1 / 16) ^ (4 : ℕ) =
        ((x - 1 / 4) ^ (2 : ℕ) * (x - 1 / 4) ^ (2 : ℕ)) *
          ((x + 1 / 4) ^ (2 : ℕ) * (x + 1 / 4) ^ (2 : ℕ)) := by
    dsimp [X]
    ring
  dsimp [N] at hcore
  calc
    16 * (x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ (2 : ℕ) * (x ^ (2 : ℕ) + y ^ (2 : ℕ) + 1 / 8) <
        (X - 1 / 16) ^ (4 : ℕ) := hcore
    _ = ((x - 1 / 4) ^ (2 : ℕ) * (x - 1 / 4) ^ (2 : ℕ)) *
          ((x + 1 / 4) ^ (2 : ℕ) * (x + 1 / 4) ^ (2 : ℕ)) := hfactor
    _ ≤ _ := by
      simpa only [mul_assoc] using hprod

private theorem xiSourceEntropyCauchyTomography_regular
    (z : XiContinuedCauchyPoint) (q : XiZeroCopy) :
    xiSpectralPoint q ≠ 0 ∧
      xiSpectralPoint q - (z : ℂ) ≠ 0 ∧
      (starRingEnd ℂ) (xiSpectralPoint q) - (z : ℂ) ≠ 0 ∧
      xiSpectralPoint q + (z : ℂ) ≠ 0 ∧
      (starRingEnd ℂ) (xiSpectralPoint q) + (z : ℂ) ≠ 0 := by
  let a : ℂ := xiSpectralPoint q
  have ha : a ≠ 0 := xiSpectralPoint_ne_zero q
  have haz : a - (z : ℂ) ≠ 0 :=
    xiSpectralPoint_sub_continuedCauchyPoint_ne z q
  have hcaz : (starRingEnd ℂ) a - (z : ℂ) ≠ 0 := by
    simpa only [a, xiSpectralPoint_lineConj] using
      xiSpectralPoint_sub_continuedCauchyPoint_ne z
        (xiZeroCopyLineConjEquiv q)
  have hnegaz : -a - (z : ℂ) ≠ 0 := by
    simpa only [a, xiSpectralPoint_reflect] using
      xiSpectralPoint_sub_continuedCauchyPoint_ne z
        (xiZeroCopyReflectEquiv q)
  have hapz : a + (z : ℂ) ≠ 0 := by
    intro h
    apply hnegaz
    rw [show -a - (z : ℂ) = -(a + (z : ℂ)) by ring, h]
    simp
  have hnegcaz : -(starRingEnd ℂ) a - (z : ℂ) ≠ 0 := by
    simpa only [a, xiSpectralPoint_reflect, xiSpectralPoint_lineConj,
      map_neg] using
        xiSpectralPoint_sub_continuedCauchyPoint_ne z
          (xiZeroCopyLineConjEquiv (xiZeroCopyReflectEquiv q))
  have hcapz : (starRingEnd ℂ) a + (z : ℂ) ≠ 0 := by
    intro h
    apply hnegcaz
    rw [show -(starRingEnd ℂ) a - (z : ℂ) =
      -((starRingEnd ℂ) a + (z : ℂ)) by ring, h]
    simp
  exact ⟨ha, haz, hcaz, hapz, hcapz⟩

/-- Every Xi quartet variance is one strictly positive Cauchy weight times the corresponding
atom of the conserved source-orientation measure. -/
theorem xiReciprocalSquareCauchyQuartetVariance_eq_sourceEntropyTomography
    (z : XiContinuedCauchyPoint) (q : XiZeroCopy) :
    xiReciprocalSquareCauchyQuartetVariance
        (z : ℂ) (xiSpectralPoint q) =
      xiSourceEntropyCauchyTomographyWeight
          (z : ℂ) (xiSpectralPoint q) *
        xiSourceEntropyOrientationMassAtom q := by
  rcases xiSourceEntropyCauchyTomography_regular z q with
    ⟨ha, haz, hcaz, hapz, hcapz⟩
  simpa only [xiSourceEntropyOrientationMassAtom,
    xiZeroCopyReciprocalSquare] using
      cauchyQuartetVariance_eq_tomographyWeight_mul_orientationMass
        (z : ℂ) (xiSpectralPoint q) ha haz hcaz hapz hcapz

/-- Off the coordinate axes, the positive tomography integrand is summable. -/
theorem summable_xiSourceEntropyCauchyTomography
    (z : XiContinuedCauchyPoint)
    (hzre : (z : ℂ).re ≠ 0) (hzim : (z : ℂ).im ≠ 0) :
    Summable (fun q : XiZeroCopy =>
      xiSourceEntropyCauchyTomographyWeight (z : ℂ) (xiSpectralPoint q) *
        xiSourceEntropyOrientationMassAtom q) := by
  exact
    (summable_xiReciprocalSquareCauchyQuartetVariance z hzre hzim).congr
      (fun q =>
        xiReciprocalSquareCauchyQuartetVariance_eq_sourceEntropyTomography
          z q)

/-- Every Xi Cauchy tomography weight is strictly positive. -/
theorem xiSourceEntropyCauchyTomographyWeight_xi_pos
    (z : XiContinuedCauchyPoint) (q : XiZeroCopy) :
    0 < xiSourceEntropyCauchyTomographyWeight
      (z : ℂ) (xiSpectralPoint q) := by
  rcases xiSourceEntropyCauchyTomography_regular z q with
    ⟨ha, haz, hcaz, hapz, hcapz⟩
  exact xiSourceEntropyCauchyTomographyWeight_pos
    (z : ℂ) (xiSpectralPoint q) ha haz hcaz hapz hcapz

/-- The source-derived Xi height gap uniformly suppresses the predetermined Cauchy tomogram:
each of its positive weights is strictly below `1 / 64`. -/
theorem xiSourceEntropyFixedCauchyTomographyWeight_lt_one_div_sixtyFour
    (q : XiZeroCopy) :
    xiSourceEntropyCauchyTomographyWeight
        (xiReciprocalSquareFixedCauchyPole : ℂ) (xiSpectralPoint q) <
      1 / 64 := by
  let a : ℂ := xiSpectralPoint q
  change xiSourceEntropyCauchyTomographyWeight
      (xiReciprocalSquareFixedCauchyPole : ℂ) a < 1 / 64
  have hx : (41 / 2 : ℝ) < a.re ^ (2 : ℕ) := by
    simpa [a, xiSpectralPoint, Complex.mul_re] using
      xiZeroCopy_fortyOne_div_two_lt_im_sq q
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hy : a.im ^ (2 : ℕ) < (1 / 4 : ℝ) := by
    have hproduct :
        0 < (q.1 : ℂ).re * (1 - (q.1 : ℂ).re) :=
      mul_pos hstrip.1 (sub_pos.mpr hstrip.2)
    have haim : a.im = -((q.1 : ℂ).re - 1 / 2) := by
      dsimp [a, xiSpectralPoint]
      simp [Complex.mul_im]
    rw [haim]
    nlinarith
  have hpoly :=
    fixedCauchyTomography_numerator_lt_denominator a.re a.im hx hy
  have hden :
      0 <
        4 *
          Complex.normSq (a - (xiReciprocalSquareFixedCauchyPole : ℂ)) *
          Complex.normSq
            ((starRingEnd ℂ) a -
              (xiReciprocalSquareFixedCauchyPole : ℂ)) *
          Complex.normSq (a + (xiReciprocalSquareFixedCauchyPole : ℂ)) *
          Complex.normSq
            ((starRingEnd ℂ) a +
              (xiReciprocalSquareFixedCauchyPole : ℂ)) := by
    rcases xiSourceEntropyCauchyTomography_regular
        xiReciprocalSquareFixedCauchyPole q with
      ⟨-, haz, hcaz, hapz, hcapz⟩
    exact mul_pos
      (mul_pos
        (mul_pos
          (mul_pos (by norm_num)
            (Complex.normSq_pos.mpr haz))
          (Complex.normSq_pos.mpr hcaz))
        (Complex.normSq_pos.mpr hapz))
      (Complex.normSq_pos.mpr hcapz)
  unfold xiSourceEntropyCauchyTomographyWeight
  rw [div_lt_iff₀ hden]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, conj_re, conj_im,
    xiReciprocalSquareFixedCauchyPole_re,
    xiReciprocalSquareFixedCauchyPole_im]
  nlinarith

/-- The fixed Cauchy tomogram is at most one sixty-fourth of total conserved source mass. -/
theorem xiSourceEntropyFixedCauchyTomography_le_measureMass_div_sixtyFour :
    xiSourceEntropyCauchyTomography xiReciprocalSquareFixedCauchyPole ≤
      xiSourceEntropyOrientationMeasureMass / 64 := by
  rw [xiSourceEntropyCauchyTomography,
    xiSourceEntropyOrientationMeasureMass, div_eq_mul_inv,
    ← tsum_mul_right]
  have hweighted :=
    summable_xiSourceEntropyCauchyTomography
      xiReciprocalSquareFixedCauchyPole (by norm_num) (by norm_num)
  have hmass :
      Summable (fun q : XiZeroCopy =>
        xiSourceEntropyOrientationMassAtom q) := by
    simpa only [xiSourceEntropyOrientationMassAtom] using
      summable_xiThermalOrientationTerm
  exact hweighted.tsum_le_tsum
    (fun q => by
      simpa only [xiSourceEntropyOrientationMassAtom, mul_comm,
        div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_right
          (le_of_lt
            (xiSourceEntropyFixedCauchyTomographyWeight_lt_one_div_sixtyFour q))
          (sq_nonneg (xiZeroCopyReciprocalSquare q).im))
    (hmass.mul_right (64 : ℝ)⁻¹)

/-- The total mass of the source-orientation measure is exactly the conserved source-entropy
energy. -/
theorem xiSourceEntropyOrientationMeasureMass_eq_energy :
    xiSourceEntropyOrientationMeasureMass =
      xiSourceEntropyOrientationEnergy := by
  unfold xiSourceEntropyOrientationMeasureMass
    xiSourceEntropyOrientationMassAtom
  rw [xiSourceEntropyOrientationEnergy_eq_thermalOrientationEnergy]
  rfl

/-- The Xi--Weil quadratic form reads the negative total mass of the canonical orientation
measure. -/
theorem xiWeilHilbertQuadratic_sourceEntropyOrientationVector_eq_neg_measureMass :
    xiWeilHilbertQuadratic xiSourceEntropyOrientationVector =
      -xiSourceEntropyOrientationMeasureMass := by
  rw [xiWeilHilbertQuadratic_xiSourceEntropyOrientationVector,
    xiSourceEntropyOrientationMeasureMass_eq_energy]

/-- **Cauchy tomography law.**  Every regular continued-Cauchy orientation defect is one
quadrant scalar times a positive weighted moment of the same conserved source-orientation
measure. -/
theorem xiSourceEntropyCauchyTomographyLaw
    (z : XiContinuedCauchyPoint) :
    xiReciprocalSquareContinuedCauchyOrientationDefect z =
      16 * (z : ℂ).re * (z : ℂ).im *
        xiSourceEntropyCauchyTomography z := by
  rw [xiReciprocalSquareContinuedCauchyOrientationDefect_eq_variance_tsum,
    xiSourceEntropyCauchyTomography]
  congr 1
  apply tsum_congr
  intro q
  exact
    xiReciprocalSquareCauchyQuartetVariance_eq_sourceEntropyTomography z q

/-- Off the coordinate axes, every Cauchy tomogram is faithful: its mass vanishes exactly when
RH holds. -/
theorem xiSourceEntropyCauchyTomography_eq_zero_iff_riemannHypothesis
    (z : XiContinuedCauchyPoint)
    (hzre : (z : ℂ).re ≠ 0) (hzim : (z : ℂ).im ≠ 0) :
    xiSourceEntropyCauchyTomography z = 0 ↔ RiemannHypothesis := by
  rw [← xiReciprocalSquareContinuedCauchyOrientationDefect_eq_zero_iff_riemannHypothesis
      z hzre hzim]
  rw [xiSourceEntropyCauchyTomographyLaw]
  have hcoefficient : 16 * (z : ℂ).re * (z : ℂ).im ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hzre) hzim
  constructor
  · intro hzero
    rw [hzero, mul_zero]
  · intro hzero
    exact (mul_eq_zero.mp hzero).resolve_left hcoefficient

/-- At the predetermined pole `1/4 + i/4`, the quadrant scalar is one.  The fixed orientation
defect is therefore exactly one positive tomogram of the conserved source-orientation measure. -/
theorem xiReciprocalSquareFixedCauchyOrientationDefect_eq_sourceEntropyTomography :
    xiReciprocalSquareContinuedCauchyOrientationDefect
        xiReciprocalSquareFixedCauchyPole =
      xiSourceEntropyCauchyTomography
        xiReciprocalSquareFixedCauchyPole := by
  rw [xiSourceEntropyCauchyTomographyLaw]
  norm_num

/-- The predetermined one-pole RH defect is uniformly bounded by one sixty-fourth of the
conserved source-entropy energy. -/
theorem xiReciprocalSquareFixedCauchyOrientationDefect_le_energy_div_sixtyFour :
    xiReciprocalSquareContinuedCauchyOrientationDefect
        xiReciprocalSquareFixedCauchyPole ≤
      xiSourceEntropyOrientationEnergy / 64 := by
  rw [xiReciprocalSquareFixedCauchyOrientationDefect_eq_sourceEntropyTomography,
    ← xiSourceEntropyOrientationMeasureMass_eq_energy]
  exact xiSourceEntropyFixedCauchyTomography_le_measureMass_div_sixtyFour

/-- New unconditional quantitative bound for the predetermined one-pole orientation defect. -/
theorem xiReciprocalSquareFixedCauchyOrientationDefect_lt_one_over_nineMillionSixHundredThousand :
    xiReciprocalSquareContinuedCauchyOrientationDefect
        xiReciprocalSquareFixedCauchyPole <
      1 / 9600000 := by
  have hdefect :=
    xiReciprocalSquareFixedCauchyOrientationDefect_le_energy_div_sixtyFour
  have henergy :=
    xiSourceEntropyOrientationEnergy_lt_one_over_oneHundredFiftyThousand
  nlinarith

end

end RHTower
