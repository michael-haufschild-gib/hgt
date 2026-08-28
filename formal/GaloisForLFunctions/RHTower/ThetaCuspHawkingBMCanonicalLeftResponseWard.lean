import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceIndependentResponseDichotomy

/-!
# Canonical BM left-response Ward

The exact BM horizon-to-AdS connection matrix depends on each Xi divisor, as do its canonical dual
left covectors. Nevertheless, evaluating either dual covector on its own matching connection column
scaled by one global amplitude `c` returns exactly `c` on every fibre.

Thus both canonical radial left responses are literally source-independent after dual
normalization. Using either as the Peierls response correction gives exactly the HC20 fixed scalar
current, with local zero locus `c = 0 ∨ Re(q) = 1/2` and global zero law `c = 0 ∨ RH`. Unit canonical
left-response stationarity is exactly canonical Peierls--Darboux optical darkness.

This closes radial left-QNM normalization and noncollapse. The already constructed global Peierls
operator realizes exact canonical left-source incidence; HC22 subsequently isolates two-branch
FE--Schwarz covariance, rather than action incidence, as the remaining endpoint.

`[NEW] [LEFT-QNM NORMALIZATION] [EXACT DICHOTOMY] [RH EQUIVALENCE] [LEAN-PROVED]`
-/

open Complex Real Set

namespace RHTower

noncomputable section

/-- Canonical regular left response to its globally scaled matching connection column. -/
def d4BMXiSecondHarmonicCanonicalRegularLeftResponse
    (n : ℕ) (c : ℂ) (q : XiZeroCopy) : ℂ :=
  d4BMXiPlusPlusRegularLeftConnectionCovector n q
    (c * d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n
      (d4BMXiMixedHorizonAngularMomentum q))
    (c * d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n
      (d4BMXiMixedHorizonAngularMomentum q))

/-- Canonical complementary left response to its globally scaled matching connection column. -/
def d4BMXiSecondHarmonicCanonicalComplementaryLeftResponse
    (n : ℕ) (c : ℂ) (q : XiZeroCopy) : ℂ :=
  d4BMXiPlusPlusComplementaryLeftConnectionCovector n q
    (c * d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n
      (d4BMXiMixedHorizonAngularMomentum q))
    (c * d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n
      (d4BMXiMixedHorizonAngularMomentum q))

/-- Canonical regular dual normalization removes every Xi-dependent connection coefficient. -/
theorem d4BMXiSecondHarmonicCanonicalRegularLeftResponse_eq
    (n : ℕ) (c : ℂ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicCanonicalRegularLeftResponse n c q = c := by
  rw [d4BMXiSecondHarmonicCanonicalRegularLeftResponse,
    d4BMXiPlusPlusRegularLeftConnectionCovector_scale,
    d4BMXiPlusPlusRegularLeftConnectionCovector_regular_eq_one, mul_one]

/-- Canonical complementary dual normalization removes every Xi-dependent connection coefficient. -/
theorem d4BMXiSecondHarmonicCanonicalComplementaryLeftResponse_eq
    (n : ℕ) (c : ℂ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicCanonicalComplementaryLeftResponse n c q = c := by
  rw [d4BMXiSecondHarmonicCanonicalComplementaryLeftResponse,
    d4BMXiPlusPlusComplementaryLeftConnectionCovector_scale,
    d4BMXiPlusPlusComplementaryLeftConnectionCovector_complementary_eq_one, mul_one]

theorem d4BMXiSecondHarmonicCanonicalRegularLeftResponse_fun_eq
    (n : ℕ) (c : ℂ) :
    d4BMXiSecondHarmonicCanonicalRegularLeftResponse n c =
      d4BMXiSecondHarmonicSourceIndependentResponseCorrection c := by
  funext q
  rw [d4BMXiSecondHarmonicCanonicalRegularLeftResponse_eq]
  rfl

theorem d4BMXiSecondHarmonicCanonicalComplementaryLeftResponse_fun_eq
    (n : ℕ) (c : ℂ) :
    d4BMXiSecondHarmonicCanonicalComplementaryLeftResponse n c =
      d4BMXiSecondHarmonicSourceIndependentResponseCorrection c := by
  funext q
  rw [d4BMXiSecondHarmonicCanonicalComplementaryLeftResponse_eq]
  rfl

/-- Peierls current corrected by canonical regular left response. -/
def d4BMXiSecondHarmonicCanonicalRegularLeftResponseCurrent
    (n : ℕ) (c : ℂ) (q : XiZeroCopy) : ℂ :=
  d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent n
    (d4BMXiSecondHarmonicCanonicalRegularLeftResponse n c) q

/-- Peierls current corrected by canonical complementary left response. -/
def d4BMXiSecondHarmonicCanonicalComplementaryLeftResponseCurrent
    (n : ℕ) (c : ℂ) (q : XiZeroCopy) : ℂ :=
  d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent n
    (d4BMXiSecondHarmonicCanonicalComplementaryLeftResponse n c) q

theorem d4BMXiSecondHarmonicCanonicalRegularLeftResponseCurrent_eq
    (n : ℕ) (c : ℂ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicCanonicalRegularLeftResponseCurrent n c q =
      d4BMXiSecondHarmonicSourceIndependentResponseCurrent n c q := by
  rw [d4BMXiSecondHarmonicCanonicalRegularLeftResponseCurrent,
    d4BMXiSecondHarmonicSourceIndependentResponseCurrent,
    d4BMXiSecondHarmonicCanonicalRegularLeftResponse_fun_eq]

theorem d4BMXiSecondHarmonicCanonicalComplementaryLeftResponseCurrent_eq
    (n : ℕ) (c : ℂ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicCanonicalComplementaryLeftResponseCurrent n c q =
      d4BMXiSecondHarmonicSourceIndependentResponseCurrent n c q := by
  rw [d4BMXiSecondHarmonicCanonicalComplementaryLeftResponseCurrent,
    d4BMXiSecondHarmonicSourceIndependentResponseCurrent,
    d4BMXiSecondHarmonicCanonicalComplementaryLeftResponse_fun_eq]

theorem d4BMXiSecondHarmonicCanonicalRegularLeftResponseCurrent_eq_zero_iff
    (n : ℕ) (c : ℂ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicCanonicalRegularLeftResponseCurrent n c q = 0 ↔
      c = 0 ∨ (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiSecondHarmonicCanonicalRegularLeftResponseCurrent_eq,
    d4BMXiSecondHarmonicSourceIndependentResponseCurrent_eq_zero_iff]

theorem d4BMXiSecondHarmonicCanonicalComplementaryLeftResponseCurrent_eq_zero_iff
    (n : ℕ) (c : ℂ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicCanonicalComplementaryLeftResponseCurrent n c q = 0 ↔
      c = 0 ∨ (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiSecondHarmonicCanonicalComplementaryLeftResponseCurrent_eq,
    d4BMXiSecondHarmonicSourceIndependentResponseCurrent_eq_zero_iff]

/-- Exact regular-left global dichotomy. -/
theorem forall_d4BMXiSecondHarmonicCanonicalRegularLeftResponseCurrent_eq_zero_iff
    (n : ℕ) (c : ℂ) :
    (∀ q : XiZeroCopy,
      d4BMXiSecondHarmonicCanonicalRegularLeftResponseCurrent n c q = 0) ↔
      c = 0 ∨ RiemannHypothesis := by
  simpa only [d4BMXiSecondHarmonicCanonicalRegularLeftResponseCurrent_eq] using
    forall_d4BMXiSecondHarmonicSourceIndependentResponseCurrent_eq_zero_iff n c

/-- Exact complementary-left global dichotomy. -/
theorem forall_d4BMXiSecondHarmonicCanonicalComplementaryLeftResponseCurrent_eq_zero_iff
    (n : ℕ) (c : ℂ) :
    (∀ q : XiZeroCopy,
      d4BMXiSecondHarmonicCanonicalComplementaryLeftResponseCurrent n c q = 0) ↔
      c = 0 ∨ RiemannHypothesis := by
  simpa only [d4BMXiSecondHarmonicCanonicalComplementaryLeftResponseCurrent_eq] using
    forall_d4BMXiSecondHarmonicSourceIndependentResponseCurrent_eq_zero_iff n c

/-- Unit regular-left Ward is exactly canonical optical darkness. -/
theorem d4BMXiSecondHarmonicCanonicalRegularUnitLeftWard_iff_canonicalOpticalWard
    (n : ℕ) :
    (∀ q : XiZeroCopy,
      d4BMXiSecondHarmonicCanonicalRegularLeftResponseCurrent n 1 q = 0) ↔
      ∀ q : XiZeroCopy,
        hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n q = 0 := by
  simpa only [d4BMXiSecondHarmonicCanonicalRegularLeftResponseCurrent_eq] using
    d4BMXiSecondHarmonicSourceIndependentUnitWard_iff_canonicalOpticalWard n

/-- Unit complementary-left Ward is exactly canonical optical darkness. -/
theorem d4BMXiSecondHarmonicCanonicalComplementaryUnitLeftWard_iff_canonicalOpticalWard
    (n : ℕ) :
    (∀ q : XiZeroCopy,
      d4BMXiSecondHarmonicCanonicalComplementaryLeftResponseCurrent n 1 q = 0) ↔
      ∀ q : XiZeroCopy,
        hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n q = 0 := by
  simpa only [d4BMXiSecondHarmonicCanonicalComplementaryLeftResponseCurrent_eq] using
    d4BMXiSecondHarmonicSourceIndependentUnitWard_iff_canonicalOpticalWard n

end

end RHTower
