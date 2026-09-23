import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskyMediatorPoleMultiplicityEndpoint
import GaloisForLFunctions.RHTower.XiWardEndpointSourceIndex

/-!
# Exact theta-reflected Teukolsky scattering

Functional reflection shifts the Birmingham--Mokhtari radial parameters by one. Reciprocal-Gamma
recurrence therefore swaps a canonical scattering numerator and denominator. Off the critical line,
the reflected frequencies are a cross-laced Jost zero--pole pair; their Cayley values are `-1` and
`1`. At critical coalescence the completed Cayley amplitude is `0`.

These statements concern the exact hypergeometric gravitational master equation. They do not assert
nonzero projection of the nonlinear Einstein source onto either channel.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Complexified displacement from the theta fixed line. -/
def d4BMXiThetaMirrorTilt (q : XiZeroCopy) : ℂ :=
  (((q.1 : ℂ).re - 1 / 2 : ℝ) : ℂ)

lemma d4BMXiReflectedRealPairMediatorAngularQ_reflect (q : XiZeroCopy) :
    d4BMXiReflectedRealPairMediatorAngularQ (xiZeroCopyReflectEquiv q) =
      -(q.1 : ℂ).re * ((q.1 : ℂ).re + 1) := by
  unfold d4BMXiReflectedRealPairMediatorAngularQ
  rw [xiZeroCopyReflectEquiv_rho]
  simp only [Complex.sub_re, Complex.one_re]
  ring

theorem d4BMXiReflectedRealPairMediatorAngularQ_sub_reflect (q : XiZeroCopy) :
    d4BMXiReflectedRealPairMediatorAngularQ q -
        d4BMXiReflectedRealPairMediatorAngularQ (xiZeroCopyReflectEquiv q) =
      4 * ((q.1 : ℂ).re - 1 / 2) := by
  rw [d4BMXiReflectedRealPairMediatorAngularQ_reflect]
  unfold d4BMXiReflectedRealPairMediatorAngularQ
  ring

theorem d4BMXiReflectedRealPairFrequency_sub_reflect
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiReflectedRealPairFrequency n q -
        d4BMXiReflectedRealPairFrequency n (xiZeroCopyReflectEquiv q) =
      2 * Complex.I * d4BMXiThetaMirrorTilt q := by
  rw [d4BMXiReflectedRealPairFrequency_eq,
    d4BMXiReflectedRealPairFrequency_eq, xiZeroCopyReflectEquiv_rho]
  unfold d4BMXiThetaMirrorTilt
  simp only [Complex.sub_re, Complex.one_re]
  push_cast
  ring

/-- Joint frequency--angular label of a reflected BM mediator. -/
def d4BMXiReflectedMediatorChannel (n : ℕ) (q : XiZeroCopy) : ℂ × ℝ :=
  (d4BMXiReflectedRealPairFrequency n q,
    d4BMXiReflectedRealPairMediatorAngularQ q)

theorem d4BMXiReflectedMediatorChannel_eq_reflect_iff
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiReflectedMediatorChannel n q =
        d4BMXiReflectedMediatorChannel n (xiZeroCopyReflectEquiv q) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    have hQ := congrArg Prod.snd h
    have hs : d4BMXiReflectedRealPairMediatorAngularQ q -
        d4BMXiReflectedRealPairMediatorAngularQ (xiZeroCopyReflectEquiv q) = 0 :=
      sub_eq_zero.mpr hQ
    rw [d4BMXiReflectedRealPairMediatorAngularQ_sub_reflect] at hs
    linarith
  · intro hline
    apply Prod.ext
    · apply sub_eq_zero.mp
      unfold d4BMXiReflectedMediatorChannel
      rw [d4BMXiReflectedRealPairFrequency_sub_reflect]
      unfold d4BMXiThetaMirrorTilt
      rw [hline]
      norm_num
    · apply sub_eq_zero.mp
      unfold d4BMXiReflectedMediatorChannel
      rw [d4BMXiReflectedRealPairMediatorAngularQ_sub_reflect, hline]
      norm_num

/-- Theta reflection cross-laces the plus root with the opposite-helicity minus root. -/
theorem d4BMXiReflectedRealPairFrequency_reflect_eq_qnmMinus
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiReflectedRealPairFrequency n (xiZeroCopyReflectEquiv q) =
      thetaCuspHawkingTopologicalBlackHoleQNMMinus (2 * n + 1)
        (d4BMXiReflectedRealPairMediatorSpectralPoint q) := by
  rw [d4BMXiReflectedRealPairFrequency_eq, xiZeroCopyReflectEquiv_rho,
    thetaCuspHawkingTopologicalBlackHoleQNMMinus,
    d4BMXiReflectedRealPairMediatorSpectralPoint_angularMomentum]
  unfold thetaCuspHawkingTopologicalBlackHoleConformalDecay
  simp only [Complex.sub_re, Complex.one_re]
  push_cast
  ring

lemma d4BMXiReflectedMediatorRadialA_reflect
    (omega : ℂ) (q : XiZeroCopy) :
    thetaCuspHawkingHypergeometricRadialA omega
        (d4BMXiReflectedRealPairMediatorSpectralPoint
          (xiZeroCopyReflectEquiv q)) =
      thetaCuspHawkingHypergeometricRadialB omega
          (d4BMXiReflectedRealPairMediatorSpectralPoint q) + 1 := by
  unfold thetaCuspHawkingHypergeometricRadialA
    thetaCuspHawkingHypergeometricRadialB
  rw [d4BMXiReflectedRealPairMediatorSpectralPoint_angularMomentum,
    d4BMXiReflectedRealPairMediatorSpectralPoint_angularMomentum,
    xiZeroCopyReflectEquiv_rho]
  simp only [Complex.sub_re, Complex.one_re]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

lemma d4BMXiReflectedMediatorRadialB_reflect
    (omega : ℂ) (q : XiZeroCopy) :
    thetaCuspHawkingHypergeometricRadialB omega
        (d4BMXiReflectedRealPairMediatorSpectralPoint
          (xiZeroCopyReflectEquiv q)) =
      thetaCuspHawkingHypergeometricRadialA omega
          (d4BMXiReflectedRealPairMediatorSpectralPoint q) - 1 := by
  unfold thetaCuspHawkingHypergeometricRadialA
    thetaCuspHawkingHypergeometricRadialB
  rw [d4BMXiReflectedRealPairMediatorSpectralPoint_angularMomentum,
    d4BMXiReflectedRealPairMediatorSpectralPoint_angularMomentum,
    xiZeroCopyReflectEquiv_rho]
  simp only [Complex.sub_re, Complex.one_re]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Entire reciprocal-Gamma recurrence, including its integral zeros. -/
lemma d4BMXiThetaMirrorReciprocalGamma_add_one (s : ℂ) :
    GaloisForLFunctions.reciprocalGammaEntire s =
      s * GaloisForLFunctions.reciprocalGammaEntire (s + 1) := by
  unfold GaloisForLFunctions.reciprocalGammaEntire
  exact Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one s

/-- Gamma-contiguous numerator of the theta-mirror scattering pair. -/
def d4BMXiThetaMirrorScatteringNumerator (omega : ℂ) (q : XiZeroCopy) : ℂ :=
  (thetaCuspHawkingHypergeometricRadialA omega
      (d4BMXiReflectedRealPairMediatorSpectralPoint q) - 1) *
    thetaCuspHawkingHypergeometricJostPlus omega
      (d4BMXiReflectedRealPairMediatorSpectralPoint q)

/-- Opposite-helicity Jost denominator of the theta-mirror scattering pair. -/
def d4BMXiThetaMirrorScatteringDenominator (omega : ℂ) (q : XiZeroCopy) : ℂ :=
  thetaCuspHawkingHypergeometricJostMinus omega
    (d4BMXiReflectedRealPairMediatorSpectralPoint q)

theorem d4BMXiThetaMirrorScatteringNumerator_reflect
    (omega : ℂ) (q : XiZeroCopy) :
    d4BMXiThetaMirrorScatteringNumerator omega (xiZeroCopyReflectEquiv q) =
      d4BMXiThetaMirrorScatteringDenominator omega q := by
  unfold d4BMXiThetaMirrorScatteringNumerator
    d4BMXiThetaMirrorScatteringDenominator
    thetaCuspHawkingHypergeometricJostPlus
    thetaCuspHawkingHypergeometricJostMinus
  rw [d4BMXiReflectedMediatorRadialA_reflect]
  convert (d4BMXiThetaMirrorReciprocalGamma_add_one
    (thetaCuspHawkingHypergeometricRadialB omega
      (d4BMXiReflectedRealPairMediatorSpectralPoint q))).symm using 1
  all_goals ring_nf

theorem d4BMXiThetaMirrorScatteringDenominator_reflect
    (omega : ℂ) (q : XiZeroCopy) :
    d4BMXiThetaMirrorScatteringDenominator omega (xiZeroCopyReflectEquiv q) =
      d4BMXiThetaMirrorScatteringNumerator omega q := by
  unfold d4BMXiThetaMirrorScatteringNumerator
    d4BMXiThetaMirrorScatteringDenominator
    thetaCuspHawkingHypergeometricJostPlus
    thetaCuspHawkingHypergeometricJostMinus
  rw [d4BMXiReflectedMediatorRadialB_reflect]
  have hrec := d4BMXiThetaMirrorReciprocalGamma_add_one
    (thetaCuspHawkingHypergeometricRadialA omega
      (d4BMXiReflectedRealPairMediatorSpectralPoint q) - 1)
  convert hrec using 1
  all_goals ring_nf

/-- Meromorphic theta-mirror scattering quotient. -/
def d4BMXiThetaMirrorSMatrix (omega : ℂ) (q : XiZeroCopy) : ℂ :=
  d4BMXiThetaMirrorScatteringNumerator omega q /
    d4BMXiThetaMirrorScatteringDenominator omega q

theorem d4BMXiThetaMirrorSMatrix_reflect
    (omega : ℂ) (q : XiZeroCopy) :
    d4BMXiThetaMirrorSMatrix omega (xiZeroCopyReflectEquiv q) =
      (d4BMXiThetaMirrorSMatrix omega q)⁻¹ := by
  rw [d4BMXiThetaMirrorSMatrix, d4BMXiThetaMirrorSMatrix,
    d4BMXiThetaMirrorScatteringNumerator_reflect,
    d4BMXiThetaMirrorScatteringDenominator_reflect]
  simp only [inv_div]

/-- Cayley coordinate compactifying the mirror zero and pole to `-1` and `1`. -/
def d4BMXiThetaMirrorCayleyAmplitude (omega : ℂ) (q : XiZeroCopy) : ℂ :=
  (d4BMXiThetaMirrorScatteringNumerator omega q -
      d4BMXiThetaMirrorScatteringDenominator omega q) /
    (d4BMXiThetaMirrorScatteringNumerator omega q +
      d4BMXiThetaMirrorScatteringDenominator omega q)

theorem d4BMXiThetaMirrorCayleyAmplitude_reflect
    (omega : ℂ) (q : XiZeroCopy) :
    d4BMXiThetaMirrorCayleyAmplitude omega (xiZeroCopyReflectEquiv q) =
      -d4BMXiThetaMirrorCayleyAmplitude omega q := by
  rw [d4BMXiThetaMirrorCayleyAmplitude, d4BMXiThetaMirrorCayleyAmplitude,
    d4BMXiThetaMirrorScatteringNumerator_reflect,
    d4BMXiThetaMirrorScatteringDenominator_reflect]
  ring

theorem d4BMXiThetaMirrorScatteringNumerator_ownFrequency_eq_zero
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiThetaMirrorScatteringNumerator
        (d4BMXiReflectedRealPairFrequency n q) q = 0 := by
  unfold d4BMXiThetaMirrorScatteringNumerator
  rw [d4BMXiReflectedRealPairFrequency_eq_mediatorQNM,
    thetaCuspHawkingHypergeometricJostPlus_qnm_zero]
  simp

theorem d4BMXiThetaMirrorScatteringDenominator_ownFrequency_ne_zero_of_tilt
    (n : ℕ) (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    d4BMXiThetaMirrorScatteringDenominator
        (d4BMXiReflectedRealPairFrequency n q) q ≠ 0 := by
  exact d4BMXiReflectedMediatorJostMinus_ne_zero_of_tilt n q htilt

theorem d4BMXiThetaMirrorScatteringDenominator_mirrorFrequency_eq_zero
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiThetaMirrorScatteringDenominator
        (d4BMXiReflectedRealPairFrequency n (xiZeroCopyReflectEquiv q)) q = 0 := by
  unfold d4BMXiThetaMirrorScatteringDenominator
  rw [d4BMXiReflectedRealPairFrequency_reflect_eq_qnmMinus,
    thetaCuspHawkingHypergeometricJostMinus_qnm_zero]

theorem d4BMXiThetaMirrorScatteringNumerator_mirrorFrequency_ne_zero_of_tilt
    (n : ℕ) (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    d4BMXiThetaMirrorScatteringNumerator
        (d4BMXiReflectedRealPairFrequency n (xiZeroCopyReflectEquiv q)) q ≠ 0 := by
  rw [← d4BMXiThetaMirrorScatteringDenominator_reflect]
  exact d4BMXiReflectedMediatorJostMinus_ne_zero_of_tilt n
    (xiZeroCopyReflectEquiv q) (xiEndpointOffLineSet_reflect q htilt)

/-- A tilted theta pair is a projective scattering zero--pole pair in one BM angular channel. -/
theorem d4BMXiThetaMirror_projective_zero_pole_pair_of_tilt
    (n : ℕ) (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    (d4BMXiThetaMirrorScatteringNumerator
          (d4BMXiReflectedRealPairFrequency n q) q = 0 ∧
        d4BMXiThetaMirrorScatteringDenominator
          (d4BMXiReflectedRealPairFrequency n q) q ≠ 0) ∧
      (d4BMXiThetaMirrorScatteringDenominator
          (d4BMXiReflectedRealPairFrequency n (xiZeroCopyReflectEquiv q)) q = 0 ∧
        d4BMXiThetaMirrorScatteringNumerator
          (d4BMXiReflectedRealPairFrequency n (xiZeroCopyReflectEquiv q)) q ≠ 0) := by
  exact ⟨⟨d4BMXiThetaMirrorScatteringNumerator_ownFrequency_eq_zero n q,
      d4BMXiThetaMirrorScatteringDenominator_ownFrequency_ne_zero_of_tilt n q htilt⟩,
    ⟨d4BMXiThetaMirrorScatteringDenominator_mirrorFrequency_eq_zero n q,
      d4BMXiThetaMirrorScatteringNumerator_mirrorFrequency_ne_zero_of_tilt n q htilt⟩⟩

theorem d4BMXiThetaMirrorCayleyAmplitude_ownFrequency_eq_neg_one_of_tilt
    (n : ℕ) (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    d4BMXiThetaMirrorCayleyAmplitude
        (d4BMXiReflectedRealPairFrequency n q) q = -1 := by
  rw [d4BMXiThetaMirrorCayleyAmplitude,
    d4BMXiThetaMirrorScatteringNumerator_ownFrequency_eq_zero]
  field_simp [d4BMXiThetaMirrorScatteringDenominator_ownFrequency_ne_zero_of_tilt
    n q htilt]
  ring

theorem d4BMXiThetaMirrorCayleyAmplitude_mirrorFrequency_eq_one_of_tilt
    (n : ℕ) (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    d4BMXiThetaMirrorCayleyAmplitude
        (d4BMXiReflectedRealPairFrequency n (xiZeroCopyReflectEquiv q)) q = 1 := by
  rw [d4BMXiThetaMirrorCayleyAmplitude,
    d4BMXiThetaMirrorScatteringDenominator_mirrorFrequency_eq_zero]
  field_simp [d4BMXiThetaMirrorScatteringNumerator_mirrorFrequency_ne_zero_of_tilt
    n q htilt]
  ring

lemma d4BMXiReflectedMediatorRadialB_eq_radialA_sub_one_of_line
    (omega : ℂ) (q : XiZeroCopy) (hline : (q.1 : ℂ).re = 1 / 2) :
    thetaCuspHawkingHypergeometricRadialB omega
        (d4BMXiReflectedRealPairMediatorSpectralPoint q) =
      thetaCuspHawkingHypergeometricRadialA omega
        (d4BMXiReflectedRealPairMediatorSpectralPoint q) - 1 := by
  unfold thetaCuspHawkingHypergeometricRadialA
    thetaCuspHawkingHypergeometricRadialB
  rw [d4BMXiReflectedRealPairMediatorSpectralPoint_angularMomentum, hline]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem d4BMXiThetaMirrorScatteringNumerator_eq_denominator_of_line
    (omega : ℂ) (q : XiZeroCopy) (hline : (q.1 : ℂ).re = 1 / 2) :
    d4BMXiThetaMirrorScatteringNumerator omega q =
      d4BMXiThetaMirrorScatteringDenominator omega q := by
  unfold d4BMXiThetaMirrorScatteringNumerator
    d4BMXiThetaMirrorScatteringDenominator
    thetaCuspHawkingHypergeometricJostPlus
    thetaCuspHawkingHypergeometricJostMinus
  rw [d4BMXiReflectedMediatorRadialB_eq_radialA_sub_one_of_line omega q hline]
  have hrec := d4BMXiThetaMirrorReciprocalGamma_add_one
    (thetaCuspHawkingHypergeometricRadialA omega
      (d4BMXiReflectedRealPairMediatorSpectralPoint q) - 1)
  symm
  convert hrec using 1
  all_goals ring_nf

theorem d4BMXiThetaMirrorCayleyAmplitude_eq_zero_of_line
    (omega : ℂ) (q : XiZeroCopy) (hline : (q.1 : ℂ).re = 1 / 2) :
    d4BMXiThetaMirrorCayleyAmplitude omega q = 0 := by
  rw [d4BMXiThetaMirrorCayleyAmplitude,
    d4BMXiThetaMirrorScatteringNumerator_eq_denominator_of_line omega q hline]
  simp

theorem d4BMXiThetaMirrorCayleyAmplitude_ownFrequency_eq_zero_iff
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiThetaMirrorCayleyAmplitude
          (d4BMXiReflectedRealPairFrequency n q) q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hzero
    by_contra htilt
    rw [d4BMXiThetaMirrorCayleyAmplitude_ownFrequency_eq_neg_one_of_tilt
      n q htilt] at hzero
    norm_num at hzero
  · exact d4BMXiThetaMirrorCayleyAmplitude_eq_zero_of_line _ q

lemma d4BMXiThetaMirrorRadialA_node
    (n : ℕ) (q : XiZeroCopy) (w : ℂ) :
    thetaCuspHawkingHypergeometricRadialA
          (d4BMFunctionalReflectionMediatorFrequency n n + w)
          (d4BMXiReflectedRealPairMediatorSpectralPoint q) + (2 * n : ℕ) =
      -(Complex.I / 2) * (w - Complex.I * d4BMXiThetaMirrorTilt q) := by
  unfold thetaCuspHawkingHypergeometricRadialA
    d4BMFunctionalReflectionMediatorFrequency d4BMXiThetaMirrorTilt
  rw [d4BMXiReflectedRealPairMediatorSpectralPoint_angularMomentum]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

lemma d4BMXiThetaMirrorRadialB_node
    (n : ℕ) (q : XiZeroCopy) (w : ℂ) :
    thetaCuspHawkingHypergeometricRadialB
          (d4BMFunctionalReflectionMediatorFrequency n n + w)
          (d4BMXiReflectedRealPairMediatorSpectralPoint q) + (2 * n + 1 : ℕ) =
      -(Complex.I / 2) * (w + Complex.I * d4BMXiThetaMirrorTilt q) := by
  unfold thetaCuspHawkingHypergeometricRadialB
    d4BMFunctionalReflectionMediatorFrequency d4BMXiThetaMirrorTilt
  rw [d4BMXiReflectedRealPairMediatorSpectralPoint_angularMomentum]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Exact BM exceptional-node polynomial centered at the universal damped frequency. -/
theorem d4BMXiThetaMirrorRadialNode_product
    (n : ℕ) (q : XiZeroCopy) (w : ℂ) :
    (thetaCuspHawkingHypergeometricRadialA
          (d4BMFunctionalReflectionMediatorFrequency n n + w)
          (d4BMXiReflectedRealPairMediatorSpectralPoint q) + (2 * n : ℕ)) *
        (thetaCuspHawkingHypergeometricRadialB
          (d4BMFunctionalReflectionMediatorFrequency n n + w)
          (d4BMXiReflectedRealPairMediatorSpectralPoint q) + (2 * n + 1 : ℕ)) =
      -(1 / 4 : ℂ) * (w ^ (2 : ℕ) + d4BMXiThetaMirrorTilt q ^ (2 : ℕ)) := by
  rw [d4BMXiThetaMirrorRadialA_node, d4BMXiThetaMirrorRadialB_node]
  ring_nf
  norm_num [Complex.I_sq]

end

end RHTower
