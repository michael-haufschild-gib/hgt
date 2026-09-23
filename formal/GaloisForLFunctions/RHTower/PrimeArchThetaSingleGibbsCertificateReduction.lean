import GaloisForLFunctions.RHTower.PrimeArchThetaMorseFisherExponentialEnvelope

/-!
# Single-Gibbs reduction of the first-atom source certificates

The first theta atom has Liouville Gibbs density `b₁` and Born--Witten density `χ₁²`.
Their exact Ward relation

`χ₁² = -b₁ - 2 b₁'`

collapses every radial Born--Witten moment to two consecutive moments of `b₁`.  Consequently
both live low-degree source certificates -- the Morse--Fisher upper certificate and the relaxed
fourth-moment certificate -- are finite rational inequalities in one positive Gibbs moment
sequence.  No auxiliary quantum density remains in the scalar verification problem.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Pointwise Ward identity between the first Born--Witten density and the first Liouville Gibbs
density. -/
theorem thetaCuspFirstAtomBornWittenDensity_eq_gibbsWard
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspBornWittenAmplitude 1 x ^ (2 : ℕ) =
      -thetaCuspLiouvilleGibbsAtom 1 x -
        2 * deriv (thetaCuspLiouvilleGibbsAtom 1) x := by
  have hsource := thetaCuspSourceTerm_eq_pi_mul_bornWittenAmplitude_sq
    (n := 1) (by norm_num) hx
  rw [(hasDerivAt_thetaCuspLiouvilleGibbsAtom 1 x).deriv]
  rw [thetaCuspSourceTerm_eq_liouvilleWard,
    (hasDerivAt_thetaCuspLiouvilleGibbsAtom 1 x).deriv] at hsource
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi] at hsource ⊢
  linarith

/-- Every first-atom radial Born--Witten power moment is a two-term expression in the single
positive Liouville Gibbs moment sequence. -/
theorem thetaCuspBornWittenRadialPowerMoment_eq_singleGibbs (m : ℕ) :
    thetaCuspBornWittenRadialPowerMoment m 1 1 =
      2 * (m + 2 : ℕ) * thetaCuspLiouvilleGibbsMoment (m + 1) 1 -
        thetaCuspLiouvilleGibbsMoment (m + 2) 1 := by
  let b : ℝ → ℝ := thetaCuspLiouvilleGibbsAtom 1
  let db : ℝ → ℝ := fun x => deriv (thetaCuspLiouvilleGibbsAtom 1) x
  let f : ℝ → ℝ := fun x => x ^ (m + 2) * b x
  let g : ℝ → ℝ := fun x => x ^ (m + 2) * db x
  have hf : IntegrableOn f (Ioi 0) := by
    simpa only [f, b, thetaCuspLiouvilleGibbsAtom] using
      integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
        (m + 2) (X ^ (2 : ℕ)) (n := 1) (by norm_num)
  have hg : IntegrableOn g (Ioi 0) := by
    have h := integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
      (m + 2) (thetaCuspLogDerivativeStep (X ^ (2 : ℕ))) (n := 1) (by norm_num)
    apply h.congr
    filter_upwards [] with x
    simp only [g, db]
    rw [(hasDerivAt_thetaCuspLiouvilleGibbsAtom 1 x).deriv]
  have hrewrite :
      thetaCuspBornWittenRadialPowerMoment m 1 1 =
        ∫ x : ℝ in Ioi 0, -f x - 2 * g x := by
    rw [thetaCuspBornWittenRadialPowerMoment]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [thetaCuspBornWittenRadialAmplitude_sq,
      thetaCuspFirstAtomBornWittenDensity_eq_gibbsWard hx.le]
    simp only [f, g, b, db]
    rw [pow_add]
    ring
  rw [hrewrite]
  rw [show (fun x : ℝ => -f x - 2 * g x) =
      (fun x : ℝ => -f x + (-2) * g x) by
        funext x
        ring]
  have hsplit := integral_add hf.neg (hg.const_mul (-2))
  change (∫ x : ℝ in Ioi 0, -f x + (-2) * g x) =
    (∫ x : ℝ in Ioi 0, -f x) +
      ∫ x : ℝ in Ioi 0, (-2) * g x at hsplit
  rw [hsplit, integral_neg, integral_const_mul]
  have hd := integral_pow_mul_thetaCuspLiouvilleGibbs_deriv_eq
    (m + 2) (by omega) (n := 1) (by norm_num)
  have hfval : (∫ x : ℝ in Ioi 0, f x) =
      thetaCuspLiouvilleGibbsMoment (m + 2) 1 := by
    rfl
  have hgval : (∫ x : ℝ in Ioi 0, g x) =
      -(m + 2 : ℕ) * thetaCuspLiouvilleGibbsMoment (m + 1) 1 := by
    simpa only [g, db, show m + 2 - 1 = m + 1 by omega] using hd
  rw [hfval, hgval]
  push_cast
  ring

/-- The sharpened Morse--Fisher upper value written solely in the first Gibbs moments. -/
def thetaCuspFirstRadialQuadraticMorseSingleGibbsUpperValue : ℝ :=
  3 * thetaCuspLiouvilleGibbsMoment 1 1 +
    (21 / 4 : ℝ) * thetaCuspLiouvilleGibbsMoment 2 1 +
    (-25 / 8 + 6 * thetaCuspFirstAtomMorseFisherDecayFactor) *
      thetaCuspLiouvilleGibbsMoment 4 1 -
    (15 / 4 + 18 * thetaCuspFirstAtomMorseFisherDecayFactor) *
      thetaCuspLiouvilleGibbsMoment 5 1 +
    ((39 / 16 : ℝ) +
      (51 / 2 : ℝ) * thetaCuspFirstAtomMorseFisherDecayFactor) *
      thetaCuspLiouvilleGibbsMoment 6 1 -
    15 * thetaCuspFirstAtomMorseFisherDecayFactor *
      thetaCuspLiouvilleGibbsMoment 7 1 +
    3 * thetaCuspFirstAtomMorseFisherDecayFactor *
      thetaCuspLiouvilleGibbsMoment 8 1

theorem thetaCuspFirstRadialQuadraticMorseFiniteMomentUpperValue_eq_singleGibbs :
    thetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeFiniteMomentUpperValue =
      thetaCuspFirstRadialQuadraticMorseSingleGibbsUpperValue := by
  rw [thetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeFiniteMomentUpperValue,
    thetaCuspFirstRadialQuadraticMorseSingleGibbsUpperValue,
    thetaCuspBornWittenRadialPowerMoment_eq_singleGibbs 0,
    thetaCuspBornWittenRadialPowerMoment_eq_singleGibbs 1,
    thetaCuspBornWittenRadialPowerMoment_eq_singleGibbs 2,
    thetaCuspBornWittenRadialPowerMoment_eq_singleGibbs 3,
    thetaCuspBornWittenRadialPowerMoment_eq_singleGibbs 4]
  norm_num
  ring

/-- The Stein coupling in the sharpened certificate is another linear functional of the same
Gibbs moment sequence. -/
theorem thetaCuspFirstRadialQuadraticSteinCoupling_eq_singleGibbs :
    thetaCuspFirstRadialQuadraticSteinCoupling =
      8 * thetaCuspLiouvilleGibbsMoment 3 1 -
        6 * thetaCuspLiouvilleGibbsMoment 4 1 +
          (1 / 2 : ℝ) * thetaCuspLiouvilleGibbsMoment 5 1 := by
  have h2 := integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
    2 1 (n := 1) (by norm_num)
  have h3 := integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
    3 1 (n := 1) (by norm_num)
  rw [thetaCuspFirstRadialQuadraticSteinCoupling]
  have hsplit := integral_sub h2 (h3.const_mul (1 / 2 : ℝ))
  change (∫ x : ℝ in Ioi 0,
      x ^ (2 : ℕ) * thetaCuspBornWittenRadialAmplitude 1 1 x ^ (2 : ℕ) -
        (1 / 2 : ℝ) *
          (x ^ (3 : ℕ) * thetaCuspBornWittenRadialAmplitude 1 1 x ^ (2 : ℕ))) =
      (∫ x : ℝ in Ioi 0,
        x ^ (2 : ℕ) * thetaCuspBornWittenRadialAmplitude 1 1 x ^ (2 : ℕ)) -
      ∫ x : ℝ in Ioi 0,
        (1 / 2 : ℝ) *
          (x ^ (3 : ℕ) * thetaCuspBornWittenRadialAmplitude 1 1 x ^ (2 : ℕ)) at hsplit
  rw [show (fun x : ℝ =>
      (x ^ (2 : ℕ) - x ^ (3 : ℕ) / 2) *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ (2 : ℕ)) =
      (fun x : ℝ =>
        x ^ (2 : ℕ) * thetaCuspBornWittenRadialAmplitude 1 1 x ^ (2 : ℕ) -
          (1 / 2 : ℝ) *
            (x ^ (3 : ℕ) * thetaCuspBornWittenRadialAmplitude 1 1 x ^ (2 : ℕ))) by
      funext x
      ring,
    hsplit, integral_const_mul]
  change thetaCuspBornWittenRadialPowerMoment 2 1 1 -
      (1 / 2 : ℝ) * thetaCuspBornWittenRadialPowerMoment 3 1 1 = _
  rw [thetaCuspBornWittenRadialPowerMoment_eq_singleGibbs 2,
    thetaCuspBornWittenRadialPowerMoment_eq_singleGibbs 3]
  norm_num
  ring

/-- The Morse--Fisher scalar certificate after eliminating all Born--Witten moments. -/
def ThetaCuspFirstAtomSingleGibbsMorseCertificate : Prop :=
  (14 * (3005 / 2997 : ℝ) ^ (2 : ℕ) - 9) *
        (8 * thetaCuspLiouvilleGibbsMoment 3 1 -
          thetaCuspLiouvilleGibbsMoment 4 1) ^ (2 : ℕ) *
          thetaCuspFirstRadialQuadraticMorseSingleGibbsUpperValue ≤
    9 * (4 * thetaCuspLiouvilleGibbsMoment 1 1 -
          thetaCuspLiouvilleGibbsMoment 2 1) *
      (8 * thetaCuspLiouvilleGibbsMoment 3 1 -
        6 * thetaCuspLiouvilleGibbsMoment 4 1 +
          (1 / 2 : ℝ) * thetaCuspLiouvilleGibbsMoment 5 1) ^ (2 : ℕ)

theorem thetaCuspFirstAtomSingleGibbsMorseCertificate_iff :
    ThetaCuspFirstAtomSingleGibbsMorseCertificate ↔
      ThetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeCertificate := by
  rw [ThetaCuspFirstAtomSingleGibbsMorseCertificate,
    ThetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeCertificate,
    thetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeUpperEnergy_eq_finiteMoments,
    thetaCuspFirstRadialQuadraticMorseFiniteMomentUpperValue_eq_singleGibbs,
    thetaCuspBornWittenRadialPowerMoment_eq_singleGibbs 0,
    thetaCuspBornWittenRadialPowerMoment_eq_singleGibbs 2,
    thetaCuspFirstRadialQuadraticSteinCoupling_eq_singleGibbs]
  norm_num

/-- The first-atom Ward moments are exactly the nonradial Born--Witten moments. -/
theorem thetaCuspBornWittenRadialRawMoment_zero_eq_firstAtomWardMoment (j : ℕ) :
    thetaCuspBornWittenRadialRawMoment j 0 1 =
      thetaCuspFirstAtomWardMoment j := by
  have hrad := thetaCuspAtomRawEvenMoment_eq_radialBornWittenRawMoment j 0 1
  have hward := thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment j
  norm_num only [Nat.add_zero] at hrad
  nlinarith [Real.pi_pos]

/-- The relaxed fourth-moment certificate in the same Gibbs coordinates. -/
def ThetaCuspFirstAtomSingleGibbsRelaxedCertificate : Prop :=
  16 * ((3005 / 2997 : ℝ) *
      (2 * Real.exp (-Real.pi) - thetaCuspLiouvilleGibbsMoment 0 1)) *
      ((3005 / 2997 : ℝ) *
        (8 * thetaCuspLiouvilleGibbsMoment 3 1 -
          thetaCuspLiouvilleGibbsMoment 4 1)) ≤
    45 * (4 * thetaCuspLiouvilleGibbsMoment 1 1 -
      thetaCuspLiouvilleGibbsMoment 2 1) ^ (2 : ℕ)

theorem thetaCuspFirstAtomSingleGibbsRelaxedCertificate_iff :
    ThetaCuspFirstAtomSingleGibbsRelaxedCertificate ↔
      16 * ((3005 / 2997 : ℝ) *
          thetaCuspBornWittenRadialRawMoment 0 0 1) *
          ((3005 / 2997 : ℝ) *
            thetaCuspBornWittenRadialRawMoment 2 0 1) ≤
        45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ (2 : ℕ) := by
  rw [ThetaCuspFirstAtomSingleGibbsRelaxedCertificate,
    thetaCuspBornWittenRadialRawMoment_zero_eq_firstAtomWardMoment 0,
    thetaCuspBornWittenRadialRawMoment_zero_eq_firstAtomWardMoment 1,
    thetaCuspBornWittenRadialRawMoment_zero_eq_firstAtomWardMoment 2]
  simp only [thetaCuspFirstAtomWardMoment]
  norm_num

/-- One positive moment fiber now contains both live low-degree source obligations. -/
def ThetaCuspFirstAtomSingleGibbsLowDegreeCertificate : Prop :=
  ThetaCuspFirstAtomSingleGibbsMorseCertificate ∧
    ThetaCuspFirstAtomSingleGibbsRelaxedCertificate

theorem thetaCuspFirstAtomSingleGibbsLowDegreeCertificate_iff :
    ThetaCuspFirstAtomSingleGibbsLowDegreeCertificate ↔
      ThetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeCertificate ∧
        16 * ((3005 / 2997 : ℝ) *
            thetaCuspBornWittenRadialRawMoment 0 0 1) *
            ((3005 / 2997 : ℝ) *
              thetaCuspBornWittenRadialRawMoment 2 0 1) ≤
          45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ (2 : ℕ) := by
  rw [ThetaCuspFirstAtomSingleGibbsLowDegreeCertificate,
    thetaCuspFirstAtomSingleGibbsMorseCertificate_iff,
    thetaCuspFirstAtomSingleGibbsRelaxedCertificate_iff]

/-- A proof of the single-Gibbs certificate controls every linear prime--archimedean
trace-Hankel test. -/
theorem forall_primeArchSourceTraceHankel_linear_nonneg_of_singleGibbsLowDegreeCertificate
    (hcert : ThetaCuspFirstAtomSingleGibbsLowDegreeCertificate) :
    ∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re := by
  rw [thetaCuspFirstAtomSingleGibbsLowDegreeCertificate_iff] at hcert
  exact forall_primeArchSourceTraceHankel_linear_nonneg_of_morseQuadraticEnvelope
    hcert.1 hcert.2

/-- Master reduction: the two low-degree Connes--Born/Witten estimate channels are exactly one
finite certificate for the moments of a single positive Gibbs density, and that certificate
implies positivity of the complete linear trace-Hankel block. -/
def ThetaCuspFirstAtomSingleGibbsCertificateMaster : Prop :=
  (ThetaCuspFirstAtomSingleGibbsLowDegreeCertificate ↔
      ThetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeCertificate ∧
        16 * ((3005 / 2997 : ℝ) *
            thetaCuspBornWittenRadialRawMoment 0 0 1) *
            ((3005 / 2997 : ℝ) *
              thetaCuspBornWittenRadialRawMoment 2 0 1) ≤
          45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ (2 : ℕ)) ∧
  (ThetaCuspFirstAtomSingleGibbsLowDegreeCertificate →
    ∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re)

theorem thetaCuspFirstAtomSingleGibbsCertificateMaster :
    ThetaCuspFirstAtomSingleGibbsCertificateMaster := by
  exact ⟨thetaCuspFirstAtomSingleGibbsLowDegreeCertificate_iff,
    forall_primeArchSourceTraceHankel_linear_nonneg_of_singleGibbsLowDegreeCertificate⟩

end

end RHTower
