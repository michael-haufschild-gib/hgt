import GaloisForLFunctions.RHTower.SourceHorizontalAdaptiveFisherCofinalContiguitySelection
import GaloisForLFunctions.RHTower.HedenmalmGammaSewnSquarefreeParityLocalization

/-!
# Adaptive horizontal occupation as bounded-admission vacuum fusion

Adaptive prime occupation has log-odds `(t - 1) log p`.  This module splits that exponent before
scalarization.  A centered horizontal bit has odds `p^t`; the arithmetic vacuum bit has odds
`p⁻¹`.  Conditioning their product on equality multiplies the two odds and recovers the adaptive
occupation exactly.  The equality aperture never collapses: its admission is at least `1/(p+1)`
at every horizontal grade.

This gives a literal cross-corpus transition target.  The centered source orientation and the
prime-vacuum grade need only be fused through a uniformly admitted equality relation; exact
unconditioned adaptive observers are stronger than necessary.  A qualitative theorem below proves
that absolute continuity still forces neutral grade for any varying admission family with a
uniform positive forward aperture.  Thus postselection cannot evade source contiguity by hiding in
events of vanishing mass.

No source theorem constructing the centered orientation is assumed here.
-/

open Real Set MeasureTheory Filter Topology
open scoped ENNReal

namespace RHTower

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Exact odds fusion -/

/-- Probability of the `true,true` state after retaining only the two equal states of two bits. -/
def sourceHorizontalEqualFusion (x y : ℝ) : ℝ :=
  x * y / (x * y + (1 - x) * (1 - y))

/-- Total mass retained by equality postselection of two independent bits. -/
def sourceHorizontalEqualAdmission (x y : ℝ) : ℝ :=
  x * y + (1 - x) * (1 - y)

/-- Centered horizontal occupation.  Its odds are exactly `p^t`. -/
def sourceHorizontalPrimeCenteredOccupation (p : Nat.Primes) (t : ℝ) : ℝ :=
  (p : ℝ) ^ t / (1 + (p : ℝ) ^ t)

/-- Arithmetic vacuum occupation.  Its odds are the prime weight `p⁻¹`. -/
def sourceHorizontalPrimeVacuumOccupation (p : Nat.Primes) : ℝ :=
  1 / ((p : ℝ) + 1)

theorem sourceHorizontalPrimeCenteredOccupation_pos (p : Nat.Primes) (t : ℝ) :
    0 < sourceHorizontalPrimeCenteredOccupation p t := by
  unfold sourceHorizontalPrimeCenteredOccupation
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  positivity

theorem sourceHorizontalPrimeCenteredOccupation_lt_one (p : Nat.Primes) (t : ℝ) :
    sourceHorizontalPrimeCenteredOccupation p t < 1 := by
  unfold sourceHorizontalPrimeCenteredOccupation
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  apply (div_lt_one (by positivity)).2
  linarith [Real.rpow_pos_of_pos hp t]

theorem sourceHorizontalPrimeVacuumOccupation_pos (p : Nat.Primes) :
    0 < sourceHorizontalPrimeVacuumOccupation p := by
  unfold sourceHorizontalPrimeVacuumOccupation
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  positivity

theorem sourceHorizontalPrimeVacuumOccupation_lt_one (p : Nat.Primes) :
    sourceHorizontalPrimeVacuumOccupation p < 1 := by
  unfold sourceHorizontalPrimeVacuumOccupation
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  apply (div_lt_one (by positivity)).2
  linarith

theorem sourceHorizontalPrimeCenteredOccupation_odds (p : Nat.Primes) (t : ℝ) :
    sourceHorizontalPrimeCenteredOccupation p t /
        (1 - sourceHorizontalPrimeCenteredOccupation p t) =
      (p : ℝ) ^ t := by
  unfold sourceHorizontalPrimeCenteredOccupation
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hpt : 0 < (p : ℝ) ^ t := Real.rpow_pos_of_pos hp _
  field_simp
  ring

theorem sourceHorizontalPrimeVacuumOccupation_odds (p : Nat.Primes) :
    sourceHorizontalPrimeVacuumOccupation p /
        (1 - sourceHorizontalPrimeVacuumOccupation p) =
      ((p : ℝ))⁻¹ := by
  unfold sourceHorizontalPrimeVacuumOccupation
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  field_simp
  rw [show (p : ℝ) + 1 - 1 = p by ring, div_self hp.ne']

/-- **Vacuum-fusion identity.** Equality postselection adds the centered horizontal and vacuum
log-odds, hence recovers adaptive occupation exactly. -/
theorem sourceHorizontalEqualFusion_centered_vacuum
    (p : Nat.Primes) (t : ℝ) :
    sourceHorizontalEqualFusion
        (sourceHorizontalPrimeCenteredOccupation p t)
        (sourceHorizontalPrimeVacuumOccupation p) =
      sourceHorizontalPrimeAdaptiveOccupation p t := by
  unfold sourceHorizontalEqualFusion sourceHorizontalPrimeCenteredOccupation
    sourceHorizontalPrimeVacuumOccupation sourceHorizontalPrimeAdaptiveOccupation
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hpt : 0 < (p : ℝ) ^ t := Real.rpow_pos_of_pos hp _
  have hsum : (p : ℝ) + (p : ℝ) ^ t ≠ 0 := by positivity
  field_simp [hsum]
  have hden :
      (p : ℝ) ^ t + (1 + (p : ℝ) ^ t - (p : ℝ) ^ t) *
          ((p : ℝ) + 1 - 1) =
        (p : ℝ) + (p : ℝ) ^ t := by ring
  rw [hden, div_self hsum]

/-- Exact equality-aperture mass for centered-horizontal/vacuum fusion. -/
theorem sourceHorizontalEqualAdmission_centered_vacuum
    (p : Nat.Primes) (t : ℝ) :
    sourceHorizontalEqualAdmission
        (sourceHorizontalPrimeCenteredOccupation p t)
        (sourceHorizontalPrimeVacuumOccupation p) =
      ((p : ℝ) ^ t + (p : ℝ)) /
        (((p : ℝ) ^ t + 1) * ((p : ℝ) + 1)) := by
  unfold sourceHorizontalEqualAdmission sourceHorizontalPrimeCenteredOccupation
    sourceHorizontalPrimeVacuumOccupation
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hpt : 0 < (p : ℝ) ^ t := Real.rpow_pos_of_pos hp _
  field_simp
  ring

/-- Equality fusion has a grade-independent arithmetic aperture.  In particular, cofinal
horizontal dilation cannot make the postselection mass disappear. -/
theorem sourceHorizontalEqualAdmission_centered_vacuum_lower
    (p : Nat.Primes) (t : ℝ) :
    1 / ((p : ℝ) + 1) ≤
      sourceHorizontalEqualAdmission
        (sourceHorizontalPrimeCenteredOccupation p t)
        (sourceHorizontalPrimeVacuumOccupation p) := by
  rw [sourceHorizontalEqualAdmission_centered_vacuum]
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hp1 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  have hpt : 0 < (p : ℝ) ^ t := Real.rpow_pos_of_pos hp _
  rw [div_le_div_iff₀ hp1 (mul_pos (by positivity) hp1)]
  have hpone : (1 : ℝ) ≤ p := by exact_mod_cast p.2.one_lt.le
  nlinarith

theorem sourceHorizontalEqualFusion_reflected_centered_vacuum
    (p : Nat.Primes) (t : ℝ) :
    sourceHorizontalEqualFusion
          (sourceHorizontalPrimeCenteredOccupation p t)
          (sourceHorizontalPrimeVacuumOccupation p) =
        sourceHorizontalPrimeAdaptiveOccupation p t ∧
      sourceHorizontalEqualFusion
          (sourceHorizontalPrimeCenteredOccupation p (-t))
          (sourceHorizontalPrimeVacuumOccupation p) =
        sourceHorizontalPrimeAdaptiveOccupation p (-t) := by
  exact ⟨sourceHorizontalEqualFusion_centered_vacuum p t,
    sourceHorizontalEqualFusion_centered_vacuum p (-t)⟩

/-- Coefficient-faithful factorization of adaptive odds into horizontal and vacuum characters. -/
theorem sourceHorizontalPrimeAdaptiveOccupation_odds_eq_centered_mul_vacuum
    (p : Nat.Primes) (t : ℝ) :
    sourceHorizontalPrimeAdaptiveOccupation p t /
        (1 - sourceHorizontalPrimeAdaptiveOccupation p t) =
      (sourceHorizontalPrimeCenteredOccupation p t /
          (1 - sourceHorizontalPrimeCenteredOccupation p t)) *
        (sourceHorizontalPrimeVacuumOccupation p /
          (1 - sourceHorizontalPrimeVacuumOccupation p)) := by
  rw [sourceHorizontalPrimeAdaptiveOccupation_odds,
    sourceHorizontalPrimeCenteredOccupation_odds,
    sourceHorizontalPrimeVacuumOccupation_odds]
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rw [Real.rpow_sub hp]
  norm_num
  simp [div_eq_mul_inv]

/-! ## Route-N squarefree parity supplies both scalar orientations -/

/-- Outward adaptive odds reconstructed non-equivariantly from critical and inward Route-N
squarefree parity odds. -/
def routeNGammaSewnOutwardAdaptiveParityOdds
    (t : ℝ) (p : Nat.Primes) : ℝ :=
  routeNGammaSewnCriticalSquarefreeParityOdds p ^ 2 /
    routeNGammaSewnTwistedSquarefreeParityOdds t p

/-- Inward adaptive odds are already the twisted Route-N squarefree parity odds. -/
def routeNGammaSewnInwardAdaptiveParityOdds
    (t : ℝ) (p : Nat.Primes) : ℝ :=
  routeNGammaSewnTwistedSquarefreeParityOdds t p

theorem routeNGammaSewnOutwardAdaptiveParityOdds_eq
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnOutwardAdaptiveParityOdds t p =
      (p : ℝ) ^ (2 * |t| - 1) := by
  rw [routeNGammaSewnOutwardAdaptiveParityOdds,
    routeNGammaSewnCriticalSquarefreeParityOdds_eq,
    routeNGammaSewnTwistedSquarefreeParityOdds_eq]
  unfold routeNGammaSewnUniversalCriticalChannelMass
    routeNGammaSewnTwistedCriticalChannelMass
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rw [pow_two, ← Real.rpow_add hp, ← Real.rpow_sub hp]
  congr 1
  ring

theorem routeNGammaSewnInwardAdaptiveParityOdds_eq
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnInwardAdaptiveParityOdds t p =
      (p : ℝ) ^ (-2 * |t| - 1) := by
  rw [routeNGammaSewnInwardAdaptiveParityOdds,
    routeNGammaSewnTwistedSquarefreeParityOdds_eq]
  unfold routeNGammaSewnTwistedCriticalChannelMass
  congr 1
  ring

/-- The two non-equivariantly reconstructed odds retain the same critical parity reservoir. -/
theorem routeNGammaSewnAdaptiveParityOdds_mul_eq_critical_sq
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnOutwardAdaptiveParityOdds t p *
        routeNGammaSewnInwardAdaptiveParityOdds t p =
      routeNGammaSewnCriticalSquarefreeParityOdds p ^ 2 := by
  unfold routeNGammaSewnOutwardAdaptiveParityOdds
    routeNGammaSewnInwardAdaptiveParityOdds
  have htwisted : routeNGammaSewnTwistedSquarefreeParityOdds t p ≠ 0 := by
    rw [routeNGammaSewnTwistedSquarefreeParityOdds_eq,
      routeNGammaSewnTwistedCriticalChannelMass]
    exact (Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _).ne'
  field_simp

theorem dyadicSquarefreeParityProbability_primeAdaptiveOdds
    (p : Nat.Primes) (u : ℝ) :
    dyadicSquarefreeParityProbability ((p : ℝ) ^ (u - 1)) (1 : Fin 2) =
      sourceHorizontalPrimeAdaptiveOccupation p u := by
  simp only [dyadicSquarefreeParityProbability, Fin.val_one, pow_one]
  unfold sourceHorizontalPrimeAdaptiveOccupation
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hpu : 0 < (p : ℝ) ^ u := Real.rpow_pos_of_pos hp _
  rw [Real.rpow_sub hp]
  field_simp
  rw [Real.rpow_one]

/-- Route N's critical/twisted squarefree parity pair reconstructs both adaptive reflection
orientations at grade `2|t|`, with no loss of the prime label. -/
theorem routeNGammaSewnAdaptiveParityProbabilities_eq
    (t : ℝ) (p : Nat.Primes) :
    dyadicSquarefreeParityProbability
          (routeNGammaSewnOutwardAdaptiveParityOdds t p) (1 : Fin 2) =
        sourceHorizontalPrimeAdaptiveOccupation p (2 * |t|) ∧
      dyadicSquarefreeParityProbability
          (routeNGammaSewnInwardAdaptiveParityOdds t p) (1 : Fin 2) =
        sourceHorizontalPrimeAdaptiveOccupation p (-(2 * |t|)) := by
  constructor
  · rw [routeNGammaSewnOutwardAdaptiveParityOdds_eq]
    exact dyadicSquarefreeParityProbability_primeAdaptiveOdds p (2 * |t|)
  · rw [routeNGammaSewnInwardAdaptiveParityOdds_eq]
    rw [show -2 * |t| - 1 = -(2 * |t|) - 1 by ring]
    exact dyadicSquarefreeParityProbability_primeAdaptiveOdds p (-(2 * |t|))

/-- Cofinal form: every nonnegative adaptive grade is the Route-N squarefree parity doublet at
half that grade.  This closes the scalar coefficient formula; source-law realization remains the
only missing transition. -/
theorem routeNGammaSewnAdaptiveParityProbabilities_eq_of_nonneg
    {u : ℝ} (hu : 0 ≤ u) (p : Nat.Primes) :
    dyadicSquarefreeParityProbability
          (routeNGammaSewnOutwardAdaptiveParityOdds (u / 2) p) (1 : Fin 2) =
        sourceHorizontalPrimeAdaptiveOccupation p u ∧
      dyadicSquarefreeParityProbability
          (routeNGammaSewnInwardAdaptiveParityOdds (u / 2) p) (1 : Fin 2) =
        sourceHorizontalPrimeAdaptiveOccupation p (-u) := by
  have habs : |u / 2| = u / 2 := abs_of_nonneg (by positivity)
  have htwo : 2 * (u / 2) = u := by ring
  simpa only [habs, htwo] using
    routeNGammaSewnAdaptiveParityProbabilities_eq (u / 2) p

/-! ## Variable-aperture contiguity -/

/-- Absolute continuity still forbids adaptive cofinal separation after varying postselection,
provided the forward admission mass has one uniform positive lower bound.  The hypotheses record
the two conditional-mass identities without requiring an implementation of conditional measures.
This is the exact receiver needed by equality fusion above. -/
theorem sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_uniformlyAdmittedContiguity
    {Ω : Type*} [MeasurableSpace Ω]
    (P R : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (p : Nat.Primes) {d t c : ℝ} (hd : 1 < d) (hc : 0 < c) (hPR : P ≪ R)
    (admitted success : ℕ → Set Ω)
    (hPconditional : ∀ n,
      (P (success n)).toReal =
        sourceHorizontalPrimeAdaptiveOccupation p (d ^ n * |t|) *
          (P (admitted n)).toReal)
    (hRconditional : ∀ n,
      (R (success n)).toReal =
        sourceHorizontalPrimeAdaptiveOccupation p (-(d ^ n * |t|)) *
          (R (admitted n)).toReal)
    (hPadmitted : ∀ n, c ≤ (P (admitted n)).toReal) :
    t = 0 := by
  by_contra ht
  have hplus := tendsto_sourceHorizontalPrimeAdaptiveOccupation_scale_one
    (p := p) hd ht
  have hminus := tendsto_sourceHorizontalPrimeAdaptiveOccupation_reflectedScale_zero
    (p := p) hd ht
  have hRbound (n : ℕ) :
      (R (success n)).toReal ≤
        sourceHorizontalPrimeAdaptiveOccupation p (-(d ^ n * |t|)) := by
    rw [hRconditional n]
    have hmass : (R (admitted n)).toReal ≤ 1 := by
      have hmono : R (admitted n) ≤ R Set.univ := measure_mono (subset_univ _)
      have hreal := ENNReal.toReal_mono (measure_ne_top R Set.univ) hmono
      simpa using hreal
    exact mul_le_of_le_one_right
      (sourceHorizontalPrimeAdaptiveOccupation_pos p _).le hmass
  have hRzeroReal : Tendsto (fun n => (R (success n)).toReal) atTop (𝓝 0) :=
    squeeze_zero (fun n => ENNReal.toReal_nonneg) hRbound hminus
  have hRzero : Tendsto (fun n => R (success n)) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal_zero_iff
      (fun n => measure_ne_top R (success n))).mp hRzeroReal
  have hPzero := tendsto_measure_zero_of_absolutelyContinuous_finite
    P R hPR hRzero
  have hPzeroReal : Tendsto (fun n => (P (success n)).toReal) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal_zero_iff
      (fun n => measure_ne_top P (success n))).mpr hPzero
  have hplusHalf : ∀ᶠ n : ℕ in atTop,
      1 / 2 < sourceHorizontalPrimeAdaptiveOccupation p (d ^ n * |t|) :=
    hplus (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hPsmall : ∀ᶠ n : ℕ in atTop, (P (success n)).toReal < c / 2 := by
    have hball := hPzeroReal (Metric.ball_mem_nhds (0 : ℝ) (by positivity : 0 < c / 2))
    filter_upwards [hball] with n hn
    change dist ((P (success n)).toReal) 0 < c / 2 at hn
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero,
      abs_of_nonneg ENNReal.toReal_nonneg] using hn
  rcases (hplusHalf.and hPsmall).exists with ⟨n, hnplus, hnsmall⟩
  rw [hPconditional n] at hnsmall
  nlinarith [hPadmitted n,
    sourceHorizontalPrimeAdaptiveOccupation_pos p (d ^ n * |t|)]

/-! ## Actual abelian source and Xi endpoint -/

/-- Concrete source handoff.  The scalar Route-N parity formula is fully discharged; the remaining
inputs are literal events on two fixed convergent abelian class laws and one uniform forward
admission bound. -/
theorem sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_abelianRouteNParityFusion
    (θP θR : AbelianZetaConvergentParameters)
    (p : Nat.Primes) {d t c : ℝ} (hd : 1 < d) (hc : 0 < c)
    (admitted success : ℕ → Set AbelianZetaGroupClass)
    (_hsub : ∀ n, success n ⊆ admitted n)
    (hPfusion : ∀ n,
      ((classLaw θP.toAbelianZetaParameters) (success n)).toReal =
        dyadicSquarefreeParityProbability
            (routeNGammaSewnOutwardAdaptiveParityOdds
              ((d ^ n * |t|) / 2) p) (1 : Fin 2) *
          ((classLaw θP.toAbelianZetaParameters) (admitted n)).toReal)
    (hRfusion : ∀ n,
      ((classLaw θR.toAbelianZetaParameters) (success n)).toReal =
        dyadicSquarefreeParityProbability
            (routeNGammaSewnInwardAdaptiveParityOdds
              ((d ^ n * |t|) / 2) p) (1 : Fin 2) *
          ((classLaw θR.toAbelianZetaParameters) (admitted n)).toReal)
    (hPadmitted : ∀ n,
      c ≤ ((classLaw θP.toAbelianZetaParameters) (admitted n)).toReal) :
    t = 0 := by
  apply sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_uniformlyAdmittedContiguity
    (classLaw θP.toAbelianZetaParameters)
    (classLaw θR.toAbelianZetaParameters) p hd hc
    (classLaw_absolutelyContinuous θR θP) admitted success
  · intro n
    rw [hPfusion n]
    have hu : 0 ≤ d ^ n * |t| := by positivity
    rw [(routeNGammaSewnAdaptiveParityProbabilities_eq_of_nonneg hu p).1]
  · intro n
    rw [hRfusion n]
    have hu : 0 ≤ d ^ n * |t| := by positivity
    rw [(routeNGammaSewnAdaptiveParityProbabilities_eq_of_nonneg hu p).2]
  · exact hPadmitted

/-- Multiplicity-resolved source certificate.  Unlike the earlier unconditioned adaptive
certificate, this exposes the concrete Route-N critical/twisted parity doublet and permits a
varying source relation, but requires its forward aperture to remain uniformly admitted. -/
structure SourceHorizontalXiRouteNParityFusionCertificate
    (q : XiZeroCopy) (p : Nat.Primes) (d : ℝ) where
  θP : AbelianZetaConvergentParameters
  θR : AbelianZetaConvergentParameters
  admitted : ℕ → Set AbelianZetaGroupClass
  success : ℕ → Set AbelianZetaGroupClass
  success_subset : ∀ n, success n ⊆ admitted n
  admissionFloor : ℝ
  admissionFloor_pos : 0 < admissionFloor
  map_P : ∀ n,
    ((classLaw θP.toAbelianZetaParameters) (success n)).toReal =
      dyadicSquarefreeParityProbability
          (routeNGammaSewnOutwardAdaptiveParityOdds
            ((d ^ n * |primeDepthBVWoldXiCenteredRate q.1|) / 2) p) (1 : Fin 2) *
        ((classLaw θP.toAbelianZetaParameters) (admitted n)).toReal
  map_R : ∀ n,
    ((classLaw θR.toAbelianZetaParameters) (success n)).toReal =
      dyadicSquarefreeParityProbability
          (routeNGammaSewnInwardAdaptiveParityOdds
            ((d ^ n * |primeDepthBVWoldXiCenteredRate q.1|) / 2) p) (1 : Fin 2) *
        ((classLaw θR.toAbelianZetaParameters) (admitted n)).toReal
  admitted_P : ∀ n,
    admissionFloor ≤
      ((classLaw θP.toAbelianZetaParameters) (admitted n)).toReal

theorem sourceHorizontalXi_re_eq_half_of_routeNParityFusionCertificate
    (q : XiZeroCopy) (p : Nat.Primes) {d : ℝ} (hd : 1 < d)
    (C : SourceHorizontalXiRouteNParityFusionCertificate q p d) :
    (q.1 : ℂ).re = 1 / 2 := by
  rw [← primeDepthBVWoldXiCenteredRate_eq_zero_iff]
  exact sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_abelianRouteNParityFusion
    C.θP C.θR p hd C.admissionFloor_pos C.admitted C.success
      C.success_subset C.map_P C.map_R C.admitted_P

/-- **Route-N/vacuum-fusion Frankenstein endpoint.**  Uniformly admitted realization of the
already source-derived critical/twisted parity doublet on fixed abelian class laws, for every
analytic multiplicity copy, proves RH. -/
theorem riemannHypothesis_of_sourceHorizontalXi_routeNParityFusionCertificates
    (hcert : ∀ q : XiZeroCopy,
      SourceHorizontalXiRouteNParityFusionCertificate
        q ⟨2, Nat.prime_two⟩ 2) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
  intro q
  exact sourceHorizontalXi_re_eq_half_of_routeNParityFusionCertificate
    (xiFirstZeroCopy q) ⟨2, Nat.prime_two⟩ (by norm_num)
      (hcert (xiFirstZeroCopy q))

end

end RHTower
