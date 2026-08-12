import GaloisForLFunctions.RHTower.SourceHorizontalAdaptiveFisherChiralitySelection
import GaloisForLFunctions.RHTower.SourceHorizontalWoldPrimeClockCubic

/-!
# Adaptive information chirality–Wold cubic bridge

The directed Bernoulli KL chirality selected by adaptive source occupation and the Route-T Wold
prime deformation have exactly the same third neutral jet, up to one explicit primewise gauge.
The gauge lies uniformly in `[1, 32]`; this transport is coefficient-faithful and cannot compactly
smooth the Wold anomaly.

This identifies two previously separate obstructions: source-horizontal information orientation
and the Wold residual cubic are the same local signed coefficient class.  It does not assert that
their global arithmetic aggregate vanishes.
-/

open Real Set MeasureTheory InformationTheory ProbabilityTheory

namespace RHTower

open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open Filter Topology

noncomputable section

/-- First jet of centered directed Bernoulli KL chirality. -/
def sourceHorizontalCenteredBernoulliKLChiralityFirstJet (c s : ℝ) : ℝ :=
  2 * s * (sourceHorizontalFermiVariance (c + s) -
    sourceHorizontalFermiVariance (c - s))

/-- First jet of the Bernoulli Fisher variance. -/
def sourceHorizontalFermiVarianceFirstJet (x : ℝ) : ℝ :=
  sourceHorizontalFermiVariance x * (1 - 2 * Real.sigmoid x)

/-- Second jet of centered directed Bernoulli KL chirality. -/
def sourceHorizontalCenteredBernoulliKLChiralitySecondJet (c s : ℝ) : ℝ :=
  2 * (sourceHorizontalFermiVariance (c + s) -
    sourceHorizontalFermiVariance (c - s)) +
  2 * s * (sourceHorizontalFermiVarianceFirstJet (c + s) +
    sourceHorizontalFermiVarianceFirstJet (c - s))

theorem sourceHorizontalDeriv_centeredBernoulliKLChirality (c : ℝ) :
    deriv (sourceHorizontalCenteredBernoulliKLChirality c) =
      sourceHorizontalCenteredBernoulliKLChiralityFirstJet c := by
  funext s
  exact (sourceHorizontalHasDerivAt_centeredBernoulliKLChirality c s).deriv

theorem sourceHorizontalHasDerivAt_centeredBernoulliKLChiralityFirstJet (c s : ℝ) :
    HasDerivAt (sourceHorizontalCenteredBernoulliKLChiralityFirstJet c)
      (sourceHorizontalCenteredBernoulliKLChiralitySecondJet c s) s := by
  have hp := (sourceHorizontalHasDerivAt_fermiVariance (c + s)).comp s
    ((hasDerivAt_const s c).add (hasDerivAt_id s))
  have hm := (sourceHorizontalHasDerivAt_fermiVariance (c - s)).comp s
    ((hasDerivAt_const s c).sub (hasDerivAt_id s))
  have h := ((hasDerivAt_id s).const_mul 2).mul (hp.sub hm)
  convert h using 1 <;> try rfl
  simp only [sourceHorizontalCenteredBernoulliKLChiralitySecondJet,
    sourceHorizontalFermiVarianceFirstJet, Function.comp_apply, Pi.sub_apply, id_eq]
  ring

theorem sourceHorizontalDeriv_centeredBernoulliKLChiralityFirstJet (c : ℝ) :
    deriv (sourceHorizontalCenteredBernoulliKLChiralityFirstJet c) =
      sourceHorizontalCenteredBernoulliKLChiralitySecondJet c := by
  funext s
  exact (sourceHorizontalHasDerivAt_centeredBernoulliKLChiralityFirstJet c s).deriv

theorem sourceHorizontalHasDerivAt_centeredBernoulliKLChiralitySecondJet_zero (c : ℝ) :
    HasDerivAt (sourceHorizontalCenteredBernoulliKLChiralitySecondJet c)
      (8 * sourceHorizontalFermiVarianceFirstJet c) 0 := by
  have hp := (sourceHorizontalHasDerivAt_fermiVariance (c + 0)).comp 0
    ((hasDerivAt_const 0 c).add (hasDerivAt_id 0))
  have hm := (sourceHorizontalHasDerivAt_fermiVariance (c - 0)).comp 0
    ((hasDerivAt_const 0 c).sub (hasDerivAt_id 0))
  have hfirst := (hp.sub hm).const_mul 2
  have hwp : DifferentiableAt ℝ
      (fun s : ℝ => sourceHorizontalFermiVarianceFirstJet (c + s)) 0 := by
    unfold sourceHorizontalFermiVarianceFirstJet
    have hs := (Real.hasDerivAt_sigmoid (c + 0)).comp 0
      ((hasDerivAt_const 0 c).add (hasDerivAt_id 0))
    exact hp.differentiableAt.mul
      ((differentiableAt_const (c := (1 : ℝ))).sub (hs.differentiableAt.const_mul 2))
  have hwm : DifferentiableAt ℝ
      (fun s : ℝ => sourceHorizontalFermiVarianceFirstJet (c - s)) 0 := by
    unfold sourceHorizontalFermiVarianceFirstJet
    have hs := (Real.hasDerivAt_sigmoid (c - 0)).comp 0
      ((hasDerivAt_const 0 c).sub (hasDerivAt_id 0))
    exact hm.differentiableAt.mul
      ((differentiableAt_const (c := (1 : ℝ))).sub (hs.differentiableAt.const_mul 2))
  have hsecond := ((hasDerivAt_id (𝕜 := ℝ) 0).const_mul 2).mul
    (hwp.hasDerivAt.add hwm.hasDerivAt)
  have h := hfirst.add hsecond
  unfold sourceHorizontalCenteredBernoulliKLChiralitySecondJet
  convert h using 1 <;> try rfl
  simp only [sourceHorizontalFermiVarianceFirstJet, Pi.add_apply, id_eq]
  ring

/-- Universal third neutral jet of centered directed Bernoulli KL chirality. -/
theorem iteratedDeriv_sourceHorizontalCenteredBernoulliKLChirality_three_zero (c : ℝ) :
    iteratedDeriv 3 (sourceHorizontalCenteredBernoulliKLChirality c) 0 =
      8 * sourceHorizontalFermiVarianceFirstJet c := by
  rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ,
    show 2 = 1 + 1 by norm_num, iteratedDeriv_succ,
    show 1 = 0 + 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_zero, sourceHorizontalDeriv_centeredBernoulliKLChirality,
    sourceHorizontalDeriv_centeredBernoulliKLChiralityFirstJet]
  exact (sourceHorizontalHasDerivAt_centeredBernoulliKLChiralitySecondJet_zero c).deriv

/-- Adaptive prime chirality has its first nonzero neutral information jet at cubic order. -/
theorem iteratedDeriv_sourceHorizontalPrimeAdaptiveKLChirality_three_zero
    (p : Nat.Primes) :
    iteratedDeriv 3 (sourceHorizontalPrimeAdaptiveKLChirality p) 0 =
      8 * sourceHorizontalFermiVarianceFirstJet (-Real.log (p : ℝ)) *
        Real.log (p : ℝ) ^ 3 := by
  have hfun : sourceHorizontalPrimeAdaptiveKLChirality p =
      fun t => sourceHorizontalCenteredBernoulliKLChirality
        (-Real.log (p : ℝ)) (t * Real.log (p : ℝ)) := by
    funext t
    exact sourceHorizontalPrimeAdaptiveKLChirality_eq_centered p t
  rw [hfun]
  let c := -Real.log (p : ℝ)
  let L := Real.log (p : ℝ)
  have hinner (t : ℝ) : HasDerivAt (fun u : ℝ => u * L) L t := by
    simpa using (hasDerivAt_id (𝕜 := ℝ) t).mul_const L
  have hfirst : deriv (fun t : ℝ =>
      sourceHorizontalCenteredBernoulliKLChirality c (t * L)) =
      fun t => sourceHorizontalCenteredBernoulliKLChiralityFirstJet c (t * L) * L := by
    funext t
    exact ((sourceHorizontalHasDerivAt_centeredBernoulliKLChirality c (t * L)).comp t
      (hinner t)).deriv
  have hsecond : deriv (fun t : ℝ =>
      sourceHorizontalCenteredBernoulliKLChiralityFirstJet c (t * L) * L) =
      fun t => sourceHorizontalCenteredBernoulliKLChiralitySecondJet c (t * L) * L ^ 2 := by
    funext t
    have h := ((sourceHorizontalHasDerivAt_centeredBernoulliKLChiralityFirstJet c (t * L)).comp
      t (hinner t)).mul_const L
    simpa only [Function.comp_apply, pow_two, mul_assoc] using h.deriv
  rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ,
    show 2 = 1 + 1 by norm_num, iteratedDeriv_succ,
    show 1 = 0 + 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_zero, hfirst, hsecond]
  have hD2 : HasDerivAt (sourceHorizontalCenteredBernoulliKLChiralitySecondJet c)
      (8 * sourceHorizontalFermiVarianceFirstJet c) (0 * L) := by
    simpa using sourceHorizontalHasDerivAt_centeredBernoulliKLChiralitySecondJet_zero c
  have hthird := (hD2.comp 0 (hinner 0)).mul_const (L ^ 2)
  convert hthird.deriv using 1
  all_goals simp [c, L]
  ring

theorem sourceHorizontalSigmoid_neg_log_prime (p : Nat.Primes) :
    Real.sigmoid (-Real.log (p : ℝ)) = 1 / ((p : ℝ) + 1) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rw [sourceHorizontalSigmoid_eq_exp_div, Real.exp_neg, Real.exp_log hp]
  field_simp [hp.ne']
  ring

theorem sourceHorizontalFermiVarianceFirstJet_neg_log_prime (p : Nat.Primes) :
    sourceHorizontalFermiVarianceFirstJet (-Real.log (p : ℝ)) =
      (p : ℝ) * ((p : ℝ) - 1) / ((p : ℝ) + 1) ^ 3 := by
  rw [sourceHorizontalFermiVarianceFirstJet, sourceHorizontalFermiVariance,
    sourceHorizontalSigmoid_neg_log_prime]
  field_simp [show (p : ℝ) + 1 ≠ 0 by positivity]
  ring

/-- Closed primewise coefficient of the adaptive information-chirality cubic. -/
theorem iteratedDeriv_sourceHorizontalPrimeAdaptiveKLChirality_three_zero_eq
    (p : Nat.Primes) :
    iteratedDeriv 3 (sourceHorizontalPrimeAdaptiveKLChirality p) 0 =
      8 * ((p : ℝ) * ((p : ℝ) - 1) / ((p : ℝ) + 1) ^ 3) *
        Real.log (p : ℝ) ^ 3 := by
  rw [iteratedDeriv_sourceHorizontalPrimeAdaptiveKLChirality_three_zero,
    sourceHorizontalFermiVarianceFirstJet_neg_log_prime]

/-- Exact gauge identifying adaptive information chirality with the Wold cubic jet. -/
def sourceHorizontalAdaptiveChiralityWoldCubicGauge (p : Nat.Primes) : ℝ :=
  8 * (p : ℝ) ^ 5 / (((p : ℝ) - 1) ^ 2 * ((p : ℝ) + 1) ^ 3)

/-- Frankenstein bridge: adaptive information chirality and Route-T Wold residual are the same
third neutral prime jet through an explicit coefficient-faithful gauge. -/
theorem sourceHorizontalAdaptiveChiralityWoldCubicGauge_mul_woldCubic
    (p : Nat.Primes) :
    sourceHorizontalAdaptiveChiralityWoldCubicGauge p *
        iteratedDeriv 3 (sourceHorizontalWoldPrimeDeformation p) 0 =
      iteratedDeriv 3 (sourceHorizontalPrimeAdaptiveKLChirality p) 0 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    linarith [show (2 : ℝ) ≤ p by exact_mod_cast p.2.two_le]
  rw [iteratedDeriv_sourceHorizontalWoldPrimeDeformation_three,
    iteratedDeriv_sourceHorizontalPrimeAdaptiveKLChirality_three_zero_eq,
    sourceHorizontalAdaptiveChiralityWoldCubicGauge, woldCoeff]
  simp only [pow_one]
  field_simp [hp.ne', hp1]

/-- Bridge gauge is uniformly separated from zero and infinity. -/
theorem sourceHorizontalAdaptiveChiralityWoldCubicGauge_bounds (p : Nat.Primes) :
    1 ≤ sourceHorizontalAdaptiveChiralityWoldCubicGauge p ∧
      sourceHorizontalAdaptiveChiralityWoldCubicGauge p ≤ 32 := by
  let P : ℝ := p
  let a : ℝ := P / (P - 1)
  let b : ℝ := P / (P + 1)
  have hP2 : 2 ≤ P := by dsimp [P]; exact_mod_cast p.2.two_le
  have hPm1 : 0 < P - 1 := by linarith
  have hPp1 : 0 < P + 1 := by linarith
  have ha1 : 1 ≤ a := by
    dsimp [a]
    rw [le_div_iff₀ hPm1]
    linarith
  have ha2 : a ≤ 2 := by
    dsimp [a]
    rw [div_le_iff₀ hPm1]
    linarith
  have hbhalf : 1 / 2 ≤ b := by
    dsimp [b]
    rw [le_div_iff₀ hPp1]
    linarith
  have hb1 : b ≤ 1 := by
    dsimp [b]
    rw [div_le_iff₀ hPp1]
    linarith
  have haSqLower : 1 ≤ a ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (by linarith : 0 ≤ a + 1)]
  have haSqUpper : a ^ 2 ≤ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha2) (by linarith : 0 ≤ a + 2)]
  have hbCubeLower : 1 / 8 ≤ b ^ 3 := by
    have hquad : 0 ≤ b ^ 2 + b / 2 + 1 / 4 := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hbhalf) hquad]
  have hbCubeUpper : b ^ 3 ≤ 1 := by
    have hquad : 0 ≤ 1 + b + b ^ 2 := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hb1) hquad]
  have hproductLower : 1 / 8 ≤ a ^ 2 * b ^ 3 := by
    nlinarith [mul_le_mul haSqLower hbCubeLower (by norm_num : 0 ≤ (1 / 8 : ℝ))
      (by linarith : 0 ≤ a ^ 2)]
  have hproductUpper : a ^ 2 * b ^ 3 ≤ 4 := by
    nlinarith [mul_le_mul haSqUpper hbCubeUpper (by linarith : 0 ≤ b ^ 3)
      (by norm_num : 0 ≤ (4 : ℝ))]
  have hgauge : sourceHorizontalAdaptiveChiralityWoldCubicGauge p =
      8 * a ^ 2 * b ^ 3 := by
    dsimp [sourceHorizontalAdaptiveChiralityWoldCubicGauge, a, b, P]
    field_simp [hPm1.ne', hPp1.ne']
  rw [hgauge]
  constructor <;> nlinarith

/-- Adaptive information and Wold cubic jets have exactly the same zero fibre. -/
theorem sourceHorizontalAdaptiveChiralityCubic_eq_zero_iff_woldCubic_eq_zero
    (p : Nat.Primes) :
    iteratedDeriv 3 (sourceHorizontalPrimeAdaptiveKLChirality p) 0 = 0 ↔
      iteratedDeriv 3 (sourceHorizontalWoldPrimeDeformation p) 0 = 0 := by
  have hg : sourceHorizontalAdaptiveChiralityWoldCubicGauge p ≠ 0 := by
    have := (sourceHorizontalAdaptiveChiralityWoldCubicGauge_bounds p).1
    positivity
  constructor
  · intro ha
    have hm : sourceHorizontalAdaptiveChiralityWoldCubicGauge p *
        iteratedDeriv 3 (sourceHorizontalWoldPrimeDeformation p) 0 = 0 := by
      rw [sourceHorizontalAdaptiveChiralityWoldCubicGauge_mul_woldCubic, ha]
    exact (mul_eq_zero.mp hm).resolve_left hg
  · intro hw
    rw [← sourceHorizontalAdaptiveChiralityWoldCubicGauge_mul_woldCubic, hw, mul_zero]

/-- Quantitative coefficient faithfulness of the cubic bridge. -/
theorem sourceHorizontalWoldCubic_le_adaptiveChiralityCubic_le (p : Nat.Primes) :
    iteratedDeriv 3 (sourceHorizontalWoldPrimeDeformation p) 0 ≤
        iteratedDeriv 3 (sourceHorizontalPrimeAdaptiveKLChirality p) 0 ∧
      iteratedDeriv 3 (sourceHorizontalPrimeAdaptiveKLChirality p) 0 ≤
        32 * iteratedDeriv 3 (sourceHorizontalWoldPrimeDeformation p) 0 := by
  have hw : 0 ≤ iteratedDeriv 3 (sourceHorizontalWoldPrimeDeformation p) 0 := by
    rw [iteratedDeriv_sourceHorizontalWoldPrimeDeformation_three]
    exact mul_nonneg (woldCoeff_nonneg 1 p) (sq_nonneg _)
  rw [← sourceHorizontalAdaptiveChiralityWoldCubicGauge_mul_woldCubic]
  constructor
  · simpa using mul_le_mul_of_nonneg_right
      (sourceHorizontalAdaptiveChiralityWoldCubicGauge_bounds p).1 hw
  · exact mul_le_mul_of_nonneg_right
      (sourceHorizontalAdaptiveChiralityWoldCubicGauge_bounds p).2 hw

theorem sourceHorizontalAdaptiveChiralityWoldCubicGauge_inv_mul_cubic
    (p : Nat.Primes) :
    (sourceHorizontalAdaptiveChiralityWoldCubicGauge p)⁻¹ *
        iteratedDeriv 3 (sourceHorizontalPrimeAdaptiveKLChirality p) 0 =
      iteratedDeriv 3 (sourceHorizontalWoldPrimeDeformation p) 0 := by
  have hg : sourceHorizontalAdaptiveChiralityWoldCubicGauge p ≠ 0 := by
    have := (sourceHorizontalAdaptiveChiralityWoldCubicGauge_bounds p).1
    positivity
  rw [← sourceHorizontalAdaptiveChiralityWoldCubicGauge_mul_woldCubic]
  field_simp [hg]

/-- Finite prime-labelled adaptive information moment whose coefficients are transported without
loss to the natural Route-T cubic moment. -/
def sourceHorizontalAdaptiveChiralityNaturalCubicMoment (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
    (sourceHorizontalAdaptiveChiralityWoldCubicGauge (nthPrimeSubtype n))⁻¹ *
      iteratedDeriv 3
        (sourceHorizontalPrimeAdaptiveKLChirality (nthPrimeSubtype n)) 0

theorem sourceHorizontalAdaptiveChiralityNaturalCubicMoment_eq_wold
    (N : ℕ) :
    sourceHorizontalAdaptiveChiralityNaturalCubicMoment N =
      sourceHorizontalWoldNaturalCubicMoment (nthPrimeSubtype N : ℕ) := by
  classical
  rw [sourceHorizontalAdaptiveChiralityNaturalCubicMoment,
    sourceHorizontalWoldNaturalCubicMoment_nthPrime_eq_ordered]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [sourceHorizontalAdaptiveChiralityWoldCubicGauge_inv_mul_cubic,
    iteratedDeriv_sourceHorizontalWoldPrimeDeformation_three,
    xiMassNthPrimeLogHeight]

/-- Adaptive-information presentation of the complete Route-T residual cubic coefficient. -/
def sourceHorizontalAdaptiveChiralityResidualCubicCoefficient (N : ℕ) : ℝ :=
  sourceHorizontalAdaptiveChiralityNaturalCubicMoment N -
    xiMassNthPrimeLogHeight N ^ 3

theorem sourceHorizontalAdaptiveChiralityResidualCubicCoefficient_eq_wold
    (N : ℕ) :
    sourceHorizontalAdaptiveChiralityResidualCubicCoefficient N =
      sourceHorizontalWoldResidualPrimitiveCubicCoefficient N := by
  rw [sourceHorizontalAdaptiveChiralityResidualCubicCoefficient,
    sourceHorizontalAdaptiveChiralityNaturalCubicMoment_eq_wold,
    sourceHorizontalWoldResidualPrimitiveCubicCoefficient]

/-- Adaptive directed-information form of Route-T's universal `-2/3` cubic horizon anomaly. -/
theorem tendsto_sourceHorizontalAdaptiveChiralityResidualCubicCoefficient_normalized :
    Tendsto (fun N : ℕ =>
      sourceHorizontalAdaptiveChiralityResidualCubicCoefficient N /
        xiMassNthPrimeLogHeight N ^ 3)
      atTop (𝓝 (-2 / 3 : ℝ)) := by
  simpa only [sourceHorizontalAdaptiveChiralityResidualCubicCoefficient_eq_wold] using
    tendsto_sourceHorizontalWoldResidualPrimitiveCubicCoefficient_normalized

/-- Multiplicity-labelled Xi response written entirely through adaptive information cubic jets. -/
def sourceZeroHorizontalAdaptiveChiralityPrimeClockCubicResponse
    (q : XiZeroCopy) (N : ℕ) : ℝ :=
  primeDepthBVWoldXiCenteredRate q.1 ^ 3 *
    (sourceHorizontalAdaptiveChiralityResidualCubicCoefficient N /
      xiMassNthPrimeLogHeight N ^ 3)

theorem sourceZeroHorizontalAdaptiveChiralityPrimeClockCubicResponse_eq_wold
    (q : XiZeroCopy) (N : ℕ) :
    sourceZeroHorizontalAdaptiveChiralityPrimeClockCubicResponse q N =
      sourceZeroHorizontalWoldPrimeClockCubicResponse q N := by
  rw [sourceZeroHorizontalAdaptiveChiralityPrimeClockCubicResponse,
    sourceZeroHorizontalWoldPrimeClockCubicResponse,
    sourceHorizontalAdaptiveChiralityResidualCubicCoefficient_eq_wold]

@[simp] theorem sourceZeroHorizontalAdaptiveChiralityPrimeClockCubicResponse_reflection
    (q : XiZeroCopy) (N : ℕ) :
    sourceZeroHorizontalAdaptiveChiralityPrimeClockCubicResponse
        (xiZeroCopyLineConjEquiv q) N =
      -sourceZeroHorizontalAdaptiveChiralityPrimeClockCubicResponse q N := by
  rw [sourceZeroHorizontalAdaptiveChiralityPrimeClockCubicResponse_eq_wold,
    sourceZeroHorizontalAdaptiveChiralityPrimeClockCubicResponse_eq_wold,
    sourceZeroHorizontalWoldPrimeClockCubicResponse_reflection]

theorem tendsto_sourceZeroHorizontalAdaptiveChiralityPrimeClockCubicResponse
    (q : XiZeroCopy) :
    Tendsto (sourceZeroHorizontalAdaptiveChiralityPrimeClockCubicResponse q) atTop
      (𝓝 ((-2 / 3 : ℝ) * primeDepthBVWoldXiCenteredRate q.1 ^ 3)) := by
  have heq : sourceZeroHorizontalAdaptiveChiralityPrimeClockCubicResponse q =
      sourceZeroHorizontalWoldPrimeClockCubicResponse q := by
    funext N
    exact sourceZeroHorizontalAdaptiveChiralityPrimeClockCubicResponse_eq_wold q N
  rw [heq]
  exact tendsto_sourceZeroHorizontalWoldPrimeClockCubicResponse q

/-- Adaptive-information cubic horizon limit vanishes exactly on the critical line. -/
theorem sourceZeroHorizontalAdaptiveChiralityPrimeClockCubicLimit_eq_zero_iff
    (q : XiZeroCopy) :
    (-2 / 3 : ℝ) * primeDepthBVWoldXiCenteredRate q.1 ^ 3 = 0 ↔
      (q.1 : ℂ).re = 1 / 2 :=
  sourceZeroHorizontalWoldPrimeClockCubicLimit_eq_zero_iff q

end
end RHTower
