import GaloisForLFunctions.RHTower.SourceHorizontalWoldEulerGreenAnomaly
import GaloisForLFunctions.RHTower.GaussReciprocalCharacterAdmission

/-!
# Source-horizontal Wold–Gauss–Hodge virial bridge

The completed finite Route-T Wold prime-clock carrier is a literal prime-labelled sum and tends
to the existing inverse-Euler Green profile. Its Euler response is the hyperbolic virial shape in
Gauss Hodge mass. At actual Gauss depth one, the two prime coefficients differ by one explicit
positive gauge.

The bridge also closes a tempting false shortcut. Centered Wold polar work omits a strictly
positive inverse-Euler reserve away from zero, so Wold properness alone cannot replace the missing
arithmetic identity annihilating Hodge mass.
-/

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Finite prime-labelled completion before the cofinal prime-clock limit. -/
def sourceHorizontalWoldPrimeClockCompletedFinitePrimitive (N : ℕ) (u : ℝ) : ℝ :=
  sourceHorizontalWoldPrimeClockProfileSeries N u + Real.sinh u

/-- Finite coefficient-faithful response before the cofinal prime-clock limit. -/
def sourceHorizontalWoldPrimeClockCompletedFiniteResponse (N : ℕ) (u : ℝ) : ℝ :=
  ∑' k : ℕ, u ^ (2 * k) / (2 * k).factorial *
    sourceHorizontalWoldOrderedNormalizedMoment N (2 * k)

/-- Each finite completion is exactly the coefficient-faithful Wold prime sum. -/
theorem sourceHorizontalWoldPrimeClockCompletedFinitePrimitive_eq_primeSum
    (N : ℕ) (u : ℝ) :
    sourceHorizontalWoldPrimeClockCompletedFinitePrimitive N u =
      ∑ n ∈ Finset.range (N + 1),
        woldCoeff 1 (nthPrimeSubtype n) *
          (Real.sinh
              (u * xiMassNthPrimeLogHeight n / xiMassNthPrimeLogHeight N) /
            xiMassNthPrimeLogHeight n) := by
  rw [sourceHorizontalWoldPrimeClockCompletedFinitePrimitive,
    sourceHorizontalWoldPrimeClockProfileSeries_eq_finiteDeformation]
  ring

/-- Cofinal finite Wold sums converge to the inverse-Euler Green profile without relabelling. -/
theorem tendsto_sourceHorizontalWoldPrimeClockCompletedFinitePrimitive (u : ℝ) :
    Filter.Tendsto
      (fun N : ℕ => sourceHorizontalWoldPrimeClockCompletedFinitePrimitive N u)
      Filter.atTop (nhds (sourceHorizontalWoldEulerGreenProfile u)) := by
  have h := (tendsto_sourceHorizontalWoldPrimeClockProfileSeries u).add_const (Real.sinh u)
  simpa [sourceHorizontalWoldPrimeClockCompletedFinitePrimitive,
    sourceHorizontalWoldPrimeClockUniversalProfile_eq_eulerGreen_sub_sinh] using h

/-- Finite Wold responses converge to the actual derivative of the inverse-Euler Green profile. -/
theorem tendsto_sourceHorizontalWoldPrimeClockCompletedFiniteResponse (u : ℝ) :
    Filter.Tendsto
      (fun N : ℕ => sourceHorizontalWoldPrimeClockCompletedFiniteResponse N u)
      Filter.atTop (nhds (deriv sourceHorizontalWoldEulerGreenProfile u)) := by
  have hmass : Filter.Tendsto
      (fun N : ℕ => sourceHorizontalWoldOrderedNormalizedMoment N 0)
      Filter.atTop (nhds 1) := by
    simpa using tendsto_sourceHorizontalWoldOrderedNormalizedMoment 0
  have hmass_lt_two : ∀ᶠ N : ℕ in Filter.atTop,
      sourceHorizontalWoldOrderedNormalizedMoment N 0 < 2 :=
    hmass.eventually_lt_const (by norm_num)
  have hlimit : Filter.Tendsto
      (fun N : ℕ => sourceHorizontalWoldPrimeClockCompletedFiniteResponse N u)
      Filter.atTop (nhds (∑' k : ℕ,
        u ^ (2 * k) / (2 * k).factorial *
          (1 / (2 * k + 1 : ℕ) : ℝ))) := by
    unfold sourceHorizontalWoldPrimeClockCompletedFiniteResponse
    apply tendsto_tsum_of_dominated_convergence
        ((Real.hasSum_cosh |u|).summable.mul_left 2)
    · intro k
      exact tendsto_const_nhds.mul
        (tendsto_sourceHorizontalWoldOrderedNormalizedMoment (2 * k))
    · filter_upwards [hmass_lt_two] with N hN k
      have hk0 : 0 ≤ sourceHorizontalWoldOrderedNormalizedMoment N (2 * k) :=
        sourceHorizontalWoldOrderedNormalizedMoment_nonneg N (2 * k)
      have hk2 : sourceHorizontalWoldOrderedNormalizedMoment N (2 * k) ≤ 2 :=
        (sourceHorizontalWoldOrderedNormalizedMoment_le_mass N (2 * k)).trans hN.le
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow]
      simp only [Nat.cast_nonneg, abs_of_nonneg, abs_of_nonneg hk0]
      calc
        |u| ^ (2 * k) / ↑(2 * k).factorial *
            sourceHorizontalWoldOrderedNormalizedMoment N (2 * k) ≤
          |u| ^ (2 * k) / ↑(2 * k).factorial * 2 :=
            mul_le_mul_of_nonneg_left hk2 (by positivity)
        _ = 2 * (|u| ^ (2 * k) / ↑(2 * k).factorial) := by ring
  rw [(hasDerivAt_sourceHorizontalWoldEulerGreenProfile u).deriv]
  have hseries :
      (∑' k : ℕ, u ^ (2 * k) / (2 * k).factorial *
        (1 / (2 * k + 1 : ℕ) : ℝ)) =
      ∑' k : ℕ, u ^ (2 * k) / (2 * k + 1).factorial := by
    apply tsum_congr
    intro k
    rw [show 2 * k + 1 = (2 * k) + 1 by omega, Nat.factorial_succ]
    push_cast
    field_simp
  rw [hseries] at hlimit
  exact hlimit

private theorem summable_eulerGreenProfile_term (u : ℝ) :
    Summable (fun k : ℕ =>
      u ^ (2 * k + 1) / (2 * k + 1).factorial *
        (1 / (2 * k + 1 : ℕ) : ℝ)) := by
  refine Summable.of_norm_bounded (Real.hasSum_sinh |u|).summable ?_
  intro k
  have hden : (1 : ℝ) ≤ (2 * k + 1 : ℕ) := by
    exact_mod_cast (show 1 ≤ 2 * k + 1 by omega)
  have hden0 : (0 : ℝ) < (2 * k + 1 : ℕ) := by positivity
  have hinv0 : 0 ≤ (1 / (2 * k + 1 : ℕ) : ℝ) := by positivity
  have hinv1 : (1 / (2 * k + 1 : ℕ) : ℝ) ≤ 1 :=
    (div_le_one hden0).2 hden
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow]
  simp only [Nat.cast_nonneg, abs_of_nonneg, abs_of_nonneg hinv0]
  exact mul_le_of_le_one_right (by positivity) hinv1

private theorem eulerGreenProfile_mul_term_nonneg (u : ℝ) (k : ℕ) :
    0 ≤ u * (u ^ (2 * k + 1) / (2 * k + 1).factorial *
      (1 / (2 * k + 1 : ℕ) : ℝ)) := by
  calc
    u * (u ^ (2 * k + 1) / (2 * k + 1).factorial *
        (1 / (2 * k + 1 : ℕ) : ℝ)) =
      u ^ (2 * k + 2) / (2 * k + 1).factorial *
        (1 / (2 * k + 1 : ℕ) : ℝ) := by
          rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, pow_succ]
          ring
    _ ≥ 0 := by
      have heven : Even (2 * k + 2) := ⟨k + 1, by omega⟩
      exact mul_nonneg
        (div_nonneg (heven.pow_nonneg u) (by positivity))
        (by positivity)

/-- The inverse-Euler reserve is strictly positive after polar pairing away from zero. -/
theorem sourceHorizontalWoldEulerGreenProfile_mul_pos_iff (u : ℝ) :
    0 < u * sourceHorizontalWoldEulerGreenProfile u ↔ u ≠ 0 := by
  constructor
  · intro h hu
    simp [hu] at h
  · intro hu
    rw [sourceHorizontalWoldEulerGreenProfile, ← tsum_mul_left]
    have hsum : Summable (fun k : ℕ =>
        u * (u ^ (2 * k + 1) / (2 * k + 1).factorial *
          (1 / (2 * k + 1 : ℕ) : ℝ))) :=
      (summable_eulerGreenProfile_term u).mul_left u
    apply hsum.tsum_pos (eulerGreenProfile_mul_term_nonneg u) 0
    norm_num
    exact hu

/-- Euler differentiation of the Wold Green profile is the Gauss hyperbolic virial shape. -/
theorem sourceHorizontalWoldEulerGreenProfile_euler (u : ℝ) :
    u ^ (2 : ℕ) * deriv sourceHorizontalWoldEulerGreenProfile u = u * Real.sinh u := by
  have h := sourceHorizontalWoldEulerGreenProfile_mul_deriv u
  calc
    u ^ (2 : ℕ) * deriv sourceHorizontalWoldEulerGreenProfile u =
        u * (u * deriv sourceHorizontalWoldEulerGreenProfile u) := by ring
    _ = u * Real.sinh u := by rw [h]

/-- The completed Euler response has exactly the central radical. -/
theorem sourceHorizontalWoldEulerGreenProfile_euler_eq_zero_iff (u : ℝ) :
    u ^ (2 : ℕ) * deriv sourceHorizontalWoldEulerGreenProfile u = 0 ↔ u = 0 := by
  rw [sourceHorizontalWoldEulerGreenProfile_euler]
  simp

/-- Exact decomposition of completed virial into centered polar work and Green reserve. -/
theorem sourceHorizontalWoldPrimeClockPolarRateWork_add_eulerGreenReserve (u : ℝ) :
    sourceHorizontalWoldPrimeClockPolarRateWork u +
        Real.log 2 / 2 * u * sourceHorizontalWoldEulerGreenProfile u =
      Real.log 2 / 2 * u * Real.sinh u := by
  rw [sourceHorizontalWoldPrimeClockPolarRateWork_eq_eulerGreenDefect]
  ring

/-- Centered Wold polar work is strictly smaller than completed virial off the central rate. -/
theorem sourceHorizontalWoldPrimeClockPolarRateWork_lt_eulerGreenVirial_iff (u : ℝ) :
    sourceHorizontalWoldPrimeClockPolarRateWork u <
        Real.log 2 / 2 * u * Real.sinh u ↔ u ≠ 0 := by
  have hlog : 0 < Real.log 2 / 2 := by positivity
  rw [← sourceHorizontalWoldPrimeClockPolarRateWork_add_eulerGreenReserve]
  simp only [lt_add_iff_pos_right]
  rw [mul_assoc]
  exact (mul_pos_iff_of_pos_left hlog).trans
    (sourceHorizontalWoldEulerGreenProfile_mul_pos_iff u)

/-- Literal Gauss Hodge mass is the Euler response of the completed Wold Green carrier. -/
theorem gaussHodgeMassCurrent_eq_woldEulerGreenResponse
    (m : ℕ) (q : XiZeroCopy) (p : Nat.Primes) :
    gaussHodgeMassCurrent m q p =
      2 * gaussReciprocalCharacterWeight m p *
        (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate q.1) ^ (2 : ℕ) *
          deriv sourceHorizontalWoldEulerGreenProfile
            (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate q.1) := by
  rw [gaussHodgeMassCurrent_eq_reciprocalCharacterVirial,
    reciprocalCharacterVirialCurrent]
  let u : ℝ := Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate q.1
  change 2 * gaussReciprocalCharacterWeight m p * u * Real.sinh u =
    2 * gaussReciprocalCharacterWeight m p * u ^ (2 : ℕ) *
      deriv sourceHorizontalWoldEulerGreenProfile u
  calc
    2 * gaussReciprocalCharacterWeight m p * u * Real.sinh u =
        2 * gaussReciprocalCharacterWeight m p * (u * Real.sinh u) := by ring
    _ = 2 * gaussReciprocalCharacterWeight m p *
        (u ^ (2 : ℕ) * deriv sourceHorizontalWoldEulerGreenProfile u) := by
          rw [sourceHorizontalWoldEulerGreenProfile_euler]
    _ = 2 * gaussReciprocalCharacterWeight m p * u ^ (2 : ℕ) *
        deriv sourceHorizontalWoldEulerGreenProfile u := by ring

/-- Exact depth-one coefficient gauge between Gauss residue and Wold source packets. -/
def gaussWoldDepthOneCoefficientGauge (p : Nat.Primes) : ℝ :=
  Real.log 2 * ((p : ℝ) - 1) * (p : ℝ) ^ (3 : ℕ) /
    (((p : ℝ) + 1) ^ (2 : ℕ) * Real.log (p : ℝ) ^ (2 : ℕ))

/-- The depth-one Gauss-to-Wold coefficient gauge is positive at every prime label. -/
theorem gaussWoldDepthOneCoefficientGauge_pos (p : Nat.Primes) :
    0 < gaussWoldDepthOneCoefficientGauge p := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_trans zero_lt_one hp
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [gaussWoldDepthOneCoefficientGauge]
  exact div_pos
    (mul_pos (mul_pos hlog2 (sub_pos.mpr hp)) (pow_pos hp0 _))
    (mul_pos (pow_pos (by linarith) _) (pow_pos hlogp _))

/-- The exact coefficient gauge dominates a fixed positive multiple of the prime label. -/
theorem gaussWoldDepthOneCoefficientGauge_linear_lower (p : Nat.Primes) :
    Real.log 2 / 18 * (p : ℝ) ≤ gaussWoldDepthOneCoefficientGauge p := by
  let P : ℝ := p
  have hp2 : (2 : ℝ) ≤ P := by
    dsimp [P]
    exact_mod_cast p.prop.two_le
  have hp0 : 0 < P := lt_of_lt_of_le (by norm_num) hp2
  have hp1 : 1 < P := lt_of_lt_of_le one_lt_two hp2
  have hlog0 : 0 < Real.log P := Real.log_pos hp1
  have hsqrt0 : 0 ≤ Real.sqrt P := Real.sqrt_nonneg P
  have hsqrtSq : (Real.sqrt P) ^ (2 : ℕ) = P := Real.sq_sqrt hp0.le
  have hs : Real.log (Real.sqrt P) ≤ Real.sqrt P - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hp0)
  have hlog : Real.log P ≤ 2 * Real.sqrt P := by
    rw [Real.log_sqrt hp0.le] at hs
    linarith
  have hlogsq : Real.log P ^ (2 : ℕ) ≤ 4 * P := by
    have hprod : 0 ≤ (2 * Real.sqrt P - Real.log P) *
        (2 * Real.sqrt P + Real.log P) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith
  have hplus : P + 1 ≤ 3 / 2 * P := by linarith
  have hplusSq : (P + 1) ^ (2 : ℕ) ≤ (3 / 2 * P) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (by linarith) hplus 2
  have hden : (P + 1) ^ (2 : ℕ) * Real.log P ^ (2 : ℕ) ≤ 9 * P ^ (3 : ℕ) := by
    calc
      (P + 1) ^ (2 : ℕ) * Real.log P ^ (2 : ℕ) ≤ (3 / 2 * P) ^ (2 : ℕ) * (4 * P) :=
        mul_le_mul hplusSq hlogsq (sq_nonneg _) (by positivity)
      _ = 9 * P ^ (3 : ℕ) := by ring
  have hnum : P / 2 * P ^ (3 : ℕ) ≤ (P - 1) * P ^ (3 : ℕ) := by
    exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hp0.le 3)
  have hden0 : 0 < (P + 1) ^ (2 : ℕ) * Real.log P ^ (2 : ℕ) := by positivity
  rw [gaussWoldDepthOneCoefficientGauge]
  change Real.log 2 / 18 * P ≤
    Real.log 2 * (P - 1) * P ^ (3 : ℕ) / ((P + 1) ^ (2 : ℕ) * Real.log P ^ (2 : ℕ))
  rw [le_div_iff₀ hden0]
  calc
    Real.log 2 / 18 * P * ((P + 1) ^ (2 : ℕ) * Real.log P ^ (2 : ℕ)) ≤
        Real.log 2 / 18 * P * (9 * P ^ (3 : ℕ)) :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    _ = Real.log 2 * (P / 2 * P ^ (3 : ℕ)) := by ring
    _ ≤ Real.log 2 * ((P - 1) * P ^ (3 : ℕ)) :=
      mul_le_mul_of_nonneg_left hnum (Real.log_pos one_lt_two).le
    _ = Real.log 2 * (P - 1) * P ^ (3 : ℕ) := by ring

/-- Along ordered primes the exact Gauss-to-Wold coefficient gauge diverges. -/
theorem tendsto_gaussWoldDepthOneCoefficientGauge_nthPrime :
    Filter.Tendsto (fun n : ℕ =>
      gaussWoldDepthOneCoefficientGauge (nthPrimeSubtype n))
      Filter.atTop Filter.atTop := by
  have hp : Filter.Tendsto (fun n : ℕ => (nthPrimeSubtype n : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp nthPrimeSubtype_strictMono.tendsto_atTop
  have hscaled : Filter.Tendsto
      (fun n : ℕ => Real.log 2 / 18 * (nthPrimeSubtype n : ℝ))
      Filter.atTop Filter.atTop :=
    hp.const_mul_atTop (by positivity)
  exact Filter.tendsto_atTop_mono
    (fun n => gaussWoldDepthOneCoefficientGauge_linear_lower (nthPrimeSubtype n)) hscaled

/-- Actual depth-one Gauss and Wold coefficients differ by the explicit positive gauge. -/
theorem gaussReciprocalCharacterWeight_one_eq_wold_gauge (p : Nat.Primes) :
    gaussReciprocalCharacterWeight 1 p =
      gaussWoldDepthOneCoefficientGauge p *
        (woldCoeff 1 p / Real.log (p : ℝ)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.prop.one_lt)).ne'
  rw [gaussReciprocalCharacterWeight, gaussChannelResidueCurrent,
    GaloisForLFunctions.RHTower.gaussChannelResidue,
    primeActivationOccupancyFisherDensity_eq,
    gaussWoldDepthOneCoefficientGauge, woldCoeff]
  norm_num
  field_simp [hp0, hlog]

/-- Finite two-scale Wold source response carrying one literal Gauss prime label. -/
def gaussWoldFiniteSourceVirialResponse
    (N m : ℕ) (p : Nat.Primes) (t : ℝ) : ℝ :=
  2 * gaussReciprocalCharacterWeight m p *
    (Real.log (p : ℝ) * t) ^ (2 : ℕ) *
      sourceHorizontalWoldPrimeClockCompletedFiniteResponse N
        (Real.log (p : ℝ) * t)

/-- The finite prime-moment source response converges labelwise to literal Gauss Hodge mass. -/
theorem tendsto_gaussWoldFiniteSourceVirialResponse
    (m : ℕ) (q : XiZeroCopy) (p : Nat.Primes) :
    Filter.Tendsto
      (fun N : ℕ => gaussWoldFiniteSourceVirialResponse N m p
        (primeDepthBVWoldXiCenteredRate q.1))
      Filter.atTop (nhds (gaussHodgeMassCurrent m q p)) := by
  rw [gaussHodgeMassCurrent_eq_woldEulerGreenResponse]
  unfold gaussWoldFiniteSourceVirialResponse
  exact tendsto_const_nhds.mul
    (tendsto_sourceHorizontalWoldPrimeClockCompletedFiniteResponse
      (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate q.1))

/-- At depth one, every finite response retains the exact unbounded Gauss-to-Wold gauge. -/
theorem gaussWoldFiniteSourceVirialResponse_one_eq_gaugedWold
    (N : ℕ) (p : Nat.Primes) (t : ℝ) :
    gaussWoldFiniteSourceVirialResponse N 1 p t =
      2 * gaussWoldDepthOneCoefficientGauge p *
        (woldCoeff 1 p / Real.log (p : ℝ)) *
        (Real.log (p : ℝ) * t) ^ (2 : ℕ) *
          sourceHorizontalWoldPrimeClockCompletedFiniteResponse N
            (Real.log (p : ℝ) * t) := by
  rw [gaussWoldFiniteSourceVirialResponse,
    gaussReciprocalCharacterWeight_one_eq_wold_gauge]
  ring

end

end RHTower
