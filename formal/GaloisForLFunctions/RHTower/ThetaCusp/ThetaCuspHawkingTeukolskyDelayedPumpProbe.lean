import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingAIMECrossBranchTeukolskyResidue
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTeukolskySingleSectorFrequencyNoGo
import GaloisForLFunctions.HTGeometry.MonomialLaplaceComplex
import GaloisForLFunctions.HTGeometry.SchwartzWeightedHolder
import GaloisForLFunctions.HTGeometry.PolyExpDecayLimit

/-!
# Delayed local Teukolsky source exclusion

A nonconstant local monomial in one fundamental Birmingham--Mokhtari pump and its real-field
partner acquires a strictly damped advanced-time translation character. Finite sums remain
transient even after polynomial factors from resonant Jordan propagation. They cannot cancel the
delay-independent cross-branch AIME numerator. Stationary completion modes and infinite threshold
spectra are outside this finite-local statement.
-/

open Complex Real Set Filter Topology MeasureTheory

namespace RHTower

noncomputable section

/-- Frequency of a nonconstant local monomial in one QNM and its real-field partner. -/
def d4BMFundamentalPumpMonomialFrequency
    (headPartner : Bool) (r s : ℕ) (q : XiZeroCopy) : ℂ :=
  if headPartner then
    d4SingleSectorMonomialFrequency r (s + 1)
      (thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q))
  else
    d4SingleSectorMonomialFrequency (r + 1) s
      (thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q))

/-- Exact decay exponent of the normalized fundamental pump. -/
lemma d4BMFundamentalPumpQNM_im_eq (q : XiZeroCopy) :
    (thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q)).im =
      -1 - (q.1 : ℂ).re / 2 := by
  rw [thetaCuspHawkingTopologicalBlackHoleQNMPlus_im]
  simp [xiSpectralPoint, thetaCuspHawkingTopologicalBlackHoleConformalDecay]
  ring

lemma d4BMFundamentalPumpQNM_im_lt_zero (q : XiZeroCopy) :
    (thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q)).im < 0 := by
  rw [thetaCuspHawkingTopologicalBlackHoleQNMPlus_im]
  have hz := abs_im_xiSpectralPoint_lt_half q
  have hz' : (xiSpectralPoint q).im < 1 / 2 := (abs_lt.mp hz).2
  norm_num [thetaCuspHawkingTopologicalBlackHoleConformalDecay]
  linarith

/-- Derivatives preserve frequency; every local monomial has total pump-factor decay. -/
lemma d4BMFundamentalPumpMonomialFrequency_im
    (headPartner : Bool) (r s : ℕ) (q : XiZeroCopy) :
    (d4BMFundamentalPumpMonomialFrequency headPartner r s q).im =
      ((r + s + 1 : ℕ) : ℝ) *
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q)).im := by
  cases headPartner <;>
    simp [d4BMFundamentalPumpMonomialFrequency, d4SingleSectorMonomialFrequency,
      d4QNMRealFieldPartnerFrequency] <;> ring

lemma d4BMFundamentalPumpMonomialFrequency_im_lt_zero
    (headPartner : Bool) (r s : ℕ) (q : XiZeroCopy) :
    (d4BMFundamentalPumpMonomialFrequency headPartner r s q).im < 0 := by
  rw [d4BMFundamentalPumpMonomialFrequency_im]
  have hcount : (0 : ℝ) < ((r + s + 1 : ℕ) : ℝ) := by positivity
  exact mul_neg_of_pos_of_neg hcount (d4BMFundamentalPumpQNM_im_lt_zero q)

/-- Exact positive delay-decay rate of a local pump monomial. -/
theorem d4BMFundamentalPumpMonomialDecayRate_eq
    (headPartner : Bool) (r s : ℕ) (q : XiZeroCopy) :
    (Complex.I * d4BMFundamentalPumpMonomialFrequency headPartner r s q).re =
      ((r + s + 1 : ℕ) : ℝ) * (1 + (q.1 : ℂ).re / 2) := by
  simp only [Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im, one_mul,
    zero_sub]
  rw [d4BMFundamentalPumpMonomialFrequency_im, d4BMFundamentalPumpQNM_im_eq]
  ring

/-- Every pump factor contributes between one and three-halves units of delay decay. -/
theorem d4BMFundamentalPumpMonomialDecayRate_mem_Ioo
    (headPartner : Bool) (r s : ℕ) (q : XiZeroCopy) :
    (Complex.I * d4BMFundamentalPumpMonomialFrequency headPartner r s q).re ∈
      Set.Ioo (((r + s + 1 : ℕ) : ℝ))
        ((3 / 2 : ℝ) * ((r + s + 1 : ℕ) : ℝ)) := by
  rw [d4BMFundamentalPumpMonomialDecayRate_eq]
  have hs := xi_divisor_support_re_mem_open_unit q.1
  have hcount : (0 : ℝ) < ((r + s + 1 : ℕ) : ℝ) := by positivity
  constructor <;> nlinarith [hs.1, hs.2]

/-- Stationary mass insertion allowed by nonnegative horizon absorption. -/
def d4BMPassiveStationaryMassNumerator (absorbedMass : NNReal) (z : ℂ) : ℂ :=
  ((absorbedMass : ℝ) : ℂ) * d4FundamentalQNMCrossBranchChiralMassJetNumerator z

/-- Passive mass completion cannot cancel normalized AIME return. -/
theorem d4BMPassiveStationaryFullNumerator_xi_ne_zero
    (absorbedMass : NNReal) (q : XiZeroCopy) :
    d4FundamentalQNMCrossBranchAIMENumerator 1 (xiSpectralPoint q) +
      d4BMPassiveStationaryMassNumerator absorbedMass (xiSpectralPoint q) ≠ 0 := by
  simp only [d4FundamentalQNMCrossBranchAIMENumerator,
    d4BMPassiveStationaryMassNumerator, map_one, one_mul]
  norm_num
  rw [show
    d4FundamentalQNMCrossBranchChiralMassJetNumerator (xiSpectralPoint q) +
        ((absorbedMass : ℝ) : ℂ) *
          d4FundamentalQNMCrossBranchChiralMassJetNumerator (xiSpectralPoint q) =
      (1 + ((absorbedMass : ℝ) : ℂ)) *
        d4FundamentalQNMCrossBranchChiralMassJetNumerator (xiSpectralPoint q) by ring]
  exact mul_ne_zero
    (by
      exact_mod_cast (ne_of_gt (by positivity :
        (0 : ℝ) < 1 + (absorbedMass : ℝ))))
    (d4FundamentalQNMCrossBranchChiralMassJetNumerator_xi_ne_zero q)

/-- Horizon passivity excludes the negative stationary AIME ray. -/
theorem d4BMPassiveStationaryMassNumerator_ne_forcedCounterterm
    (absorbedMass : NNReal) (q : XiZeroCopy) :
    d4BMPassiveStationaryMassNumerator absorbedMass (xiSpectralPoint q) ≠
      -d4FundamentalQNMCrossBranchAIMENumerator 1 (xiSpectralPoint q) := by
  intro h
  apply d4BMPassiveStationaryFullNumerator_xi_ne_zero absorbedMass q
  rw [h]
  ring

/-- Finite local source packet, including polynomial factors from finite Jordan chains. -/
def d4BMFiniteLocalDelayedSourceRemainder {mode degree : ℕ}
    (coefficient : Fin mode → Fin degree → ℂ)
    (headPartner : Fin mode → Bool) (r s : Fin mode → ℕ)
    (q : XiZeroCopy) (delay : ℝ) : ℂ :=
  ∑ j, ∑ k, coefficient j k * (delay : ℂ) ^ (k : ℕ) *
    Complex.exp (-(Complex.I *
      d4BMFundamentalPumpMonomialFrequency (headPartner j) (r j) (s j) q * delay))

/-- Every finite local pump packet decays in continuous advanced time. -/
theorem d4BMFiniteLocalDelayedSourceRemainder_tendsto_zero {mode degree : ℕ}
    (coefficient : Fin mode → Fin degree → ℂ)
    (headPartner : Fin mode → Bool) (r s : Fin mode → ℕ)
    (q : XiZeroCopy) :
    Tendsto
      (d4BMFiniteLocalDelayedSourceRemainder coefficient headPartner r s q)
      atTop (nhds 0) := by
  rw [show (0 : ℂ) = ∑ _j : Fin mode, ∑ _k : Fin degree, 0 by simp]
  apply tendsto_finsetSum
  intro j _hj
  apply tendsto_finsetSum
  intro k _hk
  have hrate : 0 < (Complex.I *
      d4BMFundamentalPumpMonomialFrequency (headPartner j) (r j) (s j) q).re := by
    simp only [Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im, one_mul,
      zero_sub]
    exact neg_pos.mpr
      (d4BMFundamentalPumpMonomialFrequency_im_lt_zero
        (headPartner j) (r j) (s j) q)
  simpa only [d4BMFiniteLocalDelayedSourceRemainder, mul_assoc, mul_zero] using
    (tendsto_const_nhds.mul
      (GaloisForLFunctions.HTGeometry.tendsto_cpow_mul_cexp hrate (k : ℕ)))

/-- Normalized AIME numerator survives every finite local delayed source packet. -/
theorem eventually_d4BMFiniteLocalDelayedFullPoleNumerator_ne_zero {mode degree : ℕ}
    (coefficient : Fin mode → Fin degree → ℂ)
    (headPartner : Fin mode → Bool) (r s : Fin mode → ℕ)
    (q : XiZeroCopy) :
    ∀ᶠ delay in atTop,
      d4FundamentalQNMCrossBranchAIMENumerator 1 (xiSpectralPoint q) +
        d4BMFiniteLocalDelayedSourceRemainder coefficient headPartner r s q delay ≠ 0 := by
  have hAIME :
      d4FundamentalQNMCrossBranchAIMENumerator 1 (xiSpectralPoint q) ≠ 0 :=
    (d4FundamentalQNMCrossBranchAIMENumerator_xi_ne_zero_iff 1 q).2 one_ne_zero
  have hlimit : Tendsto
      (fun delay => d4FundamentalQNMCrossBranchAIMENumerator 1 (xiSpectralPoint q) +
        d4BMFiniteLocalDelayedSourceRemainder coefficient headPartner r s q delay)
      atTop (nhds (d4FundamentalQNMCrossBranchAIMENumerator 1 (xiSpectralPoint q))) := by
    simpa using tendsto_const_nhds.add
      (d4BMFiniteLocalDelayedSourceRemainder_tendsto_zero
        coefficient headPartner r s q)
  exact hlimit.eventually (eventually_ne_nhds hAIME)

/-- Finite local dynamics cannot eventually equal the forced AIME counterterm. -/
theorem not_eventually_d4BMFiniteLocalDelayedSourceRemainder_eq_forcedCounterterm
    {mode degree : ℕ}
    (coefficient : Fin mode → Fin degree → ℂ)
    (headPartner : Fin mode → Bool) (r s : Fin mode → ℕ)
    (q : XiZeroCopy) :
    ¬∀ᶠ delay in atTop,
      d4BMFiniteLocalDelayedSourceRemainder coefficient headPartner r s q delay =
        -d4FundamentalQNMCrossBranchAIMENumerator 1 (xiSpectralPoint q) := by
  intro hcounterterm
  have hsurvive := eventually_d4BMFiniteLocalDelayedFullPoleNumerator_ne_zero
    coefficient headPartner r s q
  have hfalse : ∀ᶠ _delay : ℝ in atTop, False := by
    filter_upwards [hcounterterm, hsurvive] with delay hcounter hne
    apply hne
    rw [hcounter]
    ring
  obtain ⟨a, ha⟩ := eventually_atTop.1 hfalse
  exact ha a le_rfl

/-- Principal part with a finite local delayed source packet. -/
def d4BMFiniteLocalDelayedCrossBranchPolePrincipalPart {mode degree : ℕ}
    (coefficient : Fin mode → Fin degree → ℂ)
    (headPartner : Fin mode → Bool) (r s : Fin mode → ℕ)
    (q : XiZeroCopy) (delay : ℝ) (omega : ℂ) : ℂ :=
  d4FullCrossBranchPolePrincipalPart 1
    (fun _ => d4BMFiniteLocalDelayedSourceRemainder
      coefficient headPartner r s q delay)
    (xiSpectralPoint q) omega

/-- Finite local delayed dynamics eventually retain the exact negative-branch simple pole. -/
theorem eventually_d4BMFiniteLocalDelayedCrossBranchPole_order_qnmMinus_xi
    {mode degree : ℕ}
    (coefficient : Fin mode → Fin degree → ℂ)
    (headPartner : Fin mode → Bool) (r s : Fin mode → ℕ)
    (q : XiZeroCopy) :
    ∀ᶠ delay in atTop,
      meromorphicOrderAt
        (d4BMFiniteLocalDelayedCrossBranchPolePrincipalPart
          coefficient headPartner r s q delay)
        (thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)) =
          ((-1 : ℤ) : WithTop ℤ) := by
  have hsurvive := eventually_d4BMFiniteLocalDelayedFullPoleNumerator_ne_zero
    coefficient headPartner r s q
  filter_upwards [hsurvive] with delay hnonzero
  unfold d4BMFiniteLocalDelayedCrossBranchPolePrincipalPart
  apply (d4FullCrossBranchPolePrincipalPart_order_qnmMinus_xi_iff
    1 (fun _ => d4BMFiniteLocalDelayedSourceRemainder
      coefficient headPartner r s q delay) q).2
  intro hcounterterm
  apply hnonzero
  rw [hcounterterm]
  ring

/-! ## Physical hyperbolic continuum -/

/-- Physical hyperbolic line, where the angular square-root parameter is real. -/
def d4BMPhysicalContinuumSpectralPoint (t : ℝ) : ℂ :=
  2 * (t : ℂ) - Complex.I / 2

lemma d4BMPhysicalContinuumSpectralPoint_angularMomentum (t : ℝ) :
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum
        (d4BMPhysicalContinuumSpectralPoint t) = t := by
  simp [d4BMPhysicalContinuumSpectralPoint,
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum]
  ring

lemma d4BMPhysicalContinuumSpectralPoint_angularQ (t : ℝ) :
    d4ThetaTeukolskyAngularQ (d4BMPhysicalContinuumSpectralPoint t) =
      1 / 4 + (t : ℂ) ^ 2 := by
  unfold d4ThetaTeukolskyAngularQ
  rw [thetaCuspHawkingTopologicalBlackHoleAngularEigenvalue]
  rw [d4BMPhysicalContinuumSpectralPoint_angularMomentum]

/-- Physical fundamental continuum QNM has uniform damping `3/2`. -/
theorem d4BMPhysicalContinuumSpectralPoint_qnmPlus (t : ℝ) :
    thetaCuspHawkingTopologicalBlackHoleQNMPlus 0
        (d4BMPhysicalContinuumSpectralPoint t) =
      (t : ℂ) - (3 / 2 : ℝ) * Complex.I := by
  unfold thetaCuspHawkingTopologicalBlackHoleQNMPlus
    thetaCuspHawkingTopologicalBlackHoleConformalDecay
  rw [d4BMPhysicalContinuumSpectralPoint_angularMomentum]
  norm_num
  ring

/-- Exact advanced-time factorization of a physical continuum QNM. -/
theorem d4BMPhysicalContinuumTranslationCharacter_eq (t delay : ℝ) :
    Complex.exp (-Complex.I *
        thetaCuspHawkingTopologicalBlackHoleQNMPlus 0
          (d4BMPhysicalContinuumSpectralPoint t) * delay) =
      (Real.exp (-(3 / 2 * delay)) : ℂ) *
        Complex.exp (-Complex.I * (t : ℂ) * delay) := by
  rw [d4BMPhysicalContinuumSpectralPoint_qnmPlus]
  rw [show -Complex.I * ((t : ℂ) - (3 / 2 : ℝ) * Complex.I) * delay =
      (-(3 / 2 * delay) : ℝ) + (-Complex.I * (t : ℂ) * delay) by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring]
  rw [Complex.exp_add]
  norm_num

/-- Exact fundamental chiral kernel on the physical hyperbolic continuum. -/
def d4BMPhysicalContinuumChiralKernel (t : ℝ) : ℂ :=
  -3 / (((1 / 4 : ℝ) + t ^ 2) * ((9 / 4 : ℝ) + t ^ 2) : ℝ)

theorem d4BMPhysicalContinuumChiralKernel_eq_sourceKernel (t : ℝ) :
    d4FundamentalQNMChiralSourceKernel (d4BMPhysicalContinuumSpectralPoint t) =
      d4BMPhysicalContinuumChiralKernel t := by
  have hQ : d4ThetaTeukolskyAngularQ
      (d4BMPhysicalContinuumSpectralPoint t) ≠ 0 := by
    rw [d4BMPhysicalContinuumSpectralPoint_angularQ]
    intro h
    have hre := congrArg Complex.re h
    simp [pow_two, Complex.mul_re] at hre
    nlinarith [sq_nonneg t]
  have hQ2 : d4ThetaTeukolskyAngularQ
      (d4BMPhysicalContinuumSpectralPoint t) + 2 ≠ 0 := by
    rw [d4BMPhysicalContinuumSpectralPoint_angularQ]
    intro h
    have hre := congrArg Complex.re h
    simp [pow_two, Complex.mul_re] at hre
    nlinarith [sq_nonneg t]
  rw [d4FundamentalQNMChiralSourceKernel_eq _ hQ hQ2]
  rw [d4BMPhysicalContinuumSpectralPoint_angularQ]
  unfold d4BMPhysicalContinuumChiralKernel
  push_cast
  ring

lemma norm_d4BMPhysicalContinuumChiralKernel (t : ℝ) :
    ‖d4BMPhysicalContinuumChiralKernel t‖ =
      3 / (((1 / 4 : ℝ) + t ^ 2) * ((9 / 4 : ℝ) + t ^ 2)) := by
  unfold d4BMPhysicalContinuumChiralKernel
  rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity :
      0 < ((1 / 4 : ℝ) + t ^ 2) * ((9 / 4 : ℝ) + t ^ 2))]
  norm_num

lemma norm_d4BMPhysicalContinuumChiralKernel_le (t : ℝ) :
    ‖d4BMPhysicalContinuumChiralKernel t‖ ≤
      (16 / 3 : ℝ) * (1 + t ^ 2)⁻¹ := by
  rw [norm_d4BMPhysicalContinuumChiralKernel]
  have h1 : 0 < (1 / 4 : ℝ) + t ^ 2 := by positivity
  have h2 : 0 < (9 / 4 : ℝ) + t ^ 2 := by positivity
  have h3 : 0 < (1 : ℝ) + t ^ 2 := by positivity
  rw [show (16 / 3 : ℝ) * (1 + t ^ 2)⁻¹ =
      (16 / 3 : ℝ) / (1 + t ^ 2) by ring]
  apply (div_le_div_iff₀ (mul_pos h1 h2) h3).2
  nlinarith [sq_nonneg (t ^ 2)]

lemma continuous_d4BMPhysicalContinuumChiralKernel :
    Continuous d4BMPhysicalContinuumChiralKernel := by
  unfold d4BMPhysicalContinuumChiralKernel
  apply Continuous.div₀ (by fun_prop) (by fun_prop)
  intro t
  exact Complex.ofReal_ne_zero.mpr
    (mul_ne_zero (ne_of_gt (by positivity)) (ne_of_gt (by positivity)))

/-- Physical chiral projection kernel is square-integrable on the continuum. -/
theorem memLp_two_d4BMPhysicalContinuumChiralKernel :
    MemLp d4BMPhysicalContinuumChiralKernel 2 volume := by
  refine MemLp.mono
    (GaloisForLFunctions.memLp_inv_one_add_sq.const_mul (16 / 3 : ℝ))
    continuous_d4BMPhysicalContinuumChiralKernel.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (by positivity :
    0 < (16 / 3 : ℝ) * (1 + t ^ 2)⁻¹)]
  exact norm_d4BMPhysicalContinuumChiralKernel_le t

/-- Finite-energy physical continuum datum. -/
structure D4BMFiniteEnergyContinuumState where
  field : ℝ → ℂ
  finiteEnergy : MemLp field 2 volume

/-- Chiral source density obtained by physical-continuum projection. -/
def d4BMFiniteEnergyContinuumSourceDensity
    (state : D4BMFiniteEnergyContinuumState) (t : ℝ) : ℂ :=
  state.field t * d4BMPhysicalContinuumChiralKernel t

theorem integrable_d4BMFiniteEnergyContinuumSourceDensity
    (state : D4BMFiniteEnergyContinuumState) :
    Integrable (d4BMFiniteEnergyContinuumSourceDensity state) volume := by
  exact MemLp.integrable_mul state.finiteEnergy
    memLp_two_d4BMPhysicalContinuumChiralKernel

/-- Exact physical continuum response with the Birmingham--Mokhtari time character. -/
def d4BMFiniteEnergyContinuumDelayedResponse
    (state : D4BMFiniteEnergyContinuumState) (delay : ℝ) : ℂ :=
  ∫ t : ℝ, d4BMFiniteEnergyContinuumSourceDensity state t *
    Complex.exp (-Complex.I *
      thetaCuspHawkingTopologicalBlackHoleQNMPlus 0
        (d4BMPhysicalContinuumSpectralPoint t) * delay)

/-- Factorized continuum response displaying uniform horizon damping. -/
def d4BMFiniteEnergyContinuumFactoredResponse
    (state : D4BMFiniteEnergyContinuumState) (delay : ℝ) : ℂ :=
  (Real.exp (-(3 / 2 * delay)) : ℂ) *
    ∫ t : ℝ, d4BMFiniteEnergyContinuumSourceDensity state t *
      Complex.exp (-Complex.I * (t : ℂ) * delay)

lemma d4BMFiniteEnergyContinuumDelayedResponse_eq_factorized
    (state : D4BMFiniteEnergyContinuumState) (delay : ℝ) :
    d4BMFiniteEnergyContinuumDelayedResponse state delay =
      d4BMFiniteEnergyContinuumFactoredResponse state delay := by
  unfold d4BMFiniteEnergyContinuumDelayedResponse
    d4BMFiniteEnergyContinuumFactoredResponse
  rw [← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [d4BMPhysicalContinuumTranslationCharacter_eq]
  ring

lemma norm_d4BMPhysicalContinuumReducedPhase (t delay : ℝ) :
    ‖Complex.exp (-Complex.I * (t : ℂ) * delay)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

lemma integrable_d4BMFiniteEnergyContinuumReducedIntegrand
    (state : D4BMFiniteEnergyContinuumState) (delay : ℝ) :
    Integrable (fun t : ℝ =>
      d4BMFiniteEnergyContinuumSourceDensity state t *
        Complex.exp (-Complex.I * (t : ℂ) * delay)) := by
  have hphase : AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (-Complex.I * (t : ℂ) * delay)) volume := by
    fun_prop
  have h := (integrable_d4BMFiniteEnergyContinuumSourceDensity state).bdd_mul hphase
    (Filter.Eventually.of_forall fun t => by
      rw [norm_d4BMPhysicalContinuumReducedPhase])
  simpa [mul_comm] using h

lemma norm_d4BMFiniteEnergyContinuumFactoredResponse_le
    (state : D4BMFiniteEnergyContinuumState) (delay : ℝ) :
    ‖d4BMFiniteEnergyContinuumFactoredResponse state delay‖ ≤
      (∫ t : ℝ, ‖d4BMFiniteEnergyContinuumSourceDensity state t‖) *
        Real.exp (-(3 / 2 * delay)) := by
  unfold d4BMFiniteEnergyContinuumFactoredResponse
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-(3 / 2 * delay)) *
        ‖∫ t : ℝ, d4BMFiniteEnergyContinuumSourceDensity state t *
          Complex.exp (-Complex.I * (t : ℂ) * delay)‖ ≤
      Real.exp (-(3 / 2 * delay)) *
        ∫ t : ℝ, ‖d4BMFiniteEnergyContinuumSourceDensity state t *
          Complex.exp (-Complex.I * (t : ℂ) * delay)‖ := by
            gcongr
            exact norm_integral_le_integral_norm _
    _ = Real.exp (-(3 / 2 * delay)) *
        ∫ t : ℝ, ‖d4BMFiniteEnergyContinuumSourceDensity state t‖ := by
          congr 1
          apply integral_congr_ae
          filter_upwards with t
          rw [norm_mul, norm_d4BMPhysicalContinuumReducedPhase, mul_one]
    _ = (∫ t : ℝ, ‖d4BMFiniteEnergyContinuumSourceDensity state t‖) *
        Real.exp (-(3 / 2 * delay)) := by ring

/-- Every finite-energy fundamental physical continuum response decays at late time. -/
theorem d4BMFiniteEnergyContinuumDelayedResponse_tendsto_zero
    (state : D4BMFiniteEnergyContinuumState) :
    Tendsto (d4BMFiniteEnergyContinuumDelayedResponse state) atTop (nhds 0) := by
  have hfactor : d4BMFiniteEnergyContinuumDelayedResponse state =
      d4BMFiniteEnergyContinuumFactoredResponse state := by
    funext delay
    exact d4BMFiniteEnergyContinuumDelayedResponse_eq_factorized state delay
  rw [hfactor]
  apply GaloisForLFunctions.HTGeometry.tendsto_zero_of_eventually_norm_le_polyExp
    (N := 0)
    (C := ∫ t : ℝ, ‖d4BMFiniteEnergyContinuumSourceDensity state t‖)
    (δ := 3 / 2) (by norm_num)
  exact Filter.Eventually.of_forall fun delay => by
    simpa using norm_d4BMFiniteEnergyContinuumFactoredResponse_le state delay

/-! ## Passive discrete-plus-continuum completion -/

/-- Sum of finite local pump terms and finite-energy physical continuum return. -/
def d4BMFiniteLocalContinuumDelayedSourceRemainder {mode degree : ℕ}
    (coefficient : Fin mode → Fin degree → ℂ)
    (headPartner : Fin mode → Bool) (r s : Fin mode → ℕ)
    (state : D4BMFiniteEnergyContinuumState) (q : XiZeroCopy) (delay : ℝ) : ℂ :=
  d4BMFiniteLocalDelayedSourceRemainder coefficient headPartner r s q delay +
    d4BMFiniteEnergyContinuumDelayedResponse state delay

theorem d4BMFiniteLocalContinuumDelayedSourceRemainder_tendsto_zero
    {mode degree : ℕ}
    (coefficient : Fin mode → Fin degree → ℂ)
    (headPartner : Fin mode → Bool) (r s : Fin mode → ℕ)
    (state : D4BMFiniteEnergyContinuumState) (q : XiZeroCopy) :
    Tendsto
      (d4BMFiniteLocalContinuumDelayedSourceRemainder
        coefficient headPartner r s state q)
      atTop (nhds 0) := by
  change Tendsto
    (fun delay =>
      d4BMFiniteLocalDelayedSourceRemainder coefficient headPartner r s q delay +
        d4BMFiniteEnergyContinuumDelayedResponse state delay)
    atTop (nhds 0)
  simpa only [add_zero] using
    (d4BMFiniteLocalDelayedSourceRemainder_tendsto_zero
      coefficient headPartner r s q).add
      (d4BMFiniteEnergyContinuumDelayedResponse_tendsto_zero state)

/-- Passive mass plus finite local and continuum dynamics cannot erase normalized AIME. -/
theorem eventually_d4BMPassiveFiniteLocalContinuumFullPoleNumerator_ne_zero
    {mode degree : ℕ}
    (coefficient : Fin mode → Fin degree → ℂ)
    (headPartner : Fin mode → Bool) (r s : Fin mode → ℕ)
    (state : D4BMFiniteEnergyContinuumState) (absorbedMass : NNReal)
    (q : XiZeroCopy) :
    ∀ᶠ delay in atTop,
      d4FundamentalQNMCrossBranchAIMENumerator 1 (xiSpectralPoint q) +
        d4BMPassiveStationaryMassNumerator absorbedMass (xiSpectralPoint q) +
        d4BMFiniteLocalContinuumDelayedSourceRemainder
          coefficient headPartner r s state q delay ≠ 0 := by
  have hstationary :=
    d4BMPassiveStationaryFullNumerator_xi_ne_zero absorbedMass q
  have hlimit : Tendsto
      (fun delay =>
        (d4FundamentalQNMCrossBranchAIMENumerator 1 (xiSpectralPoint q) +
          d4BMPassiveStationaryMassNumerator absorbedMass (xiSpectralPoint q)) +
          d4BMFiniteLocalContinuumDelayedSourceRemainder
            coefficient headPartner r s state q delay)
      atTop (nhds
        (d4FundamentalQNMCrossBranchAIMENumerator 1 (xiSpectralPoint q) +
          d4BMPassiveStationaryMassNumerator absorbedMass (xiSpectralPoint q))) := by
    simpa using tendsto_const_nhds.add
      (d4BMFiniteLocalContinuumDelayedSourceRemainder_tendsto_zero
        coefficient headPartner r s state q)
  exact hlimit.eventually (eventually_ne_nhds hstationary)

/-- Full passive discrete-plus-continuum principal part. -/
def d4BMPassiveFiniteLocalContinuumDelayedPolePrincipalPart {mode degree : ℕ}
    (coefficient : Fin mode → Fin degree → ℂ)
    (headPartner : Fin mode → Bool) (r s : Fin mode → ℕ)
    (state : D4BMFiniteEnergyContinuumState) (absorbedMass : NNReal)
    (q : XiZeroCopy) (delay : ℝ) (omega : ℂ) : ℂ :=
  d4FullCrossBranchPolePrincipalPart 1
    (fun _ => d4BMPassiveStationaryMassNumerator absorbedMass (xiSpectralPoint q) +
      d4BMFiniteLocalContinuumDelayedSourceRemainder
        coefficient headPartner r s state q delay)
    (xiSpectralPoint q) omega

/-- Passive discrete-plus-continuum response eventually retains the exact simple pole. -/
theorem eventually_d4BMPassiveFiniteLocalContinuumDelayedPole_order_qnmMinus_xi
    {mode degree : ℕ}
    (coefficient : Fin mode → Fin degree → ℂ)
    (headPartner : Fin mode → Bool) (r s : Fin mode → ℕ)
    (state : D4BMFiniteEnergyContinuumState) (absorbedMass : NNReal)
    (q : XiZeroCopy) :
    ∀ᶠ delay in atTop,
      meromorphicOrderAt
        (d4BMPassiveFiniteLocalContinuumDelayedPolePrincipalPart
          coefficient headPartner r s state absorbedMass q delay)
        (thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)) =
          ((-1 : ℤ) : WithTop ℤ) := by
  have hsurvive :=
    eventually_d4BMPassiveFiniteLocalContinuumFullPoleNumerator_ne_zero
      coefficient headPartner r s state absorbedMass q
  filter_upwards [hsurvive] with delay hnonzero
  unfold d4BMPassiveFiniteLocalContinuumDelayedPolePrincipalPart
  apply (d4FullCrossBranchPolePrincipalPart_order_qnmMinus_xi_iff
    1 (fun _ => d4BMPassiveStationaryMassNumerator absorbedMass (xiSpectralPoint q) +
      d4BMFiniteLocalContinuumDelayedSourceRemainder
        coefficient headPartner r s state q delay) q).2
  intro hcounterterm
  apply hnonzero
  rw [add_assoc, hcounterterm]
  ring

end

end RHTower
