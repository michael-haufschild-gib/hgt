import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingKMSFriedrichsMixingEndpoint

/-!
# Exact Hawking--KMS Cayley scattering dilation of a theta resonance sector

The preceding Davies endpoint starts from the level-shift generator.  Here the population
contraction is derived instead from an explicit conservative scattering dilation.

For one analytically tilted resonance shell, let

`F = omega^(2 : ℕ) XiC(omega + a i) / (4 sqrt(3) pi)`

be the unsquared form factor obtained from the genuine theta-cusp moving-mirror Born tangent.
At coupling `lambda`, put `j = lambda^(2 : ℕ) |F|^(2 : ℕ) / 4`.  The scalar entries

`r = (1-j)/(1+j)`,  `t = lambda F/(1+j)`

are the Cayley scattering completion of the self-adjoint two-port on-shell `K`-matrix whose
off-diagonal Born tangent is `F`.  They satisfy `r^(2 : ℕ) + |t|^(2 : ℕ) = 1`, and therefore

`(x,h) |-> (r x - conj(t) h, t x + r h)`

is an exactly invertible norm-preserving two-port scattering map.  Extending it by the identity
on the zero- and two-excitation fibres gives the usual energy-preserving unitary collision of two
equal-gap modes.

Feed the horizon port with a fresh Gibbs mode at Hawking ratio
`q = exp(-2 pi omega/kappa)`.  Tracing that mode after each collision sends the exterior excited
population `p` to

`r^(2 : ℕ) p + |t|^(2 : ℕ) p_H`,  where `p_H = q/(1+q)`.

Thus the Gibbs population is fixed, KMS detailed balance is exact, and after `n` collisions the
deviation is `r^(2n) (p-p_H)`.  At unit coupling this resonance sector mixes exactly when `F` is
nonzero, hence exactly when `XiC(omega + a i)` is nonzero.  Requiring mixing on every noncentral
tilted sector is equivalent to RH.

This is an exact repeated-interaction/thermal-scattering dilation, not a declaration of a Davies
rate.  Its unitary and reduced population laws are proved below.  It does not claim that this
minimal Cayley completion is the full nonperturbative moving-mirror S-matrix, nor that it proves
return to equilibrium for an interacting Pauli--Fierz Liouvillean.  The Hartle--Hawking Gibbs
ancillas model the equilibrium horizon channel; they are not the global Unruh evaporation state.
-/

open Complex Real Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace RHTower

/-! ## Source-faithful Cayley scattering block -/

/-- Dimensionless Cayley load of one theta resonance shell. -/
def thetaCuspHawkingCayleyLoad (lambda a omega : ℝ) : ℝ :=
  lambda ^ (2 : ℕ) *
    Complex.normSq (thetaCuspHawkingFriedrichsShellFormFactor a omega) / 4

/-- Real retention amplitude of the two-port Cayley scattering block. -/
def thetaCuspHawkingCayleyRetention (lambda a omega : ℝ) : ℝ :=
  (1 - thetaCuspHawkingCayleyLoad lambda a omega) /
    (1 + thetaCuspHawkingCayleyLoad lambda a omega)

/-- Complex exchange amplitude of the two-port Cayley scattering block. -/
def thetaCuspHawkingCayleyTransition (lambda a omega : ℝ) : ℂ :=
  ((lambda : ℂ) * thetaCuspHawkingFriedrichsShellFormFactor a omega) /
    ((1 + thetaCuspHawkingCayleyLoad lambda a omega : ℝ) : ℂ)

theorem thetaCuspHawkingCayleyLoad_nonneg (lambda a omega : ℝ) :
    0 ≤ thetaCuspHawkingCayleyLoad lambda a omega := by
  unfold thetaCuspHawkingCayleyLoad
  exact div_nonneg
    (mul_nonneg (sq_nonneg lambda)
      (Complex.normSq_nonneg
        (thetaCuspHawkingFriedrichsShellFormFactor a omega)))
    (by norm_num)

theorem thetaCuspHawkingCayley_denominator_pos (lambda a omega : ℝ) :
    0 < 1 + thetaCuspHawkingCayleyLoad lambda a omega := by
  linarith [thetaCuspHawkingCayleyLoad_nonneg lambda a omega]

/-- Exact cubic Born remainder of the Cayley completion.  In particular its first coupling
coefficient is the physical unsquared theta shell form factor. -/
theorem thetaCuspHawkingCayleyTransition_sub_born
    (lambda a omega : ℝ) :
    thetaCuspHawkingCayleyTransition lambda a omega -
        (lambda : ℂ) * thetaCuspHawkingFriedrichsShellFormFactor a omega =
      -(((lambda * thetaCuspHawkingCayleyLoad lambda a omega /
          (1 + thetaCuspHawkingCayleyLoad lambda a omega) : ℝ) : ℂ) *
        thetaCuspHawkingFriedrichsShellFormFactor a omega) := by
  rw [thetaCuspHawkingCayleyTransition]
  have hden := (thetaCuspHawkingCayley_denominator_pos lambda a omega).ne'
  have hdenC :
      (1 : ℂ) + (thetaCuspHawkingCayleyLoad lambda a omega : ℂ) ≠ 0 := by
    exact_mod_cast hden
  push_cast
  field_simp [hdenC]
  ring

/-- Lossless two-port law for the exact Cayley scattering amplitudes. -/
theorem thetaCuspHawkingCayleyRetention_sq_add_transition_normSq
    (lambda a omega : ℝ) :
    thetaCuspHawkingCayleyRetention lambda a omega ^ (2 : ℕ) +
        Complex.normSq (thetaCuspHawkingCayleyTransition lambda a omega) = 1 := by
  let F : ℂ := thetaCuspHawkingFriedrichsShellFormFactor a omega
  let j : ℝ := thetaCuspHawkingCayleyLoad lambda a omega
  have hj : j = lambda ^ (2 : ℕ) * Complex.normSq F / 4 := rfl
  have hfour : lambda ^ (2 : ℕ) * Complex.normSq F = 4 * j := by
    rw [hj]
    ring
  have hden : 1 + j ≠ 0 :=
    (thetaCuspHawkingCayley_denominator_pos lambda a omega).ne'
  rw [thetaCuspHawkingCayleyRetention, thetaCuspHawkingCayleyTransition]
  change ((1 - j) / (1 + j)) ^ (2 : ℕ) +
      Complex.normSq (((lambda : ℂ) * F) / ((1 + j : ℝ) : ℂ)) = 1
  rw [Complex.normSq_div, Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_ofReal]
  field_simp [hden]
  rw [hfour]
  ring

/-- Incoming exterior output of the Cayley two-port scattering map. -/
def thetaCuspHawkingCayleyExteriorOutput
    (lambda a omega : ℝ) (x h : ℂ) : ℂ :=
  (thetaCuspHawkingCayleyRetention lambda a omega : ℂ) * x -
    conj (thetaCuspHawkingCayleyTransition lambda a omega) * h

/-- Outgoing horizon output of the Cayley two-port scattering map. -/
def thetaCuspHawkingCayleyHorizonOutput
    (lambda a omega : ℝ) (x h : ℂ) : ℂ :=
  thetaCuspHawkingCayleyTransition lambda a omega * x +
    (thetaCuspHawkingCayleyRetention lambda a omega : ℂ) * h

/-- Exact conservation of the positive two-port Hermitian form. -/
theorem thetaCuspHawkingCayley_preserves_hermitian
    (lambda a omega : ℝ) (x h : ℂ) :
    conj (thetaCuspHawkingCayleyExteriorOutput lambda a omega x h) *
          thetaCuspHawkingCayleyExteriorOutput lambda a omega x h +
        conj (thetaCuspHawkingCayleyHorizonOutput lambda a omega x h) *
          thetaCuspHawkingCayleyHorizonOutput lambda a omega x h =
      conj x * x + conj h * h := by
  let r : ℝ := thetaCuspHawkingCayleyRetention lambda a omega
  let t : ℂ := thetaCuspHawkingCayleyTransition lambda a omega
  have hunit := thetaCuspHawkingCayleyRetention_sq_add_transition_normSq
    lambda a omega
  have hunitC := congrArg (fun y : ℝ => (y : ℂ)) hunit
  push_cast at hunitC
  have hnorm : (Complex.normSq t : ℂ) = conj t * t := by
    rw [Complex.normSq_eq_conj_mul_self]
  rw [hnorm] at hunitC
  change conj ((r : ℂ) * x - conj t * h) * ((r : ℂ) * x - conj t * h) +
      conj (t * x + (r : ℂ) * h) * (t * x + (r : ℂ) * h) =
        conj x * x + conj h * h
  simp only [map_sub, map_add, map_mul, conj_ofReal, conj_conj]
  linear_combination (conj x * x + conj h * h) * hunitC

/-- Adjoint exterior coordinate of the Cayley scattering block. -/
def thetaCuspHawkingCayleyAdjointExterior
    (lambda a omega : ℝ) (y k : ℂ) : ℂ :=
  (thetaCuspHawkingCayleyRetention lambda a omega : ℂ) * y +
    conj (thetaCuspHawkingCayleyTransition lambda a omega) * k

/-- Adjoint horizon coordinate of the Cayley scattering block. -/
def thetaCuspHawkingCayleyAdjointHorizon
    (lambda a omega : ℝ) (y k : ℂ) : ℂ :=
  -thetaCuspHawkingCayleyTransition lambda a omega * y +
    (thetaCuspHawkingCayleyRetention lambda a omega : ℂ) * k

/-- The displayed adjoint is a left inverse, so the conservative scattering block is an actual
two-port unitary rather than only a norm identity on selected inputs. -/
theorem thetaCuspHawkingCayley_adjoint_after_scattering
    (lambda a omega : ℝ) (x h : ℂ) :
    thetaCuspHawkingCayleyAdjointExterior lambda a omega
        (thetaCuspHawkingCayleyExteriorOutput lambda a omega x h)
        (thetaCuspHawkingCayleyHorizonOutput lambda a omega x h) = x ∧
      thetaCuspHawkingCayleyAdjointHorizon lambda a omega
        (thetaCuspHawkingCayleyExteriorOutput lambda a omega x h)
        (thetaCuspHawkingCayleyHorizonOutput lambda a omega x h) = h := by
  let r : ℝ := thetaCuspHawkingCayleyRetention lambda a omega
  let t : ℂ := thetaCuspHawkingCayleyTransition lambda a omega
  have hunit := thetaCuspHawkingCayleyRetention_sq_add_transition_normSq
    lambda a omega
  have hunitC := congrArg (fun y : ℝ => (y : ℂ)) hunit
  push_cast at hunitC
  have hnorm : (Complex.normSq t : ℂ) = conj t * t := by
    rw [Complex.normSq_eq_conj_mul_self]
  rw [hnorm] at hunitC
  change ((r : ℂ) * ((r : ℂ) * x - conj t * h) +
        conj t * (t * x + (r : ℂ) * h) = x) ∧
      (-t * ((r : ℂ) * x - conj t * h) +
        (r : ℂ) * (t * x + (r : ℂ) * h) = h)
  constructor
  · linear_combination x * hunitC
  · linear_combination h * hunitC

/-! ## Exact Hawking Gibbs reduction -/

/-- Excited population of one horizon ancilla in the Hawking Gibbs state. -/
def thetaCuspHawkingKMSExcitedPopulation (kappa omega : ℝ) : ℝ :=
  let q := thetaCuspHawkingKMSBoltzmannRatio kappa omega
  q / (1 + q)

theorem thetaCuspHawkingKMSExcitedPopulation_pos
    (kappa omega : ℝ) :
    0 < thetaCuspHawkingKMSExcitedPopulation kappa omega := by
  unfold thetaCuspHawkingKMSExcitedPopulation
  exact div_pos (thetaCuspHawkingKMSBoltzmannRatio_pos kappa omega)
    (by linarith [thetaCuspHawkingKMSBoltzmannRatio_pos kappa omega])

/-- Exterior excited population obtained by scattering a diagonal exterior state of population
`p` against a diagonal horizon state of population `e`, then tracing the horizon port.  The four
terms are the `10`, `01`, and `11` input fibres of the energy-preserving two-mode unitary. -/
def thetaCuspHawkingCayleyReducedExcitedPopulation
    (lambda a omega p e : ℝ) : ℝ :=
  p * (1 - e) * thetaCuspHawkingCayleyRetention lambda a omega ^ (2 : ℕ) +
    (1 - p) * e *
      Complex.normSq (thetaCuspHawkingCayleyTransition lambda a omega) +
    p * e

/-- Tracing the horizon port gives the thermal attenuator affine law. -/
theorem thetaCuspHawkingCayleyReducedExcitedPopulation_eq
    (lambda a omega p e : ℝ) :
    thetaCuspHawkingCayleyReducedExcitedPopulation lambda a omega p e =
      thetaCuspHawkingCayleyRetention lambda a omega ^ (2 : ℕ) * p +
        Complex.normSq (thetaCuspHawkingCayleyTransition lambda a omega) * e := by
  have hunit := thetaCuspHawkingCayleyRetention_sq_add_transition_normSq
    lambda a omega
  have htransition :
      Complex.normSq (thetaCuspHawkingCayleyTransition lambda a omega) =
        1 - thetaCuspHawkingCayleyRetention lambda a omega ^ (2 : ℕ) := by
    linarith
  unfold thetaCuspHawkingCayleyReducedExcitedPopulation
  rw [htransition]
  ring

/-- One exact collision with a fresh Hawking Gibbs horizon mode. -/
def thetaCuspHawkingKMSCayleyPopulationChannel
    (lambda kappa a omega p : ℝ) : ℝ :=
  thetaCuspHawkingCayleyReducedExcitedPopulation lambda a omega p
    (thetaCuspHawkingKMSExcitedPopulation kappa omega)

/-- The KMS population is stationary and every deviation is multiplied by the retained power. -/
theorem thetaCuspHawkingKMSCayleyPopulationChannel_sub_gibbs
    (lambda kappa a omega p : ℝ) :
    thetaCuspHawkingKMSCayleyPopulationChannel lambda kappa a omega p -
        thetaCuspHawkingKMSExcitedPopulation kappa omega =
      thetaCuspHawkingCayleyRetention lambda a omega ^ (2 : ℕ) *
        (p - thetaCuspHawkingKMSExcitedPopulation kappa omega) := by
  rw [thetaCuspHawkingKMSCayleyPopulationChannel,
    thetaCuspHawkingCayleyReducedExcitedPopulation_eq]
  have hunit := thetaCuspHawkingCayleyRetention_sq_add_transition_normSq
    lambda a omega
  have htransition :
      Complex.normSq (thetaCuspHawkingCayleyTransition lambda a omega) =
        1 - thetaCuspHawkingCayleyRetention lambda a omega ^ (2 : ℕ) := by
    linarith
  rw [htransition]
  ring

theorem thetaCuspHawkingKMSCayleyPopulationChannel_gibbs
    (lambda kappa a omega : ℝ) :
    thetaCuspHawkingKMSCayleyPopulationChannel lambda kappa a omega
        (thetaCuspHawkingKMSExcitedPopulation kappa omega) =
      thetaCuspHawkingKMSExcitedPopulation kappa omega := by
  have h := thetaCuspHawkingKMSCayleyPopulationChannel_sub_gibbs
    lambda kappa a omega (thetaCuspHawkingKMSExcitedPopulation kappa omega)
  linarith

/-- Exact upward one-collision probability from a ground exterior mode. -/
def thetaCuspHawkingKMSCayleyUpProbability
    (lambda kappa a omega : ℝ) : ℝ :=
  Complex.normSq (thetaCuspHawkingCayleyTransition lambda a omega) *
    thetaCuspHawkingKMSExcitedPopulation kappa omega

/-- Exact downward one-collision probability from an excited exterior mode. -/
def thetaCuspHawkingKMSCayleyDownProbability
    (lambda kappa a omega : ℝ) : ℝ :=
  Complex.normSq (thetaCuspHawkingCayleyTransition lambda a omega) *
    (1 - thetaCuspHawkingKMSExcitedPopulation kappa omega)

/-- Exact Hawking KMS detailed balance of the unitary collision dilation. -/
theorem thetaCuspHawkingKMSCayleyUpProbability_eq_ratio_mul_down
    (lambda kappa a omega : ℝ) :
    thetaCuspHawkingKMSCayleyUpProbability lambda kappa a omega =
      thetaCuspHawkingKMSBoltzmannRatio kappa omega *
        thetaCuspHawkingKMSCayleyDownProbability lambda kappa a omega := by
  let q := thetaCuspHawkingKMSBoltzmannRatio kappa omega
  have hq : 1 + q ≠ 0 := by
    linarith [thetaCuspHawkingKMSBoltzmannRatio_pos kappa omega]
  rw [thetaCuspHawkingKMSCayleyUpProbability,
    thetaCuspHawkingKMSCayleyDownProbability,
    thetaCuspHawkingKMSExcitedPopulation]
  change _ * (q / (1 + q)) = q * (_ * (1 - q / (1 + q)))
  field_simp [hq]
  ring

/-! ## Repeated-scattering mixing and RH endpoint -/

/-- Closed population after `n` collisions with fresh Hawking Gibbs horizon modes. -/
def thetaCuspHawkingKMSCayleyPopulationAfter
    (lambda kappa a omega : ℝ) (n : ℕ) (p : ℝ) : ℝ :=
  thetaCuspHawkingKMSExcitedPopulation kappa omega +
    (thetaCuspHawkingCayleyRetention lambda a omega ^ (2 : ℕ)) ^ n *
      (p - thetaCuspHawkingKMSExcitedPopulation kappa omega)

theorem thetaCuspHawkingKMSCayleyPopulationAfter_zero
    (lambda kappa a omega p : ℝ) :
    thetaCuspHawkingKMSCayleyPopulationAfter lambda kappa a omega 0 p = p := by
  simp [thetaCuspHawkingKMSCayleyPopulationAfter]

/-- The closed formula is exactly the iteration of the reduced collision channel. -/
theorem thetaCuspHawkingKMSCayleyPopulationAfter_succ
    (lambda kappa a omega : ℝ) (n : ℕ) (p : ℝ) :
    thetaCuspHawkingKMSCayleyPopulationAfter lambda kappa a omega (n + 1) p =
      thetaCuspHawkingKMSCayleyPopulationChannel lambda kappa a omega
        (thetaCuspHawkingKMSCayleyPopulationAfter lambda kappa a omega n p) := by
  have hdev := thetaCuspHawkingKMSCayleyPopulationChannel_sub_gibbs lambda kappa
    a omega (thetaCuspHawkingKMSCayleyPopulationAfter lambda kappa a omega n p)
  have hchannel :
      thetaCuspHawkingKMSCayleyPopulationChannel lambda kappa a omega
          (thetaCuspHawkingKMSCayleyPopulationAfter lambda kappa a omega n p) =
        thetaCuspHawkingKMSExcitedPopulation kappa omega +
          thetaCuspHawkingCayleyRetention lambda a omega ^ (2 : ℕ) *
            (thetaCuspHawkingKMSCayleyPopulationAfter lambda kappa a omega n p -
              thetaCuspHawkingKMSExcitedPopulation kappa omega) := by
    linarith
  rw [hchannel]
  simp only [thetaCuspHawkingKMSCayleyPopulationAfter]
  rw [pow_succ]
  ring

/-- Mixing of the exact repeated-scattering dilation on all physical initial populations. -/
def ThetaCuspHawkingKMSCayleySectorMixes
    (kappa a omega : ℝ) : Prop :=
  ∀ p : ℝ, p ∈ Set.Icc 0 1 →
    Tendsto
      (fun n : ℕ => thetaCuspHawkingKMSCayleyPopulationAfter
        1 kappa a omega n p)
      atTop (𝓝 (thetaCuspHawkingKMSExcitedPopulation kappa omega))

theorem thetaCuspHawkingFriedrichsShellFormFactor_eq_zero_iff
    {a omega : ℝ} (homega : 0 < omega) :
    thetaCuspHawkingFriedrichsShellFormFactor a omega = 0 ↔
      XiC ((omega : ℂ) + (a : ℂ) * I) = 0 := by
  constructor
  · intro hF
    have hshell : thetaCuspHawkingTiltedBornRightEnergyShellDensity a omega = 0 := by
      rw [← normSq_thetaCuspHawkingFriedrichsShellFormFactor, hF]
      exact Complex.normSq_zero
    exact (thetaCuspHawkingTiltedBornRightEnergyShellDensity_eq_zero_iff homega).1 hshell
  · intro hXi
    simp [thetaCuspHawkingFriedrichsShellFormFactor, hXi]

theorem thetaCuspHawkingCayleyTransition_one_ne_zero_iff
    (a omega : ℝ) :
    thetaCuspHawkingCayleyTransition 1 a omega ≠ 0 ↔
      thetaCuspHawkingFriedrichsShellFormFactor a omega ≠ 0 := by
  have hden := (thetaCuspHawkingCayley_denominator_pos 1 a omega).ne'
  have hdenC :
      (((1 + thetaCuspHawkingCayleyLoad 1 a omega : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hden
  constructor
  · intro ht hF
    apply ht
    simp [thetaCuspHawkingCayleyTransition, hF]
  · intro hF
    rw [thetaCuspHawkingCayleyTransition]
    exact div_ne_zero (by simpa using hF) hdenC

/-- Exact mixing criterion derived from the unitary thermal scattering dilation. -/
theorem thetaCuspHawkingKMSCayleySectorMixes_iff_formFactor_ne_zero
    {kappa a omega : ℝ} :
    ThetaCuspHawkingKMSCayleySectorMixes kappa a omega ↔
      thetaCuspHawkingFriedrichsShellFormFactor a omega ≠ 0 := by
  constructor
  · intro hmix hF
    have hlim := hmix 0 (by constructor <;> norm_num)
    have hpH := thetaCuspHawkingKMSExcitedPopulation_pos kappa omega
    have hconst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
        (𝓝 (thetaCuspHawkingKMSExcitedPopulation kappa omega)) := by
      simpa [thetaCuspHawkingKMSCayleyPopulationAfter,
        thetaCuspHawkingCayleyRetention, thetaCuspHawkingCayleyLoad, hF] using hlim
    have hzero := tendsto_const_nhds_iff.mp hconst
    linarith
  · intro hF p _hp
    have ht : thetaCuspHawkingCayleyTransition 1 a omega ≠ 0 :=
      (thetaCuspHawkingCayleyTransition_one_ne_zero_iff a omega).2 hF
    have htpos : 0 < Complex.normSq
        (thetaCuspHawkingCayleyTransition 1 a omega) :=
      Complex.normSq_pos.mpr ht
    have hunit := thetaCuspHawkingCayleyRetention_sq_add_transition_normSq 1 a omega
    have hr0 : 0 ≤ thetaCuspHawkingCayleyRetention 1 a omega ^ (2 : ℕ) := sq_nonneg _
    have hr1 : thetaCuspHawkingCayleyRetention 1 a omega ^ (2 : ℕ) < 1 := by
      linarith
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    have hdev := hpow.mul_const
      (p - thetaCuspHawkingKMSExcitedPopulation kappa omega)
    have hsum :
        Tendsto
          (fun n : ℕ => thetaCuspHawkingKMSExcitedPopulation kappa omega +
            (thetaCuspHawkingCayleyRetention 1 a omega ^ (2 : ℕ)) ^ n *
              (p - thetaCuspHawkingKMSExcitedPopulation kappa omega))
          atTop
          (𝓝 (thetaCuspHawkingKMSExcitedPopulation kappa omega + 0)) :=
      tendsto_const_nhds.add (by simpa using hdev)
    simpa [thetaCuspHawkingKMSCayleyPopulationAfter] using hsum

/-- The exact scattering sector mixes precisely away from a theta/Xi dark shell. -/
theorem thetaCuspHawkingKMSCayleySectorMixes_iff_XiC_ne_zero
    {kappa a omega : ℝ} (homega : 0 < omega) :
    ThetaCuspHawkingKMSCayleySectorMixes kappa a omega ↔
      XiC ((omega : ℂ) + (a : ℂ) * I) ≠ 0 := by
  rw [thetaCuspHawkingKMSCayleySectorMixes_iff_formFactor_ne_zero,
    ne_eq, thetaCuspHawkingFriedrichsShellFormFactor_eq_zero_iff homega]

/-- Every positive-frequency noncentral tilted Hawking resonance sector mixes under its exact
KMS/Cayley repeated-scattering dilation. -/
def ThetaCuspHawkingKMSCayleyScatteringMixing : Prop :=
  ∀ (kappa a omega : ℝ), 0 < kappa → 0 < omega → |a| < 1 → a ≠ 0 →
    ThetaCuspHawkingKMSCayleySectorMixes kappa a omega

/-- **Hawking KMS/scattering endpoint.**  RH is equivalent to exact thermalization of every
noncentral tilted resonance sector in the source-faithful Cayley scattering dilation. -/
theorem riemannHypothesis_iff_thetaCuspHawkingKMSCayleyScatteringMixing :
    RiemannHypothesis ↔ ThetaCuspHawkingKMSCayleyScatteringMixing := by
  rw [riemannHypothesis_iff_XiC_zeros_real]
  constructor
  · intro hreal kappa a omega _hkappa homega _ha hane
    rw [thetaCuspHawkingKMSCayleySectorMixes_iff_XiC_ne_zero homega]
    intro hXi
    have him := hreal ((omega : ℂ) + (a : ℂ) * I) hXi
    exact hane (by simpa using him)
  · intro hmix z hz
    by_contra hzim
    have hzre : z.re ≠ 0 := by
      intro hre
      have hform : z = (z.im : ℂ) * I := by
        apply Complex.ext <;> simp [hre]
      rw [hform] at hz
      exact XiC_ne_zero_of_imaginary z.im hz
    have hstrip := xiC_zero_im_mem_openHalf hz
    have ha : |z.im| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    rcases lt_or_gt_of_ne hzre with hneg | hpos
    · have hsector := hmix 1 (-z.im) (-z.re) (by norm_num) (by linarith)
          (by simpa using ha) (neg_ne_zero.mpr hzim)
      have hXiNe :=
        (thetaCuspHawkingKMSCayleySectorMixes_iff_XiC_ne_zero
          (by linarith)).1 hsector
      apply hXiNe
      have harg :
          (((-z.re : ℝ) : ℂ) + ((-z.im : ℝ) : ℂ) * I) = -z := by
        apply Complex.ext <;> simp
      rw [harg, XiC_even]
      exact hz
    · have hsector := hmix 1 z.im z.re (by norm_num) hpos ha hzim
      have hXiNe :=
        (thetaCuspHawkingKMSCayleySectorMixes_iff_XiC_ne_zero hpos).1 hsector
      apply hXiNe
      have harg : ((z.re : ℂ) + (z.im : ℂ) * I) = z := by
        apply Complex.ext <;> simp
      rwa [harg]

end RHTower
