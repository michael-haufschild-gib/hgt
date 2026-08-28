import GaloisForLFunctions.RHTower.HedenmalmStokesOrientedFirstTraceQuantizedJump
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldZetaPoleCarrier
import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureLatticePrimeGammaBudget

/-!
# Prime Stokes jump projector onto the critical line

The oriented valuation-one prime current has one-sided wall values `-4` and `4`, although its
termwise value at the wall is zero.  Taking a symmetric first difference across an aperture `a`
therefore produces a source-defined real Stokes mask

`(J (t + a) - J (t - a)) / 8`.

As `a -> 0+`, the mask tends to `1` at centered depth `t = 0` and to `0` at every nonzero depth.
Thus the prime residue jump supplies the real/Wirtinger scalarization forced by the no-go theorem
for entire scalar masks.  The aperture is chosen before any Xi divisor is accessed.  On every
finite divisor packet the same aperture recovers critical-line multiplicity coefficient by
coefficient.

This is an unconditional source projector and finite-packet landing theorem.  It does not assert
the height-uniform interchange needed for the asymptotic HCF lattice budget.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Symmetric real Stokes difference of the prime-defined oriented first-trace current. -/
def gammaSewnMobiusApertureStokesPrimeJumpProjector
    (a t : ℝ) : ℝ :=
  (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent (t + a) -
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent (t - a)) / 8

/-- Away from the neutral wall, the oriented current is the restriction of a continuous
prime-log source. -/
theorem gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_eq_primeLogContinuation
    {t : ℝ} (ht : t ≠ 0) :
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent t =
      8 * t *
        (xiPrimeLogDirichletContinuation
          (((1 + 2 * |t| : ℝ) : ℂ))).re := by
  have hd : 0 < |t| := abs_pos.mpr ht
  have hs : (1 : ℝ) < 1 + 2 * |t| := by linarith
  rw [gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_eq,
    HedenmalmThetaSource.thetaPhysicalEndpointPrimeHardyGreenEnergy_eq_primeLogDirichlet
      |t| hd,
    ← xiPrimeLogDirichletContinuation_eq (by simpa using hs)]
  ring

/-- The only discontinuity of the oriented prime current is its quantized wall jump. -/
theorem continuousAt_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_of_ne_zero
    {t : ℝ} (ht : t ≠ 0) :
    ContinuousAt gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent t := by
  let s : ℝ → ℂ := fun u => (((1 + 2 * |u| : ℝ) : ℂ))
  have hs : 1 < (s t).re := by
    simp only [s, ofReal_re]
    linarith [abs_pos.mpr ht]
  have hscont : ContinuousAt s t := by
    dsimp only [s]
    fun_prop
  have hsource : ContinuousAt (fun u : ℝ => xiPrimeLogDirichletContinuation (s u)) t :=
    (differentiableAt_xiPrimeLogDirichletContinuation_of_one_lt_re hs).continuousAt.comp'
      hscont
  have hre : ContinuousAt
      (fun u : ℝ => (xiPrimeLogDirichletContinuation (s u)).re) t :=
    Complex.continuous_re.continuousAt.comp' hsource
  have hmodel : ContinuousAt
      (fun u : ℝ => 8 * u * (xiPrimeLogDirichletContinuation (s u)).re) t := by
    fun_prop
  have heq : gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent =ᶠ[𝓝 t]
      (fun u : ℝ => 8 * u * (xiPrimeLogDirichletContinuation (s u)).re) := by
    filter_upwards [eventually_ne_nhds ht] with u hu
    simpa only [s] using
      gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_eq_primeLogContinuation hu
  exact hmodel.congr heq.symm

/-! ## Scale-free Stokes jump charge -/

/-- A normalized Stokes jump is the right boundary value minus the left boundary value, divided
by the prime residue quantum `8`.  This relation contains no aperture scale. -/
def HasNormalizedPrimeStokesJumpAt (f : ℝ → ℝ) (t charge : ℝ) : Prop :=
  ∃ left right : ℝ,
    Tendsto f (𝓝[<] t) (𝓝 left) ∧
    Tendsto f (𝓝[>] t) (𝓝 right) ∧
    charge = (right - left) / 8

/-- The oriented prime current has normalized Stokes charge one at the neutral wall. -/
theorem hasNormalizedPrimeStokesJumpAt_orientedFirstTrace_zero :
    HasNormalizedPrimeStokesJumpAt
      gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent 0 1 := by
  refine ⟨-4, 4,
    tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsLT_zero,
    tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsGT_zero, ?_⟩
  norm_num

/-- Every nonneutral depth has zero Stokes charge because the prime current is continuous there. -/
theorem hasNormalizedPrimeStokesJumpAt_orientedFirstTrace_of_ne_zero
    {t : ℝ} (ht : t ≠ 0) :
    HasNormalizedPrimeStokesJumpAt
      gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent t 0 := by
  have hcont :=
    continuousAt_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_of_ne_zero ht
  refine ⟨gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent t,
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent t, ?_, ?_, ?_⟩
  · exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  · exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  · ring

/-- **Scale-free prime Stokes projector.**  The normalized jump charge of the source-defined
oriented prime current is exactly the indicator of neutral centered depth. -/
theorem hasNormalizedPrimeStokesJumpAt_orientedFirstTrace
    (t : ℝ) :
    HasNormalizedPrimeStokesJumpAt
      gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent t
      (if t = 0 then 1 else 0) := by
  by_cases ht : t = 0
  · subst t
    simpa using hasNormalizedPrimeStokesJumpAt_orientedFirstTrace_zero
  · simpa [ht] using
      hasNormalizedPrimeStokesJumpAt_orientedFirstTrace_of_ne_zero ht

/-- Normalized Stokes charge is unique whenever both one-sided boundary values exist. -/
theorem HasNormalizedPrimeStokesJumpAt.unique
    {f : ℝ → ℝ} {t charge₁ charge₂ : ℝ}
    (h₁ : HasNormalizedPrimeStokesJumpAt f t charge₁)
    (h₂ : HasNormalizedPrimeStokesJumpAt f t charge₂) :
    charge₁ = charge₂ := by
  obtain ⟨left₁, right₁, hleft₁, hright₁, hcharge₁⟩ := h₁
  obtain ⟨left₂, right₂, hleft₂, hright₂, hcharge₂⟩ := h₂
  have hleft : left₁ = left₂ := tendsto_nhds_unique hleft₁ hleft₂
  have hright : right₁ = right₂ := tendsto_nhds_unique hright₁ hright₂
  rw [hcharge₁, hcharge₂, hleft, hright]

/-- Exact classification of every possible normalized jump charge of the oriented prime current. -/
theorem hasNormalizedPrimeStokesJumpAt_orientedFirstTrace_iff
    (t charge : ℝ) :
    HasNormalizedPrimeStokesJumpAt
      gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent t charge ↔
      charge = if t = 0 then 1 else 0 := by
  constructor
  · intro hcharge
    exact hcharge.unique
      (hasNormalizedPrimeStokesJumpAt_orientedFirstTrace t)
  · rintro rfl
    exact hasNormalizedPrimeStokesJumpAt_orientedFirstTrace t

/-- Divisor-free real-plane form: arbitrarily small nonzero horizontal shifts have zero local
jump charge, while the critical line has charge one. -/
theorem hasNormalizedPrimeStokesJumpAt_orientedFirstTrace_criticalLine
    (z : ℂ) :
    HasNormalizedPrimeStokesJumpAt
      gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
      (2 * z.re - 1) (if z.re = 1 / 2 then 1 else 0) := by
  have hzero : 2 * z.re - 1 = 0 ↔ z.re = 1 / 2 := by
    constructor <;> intro h <;> linarith
  simpa only [hzero] using
    hasNormalizedPrimeStokesJumpAt_orientedFirstTrace (2 * z.re - 1)

/-- The unique normalized jump charge of the prime current, defined from its one-sided source
boundary values rather than from a divisor predicate. -/
def gammaSewnMobiusApertureStokesOrientedFirstTraceJumpCharge
    (t : ℝ) : ℝ :=
  Classical.choose
    (show ∃ charge : ℝ,
      HasNormalizedPrimeStokesJumpAt
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent t charge from
      ⟨if t = 0 then 1 else 0,
        hasNormalizedPrimeStokesJumpAt_orientedFirstTrace t⟩)

theorem hasNormalizedPrimeStokesJumpAt_orientedFirstTraceJumpCharge
    (t : ℝ) :
    HasNormalizedPrimeStokesJumpAt
      gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent t
      (gammaSewnMobiusApertureStokesOrientedFirstTraceJumpCharge t) := by
  exact Classical.choose_spec
    (show ∃ charge : ℝ,
      HasNormalizedPrimeStokesJumpAt
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent t charge from
      ⟨if t = 0 then 1 else 0,
        hasNormalizedPrimeStokesJumpAt_orientedFirstTrace t⟩)

/-- The source-defined jump charge is the exact neutral-depth indicator. -/
theorem gammaSewnMobiusApertureStokesOrientedFirstTraceJumpCharge_eq
    (t : ℝ) :
    gammaSewnMobiusApertureStokesOrientedFirstTraceJumpCharge t =
      if t = 0 then 1 else 0 :=
  (hasNormalizedPrimeStokesJumpAt_orientedFirstTrace_iff t
    (gammaSewnMobiusApertureStokesOrientedFirstTraceJumpCharge t)).mp
      (hasNormalizedPrimeStokesJumpAt_orientedFirstTraceJumpCharge t)

/-! ## Weighted jump calculus -/

/-- Multiplying by a continuous weight before taking the Stokes jump evaluates that weight at the
wall.  This is the linear, coefficient-faithful replacement for a quadratic diagonal residue. -/
theorem hasNormalizedPrimeStokesJumpAt_orientedFirstTrace_mul_zero
    {W : ℝ → ℝ} (hW : ContinuousAt W 0) :
    HasNormalizedPrimeStokesJumpAt
      (fun t => gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent t * W t)
      0 (W 0) := by
  have hWleft : Tendsto W (𝓝[<] (0 : ℝ)) (𝓝 (W 0)) :=
    hW.tendsto.mono_left nhdsWithin_le_nhds
  have hWright : Tendsto W (𝓝[>] (0 : ℝ)) (𝓝 (W 0)) :=
    hW.tendsto.mono_left nhdsWithin_le_nhds
  have hleft :=
    tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsLT_zero.mul hWleft
  have hright :=
    tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsGT_zero.mul hWright
  refine ⟨-4 * W 0, 4 * W 0, ?_, ?_, ?_⟩
  · simpa using hleft
  · simpa using hright
  · ring

/-- Away from the wall, multiplication by any locally continuous weight retains zero jump. -/
theorem hasNormalizedPrimeStokesJumpAt_orientedFirstTrace_mul_of_ne_zero
    {W : ℝ → ℝ} {t : ℝ} (hW : ContinuousAt W t) (ht : t ≠ 0) :
    HasNormalizedPrimeStokesJumpAt
      (fun u => gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent u * W u)
      t 0 := by
  have hcont :=
    (continuousAt_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_of_ne_zero ht).mul hW
  refine ⟨gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent t * W t,
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent t * W t, ?_, ?_, ?_⟩
  · exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  · exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  · ring

/-- Global weighted Stokes projector for every continuous real source weight. -/
theorem hasNormalizedPrimeStokesJumpAt_orientedFirstTrace_mul
    (W : ℝ → ℝ) (hW : Continuous W) (t : ℝ) :
    HasNormalizedPrimeStokesJumpAt
      (fun u => gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent u * W u)
      t (if t = 0 then W 0 else 0) := by
  by_cases ht : t = 0
  · subst t
    simpa using hasNormalizedPrimeStokesJumpAt_orientedFirstTrace_mul_zero hW.continuousAt
  · simpa [ht] using
      hasNormalizedPrimeStokesJumpAt_orientedFirstTrace_mul_of_ne_zero hW.continuousAt ht

/-! ## Explicit pole--Gamma counterjump -/

/-- The completed prime--Gamma current is continuous away from the neutral wall as well. -/
theorem continuousAt_gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent_of_ne_zero
    {t : ℝ} (ht : t ≠ 0) :
    ContinuousAt gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent t := by
  let s : ℝ → ℂ := fun u => (((1 + 2 * |u| : ℝ) : ℂ))
  have hs : 1 < (s t).re := by
    simp only [s, ofReal_re]
    linarith [abs_pos.mpr ht]
  have hscont : ContinuousAt s t := by
    dsimp only [s]
    fun_prop
  have hs1 : s t ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [s, ofReal_re, one_re] at hre
    linarith [abs_pos.mpr ht]
  have hsource : ContinuousAt (fun u : ℝ => completedPrimeGammaFlux (s u)) t :=
    (continuousAt_completedPrimeGammaFlux (by linarith) hs1
      (riemannZeta_ne_zero_of_one_lt_re hs)).comp' hscont
  have hre : ContinuousAt
      (fun u : ℝ => (completedPrimeGammaFlux (s u)).re) t :=
    Complex.continuous_re.continuousAt.comp' hsource
  have hmodel : ContinuousAt
      (fun u : ℝ => 8 * u * (completedPrimeGammaFlux (s u)).re) t := by
    fun_prop
  change ContinuousAt
    (fun u : ℝ => 8 * u *
      (completedPrimeGammaFlux (((1 + 2 * |u| : ℝ) : ℂ))).re) t
  simpa only [s] using hmodel

/-- The explicit higher-valuation/Gamma countercurrent is continuous at every nonzero depth. -/
theorem continuousAt_gammaSewnMobiusApertureStokesOrientedPolarCountercurrent_of_ne_zero
    {t : ℝ} (ht : t ≠ 0) :
    ContinuousAt gammaSewnMobiusApertureStokesOrientedPolarCountercurrent t := by
  have hcompleted :=
    continuousAt_gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent_of_ne_zero ht
  have hprime :=
    continuousAt_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_of_ne_zero ht
  have hmodel : ContinuousAt (fun u : ℝ =>
      gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent u -
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent u) t :=
    hcompleted.sub hprime
  have heq : gammaSewnMobiusApertureStokesOrientedPolarCountercurrent =ᶠ[𝓝 t]
      (fun u : ℝ =>
        gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent u -
          gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent u) := by
    filter_upwards [eventually_ne_nhds ht] with u hu
    have hdecomp :=
      gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent_eq_firstTrace_add_counter
        u hu
    linarith only [hdecomp]
  exact hmodel.congr heq.symm

/-- The explicit polar/Gamma countercurrent carries normalized wall charge `-1`. -/
theorem hasNormalizedPrimeStokesJumpAt_orientedPolarCountercurrent_zero :
    HasNormalizedPrimeStokesJumpAt
      gammaSewnMobiusApertureStokesOrientedPolarCountercurrent 0 (-1) := by
  refine ⟨4, -4,
    tendsto_gammaSewnMobiusApertureStokesOrientedPolarCountercurrent_nhdsLT_zero,
    tendsto_gammaSewnMobiusApertureStokesOrientedPolarCountercurrent_nhdsGT_zero, ?_⟩
  norm_num

/-- Off the wall, the polar/Gamma countercurrent has zero local Stokes charge. -/
theorem hasNormalizedPrimeStokesJumpAt_orientedPolarCountercurrent_of_ne_zero
    {t : ℝ} (ht : t ≠ 0) :
    HasNormalizedPrimeStokesJumpAt
      gammaSewnMobiusApertureStokesOrientedPolarCountercurrent t 0 := by
  have hcont :=
    continuousAt_gammaSewnMobiusApertureStokesOrientedPolarCountercurrent_of_ne_zero ht
  refine ⟨gammaSewnMobiusApertureStokesOrientedPolarCountercurrent t,
    gammaSewnMobiusApertureStokesOrientedPolarCountercurrent t, ?_, ?_, ?_⟩
  · exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  · exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  · ring

/-- Exact polar counterjump classification. -/
theorem hasNormalizedPrimeStokesJumpAt_orientedPolarCountercurrent
    (t : ℝ) :
    HasNormalizedPrimeStokesJumpAt
      gammaSewnMobiusApertureStokesOrientedPolarCountercurrent t
      (if t = 0 then -1 else 0) := by
  by_cases ht : t = 0
  · subst t
    simpa using hasNormalizedPrimeStokesJumpAt_orientedPolarCountercurrent_zero
  · simpa [ht] using
      hasNormalizedPrimeStokesJumpAt_orientedPolarCountercurrent_of_ne_zero ht

theorem hasNormalizedPrimeStokesJumpAt_orientedPolarCountercurrent_iff
    (t charge : ℝ) :
    HasNormalizedPrimeStokesJumpAt
      gammaSewnMobiusApertureStokesOrientedPolarCountercurrent t charge ↔
      charge = if t = 0 then -1 else 0 := by
  constructor
  · intro hcharge
    exact hcharge.unique
      (hasNormalizedPrimeStokesJumpAt_orientedPolarCountercurrent t)
  · rintro rfl
    exact hasNormalizedPrimeStokesJumpAt_orientedPolarCountercurrent t

/-- Unique source-defined jump charge of the explicit higher-valuation/Gamma countercurrent. -/
def gammaSewnMobiusApertureStokesOrientedPolarCountercurrentJumpCharge
    (t : ℝ) : ℝ :=
  Classical.choose
    (show ∃ charge : ℝ,
      HasNormalizedPrimeStokesJumpAt
        gammaSewnMobiusApertureStokesOrientedPolarCountercurrent t charge from
      ⟨if t = 0 then -1 else 0,
        hasNormalizedPrimeStokesJumpAt_orientedPolarCountercurrent t⟩)

theorem hasNormalizedPrimeStokesJumpAt_orientedPolarCountercurrentJumpCharge
    (t : ℝ) :
    HasNormalizedPrimeStokesJumpAt
      gammaSewnMobiusApertureStokesOrientedPolarCountercurrent t
      (gammaSewnMobiusApertureStokesOrientedPolarCountercurrentJumpCharge t) := by
  exact Classical.choose_spec
    (show ∃ charge : ℝ,
      HasNormalizedPrimeStokesJumpAt
        gammaSewnMobiusApertureStokesOrientedPolarCountercurrent t charge from
      ⟨if t = 0 then -1 else 0,
        hasNormalizedPrimeStokesJumpAt_orientedPolarCountercurrent t⟩)

theorem gammaSewnMobiusApertureStokesOrientedPolarCountercurrentJumpCharge_eq
    (t : ℝ) :
    gammaSewnMobiusApertureStokesOrientedPolarCountercurrentJumpCharge t =
      if t = 0 then -1 else 0 :=
  (hasNormalizedPrimeStokesJumpAt_orientedPolarCountercurrent_iff t
    (gammaSewnMobiusApertureStokesOrientedPolarCountercurrentJumpCharge t)).mp
      (hasNormalizedPrimeStokesJumpAt_orientedPolarCountercurrentJumpCharge t)

/-- The prime jump and explicit polar/Gamma counterjump cancel identically at every depth. -/
theorem orientedFirstTraceJumpCharge_add_polarCountercurrentJumpCharge
    (t : ℝ) :
    gammaSewnMobiusApertureStokesOrientedFirstTraceJumpCharge t +
      gammaSewnMobiusApertureStokesOrientedPolarCountercurrentJumpCharge t = 0 := by
  rw [gammaSewnMobiusApertureStokesOrientedFirstTraceJumpCharge_eq,
    gammaSewnMobiusApertureStokesOrientedPolarCountercurrentJumpCharge_eq]
  split_ifs <;> ring

/-- Continuous weights preserve the opposite polar/Gamma jump with coefficient `-W(0)`. -/
theorem hasNormalizedPrimeStokesJumpAt_orientedPolarCountercurrent_mul
    (W : ℝ → ℝ) (hW : Continuous W) (t : ℝ) :
    HasNormalizedPrimeStokesJumpAt
      (fun u => gammaSewnMobiusApertureStokesOrientedPolarCountercurrent u * W u)
      t (if t = 0 then -W 0 else 0) := by
  by_cases ht : t = 0
  · subst t
    have hWleft : Tendsto W (𝓝[<] (0 : ℝ)) (𝓝 (W 0)) :=
      hW.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hWright : Tendsto W (𝓝[>] (0 : ℝ)) (𝓝 (W 0)) :=
      hW.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hleft :=
      tendsto_gammaSewnMobiusApertureStokesOrientedPolarCountercurrent_nhdsLT_zero.mul hWleft
    have hright :=
      tendsto_gammaSewnMobiusApertureStokesOrientedPolarCountercurrent_nhdsGT_zero.mul hWright
    refine ⟨4 * W 0, -4 * W 0, ?_, ?_, ?_⟩
    · simpa using hleft
    · simpa using hright
    · simp only [if_pos]
      ring
  · have hcont :=
      (continuousAt_gammaSewnMobiusApertureStokesOrientedPolarCountercurrent_of_ne_zero ht).mul
        hW.continuousAt
    refine ⟨gammaSewnMobiusApertureStokesOrientedPolarCountercurrent t * W t,
      gammaSewnMobiusApertureStokesOrientedPolarCountercurrent t * W t, ?_, ?_, ?_⟩
    · exact hcont.tendsto.mono_left nhdsWithin_le_nhds
    · exact hcont.tendsto.mono_left nhdsWithin_le_nhds
    · simp [ht]

/-! ## HCF critical-feature landing -/

/-- HCF critical-line feature energy with its selector supplied by the prime Stokes jump charge. -/
def criticalLineCriticalFeaturePrimeStokesEnergy
    (t : ℝ) (q : XiZeroCopy) : ℝ :=
  gammaSewnMobiusApertureStokesOrientedFirstTraceJumpCharge
      (primeDepthBVWoldXiCenteredRate q.1) *
    Complex.normSq (criticalFeatureCauchyKernelTest t (xiSpectralPoint q))

/-- The scale-free prime Stokes selector equals the existing critical-line feature channel
coefficient by coefficient. -/
theorem criticalLineCriticalFeaturePrimeStokesEnergy_eq
    (t : ℝ) (q : XiZeroCopy) :
    criticalLineCriticalFeaturePrimeStokesEnergy t q =
      criticalLineCriticalFeatureEnergy t q := by
  rw [criticalLineCriticalFeaturePrimeStokesEnergy,
    gammaSewnMobiusApertureStokesOrientedFirstTraceJumpCharge_eq,
    criticalLineCriticalFeatureEnergy]
  simp only [primeDepthBVWoldXiCenteredRate_eq_zero_iff]
  split_ifs <;> ring

/-- The same HCF line energy supplied by the negative jump of the explicit
higher-valuation/Gamma countercurrent. -/
def criticalLineCriticalFeaturePolarStokesEnergy
    (t : ℝ) (q : XiZeroCopy) : ℝ :=
  -gammaSewnMobiusApertureStokesOrientedPolarCountercurrentJumpCharge
      (primeDepthBVWoldXiCenteredRate q.1) *
    Complex.normSq (criticalFeatureCauchyKernelTest t (xiSpectralPoint q))

theorem criticalLineCriticalFeaturePolarStokesEnergy_eq
    (t : ℝ) (q : XiZeroCopy) :
    criticalLineCriticalFeaturePolarStokesEnergy t q =
      criticalLineCriticalFeatureEnergy t q := by
  rw [criticalLineCriticalFeaturePolarStokesEnergy,
    gammaSewnMobiusApertureStokesOrientedPolarCountercurrentJumpCharge_eq,
    criticalLineCriticalFeatureEnergy]
  simp only [primeDepthBVWoldXiCenteredRate_eq_zero_iff]
  split_ifs <;> ring

/-- Multiplication occurs before the Stokes jump: its unique charge is exactly the HCF
critical-line feature energy, so no quadratic residue multiplicity is introduced. -/
theorem hasNormalizedPrimeStokesJumpAt_criticalLineCriticalFeature
    (t : ℝ) (q : XiZeroCopy) :
    HasNormalizedPrimeStokesJumpAt
      (fun u => gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent u *
        Complex.normSq (criticalFeatureCauchyKernelTest t (xiSpectralPoint q)))
      (primeDepthBVWoldXiCenteredRate q.1)
      (criticalLineCriticalFeatureEnergy t q) := by
  have h := hasNormalizedPrimeStokesJumpAt_orientedFirstTrace_mul
    (fun _u : ℝ =>
      Complex.normSq (criticalFeatureCauchyKernelTest t (xiSpectralPoint q)))
    continuous_const (primeDepthBVWoldXiCenteredRate q.1)
  simpa [criticalLineCriticalFeatureEnergy,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff] using h

/-- Pre-scalar polar/Gamma form of the HCF line channel: its weighted Stokes charge is the
negative critical-line energy. -/
theorem hasNormalizedPrimeStokesJumpAt_polarCountercurrent_criticalLineCriticalFeature
    (t : ℝ) (q : XiZeroCopy) :
    HasNormalizedPrimeStokesJumpAt
      (fun u => gammaSewnMobiusApertureStokesOrientedPolarCountercurrent u *
        Complex.normSq (criticalFeatureCauchyKernelTest t (xiSpectralPoint q)))
      (primeDepthBVWoldXiCenteredRate q.1)
      (-criticalLineCriticalFeatureEnergy t q) := by
  have h := hasNormalizedPrimeStokesJumpAt_orientedPolarCountercurrent_mul
    (fun _u : ℝ =>
      Complex.normSq (criticalFeatureCauchyKernelTest t (xiSpectralPoint q)))
    continuous_const (primeDepthBVWoldXiCenteredRate q.1)
  by_cases hq : (q.1 : ℂ).re = 1 / 2
  · have hq' : (q.1 : ℂ).re = (2 : ℝ)⁻¹ := by
      simpa only [one_div] using hq
    simpa [criticalLineCriticalFeatureEnergy,
      primeDepthBVWoldXiCenteredRate_eq_zero_iff, hq, hq'] using h
  · have hq' : (q.1 : ℂ).re ≠ (2 : ℝ)⁻¹ := by
      simpa only [one_div] using hq
    simpa [criticalLineCriticalFeatureEnergy,
      primeDepthBVWoldXiCenteredRate_eq_zero_iff, hq, hq'] using h

/-- Multiplicity-exact HCF critical-line trace with prime Stokes provenance. -/
def criticalLineCriticalFeaturePrimeStokesEnergyTrace (t : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, criticalLineCriticalFeaturePrimeStokesEnergy t q

theorem criticalLineCriticalFeaturePrimeStokesEnergyTrace_eq
    (t : ℝ) :
    criticalLineCriticalFeaturePrimeStokesEnergyTrace t =
      criticalLineCriticalFeatureEnergyTrace t := by
  rw [criticalLineCriticalFeaturePrimeStokesEnergyTrace,
    criticalLineCriticalFeatureEnergyTrace]
  exact tsum_congr (criticalLineCriticalFeaturePrimeStokesEnergy_eq t)

/-- HCF line trace sourced from the negative polar/Gamma Stokes jump. -/
def criticalLineCriticalFeaturePolarStokesEnergyTrace (t : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, criticalLineCriticalFeaturePolarStokesEnergy t q

theorem criticalLineCriticalFeaturePolarStokesEnergyTrace_eq
    (t : ℝ) :
    criticalLineCriticalFeaturePolarStokesEnergyTrace t =
      criticalLineCriticalFeatureEnergyTrace t := by
  rw [criticalLineCriticalFeaturePolarStokesEnergyTrace,
    criticalLineCriticalFeatureEnergyTrace]
  exact tsum_congr (criticalLineCriticalFeaturePolarStokesEnergy_eq t)

/-- Corrected HCF channel using the scale-free prime Stokes subtraction. -/
def criticalFeaturePrimeGammaStokesOffLineExcess (t : ℝ) : ℝ :=
  (criticalFeaturePrimeGammaSourceDiagonal t).re -
    criticalLineCriticalFeaturePrimeStokesEnergyTrace t

theorem criticalFeaturePrimeGammaStokesOffLineExcess_eq
    (t : ℝ) :
    criticalFeaturePrimeGammaStokesOffLineExcess t =
      criticalFeaturePrimeGammaOffLineExcess t := by
  rw [criticalFeaturePrimeGammaStokesOffLineExcess,
    criticalLineCriticalFeaturePrimeStokesEnergyTrace_eq,
    criticalFeaturePrimeGammaOffLineExcess]

/-- Lattice-summed HCF corrected budget with prime Stokes critical-line subtraction. -/
def criticalFeaturePrimeGammaStokesOffLineLatticeBudget
    (K : Finset ℤ) : ℝ :=
  ∑ k ∈ K, criticalFeaturePrimeGammaStokesOffLineExcess (k : ℝ)

/-- Exact replacement law: the new Stokes-corrected lattice budget equals the established HCF
off-line lattice budget, without a thin-strip width or Abel projector parameter. -/
theorem criticalFeaturePrimeGammaStokesOffLineLatticeBudget_eq
    (K : Finset ℤ) :
    criticalFeaturePrimeGammaStokesOffLineLatticeBudget K =
      criticalFeaturePrimeGammaOffLineLatticeBudget K := by
  rw [criticalFeaturePrimeGammaStokesOffLineLatticeBudget,
    criticalFeaturePrimeGammaOffLineLatticeBudget]
  apply Finset.sum_congr rfl
  intro k hk
  exact criticalFeaturePrimeGammaStokesOffLineExcess_eq (k : ℝ)

/-- HCF corrected channel written with explicit higher-valuation/Gamma Stokes subtraction. -/
def criticalFeaturePoleGammaStokesOffLineExcess (t : ℝ) : ℝ :=
  (criticalFeaturePrimeGammaSourceDiagonal t).re -
    criticalLineCriticalFeaturePolarStokesEnergyTrace t

theorem criticalFeaturePoleGammaStokesOffLineExcess_eq
    (t : ℝ) :
    criticalFeaturePoleGammaStokesOffLineExcess t =
      criticalFeaturePrimeGammaOffLineExcess t := by
  rw [criticalFeaturePoleGammaStokesOffLineExcess,
    criticalLineCriticalFeaturePolarStokesEnergyTrace_eq,
    criticalFeaturePrimeGammaOffLineExcess]

/-- Lattice HCF budget with the line subtraction realized by the explicit polar/Gamma jump. -/
def criticalFeaturePoleGammaStokesOffLineLatticeBudget
    (K : Finset ℤ) : ℝ :=
  ∑ k ∈ K, criticalFeaturePoleGammaStokesOffLineExcess (k : ℝ)

theorem criticalFeaturePoleGammaStokesOffLineLatticeBudget_eq
    (K : Finset ℤ) :
    criticalFeaturePoleGammaStokesOffLineLatticeBudget K =
      criticalFeaturePrimeGammaOffLineLatticeBudget K := by
  rw [criticalFeaturePoleGammaStokesOffLineLatticeBudget,
    criticalFeaturePrimeGammaOffLineLatticeBudget]
  apply Finset.sum_congr rfl
  intro k hk
  exact criticalFeaturePoleGammaStokesOffLineExcess_eq (k : ℝ)

/-- At nonzero centered depth, shrinking the common Stokes aperture gives zero. -/
theorem tendsto_gammaSewnMobiusApertureStokesPrimeJumpProjector_of_ne_zero
    {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun a : ℝ => gammaSewnMobiusApertureStokesPrimeJumpProjector a t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have ha : Tendsto (fun a : ℝ => a) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    nhdsWithin_le_nhds
  have hcont :=
    continuousAt_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_of_ne_zero ht
  have hplusArg : Tendsto (fun a : ℝ => t + a)
      (𝓝[>] (0 : ℝ)) (𝓝 t) := by
    simpa using tendsto_const_nhds.add ha
  have hminusArg : Tendsto (fun a : ℝ => t - a)
      (𝓝[>] (0 : ℝ)) (𝓝 t) := by
    simpa using tendsto_const_nhds.sub ha
  have hplus := hcont.tendsto.comp hplusArg
  have hminus := hcont.tendsto.comp hminusArg
  have hdiff := hplus.sub hminus
  have hscale := hdiff.const_mul (1 / 8 : ℝ)
  simpa [gammaSewnMobiusApertureStokesPrimeJumpProjector,
    div_eq_mul_inv, mul_comm] using hscale

/-- At neutral depth, the normalized prime Stokes jump has unit mass. -/
theorem tendsto_gammaSewnMobiusApertureStokesPrimeJumpProjector_zero :
    Tendsto (fun a : ℝ => gammaSewnMobiusApertureStokesPrimeJumpProjector a 0)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have h :=
    tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsGT_zero.const_mul
      (1 / 4 : ℝ)
  convert h using 1
  · funext a
    rw [gammaSewnMobiusApertureStokesPrimeJumpProjector,
      zero_add, zero_sub,
      gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_neg]
    ring
  · norm_num

/-- Pointwise source-projector law: the prime Stokes mask converges to the indicator of neutral
centered depth. -/
theorem tendsto_gammaSewnMobiusApertureStokesPrimeJumpProjector
    (t : ℝ) :
    Tendsto (fun a : ℝ => gammaSewnMobiusApertureStokesPrimeJumpProjector a t)
      (𝓝[>] (0 : ℝ)) (𝓝 (if t = 0 then 1 else 0)) := by
  by_cases ht : t = 0
  · subst t
    simpa using tendsto_gammaSewnMobiusApertureStokesPrimeJumpProjector_zero
  · simpa [ht] using
      tendsto_gammaSewnMobiusApertureStokesPrimeJumpProjector_of_ne_zero ht

/-- Divisor-free real-plane specialization of the Stokes projector. -/
def gammaSewnMobiusApertureStokesPrimeCriticalLineProjector
    (a : ℝ) (z : ℂ) : ℝ :=
  gammaSewnMobiusApertureStokesPrimeJumpProjector a (2 * z.re - 1)

/-- The source-defined real-plane mask converges pointwise to the critical-line indicator. -/
theorem tendsto_gammaSewnMobiusApertureStokesPrimeCriticalLineProjector
    (z : ℂ) :
    Tendsto (fun a : ℝ =>
      gammaSewnMobiusApertureStokesPrimeCriticalLineProjector a z)
      (𝓝[>] (0 : ℝ)) (𝓝 (if z.re = 1 / 2 then 1 else 0)) := by
  have hzero : 2 * z.re - 1 = 0 ↔ z.re = 1 / 2 := by
    constructor <;> intro h <;> linarith
  simpa only [gammaSewnMobiusApertureStokesPrimeCriticalLineProjector, hzero] using
    tendsto_gammaSewnMobiusApertureStokesPrimeJumpProjector (2 * z.re - 1)

/-- One common source aperture applied to a finite coefficient packet. -/
def finiteGammaSewnMobiusApertureStokesPrimeJumpProjection {ι : Type*}
    (s : Finset ι) (depth mass : ι → ℝ) (a : ℝ) : ℝ :=
  ∑ i ∈ s, mass i *
    gammaSewnMobiusApertureStokesPrimeJumpProjector a (depth i)

/-- Finite coefficient-faithful Stokes landing.  The limit is linear in multiplicity/mass, not
quadratic, and a single divisor-independent aperture is used for the whole packet. -/
theorem tendsto_finiteGammaSewnMobiusApertureStokesPrimeJumpProjection {ι : Type*}
    (s : Finset ι) (depth mass : ι → ℝ) :
    Tendsto
      (finiteGammaSewnMobiusApertureStokesPrimeJumpProjection s depth mass)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ i ∈ s, if depth i = 0 then mass i else 0)) := by
  change Tendsto
    (fun a : ℝ => ∑ i ∈ s, mass i *
      gammaSewnMobiusApertureStokesPrimeJumpProjector a (depth i))
    (𝓝[>] (0 : ℝ))
    (𝓝 (∑ i ∈ s, if depth i = 0 then mass i else 0))
  apply tendsto_finsetSum s
  intro i hi
  have h :=
    (tendsto_gammaSewnMobiusApertureStokesPrimeJumpProjector (depth i)).const_mul
      (mass i)
  by_cases hdepth : depth i = 0
  · simpa [hdepth] using h
  · simpa [hdepth] using h

/-- Finite multiplicity-copy landing of the source Stokes projector. -/
def finiteXiGammaSewnMobiusApertureStokesPrimeCriticalLineProjection
    (s : Finset XiZeroCopy) (a : ℝ) : ℝ :=
  ∑ q ∈ s,
    gammaSewnMobiusApertureStokesPrimeCriticalLineProjector a (q.1 : ℂ)

/-- On every finite Xi-copy packet, the common prime Stokes aperture recovers exactly the number
of multiplicity copies lying on the critical line. -/
theorem tendsto_finiteXiGammaSewnMobiusApertureStokesPrimeCriticalLineProjection
    (s : Finset XiZeroCopy) :
    Tendsto
      (finiteXiGammaSewnMobiusApertureStokesPrimeCriticalLineProjection s)
      (𝓝[>] (0 : ℝ))
      (𝓝 (((s.filter fun q => (q.1 : ℂ).re = 1 / 2).card : ℕ) : ℝ)) := by
  change Tendsto
    (fun a : ℝ => ∑ q ∈ s,
      gammaSewnMobiusApertureStokesPrimeJumpProjector a
        (primeDepthBVWoldXiCenteredRate q.1))
    (𝓝[>] (0 : ℝ)) _
  have h := tendsto_finiteGammaSewnMobiusApertureStokesPrimeJumpProjection
    s (fun q => primeDepthBVWoldXiCenteredRate q.1) (fun _ => 1)
  change Tendsto
    (fun a : ℝ => ∑ q ∈ s, (1 : ℝ) *
      gammaSewnMobiusApertureStokesPrimeJumpProjector a
        (primeDepthBVWoldXiCenteredRate q.1))
    (𝓝[>] (0 : ℝ))
    (𝓝 (∑ q ∈ s,
      if primeDepthBVWoldXiCenteredRate q.1 = 0 then (1 : ℝ) else 0)) at h
  simpa [primeDepthBVWoldXiCenteredRate_eq_zero_iff] using h

end

end RHTower
