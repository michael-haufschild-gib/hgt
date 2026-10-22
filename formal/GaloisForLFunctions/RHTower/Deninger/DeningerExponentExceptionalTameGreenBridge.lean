import GaloisForLFunctions.RHTower.WoldActivationDivisorBlowup
import GaloisForLFunctions.RHTower.Deninger.DeningerBurnolConormalRadialTopBoundaryComparison
import GaloisForLFunctions.RHTower.XiHedenmalmJordanNormalCollision

/-!
# Exponent-deformation exceptional transport into the Gamma-six Green boundary

The multiplicative exponent deformation

`ζ(s) / ζ(zs)`

has a genuine two-variable collision at `(z,s) = (1,ρ)`.  In the blow-up
chart `z = 1+t`, `s = ρ+tw`, the target normal coordinate is exactly

`zs-ρ = t (w+ρ+tw)`.

Consequently the exceptional fibre is `(w/(w+ρ))^d`, where `d` is the
actual zeta/Xi multiplicity.  Critical-line reflection moves its marked pole
from `-ρ` to `-(1-conj ρ)`; their displacement is exactly the completed-Xi
Green fracture.

The second half of the file retains the two exceptional sections as marked
branches.  For the Milnor symbol with constant leg `6^m`, its tame exponent
at a branch of order `v` is `-v*m`.  Thus the two marked tame exponents are
`(-m,m)`.  The Deninger half-density character reads their oriented difference
as the actual degree-`6^m` radial mate curvature.  At `m=1` this is the
canonical Gamma/Calderon--Witt boundary coefficient up to its already-proved
positive calibration.

All statements are unconditional.  In particular, tame reciprocity below
proves only multiplicative neutrality of the two local symbols; no Stokes
annihilation or critical-line premise is inserted.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-! ## Exact exponent collision and its exceptional fibre -/

/-- Exponent-deformed activation face `ζ(s)/ζ(zs)`. -/
def deningerExponentDeformationActivation (z s : ℂ) : ℂ :=
  riemannZeta s / riemannZeta (z * s)

/-- The exponent deformation is the existing additive activation with
translation parameter `(z-1)s`. -/
theorem deningerExponentDeformationActivation_eq_woldActivation
    (z s : ℂ) :
    deningerExponentDeformationActivation z s =
      GaloisForLFunctions.RHTower.woldActivationInfiniteDepth
        ((z - 1) * s) s := by
  rw [deningerExponentDeformationActivation,
    GaloisForLFunctions.RHTower.woldActivationInfiniteDepth]
  congr 2
  ring

/-- Source point in the `t`-chart of the exponent/divisor blow-up. -/
def deningerExponentCollisionSource
    (rho t w : ℂ) : ℂ :=
  rho + t * w

/-- Exponent-deformed target point in the same chart. -/
def deningerExponentCollisionTarget
    (rho t w : ℂ) : ℂ :=
  (1 + t) * deningerExponentCollisionSource rho t w

/-- Exact source normal coordinate. -/
theorem deningerExponentCollisionSource_sub
    (rho t w : ℂ) :
    deningerExponentCollisionSource rho t w - rho = t * w := by
  simp [deningerExponentCollisionSource]

/-- **Exact singular transport identity.**  The exponent-deformed target
normal coordinate contains the common exceptional factor `t`, with residual
coordinate `w+rho+tw`. -/
theorem deningerExponentCollisionTarget_sub
    (rho t w : ℂ) :
    deningerExponentCollisionTarget rho t w - rho =
      t * (w + rho + t * w) := by
  simp [deningerExponentCollisionTarget,
    deningerExponentCollisionSource]
  ring

/-- Exact zeta conormal order on an Xi divisor support point. -/
abbrev DeningerExponentExceptionalOrder
    (rho : XiDivisorSupport) : ℕ :=
  burnolCoPoissonXiConormalOrder rho

/-- The zeta conormal order in the exceptional fibre is the actual
multiplicity of the completed-Xi divisor. -/
theorem deningerExponentExceptionalOrder_eq_xiSupportMultiplicity
    (rho : XiDivisorSupport) :
    DeningerExponentExceptionalOrder rho = xiSupportMultiplicity rho := by
  change burnolCoPoissonXiConormalOrder rho = xiSupportMultiplicity rho
  rw [burnolCoPoissonXiConormalOrder_eq_xi_analyticOrder_toNat,
    xiSupportMultiplicity_eq_analyticOrderAt_toNat]

/-- The exponent exceptional fibre always has positive order. -/
theorem deningerExponentExceptionalOrder_pos
    (rho : XiDivisorSupport) :
    0 < DeningerExponentExceptionalOrder rho := by
  rw [deningerExponentExceptionalOrder_eq_xiSupportMultiplicity]
  exact xiSupportMultiplicity_pos rho

/-- Local zeta factorization with the exponent fixed to the actual Xi
conormal order, rather than an unnamed existential order. -/
theorem exists_riemannZeta_xiConormalFactorization
    (rho : XiDivisorSupport) :
    ∃ u : ℂ → ℂ,
      AnalyticAt ℂ u (rho : ℂ) ∧
      u (rho : ℂ) ≠ 0 ∧
      ∀ᶠ s in 𝓝 (rho : ℂ),
        riemannZeta s =
          (s - (rho : ℂ)) ^ DeningerExponentExceptionalOrder rho * u s := by
  have hstrip := xi_divisor_support_re_mem_open_unit rho
  have hrhoOne : (rho : ℂ) ≠ 1 := by
    intro h
    have hlt := hstrip.2
    rw [h] at hlt
    norm_num at hlt
  have hana : AnalyticAt ℂ riemannZeta (rho : ℂ) :=
    GaloisForLFunctions.RHTower.analyticAt_riemannZeta_of_ne_one hrhoOne
  have hfinite : analyticOrderAt riemannZeta (rho : ℂ) ≠ ⊤ := by
    intro htop
    apply GaloisForLFunctions.RHTower.not_eventually_riemannZeta_eq_zero hrhoOne
    exact analyticOrderAt_eq_top.mp htop
  have horder :
      analyticOrderAt riemannZeta (rho : ℂ) =
        (DeningerExponentExceptionalOrder rho : ℕ∞) := by
    exact (ENat.coe_toNat hfinite).symm
  obtain ⟨u, hu, hu0, hfac⟩ :=
    hana.analyticOrderAt_eq_natCast.mp horder
  exact ⟨u, hu, hu0,
    hfac.mono fun s hs => by simpa [smul_eq_mul] using hs⟩

/-- Regular projective directions in the exponent blow-up chart.  The first
excluded point is the divisor face `w=0`; the second is the exceptional pole
`w=-rho`. -/
abbrev DeningerExponentExceptionalRegularDirection
    (rho : XiDivisorSupport) :=
  {w : ℂ // w ≠ 0 ∧ w + (rho : ℂ) ≠ 0}

/-- Exceptional profile on a regular projective direction. -/
def deningerExponentExceptionalProfile
    (rho : XiDivisorSupport)
    (w : DeningerExponentExceptionalRegularDirection rho) : ℂ :=
  (w.1 / (w.1 + (rho : ℂ))) ^
    DeningerExponentExceptionalOrder rho

/-- **Exponent-deformation exceptional-fibre theorem.**  Blowing up the
literal source `ζ(s)/ζ(zs)` at `(1,rho)` produces the rational exceptional
profile `(w/(w+rho))^d`, with `d` the actual Xi multiplicity. -/
theorem tendsto_deningerExponentDeformationActivation_exceptionalProfile
    (rho : XiDivisorSupport)
    (w : DeningerExponentExceptionalRegularDirection rho) :
    Tendsto
      (fun t : ℂ =>
        deningerExponentDeformationActivation (1 + t)
          (deningerExponentCollisionSource (rho : ℂ) t w.1))
      (𝓝[≠] 0)
      (𝓝 (deningerExponentExceptionalProfile rho w)) := by
  obtain ⟨u, hu, hu0, hfac⟩ :=
    exists_riemannZeta_xiConormalFactorization rho
  let source : ℂ → ℂ := fun t =>
    deningerExponentCollisionSource (rho : ℂ) t w.1
  let target : ℂ → ℂ := fun t =>
    deningerExponentCollisionTarget (rho : ℂ) t w.1
  have hsourceContinuous : Continuous source := by
    dsimp [source, deningerExponentCollisionSource]
    fun_prop
  have htargetContinuous : Continuous target := by
    dsimp [target, deningerExponentCollisionTarget,
      deningerExponentCollisionSource]
    fun_prop
  have hsourceT : Tendsto source (𝓝 0) (𝓝 (rho : ℂ)) := by
    simpa [source, deningerExponentCollisionSource] using
      hsourceContinuous.tendsto 0
  have htargetT : Tendsto target (𝓝 0) (𝓝 (rho : ℂ)) := by
    simpa [target, deningerExponentCollisionTarget,
      deningerExponentCollisionSource] using htargetContinuous.tendsto 0
  have hdenT :
      Tendsto (fun t : ℂ => w.1 + (rho : ℂ) + t * w.1)
        (𝓝 0) (𝓝 (w.1 + (rho : ℂ))) := by
    have hcontinuous : Continuous
        (fun t : ℂ => w.1 + (rho : ℂ) + t * w.1) := by
      fun_prop
    simpa using hcontinuous.tendsto 0
  have hdenNe : ∀ᶠ t in 𝓝 0,
      w.1 + (rho : ℂ) + t * w.1 ≠ 0 :=
    hdenT.eventually (eventually_ne_nhds w.2.2)
  have hsourceFac : ∀ᶠ t in 𝓝 0,
      riemannZeta (source t) =
        (source t - (rho : ℂ)) ^ DeningerExponentExceptionalOrder rho *
          u (source t) :=
    hsourceT.eventually hfac
  have htargetFac : ∀ᶠ t in 𝓝 0,
      riemannZeta (target t) =
        (target t - (rho : ℂ)) ^ DeningerExponentExceptionalOrder rho *
          u (target t) :=
    htargetT.eventually hfac
  have hprofileT :
      Tendsto
        (fun t : ℂ =>
          (w.1 / (w.1 + (rho : ℂ) + t * w.1)) ^
              DeningerExponentExceptionalOrder rho *
            (u (source t) / u (target t)))
        (𝓝[≠] 0)
        (𝓝 (deningerExponentExceptionalProfile rho w)) := by
    have hratioCoordinate :
        Tendsto (fun t : ℂ =>
            w.1 / (w.1 + (rho : ℂ) + t * w.1))
          (𝓝[≠] 0) (𝓝 (w.1 / (w.1 + (rho : ℂ)))) :=
      (tendsto_const_nhds.div
        (hdenT.mono_left nhdsWithin_le_nhds) w.2.2)
    have huT : Tendsto u (𝓝 (rho : ℂ)) (𝓝 (u (rho : ℂ))) :=
      hu.continuousAt
    have hsourceU : Tendsto (fun t : ℂ => u (source t))
        (𝓝[≠] 0) (𝓝 (u (rho : ℂ))) :=
      (huT.comp hsourceT).mono_left nhdsWithin_le_nhds
    have htargetU : Tendsto (fun t : ℂ => u (target t))
        (𝓝[≠] 0) (𝓝 (u (rho : ℂ))) :=
      (huT.comp htargetT).mono_left nhdsWithin_le_nhds
    have huRatio : Tendsto (fun t : ℂ => u (source t) / u (target t))
        (𝓝[≠] 0) (𝓝 1) := by
      have h := hsourceU.div htargetU hu0
      change Tendsto
        ((fun t : ℂ => u (source t)) / (fun t : ℂ => u (target t)))
        (𝓝[≠] 0) (𝓝 1)
      simpa only [div_self hu0] using h
    have hmul := (hratioCoordinate.pow
      (DeningerExponentExceptionalOrder rho)).mul huRatio
    simpa [deningerExponentExceptionalProfile] using hmul
  refine Tendsto.congr' ?_ hprofileT
  filter_upwards
      [self_mem_nhdsWithin,
        hsourceFac.filter_mono nhdsWithin_le_nhds,
        htargetFac.filter_mono nhdsWithin_le_nhds,
        hdenNe.filter_mono nhdsWithin_le_nhds]
      with t ht hsf htf hden
  have ht0 : t ≠ 0 := ht
  have hsourceSub : source t - (rho : ℂ) = t * w.1 := by
    exact deningerExponentCollisionSource_sub (rho : ℂ) t w.1
  have htargetSub : target t - (rho : ℂ) =
      t * (w.1 + (rho : ℂ) + t * w.1) := by
    exact deningerExponentCollisionTarget_sub (rho : ℂ) t w.1
  symm
  rw [deningerExponentDeformationActivation]
  change riemannZeta (source t) / riemannZeta (target t) = _
  rw [hsf, htf, hsourceSub, htargetSub]
  calc
    ((t * w.1) ^ DeningerExponentExceptionalOrder rho * u (source t)) /
          ((t * (w.1 + (rho : ℂ) + t * w.1)) ^
              DeningerExponentExceptionalOrder rho * u (target t)) =
        ((t * w.1) ^ DeningerExponentExceptionalOrder rho /
            (t * (w.1 + (rho : ℂ) + t * w.1)) ^
              DeningerExponentExceptionalOrder rho) *
          (u (source t) / u (target t)) := by
      rw [mul_div_mul_comm]
    _ = (((t * w.1) /
            (t * (w.1 + (rho : ℂ) + t * w.1))) ^
              DeningerExponentExceptionalOrder rho) *
          (u (source t) / u (target t)) := by
      rw [div_pow]
    _ = (w.1 / (w.1 + (rho : ℂ) + t * w.1)) ^
            DeningerExponentExceptionalOrder rho *
          (u (source t) / u (target t)) := by
      congr 2
      field_simp [ht0, hden]

/-- Raw exceptional profile, including the two singular marked directions. -/
def deningerExponentExceptionalRawProfile
    (rho : XiDivisorSupport) (w : ℂ) : ℂ :=
  (w / (w + (rho : ℂ))) ^ DeningerExponentExceptionalOrder rho

/-- The divisor-face direction is a zero of the exceptional profile. -/
@[simp]
theorem deningerExponentExceptionalRawProfile_zero
    (rho : XiDivisorSupport) :
    deningerExponentExceptionalRawProfile rho 0 = 0 := by
  rw [deningerExponentExceptionalRawProfile, zero_div,
    zero_pow (Nat.ne_of_gt (deningerExponentExceptionalOrder_pos rho))]

/-- The denominator of the exceptional profile vanishes at the marked pole
section `w=-rho`. -/
@[simp]
theorem deningerExponentExceptionalPole_denominator
    (rho : XiDivisorSupport) :
    -(rho : ℂ) + (rho : ℂ) = 0 := by
  ring

/-- Reciprocal chart of the exceptional profile near the physical endpoint
`w=∞`. -/
def deningerExponentExceptionalInfinityChart
    (rho : XiDivisorSupport) (v : ℂ) : ℂ :=
  (1 / (1 + (rho : ℂ) * v)) ^ DeningerExponentExceptionalOrder rho

/-- The physical endpoint of the exceptional fibre retains unit amplitude. -/
@[simp]
theorem deningerExponentExceptionalInfinityChart_zero
    (rho : XiDivisorSupport) :
    deningerExponentExceptionalInfinityChart rho 0 = 1 := by
  simp [deningerExponentExceptionalInfinityChart]

/-! ## Reflected exceptional poles and the Xi Green fracture -/

/-- Marked pole section of the source exceptional profile. -/
def deningerExponentExceptionalSourcePole (q : XiZeroCopy) : ℂ :=
  -(q.1 : ℂ)

/-- Marked pole section after critical-line reflection. -/
def deningerExponentExceptionalReflectedPole (q : XiZeroCopy) : ℂ :=
  -((xiZeroCopyLineConjEquiv q).1 : ℂ)

/-- **Exceptional-pole/Green identity.**  Oriented displacement of the two
marked exceptional pole sections is exactly the completed-Xi horizontal
Green fracture. -/
theorem deningerExponentExceptionalPole_displacement_eq_greenFracture
    (q : XiZeroCopy) :
    deningerExponentExceptionalReflectedPole q -
        deningerExponentExceptionalSourcePole q =
      xiNearbyPoleDualityAdjunctionFracture (q.1 : ℂ) := by
  rw [deningerExponentExceptionalReflectedPole,
    deningerExponentExceptionalSourcePole,
    xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
  have hline : ((xiZeroCopyLineConjEquiv q).1 : ℂ) =
      1 - starRingEnd ℂ (q.1 : ℂ) := rfl
  rw [hline]
  apply Complex.ext
  · simp
    ring
  · simp

/-! ## Marked Milnor constant-leg tame boundary -/

/-- Two marked branches of the reflected exceptional divisor. -/
inductive DeningerExponentExceptionalSlot
  | source
  | reflected
  deriving DecidableEq

/-- Divisor order of `(w+rho)/(w+rho#)` on each marked branch. -/
def deningerExponentExceptionalDivisorOrder :
    DeningerExponentExceptionalSlot → ℤ
  | .source => 1
  | .reflected => -1

/-- Constant-leg tame exponent.  For a local symbol `{f,6^m}` and local
order `v(f)`, the tame symbol is `(6^m)^(-v(f))`; this definition records
its exponent of `6`. -/
def deningerConstantLegTameExponent
    (v : ℤ) (m : ℕ) : ℤ :=
  -v * (m : ℤ)

/-- Marked two-slot tame boundary of the exceptional Milnor symbol
`{(w+rho)/(w+rho#),6^m}`. -/
def deningerGammaSixExceptionalTameExponent
    (m : ℕ) (slot : DeningerExponentExceptionalSlot) : ℤ :=
  deningerConstantLegTameExponent
    (deningerExponentExceptionalDivisorOrder slot) m

@[simp]
theorem deningerGammaSixExceptionalTameExponent_source
    (m : ℕ) :
    deningerGammaSixExceptionalTameExponent m .source = -(m : ℤ) := by
  simp [deningerGammaSixExceptionalTameExponent,
    deningerConstantLegTameExponent,
    deningerExponentExceptionalDivisorOrder]

@[simp]
theorem deningerGammaSixExceptionalTameExponent_reflected
    (m : ℕ) :
    deningerGammaSixExceptionalTameExponent m .reflected = (m : ℤ) := by
  simp [deningerGammaSixExceptionalTameExponent,
    deningerConstantLegTameExponent,
    deningerExponentExceptionalDivisorOrder]

/-- Unit `6` used by the constant leg of the exceptional Milnor symbol. -/
def deningerGammaSixUnit : ℝˣ :=
  Units.mk0 6 (by norm_num)

/-- Unit realization of an exponent in the Gamma-six lattice. -/
def deningerGammaSixExponentUnit (k : ℤ) : ℝˣ :=
  deningerGammaSixUnit ^ k

/-- Actual local tame unit on one marked exceptional branch. -/
def deningerGammaSixExceptionalTameUnit
    (m : ℕ) (slot : DeningerExponentExceptionalSlot) : ℝˣ :=
  deningerGammaSixExponentUnit
    (deningerGammaSixExceptionalTameExponent m slot)

/-- Source-branch tame symbol is `6^{-m}`. -/
@[simp]
theorem deningerGammaSixExceptionalTameUnit_source
    (m : ℕ) :
    deningerGammaSixExceptionalTameUnit m .source =
      deningerGammaSixUnit ^ (-(m : ℤ)) := by
  simp [deningerGammaSixExceptionalTameUnit,
    deningerGammaSixExponentUnit]

/-- Reflected-branch tame symbol is `6^m`. -/
@[simp]
theorem deningerGammaSixExceptionalTameUnit_reflected
    (m : ℕ) :
    deningerGammaSixExceptionalTameUnit m .reflected =
      deningerGammaSixUnit ^ (m : ℤ) := by
  simp [deningerGammaSixExceptionalTameUnit,
    deningerGammaSixExponentUnit]

/-- Tame reciprocity on the paired exceptional line: the product of the two
local constant-leg symbols is one.  This is multiplicative neutrality, not
additive Stokes annihilation. -/
theorem deningerGammaSixExceptionalTameUnit_product
    (m : ℕ) :
    deningerGammaSixExceptionalTameUnit m .source *
        deningerGammaSixExceptionalTameUnit m .reflected = 1 := by
  rw [deningerGammaSixExceptionalTameUnit_source,
    deningerGammaSixExceptionalTameUnit_reflected]
  rw [← zpow_add]
  simp

/-! ## Horizontal reader and physical Gamma coefficient -/

/-- Horizontal Deninger character on the Gamma-six exponent lattice. -/
def deningerGammaSixHorizontalCharacter
    (s : ℂ) (k : ℤ) : ℝ :=
  deningerHalfDensityMateGain 6 s ^ k

/-- Oriented readout of the two marked exceptional tame branches. -/
def deningerGammaSixExceptionalTameReader
    (m : ℕ) (s : ℂ) : ℝ :=
  deningerGammaSixHorizontalCharacter s
      (deningerGammaSixExceptionalTameExponent m .reflected) -
    deningerGammaSixHorizontalCharacter s
      (deningerGammaSixExceptionalTameExponent m .source)

/-- The half-density mate gain respects the ordinary power clock `6^m`. -/
theorem deningerHalfDensityMateGain_six_pow
    (m : ℕ) (s : ℂ) :
    deningerHalfDensityMateGain (6 ^ m) s =
      deningerHalfDensityMateGain 6 s ^ m := by
  induction m with
  | zero =>
      simp [deningerHalfDensityMateGain]
  | succ m ih =>
      rw [pow_succ,
        deningerHalfDensityMateGain_mul
          (Nat.pow_pos (by norm_num : 0 < 6)) (by norm_num),
        ih, pow_succ]

/-- **Tame/Gamma-six comparison.**  The marked tame boundary at grade `m`
is read as the actual radial mate curvature of the ordinary degree `6^m`. -/
theorem deningerGammaSixExceptionalTameReader_eq_mateCurvature
    (m : ℕ) (s : ℂ) :
    deningerGammaSixExceptionalTameReader m s =
      deningerTensorSquareRadialMateCurvature (6 ^ m) s := by
  calc
    deningerGammaSixExceptionalTameReader m s =
        deningerHalfDensityMateGain 6 s ^ m -
          (deningerHalfDensityMateGain 6 s ^ m)⁻¹ := by
      simp [deningerGammaSixExceptionalTameReader,
        deningerGammaSixHorizontalCharacter]
    _ = deningerHalfDensityMateGain (6 ^ m) s -
          (deningerHalfDensityMateGain (6 ^ m) s)⁻¹ := by
      rw [deningerHalfDensityMateGain_six_pow]
    _ = deningerTensorSquareRadialMateCurvature (6 ^ m) s :=
      deningerHalfDensityMateGain_sub_inv_eq_mateCurvature
        (Nat.pow_pos (by norm_num : 0 < 6)) s

/-- At grade one, the actual ordered `(2,3)` Gamma/Calderon--Witt boundary
coefficient is the positive calibration of the exceptional tame readout. -/
theorem deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_exceptionalTameReader
    (q : XiZeroCopy) :
    deningerCalderonWittBaseGammaBoundaryDefectCoefficient q =
      ((deningerCalderonWittBaseGammaMateCalibration *
        deningerGammaSixExceptionalTameReader 1 (q.1 : ℂ) : ℝ) : ℂ) := by
  rw [deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_tensorSquareMateCurvature,
    deningerGammaSixExceptionalTameReader_eq_mateCurvature]
  norm_num

/-! ## Completed Xi and Calderon--Witt incidence landings -/

/-- Finite-support completed-Xi vector carrying the oriented exceptional
pole displacement. -/
def deningerExponentExceptionalGreenXiVector
    (q : XiZeroCopy) : DeningerArithmeticCompletedH1 :=
  lp.single 2 q
    (deningerExponentExceptionalReflectedPole q -
      deningerExponentExceptionalSourcePole q)

/-- Coefficient-faithful Calderon--Witt incidence landing of the exceptional
Green displacement. -/
def deningerExponentExceptionalGreenIncidence
    (p r : Nat.Primes) (hpr : p ≠ r) (q : XiZeroCopy) :
    DeningerCalderonWittCrossPrimeXiIncidenceCompletion p r hpr :=
  deningerCompletedXiToCrossPrimeIncidenceCompletion p r hpr
    (deningerExponentExceptionalGreenXiVector q)

/-- Decoding the exceptional Green landing recovers the actual Xi fracture
times the fixed nonzero incidence witness. -/
theorem deningerExponentExceptionalGreenIncidence_sourceValue
    (p r : Nat.Primes) (hpr : p ≠ r) (q : XiZeroCopy) :
    deningerCalderonWittCrossPrimeXiIncidenceCompletionSourceValue
        p r hpr q
        (deningerExponentExceptionalGreenIncidence p r hpr q) =
      xiNearbyPoleDualityAdjunctionFracture (q.1 : ℂ) •
        deningerCalderonWittCrossPrimeGammaWitness hpr := by
  rw [deningerExponentExceptionalGreenIncidence,
    deningerCalderonWittCrossPrimeXiIncidenceCompletionSourceValue_xi,
    deningerExponentExceptionalGreenXiVector]
  simp [deningerExponentExceptionalPole_displacement_eq_greenFracture]

/-- Finite-support completed-Xi vector carrying the physical tame readout at
ordinary exponent grade `m`. -/
def deningerGammaSixExceptionalTameXiVector
    (q : XiZeroCopy) (m : ℕ) : DeningerArithmeticCompletedH1 :=
  lp.single 2 q
    ((deningerGammaSixExceptionalTameReader m (q.1 : ℂ) : ℝ) : ℂ)

/-- Calderon--Witt incidence landing of the physical exceptional tame
readout. -/
def deningerGammaSixExceptionalTameIncidence
    (p r : Nat.Primes) (hpr : p ≠ r)
    (q : XiZeroCopy) (m : ℕ) :
    DeningerCalderonWittCrossPrimeXiIncidenceCompletion p r hpr :=
  deningerCompletedXiToCrossPrimeIncidenceCompletion p r hpr
    (deningerGammaSixExceptionalTameXiVector q m)

/-- Decoding the tame landing recovers the exact degree-`6^m` physical
radial coefficient times the fixed nonzero incidence witness. -/
theorem deningerGammaSixExceptionalTameIncidence_sourceValue
    (p r : Nat.Primes) (hpr : p ≠ r)
    (q : XiZeroCopy) (m : ℕ) :
    deningerCalderonWittCrossPrimeXiIncidenceCompletionSourceValue
        p r hpr q
        (deningerGammaSixExceptionalTameIncidence p r hpr q m) =
      ((deningerTensorSquareRadialMateCurvature
          (6 ^ m) (q.1 : ℂ) : ℝ) : ℂ) •
        deningerCalderonWittCrossPrimeGammaWitness hpr := by
  rw [deningerGammaSixExceptionalTameIncidence,
    deningerCalderonWittCrossPrimeXiIncidenceCompletionSourceValue_xi,
    deningerGammaSixExceptionalTameXiVector,
    deningerGammaSixExceptionalTameReader_eq_mateCurvature]
  simp

end

end RHTower
