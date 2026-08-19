import GaloisForLFunctions.RHTower.SuzukiTaCharacteristicEntire
import GaloisForLFunctions.RHTower.SuzukiFiniteApertureHermiteBiehler
import GaloisForLFunctions.RHTower.SuzukiXiFirstDefectJet
import GaloisForLFunctions.RHTower.SuzukiV2CharacteristicTarget

/-!
# Actual Suzuki v2 projective characteristics

Suzuki v2's fitted one-angle entire normalization cannot converge compact-open on all of `ℂ` to
its meromorphic target.  This module constructs the pole-compatible replacement directly from the
literal self-adjoint characteristic functions at extension angles `0` and `π`:

`Fₐ = -Wₐ^π / (c Wₐ^0 - Wₐ^π)`,

where `c` is the unconditionally positive Xi--Donoghue scale.  No fitted gauge occurs.

The actual all-angle spectral theorem makes the associated Livšic coordinate Schur on the upper
half-plane.  The fixed Möbius transform above therefore has a sharp aperture-independent
denominator gap `2 * min 1 c`, is holomorphic there, and is uniformly bounded.  Sequential Montel
then gives an unconditional cofinal subsequential limit for the literal `Fₐ` family.

Finally, an unconditional cross-multiplied identity identifies the divisor-faithful global
projective coordinate `(XiC' + i c XiC : XiC' - i c XiC)` with Suzuki v2's target pair
`(XiC : XiC + i XiC')`.  It avoids totalized logarithmic derivatives at Xi zeros.  Identifying the
finite normal-family limit with this global pair remains the RH-strength source problem.
-/

open Complex Metric Set Filter Topology

noncomputable section
namespace RHTower

open GaloisForLFunctions.RHTower

/-- Fixed Möbius map taking a normalized Suzuki Livšic coordinate to the v2 chart. -/
def suzukiV2MobiusTransform (c : ℝ) (w : ℂ) : ℂ :=
  (1 - w) / (((1 + c : ℝ) : ℂ) + (((c - 1 : ℝ) : ℂ) * w))

/-- Sharp closed-disk lower bound for the v2 Möbius denominator. -/
theorem two_mul_min_le_norm_suzukiV2MobiusDenominator
    (c : ℝ) (hc : 0 < c) (w : ℂ) (hw : ‖w‖ ≤ 1) :
    2 * min 1 c ≤
      ‖(((1 + c : ℝ) : ℂ) + (((c - 1 : ℝ) : ℂ) * w))‖ := by
  have hrev := norm_sub_norm_le
    (((1 + c : ℝ) : ℂ)) (-(((c - 1 : ℝ) : ℂ) * w))
  have hconst : ‖(((1 + c : ℝ) : ℂ))‖ = 1 + c := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    linarith
  have hcoef : ‖(((c - 1 : ℝ) : ℂ))‖ = |c - 1| := by
    exact Complex.norm_real _
  have hmul : |c - 1| * ‖w‖ ≤ |c - 1| := by
    simpa using mul_le_mul_of_nonneg_left hw (abs_nonneg (c - 1))
  have hbase : 1 + c - |c - 1| ≤
      ‖(((1 + c : ℝ) : ℂ) + (((c - 1 : ℝ) : ℂ) * w))‖ := by
    rw [hconst, norm_neg, norm_mul, hcoef] at hrev
    rw [sub_neg_eq_add] at hrev
    linarith
  have hid : 1 + c - |c - 1| = 2 * min 1 c := by
    by_cases h : c ≤ 1
    · rw [min_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · have h1c : 1 ≤ c := le_of_not_ge h
      rw [min_eq_left h1c, abs_of_nonneg (sub_nonneg.mpr h1c)]
      ring
  linarith

/-- A positive Donoghue scale makes the v2 transform pole-free on the closed Schur disk. -/
theorem suzukiV2MobiusDenominator_ne_zero
    (c : ℝ) (hc : 0 < c) (w : ℂ) (hw : ‖w‖ ≤ 1) :
    (((1 + c : ℝ) : ℂ) + (((c - 1 : ℝ) : ℂ) * w)) ≠ 0 := by
  intro hzero
  have h := two_mul_min_le_norm_suzukiV2MobiusDenominator c hc w hw
  rw [hzero, norm_zero] at h
  have hmin : 0 < min 1 c := lt_min (by norm_num) hc
  linarith

/-- Aperture-free bound for the v2 transform of every Schur coordinate. -/
theorem norm_suzukiV2MobiusTransform_le
    (c : ℝ) (hc : 0 < c) (w : ℂ) (hw : ‖w‖ ≤ 1) :
    ‖suzukiV2MobiusTransform c w‖ ≤ 1 / min 1 c := by
  have hm : 0 < min 1 c := lt_min (by norm_num) hc
  have hden := two_mul_min_le_norm_suzukiV2MobiusDenominator c hc w hw
  have hnum : ‖1 - w‖ ≤ 2 := by
    calc
      ‖1 - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ 2 := by
        simp only [norm_one]
        linarith
  rw [suzukiV2MobiusTransform, norm_div]
  apply (div_le_iff₀ (lt_of_lt_of_le (by positivity : 0 < 2 * min 1 c) hden)).2
  calc
    ‖1 - w‖ ≤ 2 := hnum
    _ = (1 / min 1 c) * (2 * min 1 c) := by field_simp
    _ ≤ (1 / min 1 c) *
        ‖(((1 + c : ℝ) : ℂ) + (((c - 1 : ℝ) : ℂ) * w))‖ := by
      exact mul_le_mul_of_nonneg_left hden (by positivity)

/-- `Aₐ` coordinate of the literal Suzuki characteristic pencil. -/
def suzukiTaV2CharacteristicA (a : SuzukiPositiveAperture) (z : ℂ) : ℂ :=
  (z - I) * suzukiTaPhysicalFourier a (suzukiTaPlusDeficiency a) z

/-- `Eₐ` coordinate of the literal Suzuki characteristic pencil. -/
def suzukiTaV2CharacteristicE (a : SuzukiPositiveAperture) (z : ℂ) : ℂ :=
  (z + I) * suzukiTaPhysicalFourier a (suzukiTaMinusDeficiency a) z

/-- Exact identification of Suzuki's real-angle characteristic with the unitary pencil. -/
theorem suzukiTaCharacteristic_eq_v2Pencil
    (a : SuzukiPositiveAperture) (theta : ℝ) (z : ℂ) :
    suzukiTaCharacteristic a theta z =
      suzukiCharacteristicPencil
        (suzukiTaV2CharacteristicA a) (suzukiTaV2CharacteristicE a)
        (suzukiTaBoundaryPhase theta) z := by
  rw [suzukiTaCharacteristic_eq_fourier]
  simp only [suzukiTaCharacteristicFourier, suzukiCharacteristicPencil,
    suzukiTaV2CharacteristicA, suzukiTaV2CharacteristicE]
  ring

theorem differentiable_suzukiTaV2CharacteristicA (a : SuzukiPositiveAperture) :
    Differentiable ℂ (suzukiTaV2CharacteristicA a) := by
  exact (differentiable_id.sub_const I).mul
    (differentiable_suzukiTaPhysicalFourier a (suzukiTaPlusDeficiency a))

theorem differentiable_suzukiTaV2CharacteristicE (a : SuzukiPositiveAperture) :
    Differentiable ℂ (suzukiTaV2CharacteristicE a) := by
  exact (differentiable_id.add_const I).mul
    (differentiable_suzukiTaPhysicalFourier a (suzukiTaMinusDeficiency a))

@[simp] theorem suzukiTaV2CharacteristicA_I (a : SuzukiPositiveAperture) :
    suzukiTaV2CharacteristicA a I = 0 := by
  simp [suzukiTaV2CharacteristicA]

/-- Suzuki's literal all-angle spectral reality theorem supplies the generic pencil predicate. -/
theorem suzukiTaV2_allAngleRealZeros (a : SuzukiPositiveAperture) :
    SuzukiAllAngleRealZeros
      (suzukiTaV2CharacteristicA a) (suzukiTaV2CharacteristicE a) := by
  intro u hu z hz
  obtain ⟨theta, htheta⟩ := (Complex.norm_eq_one_iff u).mp hu
  have hphase : suzukiTaBoundaryPhase theta = u := by
    rw [suzukiTaBoundaryPhase]
    convert htheta using 1
    ring
  apply suzukiTaCharacteristic_zero_im_eq_zero a theta z
  rw [suzukiTaCharacteristic_eq_v2Pencil, hphase]
  exact hz

/-- Actual normalized finite-aperture Livšic coordinate. -/
def suzukiTaV2Livsic (a : SuzukiPositiveAperture) : ℂ → ℂ :=
  suzukiLivsicQuotient (suzukiTaV2CharacteristicA a) (suzukiTaV2CharacteristicE a)

/-- Actual finite-aperture Livšic coordinates are strictly Schur on the upper half-plane. -/
theorem norm_suzukiTaV2Livsic_lt_one
    (a : SuzukiPositiveAperture) {z : ℂ} (hz : 0 < z.im) :
    ‖suzukiTaV2Livsic a z‖ < 1 := by
  exact norm_suzukiLivsicQuotient_lt_one
    (differentiable_suzukiTaV2CharacteristicA a).continuous
    (differentiable_suzukiTaV2CharacteristicE a).continuous
    (suzukiTaV2CharacteristicA_I a) (suzukiTaV2_allAngleRealZeros a) hz

/-- Literal pole-compatible Suzuki v2 characteristic built from self-adjoint angles `0` and `π`. -/
def suzukiTaV2ProjectiveCharacteristic (a : SuzukiPositiveAperture) (z : ℂ) : ℂ :=
  -suzukiTaCharacteristic a Real.pi z /
    (((xiHedenmalmDonoghueScale : ℂ) * suzukiTaCharacteristic a 0 z) -
      suzukiTaCharacteristic a Real.pi z)

theorem suzukiTaCharacteristic_zeroAngle
    (a : SuzukiPositiveAperture) (z : ℂ) :
    suzukiTaCharacteristic a 0 z =
      suzukiTaV2CharacteristicA a z + suzukiTaV2CharacteristicE a z := by
  rw [suzukiTaCharacteristic_eq_v2Pencil]
  simp [suzukiTaBoundaryPhase, suzukiCharacteristicPencil]

theorem suzukiTaCharacteristic_piAngle
    (a : SuzukiPositiveAperture) (z : ℂ) :
    suzukiTaCharacteristic a Real.pi z =
      suzukiTaV2CharacteristicA a z - suzukiTaV2CharacteristicE a z := by
  rw [suzukiTaCharacteristic_eq_v2Pencil]
  simp only [suzukiCharacteristicPencil]
  rw [show suzukiTaBoundaryPhase Real.pi = (-1 : ℂ) by
    rw [suzukiTaBoundaryPhase]
    simpa [mul_comm] using Complex.exp_pi_mul_I]
  ring

/-- The raw two-angle denominator factors through `Eₐ` and the fixed Möbius denominator. -/
theorem suzukiTaV2ProjectiveDenominator_factor
    (a : SuzukiPositiveAperture) {z : ℂ}
    (hE : suzukiTaV2CharacteristicE a z ≠ 0) :
    (((xiHedenmalmDonoghueScale : ℂ) * suzukiTaCharacteristic a 0 z) -
      suzukiTaCharacteristic a Real.pi z) =
    suzukiTaV2CharacteristicE a z *
      ((((1 + xiHedenmalmDonoghueScale : ℝ) : ℂ)) +
        (((xiHedenmalmDonoghueScale - 1 : ℝ) : ℂ) * suzukiTaV2Livsic a z)) := by
  rw [suzukiTaCharacteristic_zeroAngle, suzukiTaCharacteristic_piAngle,
    suzukiTaV2Livsic, suzukiLivsicQuotient]
  field_simp [hE]
  push_cast
  ring

/-- The literal projective characteristic has no upper-half-plane denominator zero. -/
theorem suzukiTaV2ProjectiveDenominator_ne_zero
    (a : SuzukiPositiveAperture) {z : ℂ} (hz : 0 < z.im) :
    (((xiHedenmalmDonoghueScale : ℂ) * suzukiTaCharacteristic a 0 z) -
      suzukiTaCharacteristic a Real.pi z) ≠ 0 := by
  have hE : suzukiTaV2CharacteristicE a z ≠ 0 :=
    suzukiLivsic_denominator_ne_zero
      (differentiable_suzukiTaV2CharacteristicA a).continuous
      (differentiable_suzukiTaV2CharacteristicE a).continuous
      (suzukiTaV2CharacteristicA_I a) (suzukiTaV2_allAngleRealZeros a) hz
  have htheta := (norm_suzukiTaV2Livsic_lt_one a hz).le
  have hmob := suzukiV2MobiusDenominator_ne_zero
    xiHedenmalmDonoghueScale xiHedenmalmDonoghueScale_pos
    (suzukiTaV2Livsic a z) htheta
  rw [suzukiTaV2ProjectiveDenominator_factor a hE]
  exact mul_ne_zero hE hmob

/-- Exact normalized-Livšic formula for the literal two-angle characteristic. -/
theorem suzukiTaV2ProjectiveCharacteristic_eq_mobius
    (a : SuzukiPositiveAperture) {z : ℂ} (hz : 0 < z.im) :
    suzukiTaV2ProjectiveCharacteristic a z =
      suzukiV2MobiusTransform xiHedenmalmDonoghueScale (suzukiTaV2Livsic a z) := by
  have hE : suzukiTaV2CharacteristicE a z ≠ 0 :=
    suzukiLivsic_denominator_ne_zero
      (differentiable_suzukiTaV2CharacteristicA a).continuous
      (differentiable_suzukiTaV2CharacteristicE a).continuous
      (suzukiTaV2CharacteristicA_I a) (suzukiTaV2_allAngleRealZeros a) hz
  have htheta := (norm_suzukiTaV2Livsic_lt_one a hz).le
  have hmob := suzukiV2MobiusDenominator_ne_zero
    xiHedenmalmDonoghueScale xiHedenmalmDonoghueScale_pos
    (suzukiTaV2Livsic a z) htheta
  rw [suzukiTaV2ProjectiveCharacteristic,
    suzukiTaV2ProjectiveDenominator_factor a hE,
    suzukiTaCharacteristic_piAngle, suzukiV2MobiusTransform,
    suzukiTaV2Livsic, suzukiLivsicQuotient]
  field_simp [hE, hmob]
  ring

/-- The actual two-angle quotient is globally meromorphic. -/
theorem meromorphicOn_suzukiTaV2ProjectiveCharacteristic
    (a : SuzukiPositiveAperture) :
    MeromorphicOn (suzukiTaV2ProjectiveCharacteristic a) Set.univ := by
  have hW0 : AnalyticOnNhd ℂ (suzukiTaCharacteristic a 0) Set.univ :=
    (differentiable_suzukiTaCharacteristic a 0).differentiableOn.analyticOnNhd isOpen_univ
  have hWpi : AnalyticOnNhd ℂ (suzukiTaCharacteristic a Real.pi) Set.univ :=
    (differentiable_suzukiTaCharacteristic a Real.pi).differentiableOn.analyticOnNhd isOpen_univ
  have hmer : MeromorphicOn
      (fun z => -suzukiTaCharacteristic a Real.pi z /
        (((xiHedenmalmDonoghueScale : ℂ) * suzukiTaCharacteristic a 0 z) -
          suzukiTaCharacteristic a Real.pi z)) Set.univ :=
    hWpi.neg.meromorphicOn.div
      (((analyticOnNhd_const.mul hW0).sub hWpi).meromorphicOn)
  change MeromorphicOn
    (fun z => -suzukiTaCharacteristic a Real.pi z /
      (((xiHedenmalmDonoghueScale : ℂ) * suzukiTaCharacteristic a 0 z) -
        suzukiTaCharacteristic a Real.pi z)) Set.univ
  exact hmer

/-- The globally meromorphic actual characteristic is holomorphic on the upper half-plane. -/
theorem differentiableOn_suzukiTaV2ProjectiveCharacteristic_upperHalfPlane
    (a : SuzukiPositiveAperture) :
    DifferentiableOn ℂ (suzukiTaV2ProjectiveCharacteristic a) {z : ℂ | 0 < z.im} := by
  intro z hz
  have hW0 := differentiable_suzukiTaCharacteristic a 0
  have hWpi := differentiable_suzukiTaCharacteristic a Real.pi
  exact ((hWpi.neg z).div
    ((((differentiable_const (c := (xiHedenmalmDonoghueScale : ℂ))).mul hW0).sub hWpi) z)
      (suzukiTaV2ProjectiveDenominator_ne_zero a hz)).differentiableWithinAt

/-- Aperture-uniform upper-half-plane bound for the literal `Fₐ`. -/
theorem norm_suzukiTaV2ProjectiveCharacteristic_le
    (a : SuzukiPositiveAperture) {z : ℂ} (hz : 0 < z.im) :
    ‖suzukiTaV2ProjectiveCharacteristic a z‖ ≤
      1 / min 1 xiHedenmalmDonoghueScale := by
  rw [suzukiTaV2ProjectiveCharacteristic_eq_mobius a hz]
  exact norm_suzukiV2MobiusTransform_le
    xiHedenmalmDonoghueScale xiHedenmalmDonoghueScale_pos
    (suzukiTaV2Livsic a z) (norm_suzukiTaV2Livsic_lt_one a hz).le

/-- Actual `Fₐ` normality on every ball contained in the upper half-plane. -/
theorem exists_suzukiTaV2ProjectiveCharacteristic_montel_subseq_on_upperBall
    (a : ℕ → SuzukiPositiveAperture) {c : ℂ} {R r : ℝ}
    (hr0 : 0 < r) (hrR : r < R / 2)
    (hupper : ∀ z ∈ ball c R, 0 < z.im) :
    ∃ (phi : ℕ → ℕ) (g : ℂ → ℂ), StrictMono phi ∧
      TendstoUniformlyOn
        (fun k => suzukiTaV2ProjectiveCharacteristic (a (phi k))) g atTop
        (closedBall c r) ∧
      DifferentiableOn ℂ g (ball c r) := by
  refine Bottcher.montel_subseq
    (F := fun n => suzukiTaV2ProjectiveCharacteristic (a n))
    (C := 1 / min 1 xiHedenmalmDonoghueScale)
    hr0 hrR ?_ ?_
  · intro n
    exact (differentiableOn_suzukiTaV2ProjectiveCharacteristic_upperHalfPlane (a n)).mono
      hupper
  · intro n z hz
    exact norm_suzukiTaV2ProjectiveCharacteristic_le (a n) (hupper z hz)

private theorem upper_ball_I_half (z : ℂ) (hz : z ∈ ball I (1 / 2 : ℝ)) :
    0 < z.im := by
  have hdist : ‖z - I‖ < 1 / 2 := by
    simpa [mem_ball, dist_eq] using hz
  have himnorm : |(z - I).im| ≤ ‖z - I‖ := abs_im_le_norm (z - I)
  have himabs : |z.im - 1| < 1 / 2 := by
    rw [Complex.sub_im, Complex.I_im] at himnorm
    linarith
  linarith [(abs_lt.mp himabs).1]

/-- Any sequence of literal Suzuki projective characteristics has a locally uniform subsequence
on a fixed upper-half-plane ball. -/
theorem exists_suzukiTaV2ProjectiveCharacteristic_montel_subseq
    (a : ℕ → SuzukiPositiveAperture) :
    ∃ (phi : ℕ → ℕ) (g : ℂ → ℂ), StrictMono phi ∧
      TendstoUniformlyOn
        (fun k => suzukiTaV2ProjectiveCharacteristic (a (phi k))) g atTop
        (closedBall I (1 / 8 : ℝ)) ∧
      DifferentiableOn ℂ g (ball I (1 / 8 : ℝ)) := by
  exact exists_suzukiTaV2ProjectiveCharacteristic_montel_subseq_on_upperBall
    a (c := I) (R := (1 / 2 : ℝ)) (r := (1 / 8 : ℝ))
    (by norm_num) (by norm_num) upper_ball_I_half

/-- Canonical cofinal positive-aperture schedule. -/
def suzukiTaV2CanonicalAperture (n : ℕ) : SuzukiPositiveAperture :=
  ⟨(n : ℝ) + 1, by positivity⟩

theorem tendsto_suzukiTaV2CanonicalAperture_atTop :
    Tendsto (fun n => (suzukiTaV2CanonicalAperture n).1) atTop atTop := by
  exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds

/-- Unconditional cofinal convergence construction for actual Suzuki characteristics.  Along a
strictly increasing aperture subsequence, the literal `Fₐ` converge uniformly on a fixed compact
upper-half-plane ball to a holomorphic limit. -/
theorem exists_suzukiTaV2CanonicalCofinalProjectiveLimit :
    ∃ (phi : ℕ → ℕ) (g : ℂ → ℂ), StrictMono phi ∧
      Tendsto (fun k => (suzukiTaV2CanonicalAperture (phi k)).1) atTop atTop ∧
      TendstoUniformlyOn
        (fun k => suzukiTaV2ProjectiveCharacteristic
          (suzukiTaV2CanonicalAperture (phi k))) g atTop
        (closedBall I (1 / 8 : ℝ)) ∧
      DifferentiableOn ℂ g (ball I (1 / 8 : ℝ)) := by
  obtain ⟨phi, g, hphi, hconv, hg⟩ :=
    exists_suzukiTaV2ProjectiveCharacteristic_montel_subseq suzukiTaV2CanonicalAperture
  exact ⟨phi, g, hphi,
    tendsto_suzukiTaV2CanonicalAperture_atTop.comp hphi.tendsto_atTop, hconv, hg⟩

/-- Numerator of the divisor-faithful normalized global Livšic coordinate. -/
def xiHedenmalmAlgebraicLivsicNumerator (z : ℂ) : ℂ :=
  deriv XiC z + I * (xiHedenmalmDonoghueScale : ℂ) * XiC z

/-- Denominator of the divisor-faithful normalized global Livšic coordinate. -/
def xiHedenmalmAlgebraicLivsicDenominator (z : ℂ) : ℂ :=
  deriv XiC z - I * (xiHedenmalmDonoghueScale : ℂ) * XiC z

/-- Algebraic global Livšic chart, retaining the Xi divisor before scalar division. -/
def xiHedenmalmAlgebraicLivsicTarget (z : ℂ) : ℂ :=
  xiHedenmalmAlgebraicLivsicNumerator z / xiHedenmalmAlgebraicLivsicDenominator z

/-- Divisor-faithful target identity.  Applying the v2 Möbius transform projectively to
`(XiC' + i c XiC : XiC' - i c XiC)` gives exactly
`(XiC : XiC + i XiC')`.  No division, zero-free premise, or RH is used. -/
theorem xiHedenmalmAlgebraicLivsic_v2_projective_identity (z : ℂ) :
    (xiHedenmalmAlgebraicLivsicDenominator z -
        xiHedenmalmAlgebraicLivsicNumerator z) *
        xiHedenmalmDeBrangesE z =
      XiC z *
        (((1 + xiHedenmalmDonoghueScale : ℝ) : ℂ) *
            xiHedenmalmAlgebraicLivsicDenominator z +
          ((xiHedenmalmDonoghueScale - 1 : ℝ) : ℂ) *
            xiHedenmalmAlgebraicLivsicNumerator z) := by
  rw [xiHedenmalmAlgebraicLivsicNumerator,
    xiHedenmalmAlgebraicLivsicDenominator, xiHedenmalmDeBrangesE]
  push_cast
  ring_nf
  rw [pow_two, Complex.I_mul_I]
  ring

end RHTower
