import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMMixedQuadraticCurrent
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLeftHorizonFactor

/-!
Original left-QNM radial weights of the actual mixed particular correction.
Both original radial normalizations give exact elementary blocks at the prescribed
frequency. The source equations separate the two angular resolvents and classify
the surviving full square/contact overlap: its radial zero set has at most one
point for unit amplitude. The local Green balance retains both boundary currents
and the full triple-source density.

This excludes pointwise removal by radial weights alone. It does not identify
the complete causal correction, cancel the other channels or prove extinction.
-/

open Complex Set Filter Topology
open scoped ContDiff BigOperators
namespace RHTower.D4BMMixedRadialOverlap
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMModularCore D4BMJointSource D4BMJointWave D4BMPhysicalModeAction
open D4BMGlobalAngularResponse D4BMLaplaceRadial D4BMMixedQuadraticCurrent
open D4BMFundamentalScalarMetric D4BMMetricReconstruction
noncomputable section
set_option autoImplicit false

private theorem roots (q : XiZeroCopy) (side : Bool) :
    physicalFundamentalFrequency q side=-3/2-I*physicalRadialFrequency q ∨
    physicalFundamentalFrequency q side=-3/2+I*physicalRadialFrequency q := by
  rw [physicalFundamentalFrequency_connection_root]
  cases side <;> simp

/-- The original independent left mode, with both original radial normalizations. -/
theorem profile_value (q : XiZeroCopy) (side outer : Bool) (t : Iio (0:ℝ)) :
    D4BMLeftModeRadialEquation.profile q side outer t=
      power (physicalFundamentalFrequency q side/2) (horizonCoordinate t)*(radialUnit t:ℂ) := by
  have h : D4BMLeftModeRadialEquation.profile q side outer t=
      power (physicalFundamentalFrequency q side/2) (horizonCoordinate t)*power (1/2) (1-horizonCoordinate t) := by
    cases outer
    · change horizon _ _ _ = _
      rw [horizon_eq_normalizable_fundamental _ _ (physicalFundamentalFrequency_strip q side).1
        (roots q side) (horizonCoordinate_interior t t.2)]
      exact normalizable_fundamental_value _ _ (roots q side) _
    · exact normalizable_fundamental_value _ _ (roots q side) _
  rw [h,power_half_eq_sqrt (sub_nonneg.mpr (horizonCoordinate_interior t t.2).2.le),
    ← radialUnit_eq_sqrt t t.2]

/-- The first derivative is derived from the actual continued profile. -/
theorem profileFirst_eq (q : XiZeroCopy) (side outer : Bool) (t : Iio (0:ℝ)) :
    D4BMLeftModeRadialEquation.profileFirst q side outer t=
      (physicalFundamentalFrequency q side+1-(tortoiseRadius t:ℂ)^(2 : ℕ))/(tortoiseRadius t:ℂ)*
        D4BMLeftModeRadialEquation.profile q side outer t := by
  have hz := horizonCoordinate_interior t t.2
  have hp := ((power_derivatives (physicalFundamentalFrequency q side/2) hz.1).1.scomp (t:ℝ)
    (horizonCoordinate_hasDerivAt t)).mul (radialUnit_hasDerivAt t).ofReal_comp
  have hh : HasDerivAt (D4BMLeftModeRadialEquation.profile q side outer)
      ((coordinateFirst t:ℂ)*powerFirst (physicalFundamentalFrequency q side/2) (horizonCoordinate t)*(radialUnit t:ℂ)+
        power (physicalFundamentalFrequency q side/2) (horizonCoordinate t)*((radialUnit t:ℂ)^(2 : ℕ)-1)) t := by
    apply HasDerivAt.congr_of_eventuallyEq (by simpa only [Complex.real_smul,Complex.ofReal_sub,
      Complex.ofReal_pow,Complex.ofReal_one] using! hp)
    filter_upwards [Iio_mem_nhds t.2] with v hv
    exact profile_value q side outer ⟨v,hv⟩
  rw [(D4BMLeftModeRadialEquation.profile_derivatives q side outer t).1.unique hh,profile_value]
  have hz0 : (horizonCoordinate t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hz.1.ne'
  have hr0 : (tortoiseRadius t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (lt_trans zero_lt_one (tortoiseRadius_exterior t t.2)).ne'
  dsimp only [powerFirst,coordinateFirst]
  push_cast
  rw [radialUnit_inverse_radius]
  push_cast
  field_simp [hz0,hr0]
  ring

/-- Exact physical dispersion at the original frequency. -/
theorem reader_eigenvalue (q : XiZeroCopy) (side : Bool) :
    D4BMLeftModeRadialEquation.eigenvalue q=
      (physicalFundamentalFrequency q side+1)*(physicalFundamentalFrequency q side+2) := by
  have h := D4BMLeftHorizonFactor.physical_angular_eigenvalue q side
  change physicalAngularParameter q^(2 : ℕ)-1/4=_
  linear_combination h

/-- The original left temporal and radial-curl blocks become elementary at the actual QNM. -/
theorem left_blocks (q : XiZeroCopy) (side outer : Bool) (t : Iio (0:ℝ)) :
    let w := physicalFundamentalFrequency q side
    let r := (tortoiseRadius t:ℂ)
    let g := D4BMLeftModeRadialEquation.profile q side outer t
    let dg := D4BMLeftModeRadialEquation.profileFirst q side outer t
    leftTime r g dg=w*g ∧ leftCurl r (D4BMLeftModeRadialEquation.eigenvalue q) g dg=w*(w+1)*g/r := by
  dsimp only
  rw [profileFirst_eq,reader_eigenvalue q side]
  have hr : (tortoiseRadius t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (lt_trans zero_lt_one (tortoiseRadius_exterior t t.2)).ne'
  unfold leftTime leftCurl
  constructor <;> field_simp [hr] <;> ring

/-- Original source/reader frequency gaps hold for independent Xi occurrences. -/
theorem original_frequency_gaps (q r : XiZeroCopy) (branch side : Bool) :
    0 < (physicalFundamentalFrequency r side-2*physicalRate q branch).re ∧
      (physicalFundamentalFrequency r side+2*physicalRate q branch+3).re < 0 := by
  have hq := xi_divisor_support_re_mem_open_unit q.1
  have hr := xi_divisor_support_re_mem_open_unit r.1
  rw [physicalFundamentalFrequency_eq]
  cases branch <;> cases side
  all_goals norm_num [physicalRate,Complex.sub_re,Complex.neg_re,Complex.div_re]
  all_goals constructor <;> linarith [hq.1,hq.2,hr.1,hr.2]

/-- The actual source and reader resolvents are separated, without a supplied nonresonance premise. -/
theorem eigenvalue_difference (q r : XiZeroCopy) (branch side : Bool) :
    D4BMLeftModeRadialEquation.eigenvalue r-parameter q branch=
      (physicalFundamentalFrequency r side-2*physicalRate q branch)*
        (physicalFundamentalFrequency r side+2*physicalRate q branch+3) := by
  rw [reader_eigenvalue r side,parameter_physicalRate]
  unfold D4BMQuadraticMixedSource.resolventParameter
  ring

theorem eigenvalue_difference_ne_zero (q r : XiZeroCopy) (branch : Bool) :
    D4BMLeftModeRadialEquation.eigenvalue r-parameter q branch≠0 := by
  rw [eigenvalue_difference q r branch true]
  have h := original_frequency_gaps q r branch true
  apply mul_ne_zero
  · intro he
    rw [he,Complex.zero_re] at h
    exact lt_irrefl (0:ℝ) h.1
  · intro he
    rw [he,Complex.zero_re] at h
    exact lt_irrefl (0:ℝ) h.2

/-- The actual complete mixed radial coefficients, with differentiated contact retained. -/
theorem radial_coefficients (q r : XiZeroCopy) (branch side outer : Bool) (a : ℂ) (t : Iio (0:ℝ))
    (z : {z : D4BMHorizon.Point // 0 < z 1}) :
    let p := modePoint t z.val z.2
    let s := physicalRate q branch
    let w := physicalFundamentalFrequency r side
    let R := (p.val 1:ℂ)
    let E := envelope (2*s) (a^(2 : ℕ)) p.val
    let g := D4BMLeftModeRadialEquation.profile r side outer t
    let dg := D4BMLeftModeRadialEquation.profileFirst r side outer t
    radialPairCoefficient s R E (D4BMLeftModeRadialEquation.eigenvalue r) g dg 1 0=
      (w*E*g/R^(2 : ℕ))*2*s*(w-2*s) ∧
    radialPairCoefficient s R E (D4BMLeftModeRadialEquation.eigenvalue r) g dg 0 1=
      (w*E*g/R^(2 : ℕ))*s^(2 : ℕ)*(w+(s+1)*(2*s+2-w)/(2*R^(2 : ℕ))) := by
  dsimp only
  simp only [radialPairCoefficient,
    show (modePoint t z.val z.2).val 1=tortoiseRadius t from rfl]
  rw [(left_blocks r side outer t).1,(left_blocks r side outer t).2]
  have hr : (tortoiseRadius t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (lt_trans zero_lt_one (tortoiseRadius_exterior t t.2)).ne'
  unfold sourceTime sourceCurl
  constructor <;> field_simp [hr] <;> ring

/-- Constant coefficient of the surviving full square-source overlap. -/
def overlapConstant (s w : ℂ) : ℂ := s*(w+2*s+3)*w+2*(2*s+1)*(2*s+2)

/-- Inverse-square coefficient, including the differentiated source contact. -/
def overlapInverseSquare (s w : ℂ) : ℂ := s*(w+2*s+3)*(s+1)*(2*s+2-w)/2

/-- The actual coefficient of the remaining square/reader overlap in the original radial current. -/
def bulkOverlapCoefficient (q reader : XiZeroCopy) (branch side outer : Bool) (a : ℂ)
    (t : Iio (0:ℝ)) (z : {z : D4BMHorizon.Point // 0 < z 1}) : ℂ :=
  let p := modePoint t z.val z.2
  let s := physicalRate q branch
  let r := (p.val 1:ℂ)
  let E := envelope (2*s) (a^(2 : ℕ)) p.val
  let g := D4BMLeftModeRadialEquation.profile reader side outer t
  let dg := D4BMLeftModeRadialEquation.profileFirst reader side outer t
  let lam := D4BMLeftModeRadialEquation.eigenvalue reader
  let mu := parameter q branch
  (lam-mu)*radialPairCoefficient s r E lam g dg 0 1+
    mu*radialPairCoefficient s r E lam g dg 1 0

/-- Exact reduction of the original bulk coefficient to a constant and an inverse-square term. -/
theorem bulkOverlapCoefficient_eq (q reader : XiZeroCopy) (branch side outer : Bool) (a : ℂ)
    (t : Iio (0:ℝ)) (z : {z : D4BMHorizon.Point // 0 < z 1}) :
    let p := modePoint t z.val z.2
    let s := physicalRate q branch
    let w := physicalFundamentalFrequency reader side
    let r := (p.val 1:ℂ)
    let E := envelope (2*s) (a^(2 : ℕ)) p.val
    let g := D4BMLeftModeRadialEquation.profile reader side outer t
    bulkOverlapCoefficient q reader branch side outer a t z=
      (w*E*g/r^(2 : ℕ))*(w-2*s)*s*(overlapConstant s w+overlapInverseSquare s w/r^(2 : ℕ)) := by
  dsimp only [bulkOverlapCoefficient]
  rw [(radial_coefficients q reader branch side outer a t z).1,
    (radial_coefficients q reader branch side outer a t z).2,
    eigenvalue_difference q reader branch side,parameter_physicalRate]
  unfold overlapConstant overlapInverseSquare D4BMQuadraticMixedSource.resolventParameter
  ring

private theorem source_rate_strip (q : XiZeroCopy) (b : Bool) :
    -2 < (physicalRate q b).re ∧ (physicalRate q b).re < -1 := by
  have hq := xi_divisor_support_re_mem_open_unit q.1
  cases b <;> norm_num [physicalRate] <;> constructor <;> linarith [hq.1,hq.2]

private theorem source_rate_factors (q : XiZeroCopy) (b : Bool) :
    physicalRate q b≠0 ∧ physicalRate q b+1≠0 ∧ physicalRate q b+2≠0 ∧ 4*physicalRate q b+1≠0 := by
  have hs := source_rate_strip q b
  refine ⟨?_,?_,?_,?_⟩ <;> intro h <;> have hh := congrArg Complex.re h
  all_goals norm_num [Complex.add_re,Complex.mul_re,Complex.mul_im] at hh
  all_goals linarith [hs.1,hs.2]

/-- The literal source equations forbid simultaneous loss of both overlap coefficients. -/
theorem overlap_coefficients_not_both_zero (q reader : XiZeroCopy) (branch side : Bool) :
    ¬ (overlapConstant (physicalRate q branch) (physicalFundamentalFrequency reader side)=0 ∧
      overlapInverseSquare (physicalRate q branch) (physicalFundamentalFrequency reader side)=0) := by
  let s := physicalRate q branch
  let w := physicalFundamentalFrequency reader side
  have hs := source_rate_factors q branch
  have hL : w+2*s+3≠0 := by
    intro he
    have h := (original_frequency_gaps q reader branch side).2
    change (w+2*s+3).re<0 at h
    rw [he,Complex.zero_re] at h
    exact lt_irrefl (0:ℝ) h
  intro h
  change overlapConstant s w=0 ∧ overlapInverseSquare s w=0 at h
  have hp : s*(w+2*s+3)*(s+1)*(2*s+2-w)=0 := by
    dsimp only [overlapInverseSquare] at h
    linear_combination 2*h.2
  have hw : w=2*s+2 := by
    have he := (mul_eq_zero.mp hp).resolve_left (mul_ne_zero (mul_ne_zero hs.1 hL) hs.2.1)
    linear_combination -he
  have hf : (2*s+2)*(4*s+1)*(s+2)=0 := by
    have h0 := h.1
    rw [hw] at h0
    dsimp only [overlapConstant] at h0
    linear_combination h0
  have h2s : 2*s+2≠0 := by
    rw [show 2*s+2=2*(s+1) by ring]
    exact mul_ne_zero (by norm_num) hs.2.1
  exact (mul_ne_zero (mul_ne_zero h2s hs.2.2.2) hs.2.2.1) hf

private theorem profile_ne_zero (q : XiZeroCopy) (side outer : Bool) (t : Iio (0:ℝ)) :
    D4BMLeftModeRadialEquation.profile q side outer t≠0 := by
  rw [profile_value]
  exact mul_ne_zero (power_ne_zero _ (horizonCoordinate_interior t t.2).1)
    (Complex.ofReal_ne_zero.mpr (radialUnit_bounds t t.2).1.ne')

/-- Sharp zero locus of the actual unit-amplitude overlap coefficient, at the unchanged clock. -/
theorem bulkOverlapCoefficient_zero_iff (q reader : XiZeroCopy) (branch side outer : Bool)
    (t : Iio (0:ℝ)) (z : {z : D4BMHorizon.Point // 0 < z 1}) :
    bulkOverlapCoefficient q reader branch side outer 1 t z=0 ↔
      overlapConstant (physicalRate q branch) (physicalFundamentalFrequency reader side)*(tortoiseRadius t:ℂ)^(2 : ℕ)+
        overlapInverseSquare (physicalRate q branch) (physicalFundamentalFrequency reader side)=0 := by
  have hw : physicalFundamentalFrequency reader side≠0 := by
    intro he
    apply (physicalFundamentalFrequency_strip reader side).1
    rw [he]
    rfl
  have hd : physicalFundamentalFrequency reader side-2*physicalRate q branch≠0 := by
    intro he
    have hh := (original_frequency_gaps q reader branch side).1
    rw [he,Complex.zero_re] at hh
    exact lt_irrefl (0:ℝ) hh
  have hs := (source_rate_factors q branch).1
  have hg := profile_ne_zero reader side outer t
  have hE : envelope (2*physicalRate q branch) ((1:ℂ)^(2 : ℕ)) (modePoint t z.val z.2).val≠0 := by
    rw [envelope_eq_exp]
    simp only [one_pow,one_mul,ne_eq,Complex.exp_ne_zero,not_false_eq_true]
  have hr : (tortoiseRadius t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (lt_trans zero_lt_one (tortoiseRadius_exterior t t.2)).ne'
  rw [bulkOverlapCoefficient_eq]
  simp only [show (modePoint t z.val z.2).val 1=tortoiseRadius t from rfl,
    mul_eq_zero,div_eq_zero_iff,hw,hE,hg,hd,hs,pow_ne_zero 2 hr,or_self,false_or]
  have he : overlapConstant (physicalRate q branch) (physicalFundamentalFrequency reader side)+
      overlapInverseSquare (physicalRate q branch) (physicalFundamentalFrequency reader side)/(tortoiseRadius t:ℂ)^(2 : ℕ)=
      (overlapConstant (physicalRate q branch) (physicalFundamentalFrequency reader side)*(tortoiseRadius t:ℂ)^(2 : ℕ)+
        overlapInverseSquare (physicalRate q branch) (physicalFundamentalFrequency reader side))/(tortoiseRadius t:ℂ)^(2 : ℕ) := by
    field_simp [hr]
  rw [he,div_eq_zero_iff]
  simp only [pow_ne_zero 2 hr,or_false]

/-- The actual quadratic amplitude factors out of the complete overlap coefficient. -/
theorem bulkOverlapCoefficient_amplitude (q reader : XiZeroCopy) (branch side outer : Bool) (a : ℂ)
    (t : Iio (0:ℝ)) (z : {z : D4BMHorizon.Point // 0 < z 1}) :
    bulkOverlapCoefficient q reader branch side outer a t z=
      a^(2 : ℕ)*bulkOverlapCoefficient q reader branch side outer 1 t z := by
  rw [bulkOverlapCoefficient_eq,bulkOverlapCoefficient_eq,envelope_eq_exp,envelope_eq_exp]
  ring

/-- Complete zero classification, including the actual source amplitude. -/
theorem bulkOverlapCoefficient_zero_iff_amplitude (q reader : XiZeroCopy) (branch side outer : Bool) (a : ℂ)
    (t : Iio (0:ℝ)) (z : {z : D4BMHorizon.Point // 0 < z 1}) :
    bulkOverlapCoefficient q reader branch side outer a t z=0 ↔ a=0 ∨
      overlapConstant (physicalRate q branch) (physicalFundamentalFrequency reader side)*(tortoiseRadius t:ℂ)^(2 : ℕ)+
        overlapInverseSquare (physicalRate q branch) (physicalFundamentalFrequency reader side)=0 := by
  rw [bulkOverlapCoefficient_amplitude,mul_eq_zero,bulkOverlapCoefficient_zero_iff]
  simp only [pow_eq_zero_iff (by norm_num : (2:ℕ)≠0)]

/-- The actual radial weights can kill the remaining overlap at at most one interior radius. -/
theorem bulkOverlapCoefficient_zero_set_subsingleton (q reader : XiZeroCopy) (branch side outer : Bool)
    (z : {z : D4BMHorizon.Point // 0 < z 1}) :
    Set.Subsingleton {t : Iio (0:ℝ) | bulkOverlapCoefficient q reader branch side outer 1 t z=0} := by
  intro t ht v hv
  have h1 := (bulkOverlapCoefficient_zero_iff q reader branch side outer t z).mp ht
  have h2 := (bulkOverlapCoefficient_zero_iff q reader branch side outer v z).mp hv
  have hc : overlapConstant (physicalRate q branch) (physicalFundamentalFrequency reader side)≠0 := by
    intro he
    have h := overlap_coefficients_not_both_zero q reader branch side
    apply h
    refine ⟨he,?_⟩
    simpa only [he,zero_mul,zero_add] using h1
  have hsq : (tortoiseRadius t:ℂ)^(2 : ℕ)=(tortoiseRadius v:ℂ)^(2 : ℕ) := by
    apply mul_left_cancel₀ hc
    linear_combination h1-h2
  have hsqR : (tortoiseRadius t)^(2 : ℕ)=(tortoiseRadius v)^(2 : ℕ) := by exact_mod_cast hsq
  have hr : tortoiseRadius t=tortoiseRadius v := by
    nlinarith [tortoiseRadius_exterior t t.2,tortoiseRadius_exterior v v.2]
  apply Subtype.ext
  calc
    t.val=D4BMIngoingCoordinates.tortoise (tortoiseRadius t) := (tortoise_original_inverse t t.2).symm
    _ = D4BMIngoingCoordinates.tortoise (tortoiseRadius v) := congrArg D4BMIngoingCoordinates.tortoise hr
    _ = v.val := tortoise_original_inverse v v.2

/-- Radial weights alone cannot remove the actual full square/contact overlap everywhere. -/
theorem exists_bulkOverlapCoefficient_ne_zero (q reader : XiZeroCopy) (branch side outer : Bool)
    (z : {z : D4BMHorizon.Point // 0 < z 1}) :
    ∃ t : Iio (0:ℝ), bulkOverlapCoefficient q reader branch side outer 1 t z≠0 := by
  by_contra h
  push Not at h
  let t : Iio (0:ℝ) := ⟨-1,by norm_num⟩
  let v : Iio (0:ℝ) := ⟨-2,by norm_num⟩
  have he := bulkOverlapCoefficient_zero_set_subsingleton q reader branch side outer z (h t) (h v)
  have hv := congrArg Subtype.val he
  norm_num [t,v] at hv


/-- Source-square current whose divergence controls the remaining actual angular overlap. -/
def squareReaderCurrent (q reader : XiZeroCopy) (j : Fin 2) (z : D4BMHorizon.Point) : ℂ :=
  (D4BMAngularTwoTensor.source q z)^(2 : ℕ)/2*
    coordDeriv j (D4BMLiteralCusp.scalar (physicalAngularParameter reader)) z

/-- The complete source-square/reader overlap is a boundary divergence minus a full triple density. -/
theorem squareReaderCurrent_divergence (q reader : XiZeroCopy)
    (z : {z : D4BMHorizon.Point // 0 < z 1}) :
    (∑ j : Fin 2, coordDeriv j (squareReaderCurrent q reader j) z.val)=
      (∑ j : Fin 2, fullSquareCovector q j z.val*
        D4BMLiteralCusp.vector (physicalAngularParameter reader) j z.val)+
      D4BMLeftModeRadialEquation.eigenvalue reader*(D4BMAngularTwoTensor.source q z.val)^(2 : ℕ)*
        D4BMLiteralCusp.scalar (physicalAngularParameter reader) z.val/(2*(z.val 1:ℂ)^(2 : ℕ)) := by
  let S := D4BMAngularTwoTensor.source q
  let R := D4BMLiteralCusp.scalar (physicalAngularParameter reader)
  let lam := D4BMLeftModeRadialEquation.eigenvalue reader
  have hS : ContDiffAt ℝ 2 S z.val :=
    D4BMLiteralCusp.scalar_contDiffAt (D4BMGlobalAngularResponse.center q) 2 z.val z.2
  have hR : ContDiffAt ℝ 2 R z.val :=
    D4BMLiteralCusp.scalar_contDiffAt (physicalAngularParameter reader) 2 z.val z.2
  have dS := (hS.differentiableAt (by norm_num)).hasFDerivAt
  have hd (j : Fin 2) : coordDeriv j (squareReaderCurrent q reader j) z.val=
      S z.val*coordDeriv j S z.val*coordDeriv j R z.val+
        S z.val^(2 : ℕ)/2*coordDeriv j (coordDeriv j R) z.val := by
    have dr := (ScalarTwoJet.coordDeriv_hasFDerivAt hR j).differentiableAt.hasFDerivAt
    have hh := ((dS.pow 2).mul_const (2:ℂ)⁻¹).mul dr
    change HasFDerivAt (squareReaderCurrent q reader j) _ z.val at hh
    simp only [coordDeriv,hh.fderiv,add_apply,smul_apply,
      smul_eq_mul,nsmul_eq_mul]
    ring
  have heR := D4BMLiteralCusp.scalar_equation (physicalAngularParameter reader) z.val z.2
  rw [D4BMHorizon.scalarLaplacian_eq _ z.val z.2] at heR
  have he : (z.val 1:ℂ)^(2 : ℕ)*(coordDeriv 0 (coordDeriv 0 R) z.val+
      coordDeriv 1 (coordDeriv 1 R) z.val)=lam*R z.val := by
    dsimp only [R,lam,D4BMLeftModeRadialEquation.eigenvalue,D4BMLiteralCusp.scalarQ] at heR ⊢
    linear_combination heR
  change (∑ j : Fin 2, coordDeriv j (squareReaderCurrent q reader j) z.val)=
    (∑ j : Fin 2, S z.val*D4BMHorizon.coexact S j z.val*D4BMHorizon.coexact R j z.val)+
      lam*S z.val^(2 : ℕ)*R z.val/(2*(z.val 1:ℂ)^(2 : ℕ))
  have hy : (z.val 1:ℂ)≠0 := Complex.ofReal_ne_zero.mpr z.2.ne'
  simp only [Fin.sum_univ_two,hd,D4BMHorizon.coexact,Matrix.cons_val_zero,Matrix.cons_val_one]
  field_simp [hy]
  linear_combination (S z.val^(2 : ℕ))*he

/-- Exact original left-QNM radial balance with both boundary currents and the full triple source.
No horizon, cusp, onset or source-contact contribution is set to zero. -/
theorem original_radial_triple_balance (q reader : XiZeroCopy) (branch side outer : Bool) (a : ℂ)
    (t : Iio (0:ℝ)) (z : {z : D4BMHorizon.Point // 0 < z 1}) :
    let p := modePoint t z.val z.2
    let s := physicalRate q branch
    let r := (p.val 1:ℂ)
    let E := envelope (2*s) (a^(2 : ℕ)) p.val
    let g := D4BMLeftModeRadialEquation.profile reader side outer t
    let dg := D4BMLeftModeRadialEquation.profileFirst reader side outer t
    let lam := D4BMLeftModeRadialEquation.eigenvalue reader
    let mu := parameter q branch
    let C := radialPairCoefficient s r E lam g dg 1 0
    let Omega := bulkOverlapCoefficient q reader branch side outer a t z
    (lam-mu)*current q branch a reader side outer t z 1+
      Omega*lam*(D4BMAngularTwoTensor.source q z.val)^(2 : ℕ)*
        D4BMLiteralCusp.scalar (physicalAngularParameter reader) z.val/(2*(z.val 1:ℂ)^(2 : ℕ))=
      C*(∑ j : Fin 2, coordDeriv j (angularGreenCurrent q branch reader j) z.val)+
        Omega*(∑ j : Fin 2, coordDeriv j (squareReaderCurrent q reader j) z.val) := by
  dsimp only
  rw [radial_current_angular_decomposition,squareReaderCurrent_divergence]
  dsimp only [bulkOverlapCoefficient]
  ring


end
end RHTower.D4BMMixedRadialOverlap
