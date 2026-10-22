import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMMixedRadialOverlap
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLiteralCyclicPeierlsCapRadialDefect
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLiteralCyclicPeierlsSelfInverseSquarePhysical
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCapAngularFluxCusp
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLiteralCyclicPeierlsAffineCuspIncidence
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMMixedParticularCuspFlux

/-!
The actual metric residual has two frozen radial coefficients. The cap term
uses radial block `1,0`, so it changes only the constant radial channel;
the self-copy inverse-square channel of the square/contact term survives
every complex cap mixing. Consequently no fixed mixing can make the combined
coefficient vanish on every physical radial clock. This rules out an
unrenormalized all-fibre zero residual, not the ordered CTP/current route.
-/

open Complex Set
open RHTower
open RHTower.D4BMModularCore RHTower.D4BMJointSource
open RHTower.D4BMMixedRadialOverlap
open RHTower.D4BMLiteralCyclicPeierlsCapRadialDefect
open RHTower.D4BMLiteralCyclicPeierlsSelfInverseSquarePhysical
open RHTower.D4BMPhysicalModeAction RHTower.D4BMFundamentalScalarMetric
open RHTower.D4BMLeftModeRadialEquation RHTower.D4BMJointWave
open RHTower.D4BMLaplaceRadial
open RHTower.D4BMGlobalAngularResponse RHTower.D4BMCapAngularFluxCusp
open RHTower.D4BMLiteralCyclicPeierlsAffineCuspIncidence
open RHTower.D4BMMixedParticularCuspFlux

namespace RHTower.D4BMPWResidualRadialRigidity
noncomputable section
set_option autoImplicit false

/-- Constant radial channel after mixing the actual cap and square currents. -/
def mixedConstant (s w T : ℂ) : ℂ :=
  (w - 2*s)*s*overlapConstant s w + T*(s*(s-1)/4)*2*s*(w-2*s)

/-- Inverse-square channel, unchanged by every cap mixing scalar. -/
def mixedInverseSquare (s w : ℂ) : ℂ :=
  (w - 2*s)*s*overlapInverseSquare s w

/-- The retained channel is nonzero on every physical self-copy source arm. -/
theorem physical_mixedInverseSquare_ne_zero (q : XiZeroCopy) (branch side : Bool) :
    mixedInverseSquare (physicalRate q branch) (physicalFundamentalFrequency q side) ≠ 0 := by
  let s := physicalRate q branch
  let w := physicalFundamentalFrequency q side
  have hstrip : -2 < s.re ∧ s.re < -1 := by
    have hq := xi_divisor_support_re_mem_open_unit q.1
    cases branch <;> norm_num [s,physicalRate,Complex.sub_re,Complex.neg_re] <;> constructor <;> linarith [hq.1,hq.2]
  have hs : s ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    rw [Complex.zero_re] at hr
    linarith [hstrip.2]
  have hgap : w-2*s ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    have hg := (original_frequency_gaps q q branch side).1
    change 0 < (w-2*s).re at hg
    rw [h,Complex.zero_re] at hg
    exact lt_irrefl _ hg
  exact mul_ne_zero (mul_ne_zero hgap hs)
    (self_overlapInverseSquare_ne_zero q branch side)

/-- Source-faithful identification of both radial channels in the literal
cyclic-Peierls metric residual. -/
theorem actual_mixed_coefficient_eq (q reader : XiZeroCopy)
    (branch side outer : Bool) (a T : ℂ) (t : Iio (0 : ℝ))
    (base : {z : D4BMHorizon.Point // 0 < z 1}) :
    let p := modePoint t base.val base.property
    let s := physicalRate q branch
    let w := physicalFundamentalFrequency reader side
    let R := (p.val 1 : ℂ)
    let E := envelope (2*s) (a ^ (2 : ℕ)) p.val
    let g := D4BMLeftModeRadialEquation.profile reader side outer t
    cyclicPeierlsSquareCoefficient q reader branch side outer a t base +
      T * cyclicPeierlsCapFluxCoefficient q reader branch side outer a t base =
      (w*E*g/R^(2 : ℕ)) *
        (mixedConstant s w T + mixedInverseSquare s w/R^(2 : ℕ)) := by
  dsimp only
  let p := modePoint t base.val base.property
  let s := physicalRate q branch
  let w := physicalFundamentalFrequency reader side
  let R := (p.val 1 : ℂ)
  let E := envelope (2*s) (a ^ (2 : ℕ)) p.val
  let g := D4BMLeftModeRadialEquation.profile reader side outer t
  have hA : cyclicPeierlsSquareCoefficient q reader branch side outer a t base =
      (w*E*g/R^(2 : ℕ))*(w-2*s)*s*
        (overlapConstant s w+overlapInverseSquare s w/R^(2 : ℕ)) := by
    simpa [cyclicPeierlsSquareCoefficient, p,s,w,R,E,g] using
      bulkOverlapCoefficient_eq q reader branch side outer a t base
  have hB : cyclicPeierlsCapFluxCoefficient q reader branch side outer a t base =
      (s*(s-1)/4)*(w*E*g/R^(2 : ℕ))*2*s*(w-2*s) := by
    unfold cyclicPeierlsCapFluxCoefficient
    rw [(radial_coefficients q reader branch side outer a t base).1]
    ring
  rw [hA,hB]
  unfold mixedConstant mixedInverseSquare
  ring

private theorem actual_prefactor_ne_zero (q reader : XiZeroCopy) (branch side outer : Bool)
    (t : Iio (0 : ℝ)) (base : {z : D4BMHorizon.Point // 0 < z 1}) :
    let p := modePoint t base.val base.property
    let s := physicalRate q branch
    let w := physicalFundamentalFrequency reader side
    let R := (p.val 1 : ℂ)
    let E := envelope (2*s) ((1 : ℂ) ^ (2 : ℕ)) p.val
    let g := D4BMLeftModeRadialEquation.profile reader side outer t
    w*E*g/R^(2 : ℕ) ≠ 0 := by
  dsimp only
  have hw : physicalFundamentalFrequency reader side ≠ 0 := by
    intro h
    apply (physicalFundamentalFrequency_strip reader side).1
    rw [h]
    rfl
  have hE : envelope (2*physicalRate q branch) ((1:ℂ)^(2 : ℕ))
      (modePoint t base.val base.property).val ≠ 0 := by
    rw [envelope_eq_exp]
    simp only [one_pow, one_mul, ne_eq, Complex.exp_ne_zero, not_false_eq_true]
  have hg : D4BMLeftModeRadialEquation.profile reader side outer t ≠ 0 := by
    rw [profile_value]
    exact mul_ne_zero (power_ne_zero _ (horizonCoordinate_interior t t.2).1)
      (Complex.ofReal_ne_zero.mpr (radialUnit_bounds t t.2).1.ne')
  have hr : ((modePoint t base.val base.property).val 1 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (lt_trans zero_lt_one (tortoiseRadius_exterior t t.2)).ne'
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hw hE) hg) (pow_ne_zero 2 hr)

theorem actual_mixed_coefficient_zero_iff (q reader : XiZeroCopy)
    (branch side outer : Bool) (T : ℂ) (t : Iio (0 : ℝ))
    (base : {z : D4BMHorizon.Point // 0 < z 1}) :
    cyclicPeierlsSquareCoefficient q reader branch side outer 1 t base +
      T * cyclicPeierlsCapFluxCoefficient q reader branch side outer 1 t base = 0 ↔
    mixedConstant (physicalRate q branch) (physicalFundamentalFrequency reader side) T *
      (tortoiseRadius t : ℂ)^(2 : ℕ) +
      mixedInverseSquare (physicalRate q branch) (physicalFundamentalFrequency reader side) = 0 := by
  rw [actual_mixed_coefficient_eq]
  have hp := actual_prefactor_ne_zero q reader branch side outer t base
  dsimp only at hp
  simp only [show (modePoint t base.val base.property).val 1 = tortoiseRadius t from rfl] at hp ⊢
  have hK : physicalFundamentalFrequency reader side *
      envelope (2*physicalRate q branch) ((1:ℂ)^(2 : ℕ))
        (modePoint t base.val base.property).val *
      D4BMLeftModeRadialEquation.profile reader side outer t /
        (tortoiseRadius t : ℂ)^(2 : ℕ) ≠ 0 := by
    exact hp
  rw [mul_eq_zero]
  simp only [hK, false_or]
  have hr : (tortoiseRadius t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (lt_trans zero_lt_one (tortoiseRadius_exterior t t.2)).ne'
  rw [show mixedConstant (physicalRate q branch) (physicalFundamentalFrequency reader side) T +
      mixedInverseSquare (physicalRate q branch) (physicalFundamentalFrequency reader side) /
        (tortoiseRadius t : ℂ)^(2 : ℕ) =
      (mixedConstant (physicalRate q branch) (physicalFundamentalFrequency reader side) T *
        (tortoiseRadius t : ℂ)^(2 : ℕ) +
        mixedInverseSquare (physicalRate q branch) (physicalFundamentalFrequency reader side)) /
        (tortoiseRadius t : ℂ)^(2 : ℕ) by field_simp [hr]]
  simp only [div_eq_zero_iff, pow_ne_zero 2 hr, or_false]

/-- No complex scalar can cancel the actual square-plus-cap residual at all
original physical radial clocks. -/
theorem exists_actual_mixed_coefficient_ne_zero (q : XiZeroCopy)
    (branch side outer : Bool) (T : ℂ)
    (base : {z : D4BMHorizon.Point // 0 < z 1}) :
    ∃ t : Iio (0 : ℝ),
      cyclicPeierlsSquareCoefficient q q branch side outer 1 t base +
        T * cyclicPeierlsCapFluxCoefficient q q branch side outer 1 t base ≠ 0 := by
  by_contra h
  push Not at h
  let t : Iio (0 : ℝ) := ⟨-1, by norm_num⟩
  let v : Iio (0 : ℝ) := ⟨-2, by norm_num⟩
  have h1 := (actual_mixed_coefficient_zero_iff q q branch side outer T t base).mp (h t)
  have h2 := (actual_mixed_coefficient_zero_iff q q branch side outer T v base).mp (h v)
  let C := mixedConstant (physicalRate q branch) (physicalFundamentalFrequency q side) T
  let D := mixedInverseSquare (physicalRate q branch) (physicalFundamentalFrequency q side)
  change C * (tortoiseRadius t : ℂ)^(2 : ℕ) + D = 0 at h1
  change C * (tortoiseRadius v : ℂ)^(2 : ℕ) + D = 0 at h2
  have hD : D ≠ 0 := physical_mixedInverseSquare_ne_zero q branch side
  have hC : C ≠ 0 := by
    intro hc
    have hd : D = 0 := by simpa only [hc, zero_mul, zero_add] using h1
    exact hD hd
  have hsq : (tortoiseRadius t : ℂ)^(2 : ℕ) =
      (tortoiseRadius v : ℂ)^(2 : ℕ) := by
    apply mul_left_cancel₀ hC
    linear_combination h1-h2
  have hsqR : (tortoiseRadius t)^(2 : ℕ) =
      (tortoiseRadius v)^(2 : ℕ) := by exact_mod_cast hsq
  have hr : tortoiseRadius t = tortoiseRadius v := by
    nlinarith [tortoiseRadius_exterior t t.2, tortoiseRadius_exterior v v.2]
  have ht : t = v := by
    apply Subtype.ext
    calc
      t.val = D4BMIngoingCoordinates.tortoise (tortoiseRadius t) :=
        (tortoise_original_inverse t t.2).symm
      _ = D4BMIngoingCoordinates.tortoise (tortoiseRadius v) :=
        congrArg D4BMIngoingCoordinates.tortoise hr
      _ = v.val := tortoise_original_inverse v v.2
  have hv := congrArg Subtype.val ht
  norm_num [t,v] at hv

/-- Coefficient of the unique lower-source/lower-reader cusp channel in the
square-reader face, before inserting its completed-Lambda factors. -/
def dominantSquareCoefficient (q : XiZeroCopy) : ℂ :=
  d4BMCompletedEisensteinCuspConstantCoefficient (center q) false ^ (2 : ℕ) / 2 *
  d4BMCompletedEisensteinCuspConstantCoefficient (physicalAngularParameter q) false *
  d4BMCompletedEisensteinCuspWeylExponent (physicalAngularParameter q) false

/-- Exact cap-to-square ratio for the same physical principal Weyl channel. -/
def dominantCapRatio (q : XiZeroCopy) : ℂ :=
  (1 - (q.1 : ℂ)) * (3 * (q.1 : ℂ) - 2)

theorem cap_dominant_coefficient_eq (q : XiZeroCopy) :
    constantCoefficient (center q) (physicalAngularParameter q) false false false =
      dominantCapRatio q * dominantSquareCoefficient q := by
  unfold constantCoefficient dominantCapRatio dominantSquareCoefficient
  rw [physicalAngularParameter_eq]
  simp only [d4BMCompletedEisensteinCuspWeylExponent, d4BMCuspSign,
    Bool.false_eq_true, ↓reduceIte]
  unfold D4BMGlobalAngularResponse.center
  ring

/-- The lower-source/lower-reader channel cannot disappear on a left-half Xi
copy: both completed-Lambda factors and the reader indicial factor survive. -/
theorem dominantSquareCoefficient_ne_zero (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1/2) : dominantSquareCoefficient q ≠ 0 := by
  have hsource : d4BMCompletedEisensteinCuspConstantCoefficient (center q) false =
      reflectedCompletedLambda (2*(q.1 : ℂ)-1) := by
    simp only [d4BMCompletedEisensteinCuspConstantCoefficient,
      Bool.false_eq_true, ite_false, D4BMGlobalAngularResponse.center]
    congr 1
    ring
  have hreader : d4BMCompletedEisensteinCuspConstantCoefficient
      (physicalAngularParameter q) false = reflectedCompletedLambda ((q.1 : ℂ)-1) := by
    rw [physicalAngularParameter_eq]
    simp only [d4BMCompletedEisensteinCuspConstantCoefficient,
      Bool.false_eq_true, ite_false]
    congr 1
    ring
  have hpower : d4BMCompletedEisensteinCuspWeylExponent
      (physicalAngularParameter q) false = readerPower q := by
    rw [physicalAngularParameter_eq]
    simp only [d4BMCompletedEisensteinCuspWeylExponent,d4BMCuspSign,
      readerPower, Bool.false_eq_true, ↓reduceIte]
    ring
  have hLambda : reflectedCompletedLambda (2*(q.1 : ℂ)-1) ≠ 0 := by
    intro hz
    exact affine_lower_lambda_zero_not_left q ⟨hz,hleft⟩
  unfold dominantSquareCoefficient
  rw [hsource,hreader,hpower]
  exact mul_ne_zero (mul_ne_zero
    (div_ne_zero (pow_ne_zero 2 hLambda) (by norm_num))
    (reader_completion_ne_zero q)) (reader_power_ne_zero q)

/-- The exact dominant-mode cap/square ratio is powerless to cancel the
combined physical residual coefficient on every radial fibre. -/
theorem exists_dominant_residual_coefficient_ne_zero (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1/2) (branch side outer : Bool)
    (base : {z : D4BMHorizon.Point // 0 < z 1}) :
    ∃ t : Iio (0 : ℝ), dominantSquareCoefficient q *
      (cyclicPeierlsSquareCoefficient q q branch side outer 1 t base +
        dominantCapRatio q *
          cyclicPeierlsCapFluxCoefficient q q branch side outer 1 t base) ≠ 0 := by
  obtain ⟨t,ht⟩ := exists_actual_mixed_coefficient_ne_zero q branch side outer
    (dominantCapRatio q) base
  exact ⟨t, mul_ne_zero (dominantSquareCoefficient_ne_zero q hleft) ht⟩

end
end RHTower.D4BMPWResidualRadialRigidity
