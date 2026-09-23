import GaloisForLFunctions.RHTower.XiMassParabolicHeatTransfer
import GaloisForLFunctions.RHTower.XiShiftedHankelHeatResolventBridge
import GaloisForLFunctions.RHTower.XiShiftedHankelCassiniPhaseTaxHeightThreshold

/-!
# Stieltjes--Cassini midpoint defect for squared Xi orientation

The parabolic heat chart and the shifted-Cassini chart carry the same positive orientation loss.
For `w = A + iB`, `y > 0`, and `lambda = (y+w)⁻¹`, the phase-blind Stieltjes envelope and Cassini
intrinsic velocity obey

`1/(y+A) - Re lambda = Re lambda - Re(lambda²)/Re(lambda)`

and both differences equal

`B² / ((y+A) ((y+A)²+B²))`.

The complete multiplicity-exact sum is finite, nonnegative, and vanishes exactly under RH.  Thus
Route T's parabolic Hermitian envelope and Route U's Cassini radial response are symmetric around
one phase-linear shifted-resolvent trace.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Phase-blind Stieltjes envelope of one squared Xi atom. -/
def xiHeatStieltjesEnvelopeTerm (y : ℝ) (q : XiZeroCopy) : ℝ :=
  1 / (y + (xiSquaredNode q).re)

/-- Common positive orientation gap between the heat envelope, shifted resolvent response, and
Cassini intrinsic velocity. -/
def xiHeatCassiniOrientationTerm (y : ℝ) (q : XiZeroCopy) : ℝ :=
  let A := y + (xiSquaredNode q).re
  let B := (xiSquaredNode q).im
  B ^ (2 : ℕ) / (A * (A ^ (2 : ℕ) + B ^ (2 : ℕ)))

/-- Complete phase-blind Stieltjes envelope. -/
def xiHeatStieltjesEnvelope (y : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, xiHeatStieltjesEnvelopeTerm y q

/-- Complete Stieltjes--Cassini orientation defect. -/
def xiHeatCassiniOrientationDefect (y : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, xiHeatCassiniOrientationTerm y q

/-- Complete Cassini intrinsic-velocity trace. -/
def xiHeatCassiniVelocityTrace (y : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, xiShiftedPairIntrinsicVelocity y q

private theorem xiHeatShiftedDenominator_pos
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    0 < y + (xiSquaredNode q).re :=
  add_pos hy (xiSquaredNode_re_pos q)

/-- First half of the midpoint law: Hermitian envelope minus phase-linear response. -/
theorem xiHeatCassiniOrientationTerm_eq_envelope_sub_re
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    xiHeatCassiniOrientationTerm y q =
      xiHeatStieltjesEnvelopeTerm y q - (xiShiftedReciprocalSquare y q).re := by
  let A : ℝ := y + (xiSquaredNode q).re
  let B : ℝ := (xiSquaredNode q).im
  have hA : 0 < A := by simpa only [A] using xiHeatShiftedDenominator_pos hy q
  have hD : 0 < A ^ (2 : ℕ) + B ^ (2 : ℕ) := by
    nlinarith [sq_pos_of_pos hA, sq_nonneg B]
  have hcoord : (y : ℂ) + xiSquaredNode q = (A : ℂ) + (B : ℂ) * I := by
    apply Complex.ext <;> simp [A, B]
  rw [xiShiftedReciprocalSquare_eq_inv hy.le, hcoord]
  simp only [xiHeatCassiniOrientationTerm, xiHeatStieltjesEnvelopeTerm,
    Complex.inv_re, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, add_zero, zero_add]
  dsimp only [A, B] at hA hD ⊢
  field_simp [hA.ne', hD.ne']
  ring

/-- Second half of the midpoint law: phase-linear response minus Cassini velocity. -/
theorem xiHeatCassiniOrientationTerm_eq_re_sub_velocity
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    xiHeatCassiniOrientationTerm y q =
      (xiShiftedReciprocalSquare y q).re - xiShiftedPairIntrinsicVelocity y q := by
  let A : ℝ := y + (xiSquaredNode q).re
  let B : ℝ := (xiSquaredNode q).im
  have hA : 0 < A := by simpa only [A] using xiHeatShiftedDenominator_pos hy q
  have hD : 0 < A ^ (2 : ℕ) + B ^ (2 : ℕ) := by
    nlinarith [sq_pos_of_pos hA, sq_nonneg B]
  have hcoord : (y : ℂ) + xiSquaredNode q = (A : ℂ) + (B : ℂ) * I := by
    apply Complex.ext <;> simp [A, B]
  rw [xiShiftedReciprocalSquare_eq_inv hy.le, hcoord]
  rw [xiShiftedPairIntrinsicVelocity, xiShiftedReciprocalSquare_eq_inv hy.le, hcoord,
    cassiniPairIntrinsicVelocity_inv_cartesian hA]
  simp only [xiHeatCassiniOrientationTerm, Complex.inv_re, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
    sub_zero, mul_one, add_zero, zero_add]
  dsimp only [A, B] at hA hD ⊢
  field_simp [hA.ne', hD.ne']
  ring

/-- Fisher form of the common orientation gap.  In the shifted reciprocal-square chart, the
defect is transverse phase squared divided by positive longitudinal mass. -/
theorem xiHeatCassiniOrientationTerm_eq_im_sq_div_re
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    xiHeatCassiniOrientationTerm y q =
      (xiShiftedReciprocalSquare y q).im ^ (2 : ℕ) /
        (xiShiftedReciprocalSquare y q).re := by
  let A : ℝ := y + (xiSquaredNode q).re
  let B : ℝ := (xiSquaredNode q).im
  have hA : 0 < A := by simpa only [A] using xiHeatShiftedDenominator_pos hy q
  have hD : 0 < A ^ (2 : ℕ) + B ^ (2 : ℕ) := by
    nlinarith [sq_pos_of_pos hA, sq_nonneg B]
  have hcoord : (y : ℂ) + xiSquaredNode q = (A : ℂ) + (B : ℂ) * I := by
    apply Complex.ext <;> simp [A, B]
  rw [xiShiftedReciprocalSquare_eq_inv hy.le, hcoord]
  simp only [xiHeatCassiniOrientationTerm, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, mul_one, add_zero, zero_add]
  dsimp only [A, B] at hA hD ⊢
  field_simp [hA.ne', hD.ne']

/-- Orbitwise midpoint form of the cross-route identity. -/
theorem xiHeatStieltjesEnvelopeTerm_add_velocity_eq_two_re
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    xiHeatStieltjesEnvelopeTerm y q + xiShiftedPairIntrinsicVelocity y q =
      2 * (xiShiftedReciprocalSquare y q).re := by
  have hleft := xiHeatCassiniOrientationTerm_eq_envelope_sub_re hy q
  have hright := xiHeatCassiniOrientationTerm_eq_re_sub_velocity hy q
  linarith

/-- Every orientation term is nonnegative. -/
theorem xiHeatCassiniOrientationTerm_nonneg
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    0 ≤ xiHeatCassiniOrientationTerm y q := by
  let A : ℝ := y + (xiSquaredNode q).re
  let B : ℝ := (xiSquaredNode q).im
  have hA : 0 < A := by simpa only [A] using xiHeatShiftedDenominator_pos hy q
  have hD : 0 < A ^ (2 : ℕ) + B ^ (2 : ℕ) := by
    nlinarith [sq_pos_of_pos hA, sq_nonneg B]
  rw [xiHeatCassiniOrientationTerm]
  exact div_nonneg (sq_nonneg B) (mul_pos hA hD).le

/-- An orbit contributes zero exactly when its squared spectral coordinate is real. -/
theorem xiHeatCassiniOrientationTerm_eq_zero_iff
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    xiHeatCassiniOrientationTerm y q = 0 ↔ (xiSquaredNode q).im = 0 := by
  let A : ℝ := y + (xiSquaredNode q).re
  let B : ℝ := (xiSquaredNode q).im
  have hA : 0 < A := by simpa only [A] using xiHeatShiftedDenominator_pos hy q
  have hD : 0 < A ^ (2 : ℕ) + B ^ (2 : ℕ) := by
    nlinarith [sq_pos_of_pos hA, sq_nonneg B]
  change B ^ (2 : ℕ) / (A * (A ^ (2 : ℕ) + B ^ (2 : ℕ))) = 0 ↔ B = 0
  constructor
  · intro h
    field_simp [hA.ne', hD.ne'] at h
    nlinarith
  · intro h
    simp [h]

/-- The phase-blind Stieltjes envelope is summable at every positive shift. -/
theorem summable_xiHeatStieltjesEnvelopeTerm
    {y : ℝ} (hy : 0 < y) :
    Summable (xiHeatStieltjesEnvelopeTerm y) := by
  have hsum := summable_integral_norm_xiHeatResolventAtom hy 0
  refine hsum.congr fun q => ?_
  rw [integral_norm_xiHeatResolventAtom hy.le]
  simp only [Nat.factorial_zero, Nat.cast_one, Nat.zero_add, pow_one, one_div]
  simp [xiHeatStieltjesEnvelopeTerm]

/-- One orientation term is bounded by its Stieltjes envelope. -/
theorem xiHeatCassiniOrientationTerm_le_envelope
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    xiHeatCassiniOrientationTerm y q ≤ xiHeatStieltjesEnvelopeTerm y q := by
  let A : ℝ := y + (xiSquaredNode q).re
  let B : ℝ := (xiSquaredNode q).im
  have hA : 0 < A := by simpa only [A] using xiHeatShiftedDenominator_pos hy q
  have hD : 0 < A ^ (2 : ℕ) + B ^ (2 : ℕ) := by
    nlinarith [sq_pos_of_pos hA, sq_nonneg B]
  change B ^ (2 : ℕ) / (A * (A ^ (2 : ℕ) + B ^ (2 : ℕ))) ≤ 1 / A
  rw [div_le_iff₀ (mul_pos hA hD)]
  field_simp [hA.ne']
  nlinarith [sq_nonneg A]

/-- Complete orientation defect is summable. -/
theorem summable_xiHeatCassiniOrientationTerm
    {y : ℝ} (hy : 0 < y) :
    Summable (xiHeatCassiniOrientationTerm y) :=
  Summable.of_nonneg_of_le
    (fun q => xiHeatCassiniOrientationTerm_nonneg hy q)
    (fun q => xiHeatCassiniOrientationTerm_le_envelope hy q)
    (summable_xiHeatStieltjesEnvelopeTerm hy)

/-- Cassini velocity trace is summable because it is the reflected midpoint of two summable
Stieltjes responses. -/
theorem summable_xiShiftedPairIntrinsicVelocity
    {y : ℝ} (hy : 0 < y) :
    Summable (xiShiftedPairIntrinsicVelocity y) := by
  have hlin : Summable (fun q : XiZeroCopy => (xiShiftedReciprocalSquare y q).re) :=
    (Complex.reCLM.summable
      (summable_xiShiftedReciprocalSquare_pow hy.le 0)).congr fun q => by simp
  have hmodel : Summable (fun q : XiZeroCopy =>
      2 * (xiShiftedReciprocalSquare y q).re - xiHeatStieltjesEnvelopeTerm y q) :=
    (hlin.mul_left 2).sub (summable_xiHeatStieltjesEnvelopeTerm hy)
  exact hmodel.congr fun q => by
    rw [← xiHeatStieltjesEnvelopeTerm_add_velocity_eq_two_re hy q]
    ring

/-- Complete defect is the gap between phase-blind envelope and phase-linear shifted-resolvent
response. -/
theorem xiHeatCassiniOrientationDefect_eq_envelope_sub_re_moment
    {y : ℝ} (hy : 0 < y) :
    xiHeatCassiniOrientationDefect y =
      xiHeatStieltjesEnvelope y - (xiShiftedReciprocalMoment y 0).re := by
  have hlin := summable_xiShiftedReciprocalSquare_pow hy.le 0
  have hlinRe : Summable (fun q : XiZeroCopy => (xiShiftedReciprocalSquare y q).re) :=
    (Complex.reCLM.summable hlin).congr fun q => by simp
  rw [xiHeatCassiniOrientationDefect, xiHeatStieltjesEnvelope,
    xiShiftedReciprocalMoment, Complex.re_tsum hlin]
  simp only [Nat.zero_add, pow_one]
  rw [← Summable.tsum_sub (summable_xiHeatStieltjesEnvelopeTerm hy) hlinRe]
  exact tsum_congr fun q => xiHeatCassiniOrientationTerm_eq_envelope_sub_re hy q

/-- Complete midpoint law between Route T's heat envelope and Route U's Cassini velocity. -/
theorem xiHeatStieltjesEnvelope_add_velocityTrace_eq_two_re_moment
    {y : ℝ} (hy : 0 < y) :
    xiHeatStieltjesEnvelope y + xiHeatCassiniVelocityTrace y =
      2 * (xiShiftedReciprocalMoment y 0).re := by
  have hlin := summable_xiShiftedReciprocalSquare_pow hy.le 0
  have hlinRe : Summable (fun q : XiZeroCopy => (xiShiftedReciprocalSquare y q).re) :=
    (Complex.reCLM.summable hlin).congr fun q => by simp
  rw [xiHeatStieltjesEnvelope, xiHeatCassiniVelocityTrace,
    xiShiftedReciprocalMoment, Complex.re_tsum hlin, ← tsum_mul_left]
  simp only [Nat.zero_add, pow_one]
  rw [← Summable.tsum_add (summable_xiHeatStieltjesEnvelopeTerm hy)
    (summable_xiShiftedPairIntrinsicVelocity hy)]
  exact tsum_congr fun q => xiHeatStieltjesEnvelopeTerm_add_velocity_eq_two_re hy q

/-- The complete envelope--velocity gap is exactly twice the common orientation defect. -/
theorem xiHeatStieltjesEnvelope_sub_velocityTrace_eq_two_mul_defect
    {y : ℝ} (hy : 0 < y) :
    xiHeatStieltjesEnvelope y - xiHeatCassiniVelocityTrace y =
      2 * xiHeatCassiniOrientationDefect y := by
  have hmid := xiHeatStieltjesEnvelope_add_velocityTrace_eq_two_re_moment hy
  have hdef := xiHeatCassiniOrientationDefect_eq_envelope_sub_re_moment hy
  linarith

/-- Complete orientation defect is nonnegative unconditionally. -/
theorem xiHeatCassiniOrientationDefect_nonneg
    {y : ℝ} (hy : 0 < y) :
    0 ≤ xiHeatCassiniOrientationDefect y := by
  rw [xiHeatCassiniOrientationDefect]
  exact tsum_nonneg fun q => xiHeatCassiniOrientationTerm_nonneg hy q

/-- Cassini intrinsic response never exceeds the phase-blind heat envelope. -/
theorem xiHeatCassiniVelocityTrace_le_stieltjesEnvelope
    {y : ℝ} (hy : 0 < y) :
    xiHeatCassiniVelocityTrace y ≤ xiHeatStieltjesEnvelope y := by
  have hgap := xiHeatStieltjesEnvelope_sub_velocityTrace_eq_two_mul_defect hy
  nlinarith [xiHeatCassiniOrientationDefect_nonneg hy]

/-- Complete defect vanishes exactly when every squared Xi coordinate is real. -/
theorem xiHeatCassiniOrientationDefect_eq_zero_iff
    {y : ℝ} (hy : 0 < y) :
    xiHeatCassiniOrientationDefect y = 0 ↔
      ∀ q : XiZeroCopy, (xiSquaredNode q).im = 0 := by
  constructor
  · intro hzero q
    have hle := (summable_xiHeatCassiniOrientationTerm hy).le_tsum q
      (fun r _ => xiHeatCassiniOrientationTerm_nonneg hy r)
    rw [← xiHeatCassiniOrientationDefect, hzero] at hle
    have hterm : xiHeatCassiniOrientationTerm y q = 0 :=
      le_antisymm hle (xiHeatCassiniOrientationTerm_nonneg hy q)
    exact (xiHeatCassiniOrientationTerm_eq_zero_iff hy q).mp hterm
  · intro hall
    rw [xiHeatCassiniOrientationDefect]
    have hzero : xiHeatCassiniOrientationTerm y = fun _ => 0 := by
      funext q
      exact (xiHeatCassiniOrientationTerm_eq_zero_iff hy q).2 (hall q)
    rw [hzero]
    simp

/-- **One-scalar cross-route RH criterion.**  At every positive shift, the common parabolic/Cassini
orientation gap vanishes exactly under RH. -/
theorem riemannHypothesis_iff_xiHeatCassiniOrientationDefect_eq_zero
    {y : ℝ} (hy : 0 < y) :
    RiemannHypothesis ↔ xiHeatCassiniOrientationDefect y = 0 := by
  rw [xiHeatCassiniOrientationDefect_eq_zero_iff hy]
  constructor
  · intro hRH q
    exact xiSquaredNode_im_eq_zero_of_riemannHypothesis hRH q
  · intro hall
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have him : (xiSpectralPoint q).im = 0 := by
      by_contra hoff
      exact xiSpectralSq_im_ne_zero_of_im_ne_zero hoff (by
        simpa only [xiSquaredNode] using hall q)
    refine ⟨(xiSpectralPoint q).re, ?_⟩
    conv_lhs => rw [← Complex.re_add_im (xiSpectralPoint q)]
    rw [him]
    simp

/-- Equivalent midpoint equality: RH exactly when the phase-linear response is the common value
of its heat-envelope and Cassini-velocity bounds. -/
theorem riemannHypothesis_iff_xiHeatStieltjesEnvelope_eq_re_moment
    {y : ℝ} (hy : 0 < y) :
    RiemannHypothesis ↔
      xiHeatStieltjesEnvelope y = (xiShiftedReciprocalMoment y 0).re := by
  rw [riemannHypothesis_iff_xiHeatCassiniOrientationDefect_eq_zero hy,
    xiHeatCassiniOrientationDefect_eq_envelope_sub_re_moment hy, sub_eq_zero]

/-- Cross-route equality criterion: Route T's heat envelope and Route U's Cassini velocity agree
exactly under RH. -/
theorem riemannHypothesis_iff_xiHeatStieltjesEnvelope_eq_velocityTrace
    {y : ℝ} (hy : 0 < y) :
    RiemannHypothesis ↔
      xiHeatStieltjesEnvelope y = xiHeatCassiniVelocityTrace y := by
  rw [riemannHypothesis_iff_xiHeatCassiniOrientationDefect_eq_zero hy]
  constructor
  · intro hzero
    have hgap := xiHeatStieltjesEnvelope_sub_velocityTrace_eq_two_mul_defect hy
    rw [hzero, mul_zero] at hgap
    exact sub_eq_zero.mp hgap
  · intro heq
    have hgap := xiHeatStieltjesEnvelope_sub_velocityTrace_eq_two_mul_defect hy
    rw [heq, sub_self] at hgap
    nlinarith

/-- Terminal reverse-order criterion.  Since the opposite order is unconditional, any source-side
non-amplification law in this direction collapses the full transverse divisor. -/
theorem riemannHypothesis_iff_xiHeatStieltjesEnvelope_le_velocityTrace
    {y : ℝ} (hy : 0 < y) :
    RiemannHypothesis ↔
      xiHeatStieltjesEnvelope y ≤ xiHeatCassiniVelocityTrace y := by
  rw [riemannHypothesis_iff_xiHeatStieltjesEnvelope_eq_velocityTrace hy]
  constructor
  · exact fun heq => heq.le
  · intro hle
    exact le_antisymm hle (xiHeatCassiniVelocityTrace_le_stieltjesEnvelope hy)

end

end RHTower
