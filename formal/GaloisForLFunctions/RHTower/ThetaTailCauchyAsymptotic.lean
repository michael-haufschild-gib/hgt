import GaloisForLFunctions.RHTower.ThetaTailCommonTranslationLoewnerNoGo
import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionFourthTuran
import GaloisForLFunctions.RHTower.ThetaPositiveCoshPotentialObstruction
import GaloisForLFunctions.RHTower.ThetaCuspReflectedSourceOddStationary
import Mathlib.Analysis.Calculus.LHopital
import GaloisForLFunctions.RHTower.CCMDiagonalFockLift
import GaloisForLFunctions.HTGeometry.CauchyMatrixDeterminant
import GaloisForLFunctions.HTGeometry.PositiveDefiniteMatrixLimit

/-!
# Two-term Cauchy asymptotics of the literal theta tail kernel

The complete theta source has a bounded first-logarithmic-jet error. Under a fixed
common translation this yields the leading Cauchy kernel and its constant correction,
using the exact tail derivative and L'Hopital. Every fixed finite set of distinct nodes
therefore becomes positive definite sufficiently far in the tail.

The translation threshold depends on the entire node set. These results do not exchange
rank and translation limits, prove global kernel positivity, or imply RH. In particular,
the coefficient obstruction in `LogarithmicCauchyRankBoundary` cannot be transferred to
the literal kernel without a separate estimate at growing rank.
-/

open Filter Topology MeasureTheory Set
noncomputable section
namespace RHTower.ThetaTailCauchy

private theorem shift_atTop (x : ℝ) : Tendsto (fun r : ℝ => x+r) atTop atTop :=
  tendsto_atTop_add_const_left atTop x tendsto_id

private theorem scale_shift (x r : ℝ) :
    Real.exp (-2*r)*thetaCuspMorseScale 1 (x+r) =
      Real.pi * Real.exp (2*x) := by
  unfold thetaCuspMorseScale
  simp only [Nat.cast_one, one_mul, ← Real.exp_nat_mul, Nat.cast_ofNat]
  rw [show 2*(x+r) = 2*x+2*r by ring, Real.exp_add]
  have he : Real.exp (-2*r)*Real.exp (2*r) = 1 := by
    rw [← Real.exp_add, show -2*r+2*r = 0 by ring, Real.exp_zero]
  linear_combination Real.pi*Real.exp (2*x)*he

private theorem source_score_bound {z : ℝ} (hz : 0 < z) :
    |deriv thetaCuspFullSource z / thetaCuspFullSource z +
      2*thetaCuspMorseScale 1 z| ≤ 7 := by
  let s := thetaCuspMorseScale 1 z
  let q := thetaCuspBornWittenWeight 1 z
  have hsq : q = s - 3 / 2 := thetaCuspBornWittenWeight_eq 1 z
  have hs : 3 ≤ s := le_trans Real.pi_gt_three.le
    (thetaCuspMorseScale_pi_le (by norm_num) hz.le)
  have hq : 3 / 2 ≤ q := by linarith
  have hq0 : 0 < q := by linarith
  have hi : 0 ≤ q⁻¹ := inv_nonneg.mpr hq0.le
  have hi' : q⁻¹ ≤ 2 / 3 := by
    rw [inv_eq_one_div, div_le_iff₀ hq0]
    linarith
  have hfirst : thetaCuspFirstAtomLogJetOne z = -2*s+9/2+3*q⁻¹ := by
    dsimp only [thetaCuspFirstAtomLogJetOne, thetaCuspBornWittenSuperpotential,
      thetaCuspMorseSuperpotential]
    change -2 * (s - 5 / 4 - s / q) = _
    rw [show s = q + 3 / 2 by linarith]
    field_simp
    ring
  have hden : 1 ≤ 1+thetaCuspHigherToFirstAtomLikelihoodRatio z := by
    linarith [thetaCuspHigherToFirstAtomLikelihoodRatio_nonneg hz]
  have hdenpos : 0 < 1+thetaCuspHigherToFirstAtomLikelihoodRatio z := by linarith
  have htail : |thetaCuspHigherLikelihoodLogJetOne z| ≤ 1/10 := by
    rw [thetaCuspHigherLikelihoodLogJetOne, abs_div, abs_of_pos hdenpos]
    exact (div_le_self (abs_nonneg _) hden).trans
      (abs_thetaCuspHigherLikelihoodJetOne_lt hz).le
  have heq := iteratedDeriv_one_thetaCuspLogSource_eq_full_jets hz
  rw [iteratedDeriv_one, (hasDerivAt_thetaCuspLogSource z).deriv,
    iteratedDeriv_one, hfirst] at heq
  rw [heq]
  rcases abs_le.mp htail with ⟨hl, hu⟩
  apply abs_le.mpr
  change -7 ≤ -2*s+9/2+3*q⁻¹+thetaCuspHigherLikelihoodLogJetOne z+2*s ∧
    -2*s+9/2+3*q⁻¹+thetaCuspHigherLikelihoodLogJetOne z+2*s ≤ 7
  constructor <;> linarith

/-- Leading logarithmic slope of the literal source at a fixed shifted tail point. -/
theorem scaled_source_score_limit (x : ℝ) :
    Tendsto (fun r : ℝ => Real.exp (-2*r)*deriv thetaCuspFullSource (x+r) /
      thetaCuspFullSource (x+r)) atTop (𝓝 (-2*Real.pi*Real.exp (2*x))) := by
  have hzero : Tendsto (fun r : ℝ => Real.exp (-2*r)*
      (deriv thetaCuspFullSource (x+r)/thetaCuspFullSource (x+r)+
        2*thetaCuspMorseScale 1 (x+r))) atTop (𝓝 0) := by
    have hb : ∀ᶠ r : ℝ in atTop,
        ‖Real.exp (-2*r)*(deriv thetaCuspFullSource (x+r)/thetaCuspFullSource (x+r)+
          2*thetaCuspMorseScale 1 (x+r))‖ ≤ Real.exp (-2*r)*7 := by
      filter_upwards [(shift_atTop x).eventually_gt_atTop 0] with r hr
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (source_score_bound hr) (Real.exp_pos _).le
    exact squeeze_zero_norm' hb (by
      simpa using (PositiveCoshEdge.exp_neg_rate (c := 2) (by norm_num)).mul_const 7)
  have h := hzero.sub_const (2*Real.pi*Real.exp (2*x))
  simp only [zero_sub] at h
  rw [show -(2*Real.pi*Real.exp (2*x)) = -2*Real.pi*Real.exp (2*x) by ring] at h
  apply h.congr'
  apply Eventually.of_forall
  intro r
  linear_combination 2*(scale_shift x r)

def normalizer (x y r : ℝ) : ℝ :=
  Real.exp (-2*r)*r*thetaCuspFullSource (x+r)*thetaCuspFullSource (y+r)

def normalizerJet (x y r : ℝ) : ℝ :=
  Real.exp (-2*r)*((1-2*r)*thetaCuspFullSource (x+r)*thetaCuspFullSource (y+r)+
    r*(deriv thetaCuspFullSource (x+r)*thetaCuspFullSource (y+r)+
      thetaCuspFullSource (x+r)*deriv thetaCuspFullSource (y+r)))

def normalizedSlope (x y r : ℝ) : ℝ :=
  Real.exp (-2*r)*deriv thetaCuspFullSource (x+r)/thetaCuspFullSource (x+r)+
  Real.exp (-2*r)*deriv thetaCuspFullSource (y+r)/thetaCuspFullSource (y+r)+
  Real.exp (-2*r)*(r⁻¹-2)

theorem normalizer_hasDerivAt (x y r : ℝ) :
    HasDerivAt (normalizer x y) (normalizerJet x y r) r := by
  have he := ((hasDerivAt_id r).const_mul (-2)).exp
  have hx := ((contDiff_thetaCuspFullSource.differentiable (by norm_num)).differentiableAt.hasDerivAt).comp r
    ((hasDerivAt_id r).const_add x)
  have hy := ((contDiff_thetaCuspFullSource.differentiable (by norm_num)).differentiableAt.hasDerivAt).comp r
    ((hasDerivAt_id r).const_add y)
  refine (((he.mul (hasDerivAt_id r)).mul hx).mul hy).congr_deriv ?_
  simp only [normalizerJet, Function.comp_apply, Pi.mul_apply, id_eq]
  ring

theorem normalizerJet_eq {r : ℝ} (hr : r ≠ 0) (x y : ℝ) :
    normalizerJet x y r = r*thetaCuspFullSource (x+r)*thetaCuspFullSource (y+r)*
      normalizedSlope x y r := by
  have hx := (HedenmalmThetaSource.thetaCuspFullSource_pos (x+r)).ne'
  have hy := (HedenmalmThetaSource.thetaCuspFullSource_pos (y+r)).ne'
  unfold normalizerJet normalizedSlope
  field_simp [hr, hx, hy]
  ring

theorem normalizedSlope_limit (x y : ℝ) :
    Tendsto (normalizedSlope x y) atTop
      (𝓝 (-2*Real.pi*(Real.exp (2*x)+Real.exp (2*y)))) := by
  have he := (PositiveCoshEdge.exp_neg_rate (c := 2) (by norm_num)).mul
    (tendsto_inv_atTop_zero.sub_const 2)
  have h := ((scaled_source_score_limit x).add (scaled_source_score_limit y)).add he
  convert h using 1 <;> (try funext r) <;>
    (try simp only [normalizedSlope, Pi.add_apply]) <;> ring

theorem normalizer_limit (x y : ℝ) : Tendsto (normalizer x y) atTop (𝓝 0) := by
  have h := (((PositiveCoshEdge.scaled_power_limit (c := 2) (by norm_num) 1).mul
    (tendsto_thetaCuspFullSource_atTop_zero.comp (shift_atTop x))).mul
    (tendsto_thetaCuspFullSource_atTop_zero.comp (shift_atTop y)))
  change Tendsto (fun r : ℝ => Real.exp (-2*r)*r*
    thetaCuspFullSource (x+r)*thetaCuspFullSource (y+r)) atTop (𝓝 0)
  simpa only [pow_one, zero_mul, Function.comp_apply] using h

theorem kernel_limit_zero (x y : ℝ) :
    Tendsto (fun r : ℝ => thetaTailFirstMomentKernel (x+r) (y+r)) atTop (𝓝 0) := by
  simpa only [thetaTailFirstMomentKernel_commonShift_eq_tail, id_eq] using
    (tendsto_integral_Ioi_zero (f := thetaTailCommonTranslationIntegrand x y) tendsto_id)

/-- The literal theta kernel has a Cauchy limit at every fixed pair of translated nodes. -/
theorem kernel_normalized_limit (x y : ℝ) :
    Tendsto (fun r : ℝ => thetaTailFirstMomentKernel (x+r) (y+r) / normalizer x y r)
      atTop (𝓝 (1/(Real.pi*(Real.exp (2*x)+Real.exp (2*y))))) := by
  have hc : -2*Real.pi*(Real.exp (2*x)+Real.exp (2*y)) ≠ 0 := by
    have hpi := Real.pi_pos
    have hx := Real.exp_pos (2*x)
    have hy := Real.exp_pos (2*y)
    nlinarith
  have hs := normalizedSlope_limit x y
  have hne : ∀ᶠ r : ℝ in atTop, normalizedSlope x y r ≠ 0 :=
    hs.eventually (eventually_ne_nhds hc)
  have hjet : ∀ᶠ r : ℝ in atTop, normalizerJet x y r ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hne] with r hr hn
    rw [normalizerJet_eq hr.ne']
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hr.ne'
      (HedenmalmThetaSource.thetaCuspFullSource_pos (x+r)).ne')
      (HedenmalmThetaSource.thetaCuspFullSource_pos (y+r)).ne') hn
  have hratio : Tendsto (fun r : ℝ => -thetaTailCommonTranslationGenerator r x y /
      normalizerJet x y r) atTop
      (𝓝 (1/(Real.pi*(Real.exp (2*x)+Real.exp (2*y))))) := by
    have htop : Tendsto (fun r : ℝ => -(2+(x+y)*r⁻¹)) atTop (𝓝 (-2 : ℝ)) := by
      simpa using ((tendsto_inv_atTop_zero.const_mul (x+y)).const_add 2).neg
    have h := htop.div hs hc
    have heq : (-2 : ℝ)/(-2*Real.pi*(Real.exp (2*x)+Real.exp (2*y))) =
        1/(Real.pi*(Real.exp (2*x)+Real.exp (2*y))) := by
      field_simp
    rw [heq] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    rw [normalizerJet_eq hr.ne']
    simp only [Pi.div_apply]
    unfold thetaTailCommonTranslationGenerator
    field_simp [hr.ne', (HedenmalmThetaSource.thetaCuspFullSource_pos (x+r)).ne',
      (HedenmalmThetaSource.thetaCuspFullSource_pos (y+r)).ne']
    ring
  exact HasDerivAt.lhopital_zero_atTop
    (Eventually.of_forall fun r => hasDerivAt_thetaTailFirstMomentKernel_commonShift r x y)
    (Eventually.of_forall fun r => normalizer_hasDerivAt x y r) hjet
    (kernel_limit_zero x y) (normalizer_limit x y) hratio

open Matrix

def sourceMatrix {n : ℕ} (x : Fin n → ℝ) (r : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => thetaTailFirstMomentKernel (x i+r) (x j+r)

def normalizedMatrix {n : ℕ} (x : Fin n → ℝ) (r : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Real.pi * (thetaTailFirstMomentKernel (x i+r) (x j+r) / normalizer (x i) (x j) r)

private theorem cauchy_posDef {n : ℕ} (u : Fin n → ℝ) (hu : ∀ i, 0 < u i)
    (hinj : Function.Injective u) :
    (GaloisForLFunctions.HTGeometry.cauchyMatrix u u).PosDef := by
  classical
  have hs : (GaloisForLFunctions.HTGeometry.cauchyMatrix u u).PosSemidef := by
    simpa only [GaloisForLFunctions.HTGeometry.cauchyMatrix,
      GaloisForLFunctions.RHTower.kernelMatrix, GaloisForLFunctions.RHTower.cauchyKernel,
      one_div] using GaloisForLFunctions.RHTower.posSemidef_cauchyMatrix hu
  apply hs.posDef_iff_det_ne_zero.mpr
  have hd := GaloisForLFunctions.HTGeometry.det_cauchyMatrix u u
    (fun i j => (add_pos (hu i) (hu j)).ne')
  have hp : (∏ i, ∏ j ∈ Finset.Ioi i, ((u i-u j)*(u i-u j))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hne : u i-u j ≠ 0 := sub_ne_zero.mpr (fun he =>
      (ne_of_lt (Finset.mem_Ioi.mp hj)) (hinj he))
    exact mul_ne_zero hne hne
  intro hn
  rw [hn, zero_mul] at hd
  exact hp hd.symm

/-- Every fixed distinct-node pattern has a strictly positive Cauchy limit. -/
theorem normalizedMatrix_eventually_posDef {n : ℕ} (x : Fin n → ℝ)
    (hinj : Function.Injective x) :
    ∀ᶠ r : ℝ in atTop, (normalizedMatrix x r).PosDef := by
  let u : Fin n → ℝ := fun i => Real.exp (2*x i)
  have hu : ∀ i, 0 < u i := fun i => Real.exp_pos _
  have hui : Function.Injective u := by
    intro i j hij
    have he := Real.exp_injective hij
    apply hinj
    change 2*x i = 2*x j at he
    linarith
  apply GaloisForLFunctions.HTGeometry.posDef_eventually_of_tendsto
    (cauchy_posDef u hu hui)
  · apply Eventually.of_forall
    intro r
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, normalizedMatrix]
    rw [thetaTailFirstMomentKernel_comm (x j+r) (x i+r)]
    congr 2
    unfold normalizer
    ring
  · intro i j
    have h := (kernel_normalized_limit (x i) (x j)).const_mul Real.pi
    convert h using 1 <;>
      simp only [normalizedMatrix, GaloisForLFunctions.HTGeometry.cauchyMatrix,
        Matrix.of_apply, u] <;>
      field_simp [Real.pi_ne_zero]

/-- Every fixed finite set of distinct nodes becomes positive definite under sufficiently
large common translation. The threshold is allowed to depend on the whole node set. -/
theorem sourceMatrix_eventually_posDef {n : ℕ} (x : Fin n → ℝ)
    (hinj : Function.Injective x) :
    ∀ᶠ r : ℝ in atTop, (sourceMatrix x r).PosDef := by
  classical
  filter_upwards [normalizedMatrix_eventually_posDef x hinj,
    eventually_gt_atTop (0 : ℝ)] with r hM hr
  let d : Fin n → ℝ := fun i => thetaCuspFullSource (x i+r)
  have hd : ∀ i, d i ≠ 0 := fun i =>
    (HedenmalmThetaSource.thetaCuspFullSource_pos _).ne'
  have hi : Function.Injective (Matrix.diagonal d).mulVec := by
    intro a b hab
    funext i
    have he := congrFun hab i
    simp only [Matrix.mulVec_diagonal] at he
    exact mul_left_cancel₀ (hd i) he
  have hcon := hM.conjTranspose_mul_mul_same hi
  have hscale : 0 < Real.exp (-2*r)*r/Real.pi :=
    div_pos (mul_pos (Real.exp_pos _) hr) Real.pi_pos
  have hpos := hcon.smul hscale
  convert hpos using 1
  ext i j
  simp only [sourceMatrix, Matrix.smul_apply, smul_eq_mul,
    Matrix.diagonal_conjTranspose, star_trivial, Matrix.diagonal_mul, Matrix.mul_diagonal,
    normalizedMatrix]
  dsimp [d, normalizer]
  field_simp [Real.pi_ne_zero, Real.exp_ne_zero, hr.ne',
    (HedenmalmThetaSource.thetaCuspFullSource_pos (x i+r)).ne',
    (HedenmalmThetaSource.thetaCuspFullSource_pos (x j+r)).ne']

/-- Error in the leading source score, expressed without truncating the theta sum. -/
def scoreRemainder (x r : ℝ) : ℝ :=
  Real.exp (-2*r)*deriv thetaCuspFullSource (x+r)/thetaCuspFullSource (x+r)+
    2*Real.pi*Real.exp (2*x)

private theorem scoreRemainder_eq (x r : ℝ) :
    scoreRemainder x r = Real.exp (-2*r)*
      (deriv thetaCuspFullSource (x+r)/thetaCuspFullSource (x+r)+
        2*thetaCuspMorseScale 1 (x+r)) := by
  unfold scoreRemainder
  linear_combination -2*(scale_shift x r)

/-- Every fixed polynomial multiple of the scaled score error vanishes. -/
theorem polynomial_scoreRemainder_limit (x : ℝ) (k : ℕ) :
    Tendsto (fun r : ℝ => r^k*scoreRemainder x r) atTop (𝓝 0) := by
  have hb : ∀ᶠ r : ℝ in atTop, ‖r^k*scoreRemainder x r‖ ≤
      (Real.exp (-2*r)*r^k)*7 := by
    filter_upwards [(shift_atTop x).eventually_gt_atTop 0,
      eventually_gt_atTop (0 : ℝ)] with r hx hr
    rw [scoreRemainder_eq, norm_mul, Real.norm_eq_abs, abs_of_pos (pow_pos hr k),
      Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ r^k*(Real.exp (-2*r)*7) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (source_score_bound hx) (Real.exp_pos _).le)
        (pow_nonneg hr.le k)
      _ = _ := by ring
  exact squeeze_zero_norm' hb (by
    simpa using (PositiveCoshEdge.scaled_power_limit (c := 2) (by norm_num) k).mul_const 7)

def pairScale (x y : ℝ) : ℝ := Real.pi*(Real.exp (2*x)+Real.exp (2*y))

theorem pairScale_pos (x y : ℝ) : 0 < pairScale x y :=
  mul_pos Real.pi_pos (add_pos (Real.exp_pos _) (Real.exp_pos _))

def pairProduct (x y r : ℝ) : ℝ :=
  thetaCuspFullSource (x+r)*thetaCuspFullSource (y+r)

def baseNormalizer (x y r : ℝ) : ℝ := Real.exp (-2*r)*pairProduct x y r

def baseSlope (x y r : ℝ) : ℝ :=
  Real.exp (-2*r)*deriv thetaCuspFullSource (x+r)/thetaCuspFullSource (x+r)+
  Real.exp (-2*r)*deriv thetaCuspFullSource (y+r)/thetaCuspFullSource (y+r)-
  2*Real.exp (-2*r)

private theorem pairProduct_ne_zero (x y r : ℝ) : pairProduct x y r ≠ 0 :=
  mul_ne_zero (HedenmalmThetaSource.thetaCuspFullSource_pos _).ne'
    (HedenmalmThetaSource.thetaCuspFullSource_pos _).ne'

theorem baseNormalizer_hasDerivAt (x y r : ℝ) :
    HasDerivAt (baseNormalizer x y) (pairProduct x y r*baseSlope x y r) r := by
  have he := ((hasDerivAt_id r).const_mul (-2)).exp
  have hx := ((contDiff_thetaCuspFullSource.differentiable (by norm_num)).differentiableAt.hasDerivAt).comp r
    ((hasDerivAt_id r).const_add x)
  have hy := ((contDiff_thetaCuspFullSource.differentiable (by norm_num)).differentiableAt.hasDerivAt).comp r
    ((hasDerivAt_id r).const_add y)
  refine (he.mul (hx.mul hy)).congr_deriv ?_
  simp only [pairProduct, baseSlope, Function.comp_apply, Pi.mul_apply, id_eq]
  field_simp [(HedenmalmThetaSource.thetaCuspFullSource_pos (x+r)).ne',
    (HedenmalmThetaSource.thetaCuspFullSource_pos (y+r)).ne']
  ring

theorem baseSlope_limit (x y : ℝ) :
    Tendsto (baseSlope x y) atTop (𝓝 (-2*pairScale x y)) := by
  have h := ((scaled_source_score_limit x).add (scaled_source_score_limit y)).sub
    ((PositiveCoshEdge.exp_neg_rate (c := 2) (by norm_num)).const_mul 2)
  convert h using 1 <;> (try funext r) <;>
    (try simp only [baseSlope, pairScale]) <;> ring

theorem polynomial_baseSlope_error_limit (x y : ℝ) (k : ℕ) :
    Tendsto (fun r : ℝ => r^k*(baseSlope x y r+2*pairScale x y)) atTop (𝓝 0) := by
  have h := ((polynomial_scoreRemainder_limit x k).add
    (polynomial_scoreRemainder_limit y k)).sub
    ((PositiveCoshEdge.scaled_power_limit (c := 2) (by norm_num) k).const_mul 2)
  convert h using 1 <;> (try funext r) <;>
    (try simp only [baseSlope, pairScale, scoreRemainder]) <;> ring

theorem baseNormalizer_limit (x y : ℝ) :
    Tendsto (baseNormalizer x y) atTop (𝓝 0) := by
  have h := (PositiveCoshEdge.exp_neg_rate (c := 2) (by norm_num)).mul
    ((tendsto_thetaCuspFullSource_atTop_zero.comp (shift_atTop x)).mul
      (tendsto_thetaCuspFullSource_atTop_zero.comp (shift_atTop y)))
  change Tendsto (fun r : ℝ => Real.exp (-2*r)*
    (thetaCuspFullSource (x+r)*thetaCuspFullSource (y+r))) atTop (𝓝 0)
  simpa only [zero_mul, Function.comp_apply] using h

/-- Subtracting the leading and constant terms leaves a vanishing normalized remainder. -/
theorem kernel_two_term_limit (x y : ℝ) :
    Tendsto (fun r : ℝ => thetaTailFirstMomentKernel (x+r) (y+r)/baseNormalizer x y r -
      (2*r+x+y)/(2*pairScale x y)) atTop (𝓝 0) := by
  let A := pairScale x y
  let D := baseNormalizer x y
  let P := pairProduct x y
  let T := baseSlope x y
  let L : ℝ → ℝ := fun r => (2*r+x+y)/(2*A)
  let N : ℝ → ℝ := fun r => thetaTailFirstMomentKernel (x+r) (y+r)-D r*L r
  let J : ℝ → ℝ := fun r => -(2*r+x+y)*P r-(P r*T r*L r+D r/A)
  have hA : A ≠ 0 := (pairScale_pos x y).ne'
  have hT : Tendsto T atTop (𝓝 (-2*A)) := baseSlope_limit x y
  have hT0 : -2*A ≠ 0 := mul_ne_zero (by norm_num) hA
  have hTne : ∀ᶠ r : ℝ in atTop, T r ≠ 0 :=
    hT.eventually (eventually_ne_nhds hT0)
  have hD : ∀ r, HasDerivAt D (P r*T r) r := baseNormalizer_hasDerivAt x y
  have hL : ∀ r, HasDerivAt L (1/A) r := by
    intro r
    have h := (((hasDerivAt_id r).const_mul 2).add_const x |>.add_const y).div_const (2*A)
    refine h.congr_deriv ?_
    field_simp
  have hN : ∀ r, HasDerivAt N (J r) r := by
    intro r
    refine ((hasDerivAt_thetaTailFirstMomentKernel_commonShift r x y).sub
      ((hD r).mul (hL r))).congr_deriv ?_
    dsimp [J, P, pairProduct, thetaTailCommonTranslationGenerator]
    ring
  have hDL : Tendsto (fun r => D r*L r) atTop (𝓝 0) := by
    have h := ((normalizer_limit x y).div_const A).add
      ((baseNormalizer_limit x y).mul_const ((x+y)/(2*A)))
    convert h using 1 <;> (try funext r) <;>
      (try simp only [D, L, normalizer, baseNormalizer, pairProduct]) <;> ring
  have hN0 : Tendsto N atTop (𝓝 0) := by
    simpa only [sub_zero] using (kernel_limit_zero x y).sub hDL
  have hJ : Tendsto (fun r => J r/(P r*T r)) atTop (𝓝 0) := by
    have hnum : Tendsto (fun r : ℝ =>
        (2*r+x+y)*(T r+2*A)+2*Real.exp (-2*r)) atTop (𝓝 0) := by
      have h := (((polynomial_baseSlope_error_limit x y 1).const_mul 2).add
        ((polynomial_baseSlope_error_limit x y 0).const_mul (x+y))).add
        ((PositiveCoshEdge.exp_neg_rate (c := 2) (by norm_num)).const_mul 2)
      convert h using 1 <;> (try funext r) <;>
        (try simp only [pow_one, pow_zero, one_mul, T, A]) <;> ring
    have h := hnum.neg.div (hT.const_mul (2*A))
      (mul_ne_zero (mul_ne_zero (by norm_num) hA) hT0)
    simp only [neg_zero, zero_div] at h
    apply h.congr'
    filter_upwards [hTne] with r hr
    dsimp [J, L, D, baseNormalizer]
    change -((2*r+x+y)*(T r+2*A)+2*Real.exp (-2*r))/(2*A*T r) =
      (-(2*r+x+y)*P r-(P r*T r*((2*r+x+y)/(2*A))+
        Real.exp (-2*r)*P r/A))/(P r*T r)
    have hP : P r ≠ 0 := pairProduct_ne_zero x y r
    field_simp [hA, hr, hP]
    ring
  have hquot := HasDerivAt.lhopital_zero_atTop (Eventually.of_forall hN)
    (Eventually.of_forall hD) (by
      filter_upwards [hTne] with r hr
      exact mul_ne_zero (pairProduct_ne_zero x y r) hr)
    hN0 (baseNormalizer_limit x y) hJ
  apply hquot.congr'
  apply Eventually.of_forall
  intro r
  dsimp [N, L, D, A]
  have hDne : baseNormalizer x y r ≠ 0 :=
    mul_ne_zero (Real.exp_ne_zero _) (pairProduct_ne_zero x y r)
  rw [sub_div, mul_div_cancel_left₀ _ hDne]

end RHTower.ThetaTailCauchy
