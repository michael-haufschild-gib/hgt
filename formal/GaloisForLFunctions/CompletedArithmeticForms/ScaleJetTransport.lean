import GaloisForLFunctions.CompletedArithmeticForms.HyperbolicClock
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspGaussianScaleOperator

/-!
# Exact scale transport of every first-atom reflection jet

Smooth joint partial derivatives commute before restriction to the reflection
origin. The literal Gaussian scale equation therefore generates every signed
reflection moment by one scalar differential operator. The affine factor of
the actual first theta atom contributes the exact scale derivative of that
moment, with its source amplitude retained.
-/

noncomputable section

open Topology
open scoped ContDiff

namespace GaloisForLFunctions.CompletedArithmeticForms

open _root_.RHTower

/-- Differentiation in the source scale, with the reflection coordinate fixed. -/
def sourceScalePartial (F : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  deriv (fun q => F (q, z.2)) z.1

/-- Differentiation in the reflection coordinate, with the source scale fixed. -/
def sourceReflectionPartial (F : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  deriv (fun t => F (z.1, t)) z.2

private theorem sourceScalePartial_eq_fderiv {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (z : ℝ × ℝ) :
    sourceScalePartial F z = fderiv ℝ F z (1, 0) :=
  ((hF.differentiable (by simp) z).hasFDerivAt.comp_hasDerivAt z.1
    ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))).deriv

private theorem sourceReflectionPartial_eq_fderiv {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (z : ℝ × ℝ) :
    sourceReflectionPartial F z = fderiv ℝ F z (0, 1) :=
  ((hF.differentiable (by simp) z).hasFDerivAt.comp_hasDerivAt z.2
    ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))).deriv

theorem contDiff_sourceScalePartial {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (sourceScalePartial F) := by
  have he : sourceScalePartial F = fun z => fderiv ℝ F z (1, 0) :=
    funext (sourceScalePartial_eq_fderiv hF)
  rw [he]
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact (hF.contDiffAt.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

theorem contDiff_sourceReflectionPartial {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (sourceReflectionPartial F) := by
  have he : sourceReflectionPartial F = fun z => fderiv ℝ F z (0, 1) :=
    funext (sourceReflectionPartial_eq_fderiv hF)
  rw [he]
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact (hF.contDiffAt.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

/-- The two source directions commute on their full smooth domain. -/
theorem source_partials_commute {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    sourceScalePartial (sourceReflectionPartial F) =
      sourceReflectionPartial (sourceScalePartial F) := by
  have hq : sourceScalePartial F = fun z => fderiv ℝ F z (1, 0) :=
    funext (sourceScalePartial_eq_fderiv hF)
  have ht : sourceReflectionPartial F = fun z => fderiv ℝ F z (0, 1) :=
    funext (sourceReflectionPartial_eq_fderiv hF)
  rw [hq, ht]
  funext z
  have hdf : ContDiffAt ℝ ∞ (fderiv ℝ F) z :=
    hF.contDiffAt.fderiv_right (m := ∞) (by simp)
  have hd := (hdf.differentiableAt (by simp)).hasFDerivAt
  have hqt := (hd.clm_apply (hasFDerivAt_const ((0, 1) : ℝ × ℝ) z)).comp_hasDerivAt z.1
    ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))
  have htq := (hd.clm_apply (hasFDerivAt_const ((1, 0) : ℝ × ℝ) z)).comp_hasDerivAt z.2
    ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))
  have heq : sourceScalePartial (fun z => fderiv ℝ F z (0, 1)) z =
      fderiv ℝ (fderiv ℝ F) z (1, 0) (0, 1) := by
    simpa [sourceScalePartial, Function.comp_def] using hqt.deriv
  have het : sourceReflectionPartial (fun z => fderiv ℝ F z (1, 0)) z =
      fderiv ℝ (fderiv ℝ F) z (0, 1) (1, 0) := by
    simpa [sourceReflectionPartial, Function.comp_def] using htq.deriv
  rw [heq, het]
  exact hF.contDiffAt.isSymmSndFDerivAt
    (by norm_num; exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) (1, 0) (0, 1)

/-- Reflection differentiation before the source scale is restricted. -/
def sourceReflectionJet (F : ℝ × ℝ → ℝ) : ℕ → ℝ × ℝ → ℝ
  | 0 => F
  | n + 1 => sourceReflectionPartial (sourceReflectionJet F n)

theorem contDiff_sourceReflectionJet {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    ContDiff ℝ ∞ (sourceReflectionJet F n) := by
  induction n with
  | zero => exact hF
  | succ n ih => exact contDiff_sourceReflectionPartial ih

theorem sourceReflectionJet_eq_iteratedDeriv (F : ℝ × ℝ → ℝ) (n : ℕ) (z : ℝ × ℝ) :
    sourceReflectionJet F n z = iteratedDeriv n (fun t => F (z.1, t)) z.2 := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ]
    change deriv (fun t => sourceReflectionJet F n (z.1, t)) z.2 = _
    congr 1
    funext t
    exact ih (z.1, t)

private theorem contDiffAt_reflectionSlice {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (n : ℕ) (q t : ℝ) :
    ContDiffAt ℝ n (fun u => F (q, u)) t :=
  ((hF.of_le (WithTop.coe_le_coe.mpr (le_top : (n : ℕ∞) ≤ ⊤))).comp
    (contDiff_const.prodMk contDiff_id)).contDiffAt

private theorem sourceReflectionJet_iterate (F : ℝ × ℝ → ℝ) (m n : ℕ) :
    sourceReflectionJet (sourceReflectionJet F m) n = sourceReflectionJet F (m + n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change sourceReflectionPartial (sourceReflectionJet (sourceReflectionJet F m) n) =
      sourceReflectionPartial (sourceReflectionJet F (m + n))
    rw [ih]

/-- Every finite reflection jet commutes with source-scale differentiation. -/
theorem sourceReflectionJet_scalePartial {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    sourceReflectionJet (sourceScalePartial F) n =
      sourceScalePartial (sourceReflectionJet F n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change sourceReflectionPartial (sourceReflectionJet (sourceScalePartial F) n) =
      sourceScalePartial (sourceReflectionPartial (sourceReflectionJet F n))
    rw [ih]
    exact (source_partials_commute (contDiff_sourceReflectionJet hF n)).symm

private theorem sourceReflectionJet_scale_mul (c : ℝ → ℝ) (F : ℝ × ℝ → ℝ) (n : ℕ) :
    sourceReflectionJet (fun z => c z.1 * F z) n =
      fun z => c z.1 * sourceReflectionJet F n z := by
  funext z
  simp only [sourceReflectionJet_eq_iteratedDeriv, _root_.iteratedDeriv_const_mul_field]

private theorem sourceReflectionJet_neg (F : ℝ × ℝ → ℝ) (n : ℕ) :
    sourceReflectionJet (fun z => -F z) n = fun z => -sourceReflectionJet F n z := by
  funext z
  simp only [sourceReflectionJet_eq_iteratedDeriv]
  exact iteratedDeriv_neg n (fun t => F (z.1, t)) z.2

private theorem sourceReflectionJet_add {F G : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (n : ℕ) :
    sourceReflectionJet (fun z => F z + G z) n =
      fun z => sourceReflectionJet F n z + sourceReflectionJet G n z := by
  funext z
  simp only [sourceReflectionJet_eq_iteratedDeriv]
  exact iteratedDeriv_fun_add
    (contDiffAt_reflectionSlice hF n z.1 z.2)
    (contDiffAt_reflectionSlice hG n z.1 z.2)

private theorem sourceReflectionJet_sub {F G : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (n : ℕ) :
    sourceReflectionJet (fun z => F z - G z) n =
      fun z => sourceReflectionJet F n z - sourceReflectionJet G n z := by
  funext z
  simp only [sourceReflectionJet_eq_iteratedDeriv]
  exact iteratedDeriv_fun_sub
    (contDiffAt_reflectionSlice hF n z.1 z.2)
    (contDiffAt_reflectionSlice hG n z.1 z.2)

private def gaussianScaleSource (z : ℝ × ℝ) : ℝ := ThetaCuspOddFour.gaussian z.1 z.2

private theorem contDiff_gaussianScaleSource : ContDiff ℝ ∞ gaussianScaleSource := by
  unfold gaussianScaleSource ThetaCuspOddFour.gaussian
  fun_prop

private theorem gaussianScaleSource_equation :
    (fun z => -sourceReflectionPartial (sourceReflectionPartial gaussianScaleSource) z) =
      fun z => 8 * z.1 * gaussianScaleSource z +
        (16 * z.1 ^ 2 - 4 * z.1) * sourceScalePartial gaussianScaleSource z -
        4 * z.1 ^ 2 * sourceScalePartial (sourceScalePartial gaussianScaleSource) z := by
  funext z
  exact thetaCuspGaussian_reflection_second_eq_scale z.1 z.2

private theorem gaussianScaleSource_jet_equation (n : ℕ) (z : ℝ × ℝ) :
    -sourceReflectionJet gaussianScaleSource (n + 2) z =
      8 * z.1 * sourceReflectionJet gaussianScaleSource n z +
        (16 * z.1 ^ 2 - 4 * z.1) *
          sourceScalePartial (sourceReflectionJet gaussianScaleSource n) z -
        4 * z.1 ^ 2 * sourceScalePartial
          (sourceScalePartial (sourceReflectionJet gaussianScaleSource n)) z := by
  have hF := contDiff_gaussianScaleSource
  have hq := contDiff_sourceScalePartial hF
  have hqq := contDiff_sourceScalePartial hq
  have h1 : ContDiff ℝ ∞ (fun z : ℝ × ℝ => 8 * z.1 * gaussianScaleSource z) := by fun_prop
  have h2 : ContDiff ℝ ∞ (fun z : ℝ × ℝ =>
      (16 * z.1 ^ 2 - 4 * z.1) * sourceScalePartial gaussianScaleSource z) := by fun_prop
  have h3 : ContDiff ℝ ∞ (fun z : ℝ × ℝ =>
      4 * z.1 ^ 2 * sourceScalePartial (sourceScalePartial gaussianScaleSource) z) := by fun_prop
  have h := congrArg (fun F => sourceReflectionJet F n) gaussianScaleSource_equation
  rw [sourceReflectionJet_neg, sourceReflectionJet_sub (h1.add h2) h3,
    sourceReflectionJet_add h1 h2,
    sourceReflectionJet_scale_mul (fun q => 8 * q),
    sourceReflectionJet_scale_mul (fun q => 16 * q ^ 2 - 4 * q),
    sourceReflectionJet_scale_mul (fun q => 4 * q ^ 2)] at h
  simp only [sourceReflectionJet_scalePartial hq, sourceReflectionJet_scalePartial hF] at h
  have ht : sourceReflectionJet
      (sourceReflectionPartial (sourceReflectionPartial gaussianScaleSource)) n =
        sourceReflectionJet gaussianScaleSource (n + 2) := by
    change sourceReflectionJet (sourceReflectionJet gaussianScaleSource 2) n = _
    rw [sourceReflectionJet_iterate, Nat.add_comm 2 n]
  rw [ht] at h
  exact congrFun h z

/-- Signed Gaussian reflection moments in the physical source coordinate. -/
def gaussianScaleSignedJet (k : ℕ) (q : ℝ) : ℝ :=
  (-1 : ℝ) ^ k * iteratedDeriv (2 * k) (ThetaCuspOddFour.gaussian q) 0

private theorem gaussianScaleSignedJet_eq_joint (k : ℕ) :
    gaussianScaleSignedJet k = fun q =>
      (-1 : ℝ) ^ k * sourceReflectionJet gaussianScaleSource (2 * k) (q, 0) := by
  funext q
  rw [sourceReflectionJet_eq_iteratedDeriv]
  rfl

private theorem gaussianScaleSignedJet_deriv (k : ℕ) :
    deriv (gaussianScaleSignedJet k) = fun q =>
      (-1 : ℝ) ^ k * sourceScalePartial
        (sourceReflectionJet gaussianScaleSource (2 * k)) (q, 0) := by
  rw [gaussianScaleSignedJet_eq_joint, _root_.deriv_const_mul_field']
  rfl

private theorem gaussianScaleSignedJet_second_deriv (k : ℕ) :
    deriv (deriv (gaussianScaleSignedJet k)) = fun q =>
      (-1 : ℝ) ^ k * sourceScalePartial (sourceScalePartial
        (sourceReflectionJet gaussianScaleSource (2 * k))) (q, 0) := by
  rw [gaussianScaleSignedJet_deriv, _root_.deriv_const_mul_field']
  rfl

@[simp] theorem gaussianScaleSignedJet_zero (q : ℝ) : gaussianScaleSignedJet 0 q = 1 := by
  simp [gaussianScaleSignedJet, ThetaCuspOddFour.gaussian]

/-- The exact scalar differential recurrence holds at every reflection order and every scale. -/
theorem gaussianScaleSignedJet_succ (k : ℕ) (q : ℝ) :
    gaussianScaleSignedJet (k + 1) q =
      8 * q * gaussianScaleSignedJet k q +
        (16 * q ^ 2 - 4 * q) * deriv (gaussianScaleSignedJet k) q -
        4 * q ^ 2 * deriv (deriv (gaussianScaleSignedJet k)) q := by
  have h := gaussianScaleSource_jet_equation (2 * k) (q, 0)
  rw [show 2 * k + 2 = 2 * (k + 1) by omega] at h
  rw [gaussianScaleSignedJet_second_deriv, gaussianScaleSignedJet_deriv,
    gaussianScaleSignedJet_eq_joint (k + 1), gaussianScaleSignedJet_eq_joint k]
  dsimp only [Prod.fst] at h ⊢
  rw [pow_succ]
  linear_combination (-1 : ℝ) ^ k * h

/-- The affine first-atom source contributes the exact scale derivative at every order. -/
theorem firstAtomSignedMoment_eq_scaleJet (k : ℕ) (x : ℝ) :
    (-1 : ℝ) ^ k * thetaCuspFirstAtomReflectionJet (2 * k) x =
      firstAtomClockAmplitude x *
        (firstAtomClockShape x * gaussianScaleSignedJet k
            (thetaCuspSingleAtomReflectionScale 1 x) +
          6 * thetaCuspSingleAtomReflectionScale 1 x *
            deriv (gaussianScaleSignedJet k) (thetaCuspSingleAtomReflectionScale 1 x)) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hsource : (fun t => thetaCuspSourceTerm (x + t) 1 * thetaCuspSourceTerm (x - t) 1) =
      fun t => firstAtomClockAmplitude x *
        (firstAtomClockShape x * gaussianScaleSource (q, t) +
          (6 * q) * sourceScalePartial gaussianScaleSource (q, t)) := by
    funext t
    exact thetaCuspFirstAtomPair_eq_gaussian_scale_deriv x t
  have hF := contDiff_gaussianScaleSource
  have hq := contDiff_sourceScalePartial hF
  have hleft : ContDiffAt ℝ (2 * k) (fun t => firstAtomClockShape x * gaussianScaleSource (q, t)) 0 :=
    contDiffAt_const.mul (contDiffAt_reflectionSlice hF (2 * k) q 0)
  have hright : ContDiffAt ℝ (2 * k)
      (fun t => (6 * q) * sourceScalePartial gaussianScaleSource (q, t)) 0 :=
    contDiffAt_const.mul (contDiffAt_reflectionSlice hq (2 * k) q 0)
  have hcomm : iteratedDeriv (2 * k)
      (fun t => sourceScalePartial gaussianScaleSource (q, t)) 0 =
        sourceScalePartial (sourceReflectionJet gaussianScaleSource (2 * k)) (q, 0) := by
    rw [← sourceReflectionJet_eq_iteratedDeriv (sourceScalePartial gaussianScaleSource) (2 * k) (q, 0),
      sourceReflectionJet_scalePartial contDiff_gaussianScaleSource]
  rw [thetaCuspFirstAtomReflectionJet, hsource, _root_.iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_add hleft hright, _root_.iteratedDeriv_const_mul_field,
    _root_.iteratedDeriv_const_mul_field, hcomm,
    gaussianScaleSignedJet_deriv, gaussianScaleSignedJet_eq_joint]
  dsimp only
  rw [sourceReflectionJet_eq_iteratedDeriv gaussianScaleSource (2 * k) (q, 0)]
  ring

#print axioms source_partials_commute
#print axioms sourceReflectionJet_scalePartial
#print axioms gaussianScaleSignedJet_succ
#print axioms firstAtomSignedMoment_eq_scaleJet

end GaloisForLFunctions.CompletedArithmeticForms
