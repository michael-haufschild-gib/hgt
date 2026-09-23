import GaloisForLFunctions.RHTower.ThetaCuspHawkingMassDilationOrderBlindnessNoGo
import GaloisForLFunctions.RHTower.XiPoissonProgression
import GaloisForLFunctions.RHTower.XiWardSpectralBudgetSumRule

/-!
# Bifurcation Schwarzian tilt rigidity for theta Hawking mirrors

For the physical timelike theta ray
`p_{a,lambda}(v) = v + lambda * exp(a*v) * thetaCuspFullSource(v)`,
this module evaluates the exact Davies--Fulling Schwarzian conformal anomaly at the reflection
center `v = 0`.  Writing `c = thetaCuspFullSource(0) > 0` and
`d = thetaCuspFullSource''(0)`, its reflected difference is an exact rational function:

`S_a(lambda) - S_{-a}(lambda)
  = 2*lambda*A/(1-(lambda*a*c)^(2 : ℕ))
    + 6*lambda^(3 : ℕ)*a*c*B^(2 : ℕ)/(1-(lambda*a*c)^(2 : ℕ))^(2 : ℕ)`,

where `A = a^(3 : ℕ)*c + 3*a*d` and `B = a^(2 : ℕ)*c + d`.

**[PAPER-PROVED] [LEAN-PROVED] [HAWKING-SPECIFIC]** Neutrality of this nonlinear conformal-anomaly
output for every safe mirror coupling is equivalent to `a = 0`.  Two explicit safe couplings
already suffice.  Consequently every off-critical Xi divisor tilt is unmasked by unequal
reflected conformal flux at some genuine timelike coupling.  Generic KMS, CCR, group, inverse,
Krein, or passivity laws are not used.

This is a local Davies--Fulling black-hole-collapse observable, not a stationary Jost pole and not
an EKG/Teukolsky optical identity.  Remaining RH-bearing producer is dynamical incidence:
Einstein--Klein--Gordon/Teukolsky evolution must either force reflected divisor sectors to have
this same anomaly output, which the rigidity theorem sends to `a = 0`, or convert the proven
asymmetry into unavoidable cross-sector scattering/backreaction.

Physical provenance: Anderson--Good--Evans, arXiv:1507.03489, identifies the exact moving-mirror
and null-shell-collapse Bogoliubov correspondence.  Hotta--Shino--Yoshimura,
arXiv:hep-th/9403139, and Tuning--Verlinde, arXiv:hep-th/9605063, study mirror backreaction.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Theta source value at horizon crossing. -/
def thetaCuspHawkingBifurcationThetaValue : ℝ := thetaCuspFullSource 0

/-- Even second theta jet at horizon crossing. -/
def thetaCuspHawkingBifurcationThetaSecondJet : ℝ :=
  iteratedDeriv 2 thetaCuspFullSource 0

lemma thetaCuspHawkingTiltedSourceJetOne_bifurcation (a : ℝ) :
    iteratedDeriv 1 (thetaCuspTiltedSource a) 0 = a * thetaCuspHawkingBifurcationThetaValue := by
  rw [iteratedDeriv_thetaCuspTiltedSource]
  have hodd : iteratedDeriv 1 thetaCuspFullSource 0 = 0 :=
    iteratedDeriv_thetaCuspFullSource_zero_of_odd (by decide)
  norm_num [Finset.sum_range_succ, hodd, thetaCuspHawkingBifurcationThetaValue]

lemma thetaCuspHawkingTiltedSourceJetTwo_bifurcation (a : ℝ) :
    iteratedDeriv 2 (thetaCuspTiltedSource a) 0 = a ^ (2 : ℕ) * thetaCuspHawkingBifurcationThetaValue + thetaCuspHawkingBifurcationThetaSecondJet := by
  rw [iteratedDeriv_thetaCuspTiltedSource]
  have hodd : iteratedDeriv 1 thetaCuspFullSource 0 = 0 :=
    iteratedDeriv_thetaCuspFullSource_zero_of_odd (by decide)
  norm_num [Finset.sum_range_succ, hodd, thetaCuspHawkingBifurcationThetaValue, thetaCuspHawkingBifurcationThetaSecondJet]
  ring

lemma thetaCuspHawkingTiltedSourceJetThree_bifurcation (a : ℝ) :
    iteratedDeriv 3 (thetaCuspTiltedSource a) 0 = a ^ (3 : ℕ) * thetaCuspHawkingBifurcationThetaValue + 3 * a * thetaCuspHawkingBifurcationThetaSecondJet := by
  rw [iteratedDeriv_thetaCuspTiltedSource]
  have hodd1 : iteratedDeriv 1 thetaCuspFullSource 0 = 0 :=
    iteratedDeriv_thetaCuspFullSource_zero_of_odd (by decide)
  have hodd3 : iteratedDeriv 3 thetaCuspFullSource 0 = 0 :=
    iteratedDeriv_thetaCuspFullSource_zero_of_odd (by decide)
  norm_num [Finset.sum_range_succ, hodd1, hodd3, thetaCuspHawkingBifurcationThetaValue, thetaCuspHawkingBifurcationThetaSecondJet]
  ring

lemma thetaCuspHawkingRayJetOne_bifurcation (a lambda : ℝ) :
    thetaCuspHawkingRayJetOne a lambda 0 = 1 + lambda * (a * thetaCuspHawkingBifurcationThetaValue) := by
  rw [thetaCuspHawkingRayJetOne, iteratedDeriv_one]
  rw [(hasDerivAt_thetaCuspHawkingTiltedTimelikeRay a lambda 0).deriv]
  rw [thetaCuspHawkingTiltedTimelikeRayDerivative, ← iteratedDeriv_one,
    thetaCuspHawkingTiltedSourceJetOne_bifurcation]

lemma thetaCuspHawkingRayJetTwo_bifurcation (a lambda : ℝ) :
    thetaCuspHawkingRayJetTwo a lambda 0 = lambda * (a ^ (2 : ℕ) * thetaCuspHawkingBifurcationThetaValue + thetaCuspHawkingBifurcationThetaSecondJet) := by
  have hray : thetaCuspHawkingTiltedTimelikeRay a lambda =
      id + fun x : ℝ => lambda * thetaCuspTiltedSource a x := by
    funext x
    simp [thetaCuspHawkingTiltedTimelikeRay]
  rw [thetaCuspHawkingRayJetTwo, hray]
  have hgrade : ((2 : ℕ∞) : WithTop ℕ∞) ≤
      ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
  have hid : ContDiffAt ℝ ((2 : ℕ∞) : WithTop ℕ∞) (id : ℝ → ℝ) 0 :=
    contDiff_id.contDiffAt.of_le hgrade
  have hsrc : ContDiffAt ℝ ((2 : ℕ∞) : WithTop ℕ∞) (thetaCuspTiltedSource a) 0 :=
    (contDiff_thetaCuspTiltedSource a).contDiffAt.of_le hgrade
  have hconst : ContDiffAt ℝ ((2 : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ => lambda) 0 :=
    contDiffAt_const
  have hscaled : ContDiffAt ℝ ((2 : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => lambda * thetaCuspTiltedSource a x) 0 :=
    hconst.mul hsrc
  calc
    iteratedDeriv 2 (id + fun x : ℝ => lambda * thetaCuspTiltedSource a x) 0 =
        iteratedDeriv 2 id 0 +
          iteratedDeriv 2 (fun x : ℝ => lambda * thetaCuspTiltedSource a x) 0 :=
      iteratedDeriv_add hid hscaled
    _ = iteratedDeriv 2 id 0 +
        lambda * iteratedDeriv 2 (thetaCuspTiltedSource a) 0 := by
      rw [iteratedDeriv_const_mul lambda hsrc]
    _ = _ := by rw [iteratedDeriv_id, thetaCuspHawkingTiltedSourceJetTwo_bifurcation]; norm_num

lemma thetaCuspHawkingRayJetThree_bifurcation (a lambda : ℝ) :
    thetaCuspHawkingRayJetThree a lambda 0 = lambda * (a ^ (3 : ℕ) * thetaCuspHawkingBifurcationThetaValue + 3 * a * thetaCuspHawkingBifurcationThetaSecondJet) := by
  have hray : thetaCuspHawkingTiltedTimelikeRay a lambda =
      id + fun x : ℝ => lambda * thetaCuspTiltedSource a x := by
    funext x
    simp [thetaCuspHawkingTiltedTimelikeRay]
  rw [thetaCuspHawkingRayJetThree, hray]
  have hgrade : ((3 : ℕ∞) : WithTop ℕ∞) ≤
      ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast (le_top : (3 : ℕ∞) ≤ ⊤)
  have hid : ContDiffAt ℝ ((3 : ℕ∞) : WithTop ℕ∞) (id : ℝ → ℝ) 0 :=
    contDiff_id.contDiffAt.of_le hgrade
  have hsrc : ContDiffAt ℝ ((3 : ℕ∞) : WithTop ℕ∞) (thetaCuspTiltedSource a) 0 :=
    (contDiff_thetaCuspTiltedSource a).contDiffAt.of_le hgrade
  have hconst : ContDiffAt ℝ ((3 : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ => lambda) 0 :=
    contDiffAt_const
  have hscaled : ContDiffAt ℝ ((3 : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => lambda * thetaCuspTiltedSource a x) 0 :=
    hconst.mul hsrc
  calc
    iteratedDeriv 3 (id + fun x : ℝ => lambda * thetaCuspTiltedSource a x) 0 =
        iteratedDeriv 3 id 0 +
          iteratedDeriv 3 (fun x : ℝ => lambda * thetaCuspTiltedSource a x) 0 :=
      iteratedDeriv_add hid hscaled
    _ = iteratedDeriv 3 id 0 +
        lambda * iteratedDeriv 3 (thetaCuspTiltedSource a) 0 := by
      rw [iteratedDeriv_const_mul lambda hsrc]
    _ = _ := by rw [iteratedDeriv_id, thetaCuspHawkingTiltedSourceJetThree_bifurcation]; norm_num

def thetaCuspHawkingBifurcationCurvature (a : ℝ) : ℝ := a ^ (2 : ℕ) * thetaCuspHawkingBifurcationThetaValue + thetaCuspHawkingBifurcationThetaSecondJet
def thetaCuspHawkingBifurcationJerk (a : ℝ) : ℝ := a ^ (3 : ℕ) * thetaCuspHawkingBifurcationThetaValue + 3 * a * thetaCuspHawkingBifurcationThetaSecondJet

lemma thetaCuspHawkingBifurcationJerk_eq (a : ℝ) :
    thetaCuspHawkingBifurcationJerk a = a * (a ^ (2 : ℕ) * thetaCuspHawkingBifurcationThetaValue + 3 * thetaCuspHawkingBifurcationThetaSecondJet) := by
  rw [thetaCuspHawkingBifurcationJerk]
  ring

lemma thetaCuspHawkingSchwarzian_bifurcation (a lambda : ℝ) :
    thetaCuspHawkingSchwarzian a lambda 0 =
      lambda * thetaCuspHawkingBifurcationJerk a / (1 + lambda * (a * thetaCuspHawkingBifurcationThetaValue)) -
        (3 / 2 : ℝ) *
          (lambda * thetaCuspHawkingBifurcationCurvature a / (1 + lambda * (a * thetaCuspHawkingBifurcationThetaValue))) ^ (2 : ℕ) := by
  rw [thetaCuspHawkingSchwarzian, thetaCuspHawkingSchwarzianFromThreeJets,
    thetaCuspHawkingRayJetOne_bifurcation, thetaCuspHawkingRayJetTwo_bifurcation, thetaCuspHawkingRayJetThree_bifurcation]
  simp only [thetaCuspHawkingBifurcationCurvature, thetaCuspHawkingBifurcationJerk]

lemma thetaCuspHawkingBifurcationCurvature_neg (a : ℝ) :
    thetaCuspHawkingBifurcationCurvature (-a) =
      thetaCuspHawkingBifurcationCurvature a := by
  simp [thetaCuspHawkingBifurcationCurvature]

lemma thetaCuspHawkingBifurcationJerk_neg (a : ℝ) :
    thetaCuspHawkingBifurcationJerk (-a) =
      -thetaCuspHawkingBifurcationJerk a := by
  simp [thetaCuspHawkingBifurcationJerk]
  ring

private lemma bifurcation_reflected_schwarzian_algebra
    (X Y q : ℝ) (hp : 1 + q ≠ 0) (hm : 1 - q ≠ 0) :
    (X / (1 + q) - (3 / 2 : ℝ) * (Y / (1 + q)) ^ (2 : ℕ)) -
        (-X / (1 - q) - (3 / 2 : ℝ) * (Y / (1 - q)) ^ (2 : ℕ)) =
      2 * X / (1 - q ^ (2 : ℕ)) + 6 * q * Y ^ (2 : ℕ) / (1 - q ^ (2 : ℕ)) ^ (2 : ℕ) := by
  have hf : 1 - q ^ (2 : ℕ) ≠ 0 := by
    rw [show 1 - q ^ (2 : ℕ) = (1 + q) * (1 - q) by ring]
    exact mul_ne_zero hp hm
  rw [div_pow, div_pow]
  field_simp [hp, hm, hf]
  ring

lemma thetaCuspHawkingSchwarzian_bifurcation_reflectionDifference
    (a lambda : ℝ)
    (hplus : 1 + lambda * (a * thetaCuspHawkingBifurcationThetaValue) ≠ 0)
    (hminus : 1 - lambda * (a * thetaCuspHawkingBifurcationThetaValue) ≠ 0) :
    thetaCuspHawkingSchwarzian a lambda 0 -
        thetaCuspHawkingSchwarzian (-a) lambda 0 =
      2 * lambda * thetaCuspHawkingBifurcationJerk a /
          (1 - (lambda * (a * thetaCuspHawkingBifurcationThetaValue)) ^ (2 : ℕ)) +
        6 * lambda ^ (3 : ℕ) * a * thetaCuspHawkingBifurcationThetaValue * thetaCuspHawkingBifurcationCurvature a ^ (2 : ℕ) /
          (1 - (lambda * (a * thetaCuspHawkingBifurcationThetaValue)) ^ (2 : ℕ)) ^ (2 : ℕ) := by
  rw [thetaCuspHawkingSchwarzian_bifurcation,
    thetaCuspHawkingSchwarzian_bifurcation,
    thetaCuspHawkingBifurcationJerk_neg,
    thetaCuspHawkingBifurcationCurvature_neg]
  have hfactor : 1 - (lambda * (a * thetaCuspHawkingBifurcationThetaValue)) ^ (2 : ℕ) ≠ 0 := by
    calc
      1 - (lambda * (a * thetaCuspHawkingBifurcationThetaValue)) ^ (2 : ℕ) =
          (1 + lambda * (a * thetaCuspHawkingBifurcationThetaValue)) * (1 - lambda * (a * thetaCuspHawkingBifurcationThetaValue)) := by ring
      _ ≠ 0 := mul_ne_zero hplus hminus
  have h := bifurcation_reflected_schwarzian_algebra
    (lambda * thetaCuspHawkingBifurcationJerk a) (lambda * thetaCuspHawkingBifurcationCurvature a)
      (lambda * (a * thetaCuspHawkingBifurcationThetaValue)) hplus hminus
  convert h using 1 <;> ring

def thetaCuspHawkingBifurcationReflectionPolynomial (a lambda : ℝ) : ℝ :=
  thetaCuspHawkingBifurcationJerk a + lambda ^ (2 : ℕ) *
    (-thetaCuspHawkingBifurcationJerk a * a ^ (2 : ℕ) * thetaCuspHawkingBifurcationThetaValue ^ (2 : ℕ) +
      3 * a * thetaCuspHawkingBifurcationThetaValue * thetaCuspHawkingBifurcationCurvature a ^ (2 : ℕ))

lemma thetaCuspHawkingSchwarzian_bifurcation_reflection_eq_iff_polynomial_zero
    (a lambda : ℝ) (hlambda : lambda ≠ 0)
    (hplus : 1 + lambda * (a * thetaCuspHawkingBifurcationThetaValue) ≠ 0)
    (hminus : 1 - lambda * (a * thetaCuspHawkingBifurcationThetaValue) ≠ 0) :
    thetaCuspHawkingSchwarzian a lambda 0 =
        thetaCuspHawkingSchwarzian (-a) lambda 0 ↔
      thetaCuspHawkingBifurcationReflectionPolynomial a lambda = 0 := by
  have hfactor : 1 - (lambda * (a * thetaCuspHawkingBifurcationThetaValue)) ^ (2 : ℕ) ≠ 0 := by
    rw [show 1 - (lambda * (a * thetaCuspHawkingBifurcationThetaValue)) ^ (2 : ℕ) =
      (1 + lambda * (a * thetaCuspHawkingBifurcationThetaValue)) * (1 - lambda * (a * thetaCuspHawkingBifurcationThetaValue)) by ring]
    exact mul_ne_zero hplus hminus
  have hfactor' : 1 - lambda ^ (2 : ℕ) * a ^ (2 : ℕ) * thetaCuspHawkingBifurcationThetaValue ^ (2 : ℕ) ≠ 0 := by
    rw [show 1 - lambda ^ (2 : ℕ) * a ^ (2 : ℕ) * thetaCuspHawkingBifurcationThetaValue ^ (2 : ℕ) =
      1 - (lambda * (a * thetaCuspHawkingBifurcationThetaValue)) ^ (2 : ℕ) by ring]
    exact hfactor
  rw [← sub_eq_zero, thetaCuspHawkingSchwarzian_bifurcation_reflectionDifference a lambda hplus hminus]
  have hcombine :
      2 * lambda * thetaCuspHawkingBifurcationJerk a / (1 - (lambda * (a * thetaCuspHawkingBifurcationThetaValue)) ^ (2 : ℕ)) +
          6 * lambda ^ (3 : ℕ) * a * thetaCuspHawkingBifurcationThetaValue * thetaCuspHawkingBifurcationCurvature a ^ (2 : ℕ) /
            (1 - (lambda * (a * thetaCuspHawkingBifurcationThetaValue)) ^ (2 : ℕ)) ^ (2 : ℕ) =
        lambda *
          (2 * thetaCuspHawkingBifurcationJerk a * (1 - lambda ^ (2 : ℕ) * a ^ (2 : ℕ) * thetaCuspHawkingBifurcationThetaValue ^ (2 : ℕ)) +
            lambda ^ (2 : ℕ) * a * thetaCuspHawkingBifurcationThetaValue * 6 * thetaCuspHawkingBifurcationCurvature a ^ (2 : ℕ)) /
          (1 - lambda ^ (2 : ℕ) * a ^ (2 : ℕ) * thetaCuspHawkingBifurcationThetaValue ^ (2 : ℕ)) ^ (2 : ℕ) := by
    field_simp [hfactor]
  rw [hcombine]
  unfold thetaCuspHawkingBifurcationReflectionPolynomial
  constructor <;> intro h
  · have hnum : lambda *
        (2 * thetaCuspHawkingBifurcationJerk a * (1 - lambda ^ (2 : ℕ) * a ^ (2 : ℕ) * thetaCuspHawkingBifurcationThetaValue ^ (2 : ℕ)) +
          lambda ^ (2 : ℕ) * a * thetaCuspHawkingBifurcationThetaValue * 6 * thetaCuspHawkingBifurcationCurvature a ^ (2 : ℕ)) = 0 := by
      rcases (div_eq_zero_iff).mp h with hnum | hden
      · exact hnum
      · exact ((pow_ne_zero 2 hfactor') hden).elim
    have hbracket := (mul_eq_zero.mp hnum).resolve_left hlambda
    nlinarith
  · apply (div_eq_zero_iff).mpr
    left
    apply mul_eq_zero.mpr
    right
    nlinarith

def thetaCuspHawkingBifurcationCommonCouplingRadius (a : ℝ) : ℝ :=
  min (thetaCuspHawkingTiltedCouplingRadius a)
    (thetaCuspHawkingTiltedCouplingRadius (-a))

lemma thetaCuspHawkingBifurcationCommonCouplingRadius_pos (a : ℝ) :
    0 < thetaCuspHawkingBifurcationCommonCouplingRadius a := by
  rw [thetaCuspHawkingBifurcationCommonCouplingRadius, lt_min_iff]
  exact ⟨thetaCuspHawkingTiltedCouplingRadius_pos a,
    thetaCuspHawkingTiltedCouplingRadius_pos (-a)⟩

def ThetaCuspHawkingBifurcationSchwarzianMirrorNeutral (a : ℝ) : Prop :=
  ∀ lambda : ℝ, |lambda| < thetaCuspHawkingBifurcationCommonCouplingRadius a →
    thetaCuspHawkingSchwarzian a lambda 0 =
      thetaCuspHawkingSchwarzian (-a) lambda 0

theorem thetaCuspHawkingBifurcationSchwarzianMirrorNeutral_iff_zero_tilt {a : ℝ} (ha : |a| < 1) :
    ThetaCuspHawkingBifurcationSchwarzianMirrorNeutral a ↔ a = 0 := by
  constructor
  · intro hneutral
    let r := thetaCuspHawkingBifurcationCommonCouplingRadius a
    have hr : 0 < r := thetaCuspHawkingBifurcationCommonCouplingRadius_pos a
    have hl1 : |r / 3| < r := by
      rw [abs_of_pos (div_pos hr (by norm_num))]
      nlinarith
    have hl2 : |r / 2| < r := by
      rw [abs_of_pos (div_pos hr (by norm_num))]
      nlinarith
    have hsafe_plus (lambda : ℝ) (hlambda : |lambda| < r) :
        |lambda| < thetaCuspHawkingTiltedCouplingRadius a := by
      exact lt_of_lt_of_le hlambda (min_le_left _ _)
    have hsafe_minus (lambda : ℝ) (hlambda : |lambda| < r) :
        |lambda| < thetaCuspHawkingTiltedCouplingRadius (-a) := by
      exact lt_of_lt_of_le hlambda (min_le_right _ _)
    have hden_plus (lambda : ℝ) (hlambda : |lambda| < r) :
        1 + lambda * (a * thetaCuspHawkingBifurcationThetaValue) ≠ 0 := by
      have hpos := thetaCuspHawkingTiltedTimelikeRayDerivative_pos ha
        (hsafe_plus lambda hlambda) 0
      rw [thetaCuspHawkingTiltedTimelikeRayDerivative, ← iteratedDeriv_one,
        thetaCuspHawkingTiltedSourceJetOne_bifurcation] at hpos
      exact hpos.ne'
    have hden_minus (lambda : ℝ) (hlambda : |lambda| < r) :
        1 - lambda * (a * thetaCuspHawkingBifurcationThetaValue) ≠ 0 := by
      have hneg : |(-a : ℝ)| < 1 := by simpa only [abs_neg] using ha
      have hpos := thetaCuspHawkingTiltedTimelikeRayDerivative_pos hneg
        (hsafe_minus lambda hlambda) 0
      rw [thetaCuspHawkingTiltedTimelikeRayDerivative, ← iteratedDeriv_one,
        thetaCuspHawkingTiltedSourceJetOne_bifurcation] at hpos
      rw [show 1 - lambda * (a * thetaCuspHawkingBifurcationThetaValue) =
        1 + lambda * ((-a) * thetaCuspHawkingBifurcationThetaValue) by ring]
      exact hpos.ne'
    have hEq1 := hneutral (r / 3) hl1
    have hEq2 := hneutral (r / 2) hl2
    have hP1 :=
      (thetaCuspHawkingSchwarzian_bifurcation_reflection_eq_iff_polynomial_zero a (r / 3)
        (div_ne_zero hr.ne' (by norm_num))
        (hden_plus (r / 3) hl1) (hden_minus (r / 3) hl1)).mp hEq1
    have hP2 :=
      (thetaCuspHawkingSchwarzian_bifurcation_reflection_eq_iff_polynomial_zero a (r / 2)
        (div_ne_zero hr.ne' (by norm_num))
        (hden_plus (r / 2) hl2) (hden_minus (r / 2) hl2)).mp hEq2
    let K : ℝ :=
      -thetaCuspHawkingBifurcationJerk a * a ^ (2 : ℕ) * thetaCuspHawkingBifurcationThetaValue ^ (2 : ℕ) +
        3 * a * thetaCuspHawkingBifurcationThetaValue * thetaCuspHawkingBifurcationCurvature a ^ (2 : ℕ)
    change thetaCuspHawkingBifurcationJerk a + (r / 3) ^ (2 : ℕ) * K = 0 at hP1
    change thetaCuspHawkingBifurcationJerk a + (r / 2) ^ (2 : ℕ) * K = 0 at hP2
    have hK : K = 0 := by
      nlinarith [sq_pos_of_pos hr]
    have hA : thetaCuspHawkingBifurcationJerk a = 0 := by
      nlinarith [hP1]
    by_contra ha0
    have hAfac : a ^ (2 : ℕ) * thetaCuspHawkingBifurcationThetaValue + 3 * thetaCuspHawkingBifurcationThetaSecondJet = 0 := by
      rw [thetaCuspHawkingBifurcationJerk_eq] at hA
      exact (mul_eq_zero.mp hA).resolve_left ha0
    have hc : thetaCuspHawkingBifurcationThetaValue ≠ 0 := thetaCuspFullSource_pos_zero.ne'
    have hprod : a * thetaCuspHawkingBifurcationThetaValue * thetaCuspHawkingBifurcationCurvature a ^ (2 : ℕ) = 0 := by
      dsimp only [K] at hK
      rw [hA] at hK
      nlinarith
    have hBsq : thetaCuspHawkingBifurcationCurvature a ^ (2 : ℕ) = 0 :=
      (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero ha0 hc)
    have hB : thetaCuspHawkingBifurcationCurvature a = 0 := by
      exact (mul_self_eq_zero.mp (by simpa [pow_two] using hBsq))
    rw [thetaCuspHawkingBifurcationCurvature] at hB
    have hd : thetaCuspHawkingBifurcationThetaSecondJet = 0 := by linarith [hAfac, hB]
    have hac : a ^ (2 : ℕ) * thetaCuspHawkingBifurcationThetaValue = 0 := by linarith [hB]
    exact (mul_ne_zero (pow_ne_zero 2 ha0) hc) hac
  · rintro rfl lambda hlambda
    simp only [neg_zero]

theorem exists_thetaCuspHawkingBifurcationSchwarzian_reflection_ne_of_tilt_ne_zero
    {a : ℝ} (ha : |a| < 1) (ha0 : a ≠ 0) :
    ∃ lambda : ℝ, |lambda| < thetaCuspHawkingBifurcationCommonCouplingRadius a ∧
      thetaCuspHawkingSchwarzian a lambda 0 ≠
        thetaCuspHawkingSchwarzian (-a) lambda 0 := by
  by_contra hnone
  have hneutral : ThetaCuspHawkingBifurcationSchwarzianMirrorNeutral a := by
    intro lambda hlambda
    by_contra hne
    exact hnone ⟨lambda, hlambda, hne⟩
  exact ha0
    ((thetaCuspHawkingBifurcationSchwarzianMirrorNeutral_iff_zero_tilt ha).mp
      hneutral)

theorem exists_thetaCuspHawkingBifurcationConformalFlux_reflection_ne_of_tilt_ne_zero
    {C a : ℝ} (hC : C ≠ 0) (ha : |a| < 1) (ha0 : a ≠ 0) :
    ∃ lambda : ℝ, |lambda| < thetaCuspHawkingBifurcationCommonCouplingRadius a ∧
      thetaCuspHawkingConformalFlux C a lambda 0 ≠
        thetaCuspHawkingConformalFlux C (-a) lambda 0 := by
  rcases exists_thetaCuspHawkingBifurcationSchwarzian_reflection_ne_of_tilt_ne_zero ha ha0 with
    ⟨lambda, hlambda, hne⟩
  refine ⟨lambda, hlambda, ?_⟩
  intro hflux
  apply hne
  unfold thetaCuspHawkingConformalFlux at hflux
  exact mul_left_cancel₀ (neg_ne_zero.mpr hC) hflux

theorem thetaCuspHawkingXiDivisor_bifurcationMirrorNeutral_im_eq_zero
    (q : XiZeroCopy)
    (hneutral : ThetaCuspHawkingBifurcationSchwarzianMirrorNeutral (xiSpectralPoint q).im) :
    (xiSpectralPoint q).im = 0 := by
  have ha : |(xiSpectralPoint q).im| < 1 := by
    linarith [abs_im_xiSpectralPoint_lt_half q]
  exact (thetaCuspHawkingBifurcationSchwarzianMirrorNeutral_iff_zero_tilt ha).mp hneutral

theorem exists_thetaCuspHawkingXiDivisor_bifurcationConformalFlux_reflection_ne_of_im_ne_zero
    {C : ℝ} (hC : C ≠ 0) (q : XiZeroCopy)
    (hq : (xiSpectralPoint q).im ≠ 0) :
    ∃ lambda : ℝ,
      |lambda| < thetaCuspHawkingBifurcationCommonCouplingRadius (xiSpectralPoint q).im ∧
        thetaCuspHawkingConformalFlux C (xiSpectralPoint q).im lambda 0 ≠
          thetaCuspHawkingConformalFlux C (-(xiSpectralPoint q).im) lambda 0 := by
  have ha : |(xiSpectralPoint q).im| < 1 := by
    linarith [abs_im_xiSpectralPoint_lt_half q]
  exact exists_thetaCuspHawkingBifurcationConformalFlux_reflection_ne_of_tilt_ne_zero hC ha hq

end

end RHTower
