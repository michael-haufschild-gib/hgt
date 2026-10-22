import GaloisForLFunctions.HTGeometry.ExactCompletedC5SeamOrientation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFixedActionC5AdaptiveResidualReserve
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionEighthLogJets
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFixedActionC5JacobianSeamOrientation

/-!
# Exact completed C5 seam orientation

This module retains the literal completed third channel that the adaptive-reserve approximation
deleted. The cleared compensation cancels through order eight; its ninth seam jet is `80640 * Ω`.
The new orientation is not an opaque seven-jet sign: if `A = -L₂` and

`K₆ = A*C - B² - 18*A²*B + 24*A⁴`,

then `Ω = A*K₆' - 4*A'*K₆ = A⁵ * (K₆/A⁴)'`. Thus the remaining global direct-J burden is exactly
strict projective monotonicity of the corpus's already-positive sixth reflected Hankel invariant.
At the modular centre the derivative of `Ω` is the previously closed fixed-action seam coefficient,
so `Ω > 0` and the literal direct-J Jacobian are unconditional in a punctured two-scale wedge.

RH chain: projective sixth-curvature monotonicity -> exact completed local direct-J orientation ->
compact/far-tail fixed-action assembly -> reflection-odd rank-four/Ptolemy wall -> cofinal no-escape
-> CLG/TTF or Weil polarization positivity -> RH. Any point with `Ω <= 0` kills this direct-J seam
route at that centre.
-/

open scoped BigOperators ContDiff
open Filter Topology Set

namespace RHTower

noncomputable section

open GaloisForLFunctions

private theorem iteratedDeriv_comp_const_add_real
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    ∀ (n : ℕ) (u t : ℝ),
      iteratedDeriv n (fun x => f (u + x)) t = iteratedDeriv n f (u + t) := by
  intro n
  induction n generalizing f with
  | zero => intro u t; simp [iteratedDeriv_zero]
  | succ n ih =>
      intro u t
      rw [iteratedDeriv_succ', iteratedDeriv_succ']
      have hd : deriv (fun x => f (u + x)) = fun x => deriv f (u + x) := by
        funext x
        have hinner : HasDerivAt (fun x : ℝ => u + x) 1 x := by
          simpa using (hasDerivAt_id x).const_add u
        have hcomp := (hf.differentiable (by simp)).differentiableAt.hasDerivAt.comp x hinner
        simpa [Function.comp_def] using hcomp.deriv
      rw [hd]
      exact ih (f := deriv f) hf.deriv' u t

private theorem iteratedDeriv_comp_const_sub_real
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    ∀ (n : ℕ) (u t : ℝ),
      iteratedDeriv n (fun x => f (u - x)) t =
        (-1 : ℝ) ^ n * iteratedDeriv n f (u - t) := by
  intro n
  induction n generalizing f with
  | zero => intro u t; simp [iteratedDeriv_zero]
  | succ n ih =>
      intro u t
      rw [iteratedDeriv_succ', iteratedDeriv_succ']
      have hd : deriv (fun x => f (u - x)) = fun x => -deriv f (u - x) := by
        funext x
        have hinner : HasDerivAt (fun x : ℝ => u - x) (-1) x := by
          simpa using (hasDerivAt_id x).const_sub u
        have hcomp := (hf.differentiable (by simp)).differentiableAt.hasDerivAt.comp x hinner
        simpa [Function.comp_def] using hcomp.deriv
      rw [hd, show (fun x => -deriv f (u - x)) =
        -(fun x => deriv f (u - x)) by rfl,
        iteratedDeriv_neg, ih (f := deriv f) hf.deriv']
      ring

private theorem iteratedDeriv_sub_smooth
    (f g : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y => f y - g y) x =
      iteratedDeriv n f x - iteratedDeriv n g x := by
  exact iteratedDeriv_sub
    (hf.contDiffAt.of_le (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
    (hg.contDiffAt.of_le (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))

private theorem iteratedDeriv_add_smooth
    (f g : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y => f y + g y) x =
      iteratedDeriv n f x + iteratedDeriv n g x := by
  exact iteratedDeriv_add
    (hf.contDiffAt.of_le (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
    (hg.contDiffAt.of_le (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))

private theorem contDiff_thetaCuspReflectedLogAction_all (u : ℝ) :
    ContDiff ℝ ∞ (thetaCuspReflectedLogAction u) := by
  unfold thetaCuspReflectedLogAction
  have hp : ContDiff ℝ ∞ (fun t : ℝ => thetaCuspLogSource (u + t)) :=
    contDiff_thetaCuspLogSource.comp (contDiff_const.add contDiff_id)
  have hm : ContDiff ℝ ∞ (fun t : ℝ => thetaCuspLogSource (u - t)) :=
    contDiff_thetaCuspLogSource.comp (contDiff_const.sub contDiff_id)
  exact (contDiff_const.sub hp).sub hm

private theorem contDiff_thetaCuspReflectedLogCenterJetOne_all (u : ℝ) :
    ContDiff ℝ ∞ (thetaCuspReflectedLogCenterJetOne u) := by
  unfold thetaCuspReflectedLogCenterJetOne thetaCuspLogDecaySlope
  have h1 := HTGeometry.contDiff_top_iteratedDeriv_real
    thetaCuspLogSource contDiff_thetaCuspLogSource 1
  fun_prop

private theorem iteratedDeriv_succ_thetaCuspReflectedLogAction_zero_general
    (u : ℝ) (n : ℕ) :
    iteratedDeriv (n + 1) (thetaCuspReflectedLogAction u) 0 =
      -iteratedDeriv (n + 1) thetaCuspLogSource u -
        (-1 : ℝ) ^ (n + 1) * iteratedDeriv (n + 1) thetaCuspLogSource u := by
  let fp : ℝ → ℝ := fun t => thetaCuspLogSource (u + t)
  let fm : ℝ → ℝ := fun t => thetaCuspLogSource (u - t)
  let c : ℝ → ℝ := fun _ => 2 * thetaCuspLogSource u
  have hfp : ContDiff ℝ ∞ fp := by
    dsimp only [fp]
    exact contDiff_thetaCuspLogSource.comp (contDiff_const.add contDiff_id)
  have hfm : ContDiff ℝ ∞ fm := by
    dsimp only [fm]
    exact contDiff_thetaCuspLogSource.comp (contDiff_const.sub contDiff_id)
  have hc : ContDiff ℝ ∞ c := contDiff_const
  rw [show thetaCuspReflectedLogAction u = fun t => (c t - fp t) - fm t by
    funext t; rfl]
  rw [iteratedDeriv_sub_smooth (fun t => c t - fp t) fm (hc.sub hfp) hfm,
    iteratedDeriv_sub_smooth c fp hc hfp,
    iteratedDeriv_const]
  rw [iteratedDeriv_comp_const_add_real thetaCuspLogSource
      contDiff_thetaCuspLogSource (n + 1) u 0,
    iteratedDeriv_comp_const_sub_real thetaCuspLogSource
      contDiff_thetaCuspLogSource (n + 1) u 0]
  simp

private theorem iteratedDeriv_succ_thetaCuspReflectedLogCenterJetOne_zero_general
    (u : ℝ) (n : ℕ) :
    iteratedDeriv (n + 1) (thetaCuspReflectedLogCenterJetOne u) 0 =
      -iteratedDeriv (n + 2) thetaCuspLogSource u -
        (-1 : ℝ) ^ (n + 1) * iteratedDeriv (n + 2) thetaCuspLogSource u := by
  let d : ℝ → ℝ := fun x => -iteratedDeriv 1 thetaCuspLogSource x
  let dp : ℝ → ℝ := fun t => d (u + t)
  let dm : ℝ → ℝ := fun t => d (u - t)
  let c : ℝ → ℝ := fun _ => 2 * d u
  have hd : ContDiff ℝ ∞ d := by
    dsimp only [d]
    exact (HTGeometry.contDiff_top_iteratedDeriv_real
      thetaCuspLogSource contDiff_thetaCuspLogSource 1).neg
  have hdp : ContDiff ℝ ∞ dp := by dsimp only [dp]; fun_prop
  have hdm : ContDiff ℝ ∞ dm := by dsimp only [dm]; fun_prop
  have hc : ContDiff ℝ ∞ c := contDiff_const
  rw [show thetaCuspReflectedLogCenterJetOne u = fun t => (dp t + dm t) - c t by
    funext t
    simp only [dp, dm, c, d, thetaCuspReflectedLogCenterJetOne,
      thetaCuspLogDecaySlope]]
  rw [iteratedDeriv_sub_smooth (fun t => dp t + dm t) c (hdp.add hdm) hc,
    iteratedDeriv_add_smooth dp dm hdp hdm, iteratedDeriv_const]
  rw [iteratedDeriv_comp_const_add_real d hd (n + 1) u 0,
    iteratedDeriv_comp_const_sub_real d hd (n + 1) u 0]
  have hdn : iteratedDeriv (n + 1) d u =
      -iteratedDeriv (n + 2) thetaCuspLogSource u := by
    rw [show d = -iteratedDeriv 1 thetaCuspLogSource by funext x; rfl,
      iteratedDeriv_neg]
    rw [show n + 2 = 1 + (n + 1) by omega]
    exact congrArg Neg.neg
      (congrFun (HTGeometry.iteratedDeriv_iteratedDeriv_real
        thetaCuspLogSource 1 (n + 1)) u)
  have hn : n + 1 ≠ 0 := by omega
  rw [if_neg hn]
  simp only [add_zero, sub_zero, sub_zero]
  rw [hdn]
  ring

/-- First possible local exact-completed C5 seam orientation. -/
def thetaCuspC5ExactCompletedSeamOrientation (u : ℝ) : ℝ :=
  let A := -iteratedDeriv 2 thetaCuspLogSource u
  let B := -iteratedDeriv 4 thetaCuspLogSource u
  let C := -iteratedDeriv 6 thetaCuspLogSource u
  let E := -iteratedDeriv 3 thetaCuspLogSource u
  let F := -iteratedDeriv 5 thetaCuspLogSource u
  let G := -iteratedDeriv 7 thetaCuspLogSource u
  A ^ (2 : ℕ) * G - 3 * A * C * E - 2 * A * B * F + 4 * B ^ (2 : ℕ) * E -
    18 * A ^ (3 : ℕ) * F + 36 * A ^ (2 : ℕ) * B * E

/-- Exact arbitrary-centre derivative of the ninth-order completed seam orientation. Its even
part is the already-closed direct fixed-action seam coefficient; remaining terms are odd-jet
transport corrections. -/
def thetaCuspC5ExactCompletedSeamOrientationSlope (u : ℝ) : ℝ :=
  let A := -iteratedDeriv 2 thetaCuspLogSource u
  let B := -iteratedDeriv 4 thetaCuspLogSource u
  let C := -iteratedDeriv 6 thetaCuspLogSource u
  let D := -iteratedDeriv 8 thetaCuspLogSource u
  let E := -iteratedDeriv 3 thetaCuspLogSource u
  let F := -iteratedDeriv 5 thetaCuspLogSource u
  let G := -iteratedDeriv 7 thetaCuspLogSource u
  A ^ (2 : ℕ) * D - 5 * A * B * C + 4 * B ^ (3 : ℕ) - 18 * A ^ (3 : ℕ) * C +
      36 * A ^ (2 : ℕ) * B ^ (2 : ℕ) - A * E * G + 6 * B * E * F -
    2 * A * F ^ (2 : ℕ) - 3 * C * E ^ (2 : ℕ) - 18 * A ^ (2 : ℕ) * E * F +
    72 * A * B * E ^ (2 : ℕ)

/-- Intrinsic order-six reflected Hankel invariant in completed log-source coordinates. -/
def thetaCuspC5ExactSeamSixthInvariant (u : ℝ) : ℝ :=
  let A := -iteratedDeriv 2 thetaCuspLogSource u
  let B := -iteratedDeriv 4 thetaCuspLogSource u
  let C := -iteratedDeriv 6 thetaCuspLogSource u
  A * C - B ^ (2 : ℕ) - 18 * A ^ (2 : ℕ) * B + 24 * A ^ (4 : ℕ)

/-- Projectively normalized sixth invariant whose derivative controls exact C5 seam orientation. -/
def thetaCuspC5ExactSeamNormalizedSixthInvariant (u : ℝ) : ℝ :=
  thetaCuspC5ExactSeamSixthInvariant u /
    (-iteratedDeriv 2 thetaCuspLogSource u) ^ (4 : ℕ)

private theorem hasDerivAt_neg_iteratedDeriv_thetaCuspLogSource
    (n : ℕ) (u : ℝ) :
    HasDerivAt (fun x => -iteratedDeriv n thetaCuspLogSource x)
      (-iteratedDeriv (n + 1) thetaCuspLogSource u) u := by
  convert (hasDerivAt_iteratedDeriv_thetaCuspLogSource n u).neg using 1
  all_goals rfl

/-- The slope polynomial is the literal derivative of ninth-order seam orientation. -/
theorem hasDerivAt_thetaCuspC5ExactCompletedSeamOrientation (u : ℝ) :
    HasDerivAt thetaCuspC5ExactCompletedSeamOrientation
      (thetaCuspC5ExactCompletedSeamOrientationSlope u) u := by
  let A : ℝ → ℝ := fun x => -iteratedDeriv 2 thetaCuspLogSource x
  let B : ℝ → ℝ := fun x => -iteratedDeriv 4 thetaCuspLogSource x
  let C : ℝ → ℝ := fun x => -iteratedDeriv 6 thetaCuspLogSource x
  let E : ℝ → ℝ := fun x => -iteratedDeriv 3 thetaCuspLogSource x
  let F : ℝ → ℝ := fun x => -iteratedDeriv 5 thetaCuspLogSource x
  let G : ℝ → ℝ := fun x => -iteratedDeriv 7 thetaCuspLogSource x
  have hA : HasDerivAt A (E u) u := by
    simpa only [A, E] using hasDerivAt_neg_iteratedDeriv_thetaCuspLogSource 2 u
  have hE : HasDerivAt E (B u) u := by
    simpa only [E, B] using hasDerivAt_neg_iteratedDeriv_thetaCuspLogSource 3 u
  have hB : HasDerivAt B (F u) u := by
    simpa only [B, F] using hasDerivAt_neg_iteratedDeriv_thetaCuspLogSource 4 u
  have hF : HasDerivAt F (C u) u := by
    simpa only [F, C] using hasDerivAt_neg_iteratedDeriv_thetaCuspLogSource 5 u
  have hC : HasDerivAt C (G u) u := by
    simpa only [C, G] using hasDerivAt_neg_iteratedDeriv_thetaCuspLogSource 6 u
  have hG := hasDerivAt_neg_iteratedDeriv_thetaCuspLogSource 7 u
  have h1 := (hA.pow 2).mul hG
  have h2 := ((hA.mul hC).mul hE).const_mul 3
  have h3 := ((hA.mul hB).mul hF).const_mul 2
  have h4 := ((hB.pow 2).mul hE).const_mul 4
  have h5 := ((hA.pow 3).mul hF).const_mul 18
  have h6 := (((hA.pow 2).mul hB).mul hE).const_mul 36
  have h := ((((h1.sub h2).sub h3).add h4).sub h5).add h6
  have heq :
      (((((A ^ (2 : ℕ) * G - fun y => 3 * ((A * C) * E) y) -
          fun y => 2 * ((A * B) * F) y) +
          fun y => 4 * (B ^ (2 : ℕ) * E) y) -
          fun y => 18 * (A ^ (3 : ℕ) * F) y) +
          fun y => 36 * ((A ^ (2 : ℕ) * B) * E) y) =ᶠ[nhds u]
        thetaCuspC5ExactCompletedSeamOrientation := by
    exact Filter.Eventually.of_forall fun x => by
      simp only [thetaCuspC5ExactCompletedSeamOrientation, A, B, C, E, F, G,
        Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
      ring
  have h' := h.congr_of_eventuallyEq heq.symm
  have hd : deriv thetaCuspC5ExactCompletedSeamOrientation u =
      thetaCuspC5ExactCompletedSeamOrientationSlope u := by
    rw [h'.deriv]
    simp only [A, B, C, E, F, G, Pi.mul_apply, Pi.pow_apply]
    unfold thetaCuspC5ExactCompletedSeamOrientationSlope
    norm_num
    ring
  rw [← hd]
  exact h'.differentiableAt.hasDerivAt

/-- At self-dual centre the arbitrary-centre slope is exactly the corpus's closed C5 seam
coefficient: every odd transport correction vanishes. -/
theorem thetaCuspC5ExactCompletedSeamOrientationSlope_zero_eq_fixedActionSeamLogValue :
    thetaCuspC5ExactCompletedSeamOrientationSlope 0 =
      thetaCuspC5FixedActionSeamLogValue := by
  have h3 := iteratedDeriv_thetaCuspLogSource_zero_of_odd
    (show Odd 3 by norm_num)
  have h5 := iteratedDeriv_thetaCuspLogSource_zero_of_odd
    (show Odd 5 by norm_num)
  have h7 := iteratedDeriv_thetaCuspLogSource_zero_of_odd
    (show Odd 7 by norm_num)
  unfold thetaCuspC5ExactCompletedSeamOrientationSlope
    thetaCuspC5FixedActionSeamLogValue
  rw [h3, h5, h7]
  ring

/-- The orientation starts at zero by modular parity. -/
theorem thetaCuspC5ExactCompletedSeamOrientation_zero :
    thetaCuspC5ExactCompletedSeamOrientation 0 = 0 := by
  have h3 := iteratedDeriv_thetaCuspLogSource_zero_of_odd
    (show Odd 3 by norm_num)
  have h5 := iteratedDeriv_thetaCuspLogSource_zero_of_odd
    (show Odd 5 by norm_num)
  have h7 := iteratedDeriv_thetaCuspLogSource_zero_of_odd
    (show Odd 7 by norm_num)
  unfold thetaCuspC5ExactCompletedSeamOrientation
  rw [h3, h5, h7]
  ring

/-- Existing self-dual C5 closure forces the new ninth-order orientation positive immediately to
the right of the modular centre. -/
theorem eventually_right_thetaCuspC5ExactCompletedSeamOrientation_pos :
    ∀ᶠ u in 𝓝[>] (0 : ℝ), 0 < thetaCuspC5ExactCompletedSeamOrientation u := by
  have hslope : ∀ᶠ u in 𝓝[>] (0 : ℝ),
      0 < u⁻¹ * (thetaCuspC5ExactCompletedSeamOrientation u -
        thetaCuspC5ExactCompletedSeamOrientation 0) := by
    have hder := hasDerivAt_thetaCuspC5ExactCompletedSeamOrientation 0
    have hpos : 0 < thetaCuspC5ExactCompletedSeamOrientationSlope 0 := by
      rw [thetaCuspC5ExactCompletedSeamOrientationSlope_zero_eq_fixedActionSeamLogValue]
      exact thetaCuspC5FixedActionSeamLogValue_pos
    simpa [smul_eq_mul] using
      hder.tendsto_slope_zero_right.eventually (eventually_gt_nhds hpos)
  filter_upwards [hslope, self_mem_nhdsWithin] with u hu hu0
  rw [thetaCuspC5ExactCompletedSeamOrientation_zero, sub_zero] at hu
  rcases mul_pos_iff.mp hu with hgood | hbad
  · exact hgood.2
  · exact False.elim ((not_lt_of_ge (inv_nonneg.mpr hu0.le)) hbad.1)

/-- Exact derivative of the intrinsic order-six invariant. -/
theorem hasDerivAt_thetaCuspC5ExactSeamSixthInvariant (u : ℝ) :
    let A := -iteratedDeriv 2 thetaCuspLogSource u
    let B := -iteratedDeriv 4 thetaCuspLogSource u
    let C := -iteratedDeriv 6 thetaCuspLogSource u
    let E := -iteratedDeriv 3 thetaCuspLogSource u
    let F := -iteratedDeriv 5 thetaCuspLogSource u
    let G := -iteratedDeriv 7 thetaCuspLogSource u
    HasDerivAt thetaCuspC5ExactSeamSixthInvariant
      (E * C + A * G - 2 * B * F - 36 * A * E * B -
        18 * A ^ (2 : ℕ) * F + 96 * A ^ (3 : ℕ) * E) u := by
  dsimp only
  let A : ℝ → ℝ := fun x => -iteratedDeriv 2 thetaCuspLogSource x
  let B : ℝ → ℝ := fun x => -iteratedDeriv 4 thetaCuspLogSource x
  let C : ℝ → ℝ := fun x => -iteratedDeriv 6 thetaCuspLogSource x
  have hA : HasDerivAt A (-iteratedDeriv 3 thetaCuspLogSource u) u := by
    simpa only [A] using hasDerivAt_neg_iteratedDeriv_thetaCuspLogSource 2 u
  have hB : HasDerivAt B (-iteratedDeriv 5 thetaCuspLogSource u) u := by
    simpa only [B] using hasDerivAt_neg_iteratedDeriv_thetaCuspLogSource 4 u
  have hC : HasDerivAt C (-iteratedDeriv 7 thetaCuspLogSource u) u := by
    simpa only [C] using hasDerivAt_neg_iteratedDeriv_thetaCuspLogSource 6 u
  have h := (((hA.mul hC).sub (hB.pow 2)).sub
      (((hA.pow 2).mul hB).const_mul 18)).add
    ((hA.pow 4).const_mul 24)
  have heq :
      ((A * C - B ^ (2 : ℕ) - fun y => 18 * (A ^ (2 : ℕ) * B) y) +
          fun y => 24 * (A ^ (4 : ℕ)) y) =ᶠ[nhds u]
        thetaCuspC5ExactSeamSixthInvariant := by
    exact Filter.Eventually.of_forall fun x => by
      simp only [thetaCuspC5ExactSeamSixthInvariant, A, B, C,
        Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
      ring
  have h' := h.congr_of_eventuallyEq heq.symm
  norm_num [A, B, C, Pi.mul_apply, Pi.pow_apply] at h'
  ring_nf at h'
  have hcoef :
      iteratedDeriv 3 thetaCuspLogSource u * iteratedDeriv 6 thetaCuspLogSource u +
              iteratedDeriv 3 thetaCuspLogSource u * iteratedDeriv 2 thetaCuspLogSource u *
                  iteratedDeriv 4 thetaCuspLogSource u * 36 +
            iteratedDeriv 3 thetaCuspLogSource u * iteratedDeriv 2 thetaCuspLogSource u ^ (3 : ℕ) * 96 +
          iteratedDeriv 2 thetaCuspLogSource u * iteratedDeriv 7 thetaCuspLogSource u +
        iteratedDeriv 2 thetaCuspLogSource u ^ (2 : ℕ) * iteratedDeriv 5 thetaCuspLogSource u * 18 -
      iteratedDeriv 4 thetaCuspLogSource u * iteratedDeriv 5 thetaCuspLogSource u * 2 =
      -iteratedDeriv 3 thetaCuspLogSource u * -iteratedDeriv 6 thetaCuspLogSource u +
              -iteratedDeriv 2 thetaCuspLogSource u * -iteratedDeriv 7 thetaCuspLogSource u -
            2 * -iteratedDeriv 4 thetaCuspLogSource u * -iteratedDeriv 5 thetaCuspLogSource u -
          36 * -iteratedDeriv 2 thetaCuspLogSource u * -iteratedDeriv 3 thetaCuspLogSource u *
            -iteratedDeriv 4 thetaCuspLogSource u -
        18 * (-iteratedDeriv 2 thetaCuspLogSource u) ^ (2 : ℕ) *
          -iteratedDeriv 5 thetaCuspLogSource u +
      96 * (-iteratedDeriv 2 thetaCuspLogSource u) ^ (3 : ℕ) *
        -iteratedDeriv 3 thetaCuspLogSource u := by
    ring
  rw [← hcoef]
  exact h'

/-- Ninth-order exact completed seam orientation is the projective derivative numerator of the
already-positive sixth reflected Hankel invariant. -/
theorem thetaCuspC5ExactCompletedSeamOrientation_eq_sixth_projectiveDerivative
    (u : ℝ) :
    thetaCuspC5ExactCompletedSeamOrientation u =
      (-iteratedDeriv 2 thetaCuspLogSource u) *
          deriv thetaCuspC5ExactSeamSixthInvariant u -
        4 * (-iteratedDeriv 3 thetaCuspLogSource u) *
          thetaCuspC5ExactSeamSixthInvariant u := by
  rw [(hasDerivAt_thetaCuspC5ExactSeamSixthInvariant u).deriv]
  unfold thetaCuspC5ExactCompletedSeamOrientation
    thetaCuspC5ExactSeamSixthInvariant
  ring

/-- Exact quotient-rule form: the normalized sixth invariant differentiates to orientation divided
by the fifth power of positive curvature. -/
theorem hasDerivAt_thetaCuspC5ExactSeamNormalizedSixthInvariant (u : ℝ) :
    HasDerivAt thetaCuspC5ExactSeamNormalizedSixthInvariant
      (thetaCuspC5ExactCompletedSeamOrientation u /
        (-iteratedDeriv 2 thetaCuspLogSource u) ^ (5 : ℕ)) u := by
  let A : ℝ → ℝ := fun x => -iteratedDeriv 2 thetaCuspLogSource x
  let a := A u
  let e := -iteratedDeriv 3 thetaCuspLogSource u
  let K := thetaCuspC5ExactSeamSixthInvariant u
  let J :=
    (-iteratedDeriv 3 thetaCuspLogSource u) *
          (-iteratedDeriv 6 thetaCuspLogSource u) +
        (-iteratedDeriv 2 thetaCuspLogSource u) *
          (-iteratedDeriv 7 thetaCuspLogSource u) -
      2 * (-iteratedDeriv 4 thetaCuspLogSource u) *
          (-iteratedDeriv 5 thetaCuspLogSource u) -
      36 * (-iteratedDeriv 2 thetaCuspLogSource u) *
          (-iteratedDeriv 3 thetaCuspLogSource u) *
          (-iteratedDeriv 4 thetaCuspLogSource u) -
      18 * (-iteratedDeriv 2 thetaCuspLogSource u) ^ (2 : ℕ) *
          (-iteratedDeriv 5 thetaCuspLogSource u) +
      96 * (-iteratedDeriv 2 thetaCuspLogSource u) ^ (3 : ℕ) *
          (-iteratedDeriv 3 thetaCuspLogSource u)
  have hA : HasDerivAt A (-iteratedDeriv 3 thetaCuspLogSource u) u := by
    simpa only [A] using hasDerivAt_neg_iteratedDeriv_thetaCuspLogSource 2 u
  have hAne : A u ≠ 0 := by
    dsimp only [A]
    exact ne_of_gt (by
      simpa only [thetaCuspLogCurvature] using thetaCuspLogCurvature_pos u)
  have hK : HasDerivAt thetaCuspC5ExactSeamSixthInvariant J u := by
    simpa only [J] using hasDerivAt_thetaCuspC5ExactSeamSixthInvariant u
  have hden0 := hA.pow 4
  have hquot := hK.div hden0 (pow_ne_zero 4 hAne)
  have heqquot : thetaCuspC5ExactSeamNormalizedSixthInvariant =ᶠ[nhds u]
      thetaCuspC5ExactSeamSixthInvariant / A ^ (4 : ℕ) := by
    exact Filter.Eventually.of_forall fun x => by
      simp only [thetaCuspC5ExactSeamNormalizedSixthInvariant, A,
        Pi.div_apply, Pi.pow_apply]
  have hquot' := hquot.congr_of_eventuallyEq heqquot
  have hcoeff :
      (J * a ^ (4 : ℕ) - K * ((4 : ℝ) * a ^ (4 - 1) * e)) / (a ^ (4 : ℕ)) ^ (2 : ℕ) =
        thetaCuspC5ExactCompletedSeamOrientation u / a ^ (5 : ℕ) := by
    rw [thetaCuspC5ExactCompletedSeamOrientation_eq_sixth_projectiveDerivative,
      hK.deriv]
    change
      (J * a ^ (4 : ℕ) - K * ((4 : ℝ) * a ^ (4 - 1) * e)) / (a ^ (4 : ℕ)) ^ (2 : ℕ) =
        (a * J - 4 * e * K) / a ^ (5 : ℕ)
    have hane : a ≠ 0 := by exact hAne
    field_simp [hane]
    ring
  rw [← show a = -iteratedDeriv 2 thetaCuspLogSource u by rfl, ← hcoeff]
  exact hquot'

/-- Positivity of exact seam orientation is exactly strict increase of normalized sixth curvature. -/
theorem thetaCuspC5ExactCompletedSeamOrientation_pos_iff_normalizedSixth_deriv_pos
    (u : ℝ) :
    0 < thetaCuspC5ExactCompletedSeamOrientation u ↔
      0 < deriv thetaCuspC5ExactSeamNormalizedSixthInvariant u := by
  rw [(hasDerivAt_thetaCuspC5ExactSeamNormalizedSixthInvariant u).deriv]
  have hA : 0 < -iteratedDeriv 2 thetaCuspLogSource u := by
    simpa only [thetaCuspLogCurvature] using thetaCuspLogCurvature_pos u
  exact (div_pos_iff_of_pos_right (pow_pos hA 5)).symm

/-- On the positive half-line the intrinsic sixth invariant is the corpus's native globally
positive reflected sixth curvature. -/
theorem thetaCuspC5ExactSeamSixthInvariant_eq_fullReflectionSixthCurvature
    {u : ℝ} (hu : 0 < u) :
    thetaCuspC5ExactSeamSixthInvariant u =
      thetaCuspFullReflectionSixthCurvature u := by
  have h := thetaCuspLogSource_secondSixthHankel_eq_fullReflectionSixthCurvature hu
  unfold thetaCuspC5ExactSeamSixthInvariant
  nlinarith

/-- Literal division-free exact completed-compensation seam germ. -/
def thetaCuspC5ExactCompletedClearedSeamGerm (u t : ℝ) : ℝ :=
  HTGeometry.c5ExactCompletedClearedExpression
    (thetaCuspReflectedLogAction u)
    (thetaCuspReflectedLogCenterJetOne u) t

theorem thetaCuspC5ExactCompletedClearedSeamGerm_seamJetClassification
    (u : ℝ) :
    (∀ k < 9,
      iteratedDeriv k (thetaCuspC5ExactCompletedClearedSeamGerm u) 0 = 0) ∧
      iteratedDeriv 9 (thetaCuspC5ExactCompletedClearedSeamGerm u) 0 =
        80640 * thetaCuspC5ExactCompletedSeamOrientation u := by
  let A := -iteratedDeriv 2 thetaCuspLogSource u
  let B := -iteratedDeriv 4 thetaCuspLogSource u
  let C := -iteratedDeriv 6 thetaCuspLogSource u
  let E := -iteratedDeriv 3 thetaCuspLogSource u
  let F := -iteratedDeriv 5 thetaCuspLogSource u
  let G := -iteratedDeriv 7 thetaCuspLogSource u
  have hq0 : iteratedDeriv 0 (thetaCuspReflectedLogAction u) 0 = 0 := by
    simp [iteratedDeriv_zero, thetaCuspReflectedLogAction]
    ring
  have hs0 : iteratedDeriv 0 (thetaCuspReflectedLogCenterJetOne u) 0 = 0 := by
    simp [iteratedDeriv_zero, thetaCuspReflectedLogCenterJetOne]
    ring
  have hq1 := iteratedDeriv_succ_thetaCuspReflectedLogAction_zero_general u 0
  have hq2 := iteratedDeriv_succ_thetaCuspReflectedLogAction_zero_general u 1
  have hq3 := iteratedDeriv_succ_thetaCuspReflectedLogAction_zero_general u 2
  have hq4 := iteratedDeriv_succ_thetaCuspReflectedLogAction_zero_general u 3
  have hq5 := iteratedDeriv_succ_thetaCuspReflectedLogAction_zero_general u 4
  have hq6 := iteratedDeriv_succ_thetaCuspReflectedLogAction_zero_general u 5
  have hq7 := iteratedDeriv_succ_thetaCuspReflectedLogAction_zero_general u 6
  have hs1 := iteratedDeriv_succ_thetaCuspReflectedLogCenterJetOne_zero_general u 0
  have hs2 := iteratedDeriv_succ_thetaCuspReflectedLogCenterJetOne_zero_general u 1
  have hs3 := iteratedDeriv_succ_thetaCuspReflectedLogCenterJetOne_zero_general u 2
  have hs4 := iteratedDeriv_succ_thetaCuspReflectedLogCenterJetOne_zero_general u 3
  have hs5 := iteratedDeriv_succ_thetaCuspReflectedLogCenterJetOne_zero_general u 4
  have hs6 := iteratedDeriv_succ_thetaCuspReflectedLogCenterJetOne_zero_general u 5
  have hs7 := iteratedDeriv_succ_thetaCuspReflectedLogCenterJetOne_zero_general u 6
  norm_num [A, B, C, E, F, G] at hq1 hq2 hq3 hq4 hq5 hq6 hq7
  norm_num [A, B, C, E, F, G] at hs1 hs2 hs3 hs4 hs5 hs6 hs7
  have hq1' : iteratedDeriv 1 (thetaCuspReflectedLogAction u) 0 = 0 := by
    simpa only [iteratedDeriv_one] using hq1
  have hq2' : iteratedDeriv 2 (thetaCuspReflectedLogAction u) 0 = 2 * A := by
    rw [hq2]
    dsimp only [A]
    ring
  have hq4' : iteratedDeriv 4 (thetaCuspReflectedLogAction u) 0 = 2 * B := by
    rw [hq4]
    dsimp only [B]
    ring
  have hq6' : iteratedDeriv 6 (thetaCuspReflectedLogAction u) 0 = 2 * C := by
    rw [hq6]
    dsimp only [C]
    ring
  have hs2' : iteratedDeriv 2 (thetaCuspReflectedLogCenterJetOne u) 0 = 2 * E := by
    rw [hs2]
    dsimp only [E]
    ring
  have hs4' : iteratedDeriv 4 (thetaCuspReflectedLogCenterJetOne u) 0 = 2 * F := by
    rw [hs4]
    dsimp only [F]
    ring
  have hs6' : iteratedDeriv 6 (thetaCuspReflectedLogCenterJetOne u) 0 = 2 * G := by
    rw [hs6]
    dsimp only [G]
    ring
  have hs1' : iteratedDeriv 1 (thetaCuspReflectedLogCenterJetOne u) 0 = 0 := by
    simpa only [iteratedDeriv_one] using hs1
  have h := HTGeometry.c5ExactCompletedClearedExpression_seamJetClassification
    (thetaCuspReflectedLogAction u) (thetaCuspReflectedLogCenterJetOne u)
    (contDiff_thetaCuspReflectedLogAction_all u)
    (contDiff_thetaCuspReflectedLogCenterJetOne_all u)
    A B C E F G hq0 hq1' hq2' hq3 hq4' hq5 hq6' hq7
    hs0 hs1' hs2' hs3 hs4' hs5 hs6' hs7
  change
    (∀ k < 9,
      iteratedDeriv k
        (HTGeometry.c5ExactCompletedClearedExpression
          (thetaCuspReflectedLogAction u)
          (thetaCuspReflectedLogCenterJetOne u)) 0 = 0) ∧
      iteratedDeriv 9
        (HTGeometry.c5ExactCompletedClearedExpression
          (thetaCuspReflectedLogAction u)
          (thetaCuspReflectedLogCenterJetOne u)) 0 =
        80640 * thetaCuspC5ExactCompletedSeamOrientation u
  simpa [thetaCuspC5ExactCompletedSeamOrientation, A, B, C, E, F, G] using h

private theorem contDiff_thetaCuspC5ExactCompletedClearedSeamGerm (u : ℝ) :
    ContDiff ℝ ∞ (thetaCuspC5ExactCompletedClearedSeamGerm u) := by
  let q := thetaCuspReflectedLogAction u
  let s := thetaCuspReflectedLogCenterJetOne u
  let H : ℝ → ℝ := fun x =>
    iteratedDeriv 1 q x * (x * iteratedDeriv 1 s x) -
      (iteratedDeriv 1 q x + x * iteratedDeriv 2 q x) * s x
  have hq : ContDiff ℝ ∞ q := by
    simpa only [q] using contDiff_thetaCuspReflectedLogAction_all u
  have hs : ContDiff ℝ ∞ s := by
    simpa only [s] using contDiff_thetaCuspReflectedLogCenterJetOne_all u
  have hq1 := HTGeometry.contDiff_top_iteratedDeriv_real q hq 1
  have hq2 := HTGeometry.contDiff_top_iteratedDeriv_real q hq 2
  have hs1 := HTGeometry.contDiff_top_iteratedDeriv_real s hs 1
  have hH : ContDiff ℝ ∞ H := by
    dsimp only [H]
    fun_prop
  have hH1 := HTGeometry.contDiff_top_iteratedDeriv_real H hH 1
  change ContDiff ℝ ∞ (HTGeometry.c5ExactCompletedClearedExpression q s)
  unfold HTGeometry.c5ExactCompletedClearedExpression
  dsimp only [H]
  fun_prop

private def c5ExactCompletedIteratedTaylorShift
    (f : ℝ → ℝ) (j : ℕ) (r x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (j + 1),
    iteratedDeriv k f x * r ^ k / (k.factorial : ℝ)

private theorem taylorWithinEval_add_eq_c5ExactCompletedIteratedTaylorShift
    {f : ℝ → ℝ} {x r : ℝ}
    (hf : ContDiffAt ℝ 9 f x) (hr : 0 < r) (j : ℕ) (hj : j ≤ 8) :
    taylorWithinEval f j (uIcc x (x + r)) x (x + r) =
      c5ExactCompletedIteratedTaylorShift f j r x := by
  have hle : x ≤ x + r := by linarith
  rw [uIcc_of_le hle]
  induction j with
  | zero =>
      simp [c5ExactCompletedIteratedTaylorShift, iteratedDeriv_zero]
  | succ j ih =>
      rw [taylorWithinEval_succ, ih (by omega)]
      simp only [c5ExactCompletedIteratedTaylorShift, Finset.sum_range_succ]
      have hderiv : iteratedDerivWithin (j + 1) f (Icc x (x + r)) x =
          iteratedDeriv (j + 1) f x := by
        have hj9 : ((j + 1 : ℕ) : WithTop ℕ∞) ≤ (9 : WithTop ℕ∞) := by
          exact_mod_cast (show j + 1 ≤ 9 by omega)
        have hf' : ContDiffAt ℝ (j + 1) f x := hf.of_le hj9
        exact iteratedDerivWithin_eq_iteratedDeriv
          (uniqueDiffOn_Icc (by linarith)) hf' (left_mem_Icc.mpr hle)
      rw [hderiv, Nat.factorial_succ]
      push_cast
      ring

private theorem thetaCuspC5ExactCompletedClearedSeamGerm_taylor_eight_zero
    {u t : ℝ} (ht : 0 < t) :
    taylorWithinEval (thetaCuspC5ExactCompletedClearedSeamGerm u) 8
      (uIcc 0 t) 0 t = 0 := by
  have hTaylor :=
    taylorWithinEval_add_eq_c5ExactCompletedIteratedTaylorShift
      (f := thetaCuspC5ExactCompletedClearedSeamGerm u)
      (x := 0) (r := t)
      ((contDiff_thetaCuspC5ExactCompletedClearedSeamGerm u).contDiffAt.of_le
        (by exact WithTop.coe_le_coe.mpr (le_top : (9 : ℕ∞) ≤ ⊤)))
      ht 8 (by norm_num)
  simpa only [zero_add] using hTaylor.trans (by
    unfold c5ExactCompletedIteratedTaylorShift
    apply Finset.sum_eq_zero
    intro k hk
    rw [(thetaCuspC5ExactCompletedClearedSeamGerm_seamJetClassification u).1
      k (Finset.mem_range.mp hk)]
    simp)

/-- Positive ninth orientation produces a punctured local chamber of positive cleared literal
completed compensation at the chosen centre. -/
theorem eventually_thetaCuspC5ExactCompletedClearedSeamGerm_pos_of_orientation
    {u : ℝ} (hu : 0 < u)
    (hΩ : 0 < thetaCuspC5ExactCompletedSeamOrientation u) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ u ∧ ∀ t : ℝ, 0 < t → t < δ →
      0 < thetaCuspC5ExactCompletedClearedSeamGerm u t := by
  let f := thetaCuspC5ExactCompletedClearedSeamGerm u
  have hf : ContDiff ℝ ∞ f := by
    simpa only [f] using contDiff_thetaCuspC5ExactCompletedClearedSeamGerm u
  have hf9 : ContinuousAt (iteratedDeriv 9 f) 0 :=
    (HTGeometry.contDiff_top_iteratedDeriv_real f hf 9).continuous.continuousAt
  have hpos0 : 0 < iteratedDeriv 9 f 0 := by
    have hjet := (thetaCuspC5ExactCompletedClearedSeamGerm_seamJetClassification u).2
    dsimp only [f]
    rw [hjet]
    exact mul_pos (by norm_num) hΩ
  have hevent : {x : ℝ | 0 < iteratedDeriv 9 f x} ∈ nhds 0 :=
    hf9.eventually (Ioi_mem_nhds hpos0)
  rcases Metric.mem_nhds_iff.mp hevent with ⟨ε, hε, hball⟩
  let δ := min ε u
  have hδ : 0 < δ := lt_min hε hu
  have hδu : δ ≤ u := min_le_right _ _
  refine ⟨δ, hδ, hδu, ?_⟩
  intro t ht htδ
  have hf9all : ContDiff ℝ 9 f :=
    hf.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (9 : ℕ∞) ≤ ⊤))
  have hfOn : ContDiffOn ℝ 9 f (uIcc 0 t) := hf9all.contDiffOn
  have hTaylor : taylorWithinEval f 8 (uIcc 0 t) 0 t = 0 := by
    simpa only [f] using
      thetaCuspC5ExactCompletedClearedSeamGerm_taylor_eight_zero (u := u) ht
  obtain ⟨x, hx, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := f) (x := t) (x₀ := 0) (n := 8) (ne_of_lt ht) hfOn
  rw [uIoo_of_le ht.le] at hx
  have hxball : x ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx.1]
    exact hx.2.trans (htδ.trans_le (min_le_left _ _))
  have hxpos : 0 < iteratedDeriv 9 f x := hball hxball
  rw [hTaylor, sub_zero, sub_zero] at hrem
  change 0 < f t
  rw [hrem]
  exact div_pos (mul_pos hxpos (pow_pos ht 9)) (by positivity)

private theorem iteratedDeriv_one_thetaCuspReflectedLogAction_exact
    (u t : ℝ) :
    iteratedDeriv 1 (thetaCuspReflectedLogAction u) t =
      thetaCuspReflectedLogJetOne u t := by
  rw [iteratedDeriv_one]
  exact (hasDerivAt_thetaCuspReflectedLogAction u t).deriv

private theorem iteratedDeriv_two_thetaCuspReflectedLogAction_exact
    (u t : ℝ) :
    iteratedDeriv 2 (thetaCuspReflectedLogAction u) t =
      thetaCuspReflectedLogJetTwo u t := by
  rw [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ]
  have hfun : iteratedDeriv 1 (thetaCuspReflectedLogAction u) =
      thetaCuspReflectedLogJetOne u := by
    funext x
    exact iteratedDeriv_one_thetaCuspReflectedLogAction_exact u x
  rw [hfun]
  exact (hasDerivAt_thetaCuspReflectedLogJetOne u t).deriv

private theorem hasDerivAt_thetaCuspReflectedLogCenterJetOne_displacement_exact
    (u t : ℝ) :
    HasDerivAt (thetaCuspReflectedLogCenterJetOne u)
      (thetaCuspReflectedLogCenterMixedJetOne u t) t := by
  have hp := (hasDerivAt_thetaCuspLogDecaySlope (u + t)).comp t
    ((hasDerivAt_id t).const_add u)
  have hm := (hasDerivAt_thetaCuspLogDecaySlope (u - t)).comp t
    ((hasDerivAt_id t).const_sub u)
  convert (hp.add hm).sub_const (2 * thetaCuspLogDecaySlope u) using 1
  all_goals first | rfl | (simp [thetaCuspReflectedLogCenterMixedJetOne]; ring)

private theorem hasDerivAt_thetaCuspReflectedLogCenterMixedJetOne_displacement_exact
    (u t : ℝ) :
    HasDerivAt (thetaCuspReflectedLogCenterMixedJetOne u)
      (thetaCuspReflectedLogCenterMixedJetThree u t) t := by
  have hp := (hasDerivAt_thetaCuspLogCurvature (u + t)).comp t
    ((hasDerivAt_id t).const_add u)
  have hm := (hasDerivAt_thetaCuspLogCurvature (u - t)).comp t
    ((hasDerivAt_id t).const_sub u)
  convert hp.sub hm using 1
  all_goals first | rfl | simp [thetaCuspReflectedLogCenterMixedJetThree]

private theorem iteratedDeriv_one_thetaCuspReflectedLogCenterJetOne_exact
    (u t : ℝ) :
    iteratedDeriv 1 (thetaCuspReflectedLogCenterJetOne u) t =
      thetaCuspReflectedLogCenterMixedJetOne u t := by
  rw [iteratedDeriv_one]
  exact (hasDerivAt_thetaCuspReflectedLogCenterJetOne_displacement_exact u t).deriv

private theorem hasDerivAt_thetaCuspExactCompletedVelocityCenter
    (u t : ℝ) :
    HasDerivAt
      (fun x =>
        thetaCuspReflectedLogJetOne u x *
            (x * thetaCuspReflectedLogCenterMixedJetOne u x) -
          (thetaCuspReflectedLogJetOne u x +
              x * thetaCuspReflectedLogJetTwo u x) *
            thetaCuspReflectedLogCenterJetOne u x)
      (thetaCuspReflectedLogJetOne u t *
          (t * thetaCuspReflectedLogCenterMixedJetThree u t) -
        (2 * thetaCuspReflectedLogJetTwo u t +
            t * thetaCuspReflectedLogJetThree u t) *
          thetaCuspReflectedLogCenterJetOne u t) t := by
  have ha := hasDerivAt_thetaCuspReflectedLogJetOne u t
  have hb := hasDerivAt_thetaCuspReflectedLogJetTwo u t
  have hs := hasDerivAt_thetaCuspReflectedLogCenterJetOne_displacement_exact u t
  have hm := hasDerivAt_thetaCuspReflectedLogCenterMixedJetOne_displacement_exact u t
  convert (ha.mul ((hasDerivAt_id t).mul hm)).sub
    ((ha.add ((hasDerivAt_id t).mul hb)).mul hs) using 1
  all_goals first
    | rfl
    | (simp only [id_eq, Pi.mul_apply, Pi.add_apply]; ring)

/-- The universal cleared germ is exactly positive-radius clearing of the literal completed
compensation margin. Thus its local sign is the direct-J sign in the same-half-line chamber. -/
theorem thetaCuspC5ExactCompletedClearedSeamGerm_eq_radius_mul_margin
    {u t : ℝ} (ht : 0 < t) (htu : t < u) :
    thetaCuspC5ExactCompletedClearedSeamGerm u t =
      (Real.exp (thetaCuspReflectedLogAction u t) - 1) *
        c5CompletedCompensationMargin u t := by
  have hq1 : iteratedDeriv 1 (thetaCuspReflectedLogAction u) =
      thetaCuspReflectedLogJetOne u := by
    funext x
    exact iteratedDeriv_one_thetaCuspReflectedLogAction_exact u x
  have hq2 : iteratedDeriv 2 (thetaCuspReflectedLogAction u) =
      thetaCuspReflectedLogJetTwo u := by
    funext x
    exact iteratedDeriv_two_thetaCuspReflectedLogAction_exact u x
  have hs1 : iteratedDeriv 1 (thetaCuspReflectedLogCenterJetOne u) =
      thetaCuspReflectedLogCenterMixedJetOne u := by
    funext x
    exact iteratedDeriv_one_thetaCuspReflectedLogCenterJetOne_exact u x
  let H : ℝ → ℝ := fun x =>
    thetaCuspReflectedLogJetOne u x *
        (x * thetaCuspReflectedLogCenterMixedJetOne u x) -
      (thetaCuspReflectedLogJetOne u x +
          x * thetaCuspReflectedLogJetTwo u x) *
        thetaCuspReflectedLogCenterJetOne u x
  have hH : iteratedDeriv 1 H t =
      thetaCuspReflectedLogJetOne u t *
          (t * thetaCuspReflectedLogCenterMixedJetThree u t) -
        (2 * thetaCuspReflectedLogJetTwo u t +
            t * thetaCuspReflectedLogJetThree u t) *
          thetaCuspReflectedLogCenterJetOne u t := by
    rw [iteratedDeriv_one]
    exact (hasDerivAt_thetaCuspExactCompletedVelocityCenter u t).deriv
  have hr : Real.exp (thetaCuspReflectedLogAction u t) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact ne_of_gt (by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (thetaCuspReflectedLogAction_pos (u := u) ht))
  rw [c5CompletedCompensationMargin_eq_intrinsic ht htu]
  unfold thetaCuspC5ExactCompletedClearedSeamGerm
    HTGeometry.c5ExactCompletedClearedExpression
  rw [hq1, hq2, hs1]
  change
    (Real.exp (thetaCuspReflectedLogAction u t) - 1) *
        (5 * (H t + t * iteratedDeriv 1 H t) -
          (14 + 10 * (t * thetaCuspReflectedLogJetOne u t)) * H t) -
      8 * (t * thetaCuspReflectedLogJetOne u t) * H t = _
  rw [hH]
  unfold H thetaCuspReflectedActionVelocity
    thetaCuspReflectedActionVelocityFixedActionCenterNumerator
    thetaCuspReflectedActionVelocitySlopeCurrentFixedActionCenterNumerator
  field_simp [hr]
  ring

/-- Exact orientation positivity transfers to the literal completed compensation margin near the
chosen positive centre. -/
theorem eventually_c5CompletedCompensationMargin_pos_of_exactSeamOrientation
    {u : ℝ} (hu : 0 < u)
    (hΩ : 0 < thetaCuspC5ExactCompletedSeamOrientation u) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ u ∧ ∀ t : ℝ, 0 < t → t < δ →
      0 < c5CompletedCompensationMargin u t := by
  rcases eventually_thetaCuspC5ExactCompletedClearedSeamGerm_pos_of_orientation
    hu hΩ with ⟨δ, hδ, hδu, hlocal⟩
  refine ⟨δ, hδ, hδu, ?_⟩
  intro t ht htδ
  have htu : t < u := lt_of_lt_of_le htδ hδu
  have hG := hlocal t ht htδ
  rw [thetaCuspC5ExactCompletedClearedSeamGerm_eq_radius_mul_margin ht htu] at hG
  have hrpos : 0 < Real.exp (thetaCuspReflectedLogAction u t) - 1 := by
    rw [sub_pos, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (thetaCuspReflectedLogAction_pos (u := u) ht)
  rcases mul_pos_iff.mp hG with hgood | hbad
  · exact hgood.2
  · exact False.elim ((not_lt_of_ge hrpos.le) hbad.1)

/-- Exact orientation positivity is a genuine punctured direct-J chamber at the chosen centre. -/
theorem eventually_thetaCuspReflectedActionC5FixedActionJacobian_pos_of_exactSeamOrientation
    {u : ℝ} (hu : 0 < u)
    (hΩ : 0 < thetaCuspC5ExactCompletedSeamOrientation u) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ u ∧ ∀ t : ℝ, 0 < t → t < δ →
      0 < thetaCuspReflectedActionC5FixedActionJacobian u t := by
  rcases eventually_c5CompletedCompensationMargin_pos_of_exactSeamOrientation
    hu hΩ with ⟨δ, hδ, hδu, hlocal⟩
  refine ⟨δ, hδ, hδu, ?_⟩
  intro t ht htδ
  have htu : t < u := lt_of_lt_of_le htδ hδu
  rw [thetaCuspReflectedActionC5FixedActionJacobian_pos_iff_completedCompensation
    ht htu]
  exact hlocal t ht htδ

/-- Unconditional two-scale wedge: sufficiently small positive centres each admit a punctured
positive direct fixed-action C5 Jacobian chamber. -/
theorem eventually_right_exists_local_thetaCuspReflectedActionC5FixedActionJacobian_pos :
    ∀ᶠ u in 𝓝[>] (0 : ℝ),
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ u ∧ ∀ t : ℝ, 0 < t → t < δ →
        0 < thetaCuspReflectedActionC5FixedActionJacobian u t := by
  filter_upwards
    [eventually_right_thetaCuspC5ExactCompletedSeamOrientation_pos,
      self_mem_nhdsWithin] with u hΩ hu
  exact eventually_thetaCuspReflectedActionC5FixedActionJacobian_pos_of_exactSeamOrientation
    hu hΩ

end

end RHTower
