import GaloisForLFunctions.ThetaCuspSections.RelativeEntropyOfXiTilts
import GaloisForLFunctions.RHTower.XiMagnetizationGHSConcavity
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Direction of relative entropy for real Xi tilts

Concavity of the real Xi logarithmic derivative makes susceptibility
nonincreasing on the positive ray. Analytic continuation and the strict
curvature near the origin exclude every plateau. Reflection then orders
the two directed relative entropies by the absolute sizes of the tilts,
even when the parameters lie on opposite sides of the origin.
-/

open Set Filter Topology RHTower InformationTheory
open scoped NNReal

namespace ThetaCuspSections

noncomputable section

private theorem moment_analytic (j : ℕ) (a : ℝ) :
    AnalyticAt ℝ (fun t : ℝ => thetaTiltMoment t j) a := by
  have hc : Differentiable ℂ (thetaSourceLaplaceMoment thetaCuspTiltSource j) :=
    fun w => (hasDerivAt_thetaSourceLaplaceMoment _ _ w).differentiableAt
  simpa only [thetaSourceLaplaceMoment_cusp_ofReal, Complex.ofReal_re] using
    (hc.analyticAt (a : ℂ)).re_ofReal

private theorem mean_analytic (a : ℝ) : AnalyticAt ℝ xiRealLogDeriv a := by
  rw [← funext thetaTiltMean_eq_xiRealLogDeriv]
  exact (moment_analytic 1 a).div (moment_analytic 0 a) (thetaTiltMoment_zero_pos_global a).ne'

private theorem susceptibility (a : ℝ) : deriv xiRealLogDeriv a = thetaTiltVariance a := by
  rw [← funext thetaTiltMean_eq_xiRealLogDeriv]
  exact (hasDerivAt_thetaTiltMean_global a).deriv

/-- Susceptibility decreases strictly on the entire positive ray. An interval of
equality would continue analytically to a constant function on the real line. -/
theorem susceptibility_strictAntiOn : StrictAntiOn (deriv xiRealLogDeriv) (Ici 0) := by
  have hanti := concaveOn_xiRealLogDeriv.antitoneOn_deriv
    (fun x _ => (hasDerivAt_xiRealLogDeriv x).differentiableAt)
  intro a ha b hb hab
  refine lt_of_le_of_ne (hanti ha hb hab.le) ?_
  intro he
  have hlocal : deriv xiRealLogDeriv =ᶠ[𝓝 ((a+b)/2)] fun _ => deriv xiRealLogDeriv a := by
    filter_upwards [Ioo_mem_nhds (by linarith : a < (a+b)/2) (by linarith : (a+b)/2 < b)]
      with x hx
    have hx' : x ∈ Ici (0 : ℝ) := le_trans ha hx.1.le
    exact (hanti ha hx' hx.1.le).antisymm (he.symm.le.trans (hanti hx' hb hx.2.le))
  have hg : deriv xiRealLogDeriv = fun _ => deriv xiRealLogDeriv a :=
    AnalyticOnNhd.eq_of_eventuallyEq (fun x _ => (mean_analytic x).deriv)
      (fun _ _ => analyticAt_const) hlocal
  have h := deriv2_xiRealLogDeriv_neg (w := 1) (by norm_num) (by norm_num)
  rw [hg, deriv_const] at h
  exact lt_irrefl _ h

/-- Global strict GHS concavity for the actual real Xi magnetization. -/
theorem strictConcaveOn_xiRealLogDeriv : StrictConcaveOn ℝ (Ici 0) xiRealLogDeriv :=
  StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici _)
    (fun x _ => (hasDerivAt_xiRealLogDeriv x).continuousAt.continuousWithinAt)
    (susceptibility_strictAntiOn.mono interior_subset)

/-- A single variance reading determines the absolute tilt, with strict ordering. -/
theorem thetaTiltVariance_lt_iff (a b : ℝ) : thetaTiltVariance a < thetaTiltVariance b ↔ |b| < |a| := by
  have hneg (x : ℝ) : thetaTiltVariance (-x) = thetaTiltVariance x := by
    simp only [thetaTiltVariance, thetaTiltMoment_neg x 2, thetaTiltMoment_zero_neg, thetaTiltMean_neg]
    ring
  have habs (x : ℝ) : thetaTiltVariance |x| = thetaTiltVariance x := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, hneg]
  rw [← habs a, ← habs b, ← susceptibility, ← susceptibility]
  exact susceptibility_strictAntiOn.lt_iff_gt (abs_nonneg _) (abs_nonneg _)

/-- Antisymmetric information cost for two packets equally spaced about a fixed tilt. -/
private def direction (m h : ℝ) := tiltGap (m-h) (m+h) - tiltGap (m+h) (m-h)

private theorem direction_deriv (m h : ℝ) :
    HasDerivAt (direction m) (2*h*(thetaTiltVariance (m-h) - thetaTiltVariance (m+h))) h := by
  have hp : HasDerivAt (fun t : ℝ => m+t) 1 h := by simpa using (hasDerivAt_id h).const_add m
  have hn : HasDerivAt (fun t : ℝ => m-t) (-1) h := (hasDerivAt_id h).const_sub m
  have hpart (x : ℝ) : HasDerivAt thetaTiltLogPartition (thetaTiltMean x) x :=
    (hasDerivAt_thetaTiltMoment_global x 0).log (thetaTiltMoment_zero_pos_global x).ne'
  have H := ((((hpart _).comp h hp).sub ((hpart _).comp h hn)).const_mul 2).sub
    (((hasDerivAt_id h).const_mul 2).mul
      (((hasDerivAt_thetaTiltMean_global _).comp h hp).add ((hasDerivAt_thetaTiltMean_global _).comp h hn)))
  convert H using 1
  · funext t
    dsimp [direction, tiltGap]
    ring
  · dsimp
    ring

private theorem direction_pos {m h : ℝ} (hm : 0 < m) (hh : 0 < h) : 0 < direction m h := by
  have hs : StrictMonoOn (direction m) (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
      (fun t _ => (direction_deriv m t).continuousAt.continuousWithinAt)
    intro t ht
    rw [interior_Ici] at ht
    rw [(direction_deriv m t).deriv]
    apply mul_pos (mul_pos two_pos ht)
    apply sub_pos.mpr ((thetaTiltVariance_lt_iff _ _).mpr ?_)
    rw [abs_of_pos (add_pos hm ht), abs_lt]
    constructor <;> linarith
  have hz : direction m 0 = 0 := by simp [direction]
  exact hz ▸ hs (le_refl _) hh.le hh

private theorem gap_reflect (a b : ℝ) : tiltGap (-a) (-b) = tiltGap a b := by
  simp only [tiltGap, thetaTiltLogPartition_neg, thetaTiltMean_neg]
  ring

private theorem gap_order {a b : ℝ} (hab : |a| < |b|) : tiltGap b a < tiltGap a b := by
  have hp {x y : ℝ} (hxy : x < y) (hm : 0 < x+y) : tiltGap y x < tiltGap x y := by
    have H := direction_pos (m := (x+y)/2) (h := (y-x)/2) (by linarith) (by linarith)
    simpa only [direction, show (x+y)/2-(y-x)/2 = x by ring,
      show (x+y)/2+(y-x)/2 = y by ring, sub_pos] using H
  rcases le_or_gt 0 b with hb | hb
  · rw [abs_of_nonneg hb, abs_lt] at hab
    exact hp hab.2 (by linarith [hab.1])
  · rw [abs_of_neg hb, abs_lt] at hab
    rw [← gap_reflect b a, ← gap_reflect a b]
    exact hp (by linarith [hab.1]) (by linarith [hab.2])

/-- Directed KL is larger exactly when the target has the larger absolute displacement. -/
theorem thetaTilts_klDiv_lt_reverse_iff (a b : ℝ) :
    klDiv (thetaTiltProb a) (thetaTiltProb b) < klDiv (thetaTiltProb b) (thetaTiltProb a) ↔
      |b| < |a| := by
  rw [thetaTilts_klDiv, thetaTilts_klDiv, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (tiltGap_nonneg a b)]
  refine ⟨fun h => ?_, gap_order⟩
  rcases lt_trichotomy |a| |b| with hab | hab | hab
  · exact ((gap_order hab).not_gt h).elim
  · rcases abs_eq_abs.mp hab with e | e
    · subst b
      exact (lt_irrefl _ h).elim
    · subst a
      have he := gap_reflect b (-b)
      rw [neg_neg] at he
      exact (h.ne he).elim
  · exact hab

/-- Square root of the sum of the two directed relative entropies. -/
def thetaJeffreysLength (a b : ℝ) : ℝ :=
  Real.sqrt ((klDiv (thetaTiltProb a) (thetaTiltProb b)).toReal +
    (klDiv (thetaTiltProb b) (thetaTiltProb a)).toReal)

private theorem length_eq (a b : ℝ) :
    thetaJeffreysLength a b = Real.sqrt ((b-a)*(xiRealLogDeriv b-xiRealLogDeriv a)) := by
  rw [thetaJeffreysLength, thetaTilts_klDiv, thetaTilts_klDiv,
    ENNReal.toReal_ofReal (tiltGap_nonneg _ _), ENNReal.toReal_ofReal (tiltGap_nonneg _ _),
    tiltGap_symmetrized]

private theorem segment_defect {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    thetaJeffreysLength a c ^ 2 - (thetaJeffreysLength a b + thetaJeffreysLength b c)^2 =
      (Real.sqrt ((b-a)*(xiRealLogDeriv c-xiRealLogDeriv b)) -
        Real.sqrt ((c-b)*(xiRealLogDeriv b-xiRealLogDeriv a)))^2 := by
  let A := b-a
  let B := c-b
  let U := xiRealLogDeriv b - xiRealLogDeriv a
  let V := xiRealLogDeriv c - xiRealLogDeriv b
  have hA : 0 ≤ A := sub_nonneg.mpr hab
  have hB : 0 ≤ B := sub_nonneg.mpr hbc
  have hU : 0 ≤ U := sub_nonneg.mpr (strictMono_xiRealLogDeriv.monotone hab)
  have hV : 0 ≤ V := sub_nonneg.mpr (strictMono_xiRealLogDeriv.monotone hbc)
  simp only [length_eq, show c-a = A+B by dsimp [A,B]; ring,
    show xiRealLogDeriv c-xiRealLogDeriv a = U+V by dsimp [U,V]; ring]
  change Real.sqrt ((A+B)*(U+V))^2 - (Real.sqrt (A*U)+Real.sqrt (B*V))^2 =
    (Real.sqrt (A*V)-Real.sqrt (B*U))^2
  rw [Real.sq_sqrt (mul_nonneg (add_nonneg hA hB) (add_nonneg hU hV))]
  simp only [Real.sqrt_mul hA, Real.sqrt_mul hB]
  calc
    _ = (Real.sqrt A^2 + Real.sqrt B^2)*(Real.sqrt U^2 + Real.sqrt V^2) -
        (Real.sqrt A*Real.sqrt U + Real.sqrt B*Real.sqrt V)^2 := by
          rw [Real.sq_sqrt hA, Real.sq_sqrt hB, Real.sq_sqrt hU, Real.sq_sqrt hV]
    _ = _ := by ring

/-- Along an ordered chain the square root of Jeffreys divergence satisfies the
reverse triangle inequality. The squared defect is an explicit nonnegative square. -/
theorem thetaJeffreys_reverse_triangle (a : ℝ) (u v : ℝ≥0) :
    thetaJeffreysLength a (a+u) + thetaJeffreysLength (a+u) (a+u+v) ≤
      thetaJeffreysLength a (a+u+v) := by
  have he := segment_defect (a := a) (b := a+u) (c := a+u+v)
    (le_add_of_nonneg_right u.2) (le_add_of_nonneg_right v.2)
  have hp : 0 ≤ thetaJeffreysLength a (a+u+v) := Real.sqrt_nonneg _
  nlinarith only [he, hp, sq_nonneg (Real.sqrt (((a+u)-a) *
    (xiRealLogDeriv (a+u+v)-xiRealLogDeriv (a+u))) -
    Real.sqrt (((a+u+v)-(a+u))*(xiRealLogDeriv (a+u)-xiRealLogDeriv a)))]

/-- Every strictly ordered triple on the positive ray violates the usual metric triangle
inequality. Strict GHS concavity rules out equality of the adjacent secant slopes. -/
theorem thetaJeffreys_strict_reverse_triangle (a : ℝ≥0) (u v : {x : ℝ // 0 < x}) :
    thetaJeffreysLength a (a+u.val) + thetaJeffreysLength (a+u.val) (a+u.val+v.val) <
      thetaJeffreysLength a (a+u.val+v.val) := by
  let b : ℝ := a+u.val
  let c : ℝ := b+v.val
  have hab : (a : ℝ) < b := lt_add_of_pos_right _ u.property
  have hbc : b < c := lt_add_of_pos_right _ v.property
  have hc : c ∈ Ici (0 : ℝ) := a.2.trans (hab.trans hbc).le
  have H := strictConcaveOn_xiRealLogDeriv.slope_anti_adjacent a.2 hc hab hbc
  rw [div_lt_div_iff₀ (sub_pos.mpr hbc) (sub_pos.mpr hab)] at H
  have hUV : 0 ≤ (b-a)*(xiRealLogDeriv c-xiRealLogDeriv b) :=
    mul_nonneg (sub_nonneg.mpr hab.le) (sub_nonneg.mpr (strictMono_xiRealLogDeriv hbc).le)
  have hh : Real.sqrt ((b-a)*(xiRealLogDeriv c-xiRealLogDeriv b)) <
      Real.sqrt ((c-b)*(xiRealLogDeriv b-xiRealLogDeriv a)) :=
    Real.sqrt_lt_sqrt hUV (by linarith only [H])
  have he := segment_defect hab.le hbc.le
  have hs := sq_pos_of_ne_zero (sub_ne_zero.mpr hh.ne)
  change thetaJeffreysLength a b + thetaJeffreysLength b c < thetaJeffreysLength a c
  have hp : 0 ≤ thetaJeffreysLength a c := Real.sqrt_nonneg _
  nlinarith only [he,hs,hp]


end

end ThetaCuspSections
