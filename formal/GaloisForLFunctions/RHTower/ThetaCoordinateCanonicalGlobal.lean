import GaloisForLFunctions.RHTower.ThetaCoordinateCrossCurrent

/-! Global sign of the literal canonical coordinate current. Projective descent
makes curvature concave and the position-to-slope ratio convex in source potential.
Their strict endpoint inequalities pay the complete base margin. -/

noncomputable section
open Set
namespace RHTower.ThetaCoordinate

local notation "p" => thetaCuspLogDecaySlope
local notation "c" => thetaCuspLogCurvature
local notation "v" => thetaCuspLogCurvatureJet
local notation "a" => thetaCuspLogCurvatureJetTwo

private theorem positive_after {f g : ℝ → ℝ} {x z : ℝ}
    (hf : ∀ s, x ≤ s → HasDerivAt f (g s) s) (hx : f x = 0)
    (hg : ∀ s, x < s → 0 < g s) (hxz : x < z) : 0 < f z := by
  have hm : StrictMonoOn f (Ici x) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · intro s hs; exact (hf s hs).continuousAt.continuousWithinAt
    · intro s hs
      have hxs : x < s := by simpa only [interior_Ici, mem_Ioi] using hs
      rw [(hf s hxs.le).deriv]
      exact hg s hxs
  have h := hm (show x ∈ Ici x by simp) hxz.le hxz
  rwa [hx] at h

private theorem p_zero : p 0 = 0 := by
  simp only [thetaCuspLogDecaySlope,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩, neg_zero]

private theorem p_pos {t : ℝ} (ht : 0 < t) : 0 < p t :=
  positive_after (fun x _ => hasDerivAt_thetaCuspLogDecaySlope x) p_zero
    (fun x _ => thetaCuspLogCurvature_pos x) ht

private def tangentReserve (t : ℝ) : ℝ := t*c t-p t

private theorem tangentReserve_hasDerivAt (t : ℝ) :
    HasDerivAt tangentReserve (t*v t) t := by
  convert! ((hasDerivAt_id t).mul (hasDerivAt_thetaCuspLogCurvature t)).sub
    (hasDerivAt_thetaCuspLogDecaySlope t) using 1
  dsimp
  ring

private theorem tangentReserve_pos {t : ℝ} (ht : 0 < t) :
    0 < tangentReserve t := by
  apply positive_after (fun x _ => tangentReserve_hasDerivAt x) ?_ ?_ ht
  · simp only [tangentReserve, zero_mul, p_zero, sub_self]
  · intro x hx; exact mul_pos hx (thetaCuspLogCurvatureJet_pos_of_pos hx)

/-- The actual negative log source is a strictly increasing potential on the positive ray. -/
def sourcePotential (t : ℝ) : ℝ := -thetaCuspLogSource t

theorem sourcePotential_hasDerivAt (t : ℝ) : HasDerivAt sourcePotential (p t) t := by
  have h := hasDerivAt_iteratedDeriv_thetaCuspLogSource 0 t
  change HasDerivAt thetaCuspLogSource (iteratedDeriv 1 thetaCuspLogSource t) t at h
  exact h.neg

/-- Positive numerator for convexity of position divided by slope in source potential. -/
def potentialConvexityMargin (t : ℝ) : ℝ := 3*t*c t^2-3*p t*c t-t*p t*v t

theorem potentialConvexityMargin_hasDerivAt (t : ℝ) :
    HasDerivAt potentialConvexityMargin
      (t*(c t*v t-p t*a t)+4*v t*(t*c t-p t)) t := by
  have hp := hasDerivAt_thetaCuspLogDecaySlope t
  have hc := hasDerivAt_thetaCuspLogCurvature t
  have hv := hasDerivAt_thetaCuspLogCurvatureJet t
  have hi := hasDerivAt_id t
  convert! ((((hi.const_mul 3).mul (hc.pow 2)).sub
    ((hp.const_mul 3).mul hc)).sub ((hi.mul hp).mul hv)) using 1
  dsimp
  ring

theorem potentialConvexityMargin_pos {t : ℝ} (ht : 0 < t) :
    0 < potentialConvexityMargin t := by
  apply positive_after (fun x _ => potentialConvexityMargin_hasDerivAt x) ?_ ?_ ht
  · simp only [potentialConvexityMargin, zero_mul, p_zero, mul_zero, sub_self]
  · intro x hx
    exact add_pos (mul_pos hx (projectiveSlopeReserve_pos hx))
      (mul_pos (mul_pos (by norm_num) (thetaCuspLogCurvatureJet_pos_of_pos hx))
        (tangentReserve_pos hx))

private theorem curvaturePotentialRatio_strictAnti :
    StrictAntiOn (fun t => v t/p t) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi _)
  · intro t ht
    exact ((hasDerivAt_thetaCuspLogCurvatureJet t).div
      (hasDerivAt_thetaCuspLogDecaySlope t) (p_pos ht).ne').continuousAt.continuousWithinAt
  · intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ioi, mem_Ioi] using ht
    have hd : HasDerivAt (fun s => v s/p s) ((a t*p t-v t*c t)/p t^2) t :=
      (hasDerivAt_thetaCuspLogCurvatureJet t).div
        (hasDerivAt_thetaCuspLogDecaySlope t) (p_pos ht0).ne'
    rw [hd.deriv]
    apply div_neg_of_neg_of_pos _ (sq_pos_of_pos (p_pos ht0))
    have h := projectiveSlopeReserve_pos ht0
    nlinarith only [h]

private def negativeSlopeRatio (t : ℝ) : ℝ := -(t/p t)
private def negativeSlopeRatioDerivative (t : ℝ) : ℝ := tangentReserve t/p t^2

private theorem negativeSlopeRatio_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt negativeSlopeRatio (negativeSlopeRatioDerivative t) t := by
  convert! (((hasDerivAt_id t).div (hasDerivAt_thetaCuspLogDecaySlope t)
    (p_pos ht).ne').neg) using 1
  dsimp [negativeSlopeRatioDerivative, tangentReserve]
  ring

private theorem positionPotentialRatio_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => negativeSlopeRatioDerivative s/p s)
      (-potentialConvexityMargin t/p t^4) t := by
  have hp := hasDerivAt_thetaCuspLogDecaySlope t
  have hA := tangentReserve_hasDerivAt t
  convert! ((hA.div (hp.pow 2) (pow_ne_zero 2 (p_pos ht).ne')).div hp
    (p_pos ht).ne') using 1
  dsimp [negativeSlopeRatioDerivative, tangentReserve, potentialConvexityMargin]
  field_simp [(p_pos ht).ne']
  ring

private theorem positionPotentialRatio_strictAnti :
    StrictAntiOn (fun t => negativeSlopeRatioDerivative t/p t) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi _)
  · intro t ht; exact (positionPotentialRatio_hasDerivAt ht).continuousAt.continuousWithinAt
  · intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ioi, mem_Ioi] using ht
    rw [(positionPotentialRatio_hasDerivAt ht0).deriv]
    exact div_neg_of_neg_of_pos (neg_lt_zero.mpr (potentialConvexityMargin_pos ht0))
      (pow_pos (p_pos ht0) 4)

private theorem potential_tangent_gap_pos {f f' : ℝ → ℝ}
    (hf : ∀ t, 0 < t → HasDerivAt f (f' t) t)
    (hr : StrictAntiOn (fun t => f' t/p t) (Ioi 0))
    {x z : ℝ} (hx : 0 < x) (hxz : x < z) :
    0 < p z*(f z-f x)-(sourcePotential z-sourcePotential x)*f' z := by
  have hz := hx.trans hxz
  let r := f' z/p z
  have hd (s : ℝ) (hs : 0 < s) :
      HasDerivAt (fun t => f t-sourcePotential t*r) (f' s-p s*r) s :=
    (hf s hs).sub ((sourcePotential_hasDerivAt s).mul_const r)
  have hm : StrictMonoOn (fun t => f t-sourcePotential t*r) (Icc x z) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro s hs; exact (hd s (hx.trans_le hs.1)).continuousAt.continuousWithinAt
    · intro s hs
      have hxs : x < s ∧ s < z := by simpa only [interior_Icc, mem_Ioo] using hs
      have hs0 := hx.trans hxs.1
      rw [(hd s hs0).deriv]
      have h := (div_lt_div_iff₀ (p_pos hz) (p_pos hs0)).mp (hr hs0 hz hxs.2)
      apply (mul_pos_iff_of_pos_right (p_pos hz)).mp
      have he : (f' s-p s*r)*p z = f' s*p z-f' z*p s := by
        dsimp [r]
        field_simp [(p_pos hz).ne']
      rw [he]
      exact sub_pos.mpr h
  have h := hm ⟨le_rfl,hxz.le⟩ ⟨hxz.le,le_rfl⟩ hxz
  have he : p z*(f z-f x)-(sourcePotential z-sourcePotential x)*f' z =
      p z*((f z-sourcePotential z*r)-(f x-sourcePotential x*r)) := by
    dsimp [r]
    field_simp [(p_pos hz).ne']
    ring
  rw [he]
  exact mul_pos (p_pos hz) (sub_pos.mpr h)

/-- Strict curvature trapezoid gap in the actual source potential. -/
def curvatureTrapezoidGap (x z : ℝ) : ℝ :=
  p z^2-p x^2-(sourcePotential z-sourcePotential x)*(c x+c z)

private theorem curvatureTrapezoidGap_hasDerivAt (x z : ℝ) :
    HasDerivAt (curvatureTrapezoidGap x)
      (p z*(c z-c x)-(sourcePotential z-sourcePotential x)*v z) z := by
  convert! (((hasDerivAt_thetaCuspLogDecaySlope z).pow 2).sub_const (p x^2)).sub
    (((sourcePotential_hasDerivAt z).sub_const (sourcePotential x)).mul
      ((hasDerivAt_thetaCuspLogCurvature z).const_add (c x))) using 1
  dsimp
  ring

theorem curvatureTrapezoidGap_pos {x z : ℝ} (hx : 0 < x) (hxz : x < z) :
    0 < curvatureTrapezoidGap x z := by
  apply positive_after (fun s _ => curvatureTrapezoidGap_hasDerivAt x s) ?_ ?_ hxz
  · simp only [curvatureTrapezoidGap, sub_self, zero_mul]
  · intro s hxs
    exact potential_tangent_gap_pos (fun t _ => hasDerivAt_thetaCuspLogCurvature t)
      curvaturePotentialRatio_strictAnti hx hxs

/-- Strict position-to-slope trapezoid gap in the actual source potential. -/
def positionTrapezoidGap (x z : ℝ) : ℝ :=
  (sourcePotential z-sourcePotential x)*(x/p x+z/p z)-(z^2-x^2)

private theorem positionTrapezoidGap_hasDerivAt (x : ℝ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (positionTrapezoidGap x)
      (p z*(negativeSlopeRatio z-negativeSlopeRatio x)-
        (sourcePotential z-sourcePotential x)*negativeSlopeRatioDerivative z) z := by
  have hi := hasDerivAt_id z
  have hp := hasDerivAt_thetaCuspLogDecaySlope z
  convert! (((sourcePotential_hasDerivAt z).sub_const (sourcePotential x)).mul
    ((hi.div hp (p_pos hz).ne').const_add (x/p x))).sub
      ((hi.pow 2).sub_const (x^2)) using 1
  dsimp [negativeSlopeRatio, negativeSlopeRatioDerivative, tangentReserve]
  field_simp [(p_pos hz).ne']
  ring

theorem positionTrapezoidGap_pos {x z : ℝ} (hx : 0 < x) (hxz : x < z) :
    0 < positionTrapezoidGap x z := by
  apply positive_after (fun s hs => positionTrapezoidGap_hasDerivAt x (hx.trans_le hs))
    ?_ ?_ hxz
  · simp only [positionTrapezoidGap, sub_self, zero_mul]
  · intro s hxs
    exact potential_tangent_gap_pos (fun _ ht => negativeSlopeRatio_hasDerivAt ht)
      positionPotentialRatio_strictAnti hx hxs

/-- The two source-potential trapezoids pay the entire canonical base term. -/
theorem canonicalBaseMargin_pos {t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    0 < canonicalBaseMargin t y := by
  have hz := add_pos ht hy
  have htz : t < t+y := by linarith
  have he : canonicalBaseMargin t y = p t*p (t+y)*
      (curvatureTrapezoidGap t (t+y)*(t/p t+(t+y)/p (t+y))+
        positionTrapezoidGap t (t+y)*(c t+c (t+y))) := by
    unfold canonicalBaseMargin curvatureTrapezoidGap positionTrapezoidGap
    field_simp [(p_pos ht).ne', (p_pos hz).ne']
    ring
  rw [he]
  exact mul_pos (mul_pos (p_pos ht) (p_pos hz))
    (add_pos (mul_pos (curvatureTrapezoidGap_pos ht htz)
      (add_pos (div_pos ht (p_pos ht)) (div_pos hz (p_pos hz))))
      (mul_pos (positionTrapezoidGap_pos ht htz)
        (add_pos (thetaCuspLogCurvature_pos t) (thetaCuspLogCurvature_pos (t+y)))))

/-- Global strict positivity of the literal three-point source margin. -/
theorem canonicalMargin_pos {t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    0 < canonicalMargin t y :=
  (canonicalBaseMargin_pos ht hy).trans (canonicalMargin_gt_base ht hy)

/-- The canonical coordinate current is strictly negative throughout the positive quadrant. -/
theorem canonicalCurrent_neg {t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    canonicalCurrent t y < 0 := by
  rw [canonicalCurrent_eq_margin ht hy]
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr (canonicalMargin_pos ht hy))
    (mul_pos (sq_pos_of_pos hy) (sq_pos_of_pos
      (add_pos (p_pos ht) (p_pos (add_pos ht hy)))))

end RHTower.ThetaCoordinate
