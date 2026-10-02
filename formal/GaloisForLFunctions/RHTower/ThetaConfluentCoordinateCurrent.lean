import GaloisForLFunctions.RHTower.ThetaCuspCurvatureProjectiveGlobal

/-! A global positive current for the center confluent coordinate energy.
The projective curvature reserve integrates twice to a slope-curvature
inequality. A third primitive yields a positive decomposition of the current. -/

noncomputable section
open Set
namespace RHTower.ThetaCoordinate

local notation "p" => thetaCuspLogDecaySlope
local notation "c" => thetaCuspLogCurvature
local notation "v" => thetaCuspLogCurvatureJet
local notation "a" => thetaCuspLogCurvatureJetTwo
local notation "R" => thetaCuspCompletedCurvatureProjectiveRatio
local notation "P" => thetaCuspCompletedCurvatureProjectiveEnergy

private theorem positive_from_derivative {f g : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (g t) t) (hz : f 0 = 0)
    (hg : ∀ t, 0 < t → 0 < g t) {t : ℝ} (ht : 0 < t) : 0 < f t := by
  have hm : StrictMonoOn f (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · intro x _
      exact (hf x).continuousAt.continuousWithinAt
    · intro x hx
      rw [(hf x).deriv]
      exact hg x (by simpa only [interior_Ici, mem_Ioi] using hx)
  have h := hm (show (0:ℝ) ∈ Ici 0 by simp) ht.le ht
  rwa [hz] at h

private theorem slope_zero : p 0 = 0 := by
  simp only [thetaCuspLogDecaySlope,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩, neg_zero]

private theorem velocity_zero : v 0 = 0 := by
  simp only [thetaCuspLogCurvatureJet,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 3) ⟨1,rfl⟩, neg_zero]

private theorem curvature_above_center {t : ℝ} (ht : 0 < t) : 0 < c t-c 0 := by
  exact positive_from_derivative
    (fun x => (hasDerivAt_thetaCuspLogCurvature x).sub_const (c 0)) (sub_self _)
    (fun _ hx => thetaCuspLogCurvatureJet_pos_of_pos hx) ht

private theorem slope_above_tangent {t : ℝ} (ht : 0 < t) : 0 < p t-c 0*t := by
  apply positive_from_derivative (g := fun x => c x-c 0) ?_ ?_ ?_ ht
  · intro x
    convert! (hasDerivAt_thetaCuspLogDecaySlope x).sub
      ((hasDerivAt_id x).const_mul (c 0)) using 1
    simp only [mul_one]
  · simp only [slope_zero, mul_zero, sub_zero]
  · exact fun _ hx => curvature_above_center hx

private theorem slope_pos {t : ℝ} (ht : 0 < t) : 0 < p t := by
  have h := slope_above_tangent ht
  have hq := mul_pos (thetaCuspLogCurvature_pos 0) ht
  linarith

private def projectivePrimitive (t : ℝ) : ℝ := v t-p t*R t

private theorem projectivePrimitive_hasDerivAt (t : ℝ) :
    HasDerivAt projectivePrimitive (p t*P t/c t^2) t := by
  convert! (hasDerivAt_thetaCuspLogCurvatureJet t).sub
    ((hasDerivAt_thetaCuspLogDecaySlope t).mul
      (hasDerivAt_thetaCuspCompletedCurvatureProjectiveRatio t)) using 1
  unfold thetaCuspCompletedCurvatureProjectiveRatio
  field_simp [(thetaCuspLogCurvature_pos t).ne']
  ring

private theorem projectivePrimitive_pos {t : ℝ} (ht : 0 < t) :
    0 < projectivePrimitive t := by
  apply positive_from_derivative projectivePrimitive_hasDerivAt ?_ ?_ ht
  · simp only [projectivePrimitive, velocity_zero, slope_zero, zero_mul, sub_zero]
  · intro x hx
    exact div_pos (mul_pos (slope_pos hx) (ThetaCuspDefect.projectiveEnergy_pos hx))
      (sq_pos_of_pos (thetaCuspLogCurvature_pos x))

/-- A strict slope-curvature reserve obtained by integrating projective descent. -/
def slopeEnergy (t : ℝ) : ℝ := c t^2-c 0^2-p t*v t

theorem slopeEnergy_hasDerivAt (t : ℝ) :
    HasDerivAt slopeEnergy (c t*v t-p t*a t) t := by
  convert! (((hasDerivAt_thetaCuspLogCurvature t).pow 2).sub_const (c 0^2)).sub
    ((hasDerivAt_thetaCuspLogDecaySlope t).mul
      (hasDerivAt_thetaCuspLogCurvatureJet t)) using 1
  ring

theorem slopeEnergy_pos {t : ℝ} (ht : 0 < t) : 0 < slopeEnergy t := by
  apply positive_from_derivative slopeEnergy_hasDerivAt ?_ ?_ ht
  · simp only [slopeEnergy, slope_zero, zero_mul, sub_self]
  · intro x hx
    have he : c x*v x-p x*a x = c x*projectivePrimitive x := by
      unfold projectivePrimitive thetaCuspCompletedCurvatureProjectiveRatio
      field_simp [(thetaCuspLogCurvature_pos x).ne']
    rw [he]
    exact mul_pos (thetaCuspLogCurvature_pos x) (projectivePrimitive_pos hx)

/-- The center chord comparison needed to compensate the coordinate current. -/
def chordReserve (t : ℝ) : ℝ := p t*(c t+2*c 0)-c 0*t*(2*c t+c 0)

theorem chordReserve_hasDerivAt (t : ℝ) :
    HasDerivAt chordReserve (slopeEnergy t+2*(p t-c 0*t)*v t) t := by
  convert! ((hasDerivAt_thetaCuspLogDecaySlope t).mul
    ((hasDerivAt_thetaCuspLogCurvature t).add_const (2*c 0))).sub
    (((hasDerivAt_id t).const_mul (c 0)).mul
      (((hasDerivAt_thetaCuspLogCurvature t).const_mul 2).add_const (c 0))) using 1
  simp only [slopeEnergy, id_eq]
  ring

theorem chordReserve_pos {t : ℝ} (ht : 0 < t) : 0 < chordReserve t := by
  apply positive_from_derivative chordReserve_hasDerivAt ?_ ?_ ht
  · simp only [chordReserve, slope_zero, zero_mul, mul_zero, sub_zero]
  · intro x hx
    exact add_pos (slopeEnergy_pos hx)
      (mul_pos (mul_pos (by norm_num) (slope_above_tangent hx))
        (thetaCuspLogCurvatureJet_pos_of_pos hx))

/-- Gaussian-cancelling current for the first nonzero center coordinate sign. -/
def coordinateCurrent (t : ℝ) : ℝ :=
  p t*c t+3*t*c t^2-t*p t*v t-6*c 0*t*c t+2*c 0*p t

/-- All three terms in the decomposition have independently proved signs. -/
theorem coordinateCurrent_decomposition (t : ℝ) :
    coordinateCurrent t = t*slopeEnergy t+chordReserve t+2*t*(c t-c 0)^2 := by
  unfold coordinateCurrent slopeEnergy chordReserve
  ring

/-- Global strict positivity for the literal theta source, with no tail cutoff. -/
theorem coordinateCurrent_pos {t : ℝ} (ht : 0 < t) : 0 < coordinateCurrent t := by
  rw [coordinateCurrent_decomposition]
  exact add_pos_of_pos_of_nonneg
    (add_pos (mul_pos ht (slopeEnergy_pos ht)) (chordReserve_pos ht))
    (mul_nonneg (mul_nonneg (by norm_num) ht.le) (sq_nonneg _))

end RHTower.ThetaCoordinate
