import GaloisForLFunctions.RHTower.ThetaCoordinateCanonicalGlobal
import GaloisForLFunctions.RHTower.ThetaFinitePairSturmCrossing

/-! The actual boundary coarea rate is strictly concave in the diagonal Ward clock.
The global source curvature reserve yields strict chord comparisons at every scale. -/

noncomputable section
open Set
namespace RHTower.ThetaDiagonalClock

local notation "p" => thetaCuspLogDecaySlope
local notation "c" => thetaCuspLogCurvature
local notation "v" => thetaCuspLogCurvatureJet
local notation "a" => thetaCuspLogCurvatureJetTwo
local notation "M" => ThetaCoordinate.potentialConvexityMargin

def clock (x : ℝ) : ℝ := x*p x-1
def clockRate (x : ℝ) : ℝ := p x+x*c x
def slopeRatio (x : ℝ) : ℝ := p x/x
private def tangent (x : ℝ) : ℝ := x*c x-p x
def curvatureReserve (x : ℝ) : ℝ := x*M x-(x*c x-p x)^2
def clockSlope (x : ℝ) : ℝ := (x*c x-p x)/(x^2*clockRate x)
def potentialReserve (x : ℝ) : ℝ := x*M x-2*(x*c x-p x)^2
def potentialSlope (x : ℝ) : ℝ := (x*c x-p x)/(x^2*p x)

private theorem p_zero : p 0=0 := by
  simp only [thetaCuspLogDecaySlope,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩,neg_zero]

private theorem positive_from_derivative {f g : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hz : f 0=0)
    (hg : ∀ x, 0 < x → 0 < g x) {x : ℝ} (hx : 0 < x) : 0 < f x := by
  have hm : StrictMonoOn f (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · intro t _; exact (hf t).continuousAt.continuousWithinAt
    · intro t ht
      rw [(hf t).deriv]
      exact hg t (by simpa only [interior_Ici,mem_Ioi] using ht)
  have h := hm (show (0:ℝ) ∈ Ici 0 by simp) (show x ∈ Ici 0 from hx.le) hx
  rwa [hz] at h

private theorem tangent_hasDerivAt (x : ℝ) : HasDerivAt tangent (x*v x) x := by
  convert! ((hasDerivAt_id x).mul (hasDerivAt_thetaCuspLogCurvature x)).sub
    (hasDerivAt_thetaCuspLogDecaySlope x) using 1
  dsimp
  ring

private theorem tangent_pos {x : ℝ} (hx : 0 < x) : 0 < tangent x := by
  apply positive_from_derivative tangent_hasDerivAt ?_ ?_ hx
  · simp only [tangent,zero_mul,p_zero,sub_self]
  · intro t ht; exact mul_pos ht (thetaCuspLogCurvatureJet_pos_of_pos ht)

theorem clock_hasDerivAt (x : ℝ) : HasDerivAt clock (clockRate x) x := by
  convert! ((hasDerivAt_id x).mul (hasDerivAt_thetaCuspLogDecaySlope x)).sub_const 1 using 1
  simp only [clockRate,one_mul,id_eq]

theorem clockRate_hasDerivAt (x : ℝ) :
    HasDerivAt clockRate (2*c x+x*v x) x := by
  convert! (hasDerivAt_thetaCuspLogDecaySlope x).add
    ((hasDerivAt_id x).mul (hasDerivAt_thetaCuspLogCurvature x)) using 1
  dsimp
  ring

theorem clockRate_pos {x : ℝ} (hx : 0 < x) : 0 < clockRate x :=
  add_pos (ThetaSturmCrossing.slope_pos hx) (mul_pos hx (thetaCuspLogCurvature_pos x))

theorem clock_strictMono : StrictMonoOn clock (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi _)
  · intro x _; exact (clock_hasDerivAt x).continuousAt.continuousWithinAt
  · intro x hx
    rw [(clock_hasDerivAt x).deriv]
    exact clockRate_pos (by simpa only [interior_Ioi,mem_Ioi] using hx)

/-- Exact source reserve beyond the earlier potential-convexity margin. -/
theorem curvatureReserve_hasDerivAt (x : ℝ) :
    HasDerivAt curvatureReserve
      (M x+x^2*(c x*v x-p x*a x)+2*x*v x*(x*c x-p x)) x := by
  convert! ((hasDerivAt_id x).mul
    (ThetaCoordinate.potentialConvexityMargin_hasDerivAt x)).sub
      ((tangent_hasDerivAt x).pow 2) using 1
  dsimp [tangent]
  ring

theorem curvatureReserve_pos {x : ℝ} (hx : 0 < x) : 0 < curvatureReserve x := by
  apply positive_from_derivative curvatureReserve_hasDerivAt ?_ ?_ hx
  · simp only [curvatureReserve,zero_mul,p_zero,sub_self,zero_pow (by decide : 2 ≠ 0)]
  · intro t ht
    exact add_pos (add_pos (ThetaCoordinate.potentialConvexityMargin_pos ht)
      (mul_pos (sq_pos_of_pos ht) (ThetaCoordinate.projectiveSlopeReserve_pos ht)))
      (mul_pos (mul_pos (mul_pos (by norm_num) ht)
        (thetaCuspLogCurvatureJet_pos_of_pos ht)) (tangent_pos ht))

theorem curvatureReserve_expansion (x : ℝ) :
    curvatureReserve x=2*x^2*c x^2-x*p x*c x-p x^2-x^2*p x*v x := by
  unfold curvatureReserve ThetaCoordinate.potentialConvexityMargin
  ring

theorem clockSlope_pos {x : ℝ} (hx : 0 < x) : 0 < clockSlope x :=
  div_pos (tangent_pos hx) (mul_pos (sq_pos_of_pos hx) (clockRate_pos hx))

theorem slopeRatio_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt slopeRatio (clockRate x*clockSlope x) x := by
  convert! (hasDerivAt_thetaCuspLogDecaySlope x).div (hasDerivAt_id x) hx.ne' using 1
  unfold clockSlope
  simp only [id_eq]
  field_simp [hx.ne',(clockRate_pos hx).ne']

/-- Strict negative curvature of the literal slope ratio in the Ward clock. -/
theorem clockSlope_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt clockSlope (-2*curvatureReserve x/(x^3*clockRate x^2)) x := by
  have hd := ((hasDerivAt_id x).pow 2).mul (clockRate_hasDerivAt x)
  convert! (tangent_hasDerivAt x).div hd
    (mul_ne_zero (pow_ne_zero 2 hx.ne') (clockRate_pos hx).ne') using 1
  rw [curvatureReserve_expansion]
  simp only [Pi.mul_apply,Pi.pow_apply,id_eq]
  unfold tangent clockRate
  have hQ : p x+x*c x ≠ 0 := (clockRate_pos hx).ne'
  field_simp [hx.ne',hQ]
  ring

theorem clockSlope_strictAnti : StrictAntiOn clockSlope (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi _)
  · intro x hx; exact (clockSlope_hasDerivAt hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx0 : 0 < x := by simpa only [interior_Ioi,mem_Ioi] using hx
    rw [(clockSlope_hasDerivAt hx0).deriv]
    exact div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by norm_num) (curvatureReserve_pos hx0))
      (mul_pos (pow_pos hx0 3) (sq_pos_of_pos (clockRate_pos hx0)))

private theorem strict_clock_chord {f z q s : ℝ → ℝ}
    (df : ∀ t, 0 < t → HasDerivAt f (q t*s t) t)
    (dz : ∀ t, HasDerivAt z (q t) t)
    (hq : ∀ t, 0 < t → 0 < q t) (hs : StrictAntiOn s (Ioi 0))
    {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    (z y-z x)*s y < f y-f x ∧ f y-f x < (z y-z x)*s x := by
  have hy := hx.trans hxy
  have hm : StrictMonoOn (fun t => f t-z t*s y) (Icc x y) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro t ht
      exact ((df t (hx.trans_le ht.1)).sub
        ((dz t).mul_const (s y))).continuousAt.continuousWithinAt
    · intro t ht
      have htxy : x < t ∧ t < y := by simpa only [interior_Icc,mem_Ioo] using ht
      have ht0 := hx.trans htxy.1
      have hd : HasDerivAt (fun t => f t-z t*s y) (q t*s t-q t*s y) t := by
        convert! (df t ht0).sub ((dz t).mul_const (s y)) using 1
      rw [hd.deriv]
      have h := mul_pos (hq t ht0) (sub_pos.mpr (hs ht0 hy htxy.2))
      nlinarith only [h]
  have hn : StrictMonoOn (fun t => z t*s x-f t) (Icc x y) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro t ht
      exact (((dz t).mul_const (s x)).sub
        (df t (hx.trans_le ht.1))).continuousAt.continuousWithinAt
    · intro t ht
      have htxy : x < t ∧ t < y := by simpa only [interior_Icc,mem_Ioo] using ht
      have ht0 := hx.trans htxy.1
      have hd : HasDerivAt (fun t => z t*s x-f t) (q t*s x-q t*s t) t := by
        convert! ((dz t).mul_const (s x)).sub (df t ht0) using 1
      rw [hd.deriv]
      have h := mul_pos (hq t ht0) (sub_pos.mpr (hs hx ht0 htxy.1))
      nlinarith only [h]
  have h1 := hm ⟨le_rfl,hxy.le⟩ ⟨hxy.le,le_rfl⟩ hxy
  have h2 := hn ⟨le_rfl,hxy.le⟩ ⟨hxy.le,le_rfl⟩ hxy
  constructor <;> nlinarith only [h1,h2]

/-- Every ordered positive source pair has strict lower and upper Ward-clock tangents. -/
theorem slopeRatio_clock_chord {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    (clock y-clock x)*clockSlope y < slopeRatio y-slopeRatio x ∧
      slopeRatio y-slopeRatio x < (clock y-clock x)*clockSlope x :=
  strict_clock_chord (fun _ ht => slopeRatio_hasDerivAt ht) clock_hasDerivAt
    (fun _ ht => clockRate_pos ht) clockSlope_strictAnti hx hxy

/-- The stronger potential-clock reserve has an entirely positive source derivative. -/
theorem potentialReserve_hasDerivAt (x : ℝ) :
    HasDerivAt potentialReserve (M x+x^2*(c x*v x-p x*a x)) x := by
  convert! ((hasDerivAt_id x).mul
    (ThetaCoordinate.potentialConvexityMargin_hasDerivAt x)).sub
      (((tangent_hasDerivAt x).pow 2).const_mul 2) using 1
  dsimp [tangent]
  ring

theorem potentialReserve_pos {x : ℝ} (hx : 0 < x) : 0 < potentialReserve x := by
  apply positive_from_derivative potentialReserve_hasDerivAt ?_ ?_ hx
  · simp only [potentialReserve,zero_mul,p_zero,sub_self,
      zero_pow (by decide : 2 ≠ 0),mul_zero]
  · intro t ht
    exact add_pos (ThetaCoordinate.potentialConvexityMargin_pos ht)
      (mul_pos (sq_pos_of_pos ht) (ThetaCoordinate.projectiveSlopeReserve_pos ht))

theorem potentialReserve_expansion (x : ℝ) :
    potentialReserve x=x^2*c x^2+x*p x*c x-2*p x^2-x^2*p x*v x := by
  unfold potentialReserve ThetaCoordinate.potentialConvexityMargin
  ring

theorem potentialSlope_pos {x : ℝ} (hx : 0 < x) : 0 < potentialSlope x :=
  div_pos (tangent_pos hx) (mul_pos (sq_pos_of_pos hx) (ThetaSturmCrossing.slope_pos hx))

theorem slopeRatio_hasDerivAt_potential {x : ℝ} (hx : 0 < x) :
    HasDerivAt slopeRatio (p x*potentialSlope x) x := by
  convert! (hasDerivAt_thetaCuspLogDecaySlope x).div (hasDerivAt_id x) hx.ne' using 1
  unfold potentialSlope
  simp only [id_eq]
  field_simp [hx.ne',(ThetaSturmCrossing.slope_pos hx).ne']

theorem potentialSlope_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt potentialSlope (-potentialReserve x/(x^3*p x^2)) x := by
  have hd := ((hasDerivAt_id x).pow 2).mul (hasDerivAt_thetaCuspLogDecaySlope x)
  convert! (tangent_hasDerivAt x).div hd
    (mul_ne_zero (pow_ne_zero 2 hx.ne') (ThetaSturmCrossing.slope_pos hx).ne') using 1
  rw [potentialReserve_expansion]
  simp only [Pi.mul_apply,Pi.pow_apply,id_eq]
  unfold tangent
  field_simp [hx.ne',(ThetaSturmCrossing.slope_pos hx).ne']
  ring

theorem potentialSlope_strictAnti : StrictAntiOn potentialSlope (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi _)
  · intro x hx; exact (potentialSlope_hasDerivAt hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx0 : 0 < x := by simpa only [interior_Ioi,mem_Ioi] using hx
    rw [(potentialSlope_hasDerivAt hx0).deriv]
    exact div_neg_of_neg_of_pos (neg_lt_zero.mpr (potentialReserve_pos hx0))
      (mul_pos (pow_pos hx0 3) (sq_pos_of_pos (ThetaSturmCrossing.slope_pos hx0)))

/-- Strict global source-potential concavity, expressed without an inverse clock. -/
theorem slopeRatio_potential_chord {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    (ThetaCoordinate.sourcePotential y-ThetaCoordinate.sourcePotential x)*potentialSlope y <
      slopeRatio y-slopeRatio x ∧ slopeRatio y-slopeRatio x <
        (ThetaCoordinate.sourcePotential y-ThetaCoordinate.sourcePotential x)*potentialSlope x :=
  strict_clock_chord (fun _ ht => slopeRatio_hasDerivAt_potential ht)
    ThetaCoordinate.sourcePotential_hasDerivAt (fun _ ht => ThetaSturmCrossing.slope_pos ht)
    potentialSlope_strictAnti hx hxy

end RHTower.ThetaDiagonalClock
