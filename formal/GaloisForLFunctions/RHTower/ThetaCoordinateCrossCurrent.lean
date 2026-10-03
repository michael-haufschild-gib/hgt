import GaloisForLFunctions.RHTower.ThetaCuspCurvatureLogConvex
import GaloisForLFunctions.RHTower.ThetaCoordinateCanonicalBoundary

/-! A globally positive interior term in the exact canonical coordinate margin.
Curvature logarithmic convexity forces increasing slope elasticity; its two-point
comparison pays the complete source-superadditivity term in the margin. -/

noncomputable section
open Set
namespace RHTower.ThetaCoordinate

local notation "p" => thetaCuspLogDecaySlope
local notation "c" => thetaCuspLogCurvature
local notation "v" => thetaCuspLogCurvatureJet
local notation "a" => thetaCuspLogCurvatureJetTwo

private theorem positive_from_derivative {f g : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (g t) t) (hz : f 0 = 0)
    (hg : ∀ t, 0 < t → 0 < g t) {t : ℝ} (ht : 0 < t) : 0 < f t := by
  have hm : StrictMonoOn f (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · intro x _; exact (hf x).continuousAt.continuousWithinAt
    · intro x hx
      rw [(hf x).deriv]
      exact hg x (by simpa only [interior_Ici, mem_Ioi] using hx)
  have h := hm (show (0:ℝ) ∈ Ici 0 by simp) ht.le ht
  rwa [hz] at h

private theorem p_zero : p 0 = 0 := by
  simp only [thetaCuspLogDecaySlope,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩, neg_zero]

private theorem p_pos {t : ℝ} (ht : 0 < t) : 0 < p t :=
  positive_from_derivative hasDerivAt_thetaCuspLogDecaySlope p_zero
    (fun x _ => thetaCuspLogCurvature_pos x) ht

private theorem c_strictMono : StrictMonoOn c (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro x _; exact (hasDerivAt_thetaCuspLogCurvature x).continuousAt.continuousWithinAt
  · intro x hx
    rw [(hasDerivAt_thetaCuspLogCurvature x).deriv]
    exact thetaCuspLogCurvatureJet_pos_of_pos
      (by simpa only [interior_Ici, mem_Ioi] using hx)

private theorem tangentReserve_pos {t : ℝ} (ht : 0 < t) : 0 < t*c t-p t := by
  apply positive_from_derivative (g := fun x => x*v x) ?_ ?_ ?_ ht
  · intro x
    convert! ((hasDerivAt_id x).mul (hasDerivAt_thetaCuspLogCurvature x)).sub
      (hasDerivAt_thetaCuspLogDecaySlope x) using 1
    dsimp
    ring
  · simp only [zero_mul, p_zero, sub_self]
  · intro x hx; exact mul_pos hx (thetaCuspLogCurvatureJet_pos_of_pos hx)

private theorem slopeRatio_strictMono : StrictMonoOn (fun t => p t/t) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi _)
  · intro x hx
    exact ((hasDerivAt_thetaCuspLogDecaySlope x).div (hasDerivAt_id x) (ne_of_gt hx)).continuousAt.continuousWithinAt
  · intro x hx
    have hx0 : 0 < x := by simpa only [interior_Ioi, mem_Ioi] using hx
    have hd : HasDerivAt (fun t => p t/t) ((x*c x-p x)/x^2) x := by
      convert! (hasDerivAt_thetaCuspLogDecaySlope x).div (hasDerivAt_id x) hx0.ne' using 1
      dsimp
      ring
    rw [hd.deriv]
    exact div_pos (tangentReserve_pos hx0) (sq_pos_of_pos hx0)

/-- Division-free derivative numerator of the actual slope elasticity. -/
def elasticityMargin (t : ℝ) : ℝ := p t*c t+t*p t*v t-t*c t^2

private theorem normalizedElasticityMargin_hasDerivAt (t : ℝ) :
    HasDerivAt (fun x => elasticityMargin x/c x)
      (p t*v t/c t+t*p t*ThetaCurvature.logEnergy t/c t^2) t := by
  have hp := hasDerivAt_thetaCuspLogDecaySlope t
  have hc := hasDerivAt_thetaCuspLogCurvature t
  have hv := hasDerivAt_thetaCuspLogCurvatureJet t
  have hi := hasDerivAt_id t
  have hM := ((hp.mul hc).add ((hi.mul hp).mul hv)).sub (hi.mul (hc.pow 2))
  convert! hM.div hc (thetaCuspLogCurvature_pos t).ne' using 1
  dsimp [elasticityMargin, ThetaCurvature.logEnergy]
  field_simp [(thetaCuspLogCurvature_pos t).ne']
  ring

theorem elasticityMargin_pos {t : ℝ} (ht : 0 < t) : 0 < elasticityMargin t := by
  have h : 0 < elasticityMargin t/c t := by
    apply positive_from_derivative normalizedElasticityMargin_hasDerivAt ?_ ?_ ht
    · simp only [elasticityMargin, p_zero, zero_mul, mul_zero, add_zero, sub_zero, zero_div]
    · intro x hx
      exact add_pos
        (div_pos (mul_pos (p_pos hx) (thetaCuspLogCurvatureJet_pos_of_pos hx))
          (thetaCuspLogCurvature_pos x))
        (div_pos (mul_pos (mul_pos hx (p_pos hx)) (ThetaCurvature.logEnergy_pos hx.le))
          (sq_pos_of_pos (thetaCuspLogCurvature_pos x)))
  exact (div_pos_iff_of_pos_right (thetaCuspLogCurvature_pos t)).mp h

/-- Logarithmic slope with respect to logarithmic source position. -/
def slopeElasticity (t : ℝ) : ℝ := t*c t/p t

private theorem slopeElasticity_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt slopeElasticity (elasticityMargin t/p t^2) t := by
  convert! ((hasDerivAt_id t).mul (hasDerivAt_thetaCuspLogCurvature t)).div
    (hasDerivAt_thetaCuspLogDecaySlope t) (p_pos ht).ne' using 1
  dsimp [slopeElasticity, elasticityMargin]
  ring

theorem slopeElasticity_strictMono : StrictMonoOn slopeElasticity (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi _)
  · intro x hx; exact (slopeElasticity_hasDerivAt hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx0 : 0 < x := by simpa only [interior_Ioi, mem_Ioi] using hx
    rw [(slopeElasticity_hasDerivAt hx0).deriv]
    exact div_pos (elasticityMargin_pos hx0) (sq_pos_of_pos (p_pos hx0))

private theorem slopeElasticity_pos {t : ℝ} (ht : 0 < t) : 0 < slopeElasticity t :=
  div_pos (mul_pos ht (thetaCuspLogCurvature_pos t)) (p_pos ht)

private theorem reciprocal_sum_mono {r s : ℝ} (hs : 1 ≤ s) (hrs : s ≤ r) :
    s+1/s ≤ r+1/r := by
  have hsp : 0 < s := by linarith
  have hrp : 0 < r := hsp.trans_le hrs
  have hprod : 0 ≤ r*s-1 := by
    nlinarith [mul_nonneg (show 0 ≤ r-1 by linarith) (show 0 ≤ s-1 by linarith)]
  have he : r+1/r-(s+1/s) = (r-s)*(r*s-1)/(r*s) := by
    field_simp [hrp.ne', hsp.ne']
    ring
  apply sub_nonneg.mp
  rw [he]
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr hrs) hprod) (mul_pos hrp hsp).le

private def crossComparison (x z : ℝ) : ℝ :=
  p z/p x-p x/p z-slopeElasticity x*(z/x-x/z)

private theorem crossComparison_hasDerivAt {x z : ℝ} (hx : 0 < x) (hz : 0 < z) :
    HasDerivAt (crossComparison x)
      (slopeElasticity z/z*(p z/p x+p x/p z)-
        slopeElasticity x/z*(z/x+x/z)) z := by
  have hp := hasDerivAt_thetaCuspLogDecaySlope z
  have hi := hasDerivAt_id z
  have h1 := (hp.div_const (p x)).sub ((hasDerivAt_const z (p x)).div hp (p_pos hz).ne')
  have h2 := ((hi.div_const x).sub ((hasDerivAt_const z x).div hi hz.ne')).const_mul
    (slopeElasticity x)
  convert! h1.sub h2 using 1
  dsimp [crossComparison, slopeElasticity]
  field_simp [hx.ne', hz.ne', (p_pos hx).ne', (p_pos hz).ne']
  ring

private theorem crossComparison_derivative_pos {x z : ℝ} (hx : 0 < x) (hxz : x < z) :
    0 < slopeElasticity z/z*(p z/p x+p x/p z)-
      slopeElasticity x/z*(z/x+x/z) := by
  have hz := hx.trans hxz
  have hp := (div_lt_div_iff₀ hx hz).mp (slopeRatio_strictMono hx hz hxz)
  have hrs : z/x < p z/p x := (div_lt_div_iff₀ hx (p_pos hx)).mpr (by nlinarith only [hp])
  have hs : 1 ≤ z/x := ((lt_div_iff₀ hx).mpr (by simpa using hxz)).le
  have hrec : z/x+x/z ≤ p z/p x+p x/p z := by
    convert! reciprocal_sum_mono hs hrs.le using 1 <;>
      field_simp [hx.ne', hz.ne', (p_pos hx).ne', (p_pos hz).ne']
  have hel := slopeElasticity_strictMono hx hz hxz
  have hsum : 0 < p z/p x+p x/p z :=
    add_pos (div_pos (p_pos hz) (p_pos hx)) (div_pos (p_pos hx) (p_pos hz))
  have he : slopeElasticity z/z*(p z/p x+p x/p z)-
      slopeElasticity x/z*(z/x+x/z) =
      (slopeElasticity z-slopeElasticity x)*(p z/p x+p x/p z)/z+
        (slopeElasticity x/z)*((p z/p x+p x/p z)-(z/x+x/z)) := by ring
  rw [he]
  exact add_pos_of_pos_of_nonneg (div_pos (mul_pos (sub_pos.mpr hel) hsum) hz)
    (mul_nonneg (div_pos (slopeElasticity_pos hx) hz).le (sub_nonneg.mpr hrec))

private theorem crossComparison_pos {x z : ℝ} (hx : 0 < x) (hxz : x < z) :
    0 < crossComparison x z := by
  have hm : StrictMonoOn (crossComparison x) (Ici x) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · intro s hs
      exact (crossComparison_hasDerivAt hx (hx.trans_le hs)).continuousAt.continuousWithinAt
    · intro s hs
      have hxs : x < s := by simpa only [interior_Ici, mem_Ioi] using hs
      rw [(crossComparison_hasDerivAt hx (hx.trans hxs)).deriv]
      exact crossComparison_derivative_pos hx hxs
  have h := hm (show x ∈ Ici x by simp) hxz.le hxz
  have h0 : crossComparison x x = 0 := by simp only [crossComparison, sub_self, mul_zero]
  rwa [h0] at h

/-- The complete two-point cross term occurring inside the three-point margin. -/
def crossMargin (x z : ℝ) : ℝ :=
  p z^2-p x^2-(x+z)*(p z*c x-p x*c z)

/-- Strict interior positivity for every two distinct positive source positions. -/
theorem crossMargin_pos {x z : ℝ} (hx : 0 < x) (hxz : x < z) :
    0 < crossMargin x z := by
  have hz := hx.trans hxz
  have he : crossMargin x z = p x*p z*(crossComparison x z+
      (x+z)/z*(slopeElasticity z-slopeElasticity x)) := by
    unfold crossMargin crossComparison slopeElasticity
    field_simp [hx.ne', hz.ne', (p_pos hx).ne', (p_pos hz).ne']
    ring
  rw [he]
  exact mul_pos (mul_pos (p_pos hx) (p_pos hz))
    (add_pos (crossComparison_pos hx hxz)
      (mul_pos (div_pos (add_pos hx hz) hz)
        (sub_pos.mpr (slopeElasticity_strictMono hx hz hxz))))

private theorem source_addition_pos {t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    0 < p (t+y)-p t-p y := by
  apply positive_from_derivative (g := fun x => c (x+y)-c x) ?_ ?_ ?_ ht
  · intro x
    convert! (((hasDerivAt_thetaCuspLogDecaySlope (x+y)).comp x
      ((hasDerivAt_id x).add_const y)).sub (hasDerivAt_thetaCuspLogDecaySlope x)).sub_const
      (p y) using 1
    simp only [mul_one]
  · simp only [zero_add, p_zero, sub_zero, sub_self]
  · intro x hx
    exact sub_pos.mpr (c_strictMono hx.le (add_pos hx hy).le (by linarith))

/-- The remaining base term; its sign is not asserted here. -/
def canonicalBaseMargin (t y : ℝ) : ℝ :=
  (p (t+y)^2-p t^2)*(t*(p t+p (t+y))+y*p t)-
    y*(2*t+y)*p t*p (t+y)*(c t+c (t+y))

theorem canonicalMargin_decomposition (t y : ℝ) :
    canonicalMargin t y = canonicalBaseMargin t y+
      y*(p (t+y)-p t-p y)*crossMargin t (t+y) := by
  unfold canonicalMargin canonicalBaseMargin crossMargin
  ring

/-- Global strict compensation supplied by the actual source, throughout the interior. -/
theorem canonicalMargin_gt_base {t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    canonicalBaseMargin t y < canonicalMargin t y := by
  rw [canonicalMargin_decomposition]
  have h := mul_pos (mul_pos hy (source_addition_pos ht hy))
    (crossMargin_pos ht (by linarith : t < t+y))
  linarith

end RHTower.ThetaCoordinate
