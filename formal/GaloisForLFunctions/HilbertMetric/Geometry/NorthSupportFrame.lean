import GaloisForLFunctions.HilbertMetric.Geometry.SmoothSupportCompactification
import GaloisForLFunctions.HilbertMetric.Geometry.BonnetSecondForm

/-!
# Actual first and second derivatives at the compactifying pole

The flat Schwartz displacement leaves the round first and second jets
unchanged. The pole is regular, and a height maximum there has precisely
the north-pole direction.
-/

open scoped ContDiff
namespace GaloisForLFunctions.HilbertMetric.Geometry.NorthSupportFrame
open Bottcher StereographicFrame BonnetSupport SchwartzInversion
open SmoothSupportCompactification SchwartzSurfaceCorrection SphericalChartRecovery
noncomputable section

private theorem round_formula (z : ℂ) :
    stereoInvExtended z = -normal (-z.re, z.im) := by
  ext i
  fin_cases i <;>
    simp [stereoInvExtended, normal_formula, denominator, Complex.sq_norm, Complex.normSq_apply]
    <;> ring

private theorem kelvin_line_hasDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : SchwartzMap ℂ F) (w : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => kelvin f (s • w))
      (kelvin (kelvinDerivative f) (t • w) w) t := by
  simpa only [one_smul, Function.comp_def, id_eq] using
    (kelvin_hasFDerivAt f (t • w)).comp_hasDerivAt t ((hasDerivAt_id t).smul_const w)

private theorem kelvin_line_second {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : SchwartzMap ℂ F) (w : ℂ) :
    deriv (deriv (fun t : ℝ => kelvin f (t • w))) 0 = 0 := by
  have he : deriv (fun t : ℝ => kelvin f (t • w)) =
      (fun t => kelvin (kelvinDerivative f) (t • w) w) :=
    funext (fun t => (kelvin_line_hasDerivAt f w t).deriv)
  rw [he]
  have h := (kelvin_line_hasDerivAt (kelvinDerivative f) w 0).clm_apply (hasDerivAt_const 0 w)
  simpa only [zero_smul, kelvin_zero, zero_apply,
    map_zero, add_zero] using h.deriv

/-- The two coordinate derivatives of the round north chart are explicit. -/
theorem round_partials :
    deriv (fun t : ℝ => stereoInvExtended (t : ℂ)) 0 = !₂[2, 0, 0] ∧
    deriv (fun t : ℝ => stereoInvExtended (t * Complex.I)) 0 = !₂[0, -2, 0] := by
  have hx := (normal_path (hasDerivAt_id (0 : ℝ)).neg (hasDerivAt_const 0 (0 : ℝ))).neg
  have hy := (normal_path (hasDerivAt_const 0 (0 : ℝ)) (hasDerivAt_id (0 : ℝ))).neg
  constructor
  · have he : (fun t : ℝ => stereoInvExtended (t : ℂ)) = (fun t => -normal (-t, 0)) := by
      funext t
      simpa using round_formula (t : ℂ)
    rw [he]
    have hd := hx.deriv
    change deriv (fun t : ℝ => -normal (-t, 0)) 0 = _ at hd
    apply hd.trans
    ext i
    fin_cases i <;> simp [tangentX, tangentY, denominator]
  · have he : (fun t : ℝ => stereoInvExtended (t * Complex.I)) = (fun t => -normal (0, t)) := by
      funext t
      simpa using round_formula (t * Complex.I)
    rw [he]
    have hd := hy.deriv
    change deriv (fun t : ℝ => -normal (0, t)) 0 = _ at hd
    apply hd.trans
    ext i
    fin_cases i <;> simp [tangentX, tangentY, denominator, PiLp.neg_apply]

/-- The actual second derivative in the real direction points inward with magnitude four. -/
theorem round_second :
    deriv (deriv (fun t : ℝ => stereoInvExtended (t : ℂ))) 0 = !₂[0, 0, -4] := by
  have he : deriv (fun t : ℝ => stereoInvExtended (t : ℂ)) =
      (fun t => tangentX (-t, 0)) := by
    funext t
    have h := (normal_path (hasDerivAt_id t).neg (hasDerivAt_const t (0 : ℝ))).neg
    have hf : (fun t : ℝ => stereoInvExtended (t : ℂ)) = (fun t => -normal (-t, 0)) := by
      funext s
      simpa using round_formula (s : ℂ)
    rw [hf]
    have hd := h.deriv
    change deriv (fun s : ℝ => -normal (-s, 0)) t =
      - ((-1 : ℝ) • tangentX (-t, 0) + (0 : ℝ) • tangentY (-t, 0)) at hd
    simpa only [neg_one_smul, zero_smul, add_zero, neg_neg] using hd
  rw [he]
  have h := tangentX_path (hasDerivAt_id (0 : ℝ)).neg (hasDerivAt_const 0 (0 : ℝ))
  have hd := h.deriv
  change deriv (fun t : ℝ => tangentX (-t, 0)) 0 = _ at hd
  apply hd.trans
  ext i
  fin_cases i <;> simp [normal_formula, tangentX, tangentY, denominator,
    PiLp.smul_apply]

/-- Flatness preserves the two actual surface tangents at the pole. -/
theorem north_partials (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ) :
    deriv (fun t : ℝ => north f ε (t : ℂ)) 0 = !₂[2, 0, 0] ∧
    deriv (fun t : ℝ => north f ε (t * Complex.I)) 0 = !₂[0, -2, 0] := by
  have hr := (stereoInvExtended_smooth.differentiable (by simp) 0).hasFDerivAt
  have hn := ((north_smooth f ε).differentiable (by simp) 0).hasFDerivAt
  rw [north_fderiv_round] at hn
  have hx : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
  have hy : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I 0 := by
    simpa only [one_mul] using hx.mul_const Complex.I
  constructor
  · have h₁ := hn.comp_hasDerivAt (f := fun t : ℝ => (t : ℂ)) 0 hx
    have h₂ := hr.comp_hasDerivAt (f := fun t : ℝ => (t : ℂ)) 0 hx
    exact h₁.deriv.trans (h₂.deriv.symm.trans round_partials.1)
  · have hnI : HasFDerivAt (north f ε) (fderiv ℝ stereoInvExtended 0) ((0 : ℂ) * Complex.I) := by
      simpa only [zero_mul] using hn
    have hrI : HasFDerivAt stereoInvExtended (fderiv ℝ stereoInvExtended 0) ((0 : ℂ) * Complex.I) := by
      simpa only [zero_mul] using hr
    have h₁ := hnI.comp_hasDerivAt (f := fun t : ℝ => (t : ℂ) * Complex.I) 0 hy
    have h₂ := hrI.comp_hasDerivAt (f := fun t : ℝ => (t : ℂ) * Complex.I) 0 hy
    exact h₁.deriv.trans (h₂.deriv.symm.trans round_partials.2)

/-- The pole has the round second derivative despite the nonzero Schwartz tail. -/
theorem north_second (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ) :
    deriv (deriv (fun t : ℝ => north f ε (t : ℂ))) 0 = !₂[0, 0, -4] := by
  let g := ε • complexDisplacement f
  have hs : ContDiff ℝ ∞ (fun t : ℝ => stereoInvExtended (t : ℂ)) :=
    stereoInvExtended_smooth.comp Complex.ofRealCLM.contDiff
  have hk : ContDiff ℝ ∞ (fun t : ℝ => kelvin g (t : ℂ)) :=
    (kelvin_contDiff g).comp Complex.ofRealCLM.contDiff
  have he : deriv (fun t : ℝ => north f ε (t : ℂ)) =
      deriv (fun t : ℝ => stereoInvExtended (t : ℂ)) +
      deriv (fun t : ℝ => kelvin g (t : ℂ)) := by
    funext t
    exact deriv_add (hs.differentiable (by simp) t) (hk.differentiable (by simp) t)
  rw [he, deriv_add ((contDiff_infty_iff_deriv.mp hs).2.differentiable (by simp) 0)
    ((contDiff_infty_iff_deriv.mp hk).2.differentiable (by simp) 0)]
  have hz : deriv (deriv (fun t : ℝ => kelvin g (t : ℂ))) 0 = 0 := by
    simpa only [Complex.real_smul, mul_one] using kelvin_line_second g 1
  rw [hz, add_zero, round_second]

/-- The full actual north-chart differential has the round coordinate formula. -/
theorem north_fderiv_apply (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ) (z : ℂ) :
    fderiv ℝ (north f ε) 0 z = !₂[2 * z.re, -2 * z.im, 0] := by
  have hd := ((north_smooth f ε).differentiable (by simp) 0).hasFDerivAt
  have hreal : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
  have himag : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I 0 := by
    simpa only [one_mul] using hreal.mul_const Complex.I
  have hx := hd.comp_hasDerivAt (f := fun t : ℝ => (t : ℂ)) 0 hreal
  have hdI : HasFDerivAt (north f ε) (fderiv ℝ (north f ε) 0) ((0 : ℂ) * Complex.I) := by
    simpa only [zero_mul] using hd
  have hy := hdI.comp_hasDerivAt (f := fun t : ℝ => (t : ℂ) * Complex.I) 0 himag
  have h₁ : fderiv ℝ (north f ε) 0 (1 : ℂ) = !₂[2, 0, 0] := by
    simpa using hx.deriv.symm.trans (north_partials f ε).1
  have hI : fderiv ℝ (north f ε) 0 Complex.I = !₂[0, -2, 0] := by
    simpa using hy.deriv.symm.trans (north_partials f ε).2
  have he : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [he, map_add, map_smul, map_smul, h₁, hI]
  ext i
  fin_cases i <;> simp [PiLp.add_apply, PiLp.smul_apply] <;> ring

/-- The compactifying pole is an immersion point of the actual surface. -/
theorem north_fderiv_injective (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ) :
    Function.Injective (fderiv ℝ (north f ε) 0) := by
  intro z w h
  rw [north_fderiv_apply, north_fderiv_apply] at h
  have hx := congrArg (fun v : StereographicFrame.Space => v 0) h
  have hy := congrArg (fun v : StereographicFrame.Space => v 1) h
  change 2 * z.re = 2 * w.re at hx
  change -2 * z.im = -2 * w.im at hy
  apply Complex.ext
  · linarith only [hx]
  · linarith only [hy]

#print axioms north_fderiv_injective
#print axioms north_fderiv_apply

/-- A unit height direction at a pole maximum is the north-pole normal. -/
theorem normal_of_north_height_max (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ)
    (n : StereographicFrame.Space) (hn : ‖n‖ = 1)
    (hx : IsLocalMax (fun t : ℝ => inner ℝ (north f ε (t : ℂ)) n) 0)
    (hy : IsLocalMax (fun t : ℝ => inner ℝ (north f ε (t * Complex.I)) n) 0) :
    n = northPole := by
  have hs : ContDiff ℝ ∞ (fun t : ℝ => north f ε (t : ℂ)) :=
    (north_smooth f ε).comp Complex.ofRealCLM.contDiff
  have ht : ContDiff ℝ ∞ (fun t : ℝ => north f ε ((t : ℂ) * Complex.I)) :=
    (north_smooth f ε).comp (Complex.ofRealCLM.contDiff.mul contDiff_const)
  have hdx : HasDerivAt (fun t : ℝ => north f ε (t : ℂ)) !₂[2, 0, 0] 0 := by
    rw [← (north_partials f ε).1]
    exact (hs.differentiable (by simp) 0).hasDerivAt
  have hdy : HasDerivAt (fun t : ℝ => north f ε (t * Complex.I)) !₂[0, -2, 0] 0 := by
    rw [← (north_partials f ε).2]
    exact (ht.differentiable (by simp) 0).hasDerivAt
  have hex := hx.hasDerivAt_eq_zero (hdx.inner ℝ (hasDerivAt_const 0 n))
  have hey := hy.hasDerivAt_eq_zero (hdy.inner ℝ (hasDerivAt_const 0 n))
  simp [PiLp.inner_apply, Fin.sum_univ_three] at hex hey
  have hn0 : n 0 = 0 := by linarith only [hex]
  have hn1 : n 1 = 0 := by linarith only [hey]
  have hd := (contDiff_infty_iff_deriv.mp hs).2
  have he : deriv (fun t : ℝ => inner ℝ (north f ε (t : ℂ)) n) =
      (fun t => inner ℝ (deriv (fun s : ℝ => north f ε (s : ℂ)) t) n) := by
    funext t
    have h := ((hs.differentiable (by simp) t).hasDerivAt).inner ℝ (hasDerivAt_const t n)
    simpa only [inner_zero_right, zero_add] using h.deriv
  have hsecond : deriv (deriv (fun t : ℝ => inner ℝ (north f ε (t : ℂ)) n)) 0 = -4 * n 2 := by
    rw [he]
    have h := ((hd.differentiable (by simp) 0).hasDerivAt).inner ℝ (hasDerivAt_const 0 n)
    simpa [north_second, PiLp.inner_apply, Fin.sum_univ_three, mul_comm] using h.deriv
  have hnonpos := _root_.RHTower.suzukiSecondDeriv_nonpos_of_isLocalMax hx
    (hs.continuous.continuousAt.inner continuousAt_const)
  rw [hsecond] at hnonpos
  have hnorm : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  rw [PiLp.inner_apply] at hnorm
  simp only [Fin.sum_univ_three, hn0, hn1, inner_zero_left, zero_add] at hnorm
  change n 2 * n 2 = 1 at hnorm
  have hn2 : n 2 = 1 := by nlinarith only [hnorm, hnonpos]
  ext i
  fin_cases i <;> simp [northPole, hn0, hn1, hn2]

#print axioms normal_of_north_height_max
#print axioms round_partials
#print axioms round_second
#print axioms north_partials
#print axioms north_second
end
end GaloisForLFunctions.HilbertMetric.Geometry.NorthSupportFrame
