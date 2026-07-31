import GaloisForLFunctions.RHTower.PrimeArchBernsteinExponentialPhase

/-!
# Rigidity of the Bernstein ellipse phase

The alignment phase and elliptic radius determine a nonreal point up to reflection across the
critical focal segment.  This identifies all atoms that can share one maximal affine Bernstein
mode.
-/

open Complex

namespace RHTower

noncomputable section

private lemma bernsteinEllipsePhase_mul_relation
    {u : ℂ} (him : u.im ≠ 0) :
    ((‖u‖ : ℂ) * (1 - u) =
      (‖1 - u‖ : ℂ) * (u * bernsteinEllipsePhase u)) := by
  have hu : u ≠ 0 := by
    intro h
    rw [h] at him
    exact him rfl
  have hsub : 1 - u ≠ 0 := by
    intro h
    have hu1 : u = 1 := (sub_eq_zero.mp h).symm
    rw [hu1] at him
    exact him rfl
  rw [bernsteinEllipsePhase]
  have huu : u * (starRingEnd ℂ) u = (‖u‖ ^ 2 : ℂ) := by
    simpa using Complex.mul_conj' u
  rw [show u * ((starRingEnd ℂ u / (‖u‖ : ℂ)) *
      ((1 - u) / (‖1 - u‖ : ℂ))) =
      (u * starRingEnd ℂ u) * (1 - u) /
        ((‖u‖ : ℂ) * (‖1 - u‖ : ℂ)) by ring]
  rw [huu]
  field_simp [norm_ne_zero_iff.mpr hu, norm_ne_zero_iff.mpr hsub]

private lemma bernsteinEllipsePhase_ne_one
    {u : ℂ} (him : u.im ≠ 0) : bernsteinEllipsePhase u ≠ 1 := by
  intro hw
  have halign := bernsteinEllipsePhase_mul_relation him
  rw [hw, mul_one] at halign
  have himEq := congrArg Complex.im halign
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, Complex.sub_im, Complex.one_im] at himEq
  have hu : 0 < ‖u‖ := norm_pos_iff.mpr (by
    intro h
    rw [h] at him
    exact him rfl)
  have hsub : 0 < ‖1 - u‖ := norm_pos_iff.mpr (by
    intro h
    have hu1 : u = 1 := (sub_eq_zero.mp h).symm
    rw [hu1] at him
    exact him rfl)
  exact him (by nlinarith)

private lemma bernsteinEllipsePhase_re_ne_one
    {u : ℂ} (him : u.im ≠ 0) : (bernsteinEllipsePhase u).re ≠ 1 := by
  intro hre
  have hnorm := bernsteinEllipsePhase_norm_eq_one him
  have hnormSq : ‖bernsteinEllipsePhase u‖ ^ 2 = 1 := by
    nlinarith
  have hsq : (bernsteinEllipsePhase u).im ^ 2 = 0 := by
    rw [Complex.sq_norm, Complex.normSq_apply] at hnormSq
    nlinarith
  have him0 : (bernsteinEllipsePhase u).im = 0 := sq_eq_zero_iff.mp hsq
  apply bernsteinEllipsePhase_ne_one him
  apply Complex.ext
  · simpa using hre
  · simpa using him0

private lemma norm_real_add_real_mul_sq
    (a b : ℝ) (w : ℂ) :
    ‖(a : ℂ) + (b : ℂ) * w‖ ^ 2 =
      a ^ 2 + b ^ 2 * ‖w‖ ^ 2 + 2 * a * b * w.re := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im,
    Complex.ofReal_im, Complex.mul_im, zero_mul, zero_add]
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

private lemma bernsteinEllipse_den_norm
    {u : ℂ} (him : u.im ≠ 0) :
    ‖((‖u‖ : ℝ) : ℂ) + ((‖1 - u‖ : ℝ) : ℂ) * bernsteinEllipsePhase u‖ = 1 := by
  have halign := bernsteinEllipsePhase_mul_relation him
  have hu : 0 < ‖u‖ := norm_pos_iff.mpr (by
    intro h
    rw [h] at him
    exact him rfl)
  have hmul : u *
      (((‖u‖ : ℝ) : ℂ) + ((‖1 - u‖ : ℝ) : ℂ) * bernsteinEllipsePhase u) =
      (‖u‖ : ℂ) := by
    calc
      u * (((‖u‖ : ℝ) : ℂ) +
          ((‖1 - u‖ : ℝ) : ℂ) * bernsteinEllipsePhase u) =
          (‖u‖ : ℂ) * u +
            (‖1 - u‖ : ℂ) * (u * bernsteinEllipsePhase u) := by ring
      _ = (‖u‖ : ℂ) * u + (‖u‖ : ℂ) * (1 - u) := by rw [← halign]
      _ = (‖u‖ : ℂ) := by ring
  have hnorm : ‖u‖ *
      ‖(((‖u‖ : ℝ) : ℂ) + ((‖1 - u‖ : ℝ) : ℂ) *
        bernsteinEllipsePhase u)‖ = ‖u‖ := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hu] using congrArg norm hmul
  nlinarith

/-- Equality in the affine Bernstein triangle inequality fixes the unit alignment phase. -/
lemma bernsteinEllipsePhase_eq_of_norm_affine_eq_amplitude
    {u w : ℂ} (huim : u.im ≠ 0) (hw : ‖w‖ = 1)
    (hmax : ‖1 - u + u * w‖ = ‖1 - u‖ + ‖u‖) :
    w = bernsteinEllipsePhase u := by
  have hu : u ≠ 0 := by
    intro h
    rw [h] at huim
    exact huim rfl
  have hsub : 1 - u ≠ 0 := by
    intro h
    have hu1 : u = 1 := (sub_eq_zero.mp h).symm
    rw [hu1] at huim
    exact huim rfl
  have hparallel :
      ‖u * w‖ • (1 - u) = ‖1 - u‖ • (u * w) :=
    norm_add_eq_iff_real.mp (by
      rw [hmax, norm_mul, hw, mul_one])
  have hrel :
      (‖u‖ : ℂ) * (1 - u) = (‖1 - u‖ : ℂ) * (u * w) := by
    simpa only [norm_mul, hw, mul_one, Complex.real_smul] using hparallel
  have hcanonical := bernsteinEllipsePhase_mul_relation huim
  have hscalar : (‖1 - u‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hsub)
  have huw : u * w = u * bernsteinEllipsePhase u := by
    apply mul_left_cancel₀ hscalar
    exact hrel.symm.trans hcanonical
  exact mul_left_cancel₀ hu huw

/-- Elliptic radius and alignment phase determine a nonreal point up to the reflected
complement `v = 1 - conj u`. -/
theorem eq_or_eq_one_sub_conj_of_bernsteinEllipsePhase_eq_of_amplitude_eq
    {u v : ℂ} (huim : u.im ≠ 0) (hvim : v.im ≠ 0)
    (hphase : bernsteinEllipsePhase v = bernsteinEllipsePhase u)
    (hamp : ‖v‖ + ‖1 - v‖ = ‖u‖ + ‖1 - u‖) :
    v = u ∨ v = 1 - star u := by
  let w := bernsteinEllipsePhase u
  let a := ‖u‖
  let b := ‖1 - u‖
  let c := ‖v‖
  let d := ‖1 - v‖
  have ha : 0 < a := norm_pos_iff.mpr (by
    intro h
    rw [h] at huim
    exact huim rfl)
  have hb : 0 < b := norm_pos_iff.mpr (by
    intro h
    have hu1 : u = 1 := (sub_eq_zero.mp h).symm
    rw [hu1] at huim
    exact huim rfl)
  have hc : 0 < c := norm_pos_iff.mpr (by
    intro h
    rw [h] at hvim
    exact hvim rfl)
  have hd : 0 < d := norm_pos_iff.mpr (by
    intro h
    have hv1 : v = 1 := (sub_eq_zero.mp h).symm
    rw [hv1] at hvim
    exact hvim rfl)
  have hw : ‖w‖ = 1 := bernsteinEllipsePhase_norm_eq_one huim
  have hwre : w.re ≠ 1 := bernsteinEllipsePhase_re_ne_one huim
  have huDen : ‖(a : ℂ) + (b : ℂ) * w‖ = 1 := by
    simpa only [a, b, w] using bernsteinEllipse_den_norm huim
  have hvDen : ‖(c : ℂ) + (d : ℂ) * w‖ = 1 := by
    have h := bernsteinEllipse_den_norm hvim
    rw [hphase] at h
    simpa only [c, d, w] using h
  have huSq : ‖(a : ℂ) + (b : ℂ) * w‖ ^ 2 = 1 := by nlinarith
  have hvSq : ‖(c : ℂ) + (d : ℂ) * w‖ ^ 2 = 1 := by nlinarith
  rw [norm_real_add_real_mul_sq, hw] at huSq hvSq
  have hsum : c + d = a + b := by simpa only [a, b, c, d] using hamp
  have hsumSq : (c + d) ^ 2 = (a + b) ^ 2 := by rw [hsum]
  have hprod : c * d = a * b := by
    have hzero : (c * d - a * b) * (w.re - 1) = 0 := by
      nlinarith [hsumSq]
    have hne : w.re - 1 ≠ 0 := sub_ne_zero.mpr hwre
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right hne)
  have hfactor : (c - a) * (c - b) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hca | hcb
  · left
    have hca' : c = a := sub_eq_zero.mp hca
    have hdb : d = b := by nlinarith
    have huRel := bernsteinEllipsePhase_mul_relation huim
    have hvRel := bernsteinEllipsePhase_mul_relation hvim
    rw [hphase] at hvRel
    change (a : ℂ) * (1 - u) = (b : ℂ) * (u * w) at huRel
    change (c : ℂ) * (1 - v) = (d : ℂ) * (v * w) at hvRel
    rw [hca', hdb] at hvRel
    have hdenne : (a : ℂ) + (b : ℂ) * w ≠ 0 := by
      exact norm_ne_zero_iff.mp (by rw [huDen]; norm_num)
    apply mul_right_cancel₀ hdenne
    linear_combination huRel - hvRel
  · right
    have hcb' : c = b := sub_eq_zero.mp hcb
    have hda : d = a := by nlinarith
    have huRel := bernsteinEllipsePhase_mul_relation huim
    have hvRel := bernsteinEllipsePhase_mul_relation hvim
    rw [hphase] at hvRel
    change (a : ℂ) * (1 - u) = (b : ℂ) * (u * w) at huRel
    change (c : ℂ) * (1 - v) = (d : ℂ) * (v * w) at hvRel
    rw [hcb', hda] at hvRel
    have hstarw : star w * w = 1 := by
      calc
        star w * w = (‖w‖ ^ 2 : ℂ) := by simpa using Complex.conj_mul' w
        _ = 1 := by rw [hw]; norm_num
    have huStar :
        (a : ℂ) * (1 - star u) = (b : ℂ) * (star u * star w) := by
      have h := congrArg (starRingEnd ℂ) huRel
      simp only [map_mul, map_sub, map_one, Complex.conj_ofReal] at h
      exact h
    have haw : ((a : ℂ) * w) * (1 - star u) = (b : ℂ) * star u := by
      calc
        ((a : ℂ) * w) * (1 - star u) =
            ((a : ℂ) * (1 - star u)) * w := by ring
        _ = ((b : ℂ) * (star u * star w)) * w := by rw [huStar]
        _ = (b : ℂ) * star u * (star w * w) := by ring
        _ = (b : ℂ) * star u := by rw [hstarw]; ring
    have htarget : (1 - star u) * ((b : ℂ) + (a : ℂ) * w) = (b : ℂ) := by
      calc
        (1 - star u) * ((b : ℂ) + (a : ℂ) * w) =
            (b : ℂ) * (1 - star u) +
              ((a : ℂ) * w) * (1 - star u) := by ring
        _ = (b : ℂ) * (1 - star u) + (b : ℂ) * star u := by rw [haw]
        _ = (b : ℂ) := by ring
    have hvTarget : v * ((b : ℂ) + (a : ℂ) * w) = (b : ℂ) := by
      calc
        v * ((b : ℂ) + (a : ℂ) * w) =
            (b : ℂ) * v + (a : ℂ) * (v * w) := by ring
        _ = (b : ℂ) * v + (b : ℂ) * (1 - v) := by rw [hvRel]
        _ = (b : ℂ) := by ring
    have hdenne : (b : ℂ) + (a : ℂ) * w ≠ 0 := by
      have hnorm : ‖(b : ℂ) + (a : ℂ) * w‖ = 1 := by
        simpa only [hcb', hda] using hvDen
      exact norm_ne_zero_iff.mp (by rw [hnorm]; norm_num)
    apply mul_right_cancel₀ hdenne
    exact hvTarget.trans htarget.symm

end

end RHTower
