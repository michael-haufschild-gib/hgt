import GaloisForLFunctions.FamilyContinuationTheory.TheSignalOfTheZetaKernelIsAMoebiusSum
import GaloisForLFunctions.RHTower.BarnesEulerRemainderStep

/-!
# Interpolation between two observations of a Mellin signal

On Re s = 2 the second scale derivative of x^s has modulus |s(s−1)|,
independent of x. Its integral yields a uniform chord error proportional
to the product of the distances from the two observation scales.
-/

noncomputable section
open Set Filter MeasureTheory Complex
namespace GaloisForLFunctions.FamilyContinuationTheory

private theorem mode_chord {s : ℂ} (hs : s.re=2) {a h q : ℝ}
    (ha : 0 < a) (hh : 0 ≤ h) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ‖((a+q*h:ℝ):ℂ)^s - (1-q:ℝ) • (a:ℂ)^s - q • ((a+h:ℝ):ℂ)^s‖ ≤
      (2*q*(1-q)*h^2)*(‖s‖*‖s-1‖) := by
  let f (t : ℝ) := (t:ℂ)^s
  let v (t : ℝ) := s*(t:ℂ)^(s-1)
  let w (t : ℝ) := s*((s-1)*(t:ℂ)^(s-1-1))
  let S := Icc a (a+h)
  let x := a+q*h
  let B := ‖s‖*‖s-1‖
  have xS : x ∈ S := ⟨le_add_of_nonneg_right (mul_nonneg hq hh),
    by show a + q*h ≤ a + h; linarith [mul_le_of_le_one_left hh hq1]⟩
  have h0S : a ∈ S := ⟨le_rfl,le_add_of_nonneg_right hh⟩
  have h1S : a+h ∈ S := ⟨h0S.2,le_rfl⟩
  have b0 : 0 ≤ B := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have dw (t : ℝ) (ht : t ∈ S) : HasDerivAt v (w t) t :=
    (_root_.RHTower.hasDerivAt_ofReal_cpow_all (ha.trans_le ht.1).ne' (s-1)).const_mul s
  have bw (t : ℝ) (ht : t ∈ S) : ‖w t‖ ≤ B := by
    dsimp only [w,B]
    rw [norm_mul,norm_mul,norm_cpow_eq_rpow_re_of_pos (ha.trans_le ht.1)]
    simp only [sub_re,one_re,hs,show (2:ℝ)-1-1=0 by norm_num,Real.rpow_zero,mul_one,le_refl]
  have dh (t : ℝ) (ht : t ∈ S) : ‖v t-v x‖ ≤ B*h := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (dw t ht).hasDerivWithinAt) bw (convex_Icc ..) xS ht
    apply h.trans (mul_le_mul_of_nonneg_left _ b0)
    rw [Real.norm_eq_abs,abs_le]
    exact ⟨by linarith only [ht.1,xS.2],by linarith only [xS.1,ht.2]⟩
  let g := fun t : ℝ => f t-(t:ℂ)*v x
  have dg (t : ℝ) (ht : t ∈ S) : HasDerivAt g (v t-v x) t := by
    have hi : HasDerivAt (fun y : ℝ => (y:ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
    have h1 := (_root_.RHTower.hasDerivAt_ofReal_cpow_all
      (ha.trans_le ht.1).ne' s).sub (hi.mul_const (v x))
    rw [one_mul] at h1
    exact h1
  have residual (t : ℝ) (ht : t ∈ S) : ‖g x-g t‖ ≤ B*h*|x-t| :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (dg t ht).hasDerivWithinAt) dh (convex_Icc ..) ht xS
  have hleft := residual _ h0S
  have hright := residual _ h1S
  rw [abs_of_nonneg (sub_nonneg.mpr xS.1)] at hleft
  rw [abs_of_nonpos (sub_nonpos.mpr xS.2)] at hright
  have identity : f x-(1-q:ℝ) • f a-q • f (a+h) =
      (1-q:ℝ) • (g x-g a)+q • (g x-g (a+h)) := by
    dsimp only [g,x]
    simp only [Complex.real_smul,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one]
    ring
  change ‖f x-(1-q:ℝ) • f a-q • f (a+h)‖ ≤ _
  rw [identity]
  apply (norm_add_le ..).trans
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hq1),abs_of_nonneg hq]
  exact (add_le_add (mul_le_mul_of_nonneg_left hleft (sub_nonneg.mpr hq1))
    (mul_le_mul_of_nonneg_left hright hq)).trans_eq (by dsimp only [x,B]; ring)

/-- A finite second moment on the inversion line bounds the error of linear
interpolation between any two positive scales, with no dependence on their
distance from the origin. -/
theorem mellin_signal_chord_bound {G : ℂ → ℂ}
    (hg : Continuous fun y => G (linePoint y))
    (hi : Integrable fun y => (1+‖linePoint y‖*‖linePoint y-1‖)*‖G (linePoint y)‖) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {a h q : ℝ}, 0 < a → 0 ≤ h → 0 ≤ q → q ≤ 1 →
      ‖signal G 2 (a+q*h) - (1-q:ℝ) • signal G 2 a - q • signal G 2 (a+h)‖ ≤
        B*q*(1-q)*h^2 := by
  let μ (y : ℝ) := (1+‖linePoint y‖*‖linePoint y-1‖)*‖G (linePoint y)‖
  let c := 1/(2*Real.pi)
  have c0 : 0 ≤ c := by dsimp [c]; positivity
  have μ0 (y : ℝ) : 0 ≤ μ y := by dsimp [μ]; positivity
  have gi : Integrable fun y => G (linePoint y) :=
    hi.mono' hg.aestronglyMeasurable (.of_forall fun y => le_mul_of_one_le_left (norm_nonneg _)
      (le_add_of_nonneg_right (mul_nonneg (norm_nonneg _) (norm_nonneg _))))
  let F (x y : ℝ) := (x:ℂ)^(linePoint y)*G (linePoint y)
  have Fi {x : ℝ} (hx : 0 < x) : Integrable (F x) := by
    have cont := (continuous_linePoint.const_cpow (Or.inl (ofReal_ne_zero.mpr hx.ne'))).mul hg
    apply (gi.norm.const_mul (x^2)).mono' cont.aestronglyMeasurable
    apply Eventually.of_forall
    intro y
    show ‖(x:ℂ)^(linePoint y) * G (linePoint y)‖ ≤ _
    rw [norm_mul,norm_cpow_eq_rpow_re_of_pos hx,linePoint_re,Real.rpow_two]
  have read (x : ℝ) : signal G 2 x=c • ∫ y, F x y := by simp only [signal_two_eq_integral,F,smul_eq_mul,c]
  refine ⟨2*c*(∫ y, μ y),mul_nonneg (by positivity) (integral_nonneg μ0),fun {a h q} ha hh hq hq1 => ?_⟩
  let x := a+q*h
  let E := fun y => F x y-(1-q:ℝ) • F a y-q • F (a+h) y
  have sc : 0 ≤ 2*q*(1-q)*h^2 := by have := sub_nonneg.mpr hq1; positivity
  have bound (y : ℝ) : ‖E y‖ ≤ (2*q*(1-q)*h^2)*μ y := by
    let s := linePoint y
    have eq : E y = ((x:ℂ)^s-(1-q:ℝ) • (a:ℂ)^s-q • ((a+h:ℝ):ℂ)^s)*G s := by
      dsimp only [E,F,s]; simp only [Complex.real_smul]; ring
    rw [eq,norm_mul]
    have pt := mul_le_mul_of_nonneg_right (mode_chord (linePoint_re y) ha hh hq hq1) (norm_nonneg (G s))
    apply pt.trans
    dsimp only [μ]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left zero_le_one) (norm_nonneg _)) sc
  have total := norm_integral_le_of_norm_le (hi.const_mul (2*q*(1-q)*h^2)) (Eventually.of_forall bound)
  rw [integral_const_mul] at total
  have hx : 0 < x := add_pos_of_pos_of_nonneg ha (mul_nonneg hq hh)
  have he : (∫ y, E y) = (∫ y, F x y)-(1-q:ℝ) • (∫ y, F a y)-q • (∫ y, F (a+h) y) := by
    have i3 : Integrable (fun y => (1-q:ℝ) • F a y) := (Fi ha).smul (1-q:ℝ)
    have i1 : Integrable (fun y => F x y - (1-q:ℝ) • F a y) := (Fi hx).sub i3
    have i2 : Integrable (fun y => q • F (a+h) y) := (Fi (add_pos_of_pos_of_nonneg ha hh)).smul q
    rw [show (∫ y, E y) = ∫ y, ((F x y - (1-q:ℝ) • F a y) - q • F (a+h) y) from rfl,
      integral_sub i1 i2,integral_sub (Fi hx) i3,integral_smul,integral_smul]
  rw [read,read,read,smul_comm (1-q) c,smul_comm q c,←smul_sub,←smul_sub,←he,norm_smul,Real.norm_eq_abs,abs_of_nonneg c0]
  exact (mul_le_mul_of_nonneg_left total c0).trans_eq (by ring)

#print axioms mellin_signal_chord_bound
end GaloisForLFunctions.FamilyContinuationTheory
