import GaloisForLFunctions.HTGeometry.DirectionalGagliardoFourier
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Fractional energy under the positive logarithmic chart

For every fixed compact positive interval and fractional order in `(0,1)`,
logarithmic pullback is bounded for the full nonnegative difference energy.
The constant is independent of the supported continuous function. For Schwartz
functions this gives a finite bound by physical L2 mass and Fourier energy.

The proof retains both Jacobians in an exact two-point substitution. Small
log shifts keep both nonzero difference points in an enlarged compact interval;
large shifts cost only translation-invariant L2 mass. Slice-wise application
also bounds axial fractional energy under the full planar log chart, including
the transverse Jacobian. Uniform weighted multipliers and Euler derivatives
are still needed for BAG's full moving Mellin-profile transfer.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform Topology ContDiff ENNReal
namespace GaloisForLFunctions.HTGeometry

private theorem lintegral_log_substitution (G : ℝ→ℝ≥0∞) :
    (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (x⁻¹)*G (-Real.log x))=∫⁻u : ℝ, G u := by
  have hd : ∀u∈(univ : Set ℝ), HasDerivWithinAt (fun t : ℝ => Real.exp (-t))
      (-Real.exp (-u)) univ u := by
    intro u _
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-u)*(-1)) u :=
      (Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)
    simpa only [mul_neg_one] using h1.hasDerivWithinAt
  have hinj : InjOn (fun u : ℝ => Real.exp (-u)) univ := by
    intro a _ b _ he
    simpa using Real.exp_injective he
  have himage : (fun u : ℝ => Real.exp (-u)) '' univ=Ioi (0 : ℝ) := by
    rw [image_univ]
    ext x
    constructor
    · rintro ⟨u,rfl⟩
      exact Real.exp_pos _
    · intro hx
      exact ⟨-Real.log x,by simp [Real.exp_log hx]⟩
  have hh := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ hd hinj
    (fun x : ℝ => ENNReal.ofReal (x⁻¹)*G (-Real.log x))
  rw [himage] at hh
  rw [hh,Measure.restrict_univ]
  apply lintegral_congr
  intro u
  simp only [Real.log_exp,neg_neg,abs_neg,abs_of_pos (Real.exp_pos _)]
  rw [←mul_assoc,←ENNReal.ofReal_mul (Real.exp_nonneg _),
    mul_inv_cancel₀ (Real.exp_pos _).ne',ENNReal.ofReal_one,one_mul]

private theorem lintegral_positive_shift_log (x : {r : ℝ // 0<r}) (G : ℝ→ℝ≥0∞) :
    (∫⁻ y in Ioo (0 : ℝ) x.1, ENNReal.ofReal (y⁻¹)*G (-Real.log (y/x.1)))=
      ∫⁻h in Ioi (0 : ℝ), G h := by
  have hd : ∀h∈Ioi (0 : ℝ), HasDerivWithinAt (fun t : ℝ => x.1*Real.exp (-t))
      (-(x.1*Real.exp (-h))) (Ioi (0 : ℝ)) h := by
    intro h _
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-h)*(-1)) h :=
      (Real.hasDerivAt_exp (-h)).comp h (hasDerivAt_neg h)
    simpa only [mul_neg_one,mul_neg,mul_one] using (h1.const_mul x.1).hasDerivWithinAt
  have hinj : InjOn (fun h : ℝ => x.1*Real.exp (-h)) (Ioi (0 : ℝ)) := by
    intro a _ b _ he
    have he' := mul_left_cancel₀ x.2.ne' he
    simpa using Real.exp_injective he'
  have himage : (fun h : ℝ => x.1*Real.exp (-h)) '' Ioi (0 : ℝ)=Ioo (0 : ℝ) x.1 := by
    ext y
    constructor
    · rintro ⟨h,hh,rfl⟩
      refine ⟨mul_pos x.2 (Real.exp_pos _),?_⟩
      have he : Real.exp (-h)<1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (show 0<h from hh))
      simpa only [mul_one] using mul_lt_mul_of_pos_left he x.2
    · intro hy
      have hp : 0<y/x.1 := div_pos hy.1 x.2
      have hl : y/x.1<1 := (div_lt_one x.2).mpr hy.2
      refine ⟨-Real.log (y/x.1),neg_pos.mpr (Real.log_neg hp hl),?_⟩
      change x.1*Real.exp (-(-Real.log (y/x.1)))=y
      rw [neg_neg,Real.exp_log hp]
      field_simp [x.2.ne']
  have hh := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hd hinj
    (fun y : ℝ => ENNReal.ofReal (y⁻¹)*G (-Real.log (y/x.1)))
  rw [himage] at hh
  rw [hh]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  have hp : 0<x.1*Real.exp (-h) := mul_pos x.2 (Real.exp_pos _)
  have he : x.1*Real.exp (-h)/x.1=Real.exp (-h) := by field_simp [x.2.ne']
  rw [he,Real.log_exp,neg_neg,abs_neg,abs_of_pos hp,←mul_assoc,
    ←ENNReal.ofReal_mul hp.le,mul_inv_cancel₀ hp.ne',ENNReal.ofReal_one,one_mul]

private theorem log_pair_substitution (G : ℝ→ℝ→ℝ→ℝ≥0∞) :
    (∫⁻ u : ℝ, ∫⁻ h in Ioi (0 : ℝ), G (Real.exp (-u)) (Real.exp (-(u+h))) h)=
      ∫⁻ x in Ioi (0 : ℝ), ∫⁻ y in Ioo (0 : ℝ) x,
        ENNReal.ofReal (x⁻¹)*(ENNReal.ofReal (y⁻¹)*G x y (-Real.log (y/x))) := by
  rw [←lintegral_log_substitution]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0<x := hx
  have hnode (h : ℝ) : Real.exp (-(-Real.log x+h))=x*Real.exp (-h) := by
    rw [show -(-Real.log x+h)=Real.log x+(-h) by ring,Real.exp_add,Real.exp_log hx0]
  simp only [neg_neg,Real.exp_log hx0,hnode]
  rw [←lintegral_positive_shift_log ⟨x,hx0⟩ (fun h : ℝ => G x (x*Real.exp (-h)) h)]
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  have he : x*Real.exp (Real.log (y/x))=y := by
    rw [Real.exp_log (div_pos hy.1 hx0)]
    field_simp [hx0.ne']
  rw [neg_neg,he]

private theorem log_pair_kernel_bound (s : {r : ℝ // r∈Ioo (0 : ℝ) 1})
    (a b : {r : ℝ // 0<r}) (x y : ℝ)
    (hx : x∈Icc a.1 b.1) (hy : y∈Icc a.1 b.1) (hyx : y<x) :
    (-Real.log (y/x))^(-(1+2*s.1))/(x*y) ≤
      (b.1^(1+2*s.1)/a.1^2)*(x-y)^(-(1+2*s.1)) := by
  have hx0 : 0<x := a.2.trans_le hx.1
  have hy0 : 0<y := a.2.trans_le hy.1
  have hsub : 0<x-y := sub_pos.mpr hyx
  have hlog : (x-y)/b.1 ≤ -Real.log (y/x) := by
    have hh := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
    have he : (x-y)/x=1-y/x := by field_simp
    exact (div_le_div_of_nonneg_left hsub.le hx0 hx.2).trans (by linarith only [hh,he])
  have hpow := Real.rpow_le_rpow_of_nonpos (div_pos hsub b.2) hlog
    (show -(1+2*s.1) ≤ 0 by linarith [s.2.1])
  have hxy : a.1^2 ≤ x*y := by
    simpa only [pow_two] using mul_le_mul hx.1 hy.1 a.2.le hx0.le
  calc (-Real.log (y/x))^(-(1+2*s.1))/(x*y)
      ≤ ((x-y)/b.1)^(-(1+2*s.1))/(x*y) :=
        div_le_div_of_nonneg_right hpow (mul_pos hx0 hy0).le
    _ ≤ ((x-y)/b.1)^(-(1+2*s.1))/a.1^2 :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg (div_pos hsub b.2).le _) (pow_pos a.2 2) hxy
    _ = _ := by
      rw [Real.div_rpow hsub.le b.2.le,Real.rpow_neg b.2.le,div_inv_eq_mul]
      ring

private theorem support_pair_compact (a b : {r : ℝ // 0<r}) (f : ℝ→ℂ)
    (hsupp : Function.support f⊆Icc a.1 b.1) (x y : ℝ)
    (hx : 0<x) (hy : 0<y) (hyx : y<x) (hshift : -Real.log (y/x) ≤ 1)
    (hne : f x-f y≠0) :
    x∈Icc (a.1/Real.exp 1) (Real.exp 1*b.1) ∧
      y∈Icc (a.1/Real.exp 1) (Real.exp 1*b.1) := by
  have he0 := Real.exp_pos (1 : ℝ)
  have he1 : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp (by norm_num)
  have hratio : x ≤ Real.exp 1*y := by
    have hh := Real.exp_le_exp.mpr hshift
    rw [Real.exp_neg,Real.exp_log (div_pos hy hx)] at hh
    have he : (y/x)⁻¹=x/y := by field_simp
    rw [he] at hh
    exact (div_le_iff₀ hy).mp hh
  have hmem : x∈Icc a.1 b.1 ∨ y∈Icc a.1 b.1 := by
    by_cases hfx : f x=0
    · right
      exact hsupp (show f y≠0 from fun hfy => hne (by rw [hfx,hfy,sub_self]))
    · exact Or.inl (hsupp hfx)
  have hlo : a.1/Real.exp 1 ≤ y := by
    apply (div_le_iff₀ he0).mpr
    rcases hmem with hmem | hmem
    · simpa only [mul_comm] using hmem.1.trans hratio
    · simpa only [mul_comm] using hmem.1.trans (le_mul_of_one_le_left hy.le he1)
  have hhi : x ≤ Real.exp 1*b.1 := by
    rcases hmem with hmem | hmem
    · exact hmem.2.trans (le_mul_of_one_le_left b.2.le he1)
    · exact hratio.trans (mul_le_mul_of_nonneg_left hmem.2 he0.le)
  exact ⟨⟨hlo.trans hyx.le,hhi⟩,⟨hlo,hyx.le.trans hhi⟩⟩

private theorem ordered_pair_energy (f : ℝ→ℂ) (hf : Continuous f) (s : ℝ) :
    (∫⁻ x : ℝ, ∫⁻ y in Iio x,
      ENNReal.ofReal (‖f x-f y‖^2*(x-y)^(-(1+2*s))))=
      ∫⁻ h in Ioi (0 : ℝ), ∫⁻ x : ℝ,
        ENNReal.ofReal (‖f x-f (x-h)‖^2*h^(-(1+2*s))) := by
  have hj (x : ℝ) : (∫⁻ y in Iio x,
      ENNReal.ofReal (‖f x-f y‖^2*(x-y)^(-(1+2*s))))=
      ∫⁻ h in Ioi (0 : ℝ),
        ENNReal.ofReal (‖f x-f (x-h)‖^2*h^(-(1+2*s))) := by
    have hd : ∀h∈Ioi (0 : ℝ), HasDerivWithinAt (fun t : ℝ => x-t) (-1) (Ioi 0) h := by
      intro h _
      simpa using! ((hasDerivAt_const h x).sub (hasDerivAt_id h)).hasDerivWithinAt
    have hinj : InjOn (fun h : ℝ => x-h) (Ioi 0) := by
      intro a _ b _ he
      linarith only [he]
    have himage : (fun h : ℝ => x-h) '' Ioi 0=Iio x := by
      ext y
      constructor
      · rintro ⟨h,hh,rfl⟩
        have hh0 : 0<h := hh
        change x-h<x
        linarith only [hh0]
      · intro hy
        exact ⟨x-y,(show 0<x-y from sub_pos.mpr hy),by ring⟩
    have hh := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hd hinj
      (fun y : ℝ => ENNReal.ofReal (‖f x-f y‖^2*(x-y)^(-(1+2*s))))
    rw [himage] at hh
    simpa only [abs_neg,abs_one,ENNReal.ofReal_one,one_mul,sub_sub_cancel] using hh
  simp_rw [hj]
  have hm : Measurable (fun z : ℝ×ℝ =>
      ENNReal.ofReal (‖f z.1-f (z.1-z.2)‖^2*z.2^(-(1+2*s)))) := by
    have hfm := hf.measurable
    fun_prop
  exact lintegral_lintegral_swap hm.aemeasurable

private theorem local_log_near_energy (s : {r : ℝ // r∈Ioo (0 : ℝ) 1})
    (a b : {r : ℝ // 0<r}) (f : ℝ→ℂ) (hf : Continuous f)
    (hsupp : Function.support f⊆Icc a.1 b.1) :
    (∫⁻ u : ℝ, ∫⁻ h in Ioi (0 : ℝ),
      if h ≤ 1 then ENNReal.ofReal
        (‖f (Real.exp (-u))-f (Real.exp (-(u+h)))‖^2*h^(-(1+2*s.1))) else 0) ≤
      ENNReal.ofReal ((Real.exp 1*b.1)^(1+2*s.1)/(a.1/Real.exp 1)^2)*
        ∫⁻ h in Ioi (0 : ℝ), ∫⁻ x : ℝ,
          ENNReal.ofReal (‖f x-f (x-h)‖^2*h^(-(1+2*s.1))) := by
  classical
  let A : {r : ℝ // 0<r} := ⟨a.1/Real.exp 1,div_pos a.2 (Real.exp_pos _)⟩
  let B : {r : ℝ // 0<r} := ⟨Real.exp 1*b.1,mul_pos (Real.exp_pos _) b.2⟩
  let C := B.1^(1+2*s.1)/A.1^2
  have hC : 0 ≤ C := div_nonneg (Real.rpow_pos_of_pos B.2 _).le (sq_nonneg _)
  rw [log_pair_substitution (fun x y h : ℝ =>
    if h ≤ 1 then ENNReal.ofReal (‖f x-f y‖^2*h^(-(1+2*s.1))) else 0)]
  have hp (x : ℝ) (hx : 0<x) (y : ℝ) (hy : y∈Ioo 0 x) :
      ENNReal.ofReal (x⁻¹)*(ENNReal.ofReal (y⁻¹)*
        (if -Real.log (y/x) ≤ 1 then
          ENNReal.ofReal (‖f x-f y‖^2*(-Real.log (y/x))^(-(1+2*s.1))) else 0)) ≤
        ENNReal.ofReal C*ENNReal.ofReal (‖f x-f y‖^2*(x-y)^(-(1+2*s.1))) := by
    by_cases hh : -Real.log (y/x) ≤ 1
    · rw [if_pos hh]
      by_cases he : f x-f y=0
      · simp [he]
      · obtain ⟨hxc,hyc⟩ := support_pair_compact a b f hsupp x y hx hy.1 hy.2 hh he
        have hb := log_pair_kernel_bound s A B x y hxc hyc hy.2
        rw [←ENNReal.ofReal_mul (inv_nonneg.mpr hy.1.le),
          ←ENNReal.ofReal_mul (inv_nonneg.mpr hx.le),←ENNReal.ofReal_mul hC]
        apply ENNReal.ofReal_le_ofReal
        calc x⁻¹*(y⁻¹*(‖f x-f y‖^2*(-Real.log (y/x))^(-(1+2*s.1))))
            = ‖f x-f y‖^2*((-Real.log (y/x))^(-(1+2*s.1))/(x*y)) := by ring
          _ ≤ ‖f x-f y‖^2*(C*(x-y)^(-(1+2*s.1))) :=
            mul_le_mul_of_nonneg_left hb (sq_nonneg _)
          _ = C*(‖f x-f y‖^2*(x-y)^(-(1+2*s.1))) := by ring
    · simp [hh]
  calc (∫⁻ x in Ioi (0 : ℝ), ∫⁻ y in Ioo (0 : ℝ) x,
        ENNReal.ofReal (x⁻¹)*(ENNReal.ofReal (y⁻¹)*
          (if -Real.log (y/x) ≤ 1 then
            ENNReal.ofReal (‖f x-f y‖^2*(-Real.log (y/x))^(-(1+2*s.1))) else 0)))
      ≤ ∫⁻ x in Ioi (0 : ℝ), ∫⁻ y in Ioo (0 : ℝ) x,
        ENNReal.ofReal C*ENNReal.ofReal (‖f x-f y‖^2*(x-y)^(-(1+2*s.1))) := by
          apply setLIntegral_mono' measurableSet_Ioi
          intro x hx
          exact setLIntegral_mono' measurableSet_Ioo (fun y hy => hp x hx y hy)
    _ ≤ ∫⁻ x : ℝ, ∫⁻ y in Iio x,
        ENNReal.ofReal C*ENNReal.ofReal (‖f x-f y‖^2*(x-y)^(-(1+2*s.1))) := by
          apply le_trans (lintegral_mono (fun x => lintegral_mono_set Ioo_subset_Iio_self))
          exact setLIntegral_le_lintegral _ _
    _ = _ := by
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [ordered_pair_energy f hf]

private theorem log_mass_bound (a b : {r : ℝ // 0<r}) (f : ℝ→ℂ)
    (hsupp : Function.support f⊆Icc a.1 b.1) :
    (∫⁻ u : ℝ, ENNReal.ofReal (‖f (Real.exp (-u))‖^2)) ≤
      ENNReal.ofReal (a.1⁻¹)*∫⁻ x : ℝ, ENNReal.ofReal (‖f x‖^2) := by
  rw [←lintegral_log_substitution]
  have hp (x : ℝ) (hx : 0<x) :
      ENNReal.ofReal (x⁻¹)*ENNReal.ofReal (‖f x‖^2) ≤
        ENNReal.ofReal (a.1⁻¹)*ENNReal.ofReal (‖f x‖^2) := by
    by_cases he : f x=0
    · simp [he]
    · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (inv_anti₀ a.2 (hsupp he).1)) _
  calc (∫⁻ x in Ioi (0 : ℝ),
        ENNReal.ofReal (x⁻¹)*ENNReal.ofReal (‖f (Real.exp (-(-Real.log x)))‖^2))
      ≤ ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (a.1⁻¹)*ENNReal.ofReal (‖f x‖^2) := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro x hx
        simpa only [neg_neg,Real.exp_log (show 0<x from hx)] using hp x hx
    _ ≤ ∫⁻ x : ℝ, ENNReal.ofReal (a.1⁻¹)*ENNReal.ofReal (‖f x‖^2) :=
        setLIntegral_le_lintegral _ _
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

private theorem translation_difference_mass (g : ℝ→ℂ) (hg : Continuous g) (h : ℝ) :
    (∫⁻ u : ℝ, ENNReal.ofReal (‖g u-g (u+h)‖^2)) ≤
      ENNReal.ofReal 4*∫⁻ u : ℝ, ENNReal.ofReal (‖g u‖^2) := by
  have hm : Measurable (fun u : ℝ => ENNReal.ofReal 2*ENNReal.ofReal (‖g u‖^2)) := by
    have hgm := hg.measurable
    fun_prop
  calc (∫⁻ u : ℝ, ENNReal.ofReal (‖g u-g (u+h)‖^2))
      ≤ ∫⁻ u : ℝ, ENNReal.ofReal 2*ENNReal.ofReal (‖g u‖^2)+
        ENNReal.ofReal 2*ENNReal.ofReal (‖g (u+h)‖^2) := by
          apply lintegral_mono
          intro u
          change ENNReal.ofReal (‖g u-g (u+h)‖^2) ≤
            ENNReal.ofReal 2*ENNReal.ofReal (‖g u‖^2)+
              ENNReal.ofReal 2*ENNReal.ofReal (‖g (u+h)‖^2)
          rw [←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ←ENNReal.ofReal_add (by positivity : 0 ≤ 2*‖g u‖^2) (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          have hh := pow_le_pow_left₀ (norm_nonneg (g u-g (u+h))) (norm_sub_le (g u) (g (u+h))) 2
          nlinarith [sq_nonneg (‖g u‖-‖g (u+h)‖)]
    _ = _ := by
      rw [lintegral_add_left hm]
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [lintegral_add_right_eq_self (fun u : ℝ => ENNReal.ofReal (‖g u‖^2)) h,←add_mul]
      norm_num

private theorem rpow_tail_lintegral (s : {r : ℝ // r∈Ioo (0 : ℝ) 1}) :
    (∫⁻ h in Ioi (1 : ℝ), ENNReal.ofReal (h^(-(1+2*s.1))))=
      ENNReal.ofReal ((2*s.1)⁻¹) := by
  have hp : -(1+2*s.1) < -1 := by linarith [s.2.1]
  have hi := integrableOn_Ioi_rpow_of_lt hp (by norm_num : (0 : ℝ)<1)
  rw [←ofReal_integral_eq_lintegral_ofReal hi (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    exact Real.rpow_nonneg (le_of_lt (zero_lt_one.trans hh)) _),
    integral_Ioi_rpow_of_lt hp (by norm_num : (0 : ℝ)<1),Real.one_rpow]
  congr 1
  rw [show -(1+2*s.1)+1=-(2*s.1) by ring]
  simp [one_div]

private theorem local_log_far_energy (s : {r : ℝ // r∈Ioo (0 : ℝ) 1})
    (a b : {r : ℝ // 0<r}) (f : ℝ→ℂ) (hf : Continuous f)
    (hsupp : Function.support f⊆Icc a.1 b.1) :
    (∫⁻ h in Ioi (1 : ℝ), ∫⁻ u : ℝ,
      ENNReal.ofReal (‖f (Real.exp (-u))-f (Real.exp (-(u+h)))‖^2*h^(-(1+2*s.1)))) ≤
      ENNReal.ofReal ((2*s.1)⁻¹)*(ENNReal.ofReal 4*ENNReal.ofReal (a.1⁻¹))*
        ∫⁻ x : ℝ, ENNReal.ofReal (‖f x‖^2) := by
  let g : ℝ→ℂ := fun u => f (Real.exp (-u))
  have hg : Continuous g := hf.comp (Real.continuous_exp.comp continuous_neg)
  have hp (h : ℝ) (hh : h∈Ioi (1 : ℝ)) :
      (∫⁻ u : ℝ, ENNReal.ofReal (‖g u-g (u+h)‖^2*h^(-(1+2*s.1)))) ≤
        ENNReal.ofReal (h^(-(1+2*s.1)))*
          (ENNReal.ofReal 4*(ENNReal.ofReal (a.1⁻¹)*∫⁻ x : ℝ, ENNReal.ofReal (‖f x‖^2))) := by
    have he (u : ℝ) : ENNReal.ofReal (‖g u-g (u+h)‖^2*h^(-(1+2*s.1)))=
        ENNReal.ofReal (h^(-(1+2*s.1)))*ENNReal.ofReal (‖g u-g (u+h)‖^2) := by
      rw [mul_comm,ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt (zero_lt_one.trans hh)) _)]
    simp_rw [he]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul_right ((translation_difference_mass g hg h).trans
      (mul_le_mul_right (log_mass_bound a b f hsupp) _)) _
  calc (∫⁻ h in Ioi (1 : ℝ), ∫⁻ u : ℝ,
        ENNReal.ofReal (‖g u-g (u+h)‖^2*h^(-(1+2*s.1))))
      ≤ ∫⁻ h in Ioi (1 : ℝ), ENNReal.ofReal (h^(-(1+2*s.1)))*
          (ENNReal.ofReal 4*(ENNReal.ofReal (a.1⁻¹)*∫⁻ x : ℝ, ENNReal.ofReal (‖f x‖^2))) :=
        setLIntegral_mono' measurableSet_Ioi hp
    _ = _ := by
      rw [lintegral_mul_const _ (by fun_prop),rpow_tail_lintegral]
      simp only [mul_assoc]

private theorem fractional_energy_split (g : ℝ→ℂ) (hg : Continuous g) (s : ℝ) :
    (∫⁻ h in Ioi (0 : ℝ), ∫⁻ u : ℝ,
      ENNReal.ofReal (‖g u-g (u+h)‖^2*h^(-(1+2*s))))=
      (∫⁻ u : ℝ, ∫⁻ h in Ioi (0 : ℝ),
        if h ≤ 1 then ENNReal.ofReal (‖g u-g (u+h)‖^2*h^(-(1+2*s))) else 0)+
      (∫⁻ h in Ioi (1 : ℝ), ∫⁻ u : ℝ,
        ENNReal.ofReal (‖g u-g (u+h)‖^2*h^(-(1+2*s)))) := by
  classical
  let E : ℝ→ℝ≥0∞ := fun h => ∫⁻ u : ℝ,
    ENNReal.ofReal (‖g u-g (u+h)‖^2*h^(-(1+2*s)))
  have hsplit := lintegral_add_compl (μ := volume.restrict (Ioi (0 : ℝ))) E
    (show MeasurableSet (Iic (1 : ℝ)) from measurableSet_Iic)
  rw [←lintegral_indicator measurableSet_Iic,compl_Iic,
    Measure.restrict_restrict_of_subset (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))] at hsplit
  have hnear : (∫⁻ h in Ioi (0 : ℝ), (Iic (1 : ℝ)).indicator E h)=
      ∫⁻ u : ℝ, ∫⁻ h in Ioi (0 : ℝ),
        if h ≤ 1 then ENNReal.ofReal (‖g u-g (u+h)‖^2*h^(-(1+2*s))) else 0 := by
    have he (h : ℝ) : (Iic (1 : ℝ)).indicator E h=
        ∫⁻ u : ℝ, if h ≤ 1 then
          ENNReal.ofReal (‖g u-g (u+h)‖^2*h^(-(1+2*s))) else 0 := by
      by_cases hh : h ≤ 1 <;> simp [Set.indicator,hh,E]
    simp_rw [he]
    have hm : Measurable (fun z : ℝ×ℝ =>
        if z.1 ≤ 1 then ENNReal.ofReal (‖g z.2-g (z.2+z.1)‖^2*z.1^(-(1+2*s))) else 0) := by
      have hgm := hg.measurable
      apply Measurable.ite (measurableSet_le measurable_fst measurable_const) <;> fun_prop
    exact lintegral_lintegral_swap hm.aemeasurable
  rw [hnear] at hsplit
  exact hsplit.symm

/-- Logarithmic pullback preserves fractional difference energy on every fixed
compact positive interval, with one constant for all supported continuous functions.
No integrability or energy bound is assumed. -/
theorem local_log_fractional_energy (s : {r : ℝ // r∈Ioo (0 : ℝ) 1})
    (a b : {r : ℝ // 0<r}) :
    ∃ C : ℝ, 0<C ∧ ∀f : {g : ℝ→ℂ // Continuous g ∧ Function.support g⊆Icc a.1 b.1},
      (∫⁻ h in Ioi (0 : ℝ), ∫⁻ u : ℝ,
        ENNReal.ofReal (‖f.1 (Real.exp (-u))-f.1 (Real.exp (-(u+h)))‖^2*h^(-(1+2*s.1)))) ≤
        ENNReal.ofReal C*((∫⁻ h in Ioi (0 : ℝ), ∫⁻ x : ℝ,
          ENNReal.ofReal (‖f.1 x-f.1 (x-h)‖^2*h^(-(1+2*s.1))))+
          ∫⁻ x : ℝ, ENNReal.ofReal (‖f.1 x‖^2)) := by
  let A := (Real.exp 1*b.1)^(1+2*s.1)/(a.1/Real.exp 1)^2
  let B := (2*s.1)⁻¹*4*a.1⁻¹
  have ha : 0 < a.1 := a.2
  have hbpos : 0 < b.1 := b.2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hs : 0 < s.1 := s.2.1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨A+B+1,by linarith,fun f => ?_⟩
  let g : ℝ→ℂ := fun u => f.1 (Real.exp (-u))
  have hg : Continuous g := f.2.1.comp (Real.continuous_exp.comp continuous_neg)
  rw [fractional_energy_split g hg]
  have hn := local_log_near_energy s a b f.1 f.2.1 f.2.2
  have ht := local_log_far_energy s a b f.1 f.2.1 f.2.2
  have hBe : ENNReal.ofReal ((2*s.1)⁻¹)*(ENNReal.ofReal 4*ENNReal.ofReal (a.1⁻¹))=
      ENNReal.ofReal B := by
    dsimp [B]
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (2*s.1)⁻¹*4),
      ENNReal.ofReal_mul (by positivity : 0 ≤ (2*s.1)⁻¹),mul_assoc]
  rw [hBe] at ht
  refine (add_le_add hn ht).trans ?_
  rw [mul_add]
  exact add_le_add
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal (show A ≤ A+B+1 by linarith)) _)
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal (show B ≤ A+B+1 by linarith)) _)

/-- In particular, the logarithmic fractional energy of every Schwartz function
supported in the fixed positive interval is finite, with a bound by its physical
L2 mass and weighted Fourier energy. -/
theorem local_log_fractional_schwartz (s : {r : ℝ // r∈Ioo (0 : ℝ) 1})
    (a b : {r : ℝ // 0<r}) :
    ∃ C : ℝ, 0<C ∧ ∀f : {g : SchwartzMap ℝ ℂ // Function.support g⊆Icc a.1 b.1},
      let L := ∫⁻ h in Ioi (0 : ℝ), ∫⁻ u : ℝ,
        ENNReal.ofReal (‖f.1 (Real.exp (-u))-f.1 (Real.exp (-(u+h)))‖^2*h^(-(1+2*s.1)))
      L < (∞ : ℝ≥0∞) ∧ L ≤ ENNReal.ofReal C*
        (ENNReal.ofReal (∫ξ : ℝ, |ξ|^(2*s.1)*‖(𝓕 f.1) ξ‖^2)+
          ENNReal.ofReal (∫x : ℝ, ‖f.1 x‖^2)) := by
  obtain ⟨A,hA,hAb⟩ := local_log_fractional_energy s a b
  obtain ⟨D,hD,hDb⟩ := directional_gagliardo_fourier (E := ℝ) s
  refine ⟨A*(D+1),mul_pos hA (by linarith),fun f => ?_⟩
  dsimp only
  have hb := hAb ⟨f.1, f.1.continuous, f.2⟩
  have he := (hDb f.1 (-1)).2
  have him : Integrable (fun x : ℝ => ‖f.1 x‖^2) :=
    (f.1.memLp 2).integrable_norm_pow (by norm_num : 2≠0)
  have hmass := ofReal_integral_eq_lintegral_ofReal him
    (Eventually.of_forall (fun x : ℝ => sq_nonneg ‖f.1 x‖))
  have he' : (∫⁻ h in Ioi (0 : ℝ), ∫⁻ x : ℝ,
      ENNReal.ofReal (‖f.1 x-f.1 (x-h)‖^2*h^(-(1+2*s.1))))=
      ENNReal.ofReal D*ENNReal.ofReal (∫ξ : ℝ, |ξ|^(2*s.1)*‖(𝓕 f.1) ξ‖^2) := by
    simpa only [smul_eq_mul,mul_neg_one,sub_eq_add_neg,Real.inner_apply,
      neg_one_mul,abs_neg] using he
  simp only [he',←hmass] at hb
  have hbound : (∫⁻ h in Ioi (0 : ℝ), ∫⁻ u : ℝ,
      ENNReal.ofReal (‖f.1 (Real.exp (-u))-f.1 (Real.exp (-(u+h)))‖^2*h^(-(1+2*s.1)))) ≤
      ENNReal.ofReal (A*(D+1))*
        (ENNReal.ofReal (∫ξ : ℝ, |ξ|^(2*s.1)*‖(𝓕 f.1) ξ‖^2)+
          ENNReal.ofReal (∫x : ℝ, ‖f.1 x‖^2)) := by
    refine hb.trans ?_
    rw [ENNReal.ofReal_mul hA.le,mul_assoc]
    apply mul_le_mul_right
    rw [mul_add]
    apply add_le_add
    · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith : D ≤ D+1)) _
    · calc ENNReal.ofReal (∫x : ℝ, ‖f.1 x‖^2)
          = 1*ENNReal.ofReal (∫x : ℝ, ‖f.1 x‖^2) := (one_mul _).symm
        _ ≤ _ := mul_le_mul_left (by
          simpa only [←ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show 1 ≤ D+1 by linarith)) _
  exact ⟨hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top,ENNReal.ofReal_lt_top⟩)),hbound⟩

private theorem log_supported_lintegral (a b : {r : ℝ // 0<r}) (F : ℝ→ℝ≥0∞)
    (hsupp : Function.support F⊆Icc a.1 b.1) :
    (∫⁻ v : ℝ, F (Real.exp (-v))) ≤ ENNReal.ofReal (a.1⁻¹)*∫⁻ y : ℝ, F y := by
  rw [←lintegral_log_substitution]
  calc (∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y⁻¹)*F (Real.exp (-(-Real.log y))))
      ≤ ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (a.1⁻¹)*F y := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro y hy
        rw [neg_neg,Real.exp_log (show 0<y from hy)]
        by_cases hF : F y=0
        · simp [hF]
        · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (inv_anti₀ a.2 (hsupp hF).1)) _
    _ ≤ ∫⁻ y : ℝ, ENNReal.ofReal (a.1⁻¹)*F y := setLIntegral_le_lintegral _ _
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The axial fractional estimate under the full two-coordinate logarithmic chart.
The same constant applies to the other axis by exchanging the two coordinates.
Both logarithmic Jacobians are paid; no slice-energy or integrability bound is assumed. -/
theorem local_log_fractional_planar (s : {r : ℝ // r∈Ioo (0 : ℝ) 1})
    (a b : {r : ℝ // 0<r}) :
    ∃ C : ℝ, 0<C ∧ ∀f : {g : ℝ×ℝ→ℂ // Continuous g ∧
        Function.support g⊆(Icc a.1 b.1)×ˢ(Icc a.1 b.1)},
      (∫⁻ v : ℝ, ∫⁻ h in Ioi (0 : ℝ), ∫⁻ u : ℝ,
        ENNReal.ofReal (‖f.1 (Real.exp (-u),Real.exp (-v))-
          f.1 (Real.exp (-(u+h)),Real.exp (-v))‖^2*h^(-(1+2*s.1)))) ≤
        ENNReal.ofReal C*∫⁻ y : ℝ,
          ((∫⁻ h in Ioi (0 : ℝ), ∫⁻ x : ℝ,
            ENNReal.ofReal (‖f.1 (x,y)-f.1 (x-h,y)‖^2*h^(-(1+2*s.1))))+
              ∫⁻ x : ℝ, ENNReal.ofReal (‖f.1 (x,y)‖^2)) := by
  obtain ⟨C,hC,hCb⟩ := local_log_fractional_energy s a b
  refine ⟨C/a.1,div_pos hC a.2,fun f => ?_⟩
  let F : ℝ→ℝ≥0∞ := fun y =>
    (∫⁻ h in Ioi (0 : ℝ), ∫⁻ x : ℝ,
      ENNReal.ofReal (‖f.1 (x,y)-f.1 (x-h,y)‖^2*h^(-(1+2*s.1))))+
        ∫⁻ x : ℝ, ENNReal.ofReal (‖f.1 (x,y)‖^2)
  have hfcont (y : ℝ) : Continuous (fun x : ℝ => f.1 (x,y)) :=
    f.2.1.comp (continuous_id.prodMk continuous_const)
  have hfsupp (y : ℝ) : Function.support (fun x : ℝ => f.1 (x,y))⊆Icc a.1 b.1 := by
    intro x hx
    exact (f.2.2 hx).1
  have hFsupp : Function.support F⊆Icc a.1 b.1 := by
    intro y hy
    by_contra hny
    have hfzero (x : ℝ) : f.1 (x,y)=0 := by
      by_contra hn
      exact hny (f.2.2 hn).2
    have hzero : F y=0 := by simp only [F,hfzero,sub_self,norm_zero,zero_pow (by norm_num : 2≠0),
      zero_mul,ENNReal.ofReal_zero,lintegral_zero,add_zero]
    exact hy hzero
  calc (∫⁻ v : ℝ, ∫⁻ h in Ioi (0 : ℝ), ∫⁻ u : ℝ,
        ENNReal.ofReal (‖f.1 (Real.exp (-u),Real.exp (-v))-
          f.1 (Real.exp (-(u+h)),Real.exp (-v))‖^2*h^(-(1+2*s.1))))
      ≤ ∫⁻ v : ℝ, ENNReal.ofReal C*F (Real.exp (-v)) := by
        apply lintegral_mono
        intro v
        exact hCb ⟨fun x => f.1 (x,Real.exp (-v)),hfcont _,hfsupp _⟩
    _ = ENNReal.ofReal C*∫⁻ v : ℝ, F (Real.exp (-v)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C*(ENNReal.ofReal (a.1⁻¹)*∫⁻ y : ℝ, F y) :=
      mul_le_mul_right (log_supported_lintegral a b F hFsupp) _
    _ = _ := by rw [div_eq_mul_inv,ENNReal.ofReal_mul hC.le,mul_assoc]

end GaloisForLFunctions.HTGeometry
