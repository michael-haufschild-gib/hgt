import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCommonSourceGreen
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeCharacteristicContact

/-! Angular Laplacian iterates of the original native mean and their complete spin-two primitive. -/
namespace RHTower.D4BMNativeSpinTwoPrimitive
open D4BMNativeCircle D4BMNativeResponse D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

private abbrev Point := Fin 3 → ℝ
private abbrev Field := Point → ℂ
private def D (i : Fin 3) (f : Field) (p : Point) : ℂ :=
  fderiv ℝ f p (Pi.single i 1)

@[fun_prop] private theorem D_smooth {f : Field} {p : Point}
    (hf : ContDiffAt ℝ ∞ f p) (i : Fin 3) : ContDiffAt ℝ ∞ (D i f) p :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

private theorem D_hasFDerivAt {f : Field} {p : Point}
    (hf : ContDiffAt ℝ 2 f p) (i : Fin 3) :
    HasFDerivAt (D i f) ((fderiv ℝ (fderiv ℝ f) p).flip (Pi.single i 1)) p := by
  have hd := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  simpa [D] using! hd.clm_apply (hasFDerivAt_const (Pi.single i 1) p)

private theorem D_commute {f : Field} {p : Point}
    (hf : ContDiffAt ℝ 2 f p) (i j : Fin 3) : D i (D j f) p = D j (D i f) p := by
  change fderiv ℝ (D j f) p (Pi.single i 1) = fderiv ℝ (D i f) p (Pi.single j 1)
  rw [(D_hasFDerivAt hf j).fderiv, (D_hasFDerivAt hf i).fderiv]
  exact (hf.isSymmSndFDerivAt (by simp)).eq _ _

private theorem D_eventually {f g : Field} {p : Point} (h : f =ᶠ[𝓝 p] g) (i : Fin 3) :
    D i f p = D i g p := by
  unfold D
  rw [h.fderiv_eq]

private theorem D_third {f : Field} {p : Point}
    (hf : ContDiffAt ℝ ∞ f p) (i j : Fin 3) :
    D i (D j (D j f)) p = D j (D j (D i f)) p := by
  rw [D_commute ((D_smooth hf j).of_le (by exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) i j]
  apply D_eventually
  filter_upwards [(hf.of_le (show (2 : WithTop ℕ∞) ≤ ∞ by exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eventually (by simp)] with z hz
  exact D_commute hz i j

private theorem D_add {f g : Field} {p : Point}
    (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p) (i : Fin 3) :
    D i (fun z => f z+g z) p = D i f p+D i g p := by
  simp only [D, fderiv_fun_add (hf.differentiableAt (by simp)) (hg.differentiableAt (by simp)),
    add_apply]

private theorem D_sub {f g : Field} {p : Point}
    (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p) (i : Fin 3) :
    D i (fun z => f z-g z) p = D i f p-D i g p := by
  simp only [D, fderiv_fun_sub (hf.differentiableAt (by simp)) (hg.differentiableAt (by simp)),
    sub_apply]

private theorem D_mul {f g : Field} {p : Point}
    (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p) (i : Fin 3) :
    D i (fun z => f z*g z) p = D i f p*g p+f p*D i g p := by
  simp only [D, fderiv_fun_mul (hf.differentiableAt (by simp)) (hg.differentiableAt (by simp)),
    add_apply, smul_apply, smul_eq_mul]
  ring

private def E (a : ℂ) (p : Point) : ℂ := Complex.exp (a*(p 2:ℂ))

@[fun_prop] private theorem E_smooth (a : ℂ) (p : Point) : ContDiffAt ℝ ∞ (E a) p := by
  unfold E
  apply ContDiffAt.cexp
  apply ContDiffAt.mul contDiffAt_const
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp p (contDiff_apply ℝ ℝ (2:Fin 3)).contDiffAt

private theorem E_mul (a b : ℂ) (p : Point) : E a p*E b p=E (a+b) p := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  ring

private theorem D_E (a : ℂ) (i : Fin 3) (p : Point) :
    D i (E a) p=if i=2 then a*E a p else 0 := by
  have hc := (Complex.ofRealCLM.hasFDerivAt).comp p (hasFDerivAt_apply (𝕜 := ℝ) 2 p)
  have he := (hc.const_mul a).cexp
  have he' : HasFDerivAt (E a)
      (E a p • a • Complex.ofRealCLM.comp (ContinuousLinearMap.proj 2)) p := by
    simpa only [E, Function.comp_def, Complex.ofRealCLM_apply] using! he
  change fderiv ℝ (E a) p (Pi.single i 1) = _
  rw [he'.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    Complex.ofRealCLM_apply, smul_eq_mul]
  fin_cases i <;> simp
  ring

private def L (f : Field) (p : Point) : ℂ :=
  E 2 p*D 1 (D 1 f) p+D 2 (D 2 f) p-D 2 f p

@[fun_prop] private theorem L_smooth {f : Field} {p : Point} (hf : ContDiffAt ℝ ∞ f p) :
    ContDiffAt ℝ ∞ (L f) p :=
  (((E_smooth 2 p).mul (D_smooth (D_smooth hf 1) 1)).add
    (D_smooth (D_smooth hf 2) 2)).sub (D_smooth hf 2)

private theorem D_L {f : Field} {p : Point} (hf : ContDiffAt ℝ ∞ f p) :
    D 0 (L f) p=L (D 0 f) p := by
  unfold L
  rw [D_sub (((E_smooth 2 p).mul (D_smooth (D_smooth hf 1) 1)).add
        (D_smooth (D_smooth hf 2) 2)) (D_smooth hf 2),
    D_add ((E_smooth 2 p).mul (D_smooth (D_smooth hf 1) 1))
        (D_smooth (D_smooth hf 2) 2),
    D_mul (E_smooth 2 p) (D_smooth (D_smooth hf 1) 1), D_E]
  simp only [show (0:Fin 3) ≠ 2 by decide, if_false, zero_mul, zero_add,
    D_commute (hf.of_le (by exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) 0 2]
  rw [D_third hf 0 1, D_third hf 0 2]


private theorem D_twice_add {f g : Field} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (i : Fin 3) (p : Point) :
    D i (D i (fun z => f z+g z)) p=D i (D i f) p+D i (D i g) p := by
  have he : D i (fun z => f z+g z)=fun z => D i f z+D i g z :=
    funext (fun z => D_add hf.contDiffAt hg.contDiffAt i)
  rw [he,D_add (D_smooth hf.contDiffAt i) (D_smooth hg.contDiffAt i)]

private theorem L_add {f g : Field} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (p : Point) :
    L (fun z => f z+g z) p=L f p+L g p := by
  unfold L
  rw [D_twice_add hf hg,D_twice_add hf hg,D_add hf.contDiffAt hg.contDiffAt]
  ring

private def radialCoefficient (c : ℝ → ℂ) (p : Point) : ℂ := c (p 0)
private theorem radialCoefficient_smooth {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (radialCoefficient c) := hc.comp (contDiff_apply ℝ ℝ (0:Fin 3))
private theorem D_radialCoefficient {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c)
    (i : Fin 3) (hi : i ≠ 0) (p : Point) : D i (radialCoefficient c) p=0 := by
  have h := (hc.differentiable (by simp) (p 0)).hasFDerivAt.comp p
    (hasFDerivAt_apply (𝕜 := ℝ) 0 p)
  simp only [Function.comp_def] at h
  unfold D radialCoefficient
  rw [h.fderiv,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply]
  have hz : (Pi.single i (1:ℝ):Point) 0=0 := by simp [Ne.symm hi]
  rw [hz,map_zero]

private theorem L_radialCoefficient {f : Field} (hf : ContDiff ℝ ∞ f)
    {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) (p : Point) :
    L (fun z => c (z 0)*f z) p=c (p 0)*L f p := by
  have hC := radialCoefficient_smooth hc
  have he (i : Fin 3) (hi : i ≠ 0) :
      D i (fun z => c (z 0)*f z)=fun z => c (z 0)*D i f z := by
    funext z
    change D i (fun z => radialCoefficient c z*f z) z=_
    rw [D_mul hC.contDiffAt hf.contDiffAt,D_radialCoefficient hc i hi]
    simp only [zero_mul,zero_add,radialCoefficient]
  have he2 (i : Fin 3) (hi : i ≠ 0) :
      D i (D i (fun z => c (z 0)*f z)) p=c (p 0)*D i (D i f) p := by
    rw [he i hi]
    change D i (fun z => radialCoefficient c z*D i f z) p=_
    rw [D_mul hC.contDiffAt (D_smooth hf.contDiffAt i),D_radialCoefficient hc i hi]
    simp only [zero_mul,zero_add,radialCoefficient]
  unfold L
  rw [he2 1 (by decide),he2 2 (by decide),he 2 (by decide)]
  ring

private theorem D_L_twice {f : Field} (hf : ContDiff ℝ ∞ f) (p : Point) :
    D 0 (D 0 (L f)) p=L (D 0 (D 0 f)) p := by
  have he : D 0 (L f)=L (D 0 f) := funext (fun z => D_L hf.contDiffAt)
  rw [he,D_L (D_smooth hf.contDiffAt 0)]

private def radialEquation (f g : Field) : Prop := ∀ p,
  (Real.sinh (p 0):ℂ)^(2 : ℕ)*D 0 (D 0 f) p+
    ((Real.sinh (p 0):ℂ)*(Real.cosh (p 0):ℂ))*D 0 f p=
      (Real.sinh (p 0):ℂ)^(2 : ℕ)*g p

private theorem radialEquation_laplacian {f g : Field}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (h : radialEquation f g) :
    radialEquation (L f) (L g) := by
  have hf0 : ContDiff ℝ ∞ (D 0 f) := contDiff_iff_contDiffAt.mpr (fun _ => D_smooth hf.contDiffAt 0)
  have hf00 : ContDiff ℝ ∞ (D 0 (D 0 f)) :=
    contDiff_iff_contDiffAt.mpr (fun _ => D_smooth hf0.contDiffAt 0)
  have hS : ContDiff ℝ ∞ (fun d : ℝ => (Real.sinh d:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Real.contDiff_sinh
  have hC : ContDiff ℝ ∞ (fun d : ℝ => (Real.cosh d:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Real.contDiff_cosh
  have hs := hS.pow 2
  have hsc := hS.mul hC
  intro p
  have he := congrArg (fun F : Field => L F p) (funext h)
  have hA : ContDiff ℝ ∞ (fun z : Point => (Real.sinh (z 0):ℂ)^(2 : ℕ)*D 0 (D 0 f) z) := by
    simpa only [radialCoefficient] using! (radialCoefficient_smooth hs).mul hf00
  have hB : ContDiff ℝ ∞ (fun z : Point => ((Real.sinh (z 0):ℂ)*(Real.cosh (z 0):ℂ))*D 0 f z) := by
    simpa only [radialCoefficient] using! (radialCoefficient_smooth hsc).mul hf0
  rw [L_add hA hB,
    L_radialCoefficient hf00 hs,L_radialCoefficient hf0 hsc,L_radialCoefficient hg hs,
    ← D_L_twice hf p,← D_L hf.contDiffAt] at he
  exact he

private theorem slice_derivative {f : Field} (hf : ContDiff ℝ ∞ f)
    (i : Fin 3) (p : Point) (r : ℝ) :
    HasDerivAt (fun t => f (Function.update p i t)) (D i f (Function.update p i r)) r := by
  have hl : HasDerivAt (fun t => Function.update p i t) (Pi.single i (1:ℝ)) r := by
    apply hasDerivAt_pi.mpr
    intro j
    by_cases hj : j=i
    · subst j
      simpa using! hasDerivAt_id r
    · simpa [Function.update_of_ne hj,Pi.single_apply,hj] using! hasDerivAt_const r (p j)
  exact (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt r hl

private theorem D_slice {f : Field} (hf : ContDiff ℝ ∞ f) (i : Fin 3) (p : Point) :
    D i f p=deriv (fun t => f (Function.update p i t)) (p i) := by
  simpa only [Function.update_eq_self] using (slice_derivative hf i p (p i)).deriv.symm
private theorem D_twice_slice {f : Field} (hf : ContDiff ℝ ∞ f) (i : Fin 3) (p : Point) :
    D i (D i f) p=deriv (deriv (fun t => f (Function.update p i t))) (p i) := by
  have he : deriv (fun t => f (Function.update p i t))=
      fun t => D i f (Function.update p i t) := funext (fun t => (slice_derivative hf i p t).deriv)
  rw [he]
  exact D_slice (contDiff_iff_contDiffAt.mpr (fun _ => D_smooth hf.contDiffAt i)) i p

private def circle (q : XiZeroCopy) (p : Point) : ℂ := mean q (p 0) (p 1) (p 2)
private theorem circle_smooth (q : XiZeroCopy) : ContDiff ℝ ∞ (circle q) := by
  simpa only [circle,Function.comp_def] using!
    (nativeMean_joint_smooth q).comp
      (show ContDiff ℝ ∞ (fun p : Point => (p 0,p 1,p 2)) by fun_prop)
private theorem E_two (p : Point) : E 2 p=(Real.exp (p 2):ℂ)^(2 : ℕ) := by
  unfold E
  rw [show (2:ℂ)*(p 2:ℂ)=(p 2:ℂ)+(p 2:ℂ) by ring,Complex.exp_add,← Complex.ofReal_exp]
  ring

private theorem circle_radialEquation (q : XiZeroCopy) : radialEquation (circle q) (L (circle q)) := by
  intro p
  unfold L
  rw [D_twice_slice (circle_smooth q) 0 p,D_slice (circle_smooth q) 0 p,
    D_twice_slice (circle_smooth q) 1 p,D_twice_slice (circle_smooth q) 2 p,
    D_slice (circle_smooth q) 2 p,E_two]
  simpa only [circle,Function.update_self,Function.update_of_ne (by decide : (1:Fin 3) ≠ 0),
    Function.update_of_ne (by decide : (2:Fin 3) ≠ 0),
    Function.update_of_ne (by decide : (0:Fin 3) ≠ 1),
    Function.update_of_ne (by decide : (2:Fin 3) ≠ 1),
    Function.update_of_ne (by decide : (0:Fin 3) ≠ 2),
    Function.update_of_ne (by decide : (1:Fin 3) ≠ 2)] using! mean_darboux q (p 0) (p 1) (p 2)

/-- Finite iterates of the actual base Laplacian of the original full circle mean. -/
def laplaceMean (q : XiZeroCopy) : ℕ → (Fin 3 → ℝ) → ℂ
  | 0 => circle q
  | n+1 => L (laplaceMean q n)

private theorem laplaceMean_smooth (q : XiZeroCopy) (n : ℕ) : ContDiff ℝ ∞ (laplaceMean q n) := by
  induction n with
  | zero => exact circle_smooth q
  | succ n ih => exact contDiff_iff_contDiffAt.mpr (fun _ => L_smooth ih.contDiffAt)
private theorem laplaceMean_radialEquation (q : XiZeroCopy) (n : ℕ) :
    radialEquation (laplaceMean q n) (laplaceMean q (n+1)) := by
  induction n with
  | zero => exact circle_radialEquation q
  | succ n ih => exact radialEquation_laplacian (laplaceMean_smooth q n) (laplaceMean_smooth q (n+1)) ih

private theorem radialSlice_smooth (q : XiZeroCopy) (n : ℕ) (X k : ℝ) :
    ContDiff ℝ ∞ (fun d => laplaceMean q n ![d,X,k]) :=
  (laplaceMean_smooth q n).comp (by
    apply contDiff_iff_contDiffAt.mpr
    intro d
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i <;> dsimp <;> fun_prop)

/-- Every actual angular iterate satisfies the same source-faithful radial Darboux equation. -/
theorem laplaceMean_darboux (q : XiZeroCopy) (n : ℕ) (d X k : ℝ) :
    (Real.sinh d:ℂ)^(2 : ℕ)*deriv (deriv (fun r => laplaceMean q n ![r,X,k])) d+
      (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*deriv (fun r => laplaceMean q n ![r,X,k]) d=
      (Real.sinh d:ℂ)^(2 : ℕ)*laplaceMean q (n+1) ![d,X,k] := by
  have h := laplaceMean_radialEquation q n ![d,X,k]
  rw [D_twice_slice (laplaceMean_smooth q n) 0,D_slice (laplaceMean_smooth q n) 0] at h
  have he : (fun r => Function.update (![d,X,k]:Point) 0 r)=fun r => (![r,X,k]:Point) := by
    funext r
    ext i
    fin_cases i <;> simp
  simpa only [Matrix.cons_val_zero,he] using h


private theorem regular_equation {f g : ℝ → ℂ}
    (he : ∀ d, (Real.sinh d:ℂ)^(2 : ℕ)*deriv (deriv f) d+
      (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*deriv f d=(Real.sinh d:ℂ)^(2 : ℕ)*g d)
    {d : ℝ} (hd : d ≠ 0) :
    (Real.sinh d:ℂ)*deriv (deriv f) d+(Real.cosh d:ℂ)*deriv f d-(Real.sinh d:ℂ)*g d=0 := by
  have hn : (Real.sinh d:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by simpa using hd)
  apply mul_left_cancel₀ hn
  linear_combination he d

private theorem radial_first_zero {f g : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hg : Continuous g)
    (he : ∀ d, (Real.sinh d:ℂ)^(2 : ℕ)*deriv (deriv f) d+
      (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*deriv f d=(Real.sinh d:ℂ)^(2 : ℕ)*g d) : deriv f 0=0 := by
  have h1 := (contDiff_infty_iff_deriv.mp hf).2
  have h2 := (contDiff_infty_iff_deriv.mp h1).2
  have hS : Continuous (fun d : ℝ => (Real.sinh d:ℂ)) := by fun_prop
  have hC : Continuous (fun d : ℝ => (Real.cosh d:ℂ)) := by fun_prop
  have hc := ((hS.mul h2.continuous).add (hC.mul h1.continuous)).sub (hS.mul hg)
  have hz : (fun d => (Real.sinh d:ℂ)*deriv (deriv f) d+
      (Real.cosh d:ℂ)*deriv f d-(Real.sinh d:ℂ)*g d)=ᶠ[𝓝[≠] 0] fun _ => 0 := by
    filter_upwards [self_mem_nhdsWithin] with d hd
    exact regular_equation he hd
  have hh := tendsto_nhds_unique (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' hz.symm)
  simpa using hh

private theorem sinh_ratio_limit {f : ℝ → ℂ} {a : ℂ} (hf : HasDerivAt f a 0) (h0 : f 0=0) :
    Tendsto (fun d => f d/(Real.sinh d:ℂ)) (𝓝[≠] 0) (𝓝 a) := by
  have h1 : Tendsto (fun d : ℝ => f d/(d:ℂ)) (𝓝[≠] 0) (𝓝 a) := by
    simpa only [zero_add,h0,sub_zero,Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv,mul_comm]
      using hf.tendsto_slope_zero
  have h2 : Tendsto (fun d : ℝ => (Real.sinh d:ℂ)/(d:ℂ)) (𝓝[≠] 0) (𝓝 (1:ℂ)) := by
    have h := ((Real.hasDerivAt_sinh 0).ofReal_comp).tendsto_slope_zero
    simpa only [Real.cosh_zero,Real.sinh_zero,Complex.ofReal_one,Complex.ofReal_zero,
      zero_add,sub_zero,Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv,mul_comm] using h
  have h := h1.div h2 (by simp)
  simp only [div_one] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with d hd
  have hn : (d:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
  change (f d/(d:ℂ))/((Real.sinh d:ℂ)/(d:ℂ))=f d/(Real.sinh d:ℂ)
  field_simp [hn]

private theorem radial_second_zero {f g : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hg : Continuous g)
    (he : ∀ d, (Real.sinh d:ℂ)^(2 : ℕ)*deriv (deriv f) d+
      (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*deriv f d=(Real.sinh d:ℂ)^(2 : ℕ)*g d) :
    deriv (deriv f) 0=g 0/2 := by
  have hs1 := (contDiff_infty_iff_deriv.mp hf).2
  have hs2 := (contDiff_infty_iff_deriv.mp hs1).2
  have hm := ((hs1.contDiffAt (x := 0)).differentiableAt (by simp)).hasDerivAt
  have hr := sinh_ratio_limit hm (radial_first_zero hf hg he)
  have hC : Tendsto (fun d : ℝ => (Real.cosh d:ℂ)) (𝓝[≠] 0) (𝓝 (1:ℂ)) := by
    simpa using ((show Continuous (fun d : ℝ => (Real.cosh d:ℂ)) by fun_prop).continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto _ (𝓝[≠] (0:ℝ)) _)
  have hlim := (hs2.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).add (hC.mul hr)
  have hh : (fun d => deriv (deriv f) d+(Real.cosh d:ℂ)*(deriv f d/(Real.sinh d:ℂ)))=ᶠ[𝓝[≠] 0] g := by
    filter_upwards [self_mem_nhdsWithin] with d hd
    have hn : (Real.sinh d:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by simpa using hd)
    have h := regular_equation he hd
    apply mul_left_cancel₀ hn
    field_simp [hn]
    linear_combination h
  have hh' := tendsto_nhds_unique (hlim.congr' hh)
    (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  linear_combination hh'/2

/-- The original angular-Laplacian iterate in the physical invariant coordinate. -/
def argument (q : XiZeroCopy) (n : ℕ) (z X k : ℝ) : ℂ :=
  laplaceMean q n ![Real.arcosh z,X,k]
/-- Actual interior invariant derivative of each original angular iterate. -/
def first (q : XiZeroCopy) (n : ℕ) (z X k : ℝ) : ℂ :=
  deriv (fun d => laplaceMean q n ![d,X,k]) (Real.arcosh z)/(Real.sinh (Real.arcosh z):ℂ)
private def second (q : XiZeroCopy) (n : ℕ) (z X k : ℝ) : ℂ :=
  deriv (deriv (fun d => laplaceMean q n ![d,X,k])) (Real.arcosh z)/(Real.sinh (Real.arcosh z):ℂ)^(2 : ℕ)-
    (Real.cosh (Real.arcosh z):ℂ)*deriv (fun d => laplaceMean q n ![d,X,k]) (Real.arcosh z)/
      (Real.sinh (Real.arcosh z):ℂ)^(3 : ℕ)

private theorem argument_derivatives (q : XiZeroCopy) (n : ℕ) (X k : ℝ) {z : ℝ} (hz : 1 < z) :
    HasDerivAt (fun r => argument q n r X k) (first q n z X k) z ∧
    HasDerivAt (fun r => first q n r X k) (second q n z X k) z := by
  have hs := radialSlice_smooth q n X k
  have hs1 := (contDiff_infty_iff_deriv.mp hs).2
  have hm := ((hs.contDiffAt (x := Real.arcosh z)).differentiableAt (by simp)).hasDerivAt
  have hm1 := ((hs1.contDiffAt (x := Real.arcosh z)).differentiableAt (by simp)).hasDerivAt
  have hd : HasDerivAt Real.arcosh (1/Real.sinh (Real.arcosh z)) z := by
    simpa only [one_div,Real.sinh_arcosh hz.le] using Real.hasDerivAt_arcosh hz
  have hn : (Real.sinh (Real.arcosh z):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.mpr (Real.arcosh_pos hz)).ne'
  have hr := ((Real.hasDerivAt_sinh (Real.arcosh z)).comp z hd).ofReal_comp
  constructor
  · apply (hm.scomp z hd).congr_deriv
    simp only [first,Complex.real_smul,Complex.ofReal_div,Complex.ofReal_one]
    ring
  · apply ((hm1.scomp z hd).div hr hn).congr_deriv
    dsimp [second]
    simp only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_one]
    field_simp [hn]

private theorem argument_equation (q : XiZeroCopy) (n : ℕ) (X k : ℝ) {z : ℝ} (hz : 1 < z) :
    ((z:ℂ)^(2 : ℕ)-1)*second q n z X k+2*z*first q n z X k=argument q (n+1) z X k := by
  have hn : (Real.sinh (Real.arcosh z):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.mpr (Real.arcosh_pos hz)).ne'
  have he : (z:ℂ)^(2 : ℕ)-1=(Real.sinh (Real.arcosh z):ℂ)^(2 : ℕ) := by
    have h := Real.cosh_sq_sub_sinh_sq (Real.arcosh z)
    rw [Real.cosh_arcosh hz.le] at h
    exact_mod_cast (by linarith : z^(2 : ℕ)-1=Real.sinh (Real.arcosh z)^(2 : ℕ))
  have h := laplaceMean_darboux q n (Real.arcosh z) X k
  change _=(Real.sinh (Real.arcosh z):ℂ)^(2 : ℕ)*argument q (n+1) z X k at h
  rw [Real.cosh_arcosh hz.le] at h
  rw [he]
  dsimp [second,first]
  rw [Real.cosh_arcosh hz.le]
  linear_combination (norm := (field_simp [hn]; ring)) h/(Real.sinh (Real.arcosh z):ℂ)^(2 : ℕ)

private theorem argument_continuousOn (q : XiZeroCopy) (n : ℕ) (X k : ℝ) :
    ContinuousOn (fun z => argument q n z X k) (Ici 1) := by
  simpa only [argument,Function.comp_def] using!
    (radialSlice_smooth q n X k).continuous.comp_continuousOn Real.continuousOn_arcosh

/-- Every angular iterate has its original first characteristic derivative limit. -/
theorem first_tendsto_characteristic (q : XiZeroCopy) (n : ℕ) (X k : ℝ) :
    Tendsto (fun z => first q n z X k) (𝓝[>] 1)
      (𝓝 (laplaceMean q (n+1) ![0,X,k]/2)) := by
  have hf := radialSlice_smooth q n X k
  have hg := (radialSlice_smooth q (n+1) X k).continuous
  have he := fun d => laplaceMean_darboux q n d X k
  have hs1 := (contDiff_infty_iff_deriv.mp hf).2
  have hm := ((hs1.contDiffAt (x := 0)).differentiableAt (by simp)).hasDerivAt
  have hl := sinh_ratio_limit hm (radial_first_zero hf hg he)
  rw [radial_second_zero hf hg he] at hl
  have ha : Tendsto Real.arcosh (𝓝[>] 1) (𝓝 (0:ℝ)) := by
    simpa only [ContinuousWithinAt,Real.arcosh_zero] using
      ((Real.continuousOn_arcosh 1 (by simp)).mono Ioi_subset_Ici_self)
  have har : Tendsto Real.arcosh (𝓝[>] 1) (𝓝[≠] (0:ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within Real.arcosh ha
      (by filter_upwards [self_mem_nhdsWithin] with z hz
          exact (Real.arcosh_pos hz).ne')
  exact hl.comp har

/-- The derived characteristic value is the actual right derivative of the original angular iterate. -/
theorem argument_right_derivative (q : XiZeroCopy) (n : ℕ) (X k : ℝ) :
    HasDerivWithinAt (fun z => argument q n z X k)
      (laplaceMean q (n+1) ![0,X,k]/2) (Ici 1) 1 := by
  apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 1)
  · intro z hz
    exact (argument_derivatives q n X k hz).1.differentiableAt.differentiableWithinAt
  · exact ((argument_continuousOn q n X k) 1 (by simp)).mono Ioi_subset_Ici_self
  · exact self_mem_nhdsWithin
  · apply (first_tendsto_characteristic q n X k).congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (argument_derivatives q n X k hz).1.deriv.symm

/-- Full retained spin-two density of the literal native kernel. -/
def spinTwo (q : XiZeroCopy) (z X k : ℝ) : ℂ :=
  -argument q 2 z X k+2*argument q 1 z X k

private theorem spinTwo_continuousOn (q : XiZeroCopy) (X k : ℝ) :
    ContinuousOn (fun z => spinTwo q z X k) (Ici 1) :=
  (argument_continuousOn q 2 X k).neg.add
    (continuousOn_const.mul (argument_continuousOn q 1 X k))

/-- The actual spin-two characteristic derivative retains the next full angular Laplacian. -/
theorem spinTwo_right_derivative (q : XiZeroCopy) (X k : ℝ) :
    HasDerivWithinAt (fun z => spinTwo q z X k)
      ((-laplaceMean q 3 ![0,X,k]+2*laplaceMean q 2 ![0,X,k])/2) (Ici 1) 1 := by
  apply ((argument_right_derivative q 2 X k).neg.add
    ((argument_right_derivative q 1 X k).const_mul 2)).congr_deriv
  ring

/-- This same contact is the original interior spin-two derivative limit. -/
theorem spinTwo_derivative_tendsto_characteristic (q : XiZeroCopy) (X k : ℝ) :
    Tendsto (deriv (fun z => spinTwo q z X k)) (𝓝[>] 1)
      (𝓝 ((-laplaceMean q 3 ![0,X,k]+2*laplaceMean q 2 ![0,X,k])/2)) := by
  have h := (first_tendsto_characteristic q 2 X k).neg.add
    ((first_tendsto_characteristic q 1 X k).const_mul 2)
  have he : -laplaceMean q 3 ![0,X,k]/2+2*(laplaceMean q 2 ![0,X,k]/2)=
      (-laplaceMean q 3 ![0,X,k]+2*laplaceMean q 2 ![0,X,k])/2 := by ring
  simp only [neg_div] at he
  rw [he] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact ((argument_derivatives q 2 X k hz).1.neg.add
    ((argument_derivatives q 1 X k hz).1.const_mul 2)).deriv.symm

/-- Double primitive with both original characteristic jets retained. -/
def primitive (q : XiZeroCopy) (X k z : ℝ) : ℂ :=
  ((z:ℂ)^(2 : ℕ)-1)*(argument q 1 z X k-2*z*first q 0 z X k)
/-- First primitive jet in the original invariant coordinate. -/
def primitiveFirst (q : XiZeroCopy) (X k z : ℝ) : ℂ :=
  ((z:ℂ)^(2 : ℕ)-1)*(first q 1 z X k-2*first q 0 z X k)

/-- The full-source primitive has the actual retained spin-two second derivative. -/
theorem primitive_derivatives (q : XiZeroCopy) (X k : ℝ) {z : ℝ} (hz : 1 < z) :
    HasDerivAt (primitive q X k) (primitiveFirst q X k z) z ∧
    HasDerivAt (primitiveFirst q X k) (-spinTwo q z X k) z := by
  obtain ⟨h0,h00⟩ := argument_derivatives q 0 X k hz
  obtain ⟨h1,h11⟩ := argument_derivatives q 1 X k hz
  have hx := (hasDerivAt_id z).ofReal_comp
  have hp := (hx.pow 2).sub_const (1:ℂ)
  have he0 := argument_equation q 0 X k hz
  have he1 := argument_equation q 1 X k hz
  constructor
  · apply (hp.mul (h1.sub (((hx.const_mul (2:ℂ)).mul h00)))).congr_deriv
    dsimp [primitiveFirst]
    linear_combination -2*(z:ℂ)*he0
  · apply (hp.mul (h11.sub (h00.const_mul 2))).congr_deriv
    dsimp [spinTwo]
    linear_combination he1-2*he0

/-- The primitive is the original second invariant derivative with a double zero. -/
theorem primitive_eq_weighted_second (q : XiZeroCopy) (X k : ℝ) {z : ℝ} (hz : 1 < z) :
    primitive q X k z=((z:ℂ)^(2 : ℕ)-1)^(2 : ℕ)*
      deriv (deriv (fun r => argument q 0 r X k)) z := by
  have he : deriv (fun r => argument q 0 r X k)=ᶠ[𝓝 z]
      fun r => first q 0 r X k := by
    filter_upwards [Ioi_mem_nhds hz] with r hr
    exact (argument_derivatives q 0 X k hr).1.deriv
  rw [he.deriv_eq,(argument_derivatives q 0 X k hz).2.deriv]
  dsimp [primitive]
  linear_combination -((z:ℂ)^(2 : ℕ)-1)*(argument_equation q 0 X k hz)

/-- Both displayed primitive jets vanish at the original characteristic. -/
theorem primitive_characteristic (q : XiZeroCopy) (X k : ℝ) :
    primitive q X k 1=0 ∧ primitiveFirst q X k 1=0 := by
  simp [primitive,primitiveFirst]

/-- Both actual interior primitive jets tend to zero at the characteristic. -/
theorem primitive_tendsto_characteristic (q : XiZeroCopy) (X k : ℝ) :
    Tendsto (primitive q X k) (𝓝[>] 1) (𝓝 0) ∧
    Tendsto (primitiveFirst q X k) (𝓝[>] 1) (𝓝 0) := by
  have hx : Tendsto (fun r : ℝ => (r:ℂ)) (𝓝[>] 1) (𝓝 (1:ℂ)) := by
    simpa using (Complex.continuous_ofReal.continuousAt (x := (1:ℝ))).tendsto.mono_left
      (show 𝓝[>] (1:ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  have hp : Tendsto (fun r : ℝ => (r:ℂ)^(2 : ℕ)-1) (𝓝[>] 1) (𝓝 (0:ℂ)) := by
    simpa using (hx.pow 2).sub_const (1:ℂ)
  have ha := ((argument_continuousOn q 1 X k) 1 (by simp)).mono Ioi_subset_Ici_self
  have h0 := first_tendsto_characteristic q 0 X k
  have h1 := first_tendsto_characteristic q 1 X k
  constructor
  · simpa only [primitive,zero_mul] using! hp.mul (ha.tendsto.sub ((hx.const_mul 2).mul h0))
  · simpa only [primitiveFirst,zero_mul] using! hp.mul (h1.sub (h0.const_mul 2))

/-- Exact original-source first primitive integral, including its characteristic endpoint. -/
theorem primitiveFirst_integral (q : XiZeroCopy) (X k : ℝ) (z : Ici (1:ℝ)) :
    primitiveFirst q X k z=-∫ r in (1:ℝ)..z.val, spinTwo q r X k := by
  rcases eq_or_lt_of_le (show (1:ℝ) ≤ z.val from z.property) with h0 | hz
  · simp [← h0,(primitive_characteristic q X k).2]
  have hi : IntervalIntegrable (fun r => spinTwo q r X k) volume 1 z.val :=
    ((spinTwo_continuousOn q X k).mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hz.le
  have hr := (primitive_derivatives q X k hz).2.continuousAt.tendsto.mono_left
    (show 𝓝[<] z.val ≤ 𝓝 z.val from nhdsWithin_le_nhds)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hz
    (fun r hr => (primitive_derivatives q X k hr.1).2) hi.neg
    (primitive_tendsto_characteristic q X k).2 hr
  simpa only [intervalIntegral.integral_neg,sub_zero] using he.symm

/-- The full spin-two kernel has an exact Volterra primitive with two proved zero jets. -/
theorem primitive_volterra (q : XiZeroCopy) (X k : ℝ) (z : Ici (1:ℝ)) :
    primitive q X k z=-∫ r in (1:ℝ)..z.val, ((z.val:ℂ)-(r:ℂ))*spinTwo q r X k := by
  rcases eq_or_lt_of_le (show (1:ℝ) ≤ z.val from z.property) with h0 | hz
  · simp [← h0,(primitive_characteristic q X k).1]
  let f : ℝ → ℂ := fun r => primitive q X k r+((z.val:ℂ)-(r:ℂ))*primitiveFirst q X k r
  have hd (r : ℝ) (hr : r ∈ Ioo (1:ℝ) z.val) :
      HasDerivAt f (-(((z.val:ℂ)-(r:ℂ))*spinTwo q r X k)) r := by
    obtain ⟨h1,h2⟩ := primitive_derivatives q X k hr.1
    apply (h1.add ((((hasDerivAt_id r).ofReal_comp).const_sub (z.val:ℂ)).mul h2)).congr_deriv
    simp only [id_eq,Complex.ofReal_one]
    ring
  have hc : ContinuousOn (fun r : ℝ => ((z.val:ℂ)-(r:ℂ))*spinTwo q r X k) (Ici 1) :=
    (by fun_prop : ContinuousOn (fun r : ℝ => (z.val:ℂ)-(r:ℂ)) (Ici 1)).mul
      (spinTwo_continuousOn q X k)
  have hi : IntervalIntegrable (fun r : ℝ => ((z.val:ℂ)-(r:ℂ))*spinTwo q r X k) volume 1 z.val :=
    (hc.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hz.le
  have hl : Tendsto f (𝓝[>] 1) (𝓝 0) := by
    obtain ⟨h1,h2⟩ := primitive_tendsto_characteristic q X k
    have hx := ((show Continuous (fun r : ℝ => (z.val:ℂ)-(r:ℂ)) by fun_prop).continuousAt
      (x := (1:ℝ))).tendsto.mono_left (show 𝓝[>] (1:ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
    simpa only [f,mul_zero,add_zero] using! h1.add (hx.mul h2)
  have hr : Tendsto f (𝓝[<] z.val) (𝓝 (primitive q X k z.val)) := by
    obtain ⟨h1,h2⟩ := primitive_derivatives q X k hz
    have h := (h1.add ((((hasDerivAt_id z.val).ofReal_comp).const_sub (z.val:ℂ)).mul h2)).continuousAt
    simpa only [f,Pi.add_apply,Pi.mul_apply,id_eq,sub_self,zero_mul,add_zero] using! h.tendsto.mono_left
      (show 𝓝[<] z.val ≤ 𝓝 z.val from nhdsWithin_le_nhds)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hz hd hi.neg hl hr
  simpa only [intervalIntegral.integral_neg,sub_zero] using he.symm

/-- The original primitive has a quadratic characteristic zero and its first jet a linear zero. -/
theorem primitive_characteristic_bounds (q : XiZeroCopy) (X k : ℝ) (R : Ici (1:ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : Icc (1:ℝ) R.val,
      ‖primitive q X k z‖ ≤ C*(z.val-1)^(2 : ℕ) ∧
      ‖primitiveFirst q X k z‖ ≤ C*(z.val-1) := by
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((spinTwo_continuousOn q X k).mono (show Icc (1:ℝ) R.val ⊆ Ici 1 from Icc_subset_Ici_self))
  let C := max B 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨C,hC,?_⟩
  intro z
  have hz : 1 ≤ z.val := z.property.1
  have hb (r : ℝ) (hr : r ∈ Set.uIoc (1:ℝ) z.val) : ‖spinTwo q r X k‖ ≤ C := by
    rw [uIoc_of_le hz] at hr
    exact (hB r ⟨hr.1.le,hr.2.trans z.property.2⟩).trans (le_max_left _ _)
  constructor
  · have hp := primitive_volterra q X k ⟨z.val,hz⟩
    change primitive q X k z.val=_ at hp
    rw [hp,norm_neg]
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (1:ℝ)) (b := z.val) (C := (z.val-1)*C) (f := fun r : ℝ => ((z.val:ℂ)-(r:ℂ))*spinTwo q r X k)
      (by
        intro r hr
        have hr' : r ∈ Ioc (1:ℝ) z.val := by simpa only [uIoc_of_le hz] using hr
        rw [norm_mul,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hr'.2)]
        exact mul_le_mul (by linarith [hr'.1]) (hb r hr) (norm_nonneg _) (sub_nonneg.mpr hz))
    rw [abs_of_nonneg (sub_nonneg.mpr hz)] at hi
    calc
      _ ≤ (z.val-1)*C*(z.val-1) := hi
      _ = C*(z.val-1)^(2 : ℕ) := by ring
  · have hp := primitiveFirst_integral q X k ⟨z.val,hz⟩
    change primitiveFirst q X k z.val=_ at hp
    rw [hp,norm_neg]
    simpa only [abs_of_nonneg (sub_nonneg.mpr hz)] using
      intervalIntegral.norm_integral_le_of_norm_le_const hb

private def freeze (x : ℝ) (p : Point) : Point := Function.update p 0 x
private def sourceSlice (f : Field) (x : ℝ) (p : Point) : ℂ := f (freeze x p)
private theorem freeze_smooth (x : ℝ) : ContDiff ℝ ∞ (freeze x) := by
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i=0
  · subst i; simpa [freeze] using (contDiff_const : ContDiff ℝ ∞ (fun _ : Point => x))
  · simpa [freeze,hi] using (contDiff_apply ℝ ℝ i)

private theorem D_sourceSlice {f : Field} (hf : ContDiff ℝ ∞ f)
    (x : ℝ) (p : Point) (i : Fin 3) (hi : i ≠ 0) :
    D i (sourceSlice f x) p=D i f (freeze x p) := by
  have hs : ContDiff ℝ ∞ (sourceSlice f x) := hf.comp (freeze_smooth x)
  rw [D_slice hs i p,D_slice hf i (freeze x p)]
  have he : (fun t => sourceSlice f x (Function.update p i t))=
      fun t => f (Function.update (freeze x p) i t) := by
    funext t
    unfold sourceSlice freeze
    rw [Function.update_comm hi]
  rw [he]
  simp [freeze,hi]

private theorem L_sourceSlice {f : Field} (hf : ContDiff ℝ ∞ f) (x : ℝ) (p : Point) :
    L (sourceSlice f x) p=L f (freeze x p) := by
  have hd (i : Fin 3) (hi : i ≠ 0) :
      D i (sourceSlice f x)=sourceSlice (D i f) x := by
    funext z
    exact D_sourceSlice hf x z i hi
  unfold L
  rw [hd 1 (by decide),hd 2 (by decide),
    D_sourceSlice (contDiff_iff_contDiffAt.mpr (fun _ => D_smooth hf.contDiffAt 1)) x p 1 (by decide),
    D_sourceSlice (contDiff_iff_contDiffAt.mpr (fun _ => D_smooth hf.contDiffAt 2)) x p 2 (by decide)]
  simp [E,freeze,sourceSlice]

/-- Identification with the original radius-frozen physical trace, valid on the characteristic. -/
theorem nativeSpinTwoTrace_eq (image : Bool) (q : XiZeroCopy) (h target : ℝ) (p : Fin 3 → ℝ) :
    D4BMCommonSourceGreen.nativeSpinTwoTrace image q h target p=
      spinTwo q (D4BMCausalKernel.invariant (h-target+p 0) target
        (if image then -p 0 else p 0)) (p 1) (p 2) := by
  let r := Real.arcosh (D4BMCausalKernel.invariant (h-target+p 0) target
    (if image then -p 0 else p 0))
  have he : sourceSlice (D4BMCommonSourceGreen.kernelField image q h target) (p 0)=sourceSlice (circle q) r := by
    funext z
    simp [sourceSlice,freeze,D4BMCommonSourceGreen.kernelField,nativeRiemannKernel,angularKernel,circle,r]
  have heL : L (sourceSlice (circle q) r)=sourceSlice (L (circle q)) r := by
    funext z
    exact L_sourceSlice (circle_smooth q) r z
  change -L (L (sourceSlice (D4BMCommonSourceGreen.kernelField image q h target) (p 0))) p+
    2*L (sourceSlice (D4BMCommonSourceGreen.kernelField image q h target) (p 0)) p=_
  have hs : ContDiff ℝ ∞ (L (circle q)) := laplaceMean_smooth q 1
  rw [he,heL,L_sourceSlice hs r p]
  have hp : freeze r p=![r,p 1,p 2] := by
    ext i
    fin_cases i <;> simp [freeze]
  change -laplaceMean q 2 (freeze r p)+2*laplaceMean q 1 (freeze r p)=_
  rw [hp]
  rfl

end
end RHTower.D4BMNativeSpinTwoPrimitive
