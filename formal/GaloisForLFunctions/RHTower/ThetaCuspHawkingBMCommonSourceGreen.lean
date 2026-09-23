import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCommonRadialSource
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeAngularGreen

/-! Full spatial Green transfer for the actual common BM source producer.

The radial and both angular currents retain the original measure. The public
application uses the literal theta seed and native causal kernel; all local
regularity is proved from the actual fields. Characteristic contacts and
infinite-domain limits are not discarded by this local identity.
-/

open Set Filter Topology
open scoped ContDiff
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
namespace RHTower.D4BMCommonSourceGreen
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

private def W (i : Fin 3) (f g : Field) (p : Point) : ℂ := D i f p*g p-f p*D i g p

private theorem D_W {f g : Field} {p : Point}
    (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p) (i : Fin 3) :
    D i (W i f g) p = D i (D i f) p*g p-f p*D i (D i g) p := by
  unfold W
  rw [D_sub ((D_smooth hf i).mul hg) (hf.mul (D_smooth hg i)), D_mul (D_smooth hf i) hg,
    D_mul hf (D_smooth hg i)]
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

private theorem angular_green {f g : Field} {p : Point}
    (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p) :
    D 1 (fun z => E 1 z*W 1 f g z) p+D 2 (fun z => E (-1) z*W 2 f g z) p=
      E (-1) p*(L f p*g p-f p*L g p) := by
  have hw (i : Fin 3) : ContDiffAt ℝ ∞ (W i f g) p :=
    ((D_smooth hf i).mul hg).sub (hf.mul (D_smooth hg i))
  rw [D_mul (E_smooth 1 p) (hw 1), D_mul (E_smooth (-1) p) (hw 2),
    D_E, D_E, D_W hf hg, D_W hf hg]
  have he : E (-1) p*E 2 p=E 1 p := by convert E_mul (-1) 2 p using 1; norm_num
  simp only [show (1:Fin 3) ≠ 2 by decide, if_false, if_true, zero_mul, zero_add]
  dsimp [L,W]
  linear_combination -(D 1 (D 1 f) p*g p-f p*D 1 (D 1 g) p)*he


private theorem D_const (c : ℂ) (i : Fin 3) (p : Point) : D i (fun _ => c) p=0 := by
  simp [D]

private def K (lam : ℂ) (f : Field) (p : Point) : ℂ :=
  (7*lam-2)/8*f p-(1/4:ℂ)*L f p

@[fun_prop] private theorem K_smooth (lam : ℂ) {f : Field} {p : Point}
    (hf : ContDiffAt ℝ ∞ f p) : ContDiffAt ℝ ∞ (K lam f) p :=
  (contDiffAt_const.mul hf).sub (contDiffAt_const.mul (L_smooth hf))

private theorem D_K (lam : ℂ) {f : Field} {p : Point}
    (hf : ContDiffAt ℝ ∞ f p) (i : Fin 3) :
    D i (K lam f) p=(7*lam-2)/8*D i f p-(1/4:ℂ)*D i (L f) p := by
  unfold K
  rw [D_sub (contDiffAt_const.mul hf) (contDiffAt_const.mul (L_smooth hf)),
    D_mul contDiffAt_const hf, D_mul contDiffAt_const (L_smooth hf), D_const, D_const]
  ring

private theorem K_D (lam : ℂ) {f : Field} {p : Point}
    (hf : ContDiffAt ℝ ∞ f p) : D 0 (K lam f) p=K lam (D 0 f) p := by
  rw [D_K lam hf,D_L hf]
  rfl

private def angularCurrent (c : Field) (i : Fin 3) (f g : Field) (p : Point) : ℂ :=
  c p*((if i=1 then E 1 p else E (-1) p)*W i f g p)

private theorem angular_current_green {f g c : Field} {p : Point}
    (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p)
    (hc : ContDiffAt ℝ ∞ c p) (hc1 : D 1 c p=0) (hc2 : D 2 c p=0) :
    D 1 (angularCurrent c 1 f g) p+D 2 (angularCurrent c 2 f g) p=
      c p*E (-1) p*(L f p*g p-f p*L g p) := by
  have hw (i : Fin 3) : ContDiffAt ℝ ∞ (W i f g) p :=
    ((D_smooth hf i).mul hg).sub (hf.mul (D_smooth hg i))
  have he1 : angularCurrent c 1 f g=fun z => c z*(E 1 z*W 1 f g z) := by
    funext z
    simp [angularCurrent]
  have he2 : angularCurrent c 2 f g=fun z => c z*(E (-1) z*W 2 f g z) := by
    funext z
    simp [angularCurrent]
  rw [he1,he2,D_mul hc ((E_smooth 1 p).mul (hw 1)),
    D_mul hc ((E_smooth (-1) p).mul (hw 2)), hc1,hc2]
  linear_combination c p*(angular_green hf hg)

private theorem general_green {f g A B S H : Field} {p : Point} (lam : ℂ)
    (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p)
    (hB : ContDiffAt ℝ ∞ B p) (hS : ContDiffAt ℝ ∞ S p) (hH : ContDiffAt ℝ ∞ H p)
    (hS0 : D 0 S p=H p)
    (hB1 : D 1 B p=0) (hB2 : D 2 B p=0)
    (hS1 : D 1 S p=0) (hS2 : D 2 S p=0)
    (hH1 : D 1 H p=0) (hH2 : D 2 H p=0) :
    E (-1) p*((A p*f p+B p*L f p+S p*D 0 (K lam f) p)*g p-
      f p*((A p-(7*lam-2)/8*H p)*g p+(B p+H p/4)*L g p-S p*D 0 (K lam g) p))=
    D 0 (fun z => S z*(E (-1) z*(K lam f z*g z))) p+
      (D 1 (angularCurrent (fun z => B z+H z/4) 1 f g) p+
       D 2 (angularCurrent (fun z => B z+H z/4) 2 f g) p)+
      (D 1 (angularCurrent (fun z => S z/4) 1 f (D 0 g)) p+
       D 2 (angularCurrent (fun z => S z/4) 2 f (D 0 g)) p) := by
  have hα : ContDiffAt ℝ ∞ (fun z => B z+H z/4) p := hB.add (hH.div_const 4)
  have hβ : ContDiffAt ℝ ∞ (fun z => S z/4) p := hS.div_const 4
  have dα (i : Fin 3) (hBi : D i B p=0) (hHi : D i H p=0) :
      D i (fun z => B z+H z/4) p=0 := by
    have he : (fun z => B z+H z/4)=(fun z => B z+H z*(1/4:ℂ)) := by funext z; ring
    rw [he,D_add hB (hH.mul contDiffAt_const), D_mul hH contDiffAt_const,D_const,hBi,hHi]
    ring
  have dβ (i : Fin 3) (hSi : D i S p=0) : D i (fun z => S z/4) p=0 := by
    have he : (fun z => S z/4)=(fun z => S z*(1/4:ℂ)) := by funext z; ring
    rw [he,D_mul hS contDiffAt_const,D_const,hSi]
    ring
  rw [angular_current_green hf hg hα (dα 1 hB1 hH1) (dα 2 hB2 hH2),
    angular_current_green hf (D_smooth hg 0) hβ (dβ 1 hS1) (dβ 2 hS2),
    D_mul hS ((E_smooth (-1) p).mul ((K_smooth lam hf).mul hg)),
    D_mul (E_smooth (-1) p) ((K_smooth lam hf).mul hg),
    D_mul (K_smooth lam hf) hg,D_E,hS0, K_D lam hg]
  simp only [show (0:Fin 3) ≠ 2 by decide,if_false,zero_mul,zero_add]
  dsimp [K]
  ring


open D4BMJointSource D4BMCommonRadialSource D4BMNativeCircle D4BMNativeResponse
open D4BMModularCore D4BMHorizon D4BMCausalKernel D4BMGlobalAngularResponse

private def U (x : ℝ) : ℂ := (radialUnit x:ℂ)

private theorem unit_smooth : ContDiff ℝ ∞ radialUnit := by
  unfold radialUnit
  exact Real.contDiff_sinh.neg.div Real.contDiff_cosh (fun x => (Real.cosh_pos x).ne')

@[fun_prop] private theorem U_smooth : ContDiff ℝ ∞ U :=
  Complex.ofRealCLM.contDiff.comp unit_smooth

private theorem U_derivative (x : ℝ) : HasDerivAt U (U x^(2 : ℕ)-1) x := by
  simpa [U] using! (radialUnit_hasDerivAt x).ofReal_comp

private def mass (x : ℝ) : ℂ := U x^(2 : ℕ)*(1-U x^(2 : ℕ))
private def S (x : ℝ) : ℂ := U x^(4 : ℕ)*(1+U x)
private def H (x : ℝ) : ℂ := (U x^(2 : ℕ)-1)*(4*U x^(3 : ℕ)+5*U x^(4 : ℕ))
private def B (lam : ℂ) (x : ℝ) : ℂ := mass x*U x^(2 : ℕ)*(2-lam)/8
private def A (lam : ℂ) (x : ℝ) : ℂ :=
  mass x*((5*lam-6)/4+U x^(2 : ℕ)*((4*lam+1)*(lam+2)/8-3*(7*lam-2)/8))

@[fun_prop] private theorem S_smooth : ContDiff ℝ ∞ S := by unfold S; fun_prop
@[fun_prop] private theorem H_smooth : ContDiff ℝ ∞ H := by unfold H; fun_prop
@[fun_prop] private theorem B_smooth (lam : ℂ) : ContDiff ℝ ∞ (B lam) := by
  unfold B mass
  fun_prop

private theorem S_derivative (x : ℝ) : HasDerivAt S (H x) x := by
  apply (((U_derivative x).pow 4).mul ((U_derivative x).const_add 1)).congr_deriv
  dsimp [S,H]
  ring

private theorem radial_derivative {f : ℝ → ℂ} {v : ℂ} (p : Point)
    (hf : HasDerivAt f v (p 0)) (i : Fin 3) :
    D i (fun z => f (z 0)) p=if i=0 then v else 0 := by
  have hd := hf.hasFDerivAt.comp p (hasFDerivAt_apply (𝕜 := ℝ) 0 p)
  have he := congrArg (fun T : Point →L[ℝ] ℂ => T (Pi.single i 1)) hd.fderiv
  fin_cases i <;> simpa [D,Function.comp_def] using! he

private theorem slice_derivative {f : Field} {p : Point}
    (hf : ContDiffAt ℝ ∞ f p) (i : Fin 3) :
    deriv (fun x => f (Function.update p i x)) (p i)=D i f p := by
  have hi : HasDerivAt (fun x : ℝ => Function.update p i x) (Pi.single i 1) (p i) := by
    apply hasDerivAt_pi.mpr
    intro j
    by_cases h : j=i
    · subst j
      simpa using! hasDerivAt_id (p i)
    · simpa [h] using! hasDerivAt_const (p i) (p j)
  have hF : HasFDerivAt f (fderiv ℝ f p) (Function.update p i (p i)) := by
    simpa only [Function.update_eq_self] using! (hf.differentiableAt (by simp)).hasFDerivAt
  have hh := hF.comp_hasDerivAt (p i) hi
  simpa [D] using! hh.deriv

/-- The actual common producer, with the genuine hyperbolic angular operator
in horizontal/log-height coordinates and the original tortoise derivative. -/
def producer (lam : ℂ) (f : Point → ℂ) (p : Point) : ℂ :=
  commonSource lam (fun x => f (Function.update p 0 x))
    (fun x => L f (Function.update p 0 x)) (p 0)

/-- Formal complex bilinear transpose in the original master measure.
No complex coefficient is conjugated. -/
def transposeProducer (lam : ℂ) (g : Point → ℂ) (p : Point) : ℂ :=
  (5*lam-6)/4*g p+U (p 0)^(2 : ℕ)/8*((4*lam+1)*(lam+2)*g p-(lam+4)*L g p)+
    (4*U (p 0)-U (p 0)^(2 : ℕ))*K lam g p+
    U (p 0)^(2 : ℕ)*(D 0 (K lam g) p/(U (p 0)-1)+3*K lam g p)

/-- Radial and both angular source-transfer fluxes, including the mixed
radial/angular derivatives and the exact logarithmic-height measure. -/
def current (lam : ℂ) (f g : Point → ℂ) (p : Point) : Fin 3 → ℂ :=
  let alpha := fun z : Point => B lam (z 0)+H (z 0)/4
  let beta := fun z : Point => S (z 0)/4
  ![S (p 0)*(E (-1) p*(K lam f p*g p)),
    angularCurrent alpha 1 f g p+angularCurrent beta 1 f (D 0 g) p,
    angularCurrent alpha 2 f g p+angularCurrent beta 2 f (D 0 g) p]

/-- Ordinary coordinate divergence of all three spatial fluxes. -/
def currentDivergence (lam : ℂ) (f g : Point → ℂ) (p : Point) : ℂ :=
  D 0 (fun z => current lam f g z 0) p+
  D 1 (fun z => current lam f g z 1) p+
  D 2 (fun z => current lam f g z 2) p

private theorem producer_density {f : Field} {p : Point} (lam : ℂ)
    (hf : ContDiffAt ℝ ∞ f p) (hu : U (p 0)-1 ≠ 0) :
    mass (p 0)*producer lam f p=
      A lam (p 0)*f p+B lam (p 0)*L f p+S (p 0)*D 0 (K lam f) p := by
  rw [producer,commonSource,radialGenerator,radialGenerator,
    slice_derivative hf, slice_derivative (L_smooth hf),D_K lam hf]
  simp only [Function.update_eq_self]
  dsimp [A,B,S,mass,U]
  field_simp [show (radialUnit (p 0):ℂ)-1 ≠ 0 from hu]
  ring

private theorem transpose_density (lam : ℂ) (g : Field) (p : Point)
    (hu : U (p 0)-1 ≠ 0) :
    mass (p 0)*transposeProducer lam g p=
      (A lam (p 0)-(7*lam-2)/8*H (p 0))*g p+
      (B lam (p 0)+H (p 0)/4)*L g p-S (p 0)*D 0 (K lam g) p := by
  dsimp [transposeProducer,A,B,S,H,mass,K]
  field_simp [hu]
  ring


private theorem angularCurrent_smooth {c f g : Field} {p : Point}
    (hc : ContDiffAt ℝ ∞ c p) (hf : ContDiffAt ℝ ∞ f p)
    (hg : ContDiffAt ℝ ∞ g p) (i : Fin 3) : ContDiffAt ℝ ∞ (angularCurrent c i f g) p := by
  have hw : ContDiffAt ℝ ∞ (W i f g) p :=
    ((D_smooth hf i).mul hg).sub (hf.mul (D_smooth hg i))
  unfold angularCurrent
  by_cases hi : i=1
  · subst i
    simp only [if_true]
    exact hc.mul ((E_smooth 1 p).mul hw)
  · simp only [hi,if_false]
    exact hc.mul ((E_smooth (-1) p).mul hw)

private theorem coefficient_pullback {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (p : Point) :
    ContDiffAt ℝ ∞ (fun z : Point => f (z 0)) p :=
  hf.contDiffAt.comp p (contDiff_apply ℝ ℝ (0:Fin 3)).contDiffAt

private theorem radial_zero {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (p : Point)
    (i : Fin 3) (hi : i ≠ 0) : D i (fun z => f (z 0)) p=0 := by
  rw [radial_derivative p ((hf.differentiable (by simp)) (p 0)).hasDerivAt i,if_neg hi]

/-- Coordinate density of the original stream-master measure. -/
def sourceMeasureDensity (p : Point) : ℂ := mass (p 0)*E (-1) p

private theorem common_green {f g : Field} {p : Point} (lam : ℂ)
    (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p) (hu : U (p 0)-1 ≠ 0) :
    sourceMeasureDensity p*(producer lam f p*g p-f p*transposeProducer lam g p)=
      currentDivergence lam f g p := by
  have hB := coefficient_pullback (B_smooth lam) p
  have hS := coefficient_pullback S_smooth p
  have hH := coefficient_pullback H_smooth p
  have hdS : D 0 (fun z => S (z 0)) p=H (p 0) := by
    simpa using radial_derivative p (S_derivative (p 0)) 0
  have hh := general_green (A := fun z => A lam (z 0)) lam hf hg hB hS hH hdS
    (radial_zero (B_smooth lam) p 1 (by decide)) (radial_zero (B_smooth lam) p 2 (by decide))
    (radial_zero S_smooth p 1 (by decide)) (radial_zero S_smooth p 2 (by decide))
    (radial_zero H_smooth p 1 (by decide)) (radial_zero H_smooth p 2 (by decide))
  have hα := hB.add (hH.div_const 4)
  have hβ := hS.div_const 4
  calc
    sourceMeasureDensity p*(producer lam f p*g p-f p*transposeProducer lam g p)
        = E (-1) p*((mass (p 0)*producer lam f p)*g p-
            f p*(mass (p 0)*transposeProducer lam g p)) := by unfold sourceMeasureDensity; ring
    _ = E (-1) p*((A lam (p 0)*f p+B lam (p 0)*L f p+S (p 0)*D 0 (K lam f) p)*g p-
            f p*((A lam (p 0)-(7*lam-2)/8*H (p 0))*g p+
              (B lam (p 0)+H (p 0)/4)*L g p-S (p 0)*D 0 (K lam g) p)) := by
      rw [producer_density lam hf hu,transpose_density lam g p hu]
    _ = currentDivergence lam f g p := by
      rw [hh]
      change _ =
        D 0 (fun z => S (z 0)*(E (-1) z*(K lam f z*g z))) p+
        D 1 (fun z => angularCurrent (fun z => B lam (z 0)+H (z 0)/4) 1 f g z+
          angularCurrent (fun z => S (z 0)/4) 1 f (D 0 g) z) p+
        D 2 (fun z => angularCurrent (fun z => B lam (z 0)+H (z 0)/4) 2 f g z+
          angularCurrent (fun z => S (z 0)/4) 2 f (D 0 g) z) p
      rw [D_add (angularCurrent_smooth hα hf hg 1)
          (angularCurrent_smooth hβ hf (D_smooth hg 0) 1),
        D_add (angularCurrent_smooth hα hf hg 2)
          (angularCurrent_smooth hβ hf (D_smooth hg 0) 2)]
      ring

private theorem amplitude_smooth (s w a T : ℂ) : ContDiff ℝ ∞ (sourceAmplitude s w a T) := by
  have hd : Differentiable ℝ (sourceAmplitude s w a T) :=
    fun x => (sourceAmplitude_hasDerivAt s w a T x).differentiableAt
  have he : deriv (sourceAmplitude s w a T)=
      fun x => amplitudeRate s w (radialUnit x)*sourceAmplitude s w a T x :=
    funext (fun x => (sourceAmplitude_hasDerivAt s w a T x).deriv)
  have hr : ContDiff ℝ ∞ (fun x => amplitudeRate s w (radialUnit x)) := by
    change ContDiff ℝ ∞ (fun x => w+2*s*(U x-1))
    fun_prop
  apply contDiff_infty.mpr
  intro n
  induction n with
  | zero => exact contDiff_zero.mpr hd.continuous
  | succ n ih =>
    change ContDiff ℝ ((n : WithTop ℕ∞)+1) _
    apply contDiff_succ_iff_deriv.mpr
    refine ⟨hd,by simp,?_⟩
    rw [he]
    exact (hr.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).mul ih

/-- The literal ingoing theta seed in the native logarithmic-height chart,
including its original smooth onset and complex amplitude. -/
def thetaSeed (q : XiZeroCopy) (branch : Bool) (a : ℂ) (v : ℝ) (p : Point) : ℂ :=
  seed (physicalRate q branch) a v (p 0) (fullSquarePotential q ![p 1,Real.exp (p 2)])

private theorem thetaSeed_smooth (q : XiZeroCopy) (branch : Bool) (a : ℂ) (v : ℝ) :
    ContDiff ℝ ∞ (thetaSeed q branch a v) := by
  have hb : ContDiff ℝ ∞ (fun p : Point => fullSquarePotential q ![p 1,Real.exp (p 2)]) := by
    have hm := (nativeMean_joint_smooth q).comp
      (show ContDiff ℝ ∞ (fun p : Point => ((0:ℝ),p 1,p 2)) by fun_prop)
    simpa only [Function.comp_def,mean_zero] using! hm
  unfold thetaSeed seed
  exact (((amplitude_smooth (physicalRate q branch) 0 a 1).comp
    (contDiff_apply ℝ ℝ (0:Fin 3))).mul contDiff_const).mul hb

/-- Constant and slope of the causal invariant at fixed ingoing delay. -/
def kernelArgumentBase (h target : ℝ) : ℝ := Real.cosh (h-target)/Real.cosh target

def kernelArgumentSlope (image : Bool) (h target : ℝ) : ℝ :=
  (Real.sinh (h-target)+(if image then -Real.sinh target else Real.sinh target))/Real.cosh target

/-- Both the direct and AdS image invariants are affine in the original compact
source radius when the ingoing delay is held fixed. -/
theorem kernel_invariant_affine (image : Bool) (h target source : ℝ) :
    invariant (h-target+source) target (if image then -source else source)=
      kernelArgumentBase h target-kernelArgumentSlope image h target*radialUnit source := by
  cases image <;> simp only [kernelArgumentBase,kernelArgumentSlope,invariant,radialUnit,
    Bool.false_eq_true,if_false,if_true,Real.cosh_add,Real.cosh_neg,Real.sinh_neg]
  all_goals field_simp [(Real.cosh_pos target).ne',(Real.cosh_pos source).ne']
  all_goals ring

/-- The full native causal kernel at fixed ingoing delay, for either the direct
term or the AdS image. Source-radius variation changes the static-time separation. -/
def kernelField (image : Bool) (q : XiZeroCopy) (h target : ℝ) (p : Point) : ℂ :=
  nativeRiemannKernel q (h-target+p 0) target (if image then -p 0 else p 0) (p 1) (p 2)

private theorem kernelField_smooth (image : Bool) (q : XiZeroCopy) (h target : ℝ) (p : Point)
    (hz : 1 < invariant (h-target+p 0) target (if image then -p 0 else p 0)) :
    ContDiffAt ℝ ∞ (kernelField image q h target) p := by
  have hi : ContDiff ℝ ∞ (fun z : Point =>
      invariant (h-target+z 0) target (if image then -z 0 else z 0)) := by
    cases image <;> simp only [Bool.false_eq_true,if_false,if_true]
    all_goals unfold invariant
    all_goals apply ContDiff.div <;> try fun_prop
    all_goals intro z; exact mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'
  have ha : ContDiffAt ℝ ∞ (fun z : Point =>
      Real.arcosh (invariant (h-target+z 0) target (if image then -z 0 else z 0))) p := by
    simpa only [Function.comp_def] using!
      (Real.contDiffAt_arcosh (n := ∞) hz).comp p hi.contDiffAt
  have hb : ContDiffAt ℝ ∞ (fun z : Point =>
      (Real.arcosh (invariant (h-target+z 0) target (if image then -z 0 else z 0)),z 1,z 2)) p :=
    ha.prodMk ((contDiff_apply ℝ ℝ (1:Fin 3)).contDiffAt.prodMk
      (contDiff_apply ℝ ℝ (2:Fin 3)).contDiffAt)
  change ContDiffAt ℝ ∞ (fun z : Point =>
    mean q (Real.arcosh (invariant (h-target+z 0) target (if image then -z 0 else z 0))) (z 1) (z 2)) p
  simpa only [Function.comp_def] using! (nativeMean_joint_smooth q).contDiffAt.comp p hb

/-- The retained full spin-two angular weight `-Delta(Delta-2)` applied to the
literal native kernel. No angular eigenvalue replaces either Laplacian. -/
def spinTwoKernelField (image : Bool) (q : XiZeroCopy) (h target : ℝ) (p : Point) : ℂ :=
  -L (L (kernelField image q h target)) p+2*L (kernelField image q h target) p

private theorem spinTwoKernelField_smooth (image : Bool) (q : XiZeroCopy) (h target : ℝ) (p : Point)
    (hz : 1 < invariant (h-target+p 0) target (if image then -p 0 else p 0)) :
    ContDiffAt ℝ ∞ (spinTwoKernelField image q h target) p := by
  have hg := kernelField_smooth image q h target p hz
  exact (L_smooth (L_smooth hg)).neg.add (contDiffAt_const.mul (L_smooth hg))

/-- Original negative source radius in the smooth interior of the selected
forward direct or image cone. These are geometric domain conditions. -/
abbrev SourceInterior (image : Bool) := {p : CausalPoint //
  p.source < 0 ∧ 1 < invariant p.time p.target (if image then -p.source else p.source)}

/-- Complete spatial Green identity for the original theta seed and either
native causal kernel term with its full spin-two weight. All three currents
and the fixed-ingoing-delay derivative are retained. Every regularity fact is
proved from the actual fields; no cancellation or boundary-vanishing premise
is supplied. Characteristic contacts and infinite-domain limits remain separate. -/
theorem thetaSeed_nativeSpinTwoKernel_green (q : XiZeroCopy) (branch : Bool) (a : ℂ) (v : ℝ)
    (image : Bool) (p : SourceInterior image) (X k : ℝ) :
    let z : Point := ![p.val.source,X,k]
    let f := thetaSeed q branch a v
    let g := spinTwoKernelField image q (p.val.time-p.val.source+p.val.target) p.val.target
    sourceMeasureDensity z*(producer (scalarParameter q) f z*g z-
      f z*transposeProducer (scalarParameter q) g z)=
      currentDivergence (scalarParameter q) f g z := by
  let z : Point := ![p.val.source,X,k]
  have hf := (thetaSeed_smooth q branch a v).contDiffAt (x := z)
  have hz : 1 < invariant
      ((p.val.time-p.val.source+p.val.target)-p.val.target+z 0)
      p.val.target (if image then -z 0 else z 0) := by
    simpa only [z,Matrix.cons_val_zero,add_sub_cancel_right,sub_add_cancel] using p.property.2
  have hg := spinTwoKernelField_smooth image q
    (p.val.time-p.val.source+p.val.target) p.val.target z hz
  have hu : U (z 0)-1 ≠ 0 := by
    change (radialUnit p.val.source:ℂ)-1 ≠ 0
    exact_mod_cast sub_ne_zero.mpr (ne_of_lt (radialUnit_bounds p.val.source p.property.1).2)
  exact common_green (f := thetaSeed q branch a v)
    (g := spinTwoKernelField image q (p.val.time-p.val.source+p.val.target) p.val.target)
    (p := z) (scalarParameter q) hf hg hu


private def baseField (q : XiZeroCopy) (p : Point) : ℂ := mean q 0 (p 1) (p 2)

private theorem baseField_smooth (q : XiZeroCopy) : ContDiff ℝ ∞ (baseField q) := by
  have hm := (nativeMean_joint_smooth q).comp
    (show ContDiff ℝ ∞ (fun p : Point => ((0:ℝ),p 1,p 2)) by fun_prop)
  simpa only [Function.comp_def,baseField] using! hm

private theorem base_firstX (q : XiZeroCopy) (p : Point) :
    D 1 (baseField q) p=deriv (fun X => mean q 0 X (p 2)) (p 1) := by
  rw [← slice_derivative (baseField_smooth q).contDiffAt 1]
  simp [baseField]

private theorem base_firstK (q : XiZeroCopy) (p : Point) :
    D 2 (baseField q) p=deriv (fun k => mean q 0 (p 1) k) (p 2) := by
  rw [← slice_derivative (baseField_smooth q).contDiffAt 2]
  simp [baseField]

private theorem base_secondX (q : XiZeroCopy) (p : Point) :
    D 1 (D 1 (baseField q)) p=deriv (deriv (fun X => mean q 0 X (p 2))) (p 1) := by
  rw [← slice_derivative (D_smooth (baseField_smooth q).contDiffAt 1) 1]
  simp only [base_firstX]
  simp

private theorem base_secondK (q : XiZeroCopy) (p : Point) :
    D 2 (D 2 (baseField q)) p=deriv (deriv (fun k => mean q 0 (p 1) k)) (p 2) := by
  rw [← slice_derivative (D_smooth (baseField_smooth q).contDiffAt 2) 2]
  simp only [base_firstK]
  simp

private theorem base_laplacian (q : XiZeroCopy) (p : Point) :
    L (baseField q) p=scalarLaplacian (fullSquarePotential q) ![p 1,Real.exp (p 2)] := by
  have he : E 2 p=(Real.exp (p 2):ℂ)^(2 : ℕ) := by
    dsimp [E]
    rw [two_mul,Complex.exp_add]
    simp [Complex.ofReal_exp,pow_two]
  have hc : average (fun theta => scalarLaplacian (fullSquarePotential q) (logCircle 0 theta (p 1) (p 2)))=
      scalarLaplacian (fullSquarePotential q) ![p 1,Real.exp (p 2)] := by
    have hfun : (fun theta => scalarLaplacian (fullSquarePotential q) (logCircle 0 theta (p 1) (p 2)))=
        fun _ : ℝ => scalarLaplacian (fullSquarePotential q) ![p 1,Real.exp (p 2)] := by
      funext theta
      simp [logCircle,circle,offset,height,denominator]
    rw [hfun,average,← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)]
    simp only [intervalIntegral.integral_const,sub_zero,Complex.real_smul,Complex.ofReal_mul,
      Complex.ofReal_ofNat]
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  rw [L,he,base_secondX,base_secondK,base_firstK,mean_laplacian_commutes,hc]

private theorem L_radial_mul {f : Field} (hf : ContDiff ℝ ∞ f) {c : ℝ → ℂ}
    (hc : ContDiff ℝ ∞ c) (p : Point) :
    L (fun z => c (z 0)*f z) p=c (p 0)*L f p := by
  have hd (i : Fin 3) (hi : i ≠ 0) :
      D i (fun z => c (z 0)*f z)=fun z => c (z 0)*D i f z := by
    funext z
    rw [D_mul (coefficient_pullback hc z) hf.contDiffAt,radial_zero hc z i hi]
    ring
  unfold L
  rw [hd 1 (by decide),hd 2 (by decide),
    D_mul (coefficient_pullback hc p) (D_smooth hf.contDiffAt 1),
    D_mul (coefficient_pullback hc p) (D_smooth hf.contDiffAt 2),
    radial_zero hc p 1 (by decide),radial_zero hc p 2 (by decide)]
  ring

private theorem thetaSeed_laplacian (q : XiZeroCopy) (branch : Bool) (a : ℂ) (v : ℝ) (p : Point) :
    L (thetaSeed q branch a v) p=
      seed (physicalRate q branch) a v (p 0)
        (scalarLaplacian (fullSquarePotential q) ![p 1,Real.exp (p 2)]) := by
  have he : thetaSeed q branch a v=
      fun z => (sourceAmplitude (physicalRate q branch) 0 a 1 (z 0)*
        timeOnset (2*physicalRate q branch) v)*baseField q z := by
    funext z
    simp [thetaSeed,seed,baseField,mean_zero]
  rw [he,L_radial_mul (baseField_smooth q)
    ((amplitude_smooth (physicalRate q branch) 0 a 1).mul contDiff_const),base_laplacian]
  rfl

/-- The producer in the full Green identity is exactly the already normalized
original physical source, on either branch, with its full theta Laplacian and
fixed smooth onset. This supplies the source dictionary, not a vanishing claim. -/
theorem thetaSeed_producer_original (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (v : ℝ) (x : {x : ℝ // x < 0}) (z : UpperHalfPlane) :
    timeOriginalForcing q branch a (v-x.val) x.val (coordinates z)=
      -2*(1-(radialUnit x.val:ℂ)^(2 : ℕ))*(radialUnit x.val:ℂ)*
        producer (scalarParameter q) (thetaSeed q branch a v) ![x.val,z.re,Real.log z.im] := by
  rw [timeOriginalForcing_common_source]
  congr 1
  unfold producer
  congr 1
  · funext y
    simp [thetaSeed,coordinates,Real.exp_log z.im_pos]
  · funext y
    rw [thetaSeed_laplacian]
    simp [coordinates,Real.exp_log z.im_pos]

private def freeze (x : ℝ) (p : Point) : Point := Function.update p 0 x
private def sourceSlice (f : Field) (x : ℝ) (p : Point) : ℂ := f (freeze x p)

private theorem freeze_smooth (x : ℝ) : ContDiff ℝ ∞ (freeze x) := by
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i=0
  · subst i; simpa [freeze] using (contDiff_const : ContDiff ℝ ∞ (fun _ : Point => x))
  · simpa [freeze,hi] using (contDiff_apply ℝ ℝ i)

private theorem sourceSlice_smooth {f : Field} {x : ℝ} {p : Point}
    (hf : ContDiffAt ℝ ∞ f (freeze x p)) : ContDiffAt ℝ ∞ (sourceSlice f x) p :=
  hf.comp p (freeze_smooth x).contDiffAt

private theorem D_sourceSlice {f : Field} {x : ℝ} {p : Point}
    (hf : ContDiffAt ℝ ∞ f (freeze x p)) (i : Fin 3) (hi : i ≠ 0) :
    D i (sourceSlice f x) p=D i f (freeze x p) := by
  rw [← slice_derivative (sourceSlice_smooth hf) i]
  have he : (fun t => sourceSlice f x (Function.update p i t))=
      fun t => f (Function.update (freeze x p) i t) := by
    funext t
    unfold sourceSlice freeze
    rw [Function.update_comm hi]
  rw [he]
  have hp : p i=freeze x p i := by simp [freeze,hi]
  rw [hp]
  exact slice_derivative hf i

private theorem L_sourceSlice {f : Field} (x : ℝ)
    (hf : ∀ p, ContDiffAt ℝ ∞ f (freeze x p)) (p : Point) :
    L (sourceSlice f x) p=L f (freeze x p) := by
  have hd (i : Fin 3) (hi : i ≠ 0) :
      D i (sourceSlice f x)=sourceSlice (D i f) x := by
    funext z
    exact D_sourceSlice (hf z) i hi
  unfold L
  rw [hd 1 (by decide),hd 2 (by decide),
    D_sourceSlice (D_smooth (hf p) 1) 1 (by decide),
    D_sourceSlice (D_smooth (hf p) 2) 2 (by decide)]
  simp [E,freeze,sourceSlice]

/-- Full spin-two angular trace with source radius frozen before taking any
angular derivative. This definition is meaningful on the characteristic. -/
def nativeSpinTwoTrace (image : Bool) (q : XiZeroCopy) (h target : ℝ) (p : Point) : ℂ :=
  let f := sourceSlice (kernelField image q h target) (p 0);
  -L (L f) p+2*L f p

/-- Literal full-source spin-two angular density in logarithmic height. -/
def thetaSpinTwo (q : XiZeroCopy) (p : Point) : ℂ :=
  -L (L (baseField q)) p+2*L (baseField q) p

/-- Freezing the radius preserves the actual spin-two field at every smooth
interior point; the full two angular Laplacians are retained. -/
theorem nativeSpinTwoTrace_eq_interior (image : Bool) (q : XiZeroCopy)
    (h target : ℝ) (p : Point)
    (hz : 1 < invariant (h-target+p 0) target (if image then -p 0 else p 0)) :
    nativeSpinTwoTrace image q h target p=spinTwoKernelField image q h target p := by
  have hf (z : Point) : ContDiffAt ℝ ∞ (kernelField image q h target) (freeze (p 0) z) := by
    apply kernelField_smooth
    simpa [freeze] using hz
  have he : L (sourceSlice (kernelField image q h target) (p 0))=
      sourceSlice (L (kernelField image q h target)) (p 0) := by
    funext z
    exact L_sourceSlice (p 0) hf z
  unfold nativeSpinTwoTrace
  dsimp only
  rw [he,L_sourceSlice (p 0) (fun z => L_smooth (hf z)) p]
  simp [sourceSlice,freeze,spinTwoKernelField]

private def circleField (q : XiZeroCopy) (p : Point) : ℂ := mean q (p 0) (p 1) (p 2)

private theorem circleField_smooth (q : XiZeroCopy) : ContDiff ℝ ∞ (circleField q) := by
  have hm := (nativeMean_joint_smooth q).comp
    (show ContDiff ℝ ∞ (fun p : Point => (p 0,p 1,p 2)) by fun_prop)
  simpa only [Function.comp_def,circleField] using! hm

private def circleSpinTwo (q : XiZeroCopy) (p : Point) : ℂ :=
  -L (L (circleField q)) p+2*L (circleField q) p

private theorem circleSpinTwo_smooth (q : XiZeroCopy) (p : Point) :
    ContDiffAt ℝ ∞ (circleSpinTwo q) p := by
  have hc := (circleField_smooth q).contDiffAt (x := p)
  exact (L_smooth (L_smooth hc)).neg.add (contDiffAt_const.mul (L_smooth hc))

private theorem nativeSpinTwoTrace_eq_circle (image : Bool) (q : XiZeroCopy)
    (h target : ℝ) (p : Point) :
    nativeSpinTwoTrace image q h target p=
      circleSpinTwo q (freeze
        (Real.arcosh (invariant (h-target+p 0) target (if image then -p 0 else p 0))) p) := by
  let r := Real.arcosh (invariant (h-target+p 0) target (if image then -p 0 else p 0))
  have he : sourceSlice (kernelField image q h target) (p 0)=sourceSlice (circleField q) r := by
    funext z
    simp [sourceSlice,freeze,kernelField,nativeRiemannKernel,angularKernel,circleField,r]
  have heL : L (sourceSlice (circleField q) r)=sourceSlice (L (circleField q)) r := by
    funext z
    exact L_sourceSlice r (fun _ => (circleField_smooth q).contDiffAt) z
  unfold nativeSpinTwoTrace
  dsimp only
  rw [he,heL,L_sourceSlice r (fun z => L_smooth (circleField_smooth q).contDiffAt) p]
  rfl

private theorem nativeSpinTwoTrace_continuousAt (image : Bool) (q : XiZeroCopy)
    (h target : ℝ) (p : Point)
    (hz : 0 < invariant (h-target+p 0) target (if image then -p 0 else p 0)) :
    ContinuousAt (nativeSpinTwoTrace image q h target) p := by
  have hi : Continuous (fun z : Point =>
      invariant (h-target+z 0) target (if image then -z 0 else z 0)) := by
    cases image <;> simp only [Bool.false_eq_true,if_false,if_true]
    all_goals unfold invariant
    all_goals apply Continuous.div <;> try fun_prop
    all_goals intro z; exact mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'
  have ha : ContinuousAt (fun z : Point =>
      Real.arcosh (invariant (h-target+z 0) target (if image then -z 0 else z 0))) p := by
    unfold Real.arcosh
    apply (hi.continuousAt.add ((hi.continuousAt.pow 2).sub continuousAt_const).sqrt).log
    exact ne_of_gt (add_pos_of_pos_of_nonneg hz (Real.sqrt_nonneg _))
  have hp : ContinuousAt (fun z : Point => freeze
      (Real.arcosh (invariant (h-target+z 0) target (if image then -z 0 else z 0))) z) p := by
    apply continuousAt_pi.mpr
    intro i
    by_cases he : i=0
    · subst i
      simpa [freeze] using ha
    · simpa [freeze,he] using (continuous_apply i : Continuous (fun z : Point => z i)).continuousAt
  have he : nativeSpinTwoTrace image q h target=
      fun z => circleSpinTwo q (freeze
        (Real.arcosh (invariant (h-target+z 0) target (if image then -z 0 else z 0))) z) :=
    funext (nativeSpinTwoTrace_eq_circle image q h target)
  rw [he]
  exact (circleSpinTwo_smooth q _).continuousAt.comp hp

/-- Lower source face at fixed ingoing delay, including the distinct image face. -/
def sourceCharacteristic (image : Bool) (h target : ℝ) : ℝ :=
  if image then -h/2 else target-h/2

private theorem invariant_sourceCharacteristic (image : Bool) (h target : ℝ) :
    invariant (h-target+sourceCharacteristic image h target) target
      (if image then -sourceCharacteristic image h target else sourceCharacteristic image h target)=1 := by
  cases image
  · simp only [sourceCharacteristic,Bool.false_eq_true,if_false]
    rw [show h-target+(target-h/2)=target-(target-h/2) by ring]
    exact invariant_characteristic target (target-h/2)
  · have ht : h-target+-h/2=-(target- -(-h/2)) := by ring
    simp only [sourceCharacteristic,if_true]
    rw [ht]
    have he : invariant (-(target- -(-h/2))) target (-(-h/2))=
        invariant (target- -(-h/2)) target (-(-h/2)) := by
      unfold invariant
      rw [Real.cosh_neg]
    rw [he,invariant_characteristic]

/-- Both characteristic traces retain the exact original full spin-two source. -/
theorem nativeSpinTwoTrace_characteristic (image : Bool) (q : XiZeroCopy)
    (h target X k : ℝ) :
    nativeSpinTwoTrace image q h target ![sourceCharacteristic image h target,X,k]=
      thetaSpinTwo q ![sourceCharacteristic image h target,X,k] := by
  have he : sourceSlice (kernelField image q h target) (sourceCharacteristic image h target)=
      baseField q := by
    funext p
    simp [sourceSlice,freeze,kernelField,nativeRiemannKernel,
      invariant_sourceCharacteristic,angularKernel,baseField]
  unfold nativeSpinTwoTrace
  dsimp only [Matrix.cons_val_zero]
  rw [he]
  rfl


private theorem base_laplacian_freeze (q : XiZeroCopy) (x : ℝ) (p : Point) :
    L (baseField q) (freeze x p)=L (baseField q) p := by
  have he : sourceSlice (baseField q) x=baseField q := by
    funext z
    simp [sourceSlice,freeze,baseField]
  rw [← L_sourceSlice x (fun _ => (baseField_smooth q).contDiffAt) p,he]

private theorem thetaSpinTwo_freeze (q : XiZeroCopy) (x : ℝ) (p : Point) :
    thetaSpinTwo q (freeze x p)=thetaSpinTwo q p := by
  have he : sourceSlice (L (baseField q)) x=L (baseField q) :=
    funext (base_laplacian_freeze q x)
  have he2 : L (L (baseField q)) (freeze x p)=L (L (baseField q)) p := by
    rw [← L_sourceSlice x (fun _ => L_smooth (baseField_smooth q).contDiffAt) p,he]
  simp only [thetaSpinTwo,he2,base_laplacian_freeze]

/-- The exact angular product retained by the original source's radial face. -/
def thetaAngularCoupling (q : XiZeroCopy) (X k : ℝ) : ℂ :=
  ((7*scalarParameter q-2)/8*fullSquarePotential q ![X,Real.exp k]-
    (1/4:ℂ)*scalarLaplacian (fullSquarePotential q) ![X,Real.exp k])*
      thetaSpinTwo q ![0,X,k]

/-- Radial face of the original Green current, using its continuous angular trace. -/
def sourceRadialTraceCurrent (q : XiZeroCopy) (branch : Bool) (a : ℂ) (v : ℝ)
    (image : Bool) (h target X k y : ℝ) : ℂ :=
  current (scalarParameter q) (thetaSeed q branch a v)
    (nativeSpinTwoTrace image q h target) ![y,X,k] 0

/-- Original radial seed weight, including the characteristic flux coefficient. -/
def sourceCharacteristicWeight (s : ℂ) (y : ℝ) : ℂ :=
  S y*sourceAmplitude s 0 1 1 y

private theorem sourceRadialTraceCurrent_characteristic (q : XiZeroCopy) (branch : Bool)
    (a : ℂ) (v : ℝ) (image : Bool) (h target X k : ℝ) :
    sourceRadialTraceCurrent q branch a v image h target X k
        (sourceCharacteristic image h target)=
      Complex.exp (-(k:ℂ))*a^(2 : ℕ)*timeOnset (2*physicalRate q branch) v*
        thetaAngularCoupling q X k*
        sourceCharacteristicWeight (physicalRate q branch) (sourceCharacteristic image h target) := by
  let y := sourceCharacteristic image h target
  have hspin : thetaSpinTwo q ![y,X,k]=thetaSpinTwo q ![0,X,k] := by
    have hv : freeze 0 ![y,X,k]=![0,X,k] := by
      ext i
      fin_cases i <;> simp [freeze]
    rw [← hv]
    exact (thetaSpinTwo_freeze q 0 ![y,X,k]).symm
  unfold sourceRadialTraceCurrent current
  simp only [Matrix.cons_val_zero]
  rw [nativeSpinTwoTrace_characteristic]
  change S y*(E (-1) ![y,X,k]*(K (scalarParameter q) (thetaSeed q branch a v) ![y,X,k]*
    thetaSpinTwo q ![y,X,k]))=_
  rw [hspin,K,thetaSeed_laplacian]
  simp only [thetaSeed,seed,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    E,neg_one_mul,thetaAngularCoupling,sourceCharacteristicWeight,sourceAmplitude,
    zero_mul,Complex.exp_zero,one_mul,one_pow,mul_one]
  simp only [Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_succ,Matrix.cons_val_zero]
  dsimp only [y]
  ring

private theorem sourceRadialTraceCurrent_zero (q : XiZeroCopy) (branch : Bool)
    (a : ℂ) (v : ℝ) (image : Bool) (h target X k : ℝ) :
    sourceRadialTraceCurrent q branch a v image h target X k 0=0 := by
  simp [sourceRadialTraceCurrent,current,S,U,radialUnit]

/-- Actual causal source intervals have the two stated finite characteristic
lower faces, at every positive ingoing delay and negative target radius. -/
theorem sourceCharacteristic_causal_interval (image : Bool) (h : Ioi (0:ℝ))
    (target : Iio (0:ℝ)) (y : Iic (0:ℝ)) :
    |target.val-(if image then -y.val else y.val)| ≤ h.val-target.val+y.val ↔
      sourceCharacteristic image h.val target.val ≤ y.val := by
  have hh : 0 < h.val := h.property
  have hx : target.val < 0 := target.property
  have hy : y.val ≤ 0 := y.property
  cases image <;> simp only [Bool.false_eq_true,if_false,if_true,sourceCharacteristic,abs_le]
  all_goals constructor
  all_goals intro he
  · linarith [he.1]
  · constructor <;> linarith
  · linarith [he.1]
  · constructor <;> linarith

/-- Exact signed direct-minus-image radial face. Both upper faces and both
distinct lower characteristics are included; no angular current is removed. -/
theorem sourceRadialTraceCurrent_signed_faces (q : XiZeroCopy) (branch : Bool)
    (a : ℂ) (v h target X k : ℝ) :
    (sourceRadialTraceCurrent q branch a v false h target X k 0-
      sourceRadialTraceCurrent q branch a v false h target X k
        (sourceCharacteristic false h target))-
    (sourceRadialTraceCurrent q branch a v true h target X k 0-
      sourceRadialTraceCurrent q branch a v true h target X k
        (sourceCharacteristic true h target))=
      Complex.exp (-(k:ℂ))*a^(2 : ℕ)*timeOnset (2*physicalRate q branch) v*
        thetaAngularCoupling q X k*
        (sourceCharacteristicWeight (physicalRate q branch) (-h/2)-
          sourceCharacteristicWeight (physicalRate q branch) (target-h/2)) := by
  rw [sourceRadialTraceCurrent_zero,sourceRadialTraceCurrent_zero,
    sourceRadialTraceCurrent_characteristic,sourceRadialTraceCurrent_characteristic]
  simp only [sourceCharacteristic,Bool.false_eq_true,if_false,if_true]
  ring


private theorem sourceCurve_smooth (X k : ℝ) :
    ContDiff ℝ ∞ (fun y : ℝ => (![y,X,k] : Point)) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · simpa [id_eq] using! (contDiff_id : ContDiff ℝ ∞ (fun y : ℝ => y))
  · simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => X))
  · simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => k))

/-- The original interior radial current has the displayed characteristic limit.
The full spin-two source, smooth onset, measure and branch amplitude are retained. -/
theorem sourceRadialCurrent_characteristic_limit (q : XiZeroCopy) (branch : Bool)
    (a : ℂ) (v : ℝ) (image : Bool) (h : Ioi (0:ℝ)) (target : Iio (0:ℝ)) (X k : ℝ) :
    Tendsto (fun y => current (scalarParameter q) (thetaSeed q branch a v)
      (spinTwoKernelField image q h.val target.val) ![y,X,k] 0)
      (𝓝[{y : ℝ | 1 < invariant (h.val-target.val+y) target.val (if image then -y else y)}]
        (sourceCharacteristic image h.val target.val))
      (𝓝 (Complex.exp (-(k:ℂ))*a^(2 : ℕ)*timeOnset (2*physicalRate q branch) v*
        thetaAngularCoupling q X k*sourceCharacteristicWeight (physicalRate q branch)
          (sourceCharacteristic image h.val target.val))) := by
  let e := sourceCharacteristic image h.val target.val
  have hz : 0 < invariant (h.val-target.val+e) target.val (if image then -e else e) := by
    rw [invariant_sourceCharacteristic]
    norm_num
  have ht : ContinuousAt (fun y => nativeSpinTwoTrace image q h.val target.val ![y,X,k]) e :=
    (nativeSpinTwoTrace_continuousAt image q h.val target.val ![e,X,k] hz).comp (f := fun y : ℝ => ![y,X,k]) (sourceCurve_smooth X k).continuous.continuousAt
  have he : ContinuousAt (fun y : ℝ => E (-1) ![y,X,k]) e :=
    (E_smooth (-1) ![e,X,k]).continuousAt.comp (f := fun y : ℝ => ![y,X,k]) (sourceCurve_smooth X k).continuous.continuousAt
  have hk : ContinuousAt (fun y : ℝ => K (scalarParameter q) (thetaSeed q branch a v) ![y,X,k]) e :=
    (K_smooth (scalarParameter q) (thetaSeed_smooth q branch a v).contDiffAt).continuousAt.comp
      (f := fun y : ℝ => ![y,X,k]) (sourceCurve_smooth X k).continuous.continuousAt
  have hc : ContinuousAt (sourceRadialTraceCurrent q branch a v image h.val target.val X k) e := by
    change ContinuousAt (fun y => S y*(E (-1) ![y,X,k]*
      (K (scalarParameter q) (thetaSeed q branch a v) ![y,X,k]*
        nativeSpinTwoTrace image q h.val target.val ![y,X,k]))) e
    exact S_smooth.continuous.continuousAt.mul (he.mul (hk.mul ht))
  have hh : Tendsto (sourceRadialTraceCurrent q branch a v image h.val target.val X k)
      (𝓝 e) (𝓝 (sourceRadialTraceCurrent q branch a v image h.val target.val X k e)) := hc
  rw [sourceRadialTraceCurrent_characteristic] at hh
  apply (hh.mono_left inf_le_left).congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  unfold sourceRadialTraceCurrent current
  simp only [Matrix.cons_val_zero]
  rw [nativeSpinTwoTrace_eq_interior image q h.val target.val ![y,X,k] (by simpa using hy)]


private theorem invariant_source_interior (image : Bool) (h : Ioi (0:ℝ))
    (target : Iio (0:ℝ)) (y : ℝ) (hy : sourceCharacteristic image h.val target.val < y) :
    1 < invariant (h.val-target.val+y) target.val (if image then -y else y) := by
  have hh : 0 < h.val := h.property
  have hx : target.val < 0 := target.property
  have ht : 0 < h.val-target.val+y := by
    cases image <;> simp only [sourceCharacteristic,Bool.false_eq_true,if_false,if_true] at hy
    all_goals linarith
  have ha : |target.val-(if image then -y else y)| < h.val-target.val+y := by
    rw [abs_lt]
    cases image <;> simp only [sourceCharacteristic,Bool.false_eq_true,if_false,if_true] at hy ⊢
    all_goals constructor <;> linarith
  have hc : Real.cosh (target.val-(if image then -y else y)) < Real.cosh (h.val-target.val+y) := by
    apply Real.cosh_lt_cosh.mpr
    rwa [abs_of_pos ht]
  rw [Real.cosh_sub] at hc
  unfold invariant
  apply (lt_div_iff₀ (mul_pos (Real.cosh_pos _) (Real.cosh_pos _))).mpr
  linarith

private theorem sourceCharacteristic_neg (image : Bool) (h : Ioi (0:ℝ))
    (target : Iio (0:ℝ)) : sourceCharacteristic image h.val target.val < 0 := by
  have hh : 0 < h.val := h.property
  have hx : target.val < 0 := target.property
  cases image <;> simp only [sourceCharacteristic,Bool.false_eq_true,if_false,if_true]
  all_goals linarith

private def radialField (q : XiZeroCopy) (branch : Bool) (a : ℂ) (v : ℝ)
    (image : Bool) (h target : ℝ) (p : Point) : ℂ :=
  current (scalarParameter q) (thetaSeed q branch a v)
    (spinTwoKernelField image q h target) p 0

private theorem radialField_smooth (q : XiZeroCopy) (branch : Bool) (a : ℂ) (v : ℝ)
    (image : Bool) (h target : ℝ) (p : Point)
    (hz : 1 < invariant (h-target+p 0) target (if image then -p 0 else p 0)) :
    ContDiffAt ℝ ∞ (radialField q branch a v image h target) p := by
  change ContDiffAt ℝ ∞ (fun z => S (z 0)*(E (-1) z*
    (K (scalarParameter q) (thetaSeed q branch a v) z*spinTwoKernelField image q h target z))) p
  exact (coefficient_pullback S_smooth p).mul ((E_smooth (-1) p).mul
    ((K_smooth (scalarParameter q) (thetaSeed_smooth q branch a v).contDiffAt).mul
      (spinTwoKernelField_smooth image q h target p hz)))

/-- Original source-transfer integrand after retaining both angular divergences
on the same side. Its radial primitive is the actual Green radial current. -/
def radialTransferDensity (q : XiZeroCopy) (branch : Bool) (a : ℂ) (v : ℝ)
    (image : Bool) (h target X k y : ℝ) : ℂ :=
  let f := thetaSeed q branch a v
  let g := spinTwoKernelField image q h target
  let p : Point := ![y,X,k]
  sourceMeasureDensity p*(producer (scalarParameter q) f p*g p-
    f p*transposeProducer (scalarParameter q) g p)-
    D 1 (fun z => current (scalarParameter q) f g z 1) p-
    D 2 (fun z => current (scalarParameter q) f g z 2) p

private theorem radialTransferDensity_eq (q : XiZeroCopy) (branch : Bool) (a : ℂ) (v : ℝ)
    (image : Bool) (h target X k y : ℝ) (hy : y ≤ 0)
    (hz : 1 < invariant (h-target+y) target (if image then -y else y)) :
    radialTransferDensity q branch a v image h target X k y=
      D 0 (radialField q branch a v image h target) ![y,X,k] := by
  have hu : U y-1 ≠ 0 := by
    by_cases he : y=0
    · subst y; simp [U,radialUnit]
    · change (radialUnit y:ℂ)-1 ≠ 0
      exact_mod_cast sub_ne_zero.mpr (ne_of_lt (radialUnit_bounds y (lt_of_le_of_ne hy he)).2)
  have hg := spinTwoKernelField_smooth image q h target ![y,X,k] hz
  have hh := common_green (f := thetaSeed q branch a v)
    (g := spinTwoKernelField image q h target) (p := ![y,X,k]) (scalarParameter q)
      (thetaSeed_smooth q branch a v).contDiffAt hg hu
  unfold radialTransferDensity radialField
  dsimp only
  rw [hh,currentDivergence]
  ring

private theorem radialField_curve_derivative {f : Field} (X k y : ℝ)
    (hf : ContDiffAt ℝ ∞ f ![y,X,k]) :
    HasDerivAt (fun x : ℝ => f ![x,X,k]) (D 0 f ![y,X,k]) y := by
  have hc := hf.comp y (sourceCurve_smooth X k).contDiffAt
  have he : (fun x => f (Function.update ![y,X,k] 0 x))=fun x => f ![x,X,k] := by
    funext x
    congr 1
    ext i
    fin_cases i <;> simp
  have hd := slice_derivative hf 0
  rw [he] at hd
  exact (hc.differentiableAt (by simp)).hasDerivAt.congr_deriv hd

private theorem radialTrace_eq (q : XiZeroCopy) (branch : Bool) (a : ℂ) (v : ℝ)
    (image : Bool) (h target X k y : ℝ)
    (hz : 1 < invariant (h-target+y) target (if image then -y else y)) :
    sourceRadialTraceCurrent q branch a v image h target X k y=
      radialField q branch a v image h target ![y,X,k] := by
  have ht := nativeSpinTwoTrace_eq_interior image q h target ![y,X,k] hz
  exact congrArg (fun z : ℂ => S y*(E (-1) ![y,X,k]*
    (K (scalarParameter q) (thetaSeed q branch a v) ![y,X,k]*z))) ht

/-- Complete radial transfer on a truncated physical source interval. The
integrand retains the original producer, its transpose, and both angular currents. -/
theorem sourceRadialTransfer_integral (q : XiZeroCopy) (branch : Bool) (a : ℂ) (v : ℝ)
    (image : Bool) (h : Ioi (0:ℝ)) (target : Iio (0:ℝ)) (X k : ℝ)
    (cut : Ioo (sourceCharacteristic image h.val target.val) 0) :
    (∫ y in cut.val..0, radialTransferDensity q branch a v image h.val target.val X k y)=
      -sourceRadialTraceCurrent q branch a v image h.val target.val X k cut.val := by
  let f := radialField q branch a v image h.val target.val
  have hs (y : ℝ) (hy : y ∈ Set.uIcc cut.val 0) : ContDiffAt ℝ ∞ f ![y,X,k] := by
    have hy' : y ∈ Icc cut.val 0 := by simpa only [Set.uIcc_of_le cut.property.2.le] using hy
    exact radialField_smooth q branch a v image h.val target.val ![y,X,k]
      (invariant_source_interior image h target y (cut.property.1.trans_le hy'.1))
  have hd (y : ℝ) (hy : y ∈ Set.uIcc cut.val 0) :
      HasDerivAt (fun x : ℝ => f ![x,X,k]) (D 0 f ![y,X,k]) y :=
    radialField_curve_derivative X k y (hs y hy)
  have hc : ContinuousOn (fun y : ℝ => D 0 f ![y,X,k]) (Set.uIcc cut.val 0) := by
    intro y hy
    exact ((D_smooth (hs y hy) 0).continuousAt.comp
      (f := fun x : ℝ => ![x,X,k]) (sourceCurve_smooth X k).continuous.continuousAt).continuousWithinAt
  have hint : (∫ y in cut.val..0, D 0 f ![y,X,k])=f ![0,X,k]-f ![cut.val,X,k] :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  have he : (∫ y in cut.val..0, radialTransferDensity q branch a v image h.val target.val X k y)=
      ∫ y in cut.val..0, D 0 f ![y,X,k] := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hy' : y ∈ Icc cut.val 0 := by simpa only [Set.uIcc_of_le cut.property.2.le] using hy
    exact radialTransferDensity_eq q branch a v image h.val target.val X k y hy'.2
      (invariant_source_interior image h target y (cut.property.1.trans_le hy'.1))
  have hzero : f ![0,X,k]=0 := by simp [f,radialField,current,S,U,radialUnit]
  have ht := radialTrace_eq q branch a v image h.val target.val X k cut.val
    (invariant_source_interior image h target cut.val cut.property.1)
  calc
    _ = ∫ y in cut.val..0, D 0 f ![y,X,k] := he
    _ = f ![0,X,k]-f ![cut.val,X,k] := hint
    _ = -f ![cut.val,X,k] := by rw [hzero,zero_sub]
    _ = _ := congrArg Neg.neg ht.symm

/-- The radial transfer has an exact improper characteristic value. This is a
limit of the actual truncated source/transpose integrals with both angular
divergences retained; no unproved endpoint integrability is assumed. -/
theorem sourceRadialTransfer_characteristic_integral (q : XiZeroCopy) (branch : Bool)
    (a : ℂ) (v : ℝ) (image : Bool) (h : Ioi (0:ℝ)) (target : Iio (0:ℝ)) (X k : ℝ) :
    Tendsto (fun cut : ℝ => ∫ y in cut..0,
      radialTransferDensity q branch a v image h.val target.val X k y)
      (𝓝[>] (sourceCharacteristic image h.val target.val))
      (𝓝 (-(Complex.exp (-(k:ℂ))*a^(2 : ℕ)*timeOnset (2*physicalRate q branch) v*
        thetaAngularCoupling q X k*sourceCharacteristicWeight (physicalRate q branch)
          (sourceCharacteristic image h.val target.val)))) := by
  let e := sourceCharacteristic image h.val target.val
  have hm : 𝓝[>] e ≤
      𝓝[{y : ℝ | 1 < invariant (h.val-target.val+y) target.val (if image then -y else y)}] e := by
    apply nhdsWithin_mono
    intro y hy
    exact invariant_source_interior image h target y hy
  have hh := (sourceRadialCurrent_characteristic_limit q branch a v image h target X k).mono_left hm
  have hu : ∀ᶠ cut : ℝ in 𝓝[>] e, cut < 0 :=
    (eventually_lt_nhds (sourceCharacteristic_neg image h target)).filter_mono inf_le_left
  apply hh.neg.congr'
  filter_upwards [self_mem_nhdsWithin,hu] with cut hc hcut
  have hi := sourceRadialTransfer_integral q branch a v image h target X k ⟨cut,hc,hcut⟩
  rw [hi]
  exact congrArg Neg.neg (radialTrace_eq q branch a v image h.val target.val X k cut
    (invariant_source_interior image h target cut hc)).symm

private theorem sourceCutoff_shift (e : ℝ) :
    Tendsto (fun d : ℝ => e+d) (𝓝[>] (0:ℝ)) (𝓝[>] e) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [add_zero,id_eq] using!
      (tendsto_const_nhds.add (tendsto_id.mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ) from inf_le_left)))
  · filter_upwards [self_mem_nhdsWithin] with d hd
    change e < e+d
    have hp : 0 < d := hd
    linarith

/-- Complete direct-minus-image radial transfer at the two physical source
characteristics, as a single limit of original-source integrals. The two angular
divergences remain in each integrand and the full spin-two angular coupling remains
in the result. -/
theorem sourceRadialTransfer_signed_characteristic_integral (q : XiZeroCopy) (branch : Bool)
    (a : ℂ) (v : ℝ) (h : Ioi (0:ℝ)) (target : Iio (0:ℝ)) (X k : ℝ) :
    Tendsto (fun d : ℝ =>
      (∫ y in (target.val-h.val/2+d)..0,
        radialTransferDensity q branch a v false h.val target.val X k y)-
      (∫ y in (-h.val/2+d)..0,
        radialTransferDensity q branch a v true h.val target.val X k y))
      (𝓝[>] (0:ℝ))
      (𝓝 (Complex.exp (-(k:ℂ))*a^(2 : ℕ)*timeOnset (2*physicalRate q branch) v*
        thetaAngularCoupling q X k*
        (sourceCharacteristicWeight (physicalRate q branch) (-h.val/2)-
          sourceCharacteristicWeight (physicalRate q branch) (target.val-h.val/2)))) := by
  have hd := (sourceRadialTransfer_characteristic_integral q branch a v false h target X k).comp
    (sourceCutoff_shift (sourceCharacteristic false h.val target.val))
  have hi := (sourceRadialTransfer_characteristic_integral q branch a v true h target X k).comp
    (sourceCutoff_shift (sourceCharacteristic true h.val target.val))
  have hh := hd.sub hi
  simp only [Function.comp_def,sourceCharacteristic,Bool.false_eq_true,if_false,if_true] at hh
  convert hh using 1
  congr 1
  ring


private theorem unit_tendsto_horizon : Tendsto radialUnit atBot (𝓝 (1:ℝ)) := by
  have ht : Tendsto (fun x : ℝ => 2*x) atBot atBot :=
    (tendsto_const_mul_atBot_of_pos (by norm_num : (0:ℝ)<2)).mpr tendsto_id
  have he := Real.tendsto_exp_atBot.comp ht
  have hform : radialUnit=fun x => (1-Real.exp (2*x))/(1+Real.exp (2*x)) := by
    funext x
    apply (eq_div_iff (ne_of_gt (by positivity : 0 < 1+Real.exp (2*x)))).mpr
    have hh := radialUnit_one_sub x
    nlinarith
  rw [hform]
  simpa [Function.comp_def,Pi.div_apply] using!
    (tendsto_const_nhds.sub he).div (tendsto_const_nhds.add he) (by norm_num : (1:ℝ)+0 ≠ 0)

private theorem characteristicWeight_tendsto_horizon (s : ℂ) :
    Tendsto (sourceCharacteristicWeight s) atBot (𝓝 (2*D4BMLaplaceRadial.power (2*s) 2)) := by
  have hp : ContinuousAt (fun u : ℝ => D4BMLaplaceRadial.power (2*s) (1+u)) 1 :=
    (D4BMLaplaceRadial.power_derivatives (2*s) (by norm_num : 0 < (1+(1:ℝ)))).1.continuousAt.comp
      (f := fun u : ℝ => 1+u) (by fun_prop)
  have hc : ContinuousAt (fun u : ℝ => (u:ℂ)^(4 : ℕ)*(1+(u:ℂ))*
      D4BMLaplaceRadial.power (2*s) (1+u)) 1 :=
    (show ContinuousAt (fun u : ℝ => (u:ℂ)^(4 : ℕ)*(1+(u:ℂ))) 1 by fun_prop).mul hp
  have hh := hc.tendsto.comp unit_tendsto_horizon
  have hfun : sourceCharacteristicWeight s=fun y => (radialUnit y:ℂ)^(4 : ℕ)*(1+(radialUnit y:ℂ))*
      D4BMLaplaceRadial.power (2*s) (1+radialUnit y) := by
    funext y
    simp [sourceCharacteristicWeight,S,U,sourceAmplitude]
  rw [hfun]
  norm_num at hh
  simpa only [Function.comp_def] using! hh

private theorem sourceCharacteristic_tendsto (image : Bool) (target : ℝ) :
    Tendsto (fun h : ℝ => sourceCharacteristic image h target) atTop atBot := by
  have hh : Tendsto (fun h : ℝ => (-1/2:ℝ)*h) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg (by norm_num : (-1/2:ℝ)<0)).mpr tendsto_id
  apply tendsto_atBot.mpr
  intro b
  cases image
  · filter_upwards [hh.eventually (eventually_le_atBot (b-target))] with h he
    simp only [sourceCharacteristic,Bool.false_eq_true,if_false]
    linarith
  · filter_upwards [hh.eventually (eventually_le_atBot b)] with h he
    simp only [sourceCharacteristic,if_true]
    linarith

/-- At fixed original source time and fixed target radius, the complete signed
characteristic radial face decays to zero as the ingoing delay tends to infinity.
This concerns this retained radial face, not the other current components or a
time-integrated physical extinction assertion. -/
theorem sourceRadialTraceCurrent_signed_faces_tendsto_zero (q : XiZeroCopy) (branch : Bool)
    (a : ℂ) (v target X k : ℝ) :
    Tendsto (fun h : ℝ =>
      (sourceRadialTraceCurrent q branch a v false h target X k 0-
        sourceRadialTraceCurrent q branch a v false h target X k
          (sourceCharacteristic false h target))-
      (sourceRadialTraceCurrent q branch a v true h target X k 0-
        sourceRadialTraceCurrent q branch a v true h target X k
          (sourceCharacteristic true h target))) atTop (𝓝 (0:ℂ)) := by
  have hd := (characteristicWeight_tendsto_horizon (physicalRate q branch)).comp
    (sourceCharacteristic_tendsto false target)
  have hi := (characteristicWeight_tendsto_horizon (physicalRate q branch)).comp
    (sourceCharacteristic_tendsto true target)
  have hh := (hi.sub hd).const_mul
    (Complex.exp (-(k:ℂ))*a^(2 : ℕ)*timeOnset (2*physicalRate q branch) v*thetaAngularCoupling q X k)
  simp_rw [sourceRadialTraceCurrent_signed_faces]
  simpa only [Function.comp_def,sub_self,mul_zero,sourceCharacteristic,
    Bool.false_eq_true,if_false,if_true] using! hh



/-- A fractional inward cutoff on the actual direct or image source interval. -/
def fractionalSourceCutoff (image : Bool) (h target epsilon : ℝ) : ℝ :=
  (1-epsilon)*sourceCharacteristic image h target

/-- Original radial trace at a source-time dependent fractional characteristic cutoff. -/
def sourceCutoffTrace (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (image : Bool) (T target X k : ℝ) (z : ℝ × ℝ) : ℂ :=
  sourceRadialTraceCurrent q branch a z.1 image (T-z.1) target X k
    (fractionalSourceCutoff image (T-z.1) target z.2)

private theorem sourceTrace_factor (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (v : ℝ) (image : Bool) (h target X k y : ℝ) :
    sourceRadialTraceCurrent q branch a v image h target X k y =
      S y*Complex.exp (-(k:ℂ))*
        (sourceAmplitude (physicalRate q branch) 0 a 1 y*timeOnset (2*physicalRate q branch) v)*
        ((7*scalarParameter q-2)/8*fullSquarePotential q ![X,Real.exp k]-
          (1/4:ℂ)*scalarLaplacian (fullSquarePotential q) ![X,Real.exp k])*
        nativeSpinTwoTrace image q h target ![y,X,k] := by
  unfold sourceRadialTraceCurrent current
  simp only [Matrix.cons_val_zero]
  rw [K,thetaSeed_laplacian]
  simp only [thetaSeed,seed,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    E,neg_one_mul,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_succ]
  ring

private theorem nativeTrace_joint_continuousAt (q : XiZeroCopy) (image : Bool)
    (target X k : ℝ) (z : ℝ × ℝ × ℝ)
    (hz : 0 < invariant (z.2.1-target+z.2.2) target (if image then -z.2.2 else z.2.2)) :
    ContinuousAt (fun z : ℝ × ℝ × ℝ =>
      nativeSpinTwoTrace image q z.2.1 target ![z.2.2,X,k]) z := by
  have hi : Continuous (fun z : ℝ × ℝ × ℝ =>
      invariant (z.2.1-target+z.2.2) target (if image then -z.2.2 else z.2.2)) := by
    cases image <;> simp only [Bool.false_eq_true,if_false,if_true]
    all_goals unfold invariant
    all_goals apply Continuous.div <;> try fun_prop
    all_goals intro z; exact mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'
  have ha : ContinuousAt (fun z : ℝ × ℝ × ℝ =>
      Real.arcosh (invariant (z.2.1-target+z.2.2) target (if image then -z.2.2 else z.2.2))) z := by
    unfold Real.arcosh
    apply (hi.continuousAt.add ((hi.continuousAt.pow 2).sub continuousAt_const).sqrt).log
    exact ne_of_gt (add_pos_of_pos_of_nonneg hz (Real.sqrt_nonneg _))
  have hp : ContinuousAt (fun z : ℝ × ℝ × ℝ =>
      (![Real.arcosh (invariant (z.2.1-target+z.2.2) target
        (if image then -z.2.2 else z.2.2)),X,k] : Point)) z := by
    apply continuousAt_pi.mpr
    intro i
    fin_cases i
    · simpa using! ha
    · exact continuousAt_const
    · exact continuousAt_const
  have he : (fun z : ℝ × ℝ × ℝ => nativeSpinTwoTrace image q z.2.1 target ![z.2.2,X,k]) =
      fun z => circleSpinTwo q ![Real.arcosh (invariant (z.2.1-target+z.2.2) target
        (if image then -z.2.2 else z.2.2)),X,k] := by
    funext z
    rw [nativeSpinTwoTrace_eq_circle]
    congr 1
    ext i
    fin_cases i <;> simp [freeze]
  rw [he]
  exact (circleSpinTwo_smooth q _).continuousAt.comp hp

private theorem sourceTrace_joint_continuousAt (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (image : Bool) (target X k : ℝ) (z : ℝ × ℝ × ℝ)
    (hz : 0 < invariant (z.2.1-target+z.2.2) target (if image then -z.2.2 else z.2.2)) :
    ContinuousAt (fun z : ℝ × ℝ × ℝ =>
      sourceRadialTraceCurrent q branch a z.1 image z.2.1 target X k z.2.2) z := by
  have hs : Continuous (fun z : ℝ × ℝ × ℝ => S z.2.2) :=
    S_smooth.continuous.comp (continuous_snd.comp continuous_snd)
  have ha : Continuous (fun z : ℝ × ℝ × ℝ => sourceAmplitude (physicalRate q branch) 0 a 1 z.2.2) :=
    (amplitude_smooth _ _ _ _).continuous.comp (continuous_snd.comp continuous_snd)
  have ho : Continuous (fun z : ℝ × ℝ × ℝ => timeOnset (2*physicalRate q branch) z.1) :=
    (continuous_iff_continuousAt.mpr (fun v => (timeOnset_hasDerivAt _ v).continuousAt)).comp continuous_fst
  simp_rw [sourceTrace_factor]
  exact (((hs.continuousAt.mul continuousAt_const).mul (ha.mul ho).continuousAt).mul
    continuousAt_const).mul (nativeTrace_joint_continuousAt q image target X k z hz)

private theorem invariant_source_closed (image : Bool) {h target y : ℝ}
    (hh : 0 ≤ h) (hx : target ≤ 0) (hy : sourceCharacteristic image h target ≤ y) :
    1 ≤ invariant (h-target+y) target (if image then -y else y) := by
  have ha : |target-(if image then -y else y)| ≤ h-target+y := by
    rw [abs_le]
    cases image <;> simp only [sourceCharacteristic,Bool.false_eq_true,if_false,if_true] at hy ⊢
    all_goals constructor <;> linarith
  have ht : 0 ≤ h-target+y := (abs_nonneg _).trans ha
  have hc : Real.cosh (target-(if image then -y else y)) ≤ Real.cosh (h-target+y) := by
    apply Real.cosh_le_cosh.mpr
    rwa [abs_of_nonneg ht]
  rw [Real.cosh_sub] at hc
  unfold invariant
  apply (le_div_iff₀ (mul_pos (Real.cosh_pos _) (Real.cosh_pos _))).mpr
  linarith

/-- Joint source-time/cutoff continuity of the original radial trace, including
zero delay and both characteristic contacts. No trace regularity is assumed. -/
theorem sourceCutoffTrace_continuousOn (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (image : Bool) (T : Ici (0:ℝ)) (target : Iio (0:ℝ)) (X k : ℝ) :
    ContinuousOn (sourceCutoffTrace q branch a image T.val target.val X k)
      (Icc (0:ℝ) T.val ×ˢ Icc (0:ℝ) (1/2)) := by
  have hc : Continuous (fun z : ℝ × ℝ => fractionalSourceCutoff image (T.val-z.1) target.val z.2) := by
    cases image <;> simp only [fractionalSourceCutoff,sourceCharacteristic,Bool.false_eq_true,if_false,if_true]
    all_goals fun_prop
  intro z hz
  have hh : 0 ≤ T.val-z.1 := sub_nonneg.mpr hz.1.2
  have hx : target.val ≤ 0 := target.property.le
  have he : sourceCharacteristic image (T.val-z.1) target.val ≤ 0 := by
    cases image <;> simp only [sourceCharacteristic,Bool.false_eq_true,if_false,if_true]
    all_goals linarith
  have hcut : sourceCharacteristic image (T.val-z.1) target.val ≤
      fractionalSourceCutoff image (T.val-z.1) target.val z.2 := by
    unfold fractionalSourceCutoff
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hz.2.1 he]
  have hinv := invariant_source_closed image hh hx hcut
  have hp : Continuous (fun z : ℝ × ℝ => (z.1,T.val-z.1,
      fractionalSourceCutoff image (T.val-z.1) target.val z.2)) :=
    continuous_fst.prodMk ((continuous_const.sub continuous_fst).prodMk hc)
  exact ((sourceTrace_joint_continuousAt q branch a image target.val X k
    (z.1,T.val-z.1,fractionalSourceCutoff image (T.val-z.1) target.val z.2)
    (lt_of_lt_of_le (by norm_num) hinv)).comp (f := fun z : ℝ × ℝ =>
      (z.1,T.val-z.1,fractionalSourceCutoff image (T.val-z.1) target.val z.2))
    hp.continuousAt).continuousWithinAt

end RHTower.D4BMCommonSourceGreen
