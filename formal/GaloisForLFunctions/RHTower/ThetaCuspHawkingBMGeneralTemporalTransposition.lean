import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeGoursat
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Prod

/-!
General smooth compact time/radius tests for the original full-theta causal
Dirichlet kernel. The source-based null chart is transported with its actual
area Jacobian, and the physical principal wave operator is obtained from
actual derivatives. The complete angular action, both causal supports and
the original half-factor are retained. The exact source-minus-image vertex
formula reduces to the original source with coefficient one on the physical
negative radial half-plane.

This is a kernel-level temporal weak equation. The admitted infinite future
response, retained lift/cap equations and full physical metric/QNM matching
still require their own identifications. No RH or extinction claim is made.
-/

open MeasureTheory Set Filter Topology
namespace RHTower.D4BMGeneralTemporalTransposition
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMNativeCircle D4BMCausalKernel D4BMModularCore D4BMHorizon
open scoped ContDiff ENNReal
noncomputable section
set_option autoImplicit false

private theorem primitive_pair (f phi phip : ℝ → ℂ) (U : ℝ)
    (hf : Continuous f) (hp : Continuous phi) (hd : Continuous phip)
    (hder : ∀ u, HasDerivAt phi (phip u) u) (hU : phi U=0) :
    (∫ u in (0:ℝ)..U, (∫ a in (0:ℝ)..u, f a)*phip u) =
      -(∫ u in (0:ℝ)..U, f u*phi u) := by
  have hF (u : ℝ) : HasDerivAt (fun v => ∫ a in (0:ℝ)..v, f a) (f u) u :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 u)
      (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt
  have hc : Continuous (fun v => ∫ a in (0:ℝ)..v, f a) :=
    continuous_iff_continuousAt.mpr (fun v => (hF v).continuousAt)
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hc.continuousOn hp.continuousOn (fun u _ => hF u) (fun u _ => hder u)
    (hf.intervalIntegrable 0 U) (hd.intervalIntegrable 0 U)
  simpa only [hU,mul_zero,intervalIntegral.integral_same,zero_mul,sub_self,zero_sub] using h


private theorem double_primitive_continuous (F : ℝ × ℝ → ℂ) (hF : Continuous F) :
    Continuous (fun p : ℝ × ℝ => ∫ a in (0:ℝ)..p.1, ∫ b in (0:ℝ)..p.2, F (a,b)) := by
  have hi : Continuous (fun p : (ℝ × ℝ) × ℝ => ∫ b in (0:ℝ)..p.1.2, F (p.2,b)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) (a₀ := 0)
      (f := fun p : (ℝ × ℝ) × ℝ => fun b => F (p.2,b))
      (hF.comp (continuous_fst.snd.prodMk continuous_snd)) continuous_fst.snd
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := 0)
    (f := fun p : ℝ × ℝ => fun a => ∫ b in (0:ℝ)..p.2, F (a,b)) hi continuous_fst

private theorem rectangle_swap (F : ℝ × ℝ → ℂ) (hF : Continuous F) (U V : ℝ) :
    (∫ u in (0:ℝ)..U, ∫ v in (0:ℝ)..V, F (u,v)) =
      ∫ v in (0:ℝ)..V, ∫ u in (0:ℝ)..U, F (u,v) := by
  apply intervalIntegral_intervalIntegral_swap
  exact hF.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc) |>.mono_set
    (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)

private theorem double_primitive_joint_pair (F eta etau etauv : ℝ × ℝ → ℂ)
    (U V : ℝ) (hF : Continuous F) (he : Continuous eta)
    (heu : Continuous etau) (heuv : Continuous etauv)
    (hdu : ∀ u v, HasDerivAt (fun a => eta (a,v)) (etau (u,v)) u)
    (hduv : ∀ u v, HasDerivAt (fun b => etau (u,b)) (etauv (u,v)) v)
    (hU : ∀ v, eta (U,v)=0) (hV : ∀ u, etau (u,V)=0) :
    (∫ u in (0:ℝ)..U, ∫ v in (0:ℝ)..V,
      (∫ a in (0:ℝ)..u, ∫ b in (0:ℝ)..v, F (a,b))*etauv (u,v)) =
      ∫ u in (0:ℝ)..U, ∫ v in (0:ℝ)..V, F (u,v)*eta (u,v) := by
  have c1 (u : ℝ) : Continuous (fun b => ∫ a in (0:ℝ)..u, F (a,b)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun b a : ℝ => F (a,b))
      (hF.comp (continuous_snd.prodMk continuous_fst)) 0 u
  have one (u : ℝ) :
      (∫ v in (0:ℝ)..V, (∫ a in (0:ℝ)..u, ∫ b in (0:ℝ)..v, F (a,b))*etauv (u,v)) =
        -(∫ v in (0:ℝ)..V, (∫ a in (0:ℝ)..u, F (a,v))*etau (u,v)) := by
    simp_rw [rectangle_swap F hF]
    exact primitive_pair (fun b => ∫ a in (0:ℝ)..u, F (a,b))
      (fun b => etau (u,b)) (fun b => etauv (u,b)) V (c1 u)
      (heu.comp (continuous_const.prodMk continuous_id))
      (heuv.comp (continuous_const.prodMk continuous_id)) (hduv u) (hV u)
  simp_rw [one]
  rw [intervalIntegral.integral_neg]
  have hp : Continuous (fun p : ℝ × ℝ => (∫ a in (0:ℝ)..p.1, F (a,p.2))*etau p) := by
    have hh := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) (a₀ := 0)
      (f := fun p : ℝ × ℝ => fun a => F (a,p.2))
      (hF.comp (continuous_snd.prodMk continuous_fst.snd)) continuous_fst
    exact hh.mul heu
  rw [rectangle_swap _ hp U V]
  have two (v : ℝ) :
      (∫ u in (0:ℝ)..U, (∫ a in (0:ℝ)..u, F (a,v))*etau (u,v)) =
        -(∫ u in (0:ℝ)..U, F (u,v)*eta (u,v)) :=
    primitive_pair (fun a => F (a,v)) (fun a => eta (a,v)) (fun a => etau (a,v)) U
      (hF.comp (continuous_id.prodMk continuous_const))
      (he.comp (continuous_id.prodMk continuous_const))
      (heu.comp (continuous_id.prodMk continuous_const)) (fun u => hdu u v) (hU v)
  simp_rw [two]
  rw [intervalIntegral.integral_neg,neg_neg]
  exact (rectangle_swap (fun p => F p*eta p) (hF.mul he) U V).symm

private theorem vertex_primitive_joint_pair (Q : ℂ) (F eta etau etauv : ℝ × ℝ → ℂ)
    (U V : ℝ) (hF : Continuous F) (he : Continuous eta)
    (heu : Continuous etau) (heuv : Continuous etauv)
    (hdu : ∀ u v, HasDerivAt (fun a => eta (a,v)) (etau (u,v)) u)
    (hduv : ∀ u v, HasDerivAt (fun b => etau (u,b)) (etauv (u,v)) v)
    (hU : ∀ v, eta (U,v)=0) (hV : ∀ u, etau (u,V)=0) :
    (∫ u in (0:ℝ)..U, ∫ v in (0:ℝ)..V,
      (Q+∫ a in (0:ℝ)..u, ∫ b in (0:ℝ)..v, F (a,b))*etauv (u,v)) =
      Q*eta (0,0)+∫ u in (0:ℝ)..U, ∫ v in (0:ℝ)..V, F (u,v)*eta (u,v) := by
  have h0 : Continuous (fun p : ℝ × ℝ => Q*etauv p) := continuous_const.mul heuv
  have h1 : Continuous (fun p : ℝ × ℝ =>
      (∫ a in (0:ℝ)..p.1, ∫ b in (0:ℝ)..p.2, F (a,b))*etauv p) :=
    (double_primitive_continuous F hF).mul heuv
  simp_rw [add_mul]
  have split (u : ℝ) :
      (∫ v in (0:ℝ)..V, Q*etauv (u,v)+(∫ a in (0:ℝ)..u, ∫ b in (0:ℝ)..v, F (a,b))*etauv (u,v)) =
      (∫ v in (0:ℝ)..V, Q*etauv (u,v))+
        ∫ v in (0:ℝ)..V, (∫ a in (0:ℝ)..u, ∫ b in (0:ℝ)..v, F (a,b))*etauv (u,v) :=
    intervalIntegral.integral_add
    ((h0.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 V)
    ((h1.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 V)
  simp_rw [split]
  rw [intervalIntegral.integral_add
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun u v : ℝ => Q*etauv (u,v)) h0 0 V).intervalIntegrable 0 U)
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun u v : ℝ => (∫ a in (0:ℝ)..u, ∫ b in (0:ℝ)..v, F (a,b))*etauv (u,v)) h1 0 V).intervalIntegrable 0 U),
    double_primitive_joint_pair F eta etau etauv U V hF he heu heuv hdu hduv hU hV]
  apply congrArg (fun z : ℂ => z+∫ u in (0:ℝ)..U, ∫ v in (0:ℝ)..V, F (u,v)*eta (u,v))
  have hv (u : ℝ) : (∫ v in (0:ℝ)..V, etauv (u,v)) = -etau (u,0) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hduv u v)
      ((heuv.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 V),hV u,zero_sub]
  simp_rw [intervalIntegral.integral_const_mul,hv]
  rw [intervalIntegral.integral_neg,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hdu u 0)
      ((heu.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 U),hU 0]
  ring

private theorem laplace_circle_continuous (q : XiZeroCopy) (X k : ℝ) :
    Continuous (fun p : ℝ × ℝ =>
      scalarLaplacian (fullSquarePotential q) (logCircle p.1 p.2 X k)) := by
  have hp (p : ℝ × ℝ) : 0 < logCircle p.1 p.2 X k 1 :=
    mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have he : (fun p : ℝ × ℝ => scalarLaplacian (fullSquarePotential q) (logCircle p.1 p.2 X k)) =
      fun p => (logCircle p.1 p.2 X k 1:ℂ)^2 *
        (coordDeriv 0 (coordDeriv 0 (fullSquarePotential q)) (logCircle p.1 p.2 X k)+
         coordDeriv 1 (coordDeriv 1 (fullSquarePotential q)) (logCircle p.1 p.2 X k)) := by
    funext p
    exact scalarLaplacian_eq _ _ (hp p)
  rw [he]
  apply continuous_iff_continuousAt.mpr
  intro p
  have hs : ContDiffAt ℝ ∞ (fullSquarePotential q) (logCircle p.1 p.2 X k) :=
    contDiffAt_infty.mpr (fun n => fullSquarePotential_smooth q _ (hp p) n)
  have hj (i : Fin 2) : ContinuousAt (coordDeriv i (coordDeriv i (fullSquarePotential q)))
      (logCircle p.1 p.2 X k) :=
    (coordDeriv_contDiffAt (m := ∞)
      (by simpa using coordDeriv_contDiffAt (m := ∞) (by simpa using hs) i) i).continuousAt
  have hc : Continuous (fun r : ℝ × ℝ => logCircle r.1 r.2 X k) := by
    have hd : Continuous (fun r : ℝ × ℝ => denominator r.1 r.2) := by
      unfold denominator
      fun_prop
    have hn (r : ℝ × ℝ) : denominator r.1 r.2 ≠ 0 := (denominator_pos _ _).ne'
    have ho := ((Real.continuous_sinh.comp continuous_fst).mul
      (Real.continuous_sin.comp continuous_snd)).div hd hn
    have hh := (continuous_const (y := (1:ℝ))).div hd hn
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_const.add (continuous_const.mul ho)
    · exact continuous_const.mul hh
  exact ((Complex.continuous_ofReal.comp ((continuous_apply 1).comp hc)).pow 2).continuousAt.mul
    (((hj 0).comp_of_eq (hc.continuousAt (x := p)) rfl).add
      ((hj 1).comp_of_eq (hc.continuousAt (x := p)) rfl))

private theorem angularAction_closed_continuous (q : XiZeroCopy) (X k : ℝ) :
    Continuous (fun z => angularAction q (max 1 z) X k) := by
  have hM : Continuous (fun d => average (fun theta =>
      scalarLaplacian (fullSquarePotential q) (logCircle d theta X k))) := by
    have he : (fun d => average (fun theta => scalarLaplacian (fullSquarePotential q) (logCircle d theta X k))) =
        fun d => (1/(2*Real.pi:ℂ))*∫ theta in (0:ℝ)..2*Real.pi,
          scalarLaplacian (fullSquarePotential q) (logCircle d theta X k) := by
      funext d
      rw [intervalIntegral.integral_of_le (by positivity)]
      rfl
    rw [he]
    exact continuous_const.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun d theta : ℝ => scalarLaplacian (fullSquarePotential q) (logCircle d theta X k))
        (laplace_circle_continuous q X k) 0 (2*Real.pi))
  have hR : Continuous (fun z : ℝ => Real.arcosh (max 1 z)) :=
    Real.continuousOn_arcosh.comp_continuous (continuous_const.max continuous_id)
      (fun z => le_max_left 1 z)
  convert hM.comp hR using 1
  funext z
  exact mean_laplacian_commutes q (Real.arcosh (max 1 z)) X k

/-- Full native Riemann kernel in null distances from its source vertex. -/
def coneKernel (q : XiZeroCopy) (y u v X k : ℝ) : ℂ :=
  nativeRiemannKernel q ((u+v)/2) (y+(u-v)/2) y X k

private def closedConeAction (q : XiZeroCopy) (y X k : ℝ) (p : ℝ × ℝ) : ℂ :=
  angularAction q (max 1 (invariant ((p.1+p.2)/2) (y+(p.1-p.2)/2) y)) X k /
    (4*(Real.cosh (y+(p.1-p.2)/2):ℂ)^2)

private theorem closedConeAction_continuous (q : XiZeroCopy) (y X k : ℝ) :
    Continuous (closedConeAction q y X k) := by
  have hi : Continuous (fun p : ℝ × ℝ => invariant ((p.1+p.2)/2) (y+(p.1-p.2)/2) y) := by
    unfold invariant
    apply Continuous.div <;> try fun_prop
    intro p
    exact mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'
  apply Continuous.div ((angularAction_closed_continuous q X k).comp hi) (by fun_prop)
  intro p
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'))

private theorem cone_inside (y u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |(y+(u-v)/2)-y| ≤ (u+v)/2 := by
  rw [abs_le]
  constructor <;> linarith

private theorem coneKernel_primitive (q : XiZeroCopy) (y u v X k : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    coneKernel q y u v X k = fullSquarePotential q ![X,Real.exp k] +
      ∫ a in (0:ℝ)..u, ∫ b in (0:ℝ)..v, closedConeAction q y X k (a,b) := by
  have h := nativeRiemannKernel_goursat q ⟨(u+v)/2,y+(u-v)/2,y,cone_inside y u v hu hv⟩ X k
  change coneKernel q y u v X k = _ at h
  rw [show (u+v)/2+(y+(u-v)/2)-y=u by ring,
    show (u+v)/2-(y+(u-v)/2)+y=v by ring] at h
  rw [h]
  apply congrArg (fun z : ℂ => fullSquarePotential q ![X,Real.exp k]+z)
  apply intervalIntegral.integral_congr
  intro a ha
  apply intervalIntegral.integral_congr
  intro b hb
  dsimp only
  have ha0 : 0 ≤ a := (show a ∈ Icc 0 u by simpa [uIcc_of_le hu] using ha).1
  have hb0 : 0 ≤ b := (show b ∈ Icc 0 v by simpa [uIcc_of_le hv] using hb).1
  simp only [closedConeAction,max_eq_right (invariant_causal ⟨_,_,_,cone_inside y a b ha0 hb0⟩)]

/-- The actual full-theta cone kernel against a general joint null test. -/
theorem coneKernel_joint_transposition (q : XiZeroCopy) (y X k U V : ℝ)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (eta etau etauv : ℝ × ℝ → ℂ)
    (he : Continuous eta) (heu : Continuous etau) (heuv : Continuous etauv)
    (hdu : ∀ u v, HasDerivAt (fun a => eta (a,v)) (etau (u,v)) u)
    (hduv : ∀ u v, HasDerivAt (fun b => etau (u,b)) (etauv (u,v)) v)
    (heU : ∀ v, eta (U,v)=0) (heV : ∀ u, etau (u,V)=0) :
    (∫ u in (0:ℝ)..U, ∫ v in (0:ℝ)..V, coneKernel q y u v X k*etauv (u,v)) =
      fullSquarePotential q ![X,Real.exp k]*eta (0,0) +
      ∫ u in (0:ℝ)..U, ∫ v in (0:ℝ)..V,
        angularAction q (invariant ((u+v)/2) (y+(u-v)/2) y) X k /
          (4*(Real.cosh (y+(u-v)/2):ℂ)^2)*eta (u,v) := by
  have h := vertex_primitive_joint_pair (fullSquarePotential q ![X,Real.exp k])
    (closedConeAction q y X k) eta etau etauv U V
    (closedConeAction_continuous q y X k) he heu heuv hdu hduv heU heV
  have left : (∫ u in (0:ℝ)..U, ∫ v in (0:ℝ)..V, coneKernel q y u v X k*etauv (u,v)) =
      ∫ u in (0:ℝ)..U, ∫ v in (0:ℝ)..V,
        (fullSquarePotential q ![X,Real.exp k]+
          ∫ a in (0:ℝ)..u, ∫ b in (0:ℝ)..v, closedConeAction q y X k (a,b))*etauv (u,v) := by
    apply intervalIntegral.integral_congr
    intro u hu
    apply intervalIntegral.integral_congr
    intro v hv
    dsimp only
    rw [coneKernel_primitive q y u v X k
      (show u ∈ Icc 0 U by simpa [uIcc_of_le hU] using hu).1
      (show v ∈ Icc 0 V by simpa [uIcc_of_le hV] using hv).1]
  rw [left,h]
  apply congrArg (fun z : ℂ => fullSquarePotential q ![X,Real.exp k]*eta (0,0)+z)
  apply intervalIntegral.integral_congr
  intro u hu
  apply intervalIntegral.integral_congr
  intro v hv
  dsimp only
  have hu0 := (show u ∈ Icc 0 U by simpa [uIcc_of_le hU] using hu).1
  have hv0 := (show v ∈ Icc 0 V by simpa [uIcc_of_le hV] using hv).1
  simp only [closedConeAction,max_eq_right (invariant_causal ⟨_,_,_,cone_inside y u v hu0 hv0⟩)]

/-- Physical target event in the past cone of the source event `(s,y)`. -/
def pastVertex (s y : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (s-(p.1+p.2)/2,y+(p.1-p.2)/2)

/-- Actual directional derivative in the time/radius plane. -/
def eventDir (v : ℝ × ℝ) (phi : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  fderiv ℝ phi p v

/-- The physical principal wave operator, with no spectral substitution. -/
def eventWave (phi : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  eventDir (1,0) (eventDir (1,0) phi) p - eventDir (0,1) (eventDir (0,1) phi) p

private theorem eventDir_smooth {phi : ℝ × ℝ → ℂ} (hp : ContDiff ℝ ∞ phi) (v : ℝ × ℝ) :
    ContDiff ℝ ∞ (eventDir v phi) :=
  (hp.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private theorem eventDir_second {phi : ℝ × ℝ → ℂ} (hp : ContDiff ℝ ∞ phi)
    (v w p : ℝ × ℝ) :
    eventDir v (eventDir w phi) p = fderiv ℝ (fderiv ℝ phi) p v w := by
  unfold eventDir
  rw [fderiv_clm_apply ((hp.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p)
    (differentiableAt_const _)]
  simp

private theorem null_mixed_eq_wave {phi : ℝ × ℝ → ℂ} (hp : ContDiff ℝ ∞ phi) (p : ℝ × ℝ) :
    eventDir (-1/2,-1/2) (eventDir (-1/2,1/2) phi) p = eventWave phi p/4 := by
  rw [eventDir_second hp]
  unfold eventWave
  rw [eventDir_second hp,eventDir_second hp]
  have hs := (hp.contDiffAt (x := p)).isSymmSndFDerivAt
    (by norm_num; exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) (1,0) (0,1)
  have hv : ((-1/2,-1/2) : ℝ × ℝ) = (-1/2:ℝ) • (1,0)+(-1/2:ℝ) • (0,1) := by ext <;> norm_num
  have hw : ((-1/2,1/2) : ℝ × ℝ) = (-1/2:ℝ) • (1,0)+(1/2:ℝ) • (0,1) := by ext <;> norm_num
  rw [hv,hw]
  simp only [map_add,map_smul,add_apply,smul_apply,
    Complex.real_smul,Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_one,
    Complex.ofReal_ofNat]
  rw [hs]
  ring

private theorem pastVertex_u (s y u v : ℝ) :
    HasDerivAt (fun a => pastVertex s y (a,v)) (-1/2,1/2) u := by
  have h1 := (((hasDerivAt_id u).add_const v).div_const 2).const_sub s
  have h2 := (((hasDerivAt_id u).sub_const v).div_const 2).const_add y
  simpa [pastVertex,neg_div] using h1.prodMk h2

private theorem pastVertex_v (s y u v : ℝ) :
    HasDerivAt (fun b => pastVertex s y (u,b)) (-1/2,-1/2) v := by
  have h1 := (((hasDerivAt_id v).const_add u).div_const 2).const_sub s
  have h2 := (((hasDerivAt_id v).const_sub u).div_const 2).const_add y
  simpa [pastVertex,neg_div] using h1.prodMk h2

private def pastChart (s y : ℝ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun := pastVertex s y
  invFun := fun p => (s-p.1+p.2-y,s-p.1-p.2+y)
  left_inv p := by ext <;> simp only [pastVertex] <;> ring
  right_inv p := by ext <;> simp only [pastVertex] <;> ring
  continuous_toFun := by unfold pastVertex; fun_prop
  continuous_invFun := by fun_prop

private theorem past_test_derivatives (s y : ℝ) (phi : ℝ × ℝ → ℂ)
    (hp : ContDiff ℝ ∞ phi) :
    (∀ u v, HasDerivAt (fun a => phi (pastVertex s y (a,v)))
      (eventDir (-1/2,1/2) phi (pastVertex s y (u,v))) u) ∧
    (∀ u v, HasDerivAt (fun b => eventDir (-1/2,1/2) phi (pastVertex s y (u,b)))
      (eventWave phi (pastVertex s y (u,v))/4) v) := by
  constructor
  · intro u v
    exact ((hp.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt u (pastVertex_u s y u v))
  · intro u v
    have h := (((eventDir_smooth hp (-1/2,1/2)).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt
      v (pastVertex_v s y u v))
    change HasDerivAt _ (eventDir (-1/2,-1/2) (eventDir (-1/2,1/2) phi) _) v at h
    rw [null_mixed_eq_wave hp] at h
    exact h

/-- The actual source-based null chart has area Jacobian `1/2`. -/
theorem pastVertex_volume (s y : ℝ) :
    Measure.map (pastVertex s y) volume = (2:ℝ≥0∞) • (volume : Measure (ℝ × ℝ)) := by
  let m : Measure ℝ := volume
  let mm : Measure (ℝ × ℝ) := m.prod m
  have ha : MeasurePreserving (fun p : ℝ × ℝ => (p.1+p.2,p.2)) mm mm := by
    exact measurePreserving_add_prod m m
  have hb : MeasurePreserving (fun p : ℝ × ℝ => ((-1/2)*p.1,p.2)) mm ((2:ℝ≥0∞) • mm) := by
    refine ⟨by fun_prop, ?_⟩
    change Measure.map (Prod.map (fun u : ℝ => (-1/2)*u) id) (m.prod m) = _
    rw [← Measure.map_prod_map m m (by fun_prop) measurable_id,Measure.map_id]
    have hr : Measure.map (fun u : ℝ => (-1/2)*u) m = (2:ℝ≥0∞) • m := by
      have h := Measure.map_addHaar_smul m (r := (-1/2:ℝ)) (by norm_num)
      norm_num at h
      simpa only [neg_div,neg_mul] using h
    rw [hr,Measure.prod_smul_left]
  have hn : MeasurePreserving (fun p : ℝ × ℝ => (p.1,-p.2)) mm mm :=
    (MeasurePreserving.id m).prod (Measure.measurePreserving_neg m)
  have hh : MeasurePreserving (fun p : ℝ × ℝ => (p.1,-p.1-p.2)) mm mm := by
    convert hn.comp (measurePreserving_prod_add m m) using 1
    ext p <;> simp only [Function.comp_def]
    ring
  have hh2 : MeasurePreserving (fun p : ℝ × ℝ => (p.1,-p.1-p.2))
      ((2:ℝ≥0∞) • mm) ((2:ℝ≥0∞) • mm) :=
    ⟨hh.measurable, by rw [Measure.map_smul,hh.map_eq]⟩
  have ht := measurePreserving_add_left ((2:ℝ≥0∞) • mm) (s,y)
  have h := ht.comp (hh2.comp (hb.comp ha))
  have hp : MeasurePreserving (pastVertex s y) mm ((2:ℝ≥0∞) • mm) := by
    convert h using 1
    funext p
    ext <;> simp only [Function.comp_apply,Prod.fst_add,Prod.snd_add,pastVertex] <;> ring
  simpa only [mm,m,← Measure.volume_eq_prod] using hp.map_eq

/-- Change of variables for the physical source chart, including its exact area factor. -/
theorem integral_pastVertex (s y : ℝ) (F : ℝ × ℝ → ℂ) :
    (∫ p : ℝ × ℝ, F (pastVertex s y p)) = 2*(∫ p : ℝ × ℝ, F p) := by
  have h := (pastChart s y).toMeasurableEquiv.measurableEmbedding.integral_map F (μ := volume)
  change (∫ p : ℝ × ℝ, F p ∂Measure.map (pastVertex s y) volume) = _ at h
  dsimp only [pastChart] at h
  rw [pastVertex_volume,integral_smul_measure] at h
  change (2:ℝ) • (∫ p : ℝ × ℝ, F p) = ∫ p : ℝ × ℝ, F (pastVertex s y p) at h
  simpa only [Complex.real_smul,Complex.ofReal_ofNat] using h.symm


private theorem quadrant_eq_box (F : ℝ × ℝ → ℂ) (hF : Continuous F) (R : ℝ)
    (hR : 0 ≤ R) (hzero : ∀ p : ℝ × ℝ, R ≤ ‖p‖ → F p=0) :
    (∫ p in Ici (0:ℝ) ×ˢ Ici (0:ℝ), F p) =
      ∫ u in (0:ℝ)..R, ∫ v in (0:ℝ)..R, F (u,v) := by
  have he : (Ici (0:ℝ) ×ˢ Ici (0:ℝ)).indicator F =
      (Icc (0:ℝ) R ×ˢ Icc (0:ℝ) R).indicator F := by
    funext p
    by_cases hq : p ∈ Ici (0:ℝ) ×ˢ Ici (0:ℝ)
    · by_cases hb : p ∈ Icc (0:ℝ) R ×ˢ Icc (0:ℝ) R
      · simp only [Set.indicator_of_mem hq,Set.indicator_of_mem hb]
      · have hn : R ≤ ‖p‖ := by
          have hh : R < p.1 ∨ R < p.2 := by
            by_contra! hh
            exact hb ⟨⟨hq.1,hh.1⟩,⟨hq.2,hh.2⟩⟩
          rcases hh with hh | hh
          · exact hh.le.trans ((le_abs_self _).trans (norm_fst_le p))
          · exact hh.le.trans ((le_abs_self _).trans (norm_snd_le p))
        simp only [Set.indicator_of_mem hq,Set.indicator_of_notMem hb,hzero p hn]
    · have hb : p ∉ Icc (0:ℝ) R ×ˢ Icc (0:ℝ) R := fun h => hq ⟨h.1.1,h.2.1⟩
      simp only [Set.indicator_of_notMem hq,Set.indicator_of_notMem hb]
  rw [← integral_indicator (measurableSet_Ici.prod measurableSet_Ici),he,
    integral_indicator (measurableSet_Icc.prod measurableSet_Icc),Measure.volume_eq_prod]
  rw [setIntegral_prod F
    (hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))]
  simp_rw [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hR]

private theorem rectangle_sub (F G : ℝ × ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (U V : ℝ) :
    (∫ u in (0:ℝ)..U, ∫ v in (0:ℝ)..V, F (u,v)-G (u,v)) =
      (∫ u in (0:ℝ)..U, ∫ v in (0:ℝ)..V, F (u,v))-
        ∫ u in (0:ℝ)..U, ∫ v in (0:ℝ)..V, G (u,v) := by
  have hi (u : ℝ) : (∫ v in (0:ℝ)..V, F (u,v)-G (u,v)) =
      (∫ v in (0:ℝ)..V, F (u,v))-(∫ v in (0:ℝ)..V, G (u,v)) :=
    intervalIntegral.integral_sub
    ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable (μ := volume) 0 V)
    ((hG.comp (continuous_const.prodMk continuous_id)).intervalIntegrable (μ := volume) 0 V)
  simp_rw [hi]
  exact intervalIntegral.integral_sub
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun u v : ℝ => F (u,v)) hF 0 V).intervalIntegrable 0 U)
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun u v : ℝ => G (u,v)) hG 0 V).intervalIntegrable 0 U)

private def closedKernel (q : XiZeroCopy) (y X k : ℝ) (p : ℝ × ℝ) : ℂ :=
  fullSquarePotential q ![X,Real.exp k]+
    ∫ a in (0:ℝ)..p.1, ∫ b in (0:ℝ)..p.2, closedConeAction q y X k (a,b)

private theorem closedKernel_continuous (q : XiZeroCopy) (y X k : ℝ) :
    Continuous (closedKernel q y X k) :=
  continuous_const.add (double_primitive_continuous _ (closedConeAction_continuous q y X k))

private def nullTestResidual (q : XiZeroCopy) (s y X k : ℝ)
    (phi : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  closedKernel q y X k p * (eventWave phi (pastVertex s y p)/4) -
    closedConeAction q y X k p * phi (pastVertex s y p)

private theorem residual_regular (q : XiZeroCopy) (s y X k : ℝ) (phi : ℝ × ℝ → ℂ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    Continuous (nullTestResidual q s y X k phi) ∧
      HasCompactSupport (nullTestResidual q s y X k phi) := by
  have hw : ContDiff ℝ ∞ (eventWave phi) :=
    (eventDir_smooth (eventDir_smooth hp (1,0)) (1,0)).sub
      (eventDir_smooth (eventDir_smooth hp (0,1)) (0,1))
  have hwc : HasCompactSupport (eventWave phi) :=
    ((hc.fderiv_apply ℝ (1,0)).fderiv_apply ℝ (1,0)).sub
      ((hc.fderiv_apply ℝ (0,1)).fderiv_apply ℝ (0,1))
  constructor
  · exact ((closedKernel_continuous q y X k).mul
      ((hw.continuous.comp (pastChart s y).continuous).div_const 4)).sub
      ((closedConeAction_continuous q y X k).mul (hp.continuous.comp (pastChart s y).continuous))
  · have hdiv : HasCompactSupport (fun p => eventWave phi (pastVertex s y p)/4) := by
      simp only [div_eq_mul_inv]
      exact (hwc.comp_homeomorph (pastChart s y)).mul_right
    exact hdiv.mul_left.sub ((hc.comp_homeomorph (pastChart s y)).mul_left)

private theorem residual_integral (q : XiZeroCopy) (s y X k : ℝ) (phi : ℝ × ℝ → ℂ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    (∫ p in Ici (0:ℝ) ×ˢ Ici (0:ℝ), nullTestResidual q s y X k phi p) =
      fullSquarePotential q ![X,Real.exp k]*phi (s,y) := by
  let eta := fun p => phi (pastVertex s y p)
  let etau := fun p => eventDir (-1/2,1/2) phi (pastVertex s y p)
  have hc0 : HasCompactSupport eta := hc.comp_homeomorph (pastChart s y)
  have hc1 : HasCompactSupport etau :=
    (hc.fderiv_apply ℝ (-1/2,1/2)).comp_homeomorph (pastChart s y)
  obtain ⟨R0,hR0,h0⟩ := hc0.exists_pos_le_norm
  obtain ⟨R1,hR1,h1⟩ := hc1.exists_pos_le_norm
  have hr := residual_regular q s y X k phi hp hc
  obtain ⟨R2,hR2,h2⟩ := hr.2.exists_pos_le_norm
  let R := max (max R0 R1) R2
  have hb0 : R0 ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hb1 : R1 ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  have hb2 : R2 ≤ R := le_max_right _ _
  have hR : 0 ≤ R := hR0.le.trans hb0
  rw [quadrant_eq_box _ hr.1 R hR (fun p hp => h2 p (hb2.trans hp))]
  have hd := past_test_derivatives s y phi hp
  have hdcont : Continuous (fun p => eventWave phi (pastVertex s y p)/4) :=
    (((eventDir_smooth (eventDir_smooth hp (1,0)) (1,0)).continuous.sub
      (eventDir_smooth (eventDir_smooth hp (0,1)) (0,1)).continuous).comp
      (pastChart s y).continuous |>.div_const 4)
  have ht := vertex_primitive_joint_pair (fullSquarePotential q ![X,Real.exp k])
    (closedConeAction q y X k) eta etau (fun p => eventWave phi (pastVertex s y p)/4)
    R R (closedConeAction_continuous q y X k)
    (hp.continuous.comp (pastChart s y).continuous)
    ((eventDir_smooth hp (-1/2,1/2)).continuous.comp (pastChart s y).continuous)
    hdcont hd.1 hd.2
    (fun v => h0 _ (hb0.trans ((le_abs_self R).trans (norm_fst_le (R,v)))))
    (fun u => h1 _ (hb1.trans ((le_abs_self R).trans (norm_snd_le (u,R)))))
  change (∫ u in (0:ℝ)..R, ∫ v in (0:ℝ)..R,
    closedKernel q y X k (u,v)*(eventWave phi (pastVertex s y (u,v))/4)-
      closedConeAction q y X k (u,v)*eta (u,v)) = _
  rw [rectangle_sub
    (fun p => closedKernel q y X k p*(eventWave phi (pastVertex s y p)/4))
    (fun p => closedConeAction q y X k p*eta p)
    ((closedKernel_continuous q y X k).mul hdcont)
    ((closedConeAction_continuous q y X k).mul (hp.continuous.comp (pastChart s y).continuous)) R R]
  change (∫ u in (0:ℝ)..R, ∫ v in (0:ℝ)..R, _)-_ = _
  change (∫ u in (0:ℝ)..R, ∫ v in (0:ℝ)..R, closedKernel q y X k (u,v)*
      (eventWave phi (pastVertex s y (u,v))/4)) = _ at ht
  rw [ht]
  simp only [add_sub_cancel_right,eta,pastVertex,zero_div,sub_zero,add_zero]

/-- The actual temporal wave test minus its full angular action on one causal cone. -/
def temporalConeResidual (q : XiZeroCopy) (s y X k : ℝ)
    (phi : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  if |p.2-y| ≤ s-p.1 then
    nativeRiemannKernel q (s-p.1) p.2 y X k * eventWave phi p -
      angularAction q (invariant (s-p.1) p.2 y) X k /
        (Real.cosh p.2:ℂ)^2 * phi p
  else 0

private theorem pastVertex_causal (s y : ℝ) (p : ℝ × ℝ) :
    |(pastVertex s y p).2-y| ≤ s-(pastVertex s y p).1 ↔
      p ∈ Ici (0:ℝ) ×ˢ Ici (0:ℝ) := by
  simp only [pastVertex,mem_prod,mem_Ici,abs_le]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

private theorem residual_pullback (q : XiZeroCopy) (s y X k : ℝ)
    (phi : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    temporalConeResidual q s y X k phi (pastVertex s y p) =
      4*(Ici (0:ℝ) ×ˢ Ici (0:ℝ)).indicator (nullTestResidual q s y X k phi) p := by
  by_cases hp : p ∈ Ici (0:ℝ) ×ˢ Ici (0:ℝ)
  · rw [temporalConeResidual,if_pos ((pastVertex_causal s y p).mpr hp),Set.indicator_of_mem hp,
      nullTestResidual]
    have hK : closedKernel q y X k p = coneKernel q y p.1 p.2 X k :=
      (coneKernel_primitive q y p.1 p.2 X k hp.1 hp.2).symm
    have hJ : closedConeAction q y X k p =
        angularAction q (invariant ((p.1+p.2)/2) (y+(p.1-p.2)/2) y) X k /
          (4*(Real.cosh (y+(p.1-p.2)/2):ℂ)^2) := by
      simp only [closedConeAction,max_eq_right (invariant_causal ⟨_,_,_,cone_inside y p.1 p.2 hp.1 hp.2⟩)]
    rw [hK,hJ]
    simp only [coneKernel,pastVertex]
    rw [show s-(s-(p.1+p.2)/2)=(p.1+p.2)/2 by ring]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · rw [temporalConeResidual,if_neg (fun h => hp ((pastVertex_causal s y p).mp h)),
      Set.indicator_of_notMem hp,mul_zero]

/-- Absolute integrability of the actual cone residual for every smooth compact physical test. -/
theorem temporalConeResidual_integrable (q : XiZeroCopy) (s y X k : ℝ)
    (phi : ℝ × ℝ → ℂ) (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    Integrable (temporalConeResidual q s y X k phi) := by
  have hr := residual_regular q s y X k phi hp hc
  have hi : Integrable (fun p => temporalConeResidual q s y X k phi (pastVertex s y p)) := by
    simp_rw [residual_pullback]
    exact ((hr.1.integrable_of_hasCompactSupport hr.2).indicator
      (measurableSet_Ici.prod measurableSet_Ici)).const_mul 4
  have h := ((pastChart s y).toMeasurableEquiv.measurableEmbedding.integrable_map_iff
    (μ := volume) (g := temporalConeResidual q s y X k phi)).mpr hi
  change Integrable (temporalConeResidual q s y X k phi)
    (Measure.map (pastVertex s y) volume) at h
  rw [pastVertex_volume,integrable_smul_measure (by norm_num : (2:ℝ≥0∞)≠0)
    (by norm_num : (2:ℝ≥0∞)≠⊤)] at h
  exact h

/-- The full-theta cone kernel has the exact physical wave source vertex. -/
theorem temporalConeResidual_integral (q : XiZeroCopy) (s y X k : ℝ)
    (phi : ℝ × ℝ → ℂ) (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    (∫ p : ℝ × ℝ, temporalConeResidual q s y X k phi p) =
      2*(fullSquarePotential q ![X,Real.exp k]*phi (s,y)) := by
  have h := integral_pastVertex s y (temporalConeResidual q s y X k phi)
  simp_rw [residual_pullback] at h
  rw [integral_const_mul,integral_indicator (measurableSet_Ici.prod measurableSet_Ici),
    residual_integral q s y X k phi hp hc] at h
  linear_combination -(1/2:ℂ)*h


/-- Full physical temporal test of the original Dirichlet kernel, retaining
its actual angular action, causal supports and factor one half. -/
def dirichletWaveTest (q : XiZeroCopy) (s y X k : ℝ)
    (phi : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  nativeDirichletCausalKernel q (s-p.1) p.2 y X k * eventWave phi p -
    ((if |p.2-y| ≤ s-p.1 then angularAction q (invariant (s-p.1) p.2 y) X k else 0)-
      (if |p.2+y| ≤ s-p.1 then angularAction q (invariant (s-p.1) p.2 (-y)) X k else 0)) /
      (2*(Real.cosh p.2:ℂ)^2) * phi p

private theorem dirichletWaveTest_split (q : XiZeroCopy) (s y X k : ℝ)
    (phi : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    dirichletWaveTest q s y X k phi p =
      (temporalConeResidual q s y X k phi p - temporalConeResidual q s (-y) X k phi p)/2 := by
  unfold dirichletWaveTest temporalConeResidual nativeDirichletCausalKernel
  simp only [sub_neg_eq_add]
  split_ifs <;> simp only [div_eq_mul_inv,mul_inv_rev] <;> ring

/-- Every smooth compact time/radius test is admitted for the original direct-minus-image kernel. -/
theorem dirichletWaveTest_integrable (q : XiZeroCopy) (s y X k : ℝ)
    (phi : ℝ × ℝ → ℂ) (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    Integrable (dirichletWaveTest q s y X k phi) := by
  simp_rw [show dirichletWaveTest q s y X k phi = fun p =>
    (temporalConeResidual q s y X k phi p-temporalConeResidual q s (-y) X k phi p)/2 from
      funext (dirichletWaveTest_split q s y X k phi)]
  exact ((temporalConeResidual_integrable q s y X k phi hp hc).sub
    (temporalConeResidual_integrable q s (-y) X k phi hp hc)).div_const 2

/-- Exact distributional source and image vertices of the original full-theta Dirichlet kernel. -/
theorem dirichletWaveTest_integral (q : XiZeroCopy) (s y X k : ℝ)
    (phi : ℝ × ℝ → ℂ) (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    (∫ p : ℝ × ℝ, dirichletWaveTest q s y X k phi p) =
      fullSquarePotential q ![X,Real.exp k]*(phi (s,y)-phi (s,-y)) := by
  simp_rw [dirichletWaveTest_split]
  rw [integral_div,integral_sub
    (temporalConeResidual_integrable q s y X k phi hp hc)
    (temporalConeResidual_integrable q s (-y) X k phi hp hc),
    temporalConeResidual_integral q s y X k phi hp hc,
    temporalConeResidual_integral q s (-y) X k phi hp hc]
  ring

/-- On the physical half-plane, the image vertex is absent and the actual
source coefficient is exactly one. No separability condition is placed on the test. -/
theorem physical_dirichlet_wave_transposition (q : XiZeroCopy) (s y X k : ℝ) (hy : y < 0)
    (phi : ℝ × ℝ → ℂ) (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hphysical : tsupport phi ⊆ {p : ℝ × ℝ | p.2 < 0}) :
    (∫ p : ℝ × ℝ, dirichletWaveTest q s y X k phi p) =
      fullSquarePotential q ![X,Real.exp k]*phi (s,y) := by
  have hz : phi (s,-y)=0 := by
    by_contra hn
    have h := hphysical (subset_tsupport phi (show (s,-y) ∈ Function.support phi from hn))
    change -y < 0 at h
    linarith
  rw [dirichletWaveTest_integral q s y X k phi hp hc,hz,sub_zero]

end
end RHTower.D4BMGeneralTemporalTransposition
