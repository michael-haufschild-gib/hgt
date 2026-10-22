import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullSourceAdvancedAdmission
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullSourceCircleGrowth
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeAngularGreen
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeGoursat
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod

/-!
The original full-theta Riemann kernel transposes against compact null tests
with its exact source vertex. Its full angular action transposes onto compact
horizontal/log-height tests and retains the strict native growth exponent.
Joint absolute integrability then identifies the angular test action on the
existing infinite future response with its original direct-minus-image source
integral, retaining the fixed onset and both full source rays.

The general temporal weak equation, retained lift/cap equations and complete
physical metric/QNM identification remain separate. No RH or extinction claim
is made here.
-/

open MeasureTheory Set Filter Topology
namespace RHTower.D4BMAdvancedKernelTransposition
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMNativeCircle D4BMCausalKernel D4BMModularCore D4BMHorizon
open scoped ContDiff
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

private theorem double_primitive_pair (F : ℝ × ℝ → ℂ) (phi phip psi psip : ℝ → ℂ)
    (U V : ℝ) (hF : Continuous F) (hp : Continuous phi) (hpd : Continuous phip)
    (hs : Continuous psi) (hsd : Continuous psip)
    (hphi : ∀ u, HasDerivAt phi (phip u) u)
    (hpsi : ∀ v, HasDerivAt psi (psip v) v) (hU : phi U=0) (hV : psi V=0) :
    (∫ u in (0:ℝ)..U, ∫ v in (0:ℝ)..V,
      (∫ a in (0:ℝ)..u, ∫ b in (0:ℝ)..v, F (a,b))*phip u*psip v) =
    ∫ u in (0:ℝ)..U, ∫ v in (0:ℝ)..V, F (u,v)*phi u*psi v := by
  have swap (u v : ℝ) :
      (∫ a in (0:ℝ)..u, ∫ b in (0:ℝ)..v, F (a,b)) =
        ∫ b in (0:ℝ)..v, ∫ a in (0:ℝ)..u, F (a,b) := by
    apply intervalIntegral_intervalIntegral_swap
    exact hF.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc) |>.mono_set
      (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have c1 (u : ℝ) : Continuous (fun b => ∫ a in (0:ℝ)..u, F (a,b)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun b a : ℝ => F (a,b))
      (hF.comp (continuous_snd.prodMk continuous_fst)) 0 u
  have one (u : ℝ) :
      (∫ v in (0:ℝ)..V, (∫ a in (0:ℝ)..u, ∫ b in (0:ℝ)..v, F (a,b))*phip u*psip v) =
      -phip u*(∫ v in (0:ℝ)..V, (∫ a in (0:ℝ)..u, F (a,v))*psi v) := by
    simp_rw [swap]
    have h := primitive_pair (fun b => ∫ a in (0:ℝ)..u, F (a,b)) psi psip V (c1 u) hs hsd hpsi hV
    have he : (fun v => (∫ b in (0:ℝ)..v, ∫ a in (0:ℝ)..u, F (a,b))*phip u*psip v) =
        fun v => phip u*((∫ b in (0:ℝ)..v, ∫ a in (0:ℝ)..u, F (a,b))*psip v) := by funext v; ring
    rw [he,intervalIntegral.integral_const_mul,h]
    ring
  simp_rw [one]
  have hc : Continuous (fun p : ℝ × ℝ => -phip p.1*(∫ a in (0:ℝ)..p.1, F (a,p.2))*psi p.2) := by
    have hh := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) (a₀ := 0)
      (f := fun p : ℝ × ℝ => fun a => F (a,p.2))
      (hF.comp (continuous_snd.prodMk continuous_fst.snd)) continuous_fst
    exact (hpd.comp continuous_fst).neg.mul hh |>.mul (hs.comp continuous_snd)
  have he : (fun u => -phip u*(∫ v in (0:ℝ)..V, (∫ a in (0:ℝ)..u, F (a,v))*psi v)) =
      fun u => ∫ v in (0:ℝ)..V, -phip u*(∫ a in (0:ℝ)..u, F (a,v))*psi v := by
    funext u
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v _
    ring
  rw [he]
  rw [intervalIntegral_intervalIntegral_swap
    (F := fun u v : ℝ => -phip u*(∫ a in (0:ℝ)..u, F (a,v))*psi v)
    (a := 0) (b := U) (c := 0) (d := V)
    (hc.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc) |>.mono_set
      (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc))]
  have inner (v : ℝ) :
      (∫ u in (0:ℝ)..U, -phip u*(∫ a in (0:ℝ)..u, F (a,v))*psi v) =
      ∫ u in (0:ℝ)..U, F (u,v)*phi u*psi v := by
    have h := primitive_pair (fun a => F (a,v)) phi phip U
      (hF.comp (continuous_id.prodMk continuous_const)) hp hpd hphi hU
    have he : (fun u => -phip u*(∫ a in (0:ℝ)..u, F (a,v))*psi v) =
        fun u => -((∫ a in (0:ℝ)..u, F (a,v))*phip u)*psi v := by funext u; ring
    rw [he,intervalIntegral.integral_mul_const,intervalIntegral.integral_neg,h,neg_neg,
      intervalIntegral.integral_mul_const]
  simp_rw [inner]
  symm
  apply intervalIntegral_intervalIntegral_swap
  exact (((hF.mul (hp.comp continuous_fst)).mul (hs.comp continuous_snd)).continuousOn.integrableOn_compact
    (isCompact_uIcc.prod isCompact_uIcc)).mono_set (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)


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

private theorem vertex_primitive_pair (Q : ℂ) (F : ℝ × ℝ → ℂ)
    (phi phip psi psip : ℝ → ℂ) (U V : ℝ) (hF : Continuous F)
    (hp : Continuous phi) (hpd : Continuous phip) (hs : Continuous psi) (hsd : Continuous psip)
    (hphi : ∀ u, HasDerivAt phi (phip u) u)
    (hpsi : ∀ v, HasDerivAt psi (psip v) v) (hU : phi U=0) (hV : psi V=0) :
    (∫ u in (0:ℝ)..U, ∫ v in (0:ℝ)..V,
      (Q+∫ a in (0:ℝ)..u, ∫ b in (0:ℝ)..v, F (a,b))*phip u*psip v) =
    Q*phi 0*psi 0+∫ u in (0:ℝ)..U, ∫ v in (0:ℝ)..V, F (u,v)*phi u*psi v := by
  have hD := double_primitive_continuous F hF
  have h0 : Continuous (fun p : ℝ × ℝ => Q*phip p.1*psip p.2) := by fun_prop
  have h1 : Continuous (fun p : ℝ × ℝ =>
      (∫ a in (0:ℝ)..p.1, ∫ b in (0:ℝ)..p.2, F (a,b))*phip p.1*psip p.2) :=
    (hD.mul (hpd.comp continuous_fst)).mul (hsd.comp continuous_snd)
  have he (u v : ℝ) : (Q+∫ a in (0:ℝ)..u, ∫ b in (0:ℝ)..v, F (a,b))*phip u*psip v =
      Q*phip u*psip v+(∫ a in (0:ℝ)..u, ∫ b in (0:ℝ)..v, F (a,b))*phip u*psip v := by ring
  simp_rw [he]
  have split (u : ℝ) :
      (∫ v in (0:ℝ)..V, Q*phip u*psip v+(∫ a in (0:ℝ)..u, ∫ b in (0:ℝ)..v, F (a,b))*phip u*psip v) =
      (∫ v in (0:ℝ)..V, Q*phip u*psip v)+
        ∫ v in (0:ℝ)..V, (∫ a in (0:ℝ)..u, ∫ b in (0:ℝ)..v, F (a,b))*phip u*psip v :=
    intervalIntegral.integral_add
      ((h0.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 V)
      ((h1.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 V)
  simp_rw [split]
  rw [intervalIntegral.integral_add
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun u v : ℝ => Q*phip u*psip v) h0 0 V).intervalIntegrable 0 U)
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun u v : ℝ => (∫ a in (0:ℝ)..u, ∫ b in (0:ℝ)..v, F (a,b))*phip u*psip v) h1 0 V).intervalIntegrable 0 U),
    double_primitive_pair F phi phip psi psip U V hF hp hpd hs hsd hphi hpsi hU hV]
  congr 1
  simp_rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hphi u) (hpd.intervalIntegrable 0 U),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hpsi v) (hsd.intervalIntegrable 0 V),hU,hV]
  ring

private theorem laplace_circle_continuous (q : XiZeroCopy) (X k : ℝ) :
    Continuous (fun p : ℝ × ℝ =>
      scalarLaplacian (fullSquarePotential q) (logCircle p.1 p.2 X k)) := by
  have hp (p : ℝ × ℝ) : 0 < logCircle p.1 p.2 X k 1 :=
    mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have he : (fun p : ℝ × ℝ => scalarLaplacian (fullSquarePotential q) (logCircle p.1 p.2 X k)) =
      fun p => (logCircle p.1 p.2 X k 1:ℂ)^(2 : ℕ) *
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
    (4*(Real.cosh (y+(p.1-p.2)/2):ℂ)^(2 : ℕ))

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

/-- Compact weak transposition of the actual full-theta kernel, including its source vertex. -/
theorem coneKernel_transposition (q : XiZeroCopy) (y X k U V : ℝ)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (phi phip psi psip : ℝ → ℂ)
    (hp : Continuous phi) (hpd : Continuous phip) (hs : Continuous psi) (hsd : Continuous psip)
    (hphi : ∀ u, HasDerivAt phi (phip u) u)
    (hpsi : ∀ v, HasDerivAt psi (psip v) v) (hpU : phi U=0) (hsV : psi V=0) :
    (∫ u in (0:ℝ)..U, ∫ v in (0:ℝ)..V, coneKernel q y u v X k*phip u*psip v) =
      fullSquarePotential q ![X,Real.exp k]*phi 0*psi 0 +
      ∫ u in (0:ℝ)..U, ∫ v in (0:ℝ)..V,
        angularAction q (invariant ((u+v)/2) (y+(u-v)/2) y) X k /
          (4*(Real.cosh (y+(u-v)/2):ℂ)^(2 : ℕ))*phi u*psi v := by
  have h := vertex_primitive_pair (fullSquarePotential q ![X,Real.exp k])
    (closedConeAction q y X k) phi phip psi psip U V
    (closedConeAction_continuous q y X k) hp hpd hs hsd hphi hpsi hpU hsV
  have left : (∫ u in (0:ℝ)..U, ∫ v in (0:ℝ)..V, coneKernel q y u v X k*phip u*psip v) =
      ∫ u in (0:ℝ)..U, ∫ v in (0:ℝ)..V,
        (fullSquarePotential q ![X,Real.exp k]+
          ∫ a in (0:ℝ)..u, ∫ b in (0:ℝ)..v, closedConeAction q y X k (a,b))*phip u*psip v := by
    apply intervalIntegral.integral_congr
    intro u hu
    apply intervalIntegral.integral_congr
    intro v hv
    dsimp only
    rw [coneKernel_primitive q y u v X k
      (show u ∈ Icc 0 U by simpa [uIcc_of_le hU] using hu).1
      (show v ∈ Icc 0 V by simpa [uIcc_of_le hV] using hv).1]
  rw [left,h]
  apply congrArg (fun z : ℂ => fullSquarePotential q ![X,Real.exp k]*phi 0*psi 0+z)
  apply intervalIntegral.integral_congr
  intro u hu
  apply intervalIntegral.integral_congr
  intro v hv
  dsimp only
  have hu0 := (show u ∈ Icc 0 U by simpa [uIcc_of_le hU] using hu).1
  have hv0 := (show v ∈ Icc 0 V by simpa [uIcc_of_le hV] using hv).1
  simp only [closedConeAction,max_eq_right (invariant_causal ⟨_,_,_,cone_inside y u v hu0 hv0⟩)]


private def planeDir (v : ℂ) (F : ℂ → ℂ) (z : ℂ) : ℂ := fderiv ℝ F z v

private theorem planeDir_smooth {F : ℂ → ℂ} (hF : ContDiff ℝ ∞ F) (v : ℂ) :
    ContDiff ℝ ∞ (planeDir v F) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private theorem compact_product_integrable {phi F : ℂ → ℂ}
    (hp : Continuous phi) (hc : HasCompactSupport phi) (hF : Continuous F) :
    Integrable (fun z => phi z*F z) :=
  (hp.mul hF).integrable_of_hasCompactSupport hc.mul_right

private theorem plane_first_pair (phi F : ℂ → ℂ) (v : ℂ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) (hF : ContDiff ℝ ∞ F) :
    (∫ z, phi z*planeDir v F z) = -(∫ z, planeDir v phi z*F z) := by
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure ℂ))
    (compact_product_integrable (planeDir_smooth hp v).continuous (hc.fderiv_apply ℝ v) hF.continuous)
    (compact_product_integrable hp.continuous hc (planeDir_smooth hF v).continuous)
    (compact_product_integrable hp.continuous hc hF.continuous)
    (fun z _ => hp.differentiable (by simp) z)
    (fun z _ => hF.differentiable (by simp) z)

private theorem plane_second_pair (phi F : ℂ → ℂ) (v : ℂ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) (hF : ContDiff ℝ ∞ F) :
    (∫ z, phi z*planeDir v (planeDir v F) z) =
      ∫ z, planeDir v (planeDir v phi) z*F z := by
  rw [plane_first_pair phi (planeDir v F) v hp hc (planeDir_smooth hF v),
    plane_first_pair (planeDir v phi) F v (planeDir_smooth hp v) (hc.fderiv_apply ℝ v) hF,
    neg_neg]

private theorem plane_line_first (F : ℂ → ℂ) (hF : ContDiff ℝ ∞ F)
    (l : ℝ → ℂ) (v : ℂ) (hd : ∀ r, HasDerivAt l v r) (a : ℝ) :
    planeDir v F (l a) = deriv (fun r => F (l r)) a :=
  ((hF.differentiable (by simp) (l a)).hasFDerivAt.comp_hasDerivAt a (hd a)).deriv.symm

private theorem plane_line_second (F : ℂ → ℂ) (hF : ContDiff ℝ ∞ F)
    (l : ℝ → ℂ) (v : ℂ) (hd : ∀ r, HasDerivAt l v r) (a : ℝ) :
    planeDir v (planeDir v F) (l a) = deriv (deriv (fun r => F (l r))) a := by
  have he : (fun r => planeDir v F (l r)) = deriv (fun r => F (l r)) :=
    funext (plane_line_first F hF l v hd)
  rw [plane_line_first (planeDir v F) (planeDir_smooth hF v) l v hd a,he]

private def logKernelField (q : XiZeroCopy) (t : ℝ) (z : ℂ) : ℂ :=
  angularKernel q t z.re z.im

private theorem logKernelField_smooth (q : XiZeroCopy) (t : ℝ) :
    ContDiff ℝ ∞ (logKernelField q t) := by
  unfold logKernelField angularKernel
  have hc : ContDiff ℝ ∞ (fun z : ℂ => (Real.arcosh t,z.re,z.im)) :=
    contDiff_const.prodMk (Complex.reCLM.contDiff.prodMk Complex.imCLM.contDiff)
  have h := (D4BMNativeResponse.nativeMean_joint_smooth q).comp hc
  have hs : (NormedAlgebra.toNormedSpace ℂ : NormedSpace ℝ ℂ) =
      instInnerProductSpaceRealComplex.toNormedSpace := by rfl
  rw [hs] at h
  exact h

private theorem angularAction_directions (q : XiZeroCopy) (t : ℝ) (z : ℂ) :
    angularAction q t z.re z.im =
      (Real.exp z.im:ℂ)^(2 : ℕ)*planeDir 1 (planeDir 1 (logKernelField q t)) z+
        planeDir Complex.I (planeDir Complex.I (logKernelField q t)) z-
          planeDir Complex.I (logKernelField q t) z := by
  have hx (r : ℝ) : HasDerivAt (fun X : ℝ => (X:ℂ)+(z.im:ℂ)*Complex.I) 1 r := by
    simpa using Complex.ofRealCLM.hasDerivAt.add_const ((z.im:ℂ)*Complex.I)
  have hy (r : ℝ) : HasDerivAt (fun Y : ℝ => (z.re:ℂ)+(Y:ℂ)*Complex.I) Complex.I r := by
    simpa using (Complex.ofRealCLM.hasDerivAt.mul_const Complex.I).const_add (z.re:ℂ)
  have he := Complex.re_add_im z
  have hX := plane_line_second _ (logKernelField_smooth q t) _ 1 hx z.re
  have hY := plane_line_second _ (logKernelField_smooth q t) _ Complex.I hy z.im
  have hY1 := plane_line_first _ (logKernelField_smooth q t) _ Complex.I hy z.im
  have ex : (fun r : ℝ => logKernelField q t ((r:ℂ)+(z.im:ℂ)*Complex.I)) =
      fun r => angularKernel q t r z.im := by funext r; simp [logKernelField]
  have ey : (fun r : ℝ => logKernelField q t ((z.re:ℂ)+(r:ℂ)*Complex.I)) =
      fun r => angularKernel q t z.re r := by funext r; simp [logKernelField]
  rw [he,ex] at hX
  rw [he,ey] at hY hY1
  rw [angularAction,hX,hY,hY1]

/-- Test operator in the actual horizontal/log-height chart. Its weight is the
original hyperbolic area density; all derivatives are on the compact test. -/
def angularTestAction (phi : ℂ → ℂ) (z : ℂ) : ℂ :=
  planeDir 1 (planeDir 1 (fun w => (Real.exp w.im:ℂ)*phi w)) z+
  planeDir Complex.I (planeDir Complex.I (fun w => (Real.exp (-w.im):ℂ)*phi w)) z+
  planeDir Complex.I (fun w => (Real.exp (-w.im):ℂ)*phi w) z

private theorem angularTestAction_continuous {phi : ℂ → ℂ} (hp : ContDiff ℝ ∞ phi) :
    Continuous (angularTestAction phi) := by
  have ha : ContDiff ℝ ∞ (fun w : ℂ => (Real.exp w.im:ℂ)*phi w) :=
    (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp Complex.imCLM.contDiff)).mul hp
  have hb : ContDiff ℝ ∞ (fun w : ℂ => (Real.exp (-w.im):ℂ)*phi w) :=
    (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp Complex.imCLM.contDiff.neg)).mul hp
  exact (((planeDir_smooth (planeDir_smooth ha 1) 1).continuous).add
    ((planeDir_smooth (planeDir_smooth hb Complex.I) Complex.I).continuous)).add
      (planeDir_smooth hb Complex.I).continuous

private theorem angularTestAction_compact {phi : ℂ → ℂ} (hc : HasCompactSupport phi) :
    HasCompactSupport (angularTestAction phi) := by
  have ha : HasCompactSupport (fun w : ℂ => (Real.exp w.im:ℂ)*phi w) := hc.mul_left
  have hb : HasCompactSupport (fun w : ℂ => (Real.exp (-w.im):ℂ)*phi w) := hc.mul_left
  exact (((ha.fderiv_apply ℝ 1).fderiv_apply ℝ 1).add
    ((hb.fderiv_apply ℝ Complex.I).fderiv_apply ℝ Complex.I)).add
      (hb.fderiv_apply ℝ Complex.I)

/-- Exact angular transposition of the original full-theta kernel in hyperbolic
area, with both original angular derivatives retained. -/
theorem angularAction_compact_transposition (q : XiZeroCopy) (t : ℝ) (phi : ℂ → ℂ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    (∫ z : ℂ, (Real.exp (-z.im):ℂ)*phi z*angularAction q t z.re z.im) =
      ∫ z : ℂ, angularTestAction phi z*angularKernel q t z.re z.im := by
  let A : ℂ → ℂ := fun w => (Real.exp w.im:ℂ)*phi w
  let B : ℂ → ℂ := fun w => (Real.exp (-w.im):ℂ)*phi w
  let F := logKernelField q t
  have hA : ContDiff ℝ ∞ A :=
    (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp Complex.imCLM.contDiff)).mul hp
  have hB : ContDiff ℝ ∞ B :=
    (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp Complex.imCLM.contDiff.neg)).mul hp
  have cA : HasCompactSupport A := hc.mul_left
  have cB : HasCompactSupport B := hc.mul_left
  have hF : ContDiff ℝ ∞ F := logKernelField_smooth q t
  have hD (v : ℂ) := planeDir_smooth hF v
  have hDD (v : ℂ) := planeDir_smooth (hD v) v
  have he (z : ℂ) : (Real.exp (-z.im):ℂ)*phi z*angularAction q t z.re z.im =
      A z*planeDir 1 (planeDir 1 F) z+B z*planeDir Complex.I (planeDir Complex.I F) z-
        B z*planeDir Complex.I F z := by
    rw [angularAction_directions]
    have hw : (Real.exp (-z.im):ℂ)*(Real.exp z.im:ℂ)^(2 : ℕ)=(Real.exp z.im:ℂ) := by
      rw [Real.exp_neg,Complex.ofReal_inv]
      field_simp [Complex.ofReal_ne_zero.mpr (Real.exp_pos z.im).ne']
    dsimp only [A,B,F]
    linear_combination phi z*planeDir 1 (planeDir 1 (logKernelField q t)) z*hw
  simp_rw [he]
  rw [integral_sub
    (f := fun z : ℂ => A z*planeDir 1 (planeDir 1 F) z+B z*planeDir Complex.I (planeDir Complex.I F) z)
    (g := fun z : ℂ => B z*planeDir Complex.I F z)
    ((compact_product_integrable hA.continuous cA (hDD 1).continuous).add
      (compact_product_integrable hB.continuous cB (hDD Complex.I).continuous))
    (compact_product_integrable hB.continuous cB (hD Complex.I).continuous),
    integral_add (compact_product_integrable hA.continuous cA (hDD 1).continuous)
      (compact_product_integrable hB.continuous cB (hDD Complex.I).continuous),
    plane_second_pair A F 1 hA cA hF,plane_second_pair B F Complex.I hB cB hF,
    plane_first_pair B F Complex.I hB cB hF,sub_neg_eq_add]
  have h1 := compact_product_integrable (planeDir_smooth (planeDir_smooth hA 1) 1).continuous
    ((cA.fderiv_apply ℝ 1).fderiv_apply ℝ 1) hF.continuous
  have h2 := compact_product_integrable
    (planeDir_smooth (planeDir_smooth hB Complex.I) Complex.I).continuous
    ((cB.fderiv_apply ℝ Complex.I).fderiv_apply ℝ Complex.I) hF.continuous
  have h3 := compact_product_integrable (planeDir_smooth hB Complex.I).continuous
    (cB.fderiv_apply ℝ Complex.I) hF.continuous
  rw [← integral_add h1 h2,← integral_add
    (f := fun z : ℂ => planeDir 1 (planeDir 1 A) z*F z+planeDir Complex.I (planeDir Complex.I B) z*F z)
    (g := fun z : ℂ => planeDir Complex.I B z*F z) (h1.add h2) h3]
  apply integral_congr_ae
  filter_upwards with z
  change _ = (planeDir 1 (planeDir 1 A) z+
    planeDir Complex.I (planeDir Complex.I B) z+planeDir Complex.I B z)*F z
  ring

/-- Testing the angular action recovers the strict original kernel-growth
exponent. No bound on the pointwise angular jets is assumed. -/
theorem tested_angularAction_growth (q : XiZeroCopy) (phi : ℂ → ℂ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ Real.arcosh t →
      ‖∫ z : ℂ, (Real.exp (-z.im):ℂ)*phi z*angularAction q t z.re z.im‖ ≤
        C*Real.exp (sourceGrowthExponent q*Real.arcosh t) := by
  obtain ⟨C,hC,hb⟩ := mean_global_growth q
  let w : ℂ → ℝ := fun z => ‖angularTestAction phi z‖*Real.exp (sourceGrowthExponent q*|z.im|)
  have hw : Integrable w := by
    apply ((angularTestAction_continuous hp).norm.mul (by fun_prop)).integrable_of_hasCompactSupport
    exact (angularTestAction_compact hc).norm.mul_right
  refine ⟨C*∫ z, w z,mul_nonneg hC (integral_nonneg (fun z => by dsimp [w]; positivity)),?_⟩
  intro t ht
  rw [angularAction_compact_transposition q t phi hp hc]
  have hm : Integrable (fun z => (C*Real.exp (sourceGrowthExponent q*Real.arcosh t))*w z) :=
    hw.const_mul _
  have hh := norm_integral_le_of_norm_le
    (f := fun z : ℂ => angularTestAction phi z*angularKernel q t z.re z.im) hm (Filter.Eventually.of_forall (fun z : ℂ => by
    rw [norm_mul]
    have hz := mul_le_mul_of_nonneg_left (hb (Real.arcosh t) z.re z.im ht)
      (norm_nonneg (angularTestAction phi z))
    change ‖angularTestAction phi z‖*‖mean q (Real.arcosh t) z.re z.im‖ ≤ _
    calc
      _ ≤ ‖angularTestAction phi z‖*(C*Real.exp (sourceGrowthExponent q*(Real.arcosh t+|z.im|))) := hz
      _ = (C*Real.exp (sourceGrowthExponent q*Real.arcosh t))*w z := by
        rw [mul_add,Real.exp_add]
        dsimp [w]
        ring))
  rw [integral_const_mul] at hh
  convert hh using 1
  ring


/-- The full angular test action on the original direct-minus-image causal kernel. -/
def testedDirichletAngularKernel (q : XiZeroCopy) (phi : ℂ → ℂ) (h x y : ℝ) : ℂ :=
  ((if |x-y| ≤ h then
      ∫ z : ℂ, (Real.exp (-z.im):ℂ)*phi z*angularAction q (invariant h x y) z.re z.im
    else 0)-
    (if |x+y| ≤ h then
      ∫ z : ℂ, (Real.exp (-z.im):ℂ)*phi z*angularAction q (invariant h x (-y)) z.re z.im
    else 0))/2

theorem dirichlet_angular_transposition (q : XiZeroCopy) (phi : ℂ → ℂ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) (h x y : ℝ) :
    (∫ z : ℂ, angularTestAction phi z*nativeDirichletCausalKernel q h x y z.re z.im) =
      testedDirichletAngularKernel q phi h x y := by
  have hi (Y : ℝ) : Integrable (fun z : ℂ => angularTestAction phi z*
      (if |x-Y| ≤ h then nativeRiemannKernel q h x Y z.re z.im else 0)) := by
    by_cases he : |x-Y| ≤ h
    · simp only [if_pos he]
      exact compact_product_integrable (angularTestAction_continuous hp)
        (angularTestAction_compact hc) (logKernelField_smooth q (invariant h x Y)).continuous
    · simp only [if_neg he,mul_zero]
      exact integrable_zero ℂ ℂ volume
  have he (Y : ℝ) :
      (∫ z : ℂ, angularTestAction phi z*
        (if |x-Y| ≤ h then nativeRiemannKernel q h x Y z.re z.im else 0)) =
      if |x-Y| ≤ h then
        ∫ z : ℂ, (Real.exp (-z.im):ℂ)*phi z*angularAction q (invariant h x Y) z.re z.im
      else 0 := by
    by_cases hy : |x-Y| ≤ h
    · simp only [if_pos hy]
      exact (angularAction_compact_transposition q (invariant h x Y) phi hp hc).symm
    · simp only [if_neg hy,mul_zero,integral_zero]
  have hi' := hi (-y)
  have he' := he (-y)
  simp only [sub_neg_eq_add] at hi' he'
  simp only [nativeDirichletCausalKernel,← mul_div_assoc,mul_sub]
  rw [integral_div,integral_sub (hi y) hi',he y,he']
  rfl

open D4BMJointSource D4BMFullSourceAdvanced

private abbrev sourceRegion : Set (ℝ × ℝ) := Ioi 0 ×ˢ Iio 0
private abbrev sourceMeasure : Measure (ℝ × ℝ) := volume.restrict sourceRegion

private theorem kernel_joint_measurable (q : XiZeroCopy) (x : ℝ) :
    Measurable (fun r : (ℝ × ℝ) × ℂ =>
      nativeDirichletCausalKernel q r.1.1 x r.1.2 r.2.re r.2.im) := by
  classical
  have cone (Y : (ℝ × ℝ) × ℂ → ℝ) (hy : Continuous Y) :
      Measurable (fun r : (ℝ × ℝ) × ℂ =>
        if |x-Y r| ≤ r.1.1 then nativeRiemannKernel q r.1.1 x (Y r) r.2.re r.2.im else 0) := by
    have hz : Continuous (fun r : (ℝ × ℝ) × ℂ => invariant r.1.1 x (Y r)) := by
      unfold invariant
      apply Continuous.div
      · fun_prop
      · fun_prop
      · intro r; exact mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'
    have hd := Real.continuousOn_arcosh.comp_continuous (continuous_const.max hz)
      (fun r => le_max_left (1:ℝ) (invariant r.1.1 x (Y r)))
    have hf : Continuous (fun r : (ℝ × ℝ) × ℂ =>
        mean q (Real.arcosh (max 1 (invariant r.1.1 x (Y r)))) r.2.re r.2.im) := by
      have hm := (D4BMNativeResponse.nativeMean_joint_smooth q).continuous.comp
        (hd.prodMk ((Complex.continuous_re.comp continuous_snd).prodMk
          (Complex.continuous_im.comp continuous_snd)))
      exact hm
    have hs : MeasurableSet {r : (ℝ × ℝ) × ℂ | |x-Y r| ≤ r.1.1} :=
      (isClosed_le (continuous_const.sub hy).abs continuous_fst.fst).measurableSet
    have he : Measurable (fun r : (ℝ × ℝ) × ℂ =>
        if |x-Y r| ≤ r.1.1 then
          mean q (Real.arcosh (max 1 (invariant r.1.1 x (Y r)))) r.2.re r.2.im else 0) :=
      Measurable.ite hs hf.measurable measurable_const
    convert he using 1
    funext r
    by_cases hc : |x-Y r| ≤ r.1.1
    · simp only [if_pos hc,nativeRiemannKernel,angularKernel,
        max_eq_right (invariant_causal ⟨_,_,_,hc⟩)]
    · simp only [if_neg hc]
  have hd := cone (fun r => r.1.2) continuous_fst.snd
  have hi := cone (fun r => -r.1.2) continuous_fst.snd.neg
  simpa only [sub_neg_eq_add,nativeDirichletCausalKernel,Pi.sub_apply] using
    (hd.sub hi).div_const (2:ℂ)

private def testedSourceDensity (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ)
    (tau x : ℝ) (phi : ℂ → ℂ) (r : (ℝ × ℝ) × ℂ) : ℂ :=
  angularTestAction phi r.2*density q branch amplitude tau x r.2.re r.2.im r.1

private theorem testedSourceDensity_measurable (q : XiZeroCopy) (branch : Bool)
    (amplitude : ℂ) (tau x : ℝ) (phi : ℂ → ℂ) (hp : ContDiff ℝ ∞ phi) :
    Measurable (testedSourceDensity q branch amplitude tau x phi) := by
  have hs := (timeReducedCoefficient_joint_continuous (physicalRate q branch) amplitude).comp
    (show Continuous (fun r : (ℝ × ℝ) × ℂ => (tau+r.1.1,r.1.2)) by fun_prop)
  exact ((angularTestAction_continuous hp).measurable.comp measurable_snd).mul
    ((kernel_joint_measurable q x).mul hs.measurable)

private theorem future_majorant_integrable (q : XiZeroCopy) :
    Integrable (fun p : ℝ × ℝ =>
      Real.exp ((sourceGrowthExponent q-decayExponent q)*p.1)*
        Real.exp ((2-decayExponent q)*p.2)) sourceMeasure := by
  have hc := decayExponent_bounds q
  have hh := integrableOn_exp_mul_Ioi
    (show sourceGrowthExponent q-decayExponent q < 0 by linarith) 0
  have hy := (integrableOn_exp_mul_Iic (show 0 < 2-decayExponent q by linarith) 0).mono_set
    Iio_subset_Iic_self
  dsimp only [sourceMeasure]
  rw [Measure.volume_eq_prod,← Measure.prod_restrict]
  exact hh.mul_prod hy

/-- Joint absolute admission of the full original future source and the angular
test operator, before any interchange of the infinite source integral. -/
theorem testedSourceDensity_integrable (q : XiZeroCopy) (branch : Bool)
    (amplitude : ℂ) (tau x : ℝ) (phi : ℂ → ℂ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    Integrable (testedSourceDensity q branch amplitude tau x phi) (sourceMeasure.prod volume) := by
  let w : ℂ → ℝ := fun z => ‖angularTestAction phi z‖*Real.exp (sourceGrowthExponent q*|z.im|)
  have hw : Integrable w := by
    apply ((angularTestAction_continuous hp).norm.mul (by fun_prop)).integrable_of_hasCompactSupport
    exact (angularTestAction_compact hc).norm.mul_right
  obtain ⟨C,hC,hb⟩ := density_bound q branch amplitude
  have hm := ((future_majorant_integrable q).mul_prod hw).const_mul
    (C*Real.exp (-decayExponent q*tau))
  apply hm.mono' (testedSourceDensity_measurable q branch amplitude tau x phi hp).aestronglyMeasurable
  have hS : MeasurableSet sourceRegion := measurableSet_Ioi.prod measurableSet_Iio
  have hs : ∀ᵐ r : (ℝ × ℝ) × ℂ ∂sourceMeasure.prod volume, r.1 ∈ sourceRegion := by
    apply (Measure.ae_prod_iff_ae_ae (hS.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem hS] with p hp
    exact ae_of_all _ (fun _ => hp)
  filter_upwards [hs] with r hr
  change ‖angularTestAction phi r.2*density q branch amplitude tau x r.2.re r.2.im r.1‖ ≤ _
  rw [norm_mul]
  have h := mul_le_mul_of_nonneg_left
    (hb tau x r.2.re r.2.im r.1.1 r.1.2 hr.1 hr.2) (norm_nonneg (angularTestAction phi r.2))
  refine h.trans_eq ?_
  rw [Real.exp_add]
  dsimp [w]
  ring

/-- The admitted original future response transposes its full angular action onto
the compact test. Both causal cones, image subtraction, original onset and full
infinite source domain are retained. -/
theorem original_future_angular_transposition (q : XiZeroCopy) (branch : Bool)
    (amplitude : ℂ) (tau x : ℝ) (phi : ℂ → ℂ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    (∫ z : ℂ, angularTestAction phi z*response q branch amplitude tau x z.re z.im) =
      ∫ p in sourceRegion, testedDirichletAngularKernel q phi p.1 x p.2*
        timeReducedCoefficient (physicalRate q branch) amplitude (tau+p.1) p.2 := by
  have hi := testedSourceDensity_integrable q branch amplitude tau x phi hp hc
  have hs := integral_integral_swap
    (f := fun p z => testedSourceDensity q branch amplitude tau x phi (p,z)) hi
  have left : (∫ z : ℂ, ∫ p : ℝ × ℝ, testedSourceDensity q branch amplitude tau x phi (p,z) ∂sourceMeasure) =
      ∫ z : ℂ, angularTestAction phi z*response q branch amplitude tau x z.re z.im := by
    apply integral_congr_ae
    filter_upwards with z
    dsimp only [testedSourceDensity,response]
    exact integral_const_mul (angularTestAction phi z)
      (density q branch amplitude tau x z.re z.im)
  have right : (∫ p : ℝ × ℝ, ∫ z : ℂ, testedSourceDensity q branch amplitude tau x phi (p,z) ∂volume ∂sourceMeasure) =
      ∫ p in sourceRegion, testedDirichletAngularKernel q phi p.1 x p.2*
        timeReducedCoefficient (physicalRate q branch) amplitude (tau+p.1) p.2 := by
    apply integral_congr_ae
    filter_upwards with p
    have he (z : ℂ) : testedSourceDensity q branch amplitude tau x phi (p,z) =
        (angularTestAction phi z*nativeDirichletCausalKernel q p.1 x p.2 z.re z.im)*
          timeReducedCoefficient (physicalRate q branch) amplitude (tau+p.1) p.2 := by
      dsimp only [testedSourceDensity,density]
      ring
    simp_rw [he]
    rw [integral_mul_const,dirichlet_angular_transposition q phi hp hc]
  exact left.symm.trans (hs.symm.trans right)

end
end RHTower.D4BMAdvancedKernelTransposition
