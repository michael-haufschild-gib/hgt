import GaloisForLFunctions.RHTower.ChiCubicSelectedLocalMellinEnergy
import GaloisForLFunctions.RHTower.ChiCubicPhysicalExteriorDecay

/-!
# Complete Mellin energy of the actual selected BAG cone

The fixed physical cutoff is one on a neighborhood of the stationary box.
Its actual exterior remainder and both pure second Euler derivatives have
arbitrary power saving in N on the entire positive quadrant. Exact logarithmic
substitution retains both Jacobians and axis endpoints; a separated integrable
majorant gives uniform mass over the complete Mellin parameter square.

Fourier differentiation and Plancherel turn these actual derivative masses
into full exterior H² energy. Exact local-plus-exterior decomposition then
closes the full H^(1+s) bound for the selected normalized original cone for
0<s<1/2. No uniform Schwartz budget or stationary replacement is assumed.
Arithmetic source-weighted tails and moving-test cancellation remain open.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform Topology ENNReal ContDiff
open HTGeometry (QuadrantLogSpace quadrantLogNode quadrantLogBasis quadrantLogNode_apply)
open HTGeometry.PositiveLine
open LineDeriv
namespace RHTower.BAGTrace
private abbrev E := QuadrantLogSpace
private def coord (i : Fin 2) : E→L[ℝ]ℝ := EuclideanSpace.proj i
private lemma coordinate_growth (i : Fin 2) : (fun u : E => u i).HasTemperateGrowth :=
  (coord i).hasTemperateGrowth

variable (σ : Fin 2→{r : ℝ // 0<r})

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private def localLogGradient (f : SchwartzMap E F) : SchwartzMap E (E→L[ℝ]F) :=
  (quadrantLogEuler σ 0 f).postcompCLM
    ((ContinuousLinearMap.smulRightL ℝ E F) (coord 0))+
  (quadrantLogEuler σ 1 f).postcompCLM
    ((ContinuousLinearMap.smulRightL ℝ E F) (coord 1))

private lemma gradient_apply (f : SchwartzMap E F) (x v : E) :
    localLogGradient σ f x v =
      v 0 • ((-(σ 0 : ℝ)) • f x - x 0 • (fderiv ℝ f x (quadrantLogBasis 0))) +
      v 1 • ((-(σ 1 : ℝ)) • f x - x 1 • (fderiv ℝ f x (quadrantLogBasis 1))) := by
  simp [localLogGradient,quadrantLogEuler,SchwartzMap.smulLeftCLM_apply_apply
    (coordinate_growth _),SchwartzMap.fderivCLM_apply,coord]
  module

private lemma logNode_hasFDeriv (u : E) :
    HasFDerivAt quadrantLogNode
      (((-Real.exp (-u 0)) • (coord 0)).smulRight (quadrantLogBasis 0) +
       ((-Real.exp (-u 1)) • (coord 1)).smulRight (quadrantLogBasis 1)) u := by
  have h (i : Fin 2) := (((coord i).hasFDerivAt (x := u)).neg.exp).smul_const
    (quadrantLogBasis i)
  apply ((h 0).add (h 1)).congr_fderiv
  ext v
  simp [coord]

private lemma logWeight_hasFDeriv (f : SchwartzMap E F) (u : E) :
    HasFDerivAt (quadrantLogWeight σ f) (quadrantLogWeight σ (localLogGradient σ f) u) u := by
  have he := logNode_hasFDeriv u
  have hw : HasFDerivAt (fun v : E => Real.exp (-(σ 0 : ℝ)*v 0-(σ 1 : ℝ)*v 1))
      (Real.exp (-(σ 0 : ℝ)*u 0-(σ 1 : ℝ)*u 1) •
        ((-(σ 0 : ℝ)) • coord 0 - (σ 1 : ℝ) • coord 1)) u :=
    (((coord 0).hasFDerivAt.const_mul (-(σ 0 : ℝ))).sub
      ((coord 1).hasFDerivAt.const_mul (σ 1 : ℝ))).exp
  have hf := (f.differentiableAt.hasFDerivAt.comp u he)
  apply (hw.smul hf).congr_fderiv
  ext v
  simp only [quadrantLogWeight,add_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.comp_apply,
    sub_apply,gradient_apply σ,quadrantLogNode_apply]
  dsimp [coord]
  simp only [map_add,map_smul,smul_add,smul_sub,smul_smul]
  module

private theorem logSchwartz_euler (f : SchwartzMap E ℂ) (i : Fin 2) :
    (∂_{quadrantLogBasis i} (quadrantLogSchwartz σ f) : SchwartzMap E ℂ)=
      quadrantLogSchwartz σ (quadrantLogEuler σ i f) := by
  ext u
  change fderiv ℝ (quadrantLogWeight σ f) u (quadrantLogBasis i)=
    quadrantLogSchwartz σ (quadrantLogEuler σ i f) u
  rw [(logWeight_hasFDeriv σ f u).fderiv,quadrantLogSchwartz_apply]
  simp only [quadrantLogWeight,smul_apply,gradient_apply]
  fin_cases i <;> simp [quadrantLogBasis,quadrantLogEuler,
    SchwartzMap.smulLeftCLM_apply_apply (coordinate_growth _)]

private theorem logSchwartz_euler_two (f : SchwartzMap E ℂ) (i : Fin 2) :
    (∂_{quadrantLogBasis i} (∂_{quadrantLogBasis i} (quadrantLogSchwartz σ f) : SchwartzMap E ℂ) : SchwartzMap E ℂ)=
      quadrantLogSchwartz σ (quadrantLogEuler σ i (quadrantLogEuler σ i f)) := by
  rw [logSchwartz_euler,logSchwartz_euler]

private def axisJet (v : E) : ℕ→SchwartzMap E ℂ→SchwartzMap E ℂ
  | 0,f => f
  | n+1,f => ∂_{v} (axisJet v n f)

private theorem affine_deriv (f : SchwartzMap E ℂ) (v base : E) (x : ℝ) :
    deriv (fun t : ℝ => f (base+t • v)) x=(∂_{v} f : SchwartzMap E ℂ) (base+x • v) := by
  have hc : HasDerivAt (fun t : ℝ => base+t • v) v x := by
    simpa only [one_smul] using! ((hasDerivAt_id x).smul_const v).const_add base
  exact (f.differentiableAt.hasFDerivAt.comp_hasDerivAt x hc).deriv

private theorem affine_iteratedDeriv (j : ℕ) (f : SchwartzMap E ℂ) (v base : E) (x : ℝ) :
    iteratedDeriv j (fun t : ℝ => f (base+t • v)) x=axisJet v j f (base+x • v) := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv j (fun t : ℝ => f (base+t • v))=
        fun t : ℝ => axisJet v j f (base+t • v) := funext ih
    rw [he,affine_deriv]
    rfl

private theorem axisJet_x (j : ℕ) (f : SchwartzMap E ℂ) (x y : ℝ) :
    axisJet (quadrantLogBasis 0) j f (WithLp.toLp 2 ![x,y])=
      iteratedDeriv j (fun t : ℝ => f (WithLp.toLp 2 ![t,y])) x := by
  have hp (t : ℝ) : WithLp.toLp 2 ![t,y]=
      y • quadrantLogBasis 1+t • quadrantLogBasis 0 := by
    ext i
    fin_cases i <;> simp [quadrantLogBasis]
  simp_rw [hp]
  exact (affine_iteratedDeriv j f _ _ x).symm

private theorem axisJet_y (j : ℕ) (f : SchwartzMap E ℂ) (x y : ℝ) :
    axisJet (quadrantLogBasis 1) j f (WithLp.toLp 2 ![x,y])=
      iteratedDeriv j (fun t : ℝ => f (WithLp.toLp 2 ![x,t])) y := by
  have hp (t : ℝ) : WithLp.toLp 2 ![x,t]=
      x • quadrantLogBasis 0+t • quadrantLogBasis 1 := by
    ext i
    fin_cases i <;> simp [quadrantLogBasis]
  simp_rw [hp]
  exact (affine_iteratedDeriv j f _ _ y).symm

private theorem actual_pure_jet_exterior (j m k : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℝ in atTop,
      ∀z : {z : ℝ×ℝ // 0<z.1 ∧ 0<z.2 ∧
        ¬(z.1∈Icc (1/4 : ℝ) 4 ∧ z.2∈Icc (1/4 : ℝ) 4)},
      N^k*(1+z.1.1+z.1.2)^m*
        max ‖axisJet (quadrantLogBasis 0) j (bagCubicSelectedNormalizedCone N) (WithLp.toLp 2 ![z.1.1,z.1.2])‖
          ‖axisJet (quadrantLogBasis 1) j (bagCubicSelectedNormalizedCone N) (WithLp.toLp 2 ![z.1.1,z.1.2])‖ ≤ C := by
  obtain ⟨C,hC,hCb⟩ := bagCubicNormalizedPhysicalKernel_selected_exterior_decay j m k
  refine ⟨C,hC,?_⟩
  filter_upwards [hCb,bagCubicSelectedNormalizedCone_eventually_apply] with N hN he
  intro z
  rw [axisJet_x,axisJet_y]
  have hx : (fun t : ℝ => bagCubicSelectedNormalizedCone N (WithLp.toLp 2 ![t,z.1.2]))=
      fun t : ℝ => bagCubicNormalizedPhysicalKernel (N^(-(3/4 : ℝ))) (1/Real.log N) N t z.1.2 :=
    funext (fun t => he t z.1.2)
  have hy : (fun t : ℝ => bagCubicSelectedNormalizedCone N (WithLp.toLp 2 ![z.1.1,t]))=
      fun t : ℝ => bagCubicNormalizedPhysicalKernel (N^(-(3/4 : ℝ))) (1/Real.log N) N z.1.1 t :=
    funext (fun t => he z.1.1 t)
  rw [hx,hy]
  exact hN z

private def coords : E≃ᵐℝ×ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2→ℝ)).symm.trans MeasurableEquiv.finTwoArrow

private theorem coords_preserving : MeasurePreserving coords :=
  (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

private theorem lintegral_two (F : E→ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ u : E, F u)=∫⁻ a : ℝ, ∫⁻ b : ℝ, F (WithLp.toLp 2 ![a,b]) := by
  have hp := coords_preserving.symm coords
  rw [←hp.lintegral_comp_emb coords.symm.measurableEmbedding F]
  exact lintegral_prod _ (hF.comp coords.symm.measurable).aemeasurable

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

private def point (x y : ℝ) : E := WithLp.toLp 2 ![x,y]

private theorem log_chart_lintegral (F : E→ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ u : E, F u)=∫⁻ x in Ioi (0 : ℝ), ∫⁻ y in Ioi (0 : ℝ),
      ENNReal.ofReal (x⁻¹)*(ENNReal.ofReal (y⁻¹)*F (point (-Real.log x) (-Real.log y))) := by
  rw [lintegral_two F hF]
  change (∫⁻ u : ℝ, ∫⁻ v : ℝ, F (point u v))= _
  rw [←lintegral_log_substitution (fun u : ℝ => ∫⁻ v : ℝ, F (point u v))]
  apply lintegral_congr
  intro x
  rw [←lintegral_log_substitution (fun v : ℝ => F (point (-Real.log x) v))]
  exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm

private theorem log_weight_jacobian (a b x y : ℝ) (hx : 0<x) (hy : 0<y) :
    x⁻¹*y⁻¹*Real.exp (a*Real.log x+b*Real.log y)^2=x^(2*a-1)*y^(2*b-1) := by
  rw [Real.rpow_sub hx,Real.rpow_sub hy,Real.rpow_one,Real.rpow_one,
    Real.rpow_def_of_pos hx,Real.rpow_def_of_pos hy,pow_two,←Real.exp_add]
  field_simp
  rw [←Real.exp_add]
  congr 1
  ring

private theorem logSchwartz_mass_substitution (f : SchwartzMap E ℂ) :
    (∫⁻ u : E, ENNReal.ofReal (‖quadrantLogSchwartz σ f u‖^2))=
      ∫⁻ x in Ioi (0 : ℝ), ∫⁻ y in Ioi (0 : ℝ),
        ENNReal.ofReal (x^(2*(σ 0 : ℝ)-1)*y^(2*(σ 1 : ℝ)-1)*‖f (point x y)‖^2) := by
  have hf := (quadrantLogSchwartz σ f).continuous.measurable
  rw [log_chart_lintegral _ (by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hx0 : 0<x := hx
  have hy0 : 0<y := hy
  have hn : quadrantLogNode (point (-Real.log x) (-Real.log y))=point x y := by
    ext i
    fin_cases i <;> simp [point,quadrantLogNode_apply,Real.exp_log hx0,Real.exp_log hy0]
  rw [quadrantLogSchwartz_apply]
  change ENNReal.ofReal (x⁻¹)*(ENNReal.ofReal (y⁻¹)*
    ENNReal.ofReal (‖Real.exp (-(σ 0 : ℝ)*(-Real.log x)-(σ 1 : ℝ)*(-Real.log y)) •
      f (quadrantLogNode (point (-Real.log x) (-Real.log y)))‖^2))= _
  rw [hn,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_pow,
    show -(σ 0 : ℝ)*(-Real.log x)-(σ 1 : ℝ)*(-Real.log y)=
      (σ 0 : ℝ)*Real.log x+(σ 1 : ℝ)*Real.log y by ring]
  rw [←ENNReal.ofReal_mul (inv_nonneg.mpr hy0.le),←ENNReal.ofReal_mul (inv_nonneg.mpr hx0.le)]
  congr 1
  calc x⁻¹*(y⁻¹*(Real.exp ((σ 0 : ℝ)*Real.log x+(σ 1 : ℝ)*Real.log y)^2*‖f (point x y)‖^2))=
      (x⁻¹*y⁻¹*Real.exp ((σ 0 : ℝ)*Real.log x+(σ 1 : ℝ)*Real.log y)^2)*‖f (point x y)‖^2 := by ring
    _ = _ := by rw [log_weight_jacobian _ _ x y hx0 hy0]

private def schwartzProduct (a f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  SchwartzMap.smulLeftCLM ℂ a f

private theorem schwartzProduct_apply (a f : SchwartzMap E ℂ) (x : E) :
    schwartzProduct a f x=a x*f x := by
  exact SchwartzMap.smulLeftCLM_apply_apply a.hasTemperateGrowth f x

private theorem line_product (v : E) (a f : SchwartzMap E ℂ) :
    (∂_{v} (schwartzProduct a f) : SchwartzMap E ℂ)=
      schwartzProduct (∂_{v} a) f+schwartzProduct a (∂_{v} f) := by
  ext x
  have he : (schwartzProduct a f : E→ℂ)=fun y => a y*f y := funext (schwartzProduct_apply a f)
  change fderiv ℝ (schwartzProduct a f) x v= _
  have hd := ((a.hasFDerivAt x).mul (f.hasFDerivAt x)).fderiv
  change fderiv ℝ (fun y => a y*f y) x= _ at hd
  rw [he,hd]
  simp only [add_apply,smul_apply,smul_eq_mul,schwartzProduct_apply,SchwartzMap.lineDerivOp_apply_eq_fderiv]
  ring

private theorem line_sub (v : E) (f g : SchwartzMap E ℂ) :
    (∂_{v} (f-g) : SchwartzMap E ℂ)=(∂_{v} f : SchwartzMap E ℂ)-(∂_{v} g : SchwartzMap E ℂ) := by
  simp only [sub_eq_add_neg,lineDerivOp_add,lineDerivOp_neg]

private def cutoffSchwartz : SchwartzMap E ℂ :=
  (GaloisForLFunctions.HTGeometry.mellinLocalizationCutoff_spec.2.1.comp_left
    Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp GaloisForLFunctions.HTGeometry.mellinLocalizationCutoff_spec.1)

private theorem cutoffSchwartz_apply (x : E) :
    cutoffSchwartz x=(GaloisForLFunctions.HTGeometry.mellinLocalizationCutoff x : ℂ) := rfl

private def exteriorSchwartz (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  f-schwartzProduct cutoffSchwartz f

private theorem exterior_apply (f : SchwartzMap E ℂ) (x : E) :
    exteriorSchwartz f x=(1-cutoffSchwartz x)*f x := by
  change f x-schwartzProduct cutoffSchwartz f x= _
  rw [schwartzProduct_apply]
  ring

private theorem exterior_jet_one (v : E) (f : SchwartzMap E ℂ) (x : E) :
    axisJet v 1 (exteriorSchwartz f) x=
      (1-cutoffSchwartz x)*axisJet v 1 f x-axisJet v 1 cutoffSchwartz x*f x := by
  simp only [axisJet,exteriorSchwartz,line_sub,line_product,sub_apply,add_apply,schwartzProduct_apply]
  ring

private theorem exterior_jet_two (v : E) (f : SchwartzMap E ℂ) (x : E) :
    axisJet v 2 (exteriorSchwartz f) x=
      (1-cutoffSchwartz x)*axisJet v 2 f x-
        2*axisJet v 1 cutoffSchwartz x*axisJet v 1 f x-axisJet v 2 cutoffSchwartz x*f x := by
  simp only [axisJet,exteriorSchwartz,line_sub,line_product,lineDerivOp_add,
    sub_apply,add_apply,schwartzProduct_apply]
  ring

private theorem axisJet_support (v : E) (j : ℕ) (f : SchwartzMap E ℂ) :
    tsupport (axisJet v j f)⊆tsupport f := by
  induction j with
  | zero => exact Subset.rfl
  | succ j ih => exact (SchwartzMap.tsupport_lineDerivOp_subset v _).trans ih

private theorem exterior_jets_vanish (v : E) (j : ℕ) (f : SchwartzMap E ℂ)
    (x : E) (hx : ∀i, x i∈Icc (1/4 : ℝ) 4) : axisJet v j (exteriorSchwartz f) x=0 := by
  obtain ⟨V,hV,hbox,hchi⟩ := GaloisForLFunctions.HTGeometry.mellinLocalizationCutoff_spec.2.2.2
  have he : (exteriorSchwartz f : E→ℂ)=ᶠ[𝓝 x] 0 := by
    filter_upwards [hV.mem_nhds (hbox hx)] with y hy
    simp only [exterior_apply,cutoffSchwartz_apply,hchi y hy,Complex.ofReal_one,sub_self,zero_mul]
    rfl
  have hn : x∉tsupport (exteriorSchwartz f) := notMem_tsupport_iff_eventuallyEq.mpr he
  by_contra hh
  exact hn ((axisJet_support v j _) (subset_tsupport _ hh))

private theorem cutoff_jet_bound (i : Fin 2) (j : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀x : E, ‖axisJet (quadrantLogBasis i) j cutoffSchwartz x‖ ≤ C := by
  obtain ⟨C,hC,hCb⟩ := (axisJet (quadrantLogBasis i) j cutoffSchwartz).decay 0 0
  refine ⟨C+1,by linarith,fun x => ?_⟩
  have hh : ‖axisJet (quadrantLogBasis i) j cutoffSchwartz x‖ ≤ C := by
    simpa only [pow_zero,one_mul,norm_iteratedFDeriv_zero] using hCb x
  linarith

private theorem exterior_jet_control (i : Fin 2) :
    ∃ D : ℝ, 0<D ∧ ∀(f : SchwartzMap E ℂ) (x : E) (B : ℝ),
      0 ≤ B → (∀j : Fin 3, ‖axisJet (quadrantLogBasis i) j.1 f x‖ ≤ B) →
        ∀j : Fin 3, ‖axisJet (quadrantLogBasis i) j.1 (exteriorSchwartz f) x‖ ≤ D*B := by
  obtain ⟨M0,hM0,hM0b⟩ := cutoff_jet_bound i 0
  obtain ⟨M1,hM1,hM1b⟩ := cutoff_jet_bound i 1
  obtain ⟨M2,hM2,hM2b⟩ := cutoff_jet_bound i 2
  refine ⟨1+M0+2*M1+M2,by positivity,fun f x B hB hf j => ?_⟩
  have hA : ‖1-cutoffSchwartz x‖ ≤ 1+M0 := by
    calc ‖1-cutoffSchwartz x‖ ≤ ‖(1 : ℂ)‖+‖cutoffSchwartz x‖ := norm_sub_le _ _
      _ ≤ 1+M0 := by simpa only [norm_one,axisJet] using add_le_add_right (hM0b x) 1
  have h0 : ‖f x‖ ≤ B := hf 0
  have h1 : ‖axisJet (quadrantLogBasis i) 1 f x‖ ≤ B := hf 1
  have h2 : ‖axisJet (quadrantLogBasis i) 2 f x‖ ≤ B := hf 2
  fin_cases j
  · change ‖exteriorSchwartz f x‖ ≤ _
    rw [exterior_apply,norm_mul]
    calc ‖1-cutoffSchwartz x‖*‖f x‖ ≤ (1+M0)*B :=
        mul_le_mul hA h0 (norm_nonneg _) (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg hM1.le hB,mul_nonneg hM2.le hB]
  · change ‖axisJet (quadrantLogBasis i) 1 (exteriorSchwartz f) x‖ ≤ _
    rw [exterior_jet_one]
    calc ‖(1-cutoffSchwartz x)*axisJet (quadrantLogBasis i) 1 f x-
          axisJet (quadrantLogBasis i) 1 cutoffSchwartz x*f x‖ ≤
        ‖(1-cutoffSchwartz x)*axisJet (quadrantLogBasis i) 1 f x‖+
          ‖axisJet (quadrantLogBasis i) 1 cutoffSchwartz x*f x‖ := norm_sub_le _ _
      _ ≤ (1+M0)*B+M1*B := by
        rw [norm_mul,norm_mul]
        exact add_le_add
          (mul_le_mul hA h1 (norm_nonneg _) (by positivity))
          (mul_le_mul (hM1b x) h0 (norm_nonneg _) hM1.le)
      _ ≤ _ := by nlinarith [mul_nonneg hM1.le hB,mul_nonneg hM2.le hB]
  · change ‖axisJet (quadrantLogBasis i) 2 (exteriorSchwartz f) x‖ ≤ _
    rw [exterior_jet_two]
    calc ‖(1-cutoffSchwartz x)*axisJet (quadrantLogBasis i) 2 f x-
          2*axisJet (quadrantLogBasis i) 1 cutoffSchwartz x*axisJet (quadrantLogBasis i) 1 f x-
            axisJet (quadrantLogBasis i) 2 cutoffSchwartz x*f x‖ ≤
        ‖(1-cutoffSchwartz x)*axisJet (quadrantLogBasis i) 2 f x-
          2*axisJet (quadrantLogBasis i) 1 cutoffSchwartz x*axisJet (quadrantLogBasis i) 1 f x‖+
            ‖axisJet (quadrantLogBasis i) 2 cutoffSchwartz x*f x‖ := norm_sub_le _ _
      _ ≤ (‖(1-cutoffSchwartz x)*axisJet (quadrantLogBasis i) 2 f x‖+
          ‖2*axisJet (quadrantLogBasis i) 1 cutoffSchwartz x*axisJet (quadrantLogBasis i) 1 f x‖)+
            ‖axisJet (quadrantLogBasis i) 2 cutoffSchwartz x*f x‖ :=
        add_le_add_left (norm_sub_le _ _) _
      _ ≤ ((1+M0)*B+2*M1*B)+M2*B := by
        simp only [norm_mul,Complex.norm_ofNat]
        exact add_le_add
          (add_le_add (mul_le_mul hA h2 (norm_nonneg _) (by positivity))
            (mul_le_mul (mul_le_mul_of_nonneg_left (hM1b x) (by norm_num)) h1
              (norm_nonneg _) (by positivity)))
          (mul_le_mul (hM2b x) h0 (norm_nonneg _) hM2.le)
      _ = _ := by ring

private theorem norm_axis_le_max (i : Fin 2) (j : ℕ) (f : SchwartzMap E ℂ) (x : E) :
    ‖axisJet (quadrantLogBasis i) j f x‖ ≤
      max ‖axisJet (quadrantLogBasis 0) j f x‖ ‖axisJet (quadrantLogBasis 1) j f x‖ := by
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

private theorem exterior_pure_jets (i : Fin 2) (m k : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℝ in atTop,
      ∀z : {z : ℝ×ℝ // 0<z.1 ∧ 0<z.2}, ∀j : Fin 3,
        N^k*(1+z.1.1+z.1.2)^m*
          ‖axisJet (quadrantLogBasis i) j.1 (exteriorSchwartz (bagCubicSelectedNormalizedCone N))
            (point z.1.1 z.1.2)‖ ≤ C := by
  obtain ⟨D,hD,hDb⟩ := exterior_jet_control i
  obtain ⟨C0,hC0,hC0b⟩ := actual_pure_jet_exterior 0 m k
  obtain ⟨C1,hC1,hC1b⟩ := actual_pure_jet_exterior 1 m k
  obtain ⟨C2,hC2,hC2b⟩ := actual_pure_jet_exterior 2 m k
  refine ⟨D*(C0+C1+C2),mul_pos hD (add_pos (add_pos hC0 hC1) hC2),?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ),hC0b,hC1b,hC2b] with N hN h0 h1 h2
  intro z j
  by_cases hz : z.1.1∈Icc (1/4 : ℝ) 4 ∧ z.1.2∈Icc (1/4 : ℝ) 4
  · have hb : ∀i, point z.1.1 z.1.2 i∈Icc (1/4 : ℝ) 4 := by
      intro j
      fin_cases j
      · change z.1.1∈Icc (1/4 : ℝ) 4
        exact hz.1
      · change z.1.2∈Icc (1/4 : ℝ) 4
        exact hz.2
    rw [exterior_jets_vanish _ _ _ _ hb,norm_zero,mul_zero]
    positivity
  · let w : {w : ℝ×ℝ // 0<w.1 ∧ 0<w.2 ∧
        ¬(w.1∈Icc (1/4 : ℝ) 4 ∧ w.2∈Icc (1/4 : ℝ) 4)} := ⟨z.1,z.2.1,z.2.2,hz⟩
    let f := bagCubicSelectedNormalizedCone N
    let rho := N^k*(1+z.1.1+z.1.2)^m
    have hrho : 0<rho := mul_pos (pow_pos hN _) (pow_pos (by linarith [z.2.1,z.2.2]) _)
    have hraw (j : Fin 3) : rho*‖axisJet (quadrantLogBasis i) j.1 f (point z.1.1 z.1.2)‖ ≤ C0+C1+C2 := by
      have he : rho*‖axisJet (quadrantLogBasis i) j.1 f (point z.1.1 z.1.2)‖ ≤
          rho*max ‖axisJet (quadrantLogBasis 0) j.1 f (point z.1.1 z.1.2)‖
            ‖axisJet (quadrantLogBasis 1) j.1 f (point z.1.1 z.1.2)‖ :=
        mul_le_mul_of_nonneg_left (norm_axis_le_max i j.1 f _) hrho.le
      fin_cases j
      · exact he.trans ((h0 w).trans (by linarith))
      · exact he.trans ((h1 w).trans (by linarith))
      · exact he.trans ((h2 w).trans (by linarith))
    have hin (j : Fin 3) : ‖axisJet (quadrantLogBasis i) j.1 f (point z.1.1 z.1.2)‖ ≤
        (C0+C1+C2)/rho := by
      apply (le_div_iff₀ hrho).mpr
      simpa only [mul_comm] using hraw j
    have he := hDb f (point z.1.1 z.1.2) ((C0+C1+C2)/rho) (by positivity) hin j
    change rho*‖axisJet (quadrantLogBasis i) j.1 (exteriorSchwartz f) (point z.1.1 z.1.2)‖ ≤ _
    refine (mul_le_mul_of_nonneg_left he hrho.le).trans_eq ?_
    field_simp

private def coordinateProduct (i : Fin 2) (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x : E => x i) f

private theorem coordinateProduct_apply (i : Fin 2) (f : SchwartzMap E ℂ) (x : E) :
    coordinateProduct i f x=(x i : ℂ)*f x := by
  simpa only [coordinateProduct,Complex.real_smul] using!
    SchwartzMap.smulLeftCLM_apply_apply (coordinate_growth i) f x

private theorem line_coordinate (i : Fin 2) (v : E) (f : SchwartzMap E ℂ) :
    (∂_{v} (coordinateProduct i f) : SchwartzMap E ℂ)=
      (v i) • f+coordinateProduct i (∂_{v} f) := by
  ext x
  have he : (coordinateProduct i f : E→ℂ)=fun y => y i • f y := by
    funext y
    rw [coordinateProduct_apply,Complex.real_smul]
  have hd := (((coord i).hasFDerivAt (x := x)).smul (f.hasFDerivAt x)).fderiv
  change fderiv ℝ (fun y : E => y i • f y) x= _ at hd
  change fderiv ℝ (coordinateProduct i f) x v= _
  rw [he,hd]
  simp [coordinateProduct_apply,coord,SchwartzMap.lineDerivOp_apply_eq_fderiv,
    Complex.real_smul]
  ring

private theorem euler_representation (i : Fin 2) (f : SchwartzMap E ℂ) :
    quadrantLogEuler σ i f=(-(σ i : ℝ)) • f-coordinateProduct i (∂_{quadrantLogBasis i} f) := rfl

private theorem euler_apply (i : Fin 2) (f : SchwartzMap E ℂ) (x : E) :
    quadrantLogEuler σ i f x=-((σ i : ℝ) : ℂ)*f x-
      (x i : ℂ)*(∂_{quadrantLogBasis i} f : SchwartzMap E ℂ) x := by
  rw [euler_representation]
  simp only [sub_apply,smul_apply,coordinateProduct_apply,Complex.real_smul,Complex.ofReal_neg]

private theorem euler_two_apply (i : Fin 2) (f : SchwartzMap E ℂ) (x : E) :
    quadrantLogEuler σ i (quadrantLogEuler σ i f) x=
      ((σ i : ℝ) : ℂ)^2*f x+
        ((2*(σ i : ℝ)+1 : ℝ) : ℂ)*(x i : ℂ)*axisJet (quadrantLogBasis i) 1 f x+
          (x i : ℂ)^2*axisJet (quadrantLogBasis i) 2 f x := by
  have hd : (∂_{quadrantLogBasis i} (quadrantLogEuler σ i f) : SchwartzMap E ℂ)=
      (-(σ i : ℝ)) • (∂_{quadrantLogBasis i} f : SchwartzMap E ℂ)-
        ((∂_{quadrantLogBasis i} f : SchwartzMap E ℂ)+
          coordinateProduct i (∂_{quadrantLogBasis i} (∂_{quadrantLogBasis i} f : SchwartzMap E ℂ))) := by
    rw [euler_representation,line_sub,lineDerivOp_smul,line_coordinate]
    simp [quadrantLogBasis]
  rw [euler_apply,euler_apply,hd]
  simp only [sub_apply,add_apply,smul_apply,coordinateProduct_apply,Complex.real_smul,
    Complex.ofReal_neg,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_one,axisJet]
  ring

private theorem euler_two_norm (hσ : ∀i, (σ i : ℝ) ≤ 2) (i : Fin 2)
    (f : SchwartzMap E ℂ) (x : E) (hx : ∀j, 0<x j) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀j : Fin 3, ‖axisJet (quadrantLogBasis i) j.1 f x‖ ≤ B) :
    ‖quadrantLogEuler σ i (quadrantLogEuler σ i f) x‖ ≤ 10*(1+x 0+x 1)^2*B := by
  let w := 1+x 0+x 1
  have hw : 1 ≤ w := by dsimp only [w]; linarith [hx 0,hx 1]
  have hxi : x i ≤ w := by
    fin_cases i
    · change x 0 ≤ w
      dsimp only [w]
      linarith [hx 1]
    · change x 1 ≤ w
      dsimp only [w]
      linarith [hx 0]
  have hs : 0<(σ i : ℝ) := (σ i).2
  have hs2 : (σ i : ℝ)^2 ≤ 4 := by nlinarith [hσ i]
  have hlin : (2*(σ i : ℝ)+1)*x i ≤ 5*w :=
    mul_le_mul (by linarith [hσ i]) hxi (hx i).le (by norm_num)
  have hsq : (x i)^2 ≤ w^2 := pow_le_pow_left₀ (hx i).le hxi 2
  have hcoef : (σ i : ℝ)^2+(2*(σ i : ℝ)+1)*x i+(x i)^2 ≤ 10*w^2 := by
    nlinarith [sq_nonneg (w-1)]
  have h0 : ‖f x‖ ≤ B := hf 0
  have h1 : ‖axisJet (quadrantLogBasis i) 1 f x‖ ≤ B := hf 1
  have h2 : ‖axisJet (quadrantLogBasis i) 2 f x‖ ≤ B := hf 2
  rw [euler_two_apply]
  calc ‖((σ i : ℝ) : ℂ)^2*f x+
        ((2*(σ i : ℝ)+1 : ℝ) : ℂ)*(x i : ℂ)*axisJet (quadrantLogBasis i) 1 f x+
          (x i : ℂ)^2*axisJet (quadrantLogBasis i) 2 f x‖ ≤
      ‖((σ i : ℝ) : ℂ)^2*f x+
        ((2*(σ i : ℝ)+1 : ℝ) : ℂ)*(x i : ℂ)*axisJet (quadrantLogBasis i) 1 f x‖+
          ‖(x i : ℂ)^2*axisJet (quadrantLogBasis i) 2 f x‖ := norm_add_le _ _
    _ ≤ (‖((σ i : ℝ) : ℂ)^2*f x‖+
        ‖((2*(σ i : ℝ)+1 : ℝ) : ℂ)*(x i : ℂ)*axisJet (quadrantLogBasis i) 1 f x‖)+
          ‖(x i : ℂ)^2*axisJet (quadrantLogBasis i) 2 f x‖ :=
      add_le_add_left (norm_add_le _ _) _
    _ ≤ (σ i : ℝ)^2*B+(2*(σ i : ℝ)+1)*x i*B+(x i)^2*B := by
      simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs,
        abs_of_pos (hx i),abs_of_pos (by linarith : 0<2*(σ i : ℝ)+1)]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left h0 (sq_nonneg _))
        (mul_le_mul_of_nonneg_left h1 (mul_nonneg (by linarith : 0 ≤ 2*(σ i : ℝ)+1) (hx i).le)))
        (mul_le_mul_of_nonneg_left h2 (sq_nonneg _))
    _ = ((σ i : ℝ)^2+(2*(σ i : ℝ)+1)*x i+(x i)^2)*B := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hB

private theorem exterior_euler_two_decay (i : Fin 2) (m k : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℝ in atTop,
      ∀(σ : Fin 2→{r : ℝ // 0<r}), (∀i, (σ i : ℝ) ≤ 2) →
        ∀z : {z : ℝ×ℝ // 0<z.1 ∧ 0<z.2},
          N^k*(1+z.1.1+z.1.2)^m*
            ‖quadrantLogEuler σ i (quadrantLogEuler σ i
              (exteriorSchwartz (bagCubicSelectedNormalizedCone N))) (point z.1.1 z.1.2)‖ ≤ C := by
  obtain ⟨C,hC,hCb⟩ := exterior_pure_jets i (m+2) k
  refine ⟨10*C,mul_pos (by norm_num) hC,?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ),hCb] with N hN hB
  intro σ hσ z
  let f := exteriorSchwartz (bagCubicSelectedNormalizedCone N)
  let w := 1+z.1.1+z.1.2
  let rho := N^k*w^(m+2)
  let B := C/rho
  have hw : 0<w := by dsimp only [w]; linarith [z.2.1,z.2.2]
  have hrho : 0<rho := mul_pos (pow_pos hN _) (pow_pos hw _)
  have hpos : 0 ≤ B := div_nonneg hC.le hrho.le
  have hin (j : Fin 3) : ‖axisJet (quadrantLogBasis i) j.1 f (point z.1.1 z.1.2)‖ ≤ B := by
    apply (le_div_iff₀ hrho).mpr
    simpa only [mul_comm] using hB z j
  have hx : ∀j, 0<point z.1.1 z.1.2 j := by
    intro j
    fin_cases j
    · exact z.2.1
    · exact z.2.2
  have he : ‖quadrantLogEuler σ i (quadrantLogEuler σ i f) (point z.1.1 z.1.2)‖ ≤ 10*w^2*B :=
    euler_two_norm σ hσ i f _ hx B hpos hin
  change N^k*w^m*‖quadrantLogEuler σ i (quadrantLogEuler σ i f) (point z.1.1 z.1.2)‖ ≤ _
  refine (mul_le_mul_of_nonneg_left he (mul_nonneg (pow_nonneg hN.le _) (pow_nonneg hw.le _))).trans_eq ?_
  dsimp only [B,rho]
  rw [pow_add]
  field_simp

private def inverseSquare (x : ℝ) : ℝ := 1/(1+|x|)^2

private theorem inverseSquare_nonneg (x : ℝ) : 0 ≤ inverseSquare x := by
  unfold inverseSquare
  positivity

private theorem inverseSquare_integrable : Integrable inverseSquare := by
  have hh := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num)
  convert hh using 1
  funext x
  rw [Real.norm_eq_abs,Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1+|x|),Real.rpow_two]
  simp only [inverseSquare,one_div]

private theorem inverseSquare_lintegral_two :
    (∫⁻ x : ℝ, ∫⁻ y : ℝ, ENNReal.ofReal (inverseSquare x*inverseSquare y))=
      ENNReal.ofReal ((∫x : ℝ, inverseSquare x)^2) := by
  have hI : 0 ≤ ∫x : ℝ, inverseSquare x := integral_nonneg inverseSquare_nonneg
  have hi := ofReal_integral_eq_lintegral_ofReal inverseSquare_integrable
    (Eventually.of_forall inverseSquare_nonneg)
  simp_rw [ENNReal.ofReal_mul (inverseSquare_nonneg _),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←hi]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,←hi,←ENNReal.ofReal_mul hI,pow_two]

private theorem log_density_bound (hσ : ∀i, (σ i : ℝ)∈Icc (1 : ℝ) 2)
    (f : SchwartzMap E ℂ) (C : ℝ)
    (hb : ∀z : {z : ℝ×ℝ // 0<z.1 ∧ 0<z.2},
      (1+z.1.1+z.1.2)^8*‖f (point z.1.1 z.1.2)‖ ≤ C)
    (x y : ℝ) (hx : 0<x) (hy : 0<y) :
    x^(2*(σ 0 : ℝ)-1)*y^(2*(σ 1 : ℝ)-1)*‖f (point x y)‖^2 ≤
      C^2*inverseSquare x*inverseSquare y := by
  let w := 1+x+y
  have hw : 1 ≤ w := by dsimp only [w]; linarith
  have hw0 : 0<w := zero_lt_one.trans_le hw
  have hxw : x ≤ w := by dsimp only [w]; linarith
  have hyw : y ≤ w := by dsimp only [w]; linarith
  have hpx : x^(2*(σ 0 : ℝ)-1) ≤ w^3 := by
    calc x^(2*(σ 0 : ℝ)-1) ≤ w^(2*(σ 0 : ℝ)-1) :=
        Real.rpow_le_rpow hx.le hxw (by linarith [(hσ 0).1])
      _ ≤ w^(3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hw (by linarith [(hσ 0).2])
      _ = w^3 := Real.rpow_ofNat _ _
  have hpy : y^(2*(σ 1 : ℝ)-1) ≤ w^3 := by
    calc y^(2*(σ 1 : ℝ)-1) ≤ w^(2*(σ 1 : ℝ)-1) :=
        Real.rpow_le_rpow hy.le hyw (by linarith [(hσ 1).1])
      _ ≤ w^(3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hw (by linarith [(hσ 1).2])
      _ = w^3 := Real.rpow_ofNat _ _
  have hnorm : ‖f (point x y)‖ ≤ C/w^8 := by
    apply (le_div_iff₀ (pow_pos hw0 _)).mpr
    simpa only [mul_comm] using hb ⟨(x,y),hx,hy⟩
  have hsq : ‖f (point x y)‖^2 ≤ C^2/w^16 := by
    simpa only [div_pow,←pow_mul] using pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hp : x^(2*(σ 0 : ℝ)-1)*y^(2*(σ 1 : ℝ)-1) ≤ w^6 := by
    calc x^(2*(σ 0 : ℝ)-1)*y^(2*(σ 1 : ℝ)-1) ≤ w^3*w^3 :=
        mul_le_mul hpx hpy (Real.rpow_nonneg hy.le _) (pow_nonneg hw0.le _)
      _ = w^6 := by ring
  have hden : (1+x)^2*(1+y)^2 ≤ w^10 := by
    calc
      (1+x)^2*(1+y)^2 ≤ w^2*w^2 := by
        apply mul_le_mul
        · exact pow_le_pow_left₀ (by linarith) (by dsimp only [w]; linarith) 2
        · exact pow_le_pow_left₀ (by linarith) (by dsimp only [w]; linarith) 2
        · positivity
        · positivity
      _ = w^4 := by ring
      _ ≤ w^10 := pow_le_pow_right₀ hw (by norm_num)
  calc x^(2*(σ 0 : ℝ)-1)*y^(2*(σ 1 : ℝ)-1)*‖f (point x y)‖^2 ≤
      w^6*(C^2/w^16) := mul_le_mul hp hsq (sq_nonneg _) (pow_nonneg hw0.le _)
    _ = C^2/w^10 := by field_simp
    _ ≤ C^2/((1+x)^2*(1+y)^2) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
    _ = C^2*inverseSquare x*inverseSquare y := by
      simp only [inverseSquare,abs_of_pos hx,abs_of_pos hy,div_eq_mul_inv,mul_inv_rev]
      ring

private theorem log_mass_bound :
    ∃ D : ℝ, 0<D ∧ ∀(σ : Fin 2→{r : ℝ // 0<r}),
      (∀i, (σ i : ℝ)∈Icc (1 : ℝ) 2) → ∀(f : SchwartzMap E ℂ) (C : ℝ),
        (∀z : {z : ℝ×ℝ // 0<z.1 ∧ 0<z.2}, (1+z.1.1+z.1.2)^8*‖f (point z.1.1 z.1.2)‖ ≤ C) →
          (∫⁻ u : E, ENNReal.ofReal (‖quadrantLogSchwartz σ f u‖^2)) ≤ ENNReal.ofReal (D*C^2) := by
  let baseMass := ∫x : ℝ, inverseSquare x
  refine ⟨baseMass^2+1,by positivity,fun σ hσ f C hb => ?_⟩
  rw [logSchwartz_mass_substitution]
  calc
    (∫⁻ x in Ioi (0 : ℝ), ∫⁻ y in Ioi (0 : ℝ),
      ENNReal.ofReal (x^(2*(σ 0 : ℝ)-1)*y^(2*(σ 1 : ℝ)-1)*‖f (point x y)‖^2)) ≤
        ∫⁻ x in Ioi (0 : ℝ), ∫⁻ y in Ioi (0 : ℝ),
          ENNReal.ofReal (C^2*inverseSquare x*inverseSquare y) := by
      apply setLIntegral_mono' measurableSet_Ioi
      intro x hx
      apply setLIntegral_mono' measurableSet_Ioi
      intro y hy
      exact ENNReal.ofReal_le_ofReal (log_density_bound σ hσ f C hb x y hx hy)
    _ ≤ ∫⁻ x : ℝ, ∫⁻ y : ℝ, ENNReal.ofReal (C^2*inverseSquare x*inverseSquare y) := by
      refine (lintegral_mono (fun x => setLIntegral_le_lintegral _ _)).trans ?_
      exact setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (C^2)*ENNReal.ofReal (baseMass^2) := by
      simp only [mul_assoc,ENNReal.ofReal_mul (sq_nonneg C)]
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [inverseSquare_lintegral_two]
    _ ≤ ENNReal.ofReal ((baseMass^2+1)*C^2) := by
      rw [←ENNReal.ofReal_mul (sq_nonneg C)]
      exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg C])

private def lineParameters (q : {q : E // ∀i, q i∈Icc (1 : ℝ) 2}) :
    Fin 2→{r : ℝ // 0<r} := fun i => ⟨q.1 i,zero_lt_one.trans_le (q.2 i).1⟩

/-- The literal complete moving-line logarithmic profile of the selected BAG cone. -/
def bagCubicSelectedMellin (q : {q : E // ∀i, q i∈Icc (1 : ℝ) 2}) (N : ℝ) : SchwartzMap E ℂ :=
  quadrantLogSchwartz (lineParameters q) (bagCubicSelectedNormalizedCone N)

/-- The actual physical exterior remainder under the complete logarithmic weight. -/
def bagCubicSelectedExteriorMellin (q : {q : E // ∀i, q i∈Icc (1 : ℝ) 2}) (N : ℝ) : SchwartzMap E ℂ :=
  quadrantLogSchwartz (lineParameters q) (exteriorSchwartz (bagCubicSelectedNormalizedCone N))

/-- Exact local-plus-exterior decomposition of the full selected Mellin profile. -/
theorem bagCubicSelectedMellin_decomposition (q : {q : E // ∀i, q i∈Icc (1 : ℝ) 2}) (N : ℝ) :
    bagCubicSelectedMellin q N=
      GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q (bagCubicSelectedNormalizedCone N)+
        bagCubicSelectedExteriorMellin q N := by
  ext u
  simp only [bagCubicSelectedMellin,bagCubicSelectedExteriorMellin,quadrantLogSchwartz_apply,
    add_apply,GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz_apply,
    GaloisForLFunctions.HTGeometry.compactLocalizedMellinProfile_eq,exterior_apply,cutoffSchwartz_apply,
    lineParameters,Complex.real_smul]
  ring

private theorem exterior_mass_decay (k : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℝ in atTop,
      ∀q : {q : E // ∀i, q i∈Icc (1 : ℝ) 2},
        (∫⁻ u : E, ENNReal.ofReal (‖bagCubicSelectedExteriorMellin q N u‖^2)) ≤
          ENNReal.ofReal (C/N^(2*k)) := by
  obtain ⟨D,hD,hDb⟩ := log_mass_bound
  obtain ⟨A,hA,hAb⟩ := exterior_pure_jets 0 8 k
  refine ⟨D*A^2,mul_pos hD (sq_pos_of_pos hA),?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ),hAb] with N hN hb
  intro q
  have hnorm (z : {z : ℝ×ℝ // 0<z.1 ∧ 0<z.2}) :
      (1+z.1.1+z.1.2)^8*‖exteriorSchwartz (bagCubicSelectedNormalizedCone N) (point z.1.1 z.1.2)‖ ≤
        A/N^k := by
    apply (le_div_iff₀ (pow_pos hN k)).mpr
    have hh := hb z 0
    change N^k*(1+z.1.1+z.1.2)^8*
      ‖exteriorSchwartz (bagCubicSelectedNormalizedCone N) (point z.1.1 z.1.2)‖ ≤ A at hh
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hh
  have hh := hDb (lineParameters q) (fun i => q.2 i)
    (exteriorSchwartz (bagCubicSelectedNormalizedCone N)) (A/N^k) hnorm
  refine hh.trans_eq ?_
  congr 1
  rw [div_pow,←pow_mul,Nat.mul_comm k 2]
  ring

private theorem exterior_second_mass_decay (i : Fin 2) (k : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℝ in atTop,
      ∀q : {q : E // ∀i, q i∈Icc (1 : ℝ) 2},
        (∫⁻ u : E, ENNReal.ofReal (‖axisJet (quadrantLogBasis i) 2
          (bagCubicSelectedExteriorMellin q N) u‖^2)) ≤ ENNReal.ofReal (C/N^(2*k)) := by
  obtain ⟨D,hD,hDb⟩ := log_mass_bound
  obtain ⟨A,hA,hAb⟩ := exterior_euler_two_decay i 8 k
  refine ⟨D*A^2,mul_pos hD (sq_pos_of_pos hA),?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ),hAb] with N hN hb
  intro q
  let f := exteriorSchwartz (bagCubicSelectedNormalizedCone N)
  let g := quadrantLogEuler (lineParameters q) i (quadrantLogEuler (lineParameters q) i f)
  have hnorm (z : {z : ℝ×ℝ // 0<z.1 ∧ 0<z.2}) :
      (1+z.1.1+z.1.2)^8*‖g (point z.1.1 z.1.2)‖ ≤ A/N^k := by
    apply (le_div_iff₀ (pow_pos hN k)).mpr
    have hh := hb (lineParameters q) (fun j => (q.2 j).2) z
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hh
  have he : axisJet (quadrantLogBasis i) 2 (bagCubicSelectedExteriorMellin q N)=
      quadrantLogSchwartz (lineParameters q) g := logSchwartz_euler_two (lineParameters q) f i
  rw [he]
  have hh := hDb (lineParameters q) (fun j => q.2 j) g (A/N^k) hnorm
  refine hh.trans_eq ?_
  congr 1
  rw [div_pow,←pow_mul,Nat.mul_comm k 2]
  ring

private def mass (f : E→ℂ) : ℝ≥0∞ := ∫⁻ x : E, ENNReal.ofReal (‖f x‖^2)


private theorem mass_schwartz (f : SchwartzMap E ℂ) :
    mass f=ENNReal.ofReal (∫x : E, ‖f x‖^2) := by
  exact (ofReal_integral_eq_lintegral_ofReal
    ((f.memLp 2).integrable_norm_pow (by norm_num : 2≠0))
      (Eventually.of_forall (fun x : E => sq_nonneg ‖f x‖))).symm


private def axialMoment (p : ℝ) (i : Fin 2) (f : SchwartzMap E ℂ) : ℝ≥0∞ :=
  ∫⁻ ξ : E, ENNReal.ofReal (|ξ i|^p*‖(𝓕 f) ξ‖^2)


private theorem inner_basis (ξ : E) (i : Fin 2) :
    inner ℝ ξ (HTGeometry.quadrantLogBasis i)=ξ i := by
  change inner ℝ ξ (EuclideanSpace.single i (1 : ℝ))=ξ i
  simp [EuclideanSpace.inner_single_right]


private theorem derivative_fourier_norm (i : Fin 2) (f : SchwartzMap E ℂ) (ξ : E) :
    ‖(𝓕 (∂_{HTGeometry.quadrantLogBasis i} f : SchwartzMap E ℂ)) ξ‖^2=
      (2*Real.pi)^2*|ξ i|^2*‖(𝓕 f) ξ‖^2 := by
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  have ht : (inner ℝ · (HTGeometry.quadrantLogBasis i)).HasTemperateGrowth :=
    ((innerSL ℝ).flip (HTGeometry.quadrantLogBasis i)).hasTemperateGrowth
  have hc : ‖(2*Real.pi*Complex.I : ℂ)‖=2*Real.pi := by
    simp [Complex.norm_real,abs_of_pos Real.pi_pos]
  change ‖(2*Real.pi*Complex.I : ℂ) •
    ((SchwartzMap.smulLeftCLM ℂ (fun x : E => inner ℝ x (HTGeometry.quadrantLogBasis i)) (𝓕 f)) ξ)‖^2= _
  rw [SchwartzMap.smulLeftCLM_apply_apply ht,norm_smul,norm_smul,hc,inner_basis]
  simp only [Real.norm_eq_abs,mul_pow,mul_assoc]


private theorem mass_fourier (f : SchwartzMap E ℂ) : mass (𝓕 f : SchwartzMap E ℂ)=mass f := by
  rw [mass_schwartz,mass_schwartz,SchwartzMap.integral_norm_sq_fourier]


private theorem weight_axes_bound (p : ℝ) (hp : 0 ≤ p) (a b : ℝ) :
    (1+|a|+|b|)^p ≤ (3 : ℝ)^p*(1+|a|^p+|b|^p) := by
  let M := max 1 (max |a| |b|)
  have hM : 0<M := zero_lt_one.trans_le (le_max_left _ _)
  have ha : |a| ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hb : |b| ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have h1 : 1 ≤ M := le_max_left _ _
  have hmax : M^p ≤ 1+|a|^p+|b|^p := by
    by_cases hsmall : max |a| |b| ≤ 1
    · rw [show M=1 from max_eq_left hsmall,Real.one_rpow]
      linarith [Real.rpow_nonneg (abs_nonneg a) p,Real.rpow_nonneg (abs_nonneg b) p]
    · rw [show M=max |a| |b| from max_eq_right (le_of_not_ge hsmall)]
      by_cases hab : |a| ≤ |b|
      · rw [max_eq_right hab]
        linarith [Real.rpow_nonneg (abs_nonneg a) p]
      · rw [max_eq_left (le_of_not_ge hab)]
        linarith [Real.rpow_nonneg (abs_nonneg b) p]
  calc (1+|a|+|b|)^p ≤ (3*M)^p :=
      Real.rpow_le_rpow (by positivity) (by linarith) hp
    _ = (3 : ℝ)^p*M^p := Real.mul_rpow (by norm_num) hM.le
    _ ≤ _ := mul_le_mul_of_nonneg_left hmax (Real.rpow_nonneg (by norm_num) _)

private def fourthEnergy (f : SchwartzMap E ℂ) : ℝ≥0∞ :=
  ∫⁻ ξ : E, ENNReal.ofReal ((1+|ξ 0|+|ξ 1|)^(4 : ℝ)*‖(𝓕 f) ξ‖^2)

private theorem fourthEnergy_axes (f : SchwartzMap E ℂ) :
    fourthEnergy f ≤ ENNReal.ofReal ((3 : ℝ)^(4 : ℝ))*
      (mass f+axialMoment (4 : ℝ) 0 f+axialMoment (4 : ℝ) 1 f) := by
  have hf := (𝓕 f).continuous.measurable
  have hm : Measurable (fun ξ : E => ENNReal.ofReal (‖(𝓕 f) ξ‖^2)) := by fun_prop
  have h0 : Measurable (fun ξ : E => ENNReal.ofReal (|ξ 0|^(4 : ℝ)*‖(𝓕 f) ξ‖^2)) := by fun_prop
  have he : (∫⁻ ξ : E, ENNReal.ofReal ((3 : ℝ)^(4 : ℝ))*
      (ENNReal.ofReal (‖(𝓕 f) ξ‖^2)+
        ENNReal.ofReal (|ξ 0|^(4 : ℝ)*‖(𝓕 f) ξ‖^2)+
          ENNReal.ofReal (|ξ 1|^(4 : ℝ)*‖(𝓕 f) ξ‖^2)))=
      ENNReal.ofReal ((3 : ℝ)^(4 : ℝ))*
        (mass f+axialMoment (4 : ℝ) 0 f+axialMoment (4 : ℝ) 1 f) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hm0 : Measurable (fun ξ : E => ENNReal.ofReal (‖(𝓕 f) ξ‖^2)+
        ENNReal.ofReal (|ξ 0|^(4 : ℝ)*‖(𝓕 f) ξ‖^2)) := hm.add h0
    rw [lintegral_add_left hm0,lintegral_add_left hm]
    rw [←mass_fourier f]
    rfl
  rw [←he]
  apply lintegral_mono
  intro ξ
  change ENNReal.ofReal _ ≤ ENNReal.ofReal _*(_+_+_)
  rw [←ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _)),
    ←ENNReal.ofReal_add (by positivity) (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _)),
    ←ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
  apply ENNReal.ofReal_le_ofReal
  have hb := mul_le_mul_of_nonneg_right (weight_axes_bound (4 : ℝ) (by norm_num)
    (ξ 0) (ξ 1)) (sq_nonneg ‖(𝓕 f) ξ‖)
  convert! hb using 1
  ring

private theorem second_fourier_norm (i : Fin 2) (f : SchwartzMap E ℂ) (ξ : E) :
    ‖(𝓕 (axisJet (quadrantLogBasis i) 2 f)) ξ‖^2=
      (2*Real.pi)^4*|ξ i|^4*‖(𝓕 f) ξ‖^2 := by
  simp only [axisJet,derivative_fourier_norm]
  ring

private theorem axial_fourth_le_second_mass (i : Fin 2) (f : SchwartzMap E ℂ) :
    axialMoment 4 i f ≤ mass (axisJet (quadrantLogBasis i) 2 f) := by
  have hK : 0 ≤ 2*Real.pi := by positivity
  have hK1 : 1 ≤ (2*Real.pi)^4 := one_le_pow₀ (by linarith [Real.pi_gt_three])
  have he : mass (axisJet (quadrantLogBasis i) 2 f)=
      ENNReal.ofReal ((2*Real.pi)^4)*axialMoment 4 i f := by
    rw [←mass_fourier]
    simp only [mass,axialMoment,second_fourier_norm,Real.rpow_ofNat,mul_assoc,
      ENNReal.ofReal_mul (pow_nonneg hK 4)]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [he]
  calc axialMoment 4 i f=1*axialMoment 4 i f := (one_mul _).symm
    _ ≤ _ := mul_le_mul_left (by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hK1) _

private theorem fourth_energy_bound (f : SchwartzMap E ℂ) :
    fourthEnergy f ≤ ENNReal.ofReal ((3 : ℝ)^(4 : ℝ))*
      (mass f+mass (axisJet (quadrantLogBasis 0) 2 f)+mass (axisJet (quadrantLogBasis 1) 2 f)) := by
  refine (fourthEnergy_axes f).trans ?_
  exact mul_le_mul_right (add_le_add (add_le_add le_rfl (axial_fourth_le_second_mass 0 f))
    (axial_fourth_le_second_mass 1 f)) _

/-- Arbitrary power saving for the full H² energy of the actual Mellin exterior,
uniformly over the complete moving-line parameter square. -/
theorem bagCubicSelectedExteriorMellin_energy_decay (k : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℝ in atTop,
      ∀q : {q : E // ∀i, q i∈Icc (1 : ℝ) 2},
        (∫⁻ ξ : E, ENNReal.ofReal ((1+|ξ 0|+|ξ 1|)^(4 : ℝ)*
          ‖(𝓕 (bagCubicSelectedExteriorMellin q N)) ξ‖^2)) ≤ ENNReal.ofReal (C/N^(2*k)) := by
  obtain ⟨C0,hC0,hC0b⟩ := exterior_mass_decay k
  obtain ⟨C1,hC1,hC1b⟩ := exterior_second_mass_decay 0 k
  obtain ⟨C2,hC2,hC2b⟩ := exterior_second_mass_decay 1 k
  have hK : 0<(3 : ℝ)^(4 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨(3 : ℝ)^(4 : ℝ)*(C0+C1+C2),mul_pos hK (add_pos (add_pos hC0 hC1) hC2),?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ),hC0b,hC1b,hC2b] with N hN h0 h1 h2
  intro q
  have hn : 0 ≤ N^(2*k) := pow_nonneg hN.le _
  have hd0 : 0 ≤ C0/N^(2*k) := div_nonneg hC0.le hn
  have hd1 : 0 ≤ C1/N^(2*k) := div_nonneg hC1.le hn
  have hd2 : 0 ≤ C2/N^(2*k) := div_nonneg hC2.le hn
  refine (fourth_energy_bound (bagCubicSelectedExteriorMellin q N)).trans ?_
  refine (mul_le_mul_right (add_le_add (add_le_add (h0 q) (h1 q)) (h2 q)) _).trans_eq ?_
  rw [←ENNReal.ofReal_add hd0 hd1,←ENNReal.ofReal_add (add_nonneg hd0 hd1) hd2,
    ←ENNReal.ofReal_mul hK.le]
  congr 1
  ring

private def fractionalEnergy (s : ℝ) (f : SchwartzMap E ℂ) : ℝ≥0∞ :=
  ∫⁻ ξ : E, ENNReal.ofReal ((1+|ξ 0|+|ξ 1|)^(2+2*s)*‖(𝓕 f) ξ‖^2)

private theorem fractional_energy_le_fourth (s : ℝ) (hs : s ≤ 1) (f : SchwartzMap E ℂ) :
    fractionalEnergy s f ≤ fourthEnergy f := by
  apply lintegral_mono
  intro ξ
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (ξ 0),abs_nonneg (ξ 1)])
    (by linarith)

private theorem fractional_energy_add (s : ℝ) (f g : SchwartzMap E ℂ) :
    fractionalEnergy s (f+g) ≤ 2*(fractionalEnergy s f+fractionalEnergy s g) := by
  have hf := (𝓕 f).continuous.measurable
  have hg := (𝓕 g).continuous.measurable
  have hm : Measurable (fun ξ : E => ENNReal.ofReal
      ((1+|ξ 0|+|ξ 1|)^(2+2*s)*‖(𝓕 f) ξ‖^2)) := by fun_prop
  have he : (∫⁻ ξ : E, (2 : ℝ≥0∞)*(ENNReal.ofReal
      ((1+|ξ 0|+|ξ 1|)^(2+2*s)*‖(𝓕 f) ξ‖^2)+ENNReal.ofReal
      ((1+|ξ 0|+|ξ 1|)^(2+2*s)*‖(𝓕 g) ξ‖^2)))=
        2*(fractionalEnergy s f+fractionalEnergy s g) := by
    rw [lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞)),lintegral_add_left hm]
    rfl
  rw [←he]
  apply lintegral_mono
  intro ξ
  have hw : 0 ≤ (1+|ξ 0|+|ξ 1|)^(2+2*s) := Real.rpow_nonneg (by positivity) _
  have hnorm : ‖(𝓕 f) ξ+(𝓕 g) ξ‖^2 ≤ 2*(‖(𝓕 f) ξ‖^2+‖(𝓕 g) ξ‖^2) := by
    have hb := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le ((𝓕 f) ξ) ((𝓕 g) ξ)) 2
    nlinarith [sq_nonneg (‖(𝓕 f) ξ‖-‖(𝓕 g) ξ‖)]
  change ENNReal.ofReal _ ≤ (2 : ℝ≥0∞)*(ENNReal.ofReal _+ENNReal.ofReal _)
  rw [FourierTransform.fourier_add,add_apply]
  rw [←ENNReal.ofReal_add (mul_nonneg hw (sq_nonneg _)) (mul_nonneg hw (sq_nonneg _))]
  have hp : (1+|ξ 0|+|ξ 1|)^(2+2*s)*‖(𝓕 f) ξ+(𝓕 g) ξ‖^2 ≤
      2*((1+|ξ 0|+|ξ 1|)^(2+2*s)*‖(𝓕 f) ξ‖^2+
        (1+|ξ 0|+|ξ 1|)^(2+2*s)*‖(𝓕 g) ξ‖^2) := by
    nlinarith only [mul_le_mul_of_nonneg_left hnorm hw]
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),ENNReal.ofReal_ofNat]
    using ENNReal.ofReal_le_ofReal hp

/-- Uniform full Mellin H^(1+s) energy of the actual selected normalized BAG
cone for every 0<s<1/2, including the complete physical exterior. -/
theorem bagCubicSelectedMellin_uniform_energy
    (s : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℝ in atTop,
      ∀q : {q : E // ∀i, q i∈Icc (1 : ℝ) 2},
        (∫⁻ ξ : E, ENNReal.ofReal ((1+|ξ 0|+|ξ 1|)^(2+2*s.1)*
          ‖(𝓕 (bagCubicSelectedMellin q N)) ξ‖^2)) ≤ ENNReal.ofReal C := by
  obtain ⟨A,hA,hAb⟩ := bagCubicSelectedNormalizedCone_uniform_local_mellin_energy s
  obtain ⟨B,hB,hBb⟩ := bagCubicSelectedExteriorMellin_energy_decay 0
  refine ⟨2*(A+B),mul_pos (by norm_num) (add_pos hA hB),?_⟩
  filter_upwards [hAb,hBb] with N ha hb
  intro q
  have hext : fractionalEnergy s.1 (bagCubicSelectedExteriorMellin q N) ≤ ENNReal.ofReal B := by
    refine (fractional_energy_le_fourth s.1 (by linarith [s.2.2]) _).trans ?_
    simpa! only [fourthEnergy,Nat.mul_zero,pow_zero,div_one] using hb q
  change fractionalEnergy s.1 (bagCubicSelectedMellin q N) ≤ ENNReal.ofReal (2*(A+B))
  rw [bagCubicSelectedMellin_decomposition]
  refine (fractional_energy_add s.1 _ _).trans ?_
  refine (mul_le_mul_right (add_le_add (ha q) hext) (2 : ℝ≥0∞)).trans_eq ?_
  rw [←ENNReal.ofReal_add hA.le hB.le,ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

end RHTower.BAGTrace
