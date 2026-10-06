import GaloisForLFunctions.RHTower.ChiCubicControlledCutoff
import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicConeMellin
import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicPartialPoisson
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Exact reciprocal Fourier representation of the actual cone profile

A second ordinary Fourier transform of the physical cone restriction has
an exact compact physical-height integral. The original oscillation cancels
algebraically, leaving the full phase `-(p*b + q*a + a*b)/r` and the reciprocal
factor `r^-2`. Every physical window, cutoff, Gaussian/logarithmic slice and
conjugate remains.

One-dimensional inversion proves the fixed-height chirp identity. The
existing inverse Fourier representation of each physical slice supplies a
height-independent marginal majorant from the full three-dimensional
Schwartz Fourier transform. Its integrability and finite height support
justify the complete height/Fourier interchange.

The final theorem uses the explicit controlled physical cutoff family.
It is an exact identity, with no stationary approximation, asymptotic bound,
cancellation premise or RH assumption. Uniform moving-profile regularity
and signed source transfer are subsequent obligations.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open GaloisForLFunctions.RHTower
open scoped Topology FourierTransform
namespace RHTower.BAGTrace

private abbrev Plane := EuclideanSpace ℝ (Fin 2)
private def point (p q : ℝ) : Plane := WithLp.toLp 2 ![p,q]
private def coords : Plane ≃ᵐ ℝ×ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2→ℝ)).symm.trans MeasurableEquiv.finTwoArrow

private theorem coords_preserving : MeasurePreserving coords :=
  (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

private theorem integral_two (f : Plane→ℂ) (hf : Integrable f) :
    Integrable (fun z : ℝ×ℝ => f (point z.1 z.2)) ∧
    (∫ v : Plane, f v)=∫ p : ℝ, ∫ q : ℝ, f (point p q) := by
  have hp := coords_preserving.symm coords
  have hi : Integrable (fun z : ℝ×ℝ => f (coords.symm z)) :=
    (hp.integrable_comp_emb coords.symm.measurableEmbedding).mpr hf
  refine ⟨hi,?_⟩
  rw [← hp.integral_comp' f]
  change (∫ z : ℝ×ℝ, f (coords.symm z) ∂volume.prod volume)=_
  rw [integral_prod _ hi]
  rfl

private def phase (t : ℝ) : ℂ := Complex.exp ((2*Real.pi*t : ℝ)*Complex.I)

private theorem phase_continuous : Continuous phase := by unfold phase; fun_prop

private theorem phase_norm (t : ℝ) : ‖phase t‖=1 := by
  unfold phase
  rw [Complex.norm_exp]
  simp

private theorem phase_add (t u : ℝ) : phase (t+u)=phase t*phase u := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem fourier_phase (f : ℝ→ℂ) (a : ℝ) :
    𝓕 f a=∫ x : ℝ, phase (-a*x)*f x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul]
  congr 1
  unfold phase
  congr 1
  push_cast
  ring

private theorem line_growth (x : ℝ) : (point x).HasTemperateGrowth := by
  have he : point x=fun y : ℝ => point x 0+y • point 0 1 := by
    funext y; ext i; fin_cases i <;> simp [point]
  rw [he]
  fun_prop

private theorem line_lower (x y : ℝ) : ‖y‖≤1+‖point x y‖ := by
  have h := PiLp.norm_apply_le (point x y) 1
  change ‖y‖≤‖point x y‖ at h
  linarith

private def frequencyRow (f : SchwartzMap Plane ℂ) (x : ℝ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLM ℂ (line_growth x) ⟨1,1,by simpa using line_lower x⟩ (𝓕 f)

private def physicalRow (f : Plane→ℂ) (x q : ℝ) : ℂ :=
  ∫ p : ℝ, phase (-p*x)*f (point p q)

private theorem row_fourier (f : SchwartzMap Plane ℂ) (x y : ℝ) :
    𝓕 (physicalRow f x) y=frequencyRow f x y := by
  let K := fun v : Plane => phase (-(v 0*x+v 1*y))*f v
  have hK : Integrable K := f.integrable.bdd_mul (c := 1)
    (phase_continuous.comp (by fun_prop)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun v => le_of_eq (phase_norm _)))
  have htwo := integral_two K hK
  change _=(𝓕 f) (point x y)
  rw [SchwartzMap.fourier_coe]
  conv_rhs => rw [Real.fourier_eq']
  have heq : (fun v : Plane => Complex.exp ((-2*Real.pi*inner ℝ v (point x y) : ℝ)*Complex.I)*f v)=K := by
    funext v
    congr 1
    unfold phase
    simp only [PiLp.inner_apply,Real.inner_apply,Fin.sum_univ_succ,
      Fin.sum_univ_zero,add_zero,point,Matrix.cons_val_zero]
    congr 1
    push_cast
    ring
  change _=∫ v : Plane, Complex.exp ((-2*Real.pi*inner ℝ v (point x y) : ℝ)*Complex.I)*f v
  rw [heq,htwo.2,integral_integral_swap htwo.1,fourier_phase]
  apply integral_congr_ae
  filter_upwards [] with q
  dsimp only [physicalRow]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with p
  change phase (-y*q)*(phase (-p*x)*f (point p q))=
    phase (-(p*x+q*y))*f (point p q)
  rw [← mul_assoc,← phase_add]
  congr 2
  ring

private theorem row_regular (f : SchwartzMap Plane ℂ) (lo hi : ℝ)
    (hs : ∀v : Plane,∀i : Fin 2,v i∉Icc lo hi → f v=0) (x : ℝ) :
    Continuous (physicalRow f x) ∧ HasCompactSupport (physicalRow f x) := by
  have hc : Continuous (fun z : ℝ×ℝ => phase (-z.2*x)*f (point z.2 z.1)) := by
    apply Continuous.mul
    · exact phase_continuous.comp (by fun_prop)
    · apply f.continuous.comp
      exact (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).symm.continuous.comp (by fun_prop)
  have he (q : ℝ) : (∫ p in Icc lo hi,phase (-p*x)*f (point p q))=physicalRow f x q := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    rw [hs _ 0 hp,mul_zero]
  refine ⟨?_,?_⟩
  · have h := continuous_parametric_integral_of_continuous (μ := volume)
      (f := fun q p : ℝ => phase (-p*x)*f (point p q)) hc (s := Icc lo hi) isCompact_Icc
    simpa only [he] using h
  · apply HasCompactSupport.intro (show IsCompact (Icc lo hi) from isCompact_Icc)
    intro q hq
    apply integral_eq_zero_of_ae
    filter_upwards [] with p
    simp only [hs (point p q) 1 hq,mul_zero,Pi.zero_apply]

private theorem row_inversion (f : SchwartzMap Plane ℂ) (lo hi : ℝ)
    (hs : ∀v : Plane,∀i : Fin 2,v i∉Icc lo hi → f v=0) (x t : ℝ) :
    (∫ y : ℝ, phase (t*y)*(𝓕 f) (point x y))=physicalRow f x t := by
  have hr := row_regular f lo hi hs x
  have hI : Integrable (physicalRow f x) := hr.1.integrable_of_hasCompactSupport hr.2
  have hF : 𝓕 (physicalRow f x)=(frequencyRow f x : ℝ→ℂ) := funext (row_fourier f x)
  have h := hr.1.fourierInv_fourier_eq hI (by rw [hF]; exact (frequencyRow f x).integrable)
  have hh := congrFun h t
  rw [Real.fourierInv_eq_fourier_neg] at hh
  rw [fourier_phase,hF] at hh
  simpa only [neg_neg,frequencyRow,SchwartzMap.compCLM_apply,Function.comp_apply] using hh

private theorem chirp_fourier_identity (f : SchwartzMap Plane ℂ) (lo hi : ℝ)
    (hs : ∀v : Plane,∀i : Fin 2,v i∉Icc lo hi → f v=0)
    {r : ℝ} (hr : 0<r) (a b : ℝ) :
    (∫ x : ℝ,∫ y : ℝ,phase (r*x*y-a*x-b*y)*(𝓕 f) (point x y)) =
      (r : ℂ)⁻¹*(∫ q : ℝ,∫ p : ℝ,phase (-(p+a)*(q+b)/r)*f (point p q)) := by
  have hinner (x : ℝ) :
      (∫ y : ℝ,phase (r*x*y-a*x-b*y)*(𝓕 f) (point x y)) =
        phase (-a*x)*physicalRow f x (r*x-b) := by
    calc _ = ∫ y : ℝ,phase (-a*x)*(phase ((r*x-b)*y)*(𝓕 f) (point x y)) := by
           apply integral_congr_ae
           filter_upwards [] with y
           rw [show r*x*y-a*x-b*y=(-a*x)+(r*x-b)*y by ring,phase_add,mul_assoc]
         _ = _ := by rw [integral_const_mul,row_inversion f lo hi hs]
  simp_rw [hinner]
  let H := fun x : ℝ => phase (-a*x)*physicalRow f x (r*x-b)
  have hsub : (∫ q : ℝ,H ((q+b)/r))=(r : ℂ)*(∫ x : ℝ,H x) := by
    calc _ = ∫ q : ℝ,(fun z => H (r⁻¹*z)) (q+b) := by
           apply integral_congr_ae
           filter_upwards [] with q
           congr 1
           ring
         _ = ∫ q : ℝ,H (r⁻¹*q) := integral_add_right_eq_self (fun z : ℝ => H (r⁻¹*z)) b
         _ = _ := by
           rw [Measure.integral_comp_mul_left]
           simp only [inv_inv,abs_of_pos hr,Complex.real_smul]
  change (∫ x : ℝ,H x)=_
  calc (∫ x : ℝ,H x)=(r : ℂ)⁻¹*(∫ q : ℝ,H ((q+b)/r)) := by
         rw [hsub,← mul_assoc,inv_mul_cancel₀ (by exact_mod_cast hr.ne'),one_mul]
       _ = _ := by
         congr 1
         apply integral_congr_ae
         filter_upwards [] with q
         have hq : r*((q+b)/r)-b=q := by field_simp; ring
         dsimp only [H]
         rw [hq]
         dsimp only [physicalRow]
         rw [← integral_const_mul]
         apply integral_congr_ae
         filter_upwards [] with p
         rw [← mul_assoc,← phase_add]
         congr 2
         ring

private def physicalPoint (p q r : ℝ) : BAGPhysicalSpace := WithLp.toLp 2 ![p,q,r]

private def tripleCoords : BAGPhysicalSpace ≃ᵐ ℝ×ℝ×ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 3→ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).trans
      ((MeasurableEquiv.refl ℝ).prodCongr
        (MeasurableEquiv.finTwoArrow.trans (MeasurableEquiv.prodComm : ℝ×ℝ ≃ᵐ ℝ×ℝ))))

private theorem tripleCoords_symm (z : ℝ×ℝ×ℝ) :
    tripleCoords.symm z=physicalPoint z.2.2 z.2.1 z.1 := by
  apply tripleCoords.injective
  rw [tripleCoords.apply_symm_apply]
  rfl

private theorem tripleCoords_preserving : MeasurePreserving tripleCoords :=
  (((MeasurePreserving.id (volume : Measure ℝ)).prod
    (Measure.measurePreserving_swap.comp (volume_preserving_finTwoArrow ℝ))).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2)).comp
        (PiLp.volume_preserving_ofLp (Fin 3))

private def frequencyMajorant (f : SchwartzMap BAGPhysicalSpace ℂ) (z : ℝ×ℝ) : ℝ :=
  ∫ t : ℝ, ‖(𝓕 f) (physicalPoint z.1 z.2 t)‖

private theorem frequencyMajorant_integrable (f : SchwartzMap BAGPhysicalSpace ℂ) :
    Integrable (frequencyMajorant f) := by
  let F : SchwartzMap BAGPhysicalSpace ℂ := 𝓕 f
  have hp := tripleCoords_preserving.symm tripleCoords
  have hwhole : Integrable (fun v : BAGPhysicalSpace => ‖F v‖) := F.integrable.norm
  have hi := (hp.integrable_comp_emb tripleCoords.symm.measurableEmbedding).mpr hwhole
  refine hi.integral_prod_right.swap.congr (Filter.Eventually.of_forall (fun z => ?_))
  change (∫ t : ℝ, ‖F (tripleCoords.symm (t,z.2,z.1))‖)=frequencyMajorant f z
  simp only [tripleCoords_symm]
  rfl


private theorem physical_slice_norm_le (f : SchwartzMap BAGPhysicalSpace ℂ) (lo hi : ℝ)
    (hs : ∀v : BAGPhysicalSpace,∀i : Fin 3,v i∉Icc lo hi → f v=0) (x y r : ℝ) :
    ‖bagThirdPhysicalSlice f x y r‖≤frequencyMajorant f (x,y) := by
  have he := congrFun (bagThirdPhysicalSlice_eq_inverse f lo hi hs x y) r
  rw [he,SchwartzMap.fourierInv_coe,Real.fourierInv_eq']
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [norm_smul,Complex.norm_exp_ofReal_mul_I,one_mul]
  congr 1

private theorem cone_height_identity (f : SchwartzMap BAGPhysicalSpace ℂ) (lo hi : ℝ)
    (hs : ∀v : BAGPhysicalSpace,∀i : Fin 3,v i∉Icc lo hi → f v=0) (x y : ℝ) :
    bagCubicConeSchwartz f (point x y)=
      ∫ r : ℝ,phase (r*x*y)*bagThirdPhysicalSlice f x y r := by
  have hp := bagThirdPhysicalSlice_eq_inverse f lo hi hs x y
  have hfreq : 𝓕 (bagThirdPhysicalSlice f x y)=
      (bagThirdFrequencySchwartz f x y : ℝ→ℂ) := by
    rw [hp,← SchwartzMap.fourier_coe]
    simp only [FourierTransform.fourier_fourierInv_eq]
  have h := congrFun hfreq (-x*y)
  rw [fourier_phase] at h
  have hh : bagThirdFrequencySchwartz f x y (-x*y)=bagCubicConeSchwartz f (point x y) := by
    simp only [bagThirdFrequencySchwartz,SchwartzMap.compCLM_apply,Function.comp_apply,
      bagCubicConeSchwartz_apply]
    rfl
  rw [hh] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with r
  congr 2
  ring

private theorem physical_slice_continuous (f : SchwartzMap BAGPhysicalSpace ℂ) (lo hi : ℝ)
    (hs : ∀v : BAGPhysicalSpace,∀i : Fin 3,v i∉Icc lo hi → f v=0) :
    Continuous (fun z : ℝ×ℝ×ℝ => bagThirdPhysicalSlice f z.2.1 z.2.2 z.1) := by
  let K := fun (z : ℝ×ℝ×ℝ) (q p : ℝ) =>
    Complex.exp ((-2*Real.pi*(p*z.2.1+q*z.2.2) : ℝ)*Complex.I)*
      f (physicalPoint p q z.1)
  have hc : Continuous (fun w : ((ℝ×ℝ×ℝ)×ℝ)×ℝ => K w.1.1 w.1.2 w.2) := by
    dsimp only [K]
    apply Continuous.mul
    · fun_prop
    · apply f.continuous.comp
      exact (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).symm.continuous.comp (by fun_prop)
  have hp (z : ℝ×ℝ×ℝ) (q : ℝ) :
      (∫ p in Icc lo hi,K z q p)=∫ p : ℝ,K z q p := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    dsimp only [K]
    rw [hs _ 0 hp,mul_zero]
  have hq (z : ℝ×ℝ×ℝ) (q : ℝ) (hq : q∉Icc lo hi) :
      (∫ p in Icc lo hi,K z q p)=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [] with p
    dsimp only [K]
    simp only [hs (physicalPoint p q z.1) 1 hq,mul_zero,Pi.zero_apply]
  have he (z : ℝ×ℝ×ℝ) : (∫ q in Icc lo hi,∫ p in Icc lo hi,K z q p)=
      bagThirdPhysicalSlice f z.2.1 z.2.2 z.1 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hq z)]
    change (∫ q : ℝ,∫ p in Icc lo hi,K z q p)=(∫ q : ℝ,∫ p : ℝ,K z q p)
    simp_rw [hp]
  have hinner := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun w : (ℝ×ℝ×ℝ)×ℝ => fun p : ℝ => K w.1 w.2 p)
    hc (s := Icc lo hi) isCompact_Icc
  have houter := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun z q => ∫ p in Icc lo hi,K z q p) hinner (s := Icc lo hi) isCompact_Icc
  simpa only [he] using houter

private theorem physical_slices_integrable (f : SchwartzMap BAGPhysicalSpace ℂ) (lo hi : ℝ)
    (hs : ∀v : BAGPhysicalSpace,∀i : Fin 3,v i∉Icc lo hi → f v=0) :
    Integrable (fun z : ℝ×ℝ×ℝ => bagThirdPhysicalSlice f z.2.1 z.2.2 z.1) := by
  have hband : Integrable ((Icc lo hi).indicator (fun _ : ℝ => (1 : ℝ))) :=
    (integrableOn_const (show volume (Icc lo hi)≠⊤ from isCompact_Icc.measure_lt_top.ne)).integrable_indicator
      measurableSet_Icc
  have hb := hband.mul_prod (frequencyMajorant_integrable f)
  apply hb.mono' (physical_slice_continuous f lo hi hs).aestronglyMeasurable
  filter_upwards [] with z
  by_cases hz : z.1∈Icc lo hi
  · rw [Set.indicator_of_mem hz,one_mul]
    exact physical_slice_norm_le f lo hi hs z.2.1 z.2.2 z.1
  · rw [Set.indicator_of_notMem hz,zero_mul,
      bagThirdPhysicalSlice_zero f lo hi hs z.2.1 z.2.2 z.1 hz,norm_zero]

private theorem chirped_slices_integrable (f : SchwartzMap BAGPhysicalSpace ℂ) (lo hi : ℝ)
    (hs : ∀v : BAGPhysicalSpace,∀i : Fin 3,v i∉Icc lo hi → f v=0) (a b : ℝ) :
    Integrable (fun z : ℝ×ℝ×ℝ =>
      phase (z.1*z.2.1*z.2.2-a*z.2.1-b*z.2.2)*bagThirdPhysicalSlice f z.2.1 z.2.2 z.1) := by
  exact (physical_slices_integrable f lo hi hs).bdd_mul (c := 1)
    (phase_continuous.comp (by fun_prop)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => le_of_eq (phase_norm _)))

private def planeNode (r : ℝ) (v : Plane) : BAGPhysicalSpace :=
  physicalPoint (v 0) (v 1) r

private theorem planeNode_growth (r : ℝ) : (planeNode r).HasTemperateGrowth := by
  let e (i : Fin 3) : BAGPhysicalSpace := WithLp.toLp 2 (Pi.single i 1)
  have hg (i : Fin 2) : (fun v : Plane => v i).HasTemperateGrowth :=
    (EuclideanSpace.proj i).hasTemperateGrowth
  have he : planeNode r=fun v : Plane => v 0 • e 0+v 1 • e 1+r • e 2 := by
    funext v
    ext i
    fin_cases i <;> simp [planeNode,physicalPoint,e]
  rw [he]
  exact (((hg 0).smul (Function.HasTemperateGrowth.const (e 0))).add
    ((hg 1).smul (Function.HasTemperateGrowth.const (e 1)))).add
      (Function.HasTemperateGrowth.const (r • e 2))

private theorem planeNode_lower (r : ℝ) (v : Plane) : ‖v‖≤1+‖planeNode r v‖ := by
  have hv := EuclideanSpace.norm_sq_eq v
  have he : ‖planeNode r v‖^2=v 0^2+v 1^2+r^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [planeNode,physicalPoint,Fin.sum_univ_succ]
    ring
  simp [Fin.sum_univ_succ] at hv
  nlinarith [norm_nonneg v,norm_nonneg (planeNode r v),sq_nonneg r]

private def planeSlice (f : SchwartzMap BAGPhysicalSpace ℂ) (r : ℝ) : SchwartzMap Plane ℂ :=
  SchwartzMap.compCLM ℂ (planeNode_growth r) ⟨1,1,by simpa using planeNode_lower r⟩ f

private theorem planeSlice_apply (f : SchwartzMap BAGPhysicalSpace ℂ) (r : ℝ) (v : Plane) :
    planeSlice f r v=f (planeNode r v) := rfl

private theorem planeSlice_box (f : SchwartzMap BAGPhysicalSpace ℂ) (lo hi : ℝ)
    (hs : ∀v : BAGPhysicalSpace,∀i : Fin 3,v i∉Icc lo hi → f v=0) (r : ℝ) :
    ∀v : Plane,∀i : Fin 2,v i∉Icc lo hi → planeSlice f r v=0 := by
  intro v i hv
  rw [planeSlice_apply]
  fin_cases i
  · exact hs _ 0 hv
  · exact hs _ 1 hv

private theorem planeSlice_fourier (f : SchwartzMap BAGPhysicalSpace ℂ) (r x y : ℝ) :
    (𝓕 (planeSlice f r)) (point x y)=bagThirdPhysicalSlice f x y r := by
  let K := fun v : Plane => phase (-(v 0*x+v 1*y))*planeSlice f r v
  have hK : Integrable K := (planeSlice f r).integrable.bdd_mul (c := 1)
    (phase_continuous.comp (by fun_prop)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun _ => le_of_eq (phase_norm _)))
  have htwo := integral_two K hK
  rw [SchwartzMap.fourier_coe,Real.fourier_eq']
  have heq : (fun v : Plane => Complex.exp ((-2*Real.pi*inner ℝ v (point x y) : ℝ)*Complex.I)*
      planeSlice f r v)=K := by
    funext v
    congr 1
    unfold phase
    simp only [PiLp.inner_apply,Real.inner_apply,Fin.sum_univ_succ,
      Fin.sum_univ_zero,add_zero,point,Matrix.cons_val_zero]
    congr 1
    push_cast
    ring
  change (∫ v : Plane,Complex.exp ((-2*Real.pi*inner ℝ v (point x y) : ℝ)*Complex.I)*
    planeSlice f r v)=_
  rw [heq,htwo.2,integral_integral_swap htwo.1]
  apply integral_congr_ae
  filter_upwards [] with q
  apply integral_congr_ae
  filter_upwards [] with p
  change phase (-(p*x+q*y))*planeSlice f r (point p q)=_
  rw [planeSlice_apply]
  dsimp only [bagThirdPhysicalSlice,planeNode,physicalPoint,point]
  congr 1
  unfold phase
  congr 1
  push_cast
  ring

private theorem fourier_plane (g : SchwartzMap Plane ℂ) (a b : ℝ) :
    (𝓕 g) (point a b)=∫ x : ℝ,∫ y : ℝ,phase (-(x*a+y*b))*g (point x y) := by
  let K := fun v : Plane => phase (-(v 0*a+v 1*b))*g v
  have hK : Integrable K := g.integrable.bdd_mul (c := 1)
    (phase_continuous.comp (by fun_prop)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun _ => le_of_eq (phase_norm _)))
  have htwo := integral_two K hK
  rw [SchwartzMap.fourier_coe,Real.fourier_eq']
  have heq : (fun v : Plane => Complex.exp ((-2*Real.pi*inner ℝ v (point a b) : ℝ)*Complex.I)*g v)=K := by
    funext v
    congr 1
    unfold phase
    simp only [PiLp.inner_apply,Real.inner_apply,Fin.sum_univ_succ,
      Fin.sum_univ_zero,add_zero,point,Matrix.cons_val_zero]
    congr 1
    push_cast
    ring
  change (∫ v : Plane,Complex.exp ((-2*Real.pi*inner ℝ v (point a b) : ℝ)*Complex.I)*g v)=_
  rw [heq,htwo.2]
  rfl

private theorem cone_reciprocal_fourier (f : SchwartzMap BAGPhysicalSpace ℂ) (lo hi : ℝ)
    (hlo : 0<lo) (hs : ∀v : BAGPhysicalSpace,∀i : Fin 3,v i∉Icc lo hi → f v=0)
    (a b : ℝ) :
    (𝓕 (bagCubicConeSchwartz f)) (point a b)=
      ∫ r : ℝ,(r : ℂ)⁻¹*(∫ q : ℝ,∫ p : ℝ,
        phase (-(p+a)*(q+b)/r)*f (physicalPoint p q r)) := by
  let K := fun z : ℝ×ℝ×ℝ =>
    phase (z.1*z.2.1*z.2.2-a*z.2.1-b*z.2.2)*bagThirdPhysicalSlice f z.2.1 z.2.2 z.1
  have hK : Integrable K := chirped_slices_integrable f lo hi hs a b
  have he (x y : ℝ) : phase (-(x*a+y*b))*bagCubicConeSchwartz f (point x y)=
      ∫ r : ℝ,K (r,x,y) := by
    rw [cone_height_identity f lo hi hs,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with r
    dsimp only [K]
    rw [← mul_assoc,← phase_add]
    congr 2
    ring
  rw [fourier_plane]
  simp_rw [he]
  have hKr := hK.integral_prod_right
  calc (∫ x : ℝ,∫ y : ℝ,∫ r : ℝ,K (r,x,y))
      = ∫ z : ℝ×ℝ,∫ r : ℝ,K (r,z) := by
        exact (integral_prod _ hKr).symm
    _ = ∫ r : ℝ,∫ z : ℝ×ℝ,K (r,z) := (integral_integral_swap hK).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hK.prod_right_ae] with r hr
      change (∫ z : ℝ×ℝ,K (r,z) ∂volume.prod volume)=_
      rw [integral_prod _ hr]
      by_cases hband : r∈Icc lo hi
      · have hpos : 0<r := hlo.trans_le hband.1
        have hh := chirp_fourier_identity (planeSlice f r) lo hi
          (planeSlice_box f lo hi hs r) hpos a b
        have hval (x y : ℝ) : K (r,x,y)=
            phase (r*x*y-a*x-b*y)*(𝓕 (planeSlice f r)) (point x y) := by
          rw [planeSlice_fourier]
        simp_rw [hval]
        simpa only [planeSlice_apply,planeNode,point,physicalPoint,Matrix.cons_val_zero,
          Matrix.cons_val_one] using hh
      · have hz (p q : ℝ) : f (physicalPoint p q r)=0 := hs _ 2 hband
        simp only [K,bagThirdPhysicalSlice_zero f lo hi hs _ _ r hband,hz,
          mul_zero,integral_zero]

/-- The actual physical Schwartz amplitude with the selected controlled cutoff. -/
def bagCubicControlledPhysicalSchwartz (N : {r : ℝ // 1<r})
    (H : {r : ℝ // r∈Ioo (0 : ℝ) (N.1/2)}) : SchwartzMap BAGPhysicalSpace ℂ :=
  let hp := bagCubicControlledBandCutoff_properties
    ⟨N.1,lt_trans zero_lt_one N.2⟩ H
  bagCubicPhysicalSchwartz N.2 hp.1 hp.2.2.2.1

private theorem controlled_amplitude_apply (N : {r : ℝ // 1<r})
    (H : {r : ℝ // r∈Ioo (0 : ℝ) (N.1/2)}) (v : BAGPhysicalSpace) :
    bagCubicControlledPhysicalSchwartz N H v=
      bagCubicPhysicalAmplitude N.1 (bagCubicControlledBandCutoff N.1 H.1) v := rfl

private theorem controlled_amplitude_box (N : {r : ℝ // 1<r})
    (H : {r : ℝ // r∈Ioo (0 : ℝ) (N.1/2)}) :
    ∀v : BAGPhysicalSpace,∀i : Fin 3,v i∉Icc N.1 (2*N.1) →
      bagCubicControlledPhysicalSchwartz N H v=0 := by
  have hp := bagCubicControlledBandCutoff_properties
    ⟨N.1,lt_trans zero_lt_one N.2⟩ H
  intro v i hv
  have hz : bagCubicControlledBandCutoff N.1 H.1 (v i)=0 :=
    hp.2.2.2.1 _ (fun h => hv ⟨h.1.le,h.2.le⟩)
  have hslice : bagCubicMellinSliceValue N.1 (bagCubicControlledBandCutoff N.1 H.1) 0 (v i)=0 := by
    simp only [bagCubicMellinSliceValue,hz,Complex.ofReal_zero,zero_mul,zero_div]
  rw [controlled_amplitude_apply]
  fin_cases i
  · change bagCubicMellinSliceValue N.1 (bagCubicControlledBandCutoff N.1 H.1) 0 (v 0)=0 at hslice
    simp only [bagCubicPhysicalAmplitude,hslice,mul_zero,zero_mul,zero_div]
  · change bagCubicMellinSliceValue N.1 (bagCubicControlledBandCutoff N.1 H.1) 0 (v 1)=0 at hslice
    simp only [bagCubicPhysicalAmplitude,hslice,mul_zero,zero_mul,zero_div]
  · change bagCubicMellinSliceValue N.1 (bagCubicControlledBandCutoff N.1 H.1) 0 (v 2)=0 at hslice
    simp only [bagCubicPhysicalAmplitude,hslice,map_zero,mul_zero,zero_mul,zero_div]


private theorem oscillation_phase (t : ℝ) : bourgainOscillation (2*Real.pi*t)=phase t := by
  unfold bourgainOscillation phase
  rw [mul_comm]

/-- Exact ordinary Fourier transform of the actual cone profile. The full height
window, all three physical amplitudes, and the reciprocal phase remain. -/
theorem bagCubicControlledCone_fourier_eq_reciprocal (N : {r : ℝ // 1<r})
    (H : {r : ℝ // r∈Ioo (0 : ℝ) (N.1/2)}) (a b : ℝ) :
    (𝓕 (bagCubicConeSchwartz (bagCubicControlledPhysicalSchwartz N H)))
        (WithLp.toLp 2 ![a,b]) =
      let η := bagCubicControlledBandCutoff N.1 H.1
      ∫ r : ℝ,∫ q : ℝ,∫ p : ℝ,
        (2*Real.pi : ℂ)*bagCubicMellinSliceValue N.1 η 0 p*
          bagCubicMellinSliceValue N.1 η 0 q*
          (starRingEnd ℂ) (bagCubicMellinSliceValue N.1 η 0 r)/(r : ℂ)^2*
          (bagPhysicalHeightWindow (p*q/(r*N.1)) : ℂ)*
          bourgainOscillation (-2*Real.pi*((p*b+q*a+a*b)/r)) := by
  let η := bagCubicControlledBandCutoff N.1 H.1
  have hc := cone_reciprocal_fourier (bagCubicControlledPhysicalSchwartz N H)
    N.1 (2*N.1) (lt_trans zero_lt_one N.2) (controlled_amplitude_box N H) a b
  change (𝓕 (bagCubicConeSchwartz (bagCubicControlledPhysicalSchwartz N H))) (point a b)=_
  rw [hc]
  dsimp only
  apply integral_congr_ae
  filter_upwards [] with r
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with q
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [controlled_amplitude_apply]
  change (r : ℂ)⁻¹*(phase (-(p+a)*(q+b)/r)*
    ((2*Real.pi : ℂ)*bagCubicMellinSliceValue N.1 η 0 p*
      bagCubicMellinSliceValue N.1 η 0 q*
      (starRingEnd ℂ) (bagCubicMellinSliceValue N.1 η 0 r)/(r : ℂ)*
      (bagPhysicalHeightWindow (p*q/(r*N.1)) : ℂ)*
      bourgainOscillation (2*Real.pi*(p*q/r))))=_
  rw [oscillation_phase]
  have hphase : phase (-(p+a)*(q+b)/r)*phase (p*q/r)=
      bourgainOscillation (-2*Real.pi*((p*b+q*a+a*b)/r)) := by
    rw [← phase_add]
    rw [show -2*Real.pi*((p*b+q*a+a*b)/r)=2*Real.pi*(-((p*b+q*a+a*b)/r)) by ring,
      oscillation_phase]
    congr 1
    ring
  rw [← hphase]
  simp only [div_eq_mul_inv]
  ring

end RHTower.BAGTrace
