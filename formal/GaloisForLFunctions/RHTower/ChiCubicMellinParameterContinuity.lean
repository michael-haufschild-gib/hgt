import GaloisForLFunctions.RHTower.ChiCubicMellinTrace
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Fixed-input continuity of the actual localized Mellin profiles

For each physical Schwartz input, the literal weighted logarithmic profile
is jointly smooth in the Mellin parameter and log position. The actual
physical cutoff puts every such profile in one compact logarithmic box.
All pure log jets retain this support.

On the compact parameter square, joint continuity gives integrable domination
for the squared jet differences. Dominated convergence proves L² continuity
of each jet. Exact Fourier differentiation and Plancherel bound the complete
H² energy by the mass and two pure second-derivative masses. Every lower
weighted Fourier energy consequently tends to zero as the parameter moves.
No continuity or uniform Schwartz budget is imposed as an analytic premise.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter LineDeriv HTGeometry
open scoped FourierTransform Topology ENNReal ContDiff
namespace RHTower.BAGTrace
private abbrev E := HTGeometry.QuadrantLogSpace
private abbrev Q := {q : E // ∀i, q i∈Icc (1 : ℝ) 2}

private def logBox : Set E := {u | ∀i, u i∈Icc (-Real.log 8) (Real.log 8)}

private theorem compact_logBox : IsCompact logBox := by
  have hh := (isCompact_univ_pi (fun _ : Fin 2 =>
    isCompact_Icc (a := -Real.log 8) (b := Real.log 8))).image
      (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ))
  convert hh using 1
  ext x
  constructor
  · intro hx
    refine ⟨WithLp.ofLp x,?_,?_⟩
    · exact fun i _ => hx i
    · exact WithLp.toLp_ofLp 2 x
  · rintro ⟨y,hy,rfl⟩
    exact fun i => hy i (mem_univ i)


private theorem logNode_cutoff_support (u : E)
    (hu : GaloisForLFunctions.HTGeometry.mellinLocalizationCutoff (HTGeometry.quadrantLogNode u) ≠ 0) :
    u∈logBox := by
  have hs := GaloisForLFunctions.HTGeometry.mellinLocalizationCutoff_spec.2.2.1
    (HTGeometry.quadrantLogNode u) (subset_tsupport _ hu)
  intro i
  have hi := hs i
  rw [HTGeometry.quadrantLogNode_apply] at hi
  have hlo := Real.log_le_log (by norm_num : (0 : ℝ)<1/8) hi.1.le
  have hhi := Real.log_le_log (Real.exp_pos _) hi.2.le
  simp only [one_div,Real.log_inv,Real.log_exp] at hlo hhi
  constructor <;> linarith


private def jointProfile (f : SchwartzMap E ℂ) (z : E×E) : ℂ :=
  ((Real.exp (-z.1 0*z.2 0-z.1 1*z.2 1) : ℝ) : ℂ)*
    (GaloisForLFunctions.HTGeometry.mellinLocalizationCutoff (HTGeometry.quadrantLogNode z.2) : ℂ)*
      f (HTGeometry.quadrantLogNode z.2)
private theorem jointProfile_smooth (f : SchwartzMap E ℂ) :
    ContDiff ℝ ∞ (jointProfile f) := by
  have hn : ContDiff ℝ ∞ HTGeometry.quadrantLogNode := by
    unfold HTGeometry.quadrantLogNode
    fun_prop
  have hc := GaloisForLFunctions.HTGeometry.mellinLocalizationCutoff_spec.1
  have hf := f.smooth ⊤
  have he : ContDiff ℝ ∞ (fun z : E×E => Real.exp (-z.1 0*z.2 0-z.1 1*z.2 1)) := by fun_prop
  have hnode : ContDiff ℝ ∞ (fun z : E×E => HTGeometry.quadrantLogNode z.2) := hn.comp contDiff_snd
  exact ((Complex.ofRealCLM.contDiff.comp he).mul
    (Complex.ofRealCLM.contDiff.comp (hc.comp hnode))).mul (hf.comp hnode)

private theorem jointProfile_support (f : SchwartzMap E ℂ) :
    tsupport (jointProfile f)⊆univ×ˢlogBox := by
  apply closure_minimal _ (isClosed_univ.prod compact_logBox.isClosed)
  intro z hz
  refine ⟨mem_univ _,logNode_cutoff_support z.2 ?_⟩
  intro hzero
  apply hz
  simp only [jointProfile,hzero,Complex.ofReal_zero,mul_zero,zero_mul]

private def jointJet (f : SchwartzMap E ℂ) (i : Fin 2) : ℕ→(E×E→ℂ)
  | 0 => jointProfile f
  | n+1 => fun z => fderiv ℝ (jointJet f i n) z (0,HTGeometry.quadrantLogBasis i)
private theorem jointJet_smooth (f : SchwartzMap E ℂ) (i : Fin 2) (j : ℕ) :
    ContDiff ℝ ∞ (jointJet f i j) := by
  induction j with
  | zero => exact jointProfile_smooth f
  | succ j ih => exact (ih.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
private theorem jointJet_support (f : SchwartzMap E ℂ) (i : Fin 2) (j : ℕ) :
    tsupport (jointJet f i j)⊆univ×ˢlogBox := by
  induction j with
  | zero => exact jointProfile_support f
  | succ j ih => exact (tsupport_fderiv_apply_subset ℝ (0,HTGeometry.quadrantLogBasis i)).trans ih

private def parameterBox : Set E := {q | ∀i, q i∈Icc (1 : ℝ) 2}
private theorem compact_parameterBox : IsCompact parameterBox := by
  have hh := (isCompact_univ_pi (fun _ : Fin 2 => isCompact_Icc (a := (1 : ℝ)) (b := 2))).image
    (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ))
  convert hh using 1
  ext x
  constructor
  · intro hx
    exact ⟨WithLp.ofLp x,fun i _ => hx i,WithLp.toLp_ofLp 2 x⟩
  · rintro ⟨y,hy,rfl⟩
    exact fun i => hy i (mem_univ i)

private theorem compact_parameter_L2_tendsto (F : E×E→ℂ) (hF : Continuous F)
    (hSupp : tsupport F⊆univ×ˢlogBox) (q0 : Q) :
    Tendsto (fun q : Q => ∫u : E,‖F (q.1,u)-F (q0.1,u)‖^2) (𝓝 q0) (𝓝 0) := by
  obtain ⟨C,hC⟩ := (compact_parameterBox.prod compact_logBox).exists_bound_of_continuousOn hF.continuousOn
  let B : ℝ := (2*(|C|+1))^2
  have hzero (q : E) (u : E) (hu : u∉logBox) : F (q,u)=0 := by
    by_contra hn
    exact hu (hSupp (subset_tsupport F hn)).2
  have hbound (q : Q) (u : E) : ‖‖F (q.1,u)-F (q0.1,u)‖^2‖ ≤ logBox.indicator (fun _ => B) u := by
    by_cases hu : u∈logBox
    · rw [indicator_of_mem hu,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have h1 := hC (q.1,u) ⟨q.2,hu⟩
      have h0 := hC (q0.1,u) ⟨q0.2,hu⟩
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      have hh := norm_sub_le (F (q.1,u)) (F (q0.1,u))
      linarith [le_abs_self C]
    · rw [indicator_of_notMem hu,hzero q.1 u hu,hzero q0.1 u hu]
      simp
  haveI : IsFiniteMeasure (volume.restrict logBox) := isFiniteMeasure_restrict.mpr compact_logBox.measure_ne_top
  have hBi : Integrable (logBox.indicator (fun _ : E => B)) := by
    apply (integrable_indicator_iff compact_logBox.measurableSet).2
    exact integrable_const B
  have hc (q : Q) : Continuous (fun u : E => ‖F (q.1,u)-F (q0.1,u)‖^2) := by fun_prop
  have ht (u : E) : Tendsto (fun q : Q => ‖F (q.1,u)-F (q0.1,u)‖^2) (𝓝 q0) (𝓝 0) := by
    have hp : Continuous (fun q : Q => F (q.1,u)) := by fun_prop
    simpa using ((hp.tendsto q0).sub (tendsto_const_nhds (x := F (q0.1,u)))).norm.pow 2
  have hh := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure E)) (f := fun _ => (0 : ℝ))
    (logBox.indicator (fun _ : E => B))
    (Eventually.of_forall (fun q => (hc q).aestronglyMeasurable))
    (Eventually.of_forall (fun q => Eventually.of_forall (hbound q))) hBi
    (Eventually.of_forall ht)
  simpa only [integral_zero] using hh

private def axisJet (v : E) : ℕ→SchwartzMap E ℂ→SchwartzMap E ℂ
  | 0,f => f
  | n+1,f => ∂_{v} (axisJet v n f)
private theorem slice_derivative (F : E×E→ℂ) (hF : ContDiff ℝ ∞ F) (q u v : E) :
    fderiv ℝ (fun t : E => F (q,t)) u v=fderiv ℝ F (q,u) (0,v) := by
  have hh := (hF.differentiable (by simp) (q,u)).hasFDerivAt.comp u
    ((hasFDerivAt_const q u).prodMk (hasFDerivAt_id u))
  change (fderiv ℝ (F ∘ Prod.mk q) u) v=_
  rw [hh.fderiv]
  simp
private theorem actual_jointJet (f : SchwartzMap E ℂ) (q : Q) (i : Fin 2) (j : ℕ) (u : E) :
    axisJet (HTGeometry.quadrantLogBasis i) j
      (GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q f) u=jointJet f i j (q.1,u) := by
  induction j generalizing u with
  | zero =>
    change GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q f u=jointProfile f (q.1,u)
    rw [GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz_apply,
      GaloisForLFunctions.HTGeometry.compactLocalizedMellinProfile_eq]
    rfl
  | succ j ih =>
    change fderiv ℝ (axisJet (HTGeometry.quadrantLogBasis i) j
      (GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q f)) u (HTGeometry.quadrantLogBasis i)=_
    have he : (axisJet (HTGeometry.quadrantLogBasis i) j
      (GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q f) : E→ℂ)=
        fun t => jointJet f i j (q.1,t) := funext ih
    rw [he]
    exact slice_derivative _ (jointJet_smooth f i j) _ _ _

private theorem actual_jet_L2_continuity (f : SchwartzMap E ℂ) (q0 : Q) (i : Fin 2) (j : ℕ) :
    Tendsto (fun q : Q => ∫u : E,
      ‖axisJet (HTGeometry.quadrantLogBasis i) j
        (GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q f) u-
       axisJet (HTGeometry.quadrantLogBasis i) j
        (GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q0 f) u‖^2)
      (𝓝 q0) (𝓝 0) := by
  simp only [actual_jointJet]
  exact compact_parameter_L2_tendsto _ (jointJet_smooth f i j).continuous (jointJet_support f i j) q0

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

private theorem axisJet_sub (v : E) (j : ℕ) (f g : SchwartzMap E ℂ) :
    axisJet v j (f-g)=axisJet v j f-axisJet v j g := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (∂_{v} (axisJet v j (f-g)) : SchwartzMap E ℂ)=_
    rw [ih]
    exact map_sub (lineDerivOpCLM ℂ (SchwartzMap E ℂ) v) _ _

/-- For every fixed physical Schwartz input, the literal localized Mellin
profile varies continuously in every Fourier Sobolev energy through order two.
Common compact log support and the actual jointly smooth profile supply all
jet domination; no parameter-continuity or uniform seminorm premise is used. -/
theorem bagLocalizedMellin_parameter_energy_tendsto
    (f : SchwartzMap E ℂ) (q0 : Q) (s : {r : ℝ // r∈Icc (0 : ℝ) 2}) :
    Tendsto (fun q : Q => ∫⁻ξ : E,ENNReal.ofReal ((1+|ξ 0|+|ξ 1|)^(2*s.1)*
      ‖(𝓕 (GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q f-
        GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q0 f)) ξ‖^2))
      (𝓝 q0) (𝓝 0) := by
  let h := fun q : Q => GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q f-
    GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q0 f
  let A := fun q : Q => ∫u : E,‖h q u‖^2
  let B := fun q : Q => ∫u : E,‖axisJet (quadrantLogBasis 0) 2 (h q) u‖^2
  let C := fun q : Q => ∫u : E,‖axisJet (quadrantLogBasis 1) 2 (h q) u‖^2
  have hA : Tendsto A (𝓝 q0) (𝓝 0) := by
    simpa only [A,h,axisJet,sub_apply] using actual_jet_L2_continuity f q0 0 0
  have hB : Tendsto B (𝓝 q0) (𝓝 0) := by
    simpa only [B,h,axisJet_sub,sub_apply] using actual_jet_L2_continuity f q0 0 2
  have hC : Tendsto C (𝓝 q0) (𝓝 0) := by
    simpa only [C,h,axisJet_sub,sub_apply] using actual_jet_L2_continuity f q0 1 2
  have hj : Tendsto (fun q : Q => ENNReal.ofReal ((3 : ℝ)^(4 : ℝ)*(A q+B q+C q)))
      (𝓝 q0) (𝓝 0) := by
    have hh : Tendsto (fun q : Q => (3 : ℝ)^(4 : ℝ)*(A q+B q+C q)) (𝓝 q0) (𝓝 (0 : ℝ)) := by
      simpa only [add_zero,mul_zero] using (((hA.add hB).add hC).const_mul ((3 : ℝ)^(4 : ℝ)))
    have hf := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hh
    convert! hf using 1
    simp only [ENNReal.ofReal_zero]

  have hb (q : Q) : (∫⁻ξ : E,ENNReal.ofReal ((1+|ξ 0|+|ξ 1|)^(2*s.1)*‖(𝓕 (h q)) ξ‖^2)) ≤
      ENNReal.ofReal ((3 : ℝ)^(4 : ℝ)*(A q+B q+C q)) := by
    have hs : (∫⁻ξ : E,ENNReal.ofReal ((1+|ξ 0|+|ξ 1|)^(2*s.1)*‖(𝓕 (h q)) ξ‖^2))≤fourthEnergy (h q) := by
      apply lintegral_mono
      intro ξ
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply Real.rpow_le_rpow_of_exponent_le
      · linarith [abs_nonneg (ξ 0),abs_nonneg (ξ 1)]
      · linarith [s.2.2]
    apply (hs.trans (fourth_energy_bound (h q))).trans_eq
    simp only [mass_schwartz]
    have ha0 : 0≤A q := integral_nonneg (fun u => sq_nonneg _)
    have hb0 : 0≤B q := integral_nonneg (fun u => sq_nonneg _)
    have hc0 : 0≤C q := integral_nonneg (fun u => sq_nonneg _)
    change ENNReal.ofReal ((3 : ℝ)^(4 : ℝ))*(ENNReal.ofReal (A q)+ENNReal.ofReal (B q)+ENNReal.ofReal (C q))=_
    rw [←ENNReal.ofReal_add ha0 hb0,←ENNReal.ofReal_add (add_nonneg ha0 hb0) hc0,
      ←ENNReal.ofReal_mul (by positivity : 0≤(3 : ℝ)^(4 : ℝ))]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hj (fun _ => bot_le) hb

end RHTower.BAGTrace