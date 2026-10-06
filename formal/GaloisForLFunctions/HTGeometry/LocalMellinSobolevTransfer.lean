import GaloisForLFunctions.HTGeometry.CompactMellinLocalization
import GaloisForLFunctions.HTGeometry.LocalLogFractionalEnergy

/-!
# Uniform local Mellin Sobolev transfer

The literal compactly localized Mellin log profile has complete weighted
Fourier energy of order `1 + theta` bounded by the same physical Fourier
energy, uniformly over its full compact Mellin parameter square.

The planar log chart pays both Jacobians. Actual compact Euler coefficients
transfer fractional energy to the first logarithmic derivative; exact Fourier
differentiation and the positive Gagliardo constant recover its spectral
moment. Output mass and the two diagonal moments control the full planar
weight. All energy admission is proved for Schwartz inputs, with no assumed
uniform higher seminorms. Actual selected-family and exterior attachment
remain distinct BAG obligations.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform Topology ContDiff ENNReal
namespace GaloisForLFunctions.HTGeometry
private abbrev E := HTGeometry.QuadrantLogSpace

private def chartCoords : E≃ᵐℝ×ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2→ℝ)).symm.trans MeasurableEquiv.finTwoArrow

private def axisCoords (i : Fin 2) : E≃ᵐℝ×ℝ :=
  if i=0 then chartCoords else chartCoords.trans MeasurableEquiv.prodComm

private def axisPoint (i : Fin 2) (x y : ℝ) : E := (axisCoords i).symm (x,y)

private theorem axisCoords_preserving (i : Fin 2) : MeasurePreserving (axisCoords i) := by
  have hc : MeasurePreserving chartCoords :=
    (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
  by_cases hi : i=0
  · simpa only [axisCoords,if_pos hi] using hc
  · simpa only [axisCoords,if_neg hi] using! Measure.measurePreserving_swap.comp hc

private theorem axisPoint_continuous (i : Fin 2) :
    Continuous (fun z : ℝ×ℝ => axisPoint i z.1 z.2) := by
  have hc : Continuous (fun z : ℝ×ℝ => chartCoords.symm z) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.continuous
  by_cases hi : i=0
  · simpa only [axisPoint,axisCoords,if_pos hi] using hc
  · simpa only [axisPoint,axisCoords,if_neg hi] using! hc.comp continuous_swap

private theorem axisPoint_shift (i : Fin 2) (x y h : ℝ) :
    axisPoint i (x+h) y=axisPoint i x y+h • HTGeometry.quadrantLogBasis i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [axisPoint,axisCoords,chartCoords,MeasurableEquiv.prodComm,HTGeometry.quadrantLogBasis]

private theorem axisPoint_log (i : Fin 2) (x y : ℝ) :
    HTGeometry.quadrantLogNode (axisPoint i x y)=axisPoint i (Real.exp (-x)) (Real.exp (-y)) := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [axisPoint,axisCoords,chartCoords,MeasurableEquiv.prodComm,HTGeometry.quadrantLogNode_apply]

private theorem axisPoint_box (i : Fin 2) (a b x y : ℝ) :
    (∀j, axisPoint i x y j∈Icc a b) ↔ x∈Icc a b ∧ y∈Icc a b := by
  fin_cases i <;> simp [axisPoint,axisCoords,chartCoords,MeasurableEquiv.prodComm,Fin.forall_fin_two,and_comm]

private theorem lintegral_axis (i : Fin 2) (F : E→ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ u : E, F u)=∫⁻ y : ℝ, ∫⁻ x : ℝ, F (axisPoint i x y) := by
  have hp := (axisCoords_preserving i).symm (axisCoords i)
  rw [←hp.lintegral_comp_emb (axisCoords i).symm.measurableEmbedding F]
  exact lintegral_prod_symm' _ (hF.comp (axisCoords i).symm.measurable)

private theorem axisPoint_sub (i : Fin 2) (x y h : ℝ) :
    axisPoint i (x-h) y=axisPoint i x y+h • (-HTGeometry.quadrantLogBasis i) := by
  rw [sub_eq_add_neg,axisPoint_shift]
  simp only [neg_smul,smul_neg]

private def dirEnergy (s : ℝ) (v : E) (f : E→ℂ) : ℝ≥0∞ :=
  ∫⁻ h in Ioi (0 : ℝ), ∫⁻ x : E, ENNReal.ofReal (‖f x-f (x+h • v)‖^2*h^(-(1+2*s)))

private def mass (f : E→ℂ) : ℝ≥0∞ := ∫⁻ x : E, ENNReal.ofReal (‖f x‖^2)

private theorem logNode_continuous : Continuous HTGeometry.quadrantLogNode :=
  (((Real.continuous_exp.comp (EuclideanSpace.proj 0 : E→L[ℝ]ℝ).continuous.neg).smul continuous_const).add
    ((Real.continuous_exp.comp (EuclideanSpace.proj 1 : E→L[ℝ]ℝ).continuous.neg).smul continuous_const))

private theorem euclidean_log_chart_energy (s : {r : ℝ // r∈Ioo (0 : ℝ) 1})
    (a b : {r : ℝ // 0<r}) :
    ∃ C : ℝ, 0<C ∧ ∀(i : Fin 2)
      (f : {g : E→ℂ // Continuous g ∧ Function.support g⊆{x | ∀j, x j∈Icc a.1 b.1}}),
      dirEnergy s.1 (HTGeometry.quadrantLogBasis i) (fun u => f.1 (HTGeometry.quadrantLogNode u)) ≤
        ENNReal.ofReal C*(dirEnergy s.1 (-HTGeometry.quadrantLogBasis i) f.1+mass f.1) := by
  obtain ⟨C,hC,hCb⟩ := local_log_fractional_planar s a b
  refine ⟨C,hC,fun i f => ?_⟩
  let g : ℝ×ℝ→ℂ := fun z => f.1 (axisPoint i z.1 z.2)
  have hgc : Continuous g := f.2.1.comp (axisPoint_continuous i)
  have hgm := hgc.measurable
  have hfm := f.2.1.measurable
  have hgs : Function.support g⊆Icc a.1 b.1×ˢIcc a.1 b.1 := by
    intro z hz
    exact (axisPoint_box i a.1 b.1 z.1 z.2).mp (f.2.2 hz)
  have hb := hCb ⟨g,hgc,hgs⟩
  have hleft : dirEnergy s.1 (HTGeometry.quadrantLogBasis i)
      (fun u => f.1 (HTGeometry.quadrantLogNode u))=
        ∫⁻ v : ℝ, ∫⁻ h in Ioi (0 : ℝ), ∫⁻ u : ℝ,
          ENNReal.ofReal (‖g (Real.exp (-u),Real.exp (-v))-
            g (Real.exp (-(u+h)),Real.exp (-v))‖^2*h^(-(1+2*s.1))) := by
    have hn := logNode_continuous.measurable
    have he (h : ℝ) : (∫⁻ u : E,
        ENNReal.ofReal (‖f.1 (HTGeometry.quadrantLogNode u)-
          f.1 (HTGeometry.quadrantLogNode (u+h • HTGeometry.quadrantLogBasis i))‖^2*h^(-(1+2*s.1))))=
        ∫⁻ v : ℝ, ∫⁻ u : ℝ,
          ENNReal.ofReal (‖g (Real.exp (-u),Real.exp (-v))-
            g (Real.exp (-(u+h)),Real.exp (-v))‖^2*h^(-(1+2*s.1))) := by
      rw [lintegral_axis i _ (by fun_prop)]
      apply lintegral_congr
      intro v
      apply lintegral_congr
      intro u
      simp only [←axisPoint_shift,axisPoint_log,g]
    unfold dirEnergy
    simp_rw [he]
    have hm : Measurable (fun z : ℝ×ℝ => ∫⁻ u : ℝ,
        ENNReal.ofReal (‖g (Real.exp (-u),Real.exp (-z.2))-
          g (Real.exp (-(u+z.1)),Real.exp (-z.2))‖^2*z.1^(-(1+2*s.1)))) := by fun_prop
    exact lintegral_lintegral_swap hm.aemeasurable
  have hright : (∫⁻ y : ℝ,
      ((∫⁻ h in Ioi (0 : ℝ), ∫⁻ x : ℝ,
        ENNReal.ofReal (‖g (x,y)-g (x-h,y)‖^2*h^(-(1+2*s.1))))+
          ∫⁻ x : ℝ, ENNReal.ofReal (‖g (x,y)‖^2)))=
      dirEnergy s.1 (-HTGeometry.quadrantLogBasis i) f.1+mass f.1 := by
    have hem : Measurable (fun y : ℝ => ∫⁻ h in Ioi (0 : ℝ), ∫⁻ x : ℝ,
        ENNReal.ofReal (‖g (x,y)-g (x-h,y)‖^2*h^(-(1+2*s.1)))) := by fun_prop
    rw [lintegral_add_left hem]
    congr 1
    · have hswap : Measurable (fun z : ℝ×ℝ => ∫⁻ x : ℝ,
          ENNReal.ofReal (‖g (x,z.1)-g (x-z.2,z.1)‖^2*z.2^(-(1+2*s.1)))) := by fun_prop
      rw [lintegral_lintegral_swap hswap.aemeasurable]
      apply lintegral_congr
      intro h
      rw [lintegral_axis i _ (by fun_prop)]
      apply lintegral_congr
      intro y
      apply lintegral_congr
      intro x
      simp only [g,axisPoint_sub]
    · exact (lintegral_axis i (fun x : E => ENNReal.ofReal (‖f.1 x‖^2)) (by fun_prop)).symm
  rw [hleft]
  simpa only [hright] using hb

private def spectralBudget (s : ℝ) (v : E) (f : SchwartzMap E ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (∫ξ : E, |inner ℝ v ξ|^(2*s)*‖(𝓕 f) ξ‖^2)+
    ENNReal.ofReal (∫x : E, ‖f x‖^2)

private theorem mass_schwartz (f : SchwartzMap E ℂ) :
    mass f=ENNReal.ofReal (∫x : E, ‖f x‖^2) := by
  exact (ofReal_integral_eq_lintegral_ofReal
    ((f.memLp 2).integrable_norm_pow (by norm_num : 2≠0))
      (Eventually.of_forall (fun x : E => sq_nonneg ‖f x‖))).symm

private theorem coefficient_log_energy (s : {r : ℝ // r∈Ioo (0 : ℝ) 1})
    (i : Fin 2) (k : Fin 3) (j : Fin 2) :
    ∃ C : ℝ, 0<C ∧ ∀(σ : E) (f : SchwartzMap E ℂ),
      dirEnergy s.1 (HTGeometry.quadrantLogBasis j)
        (fun u => compactMellinJetCoefficient i k (σ,HTGeometry.quadrantLogNode u)*
          f (HTGeometry.quadrantLogNode u)) ≤
        ENNReal.ofReal C*spectralBudget s.1 (-HTGeometry.quadrantLogBasis j) f := by
  obtain ⟨L,hL,hLb⟩ := euclidean_log_chart_energy s ⟨1/8,by norm_num⟩ ⟨8,by norm_num⟩
  obtain ⟨A,hA,hAb⟩ := compactMellinJetCoefficient_uniform_fractional_energy s i k
    (-HTGeometry.quadrantLogBasis j)
  obtain ⟨B,hB,hBb⟩ := compactMellinJetCoefficient_uniform_mass i k
  refine ⟨L*(A+B),mul_pos hL (add_pos hA hB),fun σ f => ?_⟩
  let g : E→ℂ := fun x => compactMellinJetCoefficient i k (σ,x)*f x
  have hgc : Continuous g :=
    ((compactMellinJetCoefficient_spec i k).1.continuous.comp
      (continuous_const.prodMk continuous_id)).mul f.continuous
  have hgs : Function.support g⊆{x | ∀j, x j∈Icc (1/8 : ℝ) 8} := by
    intro x hx j
    have hn : compactMellinJetCoefficient i k (σ,x)≠0 := by
      intro hz
      exact hx (by simp [g,hz])
    exact ⟨(compactMellinJetCoefficient_support i k _ (subset_tsupport _ hn) j).1.le,
      (compactMellinJetCoefficient_support i k _ (subset_tsupport _ hn) j).2.le⟩
  have hb := hLb j ⟨g,hgc,hgs⟩
  have hm : mass g ≤ ENNReal.ofReal B*spectralBudget s.1 (-HTGeometry.quadrantLogBasis j) f := by
    calc mass g ≤ ENNReal.ofReal B*mass f := hBb σ f
      _ ≤ ENNReal.ofReal B*spectralBudget s.1 (-HTGeometry.quadrantLogBasis j) f := by
        rw [mass_schwartz]
        exact mul_le_mul_right (le_add_of_nonneg_left zero_le) _
  refine hb.trans ?_
  change ENNReal.ofReal L*(dirEnergy s.1 (-HTGeometry.quadrantLogBasis j) g+mass g) ≤ _
  rw [ENNReal.ofReal_mul hL.le,ENNReal.ofReal_add hA.le hB.le,mul_assoc,add_mul]
  exact mul_le_mul_right (add_le_add (hAb σ f).2 hm) _

private theorem sum_energy (s : ℝ) (v : E) (f g : E→ℂ)
    (hf : Continuous f) (hg : Continuous g) :
    dirEnergy s v (fun x => f x+g x) ≤ 2*(dirEnergy s v f+dirEnergy s v g) := by
  have hfm := hf.measurable
  have hgm := hg.measurable
  have hp (h : ℝ) (hh : 0<h) (x : E) :
      ENNReal.ofReal (‖(f x+g x)-(f (x+h • v)+g (x+h • v))‖^2*h^(-(1+2*s))) ≤
        (2 : ℝ≥0∞)*(ENNReal.ofReal (‖f x-f (x+h • v)‖^2*h^(-(1+2*s)))+
          ENNReal.ofReal (‖g x-g (x+h • v)‖^2*h^(-(1+2*s)))) := by
    have hn : ‖(f x-f (x+h • v))+(g x-g (x+h • v))‖^2 ≤
        2*(‖f x-f (x+h • v)‖^2+‖g x-g (x+h • v)‖^2) := by
      have ht := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le
        (f x-f (x+h • v)) (g x-g (x+h • v))) 2
      nlinarith only [ht,sq_nonneg (‖f x-f (x+h • v)‖-‖g x-g (x+h • v)‖)]
    have hpow := (Real.rpow_pos_of_pos hh (-(1+2*s))).le
    have he : (f x+g x)-(f (x+h • v)+g (x+h • v))=
        (f x-f (x+h • v))+(g x-g (x+h • v)) := by ring
    rw [he]
    have hb := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hn hpow)
    simpa only [mul_assoc,add_mul,ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_ofNat,ENNReal.ofReal_add
        (mul_nonneg (sq_nonneg _) hpow) (mul_nonneg (sq_nonneg _) hpow)] using hb
  have hm (h : ℝ) : Measurable (fun x : E =>
      ENNReal.ofReal (‖f x-f (x+h • v)‖^2*h^(-(1+2*s)))) := by fun_prop
  have hM : Measurable (fun h : ℝ => ∫⁻ x : E,
      ENNReal.ofReal (‖f x-f (x+h • v)‖^2*h^(-(1+2*s)))) := by fun_prop
  calc dirEnergy s v (fun x => f x+g x) ≤ (∫⁻ h in Ioi (0 : ℝ), ∫⁻ x : E,
      (2 : ℝ≥0∞)*(ENNReal.ofReal (‖f x-f (x+h • v)‖^2*h^(-(1+2*s)))+
        ENNReal.ofReal (‖g x-g (x+h • v)‖^2*h^(-(1+2*s))))) := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro h hh
        exact lintegral_mono (hp h hh)
    _ = _ := by
      have he (h : ℝ) : (∫⁻ x : E,
          (2 : ℝ≥0∞)*(ENNReal.ofReal (‖f x-f (x+h • v)‖^2*h^(-(1+2*s)))+
            ENNReal.ofReal (‖g x-g (x+h • v)‖^2*h^(-(1+2*s)))))=
          2*((∫⁻ x : E, ENNReal.ofReal (‖f x-f (x+h • v)‖^2*h^(-(1+2*s))))+
            ∫⁻ x : E, ENNReal.ofReal (‖g x-g (x+h • v)‖^2*h^(-(1+2*s)))) := by
        rw [lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞)),lintegral_add_left (hm h)]
      simp_rw [he]
      rw [lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞)),lintegral_add_left hM]
      rfl

open LineDeriv

private theorem localized_euler_energy (s : {r : ℝ // r∈Ioo (0 : ℝ) 1}) (i : Fin 2) :
    ∃ C : ℝ, 0<C ∧ ∀(σ : {q : E // ∀j, q j∈Icc (1 : ℝ) 2}) (f : SchwartzMap E ℂ),
      dirEnergy s.1 (HTGeometry.quadrantLogBasis i)
        (∂_{HTGeometry.quadrantLogBasis i} (compactLocalizedMellinSchwartz σ f) : SchwartzMap E ℂ) ≤
        ENNReal.ofReal C*(spectralBudget s.1 (-HTGeometry.quadrantLogBasis i) f+
          spectralBudget s.1 (-HTGeometry.quadrantLogBasis i) (∂_{HTGeometry.quadrantLogBasis i} f)) := by
  obtain ⟨A,hA,hAb⟩ := coefficient_log_energy s i 1 i
  obtain ⟨B,hB,hBb⟩ := coefficient_log_energy s i 2 i
  refine ⟨2*(A+B),mul_pos (by norm_num) (add_pos hA hB),fun σ f => ?_⟩
  let g : E→ℂ := fun u => compactMellinJetCoefficient i 1 (σ.1,HTGeometry.quadrantLogNode u)*
    f (HTGeometry.quadrantLogNode u)
  let q : E→ℂ := fun u => compactMellinJetCoefficient i 2 (σ.1,HTGeometry.quadrantLogNode u)*
    (∂_{HTGeometry.quadrantLogBasis i} f) (HTGeometry.quadrantLogNode u)
  have hgc : Continuous g :=
    ((compactMellinJetCoefficient_spec i 1).1.continuous.comp
      (continuous_const.prodMk logNode_continuous)).mul (f.continuous.comp logNode_continuous)
  have hqc : Continuous q :=
    ((compactMellinJetCoefficient_spec i 2).1.continuous.comp
      (continuous_const.prodMk logNode_continuous)).mul
        ((∂_{HTGeometry.quadrantLogBasis i} f).continuous.comp logNode_continuous)
  have he : (⇑(∂_{HTGeometry.quadrantLogBasis i} (compactLocalizedMellinSchwartz σ f) : SchwartzMap E ℂ))=
      fun u => g u+q u := by
    funext u
    simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv,compactLocalizedMellinSchwartz_euler,
      g,q,compactMellinJetCoefficient]
  rw [he]
  refine (sum_energy s.1 _ g q hgc hqc).trans ?_
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),ENNReal.ofReal_ofNat,mul_assoc]
  apply mul_le_mul_right
  calc dirEnergy s.1 (HTGeometry.quadrantLogBasis i) g+
        dirEnergy s.1 (HTGeometry.quadrantLogBasis i) q ≤
      ENNReal.ofReal A*spectralBudget s.1 (-HTGeometry.quadrantLogBasis i) f+
        ENNReal.ofReal B*spectralBudget s.1 (-HTGeometry.quadrantLogBasis i)
          (∂_{HTGeometry.quadrantLogBasis i} f) := add_le_add (hAb σ.1 f) (hBb σ.1 _)
    _ ≤ _ := by
      rw [mul_add]
      exact add_le_add
        (mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith : A ≤ A+B)) _)
        (mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith : B ≤ A+B)) _)

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

private theorem euclidean_log_mass (a b : {r : ℝ // 0<r})
    (f : {g : E→ℂ // Continuous g ∧ Function.support g⊆{x | ∀j, x j∈Icc a.1 b.1}}) :
    mass (fun u => f.1 (HTGeometry.quadrantLogNode u)) ≤
      ENNReal.ofReal (a.1⁻¹)^2*mass f.1 := by
  let g : ℝ→ℝ→ℝ≥0∞ := fun x y => ENNReal.ofReal (‖f.1 (axisPoint 0 x y)‖^2)
  let F : ℝ→ℝ≥0∞ := fun y => ∫⁻ x : ℝ, g x y
  have hzero (x y : ℝ) (hxy : ¬(x∈Icc a.1 b.1 ∧ y∈Icc a.1 b.1)) : g x y=0 := by
    have hfzero : f.1 (axisPoint 0 x y)=0 := by
      by_contra hn
      exact hxy ((axisPoint_box 0 a.1 b.1 x y).mp (f.2.2 hn))
    simp only [g,hfzero,norm_zero,zero_pow (by norm_num : 2≠0),ENNReal.ofReal_zero]
  have hgs (y : ℝ) : Function.support (fun x => g x y)⊆Icc a.1 b.1 := by
    intro x hx
    by_contra hn
    exact hx (hzero x y (fun hh => hn hh.1))
  have hFs : Function.support F⊆Icc a.1 b.1 := by
    intro y hy
    by_contra hn
    have hz : F y=0 := by
      dsimp only [F]
      have he (x : ℝ) : g x y=0 := hzero x y (fun hh => hn hh.2)
      simp only [he,lintegral_zero]
    exact hy hz
  have hf := f.2.1.measurable
  have hn := logNode_continuous.measurable
  have he : mass (fun u => f.1 (HTGeometry.quadrantLogNode u))=
      ∫⁻ v : ℝ, ∫⁻ u : ℝ, g (Real.exp (-u)) (Real.exp (-v)) := by
    rw [mass,lintegral_axis 0 _ (by fun_prop)]
    simp only [axisPoint_log,g]
  rw [he]
  calc (∫⁻ v : ℝ, ∫⁻ u : ℝ, g (Real.exp (-u)) (Real.exp (-v))) ≤
      ∫⁻ v : ℝ, ENNReal.ofReal (a.1⁻¹)*F (Real.exp (-v)) :=
        lintegral_mono (fun v => log_supported_lintegral a b _ (hgs (Real.exp (-v))))
    _ = ENNReal.ofReal (a.1⁻¹)*∫⁻ v : ℝ, F (Real.exp (-v)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (a.1⁻¹)*(ENNReal.ofReal (a.1⁻¹)*∫⁻ y : ℝ, F y) :=
      mul_le_mul_right (log_supported_lintegral a b F hFs) _
    _ = ENNReal.ofReal (a.1⁻¹)^2*mass f.1 := by
      rw [pow_two,mul_assoc]
      congr 1
      congr 1
      exact (lintegral_axis 0 (fun x : E => ENNReal.ofReal (‖f.1 x‖^2)) (by fun_prop)).symm

private theorem localized_mass :
    ∃ C : ℝ, 0<C ∧ ∀(σ : {q : E // ∀j, q j∈Icc (1 : ℝ) 2}) (f : SchwartzMap E ℂ),
      mass (compactLocalizedMellinSchwartz σ f) ≤ ENNReal.ofReal C*mass f := by
  obtain ⟨B,hB,hBb⟩ := compactMellinJetCoefficient_uniform_mass 0 0
  refine ⟨64*B,mul_pos (by norm_num) hB,fun σ f => ?_⟩
  let g : E→ℂ := fun x => compactMellinCoefficient (σ.1,x)*f x
  have hgc : Continuous g :=
    (compactMellinCoefficient_smooth.continuous.comp
      (continuous_const.prodMk continuous_id)).mul f.continuous
  have hgs : Function.support g⊆{x | ∀j, x j∈Icc (1/8 : ℝ) 8} := by
    intro x hx j
    have hn : compactMellinJetCoefficient 0 0 (σ.1,x)≠0 := by
      intro hz
      have hz' : compactMellinCoefficient (σ.1,x)=0 := hz
      exact hx (by simp only [g,hz',zero_mul])
    have hb := compactMellinJetCoefficient_support 0 0 _ (subset_tsupport _ hn) j
    exact ⟨hb.1.le,hb.2.le⟩
  have hc := euclidean_log_mass ⟨1/8,by norm_num⟩ ⟨8,by norm_num⟩ ⟨g,hgc,hgs⟩
  have he : (compactLocalizedMellinSchwartz σ f : E→ℂ)=
      (fun u => g (HTGeometry.quadrantLogNode u)) := funext (compactLocalizedMellinSchwartz_apply σ f)
  rw [he]
  refine hc.trans ?_
  change ENNReal.ofReal ((1/8 : ℝ)⁻¹)^2*mass g ≤ _
  norm_num only [one_div,inv_inv,ENNReal.ofReal_ofNat,ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64)]
  calc (64 : ℝ≥0∞)*mass g ≤ (64 : ℝ≥0∞)*(ENNReal.ofReal B*mass f) :=
      mul_le_mul_right (hBb σ.1 f) _
    _ = _ := by norm_num [mul_assoc]

private def axialMoment (p : ℝ) (i : Fin 2) (f : SchwartzMap E ℂ) : ℝ≥0∞ :=
  ∫⁻ ξ : E, ENNReal.ofReal (|ξ i|^p*‖(𝓕 f) ξ‖^2)

private def fullEnergy (s : ℝ) (f : SchwartzMap E ℂ) : ℝ≥0∞ :=
  ∫⁻ ξ : E, ENNReal.ofReal ((1+|ξ 0|+|ξ 1|)^(2+2*s)*‖(𝓕 f) ξ‖^2)

private theorem inner_basis (ξ : E) (i : Fin 2) :
    inner ℝ ξ (HTGeometry.quadrantLogBasis i)=ξ i := by
  change inner ℝ ξ (EuclideanSpace.single i (1 : ℝ))=ξ i
  simp [EuclideanSpace.inner_single_right]

private theorem basis_inner (ξ : E) (i : Fin 2) :
    inner ℝ (HTGeometry.quadrantLogBasis i) ξ=ξ i := by
  rw [real_inner_comm,inner_basis]

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

private theorem spectralBudget_eq (s : {r : ℝ // r∈Ioo (0 : ℝ) 1})
    (i : Fin 2) (f : SchwartzMap E ℂ) :
    spectralBudget s.1 (-HTGeometry.quadrantLogBasis i) f=axialMoment (2*s.1) i f+mass f := by
  obtain ⟨D,hD,hDb⟩ := directional_gagliardo_fourier (E := E) s
  have hi := (hDb f (-HTGeometry.quadrantLogBasis i)).1
  have he := ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun ξ : E => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _)))
  rw [spectralBudget,he,←mass_schwartz]
  simp only [axialMoment,inner_neg_left,basis_inner,abs_neg]

private theorem derivative_axialMoment (p : ℝ) (hp : 0 ≤ p) (i : Fin 2) (f : SchwartzMap E ℂ) :
    axialMoment p i (∂_{HTGeometry.quadrantLogBasis i} f)=
      ENNReal.ofReal ((2*Real.pi)^2)*axialMoment (p+2) i f := by
  have he (ξ : E) : |ξ i|^p*‖(𝓕 (∂_{HTGeometry.quadrantLogBasis i} f : SchwartzMap E ℂ)) ξ‖^2=
      (2*Real.pi)^2*(|ξ i|^(p+2)*‖(𝓕 f) ξ‖^2) := by
    rw [derivative_fourier_norm,Real.rpow_add_of_nonneg (abs_nonneg _) hp (by norm_num),Real.rpow_two]
    ring
  simp only [axialMoment,he,ENNReal.ofReal_mul (sq_nonneg _)]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

private theorem derivative_mass (i : Fin 2) (f : SchwartzMap E ℂ) :
    mass (∂_{HTGeometry.quadrantLogBasis i} f : SchwartzMap E ℂ)=
      ENNReal.ofReal ((2*Real.pi)^2)*axialMoment 2 i f := by
  rw [←mass_fourier]
  simp only [mass,axialMoment,derivative_fourier_norm,Real.rpow_two,mul_assoc,
    ENNReal.ofReal_mul (sq_nonneg _)]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

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

private theorem fullEnergy_axes (s : {r : ℝ // r∈Ioo (0 : ℝ) 1}) (f : SchwartzMap E ℂ) :
    fullEnergy s.1 f ≤ ENNReal.ofReal ((3 : ℝ)^(2+2*s.1))*
      (mass f+axialMoment (2+2*s.1) 0 f+axialMoment (2+2*s.1) 1 f) := by
  have hf := (𝓕 f).continuous.measurable
  have hm : Measurable (fun ξ : E => ENNReal.ofReal (‖(𝓕 f) ξ‖^2)) := by fun_prop
  have h0 : Measurable (fun ξ : E => ENNReal.ofReal (|ξ 0|^(2+2*s.1)*‖(𝓕 f) ξ‖^2)) := by fun_prop
  have he : (∫⁻ ξ : E, ENNReal.ofReal ((3 : ℝ)^(2+2*s.1))*
      (ENNReal.ofReal (‖(𝓕 f) ξ‖^2)+
        ENNReal.ofReal (|ξ 0|^(2+2*s.1)*‖(𝓕 f) ξ‖^2)+
          ENNReal.ofReal (|ξ 1|^(2+2*s.1)*‖(𝓕 f) ξ‖^2)))=
      ENNReal.ofReal ((3 : ℝ)^(2+2*s.1))*
        (mass f+axialMoment (2+2*s.1) 0 f+axialMoment (2+2*s.1) 1 f) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hm0 : Measurable (fun ξ : E => ENNReal.ofReal (‖(𝓕 f) ξ‖^2)+
        ENNReal.ofReal (|ξ 0|^(2+2*s.1)*‖(𝓕 f) ξ‖^2)) := hm.add h0
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
  have hb := mul_le_mul_of_nonneg_right (weight_axes_bound (2+2*s.1) (by linarith [s.2.1])
    (ξ 0) (ξ 1)) (sq_nonneg ‖(𝓕 f) ξ‖)
  convert! hb using 1
  ring

private theorem axialMoment_le_full (s : {r : ℝ // r∈Ioo (0 : ℝ) 1})
    (p : ℝ) (hp : 0 ≤ p) (hps : p ≤ 2+2*s.1) (i : Fin 2) (f : SchwartzMap E ℂ) :
    axialMoment p i f ≤ fullEnergy s.1 f := by
  apply lintegral_mono
  intro ξ
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hi : |ξ i| ≤ 1+|ξ 0|+|ξ 1| := by
    fin_cases i
    · change |ξ 0| ≤ _
      linarith [abs_nonneg (ξ 1)]
    · change |ξ 1| ≤ _
      linarith [abs_nonneg (ξ 0)]
  exact (Real.rpow_le_rpow (abs_nonneg _) hi hp).trans
    (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (ξ 0),abs_nonneg (ξ 1)]) hps)

private theorem mass_le_full (s : {r : ℝ // r∈Ioo (0 : ℝ) 1}) (f : SchwartzMap E ℂ) :
    mass f ≤ fullEnergy s.1 f := by
  have he : axialMoment 0 0 f=mass f := by
    simp only [axialMoment,Real.rpow_zero,one_mul]
    exact mass_fourier f
  rw [←he]
  exact axialMoment_le_full s 0 (by norm_num) (by linarith [s.2.1]) 0 f

private theorem input_budget_le_full (s : {r : ℝ // r∈Ioo (0 : ℝ) 1})
    (i : Fin 2) (f : SchwartzMap E ℂ) :
    spectralBudget s.1 (-HTGeometry.quadrantLogBasis i) f+
      spectralBudget s.1 (-HTGeometry.quadrantLogBasis i) (∂_{HTGeometry.quadrantLogBasis i} f) ≤
        ENNReal.ofReal (2+2*(2*Real.pi)^2)*fullEnergy s.1 f := by
  rw [spectralBudget_eq,spectralBudget_eq,derivative_axialMoment _ (by linarith [s.2.1]),derivative_mass]
  have h1 := axialMoment_le_full s (2*s.1) (by linarith [s.2.1]) (by linarith) i f
  have h2 := mass_le_full s f
  have h3 := axialMoment_le_full s (2*s.1+2) (by linarith [s.2.1]) (by linarith) i f
  have h4 := axialMoment_le_full s 2 (by norm_num) (by linarith [s.2.1]) i f
  refine (add_le_add (add_le_add h1 h2)
    (add_le_add (mul_le_mul_right h3 _) (mul_le_mul_right h4 _))).trans_eq ?_
  rw [ENNReal.ofReal_add (by norm_num) (by positivity),ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_ofNat]
  ring
private theorem euler_energy_identity (s : {r : ℝ // r∈Ioo (0 : ℝ) 1}) :
    ∃ D : ℝ, 0<D ∧ ∀(f : SchwartzMap E ℂ) (i : Fin 2),
      dirEnergy s.1 (HTGeometry.quadrantLogBasis i) (∂_{HTGeometry.quadrantLogBasis i} f : SchwartzMap E ℂ)=
        ENNReal.ofReal D*axialMoment (2+2*s.1) i f := by
  obtain ⟨D,hD,hDb⟩ := directional_gagliardo_fourier (E := E) s
  have hK : 0<(2*Real.pi)^2 := sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos)
  refine ⟨D*(2*Real.pi)^2,mul_pos hD hK,fun f i => ?_⟩
  let g : SchwartzMap E ℂ := ∂_{HTGeometry.quadrantLogBasis i} f
  have hi := (hDb g (HTGeometry.quadrantLogBasis i)).1
  have he := (hDb g (HTGeometry.quadrantLogBasis i)).2
  rw [ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun ξ : E => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _)))] at he
  simp only [basis_inner] at he
  change dirEnergy s.1 (HTGeometry.quadrantLogBasis i) g=
    ENNReal.ofReal D*axialMoment (2*s.1) i g at he
  rw [he,show g=(∂_{HTGeometry.quadrantLogBasis i} f : SchwartzMap E ℂ) from rfl,
    derivative_axialMoment _ (by linarith [s.2.1]),ENNReal.ofReal_mul hD.le,mul_assoc,
    show 2*s.1+2=2+2*s.1 by ring]

private theorem axialMoment_lt_top (s : {r : ℝ // r∈Ioo (0 : ℝ) 1})
    (i : Fin 2) (f : SchwartzMap E ℂ) : axialMoment (2+2*s.1) i f < (∞ : ℝ≥0∞) := by
  obtain ⟨D,hD,hDb⟩ := euler_energy_identity s
  obtain ⟨C,hC,hCb⟩ := directional_gagliardo_fourier (E := E) s
  have he := (hCb (∂_{HTGeometry.quadrantLogBasis i} f) (HTGeometry.quadrantLogBasis i)).2
  have hb : ENNReal.ofReal D*axialMoment (2+2*s.1) i f < (∞ : ℝ≥0∞) := by
    rw [←hDb f i]
    change (∫⁻ h in Ioi (0 : ℝ), ∫⁻ x : E,
      ENNReal.ofReal (‖(∂_{HTGeometry.quadrantLogBasis i} f) x-
        (∂_{HTGeometry.quadrantLogBasis i} f) (x+h • HTGeometry.quadrantLogBasis i)‖^2*h^(-(1+2*s.1)))) < (∞ : ℝ≥0∞)
    rw [he]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  rcases ENNReal.mul_lt_top_iff.mp hb with h | h | h
  · exact h.2
  · exact False.elim ((ne_of_gt (ENNReal.ofReal_pos.mpr hD)) h)
  · simp only [h,ENNReal.zero_lt_top]

private theorem fullEnergy_lt_top (s : {r : ℝ // r∈Ioo (0 : ℝ) 1}) (f : SchwartzMap E ℂ) :
    fullEnergy s.1 f < (∞ : ℝ≥0∞) := by
  refine (fullEnergy_axes s f).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  apply ENNReal.add_lt_top.mpr
  refine ⟨ENNReal.add_lt_top.mpr ⟨?_,axialMoment_lt_top s 0 f⟩,axialMoment_lt_top s 1 f⟩
  rw [mass_schwartz]
  exact ENNReal.ofReal_lt_top

private theorem localized_axialMoment (s : {r : ℝ // r∈Ioo (0 : ℝ) 1}) (i : Fin 2) :
    ∃ C : ℝ, 0<C ∧ ∀(σ : {q : E // ∀j, q j∈Icc (1 : ℝ) 2}) (f : SchwartzMap E ℂ),
      axialMoment (2+2*s.1) i (compactLocalizedMellinSchwartz σ f) ≤
        ENNReal.ofReal C*fullEnergy s.1 f := by
  obtain ⟨D,hD,hDb⟩ := euler_energy_identity s
  obtain ⟨A,hA,hAb⟩ := localized_euler_energy s i
  let T : ℝ := 2+2*(2*Real.pi)^2
  have hT : 0<T := by dsimp only [T]; positivity
  refine ⟨D⁻¹*(A*T),mul_pos (inv_pos.mpr hD) (mul_pos hA hT),fun σ f => ?_⟩
  have hb := (hAb σ f).trans (mul_le_mul_right (input_budget_le_full s i f) (ENNReal.ofReal A))
  rw [hDb,←mul_assoc,←ENNReal.ofReal_mul hA.le] at hb
  have hh := (ENNReal.mul_le_iff_le_inv (ne_of_gt (ENNReal.ofReal_pos.mpr hD)) ENNReal.ofReal_ne_top).mp hb
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr hD.le),ENNReal.ofReal_inv_of_pos hD,mul_assoc]
  exact hh

/-- Uniform complete Fourier energy of the literal compact Mellin logarithmic profile.
The bound crosses order one through its exact Euler derivative and holds for
all inputs and all Mellin parameters in the full compact square. No analytic
budget or uniform Schwartz seminorm is assumed. -/
theorem compactLocalizedMellinSchwartz_uniform_energy
    (s : {r : ℝ // r∈Ioo (0 : ℝ) 1}) :
    ∃ C : ℝ, 0<C ∧ ∀(σ : {q : E // ∀j, q j∈Icc (1 : ℝ) 2}) (f : SchwartzMap E ℂ),
      let L := ∫⁻ ξ : E, ENNReal.ofReal ((1+|ξ 0|+|ξ 1|)^(2+2*s.1)*
        ‖(𝓕 (compactLocalizedMellinSchwartz σ f)) ξ‖^2)
      L < (∞ : ℝ≥0∞) ∧ L ≤ ENNReal.ofReal C*
        ∫⁻ ξ : E, ENNReal.ofReal ((1+|ξ 0|+|ξ 1|)^(2+2*s.1)*‖(𝓕 f) ξ‖^2) := by
  obtain ⟨M,hM,hMb⟩ := localized_mass
  obtain ⟨A,hA,hAb⟩ := localized_axialMoment s 0
  obtain ⟨B,hB,hBb⟩ := localized_axialMoment s 1
  refine ⟨(3 : ℝ)^(2+2*s.1)*(M+A+B),
    mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (add_pos (add_pos hM hA) hB),fun σ f => ?_⟩
  change fullEnergy s.1 (compactLocalizedMellinSchwartz σ f) < (∞ : ℝ≥0∞) ∧
    fullEnergy s.1 (compactLocalizedMellinSchwartz σ f) ≤
      ENNReal.ofReal ((3 : ℝ)^(2+2*s.1)*(M+A+B))*fullEnergy s.1 f
  refine ⟨fullEnergy_lt_top s _,(fullEnergy_axes s _).trans ?_⟩
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),mul_assoc]
  apply mul_le_mul_right
  have hm := (hMb σ f).trans (mul_le_mul_right (mass_le_full s f) (ENNReal.ofReal M))
  refine (add_le_add (add_le_add hm (hAb σ f)) (hBb σ f)).trans_eq ?_
  rw [ENNReal.ofReal_add (add_pos hM hA).le hB.le,ENNReal.ofReal_add hM.le hA.le]
  ring

end GaloisForLFunctions.HTGeometry
