import GaloisForLFunctions.RHTower.ChiCubicSelectedKernelConvergence
import GaloisForLFunctions.RHTower.ChiCubicSelectedLocalMellinEnergy

/-!
# Strong Cauchy control of the actual selected BAG physical profiles

The exact ordinary Fourier transform of the normalized selected cone is
`2*pi` times the reciprocal kernel at the two dilated frequencies. The
squared amplitude cancels both dilation Jacobians. Comparing two actual
kernels through the common sharp reciprocal kernel therefore transfers the
proved weighted strong convergence to physical Sobolev Cauchy control at
every order below three halves.

The complete localized Mellin operator then transfers this control uniformly
over its parameter square. This result uses differences of actual Schwartz
inputs and does not assume that their limiting physical profile is Schwartz.
Variation of the Mellin parameter for a fixed input is a separate step.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform Topology ENNReal ContDiff BigOperators
namespace RHTower.BAGTrace
private abbrev E := HTGeometry.QuadrantLogSpace

private def coords : E≃ᵐℝ×ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2→ℝ)).symm.trans MeasurableEquiv.finTwoArrow

private theorem coords_preserving : MeasurePreserving coords :=
  (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

private theorem lintegral_two (F : E→ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ u : E, F u)=∫⁻ a : ℝ, ∫⁻ b : ℝ, F (WithLp.toLp 2 ![a,b]) := by
  have hp := coords_preserving.symm coords
  rw [←hp.lintegral_comp_emb coords.symm.measurableEmbedding F]
  exact lintegral_prod _ (hF.comp coords.symm.measurable).aemeasurable

private theorem scaled_lintegral (c : ℝ) (hc : 0<c) (F : ℝ→ℝ≥0∞) :
    (∫⁻ x : ℝ, ENNReal.ofReal c*F (c*x))=∫⁻ x : ℝ, F x := by
  have hd : ∀x∈(univ : Set ℝ), HasDerivWithinAt (fun t : ℝ => c*t) c univ x := by
    intro x _
    simpa only [mul_one] using! ((hasDerivAt_id x).const_mul c).hasDerivWithinAt
  have hinj : InjOn (fun x : ℝ => c*x) univ := by
    intro x _ y _ hh
    exact mul_left_cancel₀ hc.ne' hh
  have himage : (fun x : ℝ => c*x) '' univ=univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      refine ⟨y/c,mem_univ _,?_⟩
      field_simp
  have hh := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ hd hinj F
  rw [himage,Measure.restrict_univ] at hh
  simpa only [abs_of_pos hc] using hh.symm

private theorem scaled_lintegral_two (c : ℝ) (hc : 0<c) (F : ℝ→ℝ→ℝ≥0∞) :
    (∫⁻ a : ℝ, ∫⁻ b : ℝ, ENNReal.ofReal (c^2)*F (c*a) (c*b))=
      ∫⁻ a : ℝ, ∫⁻ b : ℝ, F a b := by
  have he (a : ℝ) : (∫⁻ b : ℝ, ENNReal.ofReal (c^2)*F (c*a) (c*b))=
      ENNReal.ofReal c*∫⁻ b : ℝ, F (c*a) b := by
    rw [pow_two,ENNReal.ofReal_mul hc.le]
    simp only [mul_assoc]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,scaled_lintegral c hc]
  simp_rw [he]
  exact scaled_lintegral c hc (fun a => ∫⁻ b : ℝ, F a b)


private theorem selected_width_ratio (N : ℝ) (hN : 0<N) :
    N^(1/4 : ℝ)/N=N^(-(3/4 : ℝ)) := by
  rw [div_eq_mul_inv,←Real.rpow_neg_one,←Real.rpow_add hN]
  congr 1
  norm_num

private theorem selected_admissible : ∀ᶠ N : ℝ in atTop, 1<N ∧ N^(1/4 : ℝ)<N/2 := by
  have hd := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<3/4)
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    hd.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ)<1/2))] with N hN hdN
  refine ⟨hN,?_⟩
  have hN0 : 0<N := zero_lt_one.trans hN
  have hh : N^(1/4 : ℝ)/N < (1/2 : ℝ) := by rw [selected_width_ratio N hN0]; exact hdN
  have ht := (div_lt_iff₀ hN0).mp hh
  linarith


private def selectedReciprocal (N a b : ℝ) : ℂ :=
  bagCubicReciprocalKernel (N^(-(3/4 : ℝ))) (1/Real.log N) a b (((1/(2*Real.pi))/N)*a*b)
private def errorEnergy (s N : ℝ) (ab : ℝ×ℝ) : ℝ :=
  (1+|ab.1|+|ab.2|)^(2*s)*‖selectedReciprocal N ab.1 ab.2-bagCubicSharpReciprocalKernel ab.1 ab.2‖^2
private theorem errorEnergy_nonneg (s N : ℝ) (ab : ℝ×ℝ) : 0≤errorEnergy s N ab := by
  dsimp only [errorEnergy]
  positivity
private theorem selected_fourier :
    ∀ᶠ N : ℝ in atTop, ∀a b : ℝ,
      (𝓕 (bagCubicSelectedNormalizedCone N)) (WithLp.toLp 2 ![a,b])=
        (2*Real.pi : ℂ)*selectedReciprocal N (2*Real.pi*a) (2*Real.pi*b) := by
  filter_upwards [selected_admissible] with N hN
  intro a b
  rw [bagCubicSelectedNormalizedCone,dif_pos hN,bagCubicNormalizedConeSchwartz_fourier]
  simp only [selectedReciprocal,selected_width_ratio N (zero_lt_one.trans hN.1)]

private theorem comparison_energy (p : ℝ) (f : SchwartzMap E ℂ) (J : ℝ×ℝ→ℝ)
    (hJ : Integrable J) (hJ0 : ∀z,0≤J z)
    (hpoint : ∀a b : ℝ, (1+|a|+|b|)^p*‖(𝓕 f) (WithLp.toLp 2 ![a,b])‖^2 ≤
      (2*Real.pi)^2*J (2*Real.pi*a,2*Real.pi*b)) :
    (∫⁻ξ : E,ENNReal.ofReal ((1+|ξ 0|+|ξ 1|)^p*‖(𝓕 f) ξ‖^2)) ≤
      ENNReal.ofReal (∫ab : ℝ×ℝ,J ab) := by
  let c := 2*Real.pi
  have hc : 0<c := by dsimp only [c]; positivity
  have hf := (𝓕 f).continuous.measurable
  rw [lintegral_two _ (by fun_prop)]
  have hh (a b : ℝ) : ENNReal.ofReal ((1+|a|+|b|)^p*‖(𝓕 f) (WithLp.toLp 2 ![a,b])‖^2) ≤
      ENNReal.ofReal (c^2)*ENNReal.ofReal (J (c*a,c*b)) := by
    rw [←ENNReal.ofReal_mul (sq_nonneg c)]
    exact ENNReal.ofReal_le_ofReal (hpoint a b)
  change (∫⁻a : ℝ,∫⁻b : ℝ,ENNReal.ofReal ((1+|a|+|b|)^p*‖(𝓕 f) (WithLp.toLp 2 ![a,b])‖^2)) ≤ _
  apply (lintegral_mono (fun a => lintegral_mono (hh a))).trans_eq
  rw [scaled_lintegral_two c hc (fun a b => ENNReal.ofReal (J (a,b)))]
  rw [ofReal_integral_eq_lintegral_ofReal hJ (Eventually.of_forall hJ0)]
  exact (lintegral_prod _ (ENNReal.measurable_ofReal.comp_aemeasurable hJ.aestronglyMeasurable.aemeasurable)).symm

private theorem complex_sub_square (a b c : ℂ) :
    ‖a-b‖^2≤2*(‖a-c‖^2+‖b-c‖^2) := by
  have he : a-b=(a-c)-(b-c) := by ring
  rw [he]
  have hb := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (a-c) (b-c)) 2
  nlinarith [sq_nonneg (‖a-c‖-‖b-c‖)]

private theorem selected_difference_point (s : {r : ℝ // r∈Ico (0 : ℝ) (3/2)})
    (N M : ℝ)
    (hN : ∀a b : ℝ,(𝓕 (bagCubicSelectedNormalizedCone N)) (WithLp.toLp 2 ![a,b])=
      (2*Real.pi : ℂ)*selectedReciprocal N (2*Real.pi*a) (2*Real.pi*b))
    (hM : ∀a b : ℝ,(𝓕 (bagCubicSelectedNormalizedCone M)) (WithLp.toLp 2 ![a,b])=
      (2*Real.pi : ℂ)*selectedReciprocal M (2*Real.pi*a) (2*Real.pi*b)) (a b : ℝ) :
    (1+|a|+|b|)^(2*s.1)*‖(𝓕 (bagCubicSelectedNormalizedCone N-bagCubicSelectedNormalizedCone M))
      (WithLp.toLp 2 ![a,b])‖^2 ≤
    (2*Real.pi)^2*(2*(errorEnergy s.1 N (2*Real.pi*a,2*Real.pi*b)+
      errorEnergy s.1 M (2*Real.pi*a,2*Real.pi*b))) := by
  let c := 2*Real.pi
  have hc : 0<c := by dsimp only [c]; positivity
  have hc1 : 1≤c := by dsimp only [c]; linarith [Real.pi_gt_three]
  have hcn : ‖(2*Real.pi : ℂ)‖=c := by dsimp only [c]; simp [Complex.norm_real,abs_of_pos Real.pi_pos]
  have hF : 𝓕 (bagCubicSelectedNormalizedCone N-bagCubicSelectedNormalizedCone M)=
      𝓕 (bagCubicSelectedNormalizedCone N)-𝓕 (bagCubicSelectedNormalizedCone M) := by
    simpa only [FourierTransform.fourierEquiv_apply] using
      map_sub (FourierTransform.fourierEquiv ℂ (SchwartzMap E ℂ))
        (bagCubicSelectedNormalizedCone N) (bagCubicSelectedNormalizedCone M)
  rw [hF,sub_apply,hN,hM,←mul_sub,norm_mul,mul_pow,hcn]
  have hw : (1+|a|+|b|)^(2*s.1) ≤ (1+|c*a|+|c*b|)^(2*s.1) := by
    apply Real.rpow_le_rpow (by positivity) _ (by linarith [s.2.1])
    rw [abs_mul c a,abs_mul c b,abs_of_pos hc]
    nlinarith [abs_nonneg a,abs_nonneg b]
  have hd := complex_sub_square (selectedReciprocal N (c*a) (c*b))
    (selectedReciprocal M (c*a) (c*b)) (bagCubicSharpReciprocalKernel (c*a) (c*b))
  have hprod := mul_le_mul hw (mul_le_mul_of_nonneg_left hd (sq_nonneg c))
    (mul_nonneg (sq_nonneg c) (sq_nonneg _)) (by positivity : 0≤(1+|c*a|+|c*b|)^(2*s.1))
  apply hprod.trans_eq
  dsimp only [errorEnergy,c]
  ring


/-- The literal selected normalized physical cone family is strongly Cauchy in
every Fourier Sobolev energy below order three halves. The common sharp
reciprocal kernel is used only as a comparison center; no Schwartz limit is
assumed or identified. -/
theorem bagCubicSelectedNormalizedCone_energy_cauchy
    (s : {r : ℝ // r∈Ico (0 : ℝ) (3/2)}) (ε : {r : ℝ // 0<r}) :
    ∃ R : ℝ, ∀N M : {r : ℝ // R≤r},
      (∫⁻ξ : E,ENNReal.ofReal ((1+|ξ 0|+|ξ 1|)^(2*s.1)*
        ‖(𝓕 (bagCubicSelectedNormalizedCone N.1-bagCubicSelectedNormalizedCone M.1)) ξ‖^2)) ≤
          ENNReal.ofReal ε.1 := by
  let tau : {r : ℝ // 0<r} := ⟨1/(2*Real.pi),by positivity⟩
  have hb := bagCubicReciprocalKernel_selected_energy_tendsto s tau
  have hi : ∀ᶠ N : ℝ in atTop, Integrable (errorEnergy s.1 N) := hb.2.1
  have ht : Tendsto (fun N : ℝ => ∫ab : ℝ×ℝ,errorEnergy s.1 N ab) atTop (𝓝 0) := hb.2.2
  have he : ∀ᶠ N : ℝ in atTop,(∫ab : ℝ×ℝ,errorEnergy s.1 N ab)≤ε.1/4 :=
    ht.eventually (eventually_le_nhds (by linarith [ε.2] : (0 : ℝ)<ε.1/4))
  obtain ⟨R,hR⟩ := eventually_atTop.1 (selected_fourier.and (hi.and he))
  refine ⟨R,?_⟩
  intro N M
  have hN := hR N.1 N.2
  have hM := hR M.1 M.2
  let J := fun ab : ℝ×ℝ => 2*(errorEnergy s.1 N.1 ab+errorEnergy s.1 M.1 ab)
  have hJi : Integrable J := (hN.2.1.add hM.2.1).const_mul 2
  have hJ0 (ab : ℝ×ℝ) : 0≤J ab := by
    dsimp only [J]
    exact mul_nonneg (by norm_num) (add_nonneg (errorEnergy_nonneg s.1 N.1 ab) (errorEnergy_nonneg s.1 M.1 ab))
  have hc := comparison_energy (2*s.1)
    (bagCubicSelectedNormalizedCone N.1-bagCubicSelectedNormalizedCone M.1) J hJi hJ0
    (selected_difference_point s N.1 M.1 hN.1 hM.1)
  apply hc.trans
  apply ENNReal.ofReal_le_ofReal
  change (∫ab : ℝ×ℝ,2*(errorEnergy s.1 N.1 ab+errorEnergy s.1 M.1 ab))≤ε.1
  rw [integral_const_mul,integral_add hN.2.1 hM.2.1]
  linarith [hN.2.2,hM.2.2]

/-- Strong Cauchy transfer of the actual physical inputs through the complete
localized Mellin operator, uniformly over the entire moving-parameter square. -/
theorem bagCubicSelectedNormalizedCone_uniform_local_mellin_cauchy
    (s : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (ε : {r : ℝ // 0<r}) :
    ∃ R : ℝ, ∀N M : {r : ℝ // R≤r},
      ∀q : {q : E // ∀i, q i∈Icc (1 : ℝ) 2},
        (∫⁻ξ : E,ENNReal.ofReal ((1+|ξ 0|+|ξ 1|)^(2+2*s.1)*
          ‖(𝓕 (GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q
            (bagCubicSelectedNormalizedCone N.1-bagCubicSelectedNormalizedCone M.1))) ξ‖^2)) ≤
              ENNReal.ofReal ε.1 := by
  obtain ⟨A,hA,hAb⟩ := GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz_uniform_energy
    ⟨s.1,s.2.1,by linarith [s.2.2]⟩
  obtain ⟨R,hR⟩ := bagCubicSelectedNormalizedCone_energy_cauchy
    ⟨1+s.1,by constructor <;> linarith [s.2.1,s.2.2]⟩ ⟨ε.1/A,div_pos ε.2 hA⟩
  refine ⟨R,?_⟩
  intro N M q
  have hc := hR N M
  have hexp : 2*(1+s.1)=2+2*s.1 := by ring
  simp only [hexp] at hc
  have hb := (hAb q (bagCubicSelectedNormalizedCone N.1-bagCubicSelectedNormalizedCone M.1)).2
  apply hb.trans
  have hh := mul_le_mul_right hc (ENNReal.ofReal A)
  apply hh.trans_eq
  rw [←ENNReal.ofReal_mul hA.le]
  congr 1
  field_simp [hA.ne']

end RHTower.BAGTrace