import GaloisForLFunctions.RHTower.ModularLambdaOrbitSeparation
import GaloisForLFunctions.RHTower.ModularLambdaTestEnergy
import GaloisForLFunctions.HTGeometry.ModularFundamentalDomainMeasure
import GaloisForLFunctions.HTGeometry.UpperHalfPlaneStripIntegral
import GaloisForLFunctions.HTGeometry.ModularDirichletFormPeriodization

/-!
# The `Γ(2)`-cell Dirichlet energy of `log λ` grows linearly in the height

The hyperbolic Dirichlet density of `log λ` is `E(η) = Im(η)² |(log λ)'(η)|²` (`lambdaLogEnergy`).

* `E` is `Γ(2)`-invariant (`lambdaLogEnergy_smul`). From `log λ ∘ γ = log λ + 2πi w(γ)` one gets
  `(log λ)'(γη) = (cη + d)² (log λ)'(η)`, while `Im(γη) = Im η / |cη + d|²`.
* `∫_{𝒟 ∩ {Im ≤ T}} Σ_p E(h_p⁻¹ z) dμ(z) ≤ C T` for `T ≥ 1`, where `p` runs over
  `SL(2,ℤ)/Γ(2)` and `h_p` is a coset representative
  (`exists_lintegral_sum_lambdaLogEnergy_le`). The proof:
  - the boundary of `𝒟` is null and `μ` is `SL(2,ℤ)`-invariant;
  - `E dμ = |(log λ)'|² dx dy`;
  - the translates `h_p⁻¹ 𝒟ᵒ` are pairwise disjoint;
  - `λ` is injective on their union (degree one);
  - the height bound gives `|log |λ|| ≤ πT + C` there, so the substitution `w = λ(η)` bounds the
    energy by `∫ |w|⁻² dA` over an annulus of logarithmic width `2(πT + C)`.
-/

open Filter Topology Set UpperHalfPlane MeasureTheory CongruenceSubgroup
open scoped MatrixGroups Pointwise ENNReal

namespace GaloisForLFunctions.RHTower.ModularLambdaWinding

open Bottcher ModularGroup

noncomputable section

theorem continuousOn_deriv_lambdaLog : ContinuousOn (deriv lambdaLog) {τ : ℂ | 0 < τ.im} :=
  (differentiableOn_lambdaLog.deriv (isOpen_lt continuous_const Complex.continuous_im)).continuousOn

/-- The hyperbolic Dirichlet density of `log λ`: `Im(η)² |(log λ)'(η)|²`. -/
def lambdaLogEnergy (η : ℍ) : ℝ := η.im ^ 2 * ‖deriv lambdaLog (η : ℂ)‖ ^ 2

theorem lambdaLogEnergy_nonneg (η : ℍ) : 0 ≤ lambdaLogEnergy η := by
  unfold lambdaLogEnergy; positivity

theorem continuous_lambdaLogEnergy : Continuous lambdaLogEnergy :=
  (continuous_im.pow 2).mul
    ((continuousOn_deriv_lambdaLog.comp_continuous continuous_coe fun η => η.im_pos).norm.pow 2)

/-- **Chain rule for the `Γ(2)` cocycle.** For `γ ∈ Γ(2)`,
`(log λ)'(γη) · (cη + d)⁻² = (log λ)'(η)`: `log λ ∘ γ` and `log λ` differ by a constant. -/
theorem deriv_lambdaLog_smul_mul {g : SL(2, ℤ)} (hg : g ∈ Gamma 2) (η : ℍ) :
    deriv lambdaLog ((g • η : ℍ) : ℂ) *
        (1 / denom (Matrix.SpecialLinearGroup.mapGL ℝ g) η ^ 2) = deriv lambdaLog η := by
  set G : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ g with hG
  have hdet : G.val.det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hG, Matrix.SpecialLinearGroup.det_mapGL]; rfl
  set φ : ℂ → ℂ := fun z => ((G • ofComplex z : ℍ) : ℂ) with hφ
  have hφd : HasDerivAt φ (1 / denom G η ^ 2) η := by
    have h := (hasStrictDerivAt_smul (g := G) (by rw [hdet]; norm_num) η).hasDerivAt
    rwa [hdet, Complex.ofReal_one] at h
  have hφη : φ η = ((g • η : ℍ) : ℂ) := by simp only [hφ, ofComplex_apply]; rfl
  have hcomp : HasDerivAt (lambdaLog ∘ φ) (deriv lambdaLog (φ η) * (1 / denom G η ^ 2)) η :=
    (hasDerivAt_lambdaLog (τ := φ η) (by rw [hφη]; exact (g • η).im_pos)).comp (η : ℂ) hφd
  set c : ℂ := 2 * Real.pi * Complex.I *
    ((Multiplicative.toAdd (HTGeometry.gammaTwoWinding ⟨g, hg⟩) : ℤ) : ℂ) with hc
  have heq : (lambdaLog ∘ φ) =ᶠ[𝓝 (η : ℂ)] fun z => lambdaLog z + c := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds η.im_pos] with z hz
    simp only [Function.comp_apply, hφ, ofComplex_apply_of_im_pos (show 0 < z.im from hz)]
    exact lambdaLog_smul hg ⟨z, hz⟩
  have hlin : HasDerivAt (lambdaLog ∘ φ) (deriv lambdaLog η) η :=
    ((hasDerivAt_lambdaLog η.im_pos).add_const c).congr_of_eventuallyEq heq
  rw [← hφη]
  exact hcomp.unique hlin

/-- **`Γ(2)`-invariance of the energy density.** -/
theorem lambdaLogEnergy_smul {g : SL(2, ℤ)} (hg : g ∈ Gamma 2) (η : ℍ) :
    lambdaLogEnergy (g • η) = lambdaLogEnergy η := by
  set G : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ g with hG
  have hdet : G.val.det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hG, Matrix.SpecialLinearGroup.det_mapGL]; rfl
  have hd0 : denom G η ≠ 0 := denom_ne_zero G η
  have hd : ‖denom G η‖ ≠ 0 := norm_ne_zero_iff.2 hd0
  have him : (g • η).im = η.im / ‖denom G η‖ ^ 2 := by
    have h := UpperHalfPlane.im_smul_eq_div_normSq G η
    rw [Matrix.GeneralLinearGroup.val_det_apply, hdet] at h
    rw [show g • η = G • η from rfl, h, Complex.normSq_eq_norm_sq]; simp
  have hder : deriv lambdaLog ((g • η : ℍ) : ℂ) = deriv lambdaLog η * denom G η ^ 2 := by
    have h := deriv_lambdaLog_smul_mul hg η
    rw [← hG] at h
    rw [← h]; field_simp
  unfold lambdaLogEnergy
  rw [him, hder, norm_mul, norm_pow]
  field_simp

/-- **Hyperbolic integrals as Lebesgue integrals.** For measurable `S ⊆ ℍ`,
`∫_S F dμ = ∫_{S ⊆ ℂ} y⁻² F dx dy`. -/
theorem setLIntegral_upperHalfPlane_eq {S : Set ℍ} (hS : MeasurableSet S) (F : ℍ → ℝ≥0∞) :
    ∫⁻ η in S, F η = ∫⁻ x in UpperHalfPlane.coe '' S,
      HTGeometry.hyperbolicDensity (ofComplex x) * F (ofComplex x) := by
  rw [HTGeometry.volume_eq_comap_withDensity, restrict_withDensity hS,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ HTGeometry.measurable_hyperbolicDensity
      (ae_of_all _ fun z => HTGeometry.hyperbolicDensity_lt_top z)]
  have h2 := HTGeometry.measurePreserving_coe.setLIntegral_comp_emb measurableEmbedding_coe
    (fun x => HTGeometry.hyperbolicDensity (ofComplex x) * F (ofComplex x)) S
  simp only [ofComplex_apply] at h2
  rw [Measure.restrict_restrict (measurableEmbedding_coe.measurableSet_image.2 hS),
    inter_eq_self_of_subset_left (image_subset_range _ _)] at h2
  exact h2

/-- `E dμ = |(log λ)'|² dx dy`. -/
theorem setLIntegral_lambdaLogEnergy_eq {S : Set ℍ} (hS : MeasurableSet S) :
    ∫⁻ η in S, ENNReal.ofReal (lambdaLogEnergy η) =
      ∫⁻ x in UpperHalfPlane.coe '' S, ENNReal.ofReal (‖deriv lambdaLog x‖ ^ 2) := by
  rw [setLIntegral_upperHalfPlane_eq hS]
  refine setLIntegral_congr_fun (measurableEmbedding_coe.measurableSet_image.2 hS) ?_
  rintro _ ⟨η, -, rfl⟩
  have him : η.im ≠ 0 := η.im_pos.ne'
  show HTGeometry.hyperbolicDensity (ofComplex (η : ℂ)) *
      ENNReal.ofReal (lambdaLogEnergy (ofComplex (η : ℂ))) = ENNReal.ofReal (‖deriv lambdaLog (η : ℂ)‖ ^ 2)
  rw [ofComplex_apply, HTGeometry.hyperbolicDensity, lambdaLogEnergy,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

theorem measurableSet_fdo : MeasurableSet ModularGroup.fdo := by
  have h1 : IsOpen {z : ℍ | 1 < Complex.normSq (z : ℂ)} :=
    isOpen_lt continuous_const (Complex.continuous_normSq.comp continuous_coe)
  have h2 : IsOpen {z : ℍ | |z.re| < 1 / 2} := isOpen_lt (continuous_abs.comp continuous_re)
    continuous_const
  exact (h1.inter h2).measurableSet

/-- Two translates `h_p⁻¹ z₁`, `h_q⁻¹ z₂` of points of `𝒟ᵒ` coincide only for `p = q`: the element
`h_p h_q⁻¹` maps `z₂ ∈ 𝒟ᵒ` into `𝒟ᵒ`, so it is `±1 ∈ Γ(2)`. -/
theorem eq_of_cosetRep_inv_smul_eq {p q : SL(2, ℤ) ⧸ Gamma 2} {z₁ z₂ : ℍ}
    (hz₁ : z₁ ∈ ModularGroup.fdo) (hz₂ : z₂ ∈ ModularGroup.fdo)
    (h : (Quotient.out p)⁻¹ • z₁ = (Quotient.out q)⁻¹ • z₂) : p = q := by
  have hz : (Quotient.out p * (Quotient.out q)⁻¹) • z₂ = z₁ := by
    rw [mul_smul, ← h, smul_inv_smul]
  have hmem : (Quotient.out p)⁻¹ * Quotient.out q ∈ Gamma 2 := by
    rcases ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fdo hz₂ (hz ▸ hz₁) with h1 | h1
    · rw [mul_inv_eq_one] at h1
      rw [h1, inv_mul_cancel]; exact one_mem _
    · rw [mul_inv_eq_iff_eq_mul] at h1
      have hq : Quotient.out q = -Quotient.out p := by rw [h1]; simp
      rw [hq, mul_neg, inv_mul_cancel]; exact negI_mem_gamma2
  rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q]
  exact QuotientGroup.eq.2 hmem

theorem pairwise_disjoint_cosetRep_inv_smul_fdo :
    Pairwise (Function.onFun Disjoint fun p : SL(2, ℤ) ⧸ Gamma 2 =>
      (Quotient.out p)⁻¹ • ModularGroup.fdo) := by
  intro p q hpq
  rw [Function.onFun, Set.disjoint_left]
  rintro x ⟨z₁, hz₁, rfl⟩ ⟨z₂, hz₂, hx⟩
  exact hpq (eq_of_cosetRep_inv_smul_eq hz₁ hz₂ hx.symm)

/-- **The `Γ(2)`-cell energy of `log λ` grows linearly in the height.** With `h_p` a representative
of `p ∈ SL(2,ℤ)/Γ(2)`, `∫_{𝒟 ∩ {Im ≤ T}} Σ_p Im(h_p⁻¹z)² |(log λ)'(h_p⁻¹z)|² dμ(z) ≤ C T`. -/
theorem exists_lintegral_sum_lambdaLogEnergy_le [Fintype (SL(2, ℤ) ⧸ Gamma 2)] :
    ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T →
      ∫⁻ z in ModularGroup.fd ∩ {z : ℍ | z.im ≤ T},
          ∑ p : SL(2, ℤ) ⧸ Gamma 2, ENNReal.ofReal (lambdaLogEnergy ((Quotient.out p)⁻¹ • z)) ≤
        ENNReal.ofReal (C * T) := by
  obtain ⟨C₀, hC₀⟩ := exists_abs_log_norm_modularLambda_smul_le
  refine ⟨4 * Real.pi * (Real.pi + |C₀|), fun T hT => ?_⟩
  set A : Set ℍ := {z : ℍ | z.im ≤ T} with hA
  have hAm : MeasurableSet A := measurableSet_le continuous_im.measurable measurable_const
  set s := ModularGroup.fdo ∩ A with hs
  have hsm : MeasurableSet s := measurableSet_fdo.inter hAm
  have hae : (ModularGroup.fd ∩ A : Set ℍ) =ᵐ[volume] s := by
    rw [ae_eq_set]
    refine ⟨measure_mono_null (show (ModularGroup.fd ∩ A) \ s ⊆ ModularGroup.fd \ ModularGroup.fdo from
      fun z hz => ⟨hz.1.1, fun h => hz.2 ⟨h, hz.1.2⟩⟩) HTGeometry.volume_fd_diff_fdo, ?_⟩
    rw [Set.sdiff_eq_empty.2 (inter_subset_inter_left _ ModularGroup.fdo_subset_fd)]
    exact measure_empty
  rw [setLIntegral_congr hae]
  have hmeas : ∀ p : SL(2, ℤ) ⧸ Gamma 2,
      Measurable fun z : ℍ => ENNReal.ofReal (lambdaLogEnergy ((Quotient.out p)⁻¹ • z)) := fun p =>
    ENNReal.measurable_ofReal.comp
      (continuous_lambdaLogEnergy.comp (HTGeometry.continuous_modular_smul _)).measurable
  rw [lintegral_finsetSum _ fun p _ => hmeas p]
  set U : SL(2, ℤ) ⧸ Gamma 2 → Set ℂ := fun p => UpperHalfPlane.coe '' ((Quotient.out p)⁻¹ • s)
    with hU
  have hterm : ∀ p : SL(2, ℤ) ⧸ Gamma 2,
      ∫⁻ z in s, ENNReal.ofReal (lambdaLogEnergy ((Quotient.out p)⁻¹ • z)) =
        ∫⁻ x in U p, ENNReal.ofReal (‖deriv lambdaLog x‖ ^ 2) := fun p => by
    rw [← setLIntegral_lambdaLogEnergy_eq (hsm.const_smul _), ← Set.image_smul]
    exact (measurePreserving_smul (Quotient.out p)⁻¹ volume).setLIntegral_comp_emb
      (measurableEmbedding_const_smul _) (fun η => ENNReal.ofReal (lambdaLogEnergy η)) s
  have hUm : ∀ p, MeasurableSet (U p) := fun p =>
    measurableEmbedding_coe.measurableSet_image.2 (hsm.const_smul _)
  have hUd : Pairwise (Function.onFun Disjoint U) := fun p q hpq =>
    (Set.disjoint_image_iff UpperHalfPlane.coe_injective).2
      ((pairwise_disjoint_cosetRep_inv_smul_fdo hpq).mono
        (smul_set_mono inter_subset_left) (smul_set_mono inter_subset_left))
  have hsum : ∫⁻ x in ⋃ p, U p, ENNReal.ofReal (‖deriv lambdaLog x‖ ^ 2) =
      ∑ p, ∫⁻ x in U p, ENNReal.ofReal (‖deriv lambdaLog x‖ ^ 2) := by
    rw [lintegral_iUnion hUm hUd, tsum_fintype]
  rw [Finset.sum_congr rfl fun p _ => hterm p, ← hsum]
  set D := ⋃ p, U p with hD
  have hDm : MeasurableSet D := MeasurableSet.iUnion hUm
  have hmemD : ∀ x ∈ D, ∃ p : SL(2, ℤ) ⧸ Gamma 2, ∃ z ∈ s, x = (((Quotient.out p)⁻¹ • z : ℍ) : ℂ) := by
    intro x hx
    obtain ⟨p, ⟨η, ⟨z, hz, rfl⟩, rfl⟩⟩ := mem_iUnion.1 hx
    exact ⟨p, z, hz, rfl⟩
  have hDH : D ⊆ {τ : ℂ | 0 < τ.im} := fun x hx => by
    obtain ⟨p, z, -, rfl⟩ := hmemD x hx
    exact ((Quotient.out p)⁻¹ • z).im_pos
  have hDinj : InjOn modularLambda D := injOn_modularLambda_coe_gamma2Fdo.mono fun x hx => by
    obtain ⟨p, z, hz, rfl⟩ := hmemD x hx
    exact ⟨_, mem_iUnion.2 ⟨p, smul_mem_smul_set hz.1⟩, rfl⟩
  set M := Real.pi * T + C₀ with hM
  have hDlog : ∀ x ∈ D, Real.log ‖modularLambda x‖ ∈ Icc (-M) M := fun x hx => by
    obtain ⟨p, z, hz, rfl⟩ := hmemD x hx
    have h := hC₀ z (ModularGroup.fdo_subset_fd hz.1) (Quotient.out p)⁻¹
    have hzT : z.im ≤ T := hz.2
    have := mul_le_mul_of_nonneg_left hzT Real.pi_pos.le
    exact abs_le.1 (h.trans (by linarith))
  set G : ℝ → ℝ := (Icc (-M) M).indicator fun _ => 1 with hGdef
  have hG : Measurable G := measurable_const.indicator measurableSet_Icc
  have hcongr : ∫⁻ x in D, ENNReal.ofReal (‖deriv lambdaLog x‖ ^ 2) =
      ∫⁻ x in D, ENNReal.ofReal (‖deriv lambdaLog x‖ ^ 2 * G (lambdaLog x).re) :=
    setLIntegral_congr_fun hDm fun x hx => by
      rw [hGdef, re_lambdaLog_eq (hDH hx), indicator_of_mem (hDlog x hx), mul_one]
  have hGint : ∫⁻ t : ℝ, ENNReal.ofReal (G t) = ENNReal.ofReal (2 * M) := by
    have h : (fun t => ENNReal.ofReal (G t)) = (Icc (-M) M).indicator 1 := funext fun t => by
      simp only [hGdef, indicator]
      split_ifs <;> simp
    rw [h, lintegral_indicator_one measurableSet_Icc, Real.volume_Icc]
    congr 1; ring
  rw [hcongr]
  refine (lintegral_dirichletDensity_le hDm hDH hDinj hG).trans ?_
  rw [hGint, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hC : C₀ ≤ |C₀| * T := (le_abs_self C₀).trans (le_mul_of_one_le_right (abs_nonneg _) hT)
  have hπ := Real.pi_pos
  nlinarith

end

end GaloisForLFunctions.RHTower.ModularLambdaWinding
