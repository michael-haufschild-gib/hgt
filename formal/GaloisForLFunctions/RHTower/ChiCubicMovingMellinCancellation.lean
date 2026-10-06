import GaloisForLFunctions.RHTower.ChiCubicMellinArithmeticPairing
import GaloisForLFunctions.RHTower.ChiCubicSelectedPhysicalConvergence
import GaloisForLFunctions.RHTower.ChiCubicMellinParameterContinuity

/-!
# Signed cancellation for the actual moving BAG Mellin profile

The complete growing labelled/cofactor arithmetic source, divided by log N,
pairs to zero with the literal selected moving Mellin profile. The critical
parameters are exactly 1 + rho_i / log N on their eventual admissible range.

Actual uniform localized Cauchy convergence and fixed-input parameter
continuity compare the moving test with one fixed late Schwartz test. The
complete source pairing bound pays the difference, the signed fixed-test
law pays the fixed test, and the entire actual exterior vanishes. Exact
native Fourier transport retains both 2*pi dilation Jacobians. No uniform
Schwartz budget or analytic cancellation hypothesis is assumed.

Identification with the full original sharp physical action, including
nonzero transverse defects, remains a separate mathematical obligation.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform Topology ENNReal ContDiff
namespace RHTower.BAGTrace
private abbrev E := HTGeometry.QuadrantLogSpace
private abbrev Q := {q : E // ∀i, q i∈Icc (1 : ℝ) 2}
private def κ : ℝ := 2*Real.pi
private theorem κ_pos : 0<κ := by dsimp only [κ]; positivity
private def coords : E≃ᵐℝ×ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2→ℝ)).symm.trans MeasurableEquiv.finTwoArrow
private theorem coords_preserving : MeasurePreserving coords :=
  (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
private def coordsLinear : E≃L[ℝ]ℝ×ℝ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
private def fixedSourceTest (G : SchwartzMap E ℂ) : SchwartzMap (ℝ×ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (((Units.mk0 κ κ_pos.ne')⁻¹) • coordsLinear.symm) G
private theorem fixedSourceTest_scaled (G : SchwartzMap E ℂ) (w : ℝ×ℝ) :
    fixedSourceTest G (κ • w)=G (coords.symm w) := by
  change G (κ⁻¹ • coordsLinear.symm (κ • w))=G (coords.symm w)
  rw [coordsLinear.symm.map_smul,smul_smul,inv_mul_cancel₀ κ_pos.ne',one_smul]
  rfl
private def bareSource (ρ₁ ρ₂ : {r : ℝ // 0<r}) (N : ℕ) (w : ℝ×ℝ) : ℂ :=
  criticalCompletedConeEuler (Sieve.primeSubtypeLE N)
    (1+(((ρ₁ : ℝ)/Real.log N : ℝ) : ℂ)+(w.1 : ℂ)*Complex.I)
    (1+(((ρ₂ : ℝ)/Real.log N : ℝ) : ℂ)+(w.2 : ℂ)*Complex.I)
private theorem fixed_pairing_identity (ρ₁ ρ₂ : {r : ℝ // 0<r})
    (N : ℕ) (G : SchwartzMap E ℂ) :
    (∫ξ : E,bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N ξ*G ξ)=
      (κ^2)⁻¹ • ((∫w : ℝ×ℝ,bareSource ρ₁ ρ₂ N w*fixedSourceTest G w)/(Real.log N : ℂ)) := by
  let H := fun w : ℝ×ℝ => bareSource ρ₁ ρ₂ N w*fixedSourceTest G w/(Real.log N : ℂ)
  have hp := coords_preserving.symm coords
  calc
    _ = ∫w : ℝ×ℝ,bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N (coords.symm w)*G (coords.symm w) :=
      (hp.integral_comp coords.symm.measurableEmbedding _).symm
    _ = ∫w : ℝ×ℝ,H (κ • w) := by
      apply integral_congr_ae
      filter_upwards with w
      change bareSource ρ₁ ρ₂ N (κ • w)/(Real.log N : ℂ)*G (coords.symm w)=
        bareSource ρ₁ ρ₂ N (κ • w)*fixedSourceTest G (κ • w)/(Real.log N : ℂ)
      rw [fixedSourceTest_scaled]
      ring
    _ = (κ^2)⁻¹ • ∫w : ℝ×ℝ,H w := by
      rw [Measure.integral_comp_smul]
      simp only [Module.finrank_prod,Module.finrank_self,Nat.reduceAdd,
        abs_of_nonneg (inv_nonneg.mpr (sq_nonneg κ))]
    _ = _ := by
      dsimp only [H]
      rw [integral_div]
private theorem fixed_source_pairing_tendsto (ρ₁ ρ₂ : {r : ℝ // 0<r})
    (G : SchwartzMap E ℂ) :
    (∀ᶠ N : ℕ in atTop,Integrable (fun ξ : E => bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N ξ*G ξ)) ∧
    Tendsto (fun N : ℕ => ∫ξ : E,bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N ξ*G ξ)
      atTop (𝓝 0) := by
  obtain ⟨_C,_hC,hAdmit⟩ := bagMellinNormalizedArithmeticSource_H2_pairing_bound ρ₁ ρ₂
  refine ⟨hAdmit.mono (fun N hN => (hN G).1),?_⟩
  have ht := criticalCompletedConeEuler_schwartz_integral_tendsto ρ₁ ρ₂ (fixedSourceTest G)
  change Tendsto (fun N : ℕ => (∫w : ℝ×ℝ,bareSource ρ₁ ρ₂ N w*fixedSourceTest G w)/(Real.log N : ℂ)) atTop (𝓝 0) at ht
  simp_rw [fixed_pairing_identity]
  simpa only [smul_zero] using ht.const_smul ((κ^2)⁻¹ : ℝ)

private def unitMellinParameter : Q := ⟨WithLp.toLp 2 (fun _ : Fin 2 => (1 : ℝ)),fun _ => by constructor <;> norm_num⟩
private def nativeMellinLine (ρ₁ ρ₂ : {r : ℝ // 0<r}) (N : ℕ) : E :=
  WithLp.toLp 2 (fun i : Fin 2 => 1+((![ρ₁,ρ₂] i : {r : ℝ // 0<r}) : ℝ)/Real.log N)

/-- The literal critical Mellin parameter vector on its eventual admissible
range, with a fixed admissible value outside that range. -/
def bagCriticalMellinParameter (ρ₁ ρ₂ : {r : ℝ // 0<r}) (N : ℕ) : Q := by
  classical
  exact if h : ∀i, nativeMellinLine ρ₁ ρ₂ N i∈Icc (1 : ℝ) 2 then
    ⟨nativeMellinLine ρ₁ ρ₂ N,h⟩ else unitMellinParameter

private theorem nativeMellinLine_tendsto (ρ₁ ρ₂ : {r : ℝ // 0<r}) :
    Tendsto (nativeMellinLine ρ₁ ρ₂) atTop (𝓝 unitMellinParameter.1) := by
  have hp : Tendsto (fun N : ℕ => fun i : Fin 2 =>
      1+((![ρ₁,ρ₂] i : {r : ℝ // 0<r}) : ℝ)/Real.log N)
      atTop (𝓝 (fun _ : Fin 2 => (1 : ℝ))) := by
    apply tendsto_pi_nhds.2
    intro i
    simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_drift_zero ((![ρ₁,ρ₂] i : {r : ℝ // 0<r}) : ℝ))
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).continuousAt.tendsto.comp hp

private theorem nativeMellinLine_admissible (ρ₁ ρ₂ : {r : ℝ // 0<r}) :
    ∀ᶠ N : ℕ in atTop,∀i, nativeMellinLine ρ₁ ρ₂ N i∈Icc (1 : ℝ) 2 := by
  apply eventually_all.2
  intro i
  let ρ : {r : ℝ // 0<r} := ![ρ₁,ρ₂] i
  have hh := (tendsto_drift_zero ρ.1).eventually (eventually_le_nhds (by norm_num : (0 : ℝ)<1))
  filter_upwards [hh,eventually_ge_atTop 2] with N hN hN2
  have hL : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hd : 0≤ρ.1/Real.log N := (div_pos ρ.2 hL).le
  change 1+ρ.1/Real.log N∈Icc (1 : ℝ) 2
  constructor <;> linarith

/-- Eventual identification with both exact critical logarithmic abscissas. -/
theorem bagCriticalMellinParameter_eventually_eq (ρ₁ ρ₂ : {r : ℝ // 0<r}) :
    ∀ᶠ N : ℕ in atTop,(bagCriticalMellinParameter ρ₁ ρ₂ N).1=
      WithLp.toLp 2 (fun i : Fin 2 => 1+((![ρ₁,ρ₂] i : {r : ℝ // 0<r}) : ℝ)/Real.log N) := by
  filter_upwards [nativeMellinLine_admissible ρ₁ ρ₂] with N hN
  simp only [bagCriticalMellinParameter,dif_pos hN]
  rfl

private theorem criticalMellinParameter_tendsto (ρ₁ ρ₂ : {r : ℝ // 0<r}) :
    Tendsto (bagCriticalMellinParameter ρ₁ ρ₂) atTop (𝓝 unitMellinParameter) := by
  apply tendsto_subtype_rng.2
  apply (nativeMellinLine_tendsto ρ₁ ρ₂).congr'
  exact (bagCriticalMellinParameter_eventually_eq ρ₁ ρ₂).mono (fun N hN => hN.symm)

private def movingEnergy (f : SchwartzMap E ℂ) : ℝ≥0∞ :=
  ∫⁻ξ : E,ENNReal.ofReal ((1+|ξ 0|+|ξ 1|)^(5/2 : ℝ)*‖(𝓕 f) ξ‖^2)
private theorem movingEnergy_add (f g : SchwartzMap E ℂ) :
    movingEnergy (f+g) ≤ 2*(movingEnergy f+movingEnergy g) := by
  have hf := (𝓕 f).continuous.measurable
  have hg := (𝓕 g).continuous.measurable
  have hm : Measurable (fun ξ : E => ENNReal.ofReal
      ((1+|ξ 0|+|ξ 1|)^(5/2 : ℝ)*‖(𝓕 f) ξ‖^2)) := by fun_prop
  have he : (∫⁻ ξ : E, (2 : ℝ≥0∞)*(ENNReal.ofReal
      ((1+|ξ 0|+|ξ 1|)^(5/2 : ℝ)*‖(𝓕 f) ξ‖^2)+ENNReal.ofReal
      ((1+|ξ 0|+|ξ 1|)^(5/2 : ℝ)*‖(𝓕 g) ξ‖^2)))=
        2*(movingEnergy f+movingEnergy g) := by
    rw [lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞)),lintegral_add_left hm]
    rfl
  rw [←he]
  apply lintegral_mono
  intro ξ
  have hw : 0 ≤ (1+|ξ 0|+|ξ 1|)^(5/2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hnorm : ‖(𝓕 f) ξ+(𝓕 g) ξ‖^2 ≤ 2*(‖(𝓕 f) ξ‖^2+‖(𝓕 g) ξ‖^2) := by
    have hb := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le ((𝓕 f) ξ) ((𝓕 g) ξ)) 2
    nlinarith [sq_nonneg (‖(𝓕 f) ξ‖-‖(𝓕 g) ξ‖)]
  change ENNReal.ofReal _ ≤ (2 : ℝ≥0∞)*(ENNReal.ofReal _+ENNReal.ofReal _)
  rw [FourierTransform.fourier_add,add_apply]
  rw [←ENNReal.ofReal_add (mul_nonneg hw (sq_nonneg _)) (mul_nonneg hw (sq_nonneg _))]
  have hp : (1+|ξ 0|+|ξ 1|)^(5/2 : ℝ)*‖(𝓕 f) ξ+(𝓕 g) ξ‖^2 ≤
      2*((1+|ξ 0|+|ξ 1|)^(5/2 : ℝ)*‖(𝓕 f) ξ‖^2+
        (1+|ξ 0|+|ξ 1|)^(5/2 : ℝ)*‖(𝓕 g) ξ‖^2) := by
    nlinarith only [mul_le_mul_of_nonneg_left hnorm hw]
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),ENNReal.ofReal_ofNat]
    using ENNReal.ofReal_le_ofReal hp

private theorem localized_sub (q : Q) (f g : SchwartzMap E ℂ) :
    GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q (f-g)=
      GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q f-
        GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q g := by
  ext u
  simp only [GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz_apply,
    GaloisForLFunctions.HTGeometry.compactLocalizedMellinProfile,sub_apply,mul_sub]
private def movingLocal (ρ₁ ρ₂ : {r : ℝ // 0<r}) (N : ℕ) : SchwartzMap E ℂ :=
  GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz
    (bagCriticalMellinParameter ρ₁ ρ₂ N) (bagCubicSelectedNormalizedCone N)

private theorem moving_local_approximation (ρ₁ ρ₂ : {r : ℝ // 0<r}) (ε : {r : ℝ // 0<r}) :
    ∃ R : ℝ, ∀ᶠ N : ℕ in atTop,
      movingEnergy (movingLocal ρ₁ ρ₂ N-
        GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz unitMellinParameter
          (bagCubicSelectedNormalizedCone R))≤ENNReal.ofReal ε.1 := by
  obtain ⟨R,hR⟩ := bagCubicSelectedNormalizedCone_uniform_local_mellin_cauchy
    ⟨1/4,by norm_num⟩ ⟨ε.1/4,by linarith [ε.2]⟩
  refine ⟨R,?_⟩
  have hp := (bagLocalizedMellin_parameter_energy_tendsto (bagCubicSelectedNormalizedCone R)
    unitMellinParameter ⟨5/4,by norm_num⟩).comp (criticalMellinParameter_tendsto ρ₁ ρ₂)
  have hp' : Tendsto (fun N : ℕ => movingEnergy
      (GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz (bagCriticalMellinParameter ρ₁ ρ₂ N)
        (bagCubicSelectedNormalizedCone R)-
       GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz unitMellinParameter
        (bagCubicSelectedNormalizedCone R))) atTop (𝓝 0) := by
    convert! hp using 1
    norm_num [movingEnergy,Function.comp_apply]
    rfl
  have hsmall := hp'.eventually (eventually_le_nhds
    (show (0 : ℝ≥0∞)<ENNReal.ofReal (ε.1/4) from ENNReal.ofReal_pos.2 (by linarith [ε.2])))
  filter_upwards [hsmall,(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop R] with N hP hN
  let q := bagCriticalMellinParameter ρ₁ ρ₂ N
  let A := GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q
    (bagCubicSelectedNormalizedCone N-bagCubicSelectedNormalizedCone R)
  let B := GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q (bagCubicSelectedNormalizedCone R)-
    GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz unitMellinParameter (bagCubicSelectedNormalizedCone R)
  have hA : movingEnergy A≤ENNReal.ofReal (ε.1/4) := by
    have hh := hR ⟨N,hN⟩ ⟨R,le_rfl⟩ q
    simpa only [movingEnergy,A,show (2 : ℝ)+2*(1/4 : ℝ)=5/2 by ring] using hh
  have hB : movingEnergy B≤ENNReal.ofReal (ε.1/4) := hP
  have he : movingLocal ρ₁ ρ₂ N-
      GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz unitMellinParameter
        (bagCubicSelectedNormalizedCone R)=A+B := by
    dsimp only [movingLocal,A,B,q]
    rw [localized_sub]
    abel
  rw [he]
  apply (movingEnergy_add A B).trans
  apply (mul_le_mul_right (add_le_add hA hB) (2 : ℝ≥0∞)).trans_eq
  have heps : 0≤ε.1/4 := by linarith [ε.2]
  rw [←ENNReal.ofReal_add heps heps]
  have hh : (2 : ℝ≥0∞)=ENNReal.ofReal (2 : ℝ) := by norm_num
  rw [hh,←ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2)]
  congr 1
  ring

private theorem movingEnergy_real_bound (f : SchwartzMap E ℂ) (ε : {r : ℝ // 0<r})
    (hb : movingEnergy f≤ENNReal.ofReal ε.1) :
    Integrable (fun ξ : E => (1+|ξ 0|+|ξ 1|)^(5/2 : ℝ)*‖(𝓕 f) ξ‖^2) ∧
    (∫ξ : E,(1+|ξ 0|+|ξ 1|)^(5/2 : ℝ)*‖(𝓕 f) ξ‖^2)≤ε.1 := by
  have hf := (𝓕 f).continuous.measurable
  have hm : Measurable (fun ξ : E => (1+|ξ 0|+|ξ 1|)^(5/2 : ℝ)*‖(𝓕 f) ξ‖^2) := by fun_prop
  have hpos : ∀ᵐξ : E ∂volume,0≤(1+|ξ 0|+|ξ 1|)^(5/2 : ℝ)*‖(𝓕 f) ξ‖^2 :=
    Eventually.of_forall (fun ξ => mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))
  have hi : Integrable (fun ξ : E => (1+|ξ 0|+|ξ 1|)^(5/2 : ℝ)*‖(𝓕 f) ξ‖^2) :=
    (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable hpos).1
      (ne_of_lt (lt_of_le_of_lt hb ENNReal.ofReal_lt_top))
  refine ⟨hi,?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff ε.2.le).1
  rw [ofReal_integral_eq_lintegral_ofReal hi hpos]
  exact hb

private theorem moving_local_integrable (ρ₁ ρ₂ : {r : ℝ // 0<r}) :
    ∀ᶠ N : ℕ in atTop,Integrable (fun ξ : E =>
      bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N ξ*(𝓕 (movingLocal ρ₁ ρ₂ N)) ξ) := by
  obtain ⟨_C,_hC,hb⟩ := bagMellinNormalizedArithmeticSource_H2_pairing_bound ρ₁ ρ₂
  filter_upwards [hb] with N hN
  exact (hN (𝓕 (movingLocal ρ₁ ρ₂ N))).1

private theorem moving_local_pairing_tendsto (ρ₁ ρ₂ : {r : ℝ // 0<r}) :
    Tendsto (fun N : ℕ => ∫ξ : E,
      bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N ξ*(𝓕 (movingLocal ρ₁ ρ₂ N)) ξ)
      atTop (𝓝 0) := by
  obtain ⟨C,hC,hCb⟩ := bagLocalizedMellin_difference_arithmetic_pairing_bound ρ₁ ρ₂
  apply Metric.tendsto_nhds.2
  intro ε hε
  let δ : {r : ℝ // 0<r} := ⟨(ε/(2*C))^2,sq_pos_of_pos (div_pos hε (mul_pos (by norm_num) hC))⟩
  obtain ⟨R,hR⟩ := moving_local_approximation ρ₁ ρ₂ δ
  let F := GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz unitMellinParameter
    (bagCubicSelectedNormalizedCone R)
  have hf := fixed_source_pairing_tendsto ρ₁ ρ₂ (𝓕 F)
  have hfn : Tendsto (fun N : ℕ => ‖∫ξ : E,
      bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N ξ*(𝓕 F) ξ‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using hf.2.norm
  have hsmall := hfn.eventually (Iio_mem_nhds (by linarith : (0 : ℝ)<ε/2))
  filter_upwards [hCb,hR,hf.1,hsmall] with N hN hR hFi hsmall
  let D := movingLocal ρ₁ ρ₂ N-F
  have hd := hN (bagCriticalMellinParameter ρ₁ ρ₂ N) unitMellinParameter
    (bagCubicSelectedNormalizedCone N) (bagCubicSelectedNormalizedCone R)
  have hE := (movingEnergy_real_bound D δ hR).2
  have hdsmall : ‖∫ξ : E,bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N ξ*(𝓕 D) ξ‖≤ε/2 := by
    calc
      _ ≤ C*Real.sqrt (∫ξ : E,(1+|ξ 0|+|ξ 1|)^(5/2 : ℝ)*‖(𝓕 D) ξ‖^2) := hd.2
      _ ≤ C*Real.sqrt δ.1 := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE) hC.le
      _ = ε/2 := by
        dsimp only [δ]
        rw [Real.sqrt_sq (div_nonneg hε.le (mul_pos (by norm_num) hC).le)]
        field_simp [hC.ne']
  have hG : 𝓕 (movingLocal ρ₁ ρ₂ N)=𝓕 D+𝓕 F := by
    rw [←FourierTransform.fourier_add]
    congr 1
    exact (sub_add_cancel (movingLocal ρ₁ ρ₂ N) F).symm
  have hi : (∫ξ : E,bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N ξ*(𝓕 (movingLocal ρ₁ ρ₂ N)) ξ)=
      (∫ξ : E,bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N ξ*(𝓕 D) ξ)+
        ∫ξ : E,bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N ξ*(𝓕 F) ξ := by
    simp only [hG,add_apply,mul_add]
    exact integral_add hd.1 hFi
  rw [dist_zero_right,hi]
  apply (norm_add_le _ _).trans_lt
  linarith

/-- Signed cancellation of the full arithmetic pairing with the literal
selected moving Mellin profile on its actual critical logarithmic lines.
Both growing cofactors and all labelled valuation sectors remain in the
source. The local test is controlled by actual Cauchy transfer and fixed-input
parameter continuity; the complete physical exterior is included. -/
theorem bagCubicSelectedMellin_arithmetic_pairing_tendsto
    (ρ₁ ρ₂ : {r : ℝ // 0<r}) :
    (∀ᶠ N : ℕ in atTop,Integrable (fun ξ : E =>
      bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N ξ*
        (𝓕 (bagCubicSelectedMellin (bagCriticalMellinParameter ρ₁ ρ₂ N) N)) ξ)) ∧
    Tendsto (fun N : ℕ => ∫ξ : E,
      bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N ξ*
        (𝓕 (bagCubicSelectedMellin (bagCriticalMellinParameter ρ₁ ρ₂ N) N)) ξ)
      atTop (𝓝 0) := by
  have hl := moving_local_pairing_tendsto ρ₁ ρ₂
  have he := bagCubicSelectedExteriorMellin_arithmetic_pairing_tendsto ρ₁ ρ₂
    (bagCriticalMellinParameter ρ₁ ρ₂)
  obtain ⟨_C,_hC,hExt⟩ := bagCubicSelectedExteriorMellin_arithmetic_pairing_decay ρ₁ ρ₂
  have hi : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ξ : E => bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N ξ*(𝓕 (movingLocal ρ₁ ρ₂ N)) ξ) ∧
      Integrable (fun ξ : E => bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N ξ*
        (𝓕 (bagCubicSelectedExteriorMellin (bagCriticalMellinParameter ρ₁ ρ₂ N) N)) ξ) := by
    filter_upwards [moving_local_integrable ρ₁ ρ₂,hExt] with N hl he
    exact ⟨hl,(he (bagCriticalMellinParameter ρ₁ ρ₂ N)).1⟩
  have hsplit (N : ℕ) (ξ : E) :
      bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N ξ*
        (𝓕 (bagCubicSelectedMellin (bagCriticalMellinParameter ρ₁ ρ₂ N) N)) ξ=
      bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N ξ*(𝓕 (movingLocal ρ₁ ρ₂ N)) ξ+
      bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N ξ*
        (𝓕 (bagCubicSelectedExteriorMellin (bagCriticalMellinParameter ρ₁ ρ₂ N) N)) ξ := by
    rw [bagCubicSelectedMellin_decomposition,FourierTransform.fourier_add,add_apply,mul_add]
    rfl
  constructor
  · filter_upwards [hi] with N hN
    exact (hN.1.add hN.2).congr (Eventually.of_forall (fun ξ => (hsplit N ξ).symm))
  · have hh := hl.add he
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [hi] with N hN
    rw [←integral_add hN.1 hN.2]
    apply integral_congr_ae
    exact Eventually.of_forall (fun ξ => (hsplit N ξ).symm)

end RHTower.BAGTrace
