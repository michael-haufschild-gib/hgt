import GaloisForLFunctions.RHTower.WeilConeXiDivisibleBlindTest
import GaloisForLFunctions.RHTower.WeilWorkExposingRayPrimitiveSharpness
import Zeta23.Taper.Decay

/-! Fourier mass and archimedean integrability for the existing exponential
test class, without a compact-support assumption. -/

open MeasureTheory Set Filter
open scoped Topology
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower _root_.RHTower.WeilSpectral _root_.Zeta23
noncomputable section
set_option autoImplicit false

theorem expDecayTest_integrable {F : ℝ → ℝ} (hF : ExpDecayTest F) : Integrable F := by
  refine (integrable_tailMajorant hF (Λ := 0) le_rfl).mono'
    hF.1.continuous.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  unfold tailMajorant
  calc
    |F x| ≤ |F x|+2*(|deriv F x|+2*0*|F x|) := le_add_of_nonneg_right (by positivity)
    _ ≤ _ := le_mul_of_one_le_right (by positivity)
      (Real.one_le_exp_iff.mpr (by positivity))

theorem expDecayTest_exists_fourier_bound {F : ℝ → ℝ} (hF : ExpDecayTest F) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ L r : ℝ, ‖paperFT (fun x => (truncTest F L x : ℂ)) (r : ℂ)‖ ≤ M/(1+|r|)) ∧
      ∀ r : ℝ, ‖paperFT (fun x => (F x : ℂ)) (r : ℂ)‖ ≤ M/(1+|r|) := by
  obtain ⟨Λ,hΛ0,hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  let M := ∫ x : ℝ, tailMajorant F Λ x
  have hM : 0 ≤ M := integral_nonneg fun x => tailMajorant_nonneg F hΛ0 x
  have hb (L r : ℝ) : ‖paperFT (fun x => (truncTest F L x : ℂ)) (r : ℂ)‖ ≤ M/(1+|r|) := by
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact one_add_abs_mul_norm_paperFT_truncTest_le hF hΛ hΛ0 L r
  refine ⟨M,hM,hb,fun r => ?_⟩
  exact le_of_tendsto (tendsto_paperFT_truncTest hF (z := (r : ℂ)) (by simp)).norm
    (Eventually.of_forall fun L => hb L r)

private theorem sq_fourier_bound {f : ℝ → ℂ} {M : ℝ} {r : ℝ}
    (hb : ‖paperFT f (r : ℂ)‖ ≤ M/(1+|r|)) :
    ‖paperFT f (r : ℂ)‖^2 ≤ M^2*(1+‖r‖)^(-(2 : ℝ)) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [Real.norm_eq_abs, Real.rpow_neg (by positivity : 0 ≤ 1+|r|),
    Real.rpow_two, ← div_eq_mul_inv]
  simpa only [div_pow] using h

theorem expDecayTest_fourier_sq_integrable {F : ℝ → ℝ} (hF : ExpDecayTest F) :
    Integrable (fun r : ℝ => ‖paperFT (fun x => (F x : ℂ)) (r : ℂ)‖^2) := by
  obtain ⟨M,hM,_,hb⟩ := expDecayTest_exists_fourier_bound hF
  have hc := _root_.Zeta23.Taper.continuous_paperFT_ofReal (expDecayTest_integrable hF).ofReal
  refine ((integrable_one_add_norm (E := ℝ) (r := 2) (by norm_num)).const_mul (M^2)).mono'
    (hc.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun r => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_fourier_bound (hb r)

theorem expDecayTest_fourier_mass_trunc_tendsto {F : ℝ → ℝ} (hF : ExpDecayTest F) :
    Tendsto (fun L : ℝ => ∫ r : ℝ,
      ‖paperFT (fun x => (truncTest F L x : ℂ)) (r : ℂ)‖^2) atTop
      (𝓝 (∫ r : ℝ, ‖paperFT (fun x => (F x : ℂ)) (r : ℂ)‖^2)) := by
  obtain ⟨M,hM,hb,_⟩ := expDecayTest_exists_fourier_bound hF
  have hi : Integrable (fun r : ℝ => M^2*(1+‖r‖)^(-(2 : ℝ))) :=
    (integrable_one_add_norm (E := ℝ) (r := 2) (by norm_num)).const_mul (M^2)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun r : ℝ => M^2*(1+‖r‖)^(-(2 : ℝ))) ?_ ?_ hi ?_
  · apply Eventually.of_forall
    intro L
    have hc := _root_.Zeta23.Taper.continuous_paperFT_ofReal
      ((contDiff_ofReal_truncTest hF.1 L).continuous.integrable_of_hasCompactSupport
        ((hasCompactSupport_truncTest F L).comp_left Complex.ofReal_zero))
    exact (hc.norm.pow 2).aestronglyMeasurable
  · apply Eventually.of_forall
    intro L
    apply Eventually.of_forall
    intro r
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_fourier_bound (hb L r)
  · apply Eventually.of_forall
    intro r
    exact (tendsto_paperFT_truncTest hF (z := (r : ℂ)) (by simp)).norm.pow 2

private theorem tsupport_ofReal_truncTest (F : ℝ → ℝ) (L : ℝ) :
    tsupport (fun x => (truncTest F L x : ℂ)) ⊆ Icc (-L) L := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  change (truncTest F L x : ℂ) ≠ 0 at hx
  by_contra hn
  simp only [mem_Icc, not_and_or, not_le] at hn
  have hL : L ≤ |x| := by
    rcases hn with hn | hn
    · linarith [neg_le_abs x]
    · linarith [le_abs_self x]
  exact hx (by rw [truncTest_eq_zero hL, Complex.ofReal_zero])

/-- The actual noncompact test has the same literal `2*pi` Parseval factor. -/
theorem expDecayTest_fourier_mass_eq {F : ℝ → ℝ} (hF : ExpDecayTest F) :
    (∫ r : ℝ, ‖paperFT (fun x => (F x : ℂ)) (r : ℂ)‖^2) =
      2*Real.pi*(∫ x : ℝ, F x^2) := by
  have ht (L : ℝ) : (∫ r : ℝ,
      ‖paperFT (fun x => (truncTest F L x : ℂ)) (r : ℂ)‖^2) =
      2*Real.pi*(∫ x : ℝ, truncTest F L x^2) := by
    simpa only [ExposingRayPrimitive.fourierMass, ExposingRayMass.mass,
      Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      ExposingRayPrimitive.fourierMass_eq (contDiff_ofReal_truncTest hF.1 L)
        (tsupport_ofReal_truncTest F L)
  have hf := expDecayTest_fourier_mass_trunc_tendsto hF
  simp_rw [ht] at hf
  have hp : Tendsto (fun L : ℝ => ∫ x : ℝ, truncTest F L x^2) atTop
      (𝓝 (∫ x : ℝ, F x^2)) := by
    simpa only [crossCorr, sub_zero, ← pow_two] using tendsto_crossCorr_truncTest hF 0
  exact tendsto_nhds_unique hf (hp.const_mul (2*Real.pi))

theorem expDecayTest_fourier_sq_gamma_integrable {F : ℝ → ℝ} (hF : ExpDecayTest F) :
    Integrable (fun r : ℝ => ‖paperFT (fun x => (F x : ℂ)) (r : ℂ)‖^2*EF.gammaBracket r) := by
  obtain ⟨M,hM,_,hb⟩ := expDecayTest_exists_fourier_bound hF
  let K : ℝ := digammaVerticalGrowthConst (1/4)+Real.log Real.pi
  have hK : 0 ≤ K := by
    have hpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
    have hc : 0 ≤ digammaVerticalGrowthConst (1/4) := by
      unfold digammaVerticalGrowthConst
      positivity
    dsimp [K]
    linarith
  have hc := _root_.Zeta23.Taper.continuous_paperFT_ofReal (expDecayTest_integrable hF).ofReal
  have hi : Integrable (fun r : ℝ => M^2*(K+2)*(1+‖r‖)^(-(3/2 : ℝ))) :=
    (integrable_one_add_norm (E := ℝ) (r := 3/2) (by norm_num)).const_mul (M^2*(K+2))
  refine hi.mono' ((hc.norm.pow 2).mul WeilHerglotz.continuous_gammaBracket).aestronglyMeasurable
    (Eventually.of_forall fun r => ?_)
  have hr : 0 < 1+|r| := by positivity
  have hn : ‖paperFT (fun x => (F x : ℂ)) (r : ℂ)‖^2 ≤ M^2/(1+|r|)^2 := by
    rw [← div_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb r) 2
  have hg := abs_gammaBracket_le_sqrt r
  have hs : 1 ≤ Real.sqrt (1+|r|) := Real.one_le_sqrt.mpr (by linarith [abs_nonneg r])
  have hg' : |EF.gammaBracket r| ≤ (K+2)*Real.sqrt (1+|r|) := by
    change |EF.gammaBracket r| ≤ K+2*Real.sqrt (1+|r|) at hg
    nlinarith
  have he : Real.sqrt (1+|r|)/(1+|r|)^2 = (1+‖r‖)^(-(3/2 : ℝ)) := by
    rw [Real.norm_eq_abs, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_sub hr]
    norm_num
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ M^2/(1+|r|)^2*((K+2)*Real.sqrt (1+|r|)) :=
      mul_le_mul hn hg' (abs_nonneg _) (by positivity)
    _ = M^2*(K+2)*(Real.sqrt (1+|r|)/(1+|r|)^2) := by ring
    _ = _ := by rw [he]

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
