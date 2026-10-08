import GaloisForLFunctions.RHTower.ThetaThresholdXiDivisibleUniqueness
import GaloisForLFunctions.RHTower.RiemannAutocorrFourier
import GaloisForLFunctions.RHTower.WeilPositivityMultiplicativeToeplitzBound
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Coefficient cost of approximating a shifted Xi profile

Finite physical translates preserve every real Xi zero. A spectral translate need not.
The actual double-exponential theta tail turns this mismatch into a quantitative
L² stability bound. This concerns strong-norm approximation, not finite-moment cancellation.
-/

open MeasureTheory Set Filter Topology Complex
open scoped Real NNReal ENNReal InnerProductSpace
open Bottcher Zeta23

noncomputable section
namespace RHTower.WeilWorkDeficitApproximation

/-- A finite complex packet with a fixed physical shift aperture. -/
structure Packet (a : ℝ≥0) where
  size : ℕ
  coeff : Fin size → ℂ
  shift : Fin size → Icc (-(a : ℝ)) (a : ℝ)

def Packet.variation {a : ℝ≥0} (P : Packet a) : ℝ := ∑ j, ‖P.coeff j‖

def Packet.source {a : ℝ≥0} (P : Packet a) (u : ℝ) : ℂ :=
  ∑ j, P.coeff j * riemannPhiKernel (u - P.shift j)

def modulatedPhi (γ u : ℝ) : ℂ :=
  Complex.exp (-(I * (γ : ℂ) * (u : ℂ))) * riemannPhiKernel u

def Packet.error {a : ℝ≥0} (P : Packet a) (γ u : ℝ) : ℂ :=
  P.source u - modulatedPhi γ u

/-- Physical L² error; paper-frequency Plancherel multiplies its square by `2π`. -/
def Packet.errorNorm {a : ℝ≥0} (P : Packet a) (γ : ℝ) : ℝ :=
  (eLpNorm (P.error γ) 2 volume).toReal

private theorem norm_modulatedPhi (γ u : ℝ) :
    ‖modulatedPhi γ u‖ = ‖riemannPhiKernel u‖ := by
  simp [modulatedPhi, Complex.norm_exp]

private theorem continuous_modulatedPhi (γ : ℝ) : Continuous (modulatedPhi γ) :=
  (by fun_prop : Continuous fun u : ℝ => Complex.exp (-(I * (γ : ℂ) * (u : ℂ)))).mul
    continuous_riemannPhiKernel

private theorem integrable_source {a : ℝ≥0} (P : Packet a) : Integrable P.source :=
  integrable_finsetSum _ fun j _ =>
    (integrable_riemannPhiKernel.comp_sub_right (P.shift j : ℝ)).const_mul _

private theorem integrable_modulatedPhi (γ : ℝ) : Integrable (modulatedPhi γ) :=
  integrable_riemannPhiKernel.norm.mono' (continuous_modulatedPhi γ).aestronglyMeasurable
    (Eventually.of_forall fun u => (norm_modulatedPhi γ u).le)

private theorem integrable_error {a : ℝ≥0} (P : Packet a) (γ : ℝ) :
    Integrable (P.error γ) := (integrable_source P).sub (integrable_modulatedPhi γ)

private theorem memLp_phi : MemLp riemannPhiKernel 2 volume := by
  obtain ⟨C, hC, hb⟩ := exists_norm_riemannPhiKernel_le_exp (B := 1) zero_le_one
  apply (memLp_two_iff_integrable_sq_norm continuous_riemannPhiKernel.aestronglyMeasurable).mpr
  refine (integrable_exp_neg_abs.const_mul (C ^ 2)).mono'
    (continuous_riemannPhiKernel.norm.pow 2).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hh := hb u
  simp only [one_mul] at hh
  calc ‖riemannPhiKernel u‖ ^ 2 ≤ (C * Real.exp (-|u|)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hh 2
    _ = C ^ 2 * Real.exp (-|u| + -|u|) := by rw [Real.exp_add]; ring
    _ ≤ C ^ 2 * Real.exp (-|u|) := by gcongr; linarith [abs_nonneg u]

private theorem memLp_error {a : ℝ≥0} (P : Packet a) (γ : ℝ) :
    MemLp (P.error γ) 2 volume := by
  have hs : MemLp P.source 2 volume :=
    memLp_finsetSum _ fun j _ =>
      (memLp_phi.comp_measurePreserving (measurePreserving_sub_right volume
        (P.shift j : ℝ))).const_mul _
  have hm : MemLp (modulatedPhi γ) 2 volume :=
    memLp_phi.of_le (continuous_modulatedPhi γ).aestronglyMeasurable
      (Eventually.of_forall fun u => (norm_modulatedPhi γ u).le)
  exact hs.sub hm

private theorem kernel_envelope : ∃ B : ℝ, 0 < B ∧ ∀ u : ℝ,
    ‖riemannPhiKernel u‖ ≤ B * Real.exp (-Real.exp (2 * |u|)) * Real.exp (-|u|) := by
  obtain ⟨C, hC⟩ := riemannPhiKernel_decay_below_theta (c := 2) (by norm_num)
    (by linarith [Real.pi_gt_three])
  refine ⟨|C| + 1, by positivity, fun u => ?_⟩
  have hh : |u| ≤ Real.exp (2 * |u|) := by
    linarith [Real.add_one_le_exp (2 * |u|), abs_nonneg u]
  calc ‖riemannPhiKernel u‖ ≤ C * Real.exp (-(2 * Real.exp (2 * |u|))) := hC u
    _ ≤ (|C| + 1) * Real.exp (-(2 * Real.exp (2 * |u|))) := by
      gcongr; linarith [le_abs_self C]
    _ ≤ (|C| + 1) * Real.exp (-Real.exp (2 * |u|) + -|u|) := by gcongr; linarith
    _ = _ := by rw [Real.exp_add]; ring

private theorem phi_tail {B : ℝ} (hB : 0 < B)
    (hb : ∀ u : ℝ, ‖riemannPhiKernel u‖ ≤
      B * Real.exp (-Real.exp (2 * |u|)) * Real.exp (-|u|))
    {a L x : ℝ} (hx : |x| ≤ a) :
    (∫ u in (Icc (-L) L)ᶜ, ‖riemannPhiKernel (u-x)‖) ≤
      2 * B * Real.exp (-Real.exp (2 * (L-a))) := by
  let D := B * Real.exp (-Real.exp (2 * (L-a)))
  have hi : Integrable fun u : ℝ => D * Real.exp (-|u-x|) :=
    (integrable_exp_neg_abs.comp_sub_right x).const_mul D
  have hmono : (∫ u in (Icc (-L) L)ᶜ, ‖riemannPhiKernel (u-x)‖) ≤
      ∫ u in (Icc (-L) L)ᶜ, D * Real.exp (-|u-x|) := by
    apply setIntegral_mono_on (integrable_riemannPhiKernel.comp_sub_right x).norm.integrableOn
      hi.integrableOn measurableSet_Icc.compl
    intro u hu
    have hLu : L ≤ |u| := by
      by_contra h
      have hh := abs_lt.mp (lt_of_not_ge h)
      exact hu ⟨hh.1.le, hh.2.le⟩
    have hd : L-a ≤ |u-x| := by linarith [abs_sub_abs_le_abs_sub u x]
    exact (hb (u-x)).trans (by dsimp [D]; gcongr)
  refine hmono.trans ?_
  calc (∫ u in (Icc (-L) L)ᶜ, D * Real.exp (-|u-x|)) ≤
      ∫ u : ℝ, D * Real.exp (-|u-x|) :=
        setIntegral_le_integral hi (Eventually.of_forall fun _ => by dsimp [D]; positivity)
    _ = D * 2 := by
      rw [integral_const_mul,
        integral_sub_right_eq_self (fun u : ℝ => Real.exp (-|u|)) x, integral_exp_neg_abs]
    _ = _ := by dsimp [D]; ring

private theorem error_tail {B : ℝ} (hB : 0 < B)
    (hb : ∀ u : ℝ, ‖riemannPhiKernel u‖ ≤
      B * Real.exp (-Real.exp (2 * |u|)) * Real.exp (-|u|))
    {a : ℝ≥0} (P : Packet a) (γ L : ℝ) :
    (∫ u in (Icc (-L) L)ᶜ, ‖P.error γ u‖) ≤
      2 * B * (P.variation + 1) * Real.exp (-Real.exp (2 * (L-a))) := by
  have hs (j : Fin P.size) : Integrable fun u : ℝ =>
      ‖P.coeff j‖ * ‖riemannPhiKernel (u-P.shift j)‖ :=
    (integrable_riemannPhiKernel.comp_sub_right (P.shift j : ℝ)).norm.const_mul _
  have hp : ∀ u, ‖P.error γ u‖ ≤
      (∑ j, ‖P.coeff j‖ * ‖riemannPhiKernel (u-P.shift j)‖) + ‖riemannPhiKernel u‖ := by
    intro u
    exact (norm_sub_le _ _).trans (add_le_add
      ((norm_sum_le _ _).trans_eq (by simp)) (norm_modulatedPhi γ u).le)
  have hm := setIntegral_mono_on (s := (Icc (-L) L)ᶜ) (integrable_error P γ).norm.integrableOn
    ((integrable_finsetSum _ fun j _ => hs j).add integrable_riemannPhiKernel.norm).integrableOn
    measurableSet_Icc.compl (fun u _ => hp u)
  change (∫ u in (Icc (-L) L)ᶜ, ‖P.error γ u‖) ≤
    ∫ u in (Icc (-L) L)ᶜ,
      (∑ j, ‖P.coeff j‖ * ‖riemannPhiKernel (u-P.shift j)‖) + ‖riemannPhiKernel u‖ at hm
  rw [integral_add (integrable_finsetSum Finset.univ fun j _ => hs j).integrableOn
    integrable_riemannPhiKernel.norm.integrableOn,
    integral_finsetSum Finset.univ (fun j _ => (hs j).integrableOn)] at hm
  simp only [integral_const_mul] at hm
  have hj (j : Fin P.size) := phi_tail hB hb
    (L := L) (abs_le.mpr (P.shift j).property)
  have h0 := phi_tail hB hb (a := (a : ℝ)) (L := L) (x := 0)
    (by simp)
  simp only [sub_zero] at h0
  refine hm.trans ((add_le_add (Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_left (hj j) (norm_nonneg _)) h0).trans_eq ?_)
  simp only [← Finset.sum_mul, Packet.variation]
  ring

private theorem integrable_char_mul {f : ℝ → ℂ} (hf : Integrable f) (r : ℝ) :
    Integrable fun u => f u * Complex.exp (I * (r : ℂ) * (u : ℂ)) := by
  refine hf.norm.mono' (hf.aestronglyMeasurable.mul
    (by fun_prop : Continuous fun u : ℝ => Complex.exp (I * (r : ℂ) * (u : ℂ))).aestronglyMeasurable)
    (Eventually.of_forall fun u => ?_)
  simp [Complex.norm_exp]

private theorem paperFT_phi (z : ℂ) : paperFT riemannPhiKernel z = XiC z := by
  rw [paperFT_riemannPhiKernel, riemannPhiTransform_eq_xi]
  simp only [XiC, mul_comm I z]

/-- The error at a preserved real Xi zero is exactly the nonzero central value. -/
theorem paperFT_error_at_zero {a : ℝ≥0} (P : Packet a)
    (γ : {r : ℝ // XiC (r : ℂ) = 0}) :
    paperFT (P.error γ) γ = -XiC 0 := by
  have hp : paperFT P.source γ = 0 := by
    unfold paperFT Packet.source
    simp only [Finset.sum_mul]
    rw [integral_finsetSum _ (fun j _ => integrable_char_mul
      ((integrable_riemannPhiKernel.comp_sub_right (P.shift j : ℝ)).const_mul _) γ)]
    have he (j : Fin P.size) :
        (∫ u : ℝ, (P.coeff j * riemannPhiKernel (u-P.shift j)) *
          Complex.exp (I * (γ : ℂ) * (u : ℂ))) = 0 := by
      simp only [mul_assoc (P.coeff j), integral_const_mul]
      change P.coeff j * paperFT (fun u => riemannPhiKernel (u-P.shift j)) γ = 0
      rw [paperFT_translate', paperFT_phi, γ.property, mul_zero, mul_zero]
    simp only [he, Finset.sum_const_zero]
  have hm : paperFT (modulatedPhi γ) γ = XiC 0 := by
    change paperFT (fun u => Complex.exp (-(I * (γ : ℂ) * (u : ℂ))) *
      riemannPhiKernel u) γ = _
    rw [paperFT_modulate, sub_self, paperFT_phi]
  calc
    paperFT (P.error γ) γ = paperFT P.source γ - paperFT (modulatedPhi γ) γ := by
      unfold paperFT Packet.error
      simp only [sub_mul]
      exact integral_sub (integrable_char_mul (integrable_source P) γ)
        (integrable_char_mul (integrable_modulatedPhi γ) γ)
    _ = _ := by rw [hp, hm, zero_sub]

private theorem integral_norm_Icc_le {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    {L : ℝ} (hL : 0 < L) :
    (∫ u in Icc (-L) L, ‖f u‖) ≤
      Real.sqrt (2 * L) * (eLpNorm f 2 volume).toReal := by
  let g := hf.norm.toLp (fun u => ‖f u‖)
  have hs : volume (Icc (-L) L) ≠ ∞ := isCompact_Icc.measure_lt_top.ne
  let v : Lp ℝ 2 volume := indicatorConstLp 2 measurableSet_Icc hs (1 : ℝ)
  have hi : (⟪v, g⟫_ℝ) = ∫ u in Icc (-L) L, ‖f u‖ := by
    rw [L2.inner_indicatorConstLp_one]
    exact setIntegral_congr_ae measurableSet_Icc (hf.norm.coeFn_toLp.mono fun _ h _ => h)
  have hv : ‖v‖ = Real.sqrt (2 * L) := by
    simp [v, norm_indicatorConstLp, Measure.real, Real.volume_Icc,
      Real.sqrt_eq_rpow, sub_neg_eq_add, ← two_mul, ENNReal.toReal_ofReal hL.le]
  have hg : ‖g‖ = (eLpNorm f 2 volume).toReal := by
    simp [g, Lp.norm_toLp, eLpNorm_norm]
  have h : ‖⟪v, g⟫_ℝ‖ ≤ ‖v‖ * ‖g‖ := norm_inner_le_norm v g
  rw [hi, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), hv, hg] at h
  exact h

/-- A real Xi zero remains stable under finite-aperture approximation.
The complete coefficient variation and the actual theta tail are retained. -/
theorem zero_approximation_cutoff_bound : ∃ B : ℝ, 0 < B ∧
    ∀ (a : ℝ≥0) (P : Packet a) (γ : {r : ℝ // XiC (r : ℂ) = 0})
      (L : ℝ), 0 < L →
      ‖XiC 0‖ ≤ Real.sqrt (2 * L) * P.errorNorm γ +
        2 * B * (P.variation + 1) * Real.exp (-Real.exp (2 * (L-a))) := by
  obtain ⟨B, hB, hb⟩ := kernel_envelope
  refine ⟨B, hB, fun a P γ L hL => ?_⟩
  have hf := integrable_error P γ
  have hnorm : ‖XiC 0‖ ≤ ∫ u : ℝ, ‖P.error γ u‖ := by
    have h := norm_integral_le_integral_norm (μ := volume)
      (fun u => P.error γ u * Complex.exp (I * (γ : ℂ) * (u : ℂ)))
    change ‖paperFT (P.error γ) γ‖ ≤ _ at h
    rw [paperFT_error_at_zero, norm_neg] at h
    simpa [norm_mul, Complex.norm_exp] using h
  rw [← integral_add_compl measurableSet_Icc hf.norm] at hnorm
  exact hnorm.trans (add_le_add (integral_norm_Icc_le (memLp_error P γ) hL)
    (error_tail hB hb P γ L))

/-- An exponential coefficient budget permits only logarithmic improvement in
squared error, uniformly over every real Xi zero. No zero simplicity is required. -/
theorem exponential_budget_error_bound : ∃ K : ℝ, 1 < K ∧
    ∀ (a : ℝ≥0) (P : Packet a) (γ : {r : ℝ // XiC (r : ℂ) = 0})
      (N : ℝ), 0 ≤ N → P.variation ≤ Real.exp N →
      ‖XiC 0‖ ^ 2 ≤ 8 * ((a : ℝ) + Real.log (N + K)) * P.errorNorm γ ^ 2 := by
  obtain ⟨B, hB, hb⟩ := zero_approximation_cutoff_bound
  let h := ‖XiC 0‖
  have hh : 0 < h := norm_pos_iff.mpr XiC_zero_ne
  let K := 2 + 8 * B / h
  have hK : 1 < K := by
    have : 0 < 8 * B / h := by positivity
    dsimp [K]
    linarith
  have hKt : 4 * B * Real.exp (-K) ≤ h / 2 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    have hmul : (8 * B / h) * h = 8 * B := div_mul_cancel₀ _ hh.ne'
    have he := Real.add_one_le_exp K
    dsimp [K] at he
    nlinarith
  refine ⟨K, hK, fun a P γ N hN hV => ?_⟩
  have hA : 1 < N + K := by linarith
  have hAp : 0 < N + K := by linarith
  let L := (a : ℝ) + Real.log (N + K)
  have hL : 0 < L := add_pos_of_nonneg_of_pos a.coe_nonneg (Real.log_pos hA)
  have hexp : N + K ≤ Real.exp (2 * (L - a)) := by
    dsimp [L]
    rw [add_sub_cancel_left, two_mul, Real.exp_add, Real.exp_log hAp]
    nlinarith
  have htail : 2 * B * (P.variation + 1) * Real.exp (-Real.exp (2 * (L-a))) ≤ h / 2 := by
    calc
      _ ≤ 2 * B * (Real.exp N + 1) * Real.exp (-(N+K)) := by gcongr
      _ ≤ 2 * B * (2 * Real.exp N) * Real.exp (-(N+K)) := by
        gcongr
        linarith [Real.one_le_exp_iff.mpr hN]
      _ = 4 * B * Real.exp (-K) := by
        rw [neg_add, Real.exp_add, Real.exp_neg N]
        field_simp
        ring
      _ ≤ _ := hKt
  have hhalf : h / 2 ≤ Real.sqrt (2 * L) * P.errorNorm γ := by
    have ht := hb a P γ L hL
    change h ≤ _ at ht
    linarith
  have he : 0 ≤ P.errorNorm γ := ENNReal.toReal_nonneg
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ h / 2) hhalf 2
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * L)] at hs
  change h ^ 2 ≤ 8 * L * P.errorNorm γ ^ 2
  nlinarith

/-- Explicit minimum variation for every finite-aperture packet approximating
a spectral shift by a real Xi zero. The L² error is always strictly positive. -/
theorem double_exponential_variation_bound : ∃ K : ℝ, 1 < K ∧
    ∀ (a : ℝ≥0) (P : Packet a) (γ : {r : ℝ // XiC (r : ℂ) = 0}),
      0 < P.errorNorm γ ∧
      Real.exp (Real.exp (‖XiC 0‖ ^ 2 / (8 * P.errorNorm γ ^ 2) - a) - K) ≤
        P.variation + 1 := by
  obtain ⟨K, hK, hb⟩ := exponential_budget_error_bound
  refine ⟨K, hK, fun a P γ => ?_⟩
  have hV : 0 ≤ P.variation := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hVp : 0 < P.variation + 1 := by linarith
  let N := Real.log (P.variation + 1)
  have hN : 0 ≤ N := Real.log_nonneg (by linarith)
  have hNe : Real.exp N = P.variation + 1 := Real.exp_log hVp
  have hbd := hb a P γ N hN (by rw [hNe]; linarith)
  have he : 0 < P.errorNorm γ := by
    have hn : 0 ≤ P.errorNorm γ := ENNReal.toReal_nonneg
    have hh : 0 < ‖XiC 0‖ := norm_pos_iff.mpr XiC_zero_ne
    by_contra hn'
    have hz : P.errorNorm γ = 0 := le_antisymm (le_of_not_gt hn') hn
    rw [hz] at hbd
    nlinarith
  refine ⟨he, ?_⟩
  have hd : ‖XiC 0‖ ^ 2 / (8 * P.errorNorm γ ^ 2) ≤ (a : ℝ) + Real.log (N+K) := by
    apply (div_le_iff₀ (by positivity : 0 < 8 * P.errorNorm γ ^ 2)).mpr
    nlinarith [hbd]
  have hex : Real.exp (‖XiC 0‖ ^ 2 / (8 * P.errorNorm γ ^ 2) - a) ≤ N+K := by
    calc
      _ ≤ Real.exp (Real.log (N+K)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := Real.exp_log (by linarith)
  calc
    _ ≤ Real.exp N := Real.exp_le_exp.mpr (by linarith)
    _ = _ := hNe

end RHTower.WeilWorkDeficitApproximation
