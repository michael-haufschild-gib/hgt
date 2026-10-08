import GaloisForLFunctions.RHTower.WeilWorkQuantizationPeriodicSymbol
import GaloisForLFunctions.Bottcher.AnnulusRoot
import GaloisForLFunctions.Bottcher.WindingCertificates

/-!
# The winding-normalized logarithm of the actual periodic symbol

The analytic nonzero symbol produces its own closed differentiable circle
loop. Its logarithmic-derivative integral is an integer multiple of 2πi.
Removing that monomial produces an analytic logarithm on the whole annulus.
No winding value or logarithm is added to the actual source as a premise.
-/

open Complex Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace RHTower.WeilSpectral
open Bottcher GaloisForLFunctions.HTGeometry

private theorem quantization_circle_mem_annulus {a b : ℝ} (ha : a < 1) (hb : 1 < b)
    (θ : ℝ) : circleMap 0 1 θ ∈ annulusSet a b := by
  change a < ‖circleMap 0 1 θ‖ ∧ ‖circleMap 0 1 θ‖ < b
  simpa only [_root_.norm_circleMap_zero, abs_one] using And.intro ha hb

/-- Continuity of the core logarithmic-derivative integrand is supplied by analyticity. -/
theorem continuous_quantization_logDeriv_circle {P : ℂ → ℂ} {a b : ℝ}
    (ha : a < 1) (hb : 1 < b) (hP : AnalyticOnNhd ℂ P (annulusSet a b))
    (hne : ∀ z ∈ annulusSet a b, P z ≠ 0) :
    Continuous (fun θ : ℝ => logDeriv P (circleMap 0 1 θ) * (circleMap 0 1 θ * I)) := by
  have hld : ContinuousOn (logDeriv P) (annulusSet a b) := by
    change ContinuousOn (fun z => deriv P z / P z) (annulusSet a b)
    exact hP.deriv.continuousOn.div hP.continuousOn hne
  exact (hld.comp_continuous (continuous_circleMap 0 1)
    (quantization_circle_mem_annulus ha hb)).mul ((continuous_circleMap 0 1).mul continuous_const)

/-- The core winding is an integer, derived from the actual analytic loop. -/
theorem quantization_exists_integer_winding {P : ℂ → ℂ} {a b : ℝ}
    (ha : a < 1) (hb : 1 < b) (hP : AnalyticOnNhd ℂ P (annulusSet a b))
    (hne : ∀ z ∈ annulusSet a b, P z ≠ 0) :
    ∃ N : ℤ, (∫ θ in (0 : ℝ)..(2 * Real.pi),
      logDeriv P (circleMap 0 1 θ) * (circleMap 0 1 θ * I)) =
        (N : ℂ) * (2 * Real.pi * I) := by
  have hcm := quantization_circle_mem_annulus ha hb
  let ℓ : C1Loop := {
    γ := fun θ => P (circleMap 0 1 θ)
    γ' := fun θ => deriv P (circleMap 0 1 θ) * (circleMap 0 1 θ * I)
    cont := hP.continuousOn.comp_continuous (continuous_circleMap 0 1) hcm
    cont' := (hP.deriv.continuousOn.comp_continuous (continuous_circleMap 0 1) hcm).mul
      ((continuous_circleMap 0 1).mul continuous_const)
    deriv := fun θ _ => by
      have hc := ((hP _ (hcm θ)).differentiableAt.hasDerivAt).scomp θ
        (hasDerivAt_circleMap 0 1 θ)
      convert hc using 1
      · rfl
      · rfl
      · simp only [smul_eq_mul, mul_comm]
    closed := congrArg P (by simpa using periodic_circleMap (0 : ℂ) 1 (0 : ℝ)) }
  obtain ⟨N, hN⟩ := exists_int_windInt ℓ (a := 0) (fun θ => hne _ (hcm θ))
  refine ⟨N, ?_⟩
  have he : (∫ θ in (0 : ℝ)..(2 * Real.pi),
      logDeriv P (circleMap 0 1 θ) * (circleMap 0 1 θ * I)) = windInt ℓ 0 := by
    unfold windInt
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only [ℓ]
    rw [logDeriv_apply, sub_zero, div_eq_mul_inv]
    ring
  exact he.trans hN

/-- Dividing out the winding monomial pays the annular-logarithm condition. -/
theorem quantization_annulus_log_of_winding {P : ℂ → ℂ} {a b : ℝ}
    (ha0 : 0 < a) (ha : a < 1) (hb : 1 < b)
    (hP : AnalyticOnNhd ℂ P (annulusSet a b))
    (hne : ∀ z ∈ annulusSet a b, P z ≠ 0) (N : ℤ)
    (hwind : (∫ θ in (0 : ℝ)..(2 * Real.pi),
      logDeriv P (circleMap 0 1 θ) * (circleMap 0 1 θ * I)) =
        (N : ℂ) * (2 * Real.pi * I)) :
    ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L (annulusSet a b) ∧
      ∀ z ∈ annulusSet a b, P z = z ^ N * cexp (L z) := by
  let p : ℂ → ℂ := fun z => z ^ (-N)
  have hp : AnalyticOnNhd ℂ p (annulusSet a b) := by
    have hd : DifferentiableOn ℂ p (annulusSet a b) := fun z hz =>
      (differentiableAt_zpow.mpr (Or.inl (annulus_mem_ne_zero ha0 hz))).differentiableWithinAt
    exact hd.analyticOnNhd (isOpen_annulusSet a b)
  have hpne : ∀ z ∈ annulusSet a b, p z ≠ 0 := fun z hz =>
    zpow_ne_zero _ (annulus_mem_ne_zero ha0 hz)
  let g : ℂ → ℂ := fun z => P z * p z
  have hg : AnalyticOnNhd ℂ g (annulusSet a b) := hP.mul hp
  have hgne : ∀ z ∈ annulusSet a b, g z ≠ 0 := fun z hz => mul_ne_zero (hne z hz) (hpne z hz)
  have hsplit (θ : ℝ) :
      logDeriv g (circleMap 0 1 θ) * (circleMap 0 1 θ * I) =
        logDeriv P (circleMap 0 1 θ) * (circleMap 0 1 θ * I) +
          logDeriv p (circleMap 0 1 θ) * (circleMap 0 1 θ * I) := by
    have hm := quantization_circle_mem_annulus ha hb θ
    have hd : logDeriv g (circleMap 0 1 θ) =
        logDeriv P (circleMap 0 1 θ) + logDeriv p (circleMap 0 1 θ) :=
      logDeriv_mul _ (hne _ hm) (hpne _ hm) (hP _ hm).differentiableAt (hp _ hm).differentiableAt
    rw [hd]
    ring
  have hw : (∫ θ in (0 : ℝ)..(2 * Real.pi),
      logDeriv g (circleMap 0 1 θ) * (circleMap 0 1 θ * I)) = 0 := by
    rw [intervalIntegral.integral_congr (fun θ _ => hsplit θ),
      intervalIntegral.integral_add
        ((continuous_quantization_logDeriv_circle ha hb hP hne).intervalIntegrable _ _)
        ((continuous_quantization_logDeriv_circle ha hb hp hpne).intervalIntegrable _ _)]
    rw [hwind, winding_zpow_circle (by norm_num : (0 : ℝ) < 1) (-N)]
    push_cast
    ring
  obtain ⟨L, hL, he⟩ := exists_log_on_annulus ha0 ha hb hg hgne hw
  refine ⟨L, hL, fun z hz => ?_⟩
  rw [he z hz]
  dsimp only [g, p]
  rw [mul_left_comm, zpow_neg, mul_inv_cancel₀ (zpow_ne_zero N (annulus_mem_ne_zero ha0 hz)), mul_one]

/-- Both winding and logarithm are constructed on the nonzero annulus. -/
theorem quantization_exists_annulus_log {P : ℂ → ℂ} {a b : ℝ}
    (ha0 : 0 < a) (ha : a < 1) (hb : 1 < b)
    (hP : AnalyticOnNhd ℂ P (annulusSet a b))
    (hne : ∀ z ∈ annulusSet a b, P z ≠ 0) :
    ∃ (N : ℤ) (L : ℂ → ℂ), AnalyticOnNhd ℂ L (annulusSet a b) ∧
      ∀ z ∈ annulusSet a b, P z = z ^ N * cexp (L z) := by
  obtain ⟨N, hN⟩ := quantization_exists_integer_winding ha hb hP hne
  obtain ⟨L, hL, he⟩ := quantization_annulus_log_of_winding ha0 ha hb hP hne N hN
  exact ⟨N, L, hL, he⟩

end RHTower.WeilSpectral
