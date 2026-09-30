import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Exact norms of continuous multipliers on Lebesgue L²

Positive-volume interval indicators force the pointwise symbol norm below
the operator norm. Continuity identifies the literal essential supremum,
including the squared norm needed for weighted transport.
-/

noncomputable section
open Filter Topology Set
open scoped ENNReal
namespace MeasureTheory

/-- Positive-volume open level sets identify the essential supremum. -/
theorem continuous_essSup_ofReal_eq_iSup {f : ℝ → ℝ} (hf : Continuous f) :
    essSup (fun x => ENNReal.ofReal (f x)) (volume : Measure ℝ) =
      ⨆ x, ENNReal.ofReal (f x) := by
  apply (iSup_eq_essSup ?_).symm
  intro x a ha
  exact (isOpen_lt continuous_const (ENNReal.continuous_ofReal.comp hf)).measure_ne_zero
    volume ⟨x, ha⟩

/-- Every continuous multiplication symbol is bounded by its operator norm. -/
theorem norm_symbol_le_of_ae_mul_continuous {ψ : ℝ → ℂ}
    {T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)}
    (hψ : Continuous ψ)
    (hT : ∀ f, (T f : ℝ → ℂ) =ᵐ[volume] fun x => ψ x * f x) (x₀ : ℝ) :
    ‖ψ x₀‖ ≤ ‖T‖ := by
  by_contra hbad
  obtain ⟨C, hTC, hCψ⟩ := exists_between (lt_of_not_ge hbad)
  have hC0 : 0 < C := lt_of_le_of_lt (norm_nonneg T) hTC
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    ((hψ.norm.tendsto x₀).eventually (eventually_gt_nhds hCψ))
  have hfin : volume (Metric.ball x₀ r) ≠ ∞ := by
    rw [Real.volume_ball]
    exact ENNReal.ofReal_ne_top
  let f : Lp ℂ 2 (volume : Measure ℝ) :=
    indicatorConstLp 2 measurableSet_ball hfin (1 : ℂ)
  have hfpos : 0 < ‖f‖ := by
    dsimp only [f]
    rw [norm_indicatorConstLp (by norm_num) (by norm_num), norm_one, one_mul,
      measureReal_def, Real.volume_ball, ENNReal.toReal_ofReal (by positivity)]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hle : ‖(C : ℂ) • f‖ ≤ ‖T f‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_smul (C : ℂ) f, hT f,
      (indicatorConstLp_coeFn (p := 2) (hs := measurableSet_ball) (hμs := hfin)
        (c := (1 : ℂ)))] with y hsmul hTy hfy
    rw [hsmul, hTy, Pi.smul_apply, norm_smul, norm_mul]
    by_cases hy : y ∈ Metric.ball x₀ r
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC0]
      exact mul_le_mul_of_nonneg_right (hball hy).le (norm_nonneg _)
    · change f y = _ at hfy
      rw [hfy, indicator_of_notMem hy]
      simp
  have hle' : C * ‖f‖ ≤ ‖T‖ * ‖f‖ := by
    calc
      C * ‖f‖ = ‖(C : ℂ) • f‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC0]
      _ ≤ ‖T f‖ := hle
      _ ≤ ‖T‖ * ‖f‖ := T.le_opNorm f
  exact (not_le_of_gt (mul_lt_mul_of_pos_right hTC hfpos)) hle'

/-- The exact operator norm equals the literal symbol essential supremum. -/
theorem ofReal_norm_eq_essSup_of_ae_mul_continuous {ψ : ℝ → ℂ}
    {T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)}
    (hψ : Continuous ψ)
    (hT : ∀ f, (T f : ℝ → ℂ) =ᵐ[volume] fun x => ψ x * f x) :
    ENNReal.ofReal ‖T‖ = essSup (fun x => ENNReal.ofReal ‖ψ x‖) volume := by
  rw [continuous_essSup_ofReal_eq_iSup hψ.norm]
  have hs : (⨆ x, ENNReal.ofReal ‖ψ x‖) ≤ ENNReal.ofReal ‖T‖ :=
    iSup_le fun x => ENNReal.ofReal_le_ofReal (norm_symbol_le_of_ae_mul_continuous hψ hT x)
  have hfin : (⨆ x, ENNReal.ofReal ‖ψ x‖) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs
  have hbound : ∀ x, ‖ψ x‖ ≤ (⨆ y, ENNReal.ofReal ‖ψ y‖).toReal := by
    intro x
    have h := ENNReal.toReal_mono hfin
      (le_iSup (fun y => ENNReal.ofReal ‖ψ y‖) x)
    simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using h
  have hn := norm_le_of_ae_mul ENNReal.toReal_nonneg hbound hT
  apply le_antisymm _ hs
  calc
    ENNReal.ofReal ‖T‖ ≤ ENNReal.ofReal (⨆ y, ENNReal.ofReal ‖ψ y‖).toReal :=
      ENNReal.ofReal_le_ofReal hn
    _ = _ := ENNReal.ofReal_toReal hfin

/-- Squaring preserves the exact essential-supremum norm law. -/
theorem ofReal_norm_sq_eq_essSup_of_ae_mul_continuous {ψ : ℝ → ℂ}
    {T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)}
    (hψ : Continuous ψ)
    (hT : ∀ f, (T f : ℝ → ℂ) =ᵐ[volume] fun x => ψ x * f x) :
    ENNReal.ofReal (‖T‖ ^ 2) =
      essSup (fun x => ENNReal.ofReal (‖ψ x‖ ^ 2)) volume := by
  rw [ENNReal.ofReal_pow (norm_nonneg T), ofReal_norm_eq_essSup_of_ae_mul_continuous hψ hT,
    continuous_essSup_ofReal_eq_iSup hψ.norm, ENNReal.iSup_pow,
    continuous_essSup_ofReal_eq_iSup (f := fun x => ‖ψ x‖ ^ 2) (hψ.norm.pow 2)]
  simp_rw [ENNReal.ofReal_pow (norm_nonneg _)]

end MeasureTheory
