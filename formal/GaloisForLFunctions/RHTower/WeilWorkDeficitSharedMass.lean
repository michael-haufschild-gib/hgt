import GaloisForLFunctions.RHTower.WeilWorkDeficitRecovery
import Mathlib.MeasureTheory.Measure.Sub

/-!
# The critical mass shared with the actual Xi divisor

Clipping the carried weight at one produces a common positive submeasure of the canonical
spectral measure and the projected Xi divisor. This construction retains every multiplicity
copy and does not assume that the canonical measure is discrete.
-/

open Complex MeasureTheory Filter Topology Set
open scoped BigOperators ENNReal

noncomputable section

namespace RHTower.WeilSpectral

/-- The part of one divisor copy carried by its critical spectral atom. -/
def sharedCopyWeight {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (q : XiZeroCopy) : ℝ :=
  1 - deficitWeight hW q

theorem sharedCopyWeight_nonneg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (q : XiZeroCopy) : 0 ≤ sharedCopyWeight hW q :=
  sub_nonneg.mpr (deficitWeight_le_one hW q)

theorem sharedCopyWeight_le_one {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (q : XiZeroCopy) : sharedCopyWeight hW q ≤ 1 := by
  have := deficitWeight_nonneg hW q
  unfold sharedCopyWeight
  linarith

theorem sharedCopyWeight_le_carried {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (q : XiZeroCopy) : sharedCopyWeight hW q ≤ carriedWeight hW q := by
  have := one_sub_le hW q
  unfold sharedCopyWeight
  linarith

/-- The divisor projected to the ordinate axis, with all multiplicities. -/
def deficitOrdinateMeasure : Measure ℝ :=
  Measure.sum fun q : XiZeroCopy => Measure.dirac (q.1 : ℂ).im

/-- The shared critical atoms, clipped copy by copy. -/
def deficitSharedMeasure {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) : Measure ℝ :=
  Measure.sum fun q : XiZeroCopy =>
    ENNReal.ofReal (sharedCopyWeight hW q) • Measure.dirac (q.1 : ℂ).im

theorem deficitSharedMeasure_le_ordinate {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    deficitSharedMeasure hW ≤ deficitOrdinateMeasure := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [deficitSharedMeasure, deficitOrdinateMeasure, Measure.sum_apply _ hs,
    Measure.sum_apply _ hs]
  apply ENNReal.tsum_le_tsum
  intro q
  rw [Measure.smul_apply, smul_eq_mul]
  have h : ENNReal.ofReal (sharedCopyWeight hW q) ≤ 1 := by
    simpa using ENNReal.ofReal_le_ofReal (sharedCopyWeight_le_one hW q)
  simpa using mul_le_mul_left h (Measure.dirac (q.1 : ℂ).im s)

private theorem tsum_shared_le_lintegral {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (g : ℝ → ℝ≥0∞) :
    ∑' q : XiZeroCopy, ENNReal.ofReal (sharedCopyWeight hW q) * g (q.1 : ℂ).im ≤
      ∫⁻ r, g r ∂boundaryMeasure hW := by
  set μ := boundaryMeasure hW
  have hfib : ∀ ρ : XiDivisorSupport,
      (∑' i : Fin (xiDivisorMult ρ),
        ENNReal.ofReal (sharedCopyWeight hW ⟨ρ, i⟩) * g (ρ : ℂ).im) ≤
      if (ρ : ℂ).re = 1 / 2 then μ {(ρ : ℂ).im} * g (ρ : ℂ).im else 0 := by
    intro ρ
    let q : XiZeroCopy := ⟨ρ, ⟨0, xiDivisorMult_pos ρ⟩⟩
    have hconst : ∀ i : Fin (xiDivisorMult ρ),
        sharedCopyWeight hW ⟨ρ, i⟩ = sharedCopyWeight hW q := fun _ => rfl
    rw [tsum_fintype]
    simp_rw [hconst]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    by_cases hc : (ρ : ℂ).re = 1 / 2
    · rw [if_pos hc, ← mul_assoc]
      have hm : (0 : ℝ) < xiDivisorMult ρ := by exact_mod_cast xiDivisorMult_pos ρ
      have hw := sharedCopyWeight_le_carried hW q
      have hmass : (xiDivisorMult ρ : ℝ) * sharedCopyWeight hW q ≤ (μ {(ρ : ℂ).im}).toReal := by
        change sharedCopyWeight hW q ≤
          (if (ρ : ℂ).re = 1 / 2 then (μ {(ρ : ℂ).im}).toReal / xiDivisorMult ρ else 0) at hw
        rw [if_pos hc] at hw
        nlinarith [(le_div_iff₀ hm).mp hw]
      have hen : (xiDivisorMult ρ : ℝ≥0∞) * ENNReal.ofReal (sharedCopyWeight hW q) ≤
          μ {(ρ : ℂ).im} := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        exact (ENNReal.ofReal_le_ofReal hmass).trans ENNReal.ofReal_toReal_le
      exact mul_le_mul_left hen _
    · rw [if_neg hc]
      have hw : sharedCopyWeight hW q = 0 := by
        change 1 - (if (ρ : ℂ).re = 1 / 2 then _ else 1) = 0
        rw [if_neg hc, sub_self]
      simp [hw]
  rw [ENNReal.tsum_sigma']
  refine (ENNReal.tsum_le_tsum hfib).trans ?_
  have hsub : (∑' ρ : XiDivisorSupport,
      if (ρ : ℂ).re = 1 / 2 then μ {(ρ : ℂ).im} * g (ρ : ℂ).im else 0) =
      ∑' ρ : CritPoint, μ {(ρ.1 : ℂ).im} * g (ρ.1 : ℂ).im := by
    set f : XiDivisorSupport → ℝ≥0∞ := fun ρ => μ {(ρ : ℂ).im} * g (ρ : ℂ).im
    have ht := tsum_subtype {ρ : XiDivisorSupport | (ρ : ℂ).re = 1 / 2} f
    calc
      (∑' ρ : XiDivisorSupport, if (ρ : ℂ).re = 1 / 2 then f ρ else 0) =
          ∑' ρ, ({ρ : XiDivisorSupport | (ρ : ℂ).re = 1 / 2}).indicator f ρ := by
        apply tsum_congr
        intro ρ
        rfl
      _ = ∑' ρ : ({ρ : XiDivisorSupport | (ρ : ℂ).re = 1 / 2} : Set XiDivisorSupport),
          f ρ := ht.symm
      _ = _ := rfl
  rw [hsub]
  let S : Set ℝ := Set.range fun ρ : CritPoint => (ρ.1 : ℂ).im
  have heq : (∑' ρ : CritPoint, μ {(ρ.1 : ℂ).im} * g (ρ.1 : ℂ).im) =
      ∑' γ : S, g γ * μ {(γ : ℝ)} := by
    rw [← Equiv.tsum_eq (Equiv.ofInjective _ critOrd_injective)]
    apply tsum_congr
    intro ρ
    simp [Equiv.ofInjective, mul_comm]
  rw [heq, ← lintegral_countable _ (Set.countable_range _)]
  exact setLIntegral_le_lintegral _ _

/-- The clipped critical atoms are an actual submeasure of the canonical measure. -/
theorem deficitSharedMeasure_le_boundary {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    deficitSharedMeasure hW ≤ boundaryMeasure hW := by
  classical
  apply Measure.le_iff.mpr
  intro s hs
  rw [deficitSharedMeasure, Measure.sum_apply _ hs]
  have h := tsum_shared_le_lintegral hW (s.indicator (fun _ => 1))
  rw [lintegral_indicator_const hs 1, one_mul] at h
  convert h using 1
  apply tsum_congr
  intro q
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
  rfl

private theorem weightedOrdinateMeasure_Ioc (w : XiZeroCopy → ℝ≥0∞) (T : ℝ) :
    (Measure.sum fun q : XiZeroCopy => w q • Measure.dirac (q.1 : ℂ).im) (Ioc 0 T) =
      ∑ q ∈ (finite_deficitWindow T).toFinset, w q := by
  classical
  rw [Measure.sum_apply _ measurableSet_Ioc]
  calc
    (∑' q : XiZeroCopy, (w q • Measure.dirac (q.1 : ℂ).im) (Ioc 0 T)) =
        ∑ q ∈ (finite_deficitWindow T).toFinset,
          (w q • Measure.dirac (q.1 : ℂ).im) (Ioc 0 T) := by
      apply tsum_eq_sum
      intro q hq
      have hnot : (q.1 : ℂ).im ∉ Ioc 0 T := by
        simpa only [Set.Finite.mem_toFinset, deficitWindow, Set.mem_setOf_eq, Set.mem_Ioc] using hq
      simp [Measure.smul_apply, Set.indicator_of_notMem hnot]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      have hmem : (q.1 : ℂ).im ∈ Ioc 0 T := by
        simpa only [Set.Finite.mem_toFinset, deficitWindow, Set.mem_setOf_eq, Set.mem_Ioc] using hq
      simp [Measure.smul_apply, Measure.dirac_apply_of_mem hmem]

theorem deficitOrdinateMeasure_Ioc (T : ℝ) :
    deficitOrdinateMeasure (Ioc 0 T) = ((finite_deficitWindow T).toFinset.card : ℝ≥0∞) := by
  simpa [deficitOrdinateMeasure] using weightedOrdinateMeasure_Ioc (fun _ => 1) T

theorem deficitSharedMeasure_Ioc {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (T : ℝ) :
    deficitSharedMeasure hW (Ioc 0 T) =
      ∑ q ∈ (finite_deficitWindow T).toFinset, ENNReal.ofReal (sharedCopyWeight hW q) :=
  weightedOrdinateMeasure_Ioc _ T

/-- The shared mass is exactly the total multiplicity count minus the deficit. -/
theorem deficitSharedMeasure_real_Ioc {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (T : ℝ) :
    (deficitSharedMeasure hW).real (Ioc 0 T) =
      ((finite_deficitWindow T).toFinset.card : ℝ) - deficitCount hW T := by
  classical
  rw [measureReal_def, deficitSharedMeasure_Ioc,
    ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
  simp_rw [ENNReal.toReal_ofReal (sharedCopyWeight_nonneg hW _), sharedCopyWeight]
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
    deficitCount_eq_sum_window hW le_rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  rw [Set.Finite.mem_toFinset] at hq
  rw [if_pos hq]

theorem isFiniteMeasure_deficitOrdinateWindow (T : ℝ) :
    IsFiniteMeasure (deficitOrdinateMeasure.restrict (Ioc 0 T)) := by
  constructor
  rw [Measure.restrict_apply_univ, deficitOrdinateMeasure_Ioc]
  exact ENNReal.natCast_lt_top _

theorem isFiniteMeasure_deficitSharedWindow {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (T : ℝ) : IsFiniteMeasure ((deficitSharedMeasure hW).restrict (Ioc 0 T)) := by
  haveI := isFiniteMeasure_deficitOrdinateWindow T
  exact isFiniteMeasure_of_le _ (Measure.restrict_mono_measure
    (deficitSharedMeasure_le_ordinate hW) _)

/-- The canonical measure has finite mass on every bounded positive-height window. -/
theorem isFiniteMeasure_deficitBoundaryWindow {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (T : ℝ) : IsFiniteMeasure ((boundaryMeasure hW).restrict (Ioc 0 T)) := by
  have hi0 := integrable_inv_one_add_sq_sub hW 0
  simp only [sub_zero] at hi0
  have hi := (hi0.const_mul (1 + T ^ 2)).restrict
    (s := Ioc 0 T)
  have hdom : ∀ᵐ r ∂(boundaryMeasure hW).restrict (Ioc 0 T),
      ‖(1 : ℝ)‖ ≤ (1 + T ^ 2) * (1 / (1 + r ^ 2)) := by
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro r hr
    rw [norm_one, mul_one_div, le_div_iff₀ (by positivity)]
    nlinarith [hr.1, hr.2, sq_nonneg (T - r)]
  exact (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).mp
    (hi.mono' aestronglyMeasurable_const hdom)

private theorem norm_integral_sub_le_common_mass {μ ν χ : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure χ]
    (hχμ : χ ≤ μ) (hχν : χ ≤ ν) {f : ℝ → ℂ} (hf : Continuous f)
    (hb : ∀ r, ‖f r‖ ≤ 1) :
    ‖(∫ r, f r ∂μ) - ∫ r, f r ∂ν‖ ≤ μ.real univ + ν.real univ - 2 * χ.real univ := by
  have hi : ∀ ξ : Measure ℝ, IsFiniteMeasure ξ → Integrable f ξ := by
    intro ξ hξ
    letI := hξ
    exact (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable (Eventually.of_forall hb)
  have hμ := integral_add_measure (hi (μ - χ) inferInstance) (hi χ inferInstance)
  have hν := integral_add_measure (hi (ν - χ) inferInstance) (hi χ inferInstance)
  rw [Measure.sub_add_cancel_of_le hχμ] at hμ
  rw [Measure.sub_add_cancel_of_le hχν] at hν
  calc
    ‖(∫ r, f r ∂μ) - ∫ r, f r ∂ν‖ =
        ‖(∫ r, f r ∂(μ - χ)) - ∫ r, f r ∂(ν - χ)‖ := by
      rw [hμ, hν]
      congr 1
      abel
    _ ≤ ‖∫ r, f r ∂(μ - χ)‖ + ‖∫ r, f r ∂(ν - χ)‖ := norm_sub_le _ _
    _ ≤ (μ - χ).real univ + (ν - χ).real univ := by
      apply add_le_add <;>
        simpa only [one_mul] using norm_integral_le_of_norm_le_const (Eventually.of_forall hb)
    _ = _ := by
      simp only [measureReal_def, Measure.sub_apply MeasurableSet.univ hχμ,
        Measure.sub_apply MeasurableSet.univ hχν,
        ENNReal.toReal_sub_of_le (hχμ univ) (measure_ne_top μ univ),
        ENNReal.toReal_sub_of_le (hχν univ) (measure_ne_top ν univ)]
      ring

/-- Fixed-frequency discrepancy is paid by twice the actual deficit and the total mass error. -/
theorem norm_deficitWindow_fourier_sub_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k T : ℝ) :
    ‖(∫ r in Ioc 0 T, Complex.exp (((k * r : ℝ) : ℂ) * I) ∂boundaryMeasure hW) -
        ∫ r in Ioc 0 T, Complex.exp (((k * r : ℝ) : ℂ) * I) ∂deficitOrdinateMeasure‖ ≤
      (boundaryMeasure hW).real (Ioc 0 T) - ((finite_deficitWindow T).toFinset.card : ℝ) +
        2 * deficitCount hW T := by
  haveI := isFiniteMeasure_deficitBoundaryWindow hW T
  haveI := isFiniteMeasure_deficitOrdinateWindow T
  haveI := isFiniteMeasure_deficitSharedWindow hW T
  have hc : Continuous (fun r : ℝ => Complex.exp (((k * r : ℝ) : ℂ) * I)) := by fun_prop
  have hb : ∀ r : ℝ, ‖Complex.exp (((k * r : ℝ) : ℂ) * I)‖ ≤ 1 := fun r =>
    (Complex.norm_exp_ofReal_mul_I (k * r)).le
  have h := norm_integral_sub_le_common_mass
    (Measure.restrict_mono_measure (deficitSharedMeasure_le_boundary hW) (Ioc 0 T))
    (Measure.restrict_mono_measure (deficitSharedMeasure_le_ordinate hW) (Ioc 0 T)) hc hb
  have hν : (deficitOrdinateMeasure.restrict (Ioc 0 T)).real univ =
      ((finite_deficitWindow T).toFinset.card : ℝ) := by
    rw [measureReal_restrict_apply_univ, measureReal_def, deficitOrdinateMeasure_Ioc,
      ENNReal.toReal_natCast]
  have hχ : ((deficitSharedMeasure hW).restrict (Ioc 0 T)).real univ =
      ((finite_deficitWindow T).toFinset.card : ℝ) - deficitCount hW T := by
    rw [measureReal_restrict_apply_univ, deficitSharedMeasure_real_Ioc]
  rw [hν, hχ, measureReal_restrict_apply_univ] at h
  convert h using 1
  ring

end RHTower.WeilSpectral

end
