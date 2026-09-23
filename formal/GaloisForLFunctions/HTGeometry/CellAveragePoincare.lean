import GaloisForLFunctions.HTGeometry.IntervalPoincare
import Mathlib.MeasureTheory.Integral.Average

open MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The squared-error minimization property of a measure average. -/
theorem integral_sq_sub_average_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ} (hf : Integrable f μ)
    (hcenter : Integrable (fun x => (f x - (⨍ y, f y ∂μ)) ^ (2 : ℕ)) μ)
    {c : ℝ} :
    (∫ x, (f x - (⨍ y, f y ∂μ)) ^ (2 : ℕ) ∂μ) ≤ ∫ x, (f x - c) ^ (2 : ℕ) ∂μ := by
  let m : ℝ := ⨍ y, f y ∂μ
  change Integrable (fun x => (f x - m) ^ (2 : ℕ)) μ at hcenter
  have hlin : Integrable (fun x => f x - m) μ :=
    hf.sub (integrable_const _)
  have hmean : (∫ x, f x - m ∂μ) = 0 := by
    exact integral_sub_average μ f
  have hcross : Integrable (fun x => (2 * (m - c)) * (f x - m)) μ :=
    hlin.const_mul _
  have hconst : Integrable (fun _ : α => (m - c) ^ (2 : ℕ)) μ :=
    integrable_const _
  have hdecomp : (∫ x, (f x - c) ^ (2 : ℕ) ∂μ) =
      (∫ x, (f x - m) ^ (2 : ℕ) ∂μ) +
        (2 * (m - c)) * (∫ x, f x - m ∂μ) +
        ∫ _x, (m - c) ^ (2 : ℕ) ∂μ := by
    calc
      (∫ x, (f x - c) ^ (2 : ℕ) ∂μ) =
          ∫ x, ((f x - m) ^ (2 : ℕ) + (2 * (m - c)) * (f x - m) + (m - c) ^ (2 : ℕ)) ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = (∫ x, ((f x - m) ^ (2 : ℕ) + (2 * (m - c)) * (f x - m)) ∂μ) +
          ∫ _x, (m - c) ^ (2 : ℕ) ∂μ := by
        exact integral_add (hcenter.add hcross) hconst
      _ = (∫ x, (f x - m) ^ (2 : ℕ) ∂μ) +
          (∫ x, (2 * (m - c)) * (f x - m) ∂μ) +
          ∫ _x, (m - c) ^ (2 : ℕ) ∂μ := by
        rw [integral_add hcenter hcross]
      _ = (∫ x, (f x - m) ^ (2 : ℕ) ∂μ) +
          (2 * (m - c)) * (∫ x, f x - m ∂μ) +
          ∫ _x, (m - c) ^ (2 : ℕ) ∂μ := by
        rw [integral_const_mul]
  have hnonneg : (0 : ℝ) ≤ ∫ _x, (m - c) ^ (2 : ℕ) ∂μ := by
    exact integral_nonneg fun _ => sq_nonneg _
  rw [show (∫ x, (f x - (⨍ y, f y ∂μ)) ^ (2 : ℕ) ∂μ) =
      (∫ x, (f x - m) ^ (2 : ℕ) ∂μ) by rfl, hdecomp, hmean]
  linarith


/-- A cell mean obeys the same one-dimensional Poincaré bound as a left endpoint. -/
theorem integral_sub_average_sq_le_of_hasDerivAt {g g' : ℝ → ℝ} {α β : ℝ}
    (hαβ : α ≤ β) (hderiv : ∀ y : ℝ, HasDerivAt g (g' y) y)
    (hg' : IntervalIntegrable g' volume α β)
    (hg'2 : IntervalIntegrable (fun y => g' y ^ (2 : ℕ)) volume α β) :
    (∫ x in Set.Ioc α β,
      (g x - (⨍ y, g y ∂(volume.restrict (Set.Ioc α β)))) ^ (2 : ℕ)) ≤
      (β - α) ^ (2 : ℕ) * ∫ y in Set.Ioc α β, g' y ^ (2 : ℕ) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc α β)
  have hcont : Continuous g :=
    continuous_iff_continuousAt.2 fun x => (hderiv x).continuousAt
  have hmeanInt : Integrable (fun x => g x - (⨍ y, g y ∂μ)) μ := by
    change IntegrableOn (fun x => g x - (⨍ y, g y ∂μ)) (Set.Ioc α β) volume
    exact (hcont.sub continuous_const).integrableOn_Ioc
  have hcenter : Integrable (fun x => (g x - (⨍ y, g y ∂μ)) ^ (2 : ℕ)) μ := by
    change IntegrableOn (fun x => (g x - (⨍ y, g y ∂μ)) ^ (2 : ℕ)) (Set.Ioc α β) volume
    exact ((hcont.sub continuous_const).pow 2).integrableOn_Ioc
  have hmin := integral_sq_sub_average_le μ
    (show Integrable g μ by
      change IntegrableOn g (Set.Ioc α β) volume
      exact hcont.integrableOn_Ioc)
    hcenter (c := g α)
  have hpoint : IntegrableOn (fun x => (g x - g α) ^ (2 : ℕ)) (Set.Ioc α β) volume :=
    ((hcont.sub continuous_const).pow 2).integrableOn_Ioc
  have hpoin := integral_sub_left_sq_le_of_hasDerivAt hαβ hderiv hg' hg'2 hpoint
  change (∫ x, (g x - (⨍ y, g y ∂μ)) ^ (2 : ℕ) ∂μ) ≤ _
  exact hmin.trans hpoin

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

/-- The squared-error minimization property of a complex measure average. -/
theorem integral_normSq_sub_average_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℂ} (hf : Integrable f μ)
    (hcenter : Integrable (fun x => Complex.normSq (f x - (⨍ y, f y ∂μ))) μ)
    {c : ℂ} :
    (∫ x, Complex.normSq (f x - (⨍ y, f y ∂μ)) ∂μ) ≤
      ∫ x, Complex.normSq (f x - c) ∂μ := by
  let m : ℂ := ⨍ y, f y ∂μ
  change Integrable (fun x => Complex.normSq (f x - m)) μ at hcenter
  have hlin : Integrable (fun x => f x - m) μ :=
    hf.sub (integrable_const _)
  have hmean : (∫ x, f x - m ∂μ) = 0 := by
    exact integral_sub_average μ f
  let d : ℂ := m - c
  have hprod : Integrable (fun x => (f x - m) * (starRingEnd ℂ) d) μ :=
    hlin.mul_const _
  have hcross : Integrable (fun x => 2 * ((f x - m) * (starRingEnd ℂ) d).re) μ :=
    hprod.re.const_mul 2
  have hconst : Integrable (fun _x : α => Complex.normSq d) μ :=
    integrable_const _
  have hcross_zero : (∫ x, 2 * ((f x - m) * (starRingEnd ℂ) d).re ∂μ) = 0 := by
    rw [integral_const_mul]
    change 2 * (∫ x, RCLike.re ((f x - m) * (starRingEnd ℂ) d) ∂μ) = 0
    rw [integral_re hprod, integral_mul_const, hmean]
    simp
  have hdecomp : (∫ x, Complex.normSq (f x - c) ∂μ) =
      (∫ x, Complex.normSq (f x - m) ∂μ) +
        (∫ x, 2 * ((f x - m) * (starRingEnd ℂ) d).re ∂μ) +
        ∫ _x, Complex.normSq d ∂μ := by
    calc
      (∫ x, Complex.normSq (f x - c) ∂μ) =
          ∫ x, (Complex.normSq (f x - m) +
            2 * ((f x - m) * (starRingEnd ℂ) d).re + Complex.normSq d) ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        have hsub : f x - c = (f x - m) + d := by
          dsimp only [d]
          ring
        rw [hsub, Complex.normSq_add]
        ring
      _ = (∫ x, (Complex.normSq (f x - m) +
          2 * ((f x - m) * (starRingEnd ℂ) d).re) ∂μ) +
          ∫ _x, Complex.normSq d ∂μ := by
        exact integral_add (hcenter.add hcross) hconst
      _ = (∫ x, Complex.normSq (f x - m) ∂μ) +
          (∫ x, 2 * ((f x - m) * (starRingEnd ℂ) d).re ∂μ) +
          ∫ _x, Complex.normSq d ∂μ := by
        rw [integral_add hcenter hcross]
  have hnonneg : (0 : ℝ) ≤ ∫ _x, Complex.normSq d ∂μ := by
    exact integral_nonneg fun _ => Complex.normSq_nonneg _
  rw [show (∫ x, Complex.normSq (f x - (⨍ y, f y ∂μ)) ∂μ) =
      (∫ x, Complex.normSq (f x - m) ∂μ) by rfl, hdecomp, hcross_zero]
  linarith

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

/-- Complex-valued interval Poincaré estimate from the real and imaginary components. -/
theorem integral_normSq_sub_left_le_of_hasDerivAt {g g' : ℝ → ℂ} {α β : ℝ}
    (hαβ : α ≤ β) (hderiv : ∀ y : ℝ, HasDerivAt g (g' y) y)
    (hg'c : Continuous g') :
    (∫ x in Set.Ioc α β, Complex.normSq (g x - g α)) ≤
      (β - α) ^ (2 : ℕ) * ∫ y in Set.Ioc α β, Complex.normSq (g' y) := by
  have hcont : Continuous g :=
    continuous_iff_continuousAt.2 fun x => (hderiv x).continuousAt
  have hderivRe (y : ℝ) : HasDerivAt (fun t : ℝ => (g t).re) (g' y).re y := by
    simpa only [Function.comp_def, Complex.reCLM_apply] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt y (hderiv y)
  have hderivIm (y : ℝ) : HasDerivAt (fun t : ℝ => (g t).im) (g' y).im y := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt y (hderiv y)
  have hcontRe : Continuous (fun y : ℝ => (g' y).re) :=
    Complex.continuous_re.comp hg'c
  have hcontIm : Continuous (fun y : ℝ => (g' y).im) :=
    Complex.continuous_im.comp hg'c
  have hErrRe : IntegrableOn (fun x : ℝ => ((g x - g α).re) ^ (2 : ℕ)) (Set.Ioc α β) volume := by
    exact ((Complex.continuous_re.comp (hcont.sub continuous_const)).pow 2).integrableOn_Ioc
  have hErrIm : IntegrableOn (fun x : ℝ => ((g x - g α).im) ^ (2 : ℕ)) (Set.Ioc α β) volume := by
    exact ((Complex.continuous_im.comp (hcont.sub continuous_const)).pow 2).integrableOn_Ioc
  have hRe := integral_sub_left_sq_le_of_hasDerivAt hαβ hderivRe
    (hcontRe.intervalIntegrable α β) ((hcontRe.pow 2).intervalIntegrable α β) hErrRe
  have hIm := integral_sub_left_sq_le_of_hasDerivAt hαβ hderivIm
    (hcontIm.intervalIntegrable α β) ((hcontIm.pow 2).intervalIntegrable α β) hErrIm
  have hDerivRe : IntegrableOn (fun y : ℝ => (g' y).re ^ (2 : ℕ)) (Set.Ioc α β) volume :=
    (hcontRe.pow 2).integrableOn_Ioc
  have hDerivIm : IntegrableOn (fun y : ℝ => (g' y).im ^ (2 : ℕ)) (Set.Ioc α β) volume :=
    (hcontIm.pow 2).integrableOn_Ioc
  calc
    (∫ x in Set.Ioc α β, Complex.normSq (g x - g α)) =
        (∫ x in Set.Ioc α β, ((g x - g α).re) ^ (2 : ℕ) + ((g x - g α).im) ^ (2 : ℕ)) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x _
      change Complex.normSq (g x - g α) = _
      rw [Complex.normSq_apply]
      ring
    _ = (∫ x in Set.Ioc α β, ((g x - g α).re) ^ (2 : ℕ)) +
        ∫ x in Set.Ioc α β, ((g x - g α).im) ^ (2 : ℕ) := by
      exact integral_add hErrRe hErrIm
    _ ≤ (β - α) ^ (2 : ℕ) * (∫ y in Set.Ioc α β, (g' y).re ^ (2 : ℕ)) +
        (β - α) ^ (2 : ℕ) * ∫ y in Set.Ioc α β, (g' y).im ^ (2 : ℕ) :=
      add_le_add hRe hIm
    _ = (β - α) ^ (2 : ℕ) *
        ((∫ y in Set.Ioc α β, (g' y).re ^ (2 : ℕ)) +
          ∫ y in Set.Ioc α β, (g' y).im ^ (2 : ℕ)) := by ring
    _ = (β - α) ^ (2 : ℕ) * ∫ y in Set.Ioc α β, Complex.normSq (g' y) := by
      rw [← integral_add hDerivRe hDerivIm]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioc
      intro y _
      change (g' y).re ^ (2 : ℕ) + (g' y).im ^ (2 : ℕ) = Complex.normSq (g' y)
      rw [Complex.normSq_apply]
      ring

/-- A complex cell mean obeys the interval Poincaré bound. -/
theorem integral_normSq_sub_average_le_of_hasDerivAt {g g' : ℝ → ℂ} {α β : ℝ}
    (hαβ : α ≤ β) (hderiv : ∀ y : ℝ, HasDerivAt g (g' y) y)
    (hg'c : Continuous g') :
    (∫ x in Set.Ioc α β,
      Complex.normSq (g x - (⨍ y, g y ∂(volume.restrict (Set.Ioc α β))))) ≤
      (β - α) ^ (2 : ℕ) * ∫ y in Set.Ioc α β, Complex.normSq (g' y) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc α β)
  have hcont : Continuous g :=
    continuous_iff_continuousAt.2 fun x => (hderiv x).continuousAt
  have hcenter : Integrable (fun x => Complex.normSq (g x - (⨍ y, g y ∂μ))) μ := by
    change IntegrableOn (fun x => Complex.normSq (g x - (⨍ y, g y ∂μ)))
      (Set.Ioc α β) volume
    exact (Complex.continuous_normSq.comp (hcont.sub continuous_const)).integrableOn_Ioc
  have hmin := integral_normSq_sub_average_le μ
    (show Integrable g μ by
      change IntegrableOn g (Set.Ioc α β) volume
      exact hcont.integrableOn_Ioc)
    hcenter (c := g α)
  have hpoin := integral_normSq_sub_left_le_of_hasDerivAt hαβ hderiv hg'c
  change (∫ x, Complex.normSq (g x - (⨍ y, g y ∂μ)) ∂μ) ≤ _
  exact hmin.trans hpoin
/-- Complex interval Poincaré with derivative and derivative-continuity required only on the cell. -/
theorem integral_normSq_sub_left_le_of_hasDerivAt_on_Icc {g g' : ℝ → ℂ} {α β : ℝ}
    (hαβ : α ≤ β) (hderiv : ∀ y ∈ Set.Icc α β, HasDerivAt g (g' y) y)
    (hg'c : ContinuousOn g' (Set.Icc α β)) :
    (∫ x in Set.Ioc α β, Complex.normSq (g x - g α)) ≤
      (β - α) ^ (2 : ℕ) * ∫ y in Set.Ioc α β, Complex.normSq (g' y) := by
  have hcont : ContinuousOn g (Set.Icc α β) := fun x hx =>
    (hderiv x hx).continuousAt.continuousWithinAt
  have hderivRe (y : ℝ) (hy : y ∈ Set.Icc α β) :
      HasDerivAt (fun t : ℝ => (g t).re) (g' y).re y := by
    simpa only [Function.comp_def, Complex.reCLM_apply] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt y (hderiv y hy)
  have hderivIm (y : ℝ) (hy : y ∈ Set.Icc α β) :
      HasDerivAt (fun t : ℝ => (g t).im) (g' y).im y := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt y (hderiv y hy)
  have hcontRe : ContinuousOn (fun y : ℝ => (g' y).re) (Set.Icc α β) := by
    fun_prop
  have hcontIm : ContinuousOn (fun y : ℝ => (g' y).im) (Set.Icc α β) := by
    fun_prop
  have hErrRe : IntegrableOn (fun x : ℝ => ((g x - g α).re) ^ (2 : ℕ)) (Set.Ioc α β) volume := by
    have hIcc : IntegrableOn (fun x : ℝ => ((g x - g α).re) ^ (2 : ℕ)) (Set.Icc α β) volume :=
      (by fun_prop : ContinuousOn (fun x : ℝ => ((g x - g α).re) ^ (2 : ℕ))
        (Set.Icc α β)).integrableOn_compact isCompact_Icc
    exact hIcc.mono_set Set.Ioc_subset_Icc_self
  have hErrIm : IntegrableOn (fun x : ℝ => ((g x - g α).im) ^ (2 : ℕ)) (Set.Ioc α β) volume := by
    have hIcc : IntegrableOn (fun x : ℝ => ((g x - g α).im) ^ (2 : ℕ)) (Set.Icc α β) volume :=
      (by fun_prop : ContinuousOn (fun x : ℝ => ((g x - g α).im) ^ (2 : ℕ))
        (Set.Icc α β)).integrableOn_compact isCompact_Icc
    exact hIcc.mono_set Set.Ioc_subset_Icc_self
  have hIntRe : IntervalIntegrable (fun y : ℝ => (g' y).re) volume α β := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hαβ]
    exact (hcontRe.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hIntIm : IntervalIntegrable (fun y : ℝ => (g' y).im) volume α β := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hαβ]
    exact (hcontIm.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hIntReSq : IntervalIntegrable (fun y : ℝ => (g' y).re ^ (2 : ℕ)) volume α β := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hαβ]
    exact ((hcontRe.pow 2).integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hIntImSq : IntervalIntegrable (fun y : ℝ => (g' y).im ^ (2 : ℕ)) volume α β := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hαβ]
    exact ((hcontIm.pow 2).integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hRe := integral_sub_left_sq_le_of_hasDerivAt_on_Icc hαβ hderivRe hIntRe hIntReSq hErrRe
  have hIm := integral_sub_left_sq_le_of_hasDerivAt_on_Icc hαβ hderivIm hIntIm hIntImSq hErrIm
  have hDerivRe : IntegrableOn (fun y : ℝ => (g' y).re ^ (2 : ℕ)) (Set.Ioc α β) volume :=
    (hcontRe.pow 2).integrableOn_compact isCompact_Icc |>.mono_set Set.Ioc_subset_Icc_self
  have hDerivIm : IntegrableOn (fun y : ℝ => (g' y).im ^ (2 : ℕ)) (Set.Ioc α β) volume :=
    (hcontIm.pow 2).integrableOn_compact isCompact_Icc |>.mono_set Set.Ioc_subset_Icc_self
  calc
    (∫ x in Set.Ioc α β, Complex.normSq (g x - g α)) =
        (∫ x in Set.Ioc α β, ((g x - g α).re) ^ (2 : ℕ) + ((g x - g α).im) ^ (2 : ℕ)) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x _
      change Complex.normSq (g x - g α) = _
      rw [Complex.normSq_apply]
      ring
    _ = (∫ x in Set.Ioc α β, ((g x - g α).re) ^ (2 : ℕ)) +
        ∫ x in Set.Ioc α β, ((g x - g α).im) ^ (2 : ℕ) := integral_add hErrRe hErrIm
    _ ≤ (β - α) ^ (2 : ℕ) * (∫ y in Set.Ioc α β, (g' y).re ^ (2 : ℕ)) +
        (β - α) ^ (2 : ℕ) * ∫ y in Set.Ioc α β, (g' y).im ^ (2 : ℕ) := add_le_add hRe hIm
    _ = (β - α) ^ (2 : ℕ) * (∫ y in Set.Ioc α β,
        (g' y).re ^ (2 : ℕ) + (g' y).im ^ (2 : ℕ)) := by
      rw [integral_add hDerivRe hDerivIm]
      ring
    _ = (β - α) ^ (2 : ℕ) * ∫ y in Set.Ioc α β, Complex.normSq (g' y) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioc
      intro y _
      change (g' y).re ^ (2 : ℕ) + (g' y).im ^ (2 : ℕ) = Complex.normSq (g' y)
      rw [Complex.normSq_apply]
      ring

/-- Complex cell means obey Poincaré with all regularity assumed only on the cell. -/
theorem integral_normSq_sub_average_le_of_hasDerivAt_on_Icc {g g' : ℝ → ℂ} {α β : ℝ}
    (hαβ : α ≤ β) (hderiv : ∀ y ∈ Set.Icc α β, HasDerivAt g (g' y) y)
    (hg'c : ContinuousOn g' (Set.Icc α β)) :
    (∫ x in Set.Ioc α β,
      Complex.normSq (g x - (⨍ y, g y ∂(volume.restrict (Set.Ioc α β))))) ≤
      (β - α) ^ (2 : ℕ) * ∫ y in Set.Ioc α β, Complex.normSq (g' y) := by
  have hcont : ContinuousOn g (Set.Icc α β) := fun x hx =>
    (hderiv x hx).continuousAt.continuousWithinAt
  let μ : Measure ℝ := volume.restrict (Set.Ioc α β)
  have hcenter : Integrable (fun x => Complex.normSq (g x - (⨍ y, g y ∂μ))) μ := by
    change IntegrableOn (fun x => Complex.normSq (g x - (⨍ y, g y ∂μ)))
      (Set.Ioc α β) volume
    have hIcc : IntegrableOn (fun x => Complex.normSq (g x - (⨍ y, g y ∂μ)))
        (Set.Icc α β) volume :=
      (by fun_prop : ContinuousOn (fun x : ℝ =>
        Complex.normSq (g x - (⨍ y, g y ∂μ))) (Set.Icc α β)).integrableOn_compact isCompact_Icc
    exact hIcc.mono_set Set.Ioc_subset_Icc_self
  have hmin := integral_normSq_sub_average_le μ
    (show Integrable g μ by
      change IntegrableOn g (Set.Ioc α β) volume
      exact (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self)
    hcenter (c := g α)
  have hpoin := integral_normSq_sub_left_le_of_hasDerivAt_on_Icc hαβ hderiv hg'c
  change (∫ x, Complex.normSq (g x - (⨍ y, g y ∂μ)) ∂μ) ≤ _
  exact hmin.trans hpoin


end GaloisForLFunctions.HTGeometry
