import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier
import GaloisForLFunctions.RHTower.SoninEvenCarrier

/-!
# Bounded multipliers on the even Sonin carrier

An even bounded measurable symbol commutes with the reflection, so multiplication by it preserves
the even carrier and restricts to a continuous linear map there.  The physical cutoffs are the
special case of a symmetric indicator symbol.
-/

noncomputable section

namespace RHTower

open MeasureTheory

/-- Multiplication by an even symbol commutes with the reflection. -/
theorem l2Reflection_lpBoundedMulCLM {φ : ℝ → ℂ} (hφ : Measurable φ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C) (heven : ∀ x, φ (-x) = φ x) (f : SoninL2) :
    l2Reflection (lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) hφ hC0 hC f) =
      lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) hφ hC0 hC (l2Reflection f) := by
  apply Lp.ext
  have hneg :=
    (lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ)) hφ hC0 hC f).comp_tendsto
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [
    l2Reflection_ae (lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) hφ hC0 hC f),
    hneg,
    lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ)) hφ hC0 hC (l2Reflection f),
    l2Reflection_ae f
  ] with x href hmul hright hf
  have hmul' :
      (lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) hφ hC0 hC f : ℝ → ℂ) (-x) =
        φ (-x) * (f : ℝ → ℂ) (-x) := by
    simpa [Function.comp_apply] using hmul
  rw [href, hmul', heven, hright, hf]

/-- Multiplication by an even bounded symbol preserves the even carrier. -/
theorem lpBoundedMulCLM_mapsTo_evenSubspace {φ : ℝ → ℂ} (hφ : Measurable φ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C) (heven : ∀ x, φ (-x) = φ x) :
    Set.MapsTo (lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) hφ hC0 hC)
      evenSubspace evenSubspace := by
  intro f hf
  apply (mem_evenSubspace_iff _).mpr
  rw [l2Reflection_lpBoundedMulCLM hφ hC0 hC heven, (mem_evenSubspace_iff f).mp hf]

/-- Multiplication by an even bounded measurable symbol on the even Sonin carrier. -/
def evenBoundedMul {φ : ℝ → ℂ} (hφ : Measurable φ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C) (heven : ∀ x, φ (-x) = φ x) :
    evenSubspace →L[ℂ] evenSubspace :=
  (lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) hφ hC0 hC).restrict
    (lpBoundedMulCLM_mapsTo_evenSubspace hφ hC0 hC heven)

@[simp] theorem coe_evenBoundedMul_apply {φ : ℝ → ℂ} (hφ : Measurable φ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C) (heven : ∀ x, φ (-x) = φ x) (f : evenSubspace) :
    ((evenBoundedMul hφ hC0 hC heven f : evenSubspace) : SoninL2) =
      lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) hφ hC0 hC f := rfl

theorem evenBoundedMul_coeFn {φ : ℝ → ℂ} (hφ : Measurable φ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C) (heven : ∀ x, φ (-x) = φ x) (f : evenSubspace) :
    (((evenBoundedMul hφ hC0 hC heven f : evenSubspace) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => φ x * ((f : SoninL2) : ℝ → ℂ) x := by
  rw [coe_evenBoundedMul_apply]
  exact lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ)) hφ hC0 hC f

end RHTower

namespace RHTower

open MeasureTheory
open scoped ENNReal

/-- An operator on the even carrier acting almost everywhere as multiplication by a bounded symbol
has operator norm at most the symbol bound. -/
theorem norm_le_of_evenCoeFn_mul {T : evenSubspace →L[ℂ] evenSubspace} {ψ : ℝ → ℂ}
    {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ x, ‖ψ x‖ ≤ K)
    (hT : ∀ f : evenSubspace, (((T f : evenSubspace) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => ψ x * ((f : SoninL2) : ℝ → ℂ) x) :
    ‖T‖ ≤ K := by
  refine ContinuousLinearMap.opNorm_le_bound _ hK0 fun f => ?_
  have hnormT : ‖T f‖ = ‖((T f : evenSubspace) : SoninL2)‖ := rfl
  have hnormf : ‖f‖ = ‖((f : evenSubspace) : SoninL2)‖ := rfl
  rw [hnormT, hnormf, Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (hT f)]
  have hle := eLpNorm_mul_le_of_bound (p := 2) (μ := (volume : Measure ℝ)) hK0 hK
    (((f : evenSubspace) : SoninL2) : ℝ → ℂ)
  have hfin : eLpNorm ((((f : evenSubspace) : SoninL2) : ℝ → ℂ)) 2 volume ≠ ∞ :=
    Lp.eLpNorm_ne_top _
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by simp [enorm_eq_nnnorm]) hfin) hle
  refine h.trans ?_
  rw [ENNReal.toReal_mul]
  have hnorm : (‖(K : ℝ)‖ₑ).toReal = K := by
    simp [enorm_eq_nnnorm, Real.norm_eq_abs, abs_of_nonneg hK0]
  rw [hnorm]

/-- Almost-everywhere action of a physical cutoff on the even carrier. -/
theorem evenIndicatorCutoff_coeFn (s : ℝ) (f : evenSubspace) :
    (((evenIndicatorCutoff s f : evenSubspace) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun t => (centralInterval s).indicator (fun _ => (1 : ℂ)) t *
        (((f : evenSubspace) : SoninL2) : ℝ → ℂ) t := by
  rw [coe_evenIndicatorCutoff_apply]
  filter_upwards [indicatorCutoff_ae (centralInterval s) (measurableSet_centralInterval s)
    ((f : evenSubspace) : SoninL2)] with t ht
  rw [ht]
  by_cases h : t ∈ centralInterval s <;> simp [h]

end RHTower

namespace RHTower

open MeasureTheory
open scoped ENNReal

/-- Almost-everywhere action of a finite sum of multiplier-like operators. -/
theorem evenCoeFn_sum {ι : Type*} (s : Finset ι)
    (T : ι → evenSubspace →L[ℂ] evenSubspace) (ψ : ι → ℝ → ℂ) (f : evenSubspace)
    (h : ∀ i ∈ s, (((T i f : evenSubspace) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun t => ψ i t * (((f : evenSubspace) : SoninL2) : ℝ → ℂ) t) :
    ((((∑ i ∈ s, T i) f : evenSubspace) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun t => (∑ i ∈ s, ψ i t) * (((f : evenSubspace) : SoninL2) : ℝ → ℂ) t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      have h0 : (((0 : evenSubspace →L[ℂ] evenSubspace) f : evenSubspace) : SoninL2) = 0 := by
        simp
      rw [h0]
      filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with t ht
      rw [ht]
      simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      have happ : (((T i + ∑ j ∈ s, T j) f : evenSubspace) : SoninL2) =
          ((T i f : evenSubspace) : SoninL2) +
            (((∑ j ∈ s, T j) f : evenSubspace) : SoninL2) := by
        simp
      rw [happ]
      have hih := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      filter_upwards [Lp.coeFn_add ((T i f : evenSubspace) : SoninL2)
          (((∑ j ∈ s, T j) f : evenSubspace) : SoninL2),
        h i (Finset.mem_insert_self i s), hih] with t hadd h1 h2
      rw [hadd, Pi.add_apply, h1, h2, Finset.sum_insert hi, add_mul]

/-- Almost-everywhere action of a scalar multiple of a cutoff difference. -/
theorem evenSmulCutoffDiff_coeFn (c : ℂ) (u v : ℝ) (f : evenSubspace) :
    ((((c • (evenIndicatorCutoff v - evenIndicatorCutoff u)) f : evenSubspace) :
        SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun t => (c * ((centralInterval v).indicator (fun _ => (1 : ℂ)) t -
          (centralInterval u).indicator (fun _ => (1 : ℂ)) t)) *
        (((f : evenSubspace) : SoninL2) : ℝ → ℂ) t := by
  have happ : ((((c • (evenIndicatorCutoff v - evenIndicatorCutoff u)) f : evenSubspace) :
      SoninL2)) =
      c • (((evenIndicatorCutoff v f : evenSubspace) : SoninL2) -
        ((evenIndicatorCutoff u f : evenSubspace) : SoninL2)) := by
    simp
  rw [happ]
  filter_upwards [Lp.coeFn_smul c (((evenIndicatorCutoff v f : evenSubspace) : SoninL2) -
      ((evenIndicatorCutoff u f : evenSubspace) : SoninL2)),
    Lp.coeFn_sub ((evenIndicatorCutoff v f : evenSubspace) : SoninL2)
      ((evenIndicatorCutoff u f : evenSubspace) : SoninL2),
    evenIndicatorCutoff_coeFn v f, evenIndicatorCutoff_coeFn u f] with t h1 h2 h3 h4
  rw [h1, Pi.smul_apply, h2, Pi.sub_apply, h3, h4, smul_eq_mul]
  ring

end RHTower
