import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Exact norm of multiplication by an arbitrary L-infinity symbol on the line

The Holder construction already used by the polynomial sign cone gives the
complex multiplication operator. Finite positive-measure indicator probes
recover its full essential-supremum norm, without continuity of the symbol.
-/

open MeasureTheory Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The existing Holder multiplication construction on complex Lebesgue L2. -/
def lineLinftyMultiplier : Lp ℂ ∞ (volume : Measure ℝ) →L[ℂ]
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (ContinuousLinearMap.lsmul ℂ ℂ).holderL volume ∞ 2 2

/-- The operator acts by the actual measurable symbol almost everywhere. -/
theorem lineLinftyMultiplier_ae (g : Lp ℂ ∞ (volume : Measure ℝ))
    (u : Lp ℂ 2 (volume : Measure ℝ)) :
    (lineLinftyMultiplier g u : ℝ → ℂ) =ᵐ[volume] fun x => g x * u x := by
  exact (ContinuousLinearMap.lsmul ℂ ℂ).coeFn_holder g u

/-- Holder gives the sharp candidate upper bound. -/
theorem norm_lineLinftyMultiplier_le (g : Lp ℂ ∞ (volume : Measure ℝ)) :
    ‖lineLinftyMultiplier g‖ ≤ ‖g‖ := by
  have h : ‖lineLinftyMultiplier‖ ≤ 1 := by
    exact (ContinuousLinearMap.norm_holderL_le _).trans (by simp)
  exact (lineLinftyMultiplier.le_opNorm g).trans (by simpa using mul_le_mul_of_nonneg_right h (norm_nonneg g))

private theorem linfty_norm_le_of_ae (g : Lp ℂ ∞ (volume : Measure ℝ))
    (c : ℝ) (hc : 0 ≤ c) (h : ∀ᵐ x ∂volume, ‖g x‖ ≤ c) : ‖g‖ ≤ c := by
  have he := eLpNormEssSup_le_of_ae_bound h
  rw [Lp.norm_def, eLpNorm_exponent_top]
  exact ENNReal.toReal_le_of_le_ofReal hc he

/-- Multiplication on L2 remembers the entire L-infinity norm, including discontinuous symbols. -/
theorem norm_lineLinftyMultiplier (g : Lp ℂ ∞ (volume : Measure ℝ)) :
    ‖lineLinftyMultiplier g‖ = ‖g‖ := by
  apply le_antisymm (norm_lineLinftyMultiplier_le g)
  by_contra hn
  have hlt : ‖lineLinftyMultiplier g‖ < ‖g‖ := lt_of_not_ge hn
  obtain ⟨c, hTc, hcg⟩ := exists_between hlt
  have hc : 0 < c := (norm_nonneg _).trans_lt hTc
  have hnot : ¬ ∀ᵐ x ∂volume, ‖g x‖ ≤ c := by
    intro h
    exact hcg.not_ge (linfty_norm_le_of_ae g c hc.le h)
  have hpos : 0 < volume {x : ℝ | c < ‖g x‖} := by
    apply pos_iff_ne_zero.2
    simpa only [ae_iff, not_le] using hnot
  obtain ⟨n, hn⟩ := (Measure.exists_measure_inter_spanningSets_pos _).2 hpos
  let S : Set ℝ := {x : ℝ | c < ‖g x‖} ∩ spanningSets (volume : Measure ℝ) n
  have hSm : MeasurableSet S :=
    (measurableSet_lt measurable_const (Lp.stronglyMeasurable g).measurable.norm).inter
      (measurableSet_spanningSets volume n)
  have hSfin : volume S ≠ ∞ :=
    ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top volume n)).ne
  have hSpos : 0 < volume S := hn
  let u : Lp ℂ 2 (volume : Measure ℝ) := indicatorConstLp 2 hSm hSfin (1 : ℂ)
  let v : Lp ℂ 2 (volume : Measure ℝ) := indicatorConstLp 2 hSm hSfin (c : ℂ)
  have hu : 0 < ‖u‖ := by
    dsimp [u]
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    simpa only [norm_one, one_mul, measureReal_def] using
      Real.rpow_pos_of_pos (ENNReal.toReal_pos hSpos.ne' hSfin) (1 / (2 : ℝ≥0∞).toReal)
  have hv : ‖v‖ = c * ‖u‖ := by
    dsimp [u, v]
    rw [norm_indicatorConstLp (by norm_num) (by norm_num),
      norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp [Complex.norm_real, abs_of_pos hc]
  have hlow : ‖v‖ ≤ ‖lineLinftyMultiplier g u‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [lineLinftyMultiplier_ae g u,
      indicatorConstLp_coeFn (p := 2) (hs := hSm) (hμs := hSfin) (c := (1 : ℂ)),
      indicatorConstLp_coeFn (p := 2) (hs := hSm) (hμs := hSfin) (c := (c : ℂ))]
      with x h0 h1 h2
    change u x = S.indicator (fun _ => (1 : ℂ)) x at h1
    change v x = S.indicator (fun _ => (c : ℂ)) x at h2
    rw [h0, h1, h2]
    by_cases hx : x ∈ S
    · simp only [indicator_of_mem hx, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
      exact hx.1.le
    · simp only [indicator_of_notMem hx, mul_zero, norm_zero, le_refl]
  have hup := (lineLinftyMultiplier g).le_opNorm u
  rw [hv] at hlow
  nlinarith

/-- The multiplication representation is a linear isometry. -/
def lineLinftyMultiplierIsometry : Lp ℂ ∞ (volume : Measure ℝ) →ₗᵢ[ℂ]
    (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) :=
  { lineLinftyMultiplier.toLinearMap with norm_map' := norm_lineLinftyMultiplier }

/-- Exact operator distance equals essential-supremum distance of symbols. -/
theorem dist_lineLinftyMultiplier (g h : Lp ℂ ∞ (volume : Measure ℝ)) :
    dist (lineLinftyMultiplier g) (lineLinftyMultiplier h) = dist g h :=
  lineLinftyMultiplierIsometry.isometry.dist_eq g h

/-- No nonzero measurable symbol disappears in the multiplication representation. -/
theorem lineLinftyMultiplier_injective : Function.Injective lineLinftyMultiplier :=
  lineLinftyMultiplierIsometry.injective

/-- Equality of multiplication operators is exactly almost-everywhere equality of symbols. -/
theorem lineLinftyMultiplier_eq_iff_ae (g h : Lp ℂ ∞ (volume : Measure ℝ)) :
    lineLinftyMultiplier g = lineLinftyMultiplier h ↔ (g : ℝ → ℂ) =ᵐ[volume] h := by
  constructor
  · intro he
    rw [lineLinftyMultiplier_injective he]
  · intro he
    exact congrArg lineLinftyMultiplier (Lp.ext he)

end
end GaloisForLFunctions.HTGeometry
