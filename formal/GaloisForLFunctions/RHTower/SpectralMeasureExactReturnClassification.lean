import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Exact-return classification for arbitrary spectral measures

For every probability measure on the real energy axis, unit survival at a
nonzero time is equivalent to locking almost every spectral phase to one
unit complex number.  Such a phase fibre is countable.  Consequently exact
return forces a countable full-mass spectral carrier, every atomless
probability spectrum has strictly subunit survival at every nonzero time,
and an exactly returning spectrum has no nonzero atomless submeasure.
-/

open scoped ENNReal InnerProductSpace
open Complex MeasureTheory Set Filter Function

noncomputable section

namespace RHTower.SpectralMemory

/-- Spectral phase accumulated by energy `x` at time `t`. -/
def spectralPhase (t x : ℝ) : ℂ :=
  Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)

/-- Every spectral phase lies on the complex unit circle. -/
theorem spectralPhase_norm (t x : ℝ) :
    ‖spectralPhase t x‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I (t * x)

/-- Spectral phase is continuous in energy. -/
theorem spectralPhase_continuous (t : ℝ) :
    Continuous (spectralPhase t) := by
  unfold spectralPhase
  fun_prop

/-- At nonzero time, the energies producing one prescribed phase form a
countable affine lattice. -/
theorem phaseFiber_countable {t : ℝ} (ht : t ≠ 0) (c : ℂ) :
    {x : ℝ | spectralPhase t x = c}.Countable := by
  let f : ℝ → ℂ := fun x => (((t * x : ℝ) : ℂ) * Complex.I)
  have hf : Function.Injective f := by
    intro x y hxy
    have hmul : t * x = t * y := by
      simpa [f] using congrArg Complex.im hxy
    exact mul_left_cancel₀ ht hmul
  exact ((countable_singleton c).preimage_cexp).preimage hf

private theorem eq_one_of_norm_eq_one_of_re_eq_one
    {z : ℂ} (hnorm : ‖z‖ = 1) (hre : z.re = 1) :
    z = 1 := by
  apply Complex.ext
  · simpa using hre
  · have hsquare :
        z.re * z.re + z.im * z.im = 1 := by
      rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hnorm]
      norm_num
    have him : z.im = 0 := by
      nlinarith [sq_nonneg z.im]
    simpa using him

private theorem spectralPhase_ae_eq_charFun_of_norm_eq_one
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ)
    (hnorm : ‖charFun μ t‖ = 1) :
    spectralPhase t =ᵐ[μ] const ℝ (charFun μ t) := by
  let f := BoundedContinuousFunction.innerProbChar (E := ℝ) t
  let c : ℂ := charFun μ t
  have hf : Integrable (fun x : ℝ => f x) μ := f.integrable μ
  have hzint : Integrable (fun x : ℝ => star c * f x) μ :=
    hf.const_mul _
  have hreal :
      (∫ x : ℝ, (star c * f x).re ∂μ) = 1 := by
    rw [← RCLike.re_eq_complex_re, integral_re hzint,
      integral_const_mul]
    change (star c * charFun μ t).re = 1
    simp [Complex.conj_mul', c, hnorm]
  have hnonneg :
      ∀ x : ℝ, 0 ≤ 1 - (star c * f x).re := by
    intro x
    have hre := Complex.re_le_norm (star c * f x)
    have hfNorm : ‖f x‖ = 1 := by
      simpa [f, spectralPhase,
        BoundedContinuousFunction.innerProbChar_apply,
        Real.inner_apply, mul_comm] using spectralPhase_norm t x
    have hprod : ‖star c * f x‖ = 1 := by
      rw [norm_mul, norm_star, show ‖c‖ = 1 by exact hnorm, hfNorm,
        one_mul]
    exact sub_nonneg.mpr (hre.trans_eq hprod)
  have hsubint :
      Integrable (fun x : ℝ => 1 - (star c * f x).re) μ :=
    (integrable_const 1).sub hzint.re
  have hzero :
      (∫ x : ℝ, 1 - (star c * f x).re ∂μ) = 0 := by
    rw [← RCLike.re_eq_complex_re,
      integral_sub (integrable_const 1) hzint.re,
      integral_const]
    rw [show (∫ x : ℝ, RCLike.re (star c * f x) ∂μ) = 1 by
      simpa only [RCLike.re_eq_complex_re] using hreal]
    simp
  have haeZero :
      (fun x : ℝ => 1 - (star c * f x).re) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg hnonneg hsubint).mp hzero
  filter_upwards [haeZero] with x hx
  have hre : (star c * f x).re = 1 := by
    exact (sub_eq_zero.mp hx).symm
  have hfNorm : ‖f x‖ = 1 := by
    simpa [f, spectralPhase,
      BoundedContinuousFunction.innerProbChar_apply,
      Real.inner_apply, mul_comm] using spectralPhase_norm t x
  have hprodNorm : ‖star c * f x‖ = 1 := by
    rw [norm_mul, norm_star, show ‖c‖ = 1 by exact hnorm, hfNorm,
      one_mul]
  have hone : star c * f x = 1 :=
    eq_one_of_norm_eq_one_of_re_eq_one hprodNorm hre
  have hcstar : c * star c = 1 := by
    simp [Complex.mul_conj', c, hnorm]
  change spectralPhase t x = c
  have hfx : f x = c := by
    calc
      f x = (c * star c) * f x := by rw [hcstar, one_mul]
      _ = c * (star c * f x) := by ring
      _ = c := by rw [hone, mul_one]
  simpa [f, spectralPhase,
    BoundedContinuousFunction.innerProbChar_apply] using hfx

/-- Universal strict alternative: spectral phases are almost everywhere
locked to their average, or the survival amplitude has norm strictly below
one. -/
theorem spectralPhase_ae_eq_const_or_norm_charFun_lt_one
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    spectralPhase t =ᵐ[μ] const ℝ (charFun μ t) ∨
      ‖charFun μ t‖ < 1 := by
  by_cases hnorm : ‖charFun μ t‖ = 1
  · exact Or.inl
      (spectralPhase_ae_eq_charFun_of_norm_eq_one μ t hnorm)
  · exact Or.inr
      (lt_of_le_of_ne (norm_charFun_le_one t) hnorm)

/-- Exact survival occurs precisely when almost every spectral energy has
one common accumulated phase. -/
theorem norm_charFun_eq_one_iff_phase_locked
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    ‖charFun μ t‖ = 1 ↔
      ∃ c : ℂ, ‖c‖ = 1 ∧ spectralPhase t =ᵐ[μ] const ℝ c := by
  constructor
  · intro hnorm
    refine ⟨charFun μ t, hnorm, ?_⟩
    rcases spectralPhase_ae_eq_const_or_norm_charFun_lt_one μ t with h | h
    · exact h
    · linarith
  · rintro ⟨c, hc, hae⟩
    have hint : charFun μ t = c := by
      rw [charFun_apply_real]
      simp_rw [← Complex.ofReal_mul]
      change (∫ x : ℝ, spectralPhase t x ∂μ) = c
      calc
        (∫ x : ℝ, spectralPhase t x ∂μ) =
            ∫ _x : ℝ, c ∂μ := integral_congr_ae hae
        _ = c := by simp
    rw [hint, hc]

/-- Every exact nonzero-time return has a countable full-mass spectral
carrier. -/
theorem exact_return_has_countable_spectral_carrier
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : t ≠ 0) (hreturn : ‖charFun μ t‖ = 1) :
    ∃ s : Set ℝ, s.Countable ∧ μ s = 1 := by
  obtain ⟨c, _hc, hae⟩ :=
    (norm_charFun_eq_one_iff_phase_locked μ t).mp hreturn
  let s : Set ℝ := {x : ℝ | spectralPhase t x = c}
  have hs : s.Countable := phaseFiber_countable ht c
  have haes : ∀ᵐ x ∂μ, x ∈ s := by
    simpa [s, EventuallyEq, const] using hae
  have hsm : MeasurableSet s := by
    exact (measurableSet_singleton c).preimage
      (spectralPhase_continuous t).measurable
  refine ⟨s, hs, ?_⟩
  have hmeasure : μ s = μ Set.univ :=
    (ae_mem_iff_measure_eq hsm.nullMeasurableSet).mp haes
  simpa using hmeasure

/-- An atomless probability spectral measure has strictly subunit survival
at every nonzero time. -/
theorem atomless_spectral_measure_never_exactly_returns
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {t : ℝ} (ht : t ≠ 0) :
    ‖charFun μ t‖ < 1 := by
  by_contra hnot
  have hreturn : ‖charFun μ t‖ = 1 :=
    le_antisymm (norm_charFun_le_one t) (not_lt.mp hnot)
  obtain ⟨s, hs, hmass⟩ :=
    exact_return_has_countable_spectral_carrier μ ht hreturn
  have hzero : μ s = 0 := hs.measure_zero μ
  rw [hzero] at hmass
  norm_num at hmass

/-- Strong mixed-spectrum boundary: if a probability spectrum returns
exactly at a nonzero time, every atomless submeasure is zero.  Thus any
continuous component, however small, forbids exact return. -/
theorem exact_return_has_no_atomless_submeasure
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass ν]
    {t : ℝ} (ht : t ≠ 0) (hreturn : ‖charFun μ t‖ = 1)
    (hνμ : ν ≤ μ) :
    ν = 0 := by
  obtain ⟨s, hs, hmass⟩ :=
    exact_return_has_countable_spectral_carrier μ ht hreturn
  have hμcomp : μ sᶜ = 0 := by
    rw [measure_compl hs.measurableSet (by finiteness), hmass]
    simp
  have hνs : ν s = 0 := hs.measure_zero ν
  have hνcomp : ν sᶜ = 0 :=
    le_antisymm ((hνμ (sᶜ)).trans_eq hμcomp) (by simp)
  rw [← Measure.measure_univ_eq_zero]
  calc
    ν Set.univ = ν (s ∪ sᶜ) := by rw [union_compl_self]
    _ = ν s + ν sᶜ :=
      measure_union disjoint_compl_right hs.measurableSet.compl
    _ = 0 := by rw [hνs, hνcomp, add_zero]

end RHTower.SpectralMemory
