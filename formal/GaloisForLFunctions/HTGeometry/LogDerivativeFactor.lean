import GaloisForLFunctions.HTGeometry.LogDerivativeBound
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# The logarithmic derivative across a zero factorization

Extracting the zeros of a function splits its logarithmic derivative into an explicit rational part
and the logarithmic derivative of the zero-free cofactor.  The rational part is the sum of
`m_a / (· - a)` over the zeros, whose proximity is governed by the zero count; the cofactor is
covered by the Borel--Carathéodory estimate.

Together with `LogDerivativeBound` this reduces the general logarithmic-derivative estimate to
counting.
-/

open Metric

namespace GaloisForLFunctions.HTGeometry

/-- The logarithmic derivative of a linear factor. -/
theorem logDeriv_sub_const (a z : ℂ) : logDeriv (fun w : ℂ => w - a) z = 1 / (z - a) := by
  have hd : HasDerivAt (fun w : ℂ => w - a) 1 z := (hasDerivAt_id z).sub_const a
  rw [logDeriv_apply, hd.deriv]

/-- **The logarithmic derivative across a zero factorization.**  If `f = ∏ (· - a)^{m a} · h` on an
open set with `h` zero free, then away from the zeros

  `f'/f = ∑ m_a/(· - a) + h'/h`. -/
theorem logDeriv_of_factor {f h : ℂ → ℂ} {T : Finset ℂ} {m : ℂ → ℕ} {U : Set ℂ}
    (hU : IsOpen U) (hh : DifferentiableOn ℂ h U) (hhne : ∀ z ∈ U, h z ≠ 0)
    (hfac : ∀ z ∈ U, f z = (∏ a ∈ T, (z - a) ^ (m a)) * h z)
    {z : ℂ} (hz : z ∈ U) (hzne : ∀ a ∈ T, z ≠ a) :
    logDeriv f z = (∑ a ∈ T, (m a : ℂ) / (z - a)) + logDeriv h z := by
  classical
  have hnhds : U ∈ nhds z := hU.mem_nhds hz
  have hhat : DifferentiableAt ℂ h z := hh.differentiableAt hnhds
  have hne : ∀ a ∈ T, ((z - a) : ℂ) ≠ 0 := fun a ha => sub_ne_zero.mpr (hzne a ha)
  have hPd : DifferentiableAt ℂ (fun w : ℂ => ∏ a ∈ T, (w - a) ^ (m a)) z := by
    refine DifferentiableAt.fun_finsetProd ?_
    intro a _
    exact ((differentiableAt_id).sub_const a).pow (m a)
  have hP0 : (∏ a ∈ T, (z - a) ^ (m a)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a ha => pow_ne_zero _ (hne a ha)
  have heq : f =ᶠ[nhds z] fun w => (∏ a ∈ T, (w - a) ^ (m a)) * h w := by
    filter_upwards [hnhds] with w hw
    exact hfac w hw
  have hlog : logDeriv f z = logDeriv (fun w => (∏ a ∈ T, (w - a) ^ (m a)) * h w) z := by
    rw [logDeriv_apply, logDeriv_apply, heq.deriv_eq, heq.eq_of_nhds]
  rw [hlog, logDeriv_mul z hP0 (hhne z hz) hPd hhat]
  congr 1
  rw [logDeriv_prod (𝕜 := ℂ) (𝕜' := ℂ) (s := T) (f := fun a w : ℂ => (w - a) ^ (m a)) (x := z)
    (fun a ha => pow_ne_zero _ (hne a ha))
    (fun a _ => ((differentiableAt_id).sub_const a).pow (m a))]
  refine Finset.sum_congr rfl ?_
  intro a ha
  rw [logDeriv_fun_pow (𝕜 := ℂ) (𝕜' := ℂ) (f := fun w : ℂ => w - a) (x := z) (by fun_prop) (m a),
    logDeriv_sub_const]
  field_simp

/-- **The rational part is bounded by the zero count over the distances.** -/
theorem norm_sum_multiplicity_div_le {T : Finset ℂ} {m : ℂ → ℕ} {z : ℂ} {d : ℝ} (hd : 0 < d)
    (hfar : ∀ a ∈ T, d ≤ ‖z - a‖) :
    ‖∑ a ∈ T, (m a : ℂ) / (z - a)‖ ≤ (∑ a ∈ T, (m a : ℝ)) / d := by
  classical
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_div]
  refine Finset.sum_le_sum ?_
  intro a ha
  rw [norm_div]
  have hnum : ‖(m a : ℂ)‖ = (m a : ℝ) := by
    rw [Complex.norm_natCast]
  rw [hnum]
  have hpos : 0 < ‖z - a‖ := lt_of_lt_of_le hd (hfar a ha)
  rw [div_le_div_iff₀ hpos hd]
  have hm0 : (0 : ℝ) ≤ (m a : ℝ) := Nat.cast_nonneg _
  nlinarith [hfar a ha, hm0]

/-- **The pointwise proximity integrand of the logarithmic derivative.**  Away from the zeros,

  `log⁺‖f'/f‖ ≤ log 2 + log |T| + ∑_a (log m_a + log⁺(1/‖z − a‖)) + log⁺‖h'/h‖`.

Every term on the right integrates to something controlled: the zero terms by
`circleAverage_negPart_log_norm_sub_le`, the cofactor term by the Borel--Carathéodory estimate. -/
theorem posLog_norm_logDeriv_le_of_factor {f h : ℂ → ℂ} {T : Finset ℂ} {m : ℂ → ℕ} {U : Set ℂ}
    (hU : IsOpen U) (hh : DifferentiableOn ℂ h U) (hhne : ∀ z ∈ U, h z ≠ 0)
    (hfac : ∀ z ∈ U, f z = (∏ a ∈ T, (z - a) ^ (m a)) * h z)
    {z : ℂ} (hz : z ∈ U) (hzne : ∀ a ∈ T, z ≠ a) :
    Real.posLog ‖deriv f z / f z‖
      ≤ Real.log 2 + (Real.log (T.card : ℝ)
          + ∑ a ∈ T, (Real.log (m a : ℝ) + Real.posLog ‖z - a‖⁻¹))
        + Real.posLog ‖deriv h z / h z‖ := by
  classical
  have hsplit := logDeriv_of_factor hU hh hhne hfac hz hzne
  rw [logDeriv_apply, logDeriv_apply] at hsplit
  -- the triangle inequality on the split
  have htri : ‖deriv f z / f z‖
      ≤ ‖∑ a ∈ T, (m a : ℂ) / (z - a)‖ + ‖deriv h z / h z‖ := by
    rw [hsplit]
    exact norm_add_le _ _
  have hstep₁ : Real.posLog ‖deriv f z / f z‖
      ≤ Real.log 2 + Real.posLog ‖∑ a ∈ T, (m a : ℂ) / (z - a)‖
        + Real.posLog ‖deriv h z / h z‖ :=
    le_trans (Real.posLog_le_posLog (norm_nonneg _) htri) Real.posLog_add
  -- the rational part
  have hnormS : ‖∑ a ∈ T, (m a : ℂ) / (z - a)‖ ≤ ∑ a ∈ T, (m a : ℝ) * ‖z - a‖⁻¹ := by
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum ?_
    intro a _
    rw [norm_div, Complex.norm_natCast, div_eq_mul_inv]
  have hstep₂ : Real.posLog ‖∑ a ∈ T, (m a : ℂ) / (z - a)‖
      ≤ Real.log (T.card : ℝ) + ∑ a ∈ T, (Real.log (m a : ℝ) + Real.posLog ‖z - a‖⁻¹) := by
    refine le_trans (Real.posLog_le_posLog (norm_nonneg _) hnormS) ?_
    refine le_trans (Real.posLog_sum T _) ?_
    have hterm : ∀ a ∈ T, Real.posLog ((m a : ℝ) * ‖z - a‖⁻¹)
        ≤ Real.log (m a : ℝ) + Real.posLog ‖z - a‖⁻¹ := fun a _ => Real.posLog_nat_mul
    have := Finset.sum_le_sum hterm
    linarith
  linarith

end GaloisForLFunctions.HTGeometry
