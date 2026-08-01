import GaloisForLFunctions.HTGeometry.SpikeSobolev
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Square bound for a convolution kernel on a finite interval

A convolution kernel `K (t, s) = g (t - s)` on the square `[0,a]²` has square integral controlled
by the square integral of `g` on `[-a,a]`:

`∫₀ᵃ ∫₀ᵃ g (t - s)² ds dt ≤ a * ∫₋ₐᵃ g² `.

The mechanism is the substitution `u = t - s`, which turns the inner integral into an integral over
`[t - a, t]`, a subinterval of `[-a, a]` for every `t` in `[0, a]`; the integrand is a square, hence
nonnegative, so enlarging the interval only increases it.

This is the finiteness input needed to regard such a kernel as a Hilbert–Schmidt kernel: for a
continuous `g` the right-hand side is finite, so the kernel is square integrable on the square.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory intervalIntegral

variable {g : ℝ → ℝ}

/-- The inner convolution integral is an integral of `g²` over a shifted interval. -/
theorem integral_sq_sub_eq (a t : ℝ) :
    ∫ s in (0 : ℝ)..a, (g (t - s)) ^ 2 = ∫ u in (t - a)..t, (g u) ^ 2 := by
  have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := a)
    (fun x => (g x) ^ 2) t
  simpa using h

/-- For `t` in `[0, a]` the shifted interval sits inside `[-a, a]`, and the integrand is a square,
so the inner integral is bounded by the full square integral. -/
theorem integral_sq_sub_le (hg : Continuous g) {a t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) a) :
    ∫ s in (0 : ℝ)..a, (g (t - s)) ^ 2 ≤ ∫ u in (-a)..a, (g u) ^ 2 := by
  obtain ⟨ht0, hta⟩ := ht
  rw [integral_sq_sub_eq a t]
  refine intervalIntegral.integral_mono_interval (by linarith) (by linarith) hta ?_ ?_
  · filter_upwards with u using sq_nonneg (g u)
  · exact ((hg.pow 2).intervalIntegrable _ _)

/-- The primitive of `g²`, used to identify the inner integral as a continuous function of the
outer variable. -/
theorem continuous_primitive_sq (hg : Continuous g) :
    Continuous fun x : ℝ => ∫ u in (0 : ℝ)..x, (g u) ^ 2 :=
  intervalIntegral.continuous_primitive (fun _ _ => (hg.pow 2).intervalIntegrable _ _) 0

/-- The inner convolution integral depends continuously on the outer variable. -/
theorem continuous_integral_sq_sub (hg : Continuous g) (a : ℝ) :
    Continuous fun t : ℝ => ∫ s in (0 : ℝ)..a, (g (t - s)) ^ 2 := by
  have hprim := continuous_primitive_sq hg
  have hEq : (fun t : ℝ => ∫ s in (0 : ℝ)..a, (g (t - s)) ^ 2)
      = fun t : ℝ => (∫ u in (0 : ℝ)..t, (g u) ^ 2) - ∫ u in (0 : ℝ)..(t - a), (g u) ^ 2 := by
    funext t
    rw [integral_sq_sub_eq a t]
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (μ := volume) (a := (0 : ℝ)) (b := t - a) (c := t)
      ((hg.pow 2).intervalIntegrable _ _) ((hg.pow 2).intervalIntegrable _ _)
    simp only [Pi.pow_apply] at hadd
    linarith [hadd]
  rw [hEq]
  exact hprim.sub (hprim.comp (continuous_id.sub continuous_const))

/-- **Square bound for a convolution kernel on a finite interval.**  The square integral of
`(t, s) ↦ g (t - s)` over `[0,a]²` is at most `a` times the square integral of `g` over `[-a,a]`. -/
theorem integral_integral_sq_sub_le (hg : Continuous g) {a : ℝ} (ha : 0 ≤ a) :
    (∫ t in (0 : ℝ)..a, ∫ s in (0 : ℝ)..a, (g (t - s)) ^ 2)
      ≤ a * ∫ u in (-a)..a, (g u) ^ 2 := by
  have hmono : ∫ t in (0 : ℝ)..a, (∫ s in (0 : ℝ)..a, (g (t - s)) ^ 2)
      ≤ ∫ _t in (0 : ℝ)..a, ∫ u in (-a)..a, (g u) ^ 2 := by
    refine intervalIntegral.integral_mono_on ha ?_ intervalIntegrable_const ?_
    · exact (continuous_integral_sq_sub hg a).intervalIntegrable _ _
    · intro t ht
      exact integral_sq_sub_le hg ht
  calc ∫ t in (0 : ℝ)..a, (∫ s in (0 : ℝ)..a, (g (t - s)) ^ 2)
      ≤ ∫ _t in (0 : ℝ)..a, ∫ u in (-a)..a, (g u) ^ 2 := hmono
    _ = a * ∫ u in (-a)..a, (g u) ^ 2 := by
        rw [intervalIntegral.integral_const]
        simp

/-! ## A Dirac component blocks compactness

The bound above makes a *continuous* convolution kernel Hilbert–Schmidt, hence compact.  The
complementary fact is that a kernel carrying a Dirac mass at the origin can never be compact: such a
kernel contributes a nonzero multiple of the identity, and on an infinite-dimensional space no
operator of the form `c • id + K` with `c ≠ 0` and `K` compact is compact.  This is the obstruction
that separates a convolution kernel given by a function from one given by a distribution with an
atom at `0`. -/

section DiracComponent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **An identity component blocks compactness.**  On an infinite-dimensional space, `c • id + K`
with `c ≠ 0` and `K` compact is never a compact operator: subtracting `K` would make `c • id`
compact, hence the identity compact, forcing finite dimension. -/
theorem not_isCompactOperator_smul_id_add
    (hinf : ¬ FiniteDimensional ℂ E) {c : ℂ} (hc : c ≠ 0)
    {K : E →L[ℂ] E} (hK : IsCompactOperator K) :
    ¬ IsCompactOperator (c • ContinuousLinearMap.id ℂ E + K) := by
  intro h
  have heq : (⇑(c • ContinuousLinearMap.id ℂ E + K) - ⇑K : E → E)
      = ⇑(c • ContinuousLinearMap.id ℂ E : E →L[ℂ] E) := by
    funext x
    simp
  have hsmul : IsCompactOperator ((c • ContinuousLinearMap.id ℂ E : E →L[ℂ] E)) := by
    rw [← heq]
    exact h.sub hK
  have hid : IsCompactOperator ((ContinuousLinearMap.id ℂ E : E →L[ℂ] E)) := by
    have hinv : c⁻¹ • (c • ContinuousLinearMap.id ℂ E : E →L[ℂ] E)
        = ContinuousLinearMap.id ℂ E := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [← hinv]
    exact hsmul.smul c⁻¹
  exact hinf (FiniteDimensional.of_isCompactOperator_id hid)

end DiracComponent

end GaloisForLFunctions.HTGeometry
