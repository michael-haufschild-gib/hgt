import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerGaussianSourceApproximation
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerStrongLogOperatorContinuity

/-! # Summing contour blocks in the original Meyer topology

Summability in every defining weighted derivative gauge gives an actual
all-weight source limit. Weighted Mellin-strip control pays these gauges.
This uses completeness of the original source, not a spectral completion.
-/

open Complex MeasureTheory Set Filter Topology TopologicalSpace

namespace RHTower
noncomputable section
open scoped DeningerMeyerNaturalTopology BoundedContinuousFunction

/-- Completeness and the defining gauges give an intrinsic series criterion. -/
theorem deningerMeyerStrongLog_summable_of_gauges
    {ι : Type*} {g : ι → DeningerMeyerStrongLogTarget}
    (hg : ∀ n k, Summable (fun i => deningerMeyerStrongLogGaugeLinear n k (g i))) :
    Summable g := by
  let e : DeningerMeyerStrongLogTarget →ₗ[ℂ] (ℕ × ℤ → ℝ →ᵇ ℂ) :=
    LinearMap.pi (fun p : ℕ × ℤ => deningerMeyerStrongLogGaugeLinear p.1 p.2)
  have hi : IsInducing e := inducing_iInf_to_pi
    (fun p : ℕ × ℤ => deningerMeyerStrongLogGaugeLinear p.1 p.2)
  have hu := AddMonoidHom.isUniformInducing_of_isInducing
    (f := e.toAddMonoidHom) hi
  have hs : Summable (fun i => e (g i)) := Pi.summable.mpr (fun p => hg p.1 p.2)
  apply summable_iff_cauchySeq_finset.mpr
  have hc := summable_iff_cauchySeq_finset.mp hs
  change Cauchy (Filter.map (fun s : Finset ι => ∑ i ∈ s, e (g i)) atTop) at hc
  have he : (fun s : Finset ι => ∑ i ∈ s, e (g i)) =
      e ∘ (fun s : Finset ι => ∑ i ∈ s, g i) := by
    funext s
    simp only [Function.comp_apply, map_sum]
  rw [he, ← Filter.map_map] at hc
  exact hu.cauchy_map_iff.mp hc

def deningerMeyerStripGaugeConstant (n : ℕ) (k : ℤ) : ℝ :=
  (1/(2*Real.pi)) * (|(k : ℝ)|+1)^n * ∫ y : ℝ, (1+y^2)⁻¹

theorem deningerMeyerStripGaugeConstant_nonneg (n : ℕ) (k : ℤ) :
    0 ≤ deningerMeyerStripGaugeConstant n k := by
  unfold deningerMeyerStripGaugeConstant
  apply mul_nonneg (by positivity)
  exact integral_nonneg (fun y => by positivity)

/-- A single weighted Mellin-line estimate controls an original source gauge. -/
theorem deningerMeyerInverseMellinSource_gauge_le_weighted
    {F : ℂ → ℂ} (hF : DeningerEntireMellinRegular F) (n : ℕ) (k : ℤ) {M : ℝ}
    (hM : ∀ y : ℝ, ‖F ((k : ℂ)+y*I)‖*(1+y^2)^(n+1) ≤ M) :
    ‖deningerMeyerStrongLogGauge n k (deningerMeyerInverseMellinSource F hF)‖ ≤
      deningerMeyerStripGaugeConstant n k*M := by
  have hline : ∀ y : ℝ,
      ‖(-((k : ℂ)+y*I))^n * F ((k : ℂ)+y*I)‖ ≤
        ((|(k : ℝ)|+1)^n*M) * (1+y^2)⁻¹ := by
    intro y
    have hL : 0 < 1+y^2 := by positivity
    have hy : |y| ≤ 1+y^2 := by
      nlinarith [sq_nonneg (|y|-1), sq_abs y, abs_nonneg y]
    have hs : ‖(k : ℂ)+y*I‖ ≤ (|(k : ℝ)|+1)*(1+y^2) := by
      have h : ‖(k : ℂ)+y*I‖ ≤ |(k : ℝ)|+|y| := by
        simpa using Complex.norm_le_abs_re_add_abs_im ((k : ℂ)+y*I)
      nlinarith [abs_nonneg (k : ℝ), sq_nonneg y]
    have hp : ‖-((k : ℂ)+y*I)‖^n ≤ (|(k : ℝ)|+1)^n*(1+y^2)^n := by
      rw [norm_neg, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hs n
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ hL).mpr
    calc
      ‖(-((k : ℂ)+y*I))^n * F ((k : ℂ)+y*I)‖*(1+y^2) =
          ‖-((k : ℂ)+y*I)‖^n * (‖F ((k : ℂ)+y*I)‖*(1+y^2)) := by
        rw [norm_mul, norm_pow]; ring
      _ ≤ ((|(k : ℝ)|+1)^n*(1+y^2)^n) *
          (‖F ((k : ℂ)+y*I)‖*(1+y^2)) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
      _ = (|(k : ℝ)|+1)^n*(‖F ((k : ℂ)+y*I)‖*(1+y^2)^(n+1)) := by ring
      _ ≤ (|(k : ℝ)|+1)^n*M := mul_le_mul_of_nonneg_left (hM y) (by positivity)
  have hi := ((hF.signedPow n ((k : ℝ)-1) ((k : ℝ)+1)).integrable_line
    (c := (k : ℝ)) (by linarith) (by linarith)).norm
  calc
    ‖deningerMeyerStrongLogGauge n k (deningerMeyerInverseMellinSource F hF)‖ ≤
        (1/(2*Real.pi))*∫ y : ℝ, ‖(-((k : ℂ)+y*I))^n * F ((k : ℂ)+y*I)‖ :=
      deningerMeyerInverseMellinSource_gauge_le hF n k
    _ ≤ (1/(2*Real.pi))*∫ y : ℝ, ((|(k : ℝ)|+1)^n*M)*(1+y^2)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact integral_mono (by simpa using hi)
        (integrable_inv_one_add_sq.const_mul _) hline
    _ = deningerMeyerStripGaugeConstant n k*M := by
      rw [integral_const_mul]
      unfold deningerMeyerStripGaugeConstant
      ring

/-- Summable weighted contour blocks converge in the literal original source. -/
theorem deningerMeyerInverseMellinSource_summable {ι : Type*} {F : ι → ℂ → ℂ}
    (hF : ∀ i, DeningerEntireMellinRegular (F i)) {u : ι → ℝ} (hu : Summable u)
    (hb : ∀ r : ℝ, ∀ K : ℕ, ∀ᶠ i in cofinite, ∀ z : ℂ, |z.re| ≤ r →
      ‖F i z‖*(1+z.im^2)^K ≤ u i) :
    Summable (fun i => deningerMeyerInverseMellinSource (F i) (hF i)) := by
  apply deningerMeyerStrongLog_summable_of_gauges
  intro n k
  apply (hu.mul_left (deningerMeyerStripGaugeConstant n k)).of_norm_bounded_eventually
  filter_upwards [hb |(k : ℝ)| (n+1)] with i hi
  exact deningerMeyerInverseMellinSource_gauge_le_weighted (hF i) n k (fun y => by
    simpa using hi ((k : ℂ)+y*I) (by simp))

end
end RHTower
