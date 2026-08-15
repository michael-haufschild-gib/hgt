import GaloisForLFunctions.RHTower.SelbergClass.BarnesTwoGammaTail
import GaloisForLFunctions.HTGeometry.GammaAnalyticOffPoles

/-!
# Absolute integrability on a Barnes two-Gamma vertical line

This module converts the concrete pointwise tail estimate for
`Γ(ξ - (c + it)) Γ(c + it) η^(-(c + it))` into absolute integrability on the
whole real line.  It contains no contour displacement, residue sum, or Barnes
evaluation.
-/

open Complex Filter Set MeasureTheory
open scoped BigOperators Topology

namespace RHTower

noncomputable section

private theorem continuous_barnesTwoGammaIntegrand
    (ξ η : ℂ) (c : ℝ) (hc : 0 < c) (hcξ : c < ξ.re) (hη : η ≠ 0) :
    Continuous (barnesTwoGammaIntegrand ξ η c) := by
  let line : ℝ → ℂ := fun t => (c : ℂ) + (t : ℂ) * I
  have hline : Continuous line :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hright : Continuous (fun t : ℝ => Gamma (line t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hpos : 0 < (line t).re := by
      dsimp [line]
      simp [hc]
    exact (HTGeometry.analyticAt_Gamma_of_re_pos hpos).continuousAt.comp hline.continuousAt
  have hleft : Continuous (fun t : ℝ => Gamma (ξ - line t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hpos : 0 < (ξ - line t).re := by
      have hlineRe : (line t).re = c := by
        dsimp [line]
        simp
      rw [Complex.sub_re, hlineRe]
      linarith
    have hsubAt : ContinuousAt (fun z : ℂ => ξ - z) (line t) :=
      (continuous_const.sub continuous_id).continuousAt
    have hgammaSubAt : ContinuousAt (fun z : ℂ => Gamma (ξ - z)) (line t) :=
      (HTGeometry.analyticAt_Gamma_of_re_pos hpos).continuousAt.comp hsubAt
    have hcomp : ContinuousAt (Gamma ∘ fun t : ℝ => ξ - line t) t :=
      hgammaSubAt.comp hline.continuousAt
    simpa [Function.comp_def] using hcomp
  have hpow : Continuous (fun t : ℝ => η ^ (-line t)) :=
    Continuous.const_cpow hline.neg (Or.inl hη)
  change Continuous (fun t : ℝ => Gamma (ξ - line t) * Gamma (line t) * η ^ (-line t))
  exact (hleft.mul hright).mul hpow

/-- The concrete Barnes two-Gamma integrand is absolutely integrable on every
positive line strictly left of `Re ξ`, provided the power base stays inside the
open slit sector `|arg η| < π`. -/
theorem integrable_barnesTwoGammaIntegrand
    {ξ η : ℂ} {c : ℝ} (hc : 0 < c) (hcξ : c < ξ.re)
    (hη : η ≠ 0) (harg : |Complex.arg η| < Real.pi) :
    Integrable (barnesTwoGammaIntegrand ξ η c) := by
  obtain ⟨hrate, C, N, hC, htail⟩ :=
    exists_bound_norm_barnesTwoGammaIntegrand_tail ξ η c hc hcξ hη harg
  let R : ℝ := |ξ.im| + 1
  let g : ℝ → ℝ := fun t => C * |t| ^ N * Real.exp (-(Real.pi - |Complex.arg η|) * |t|)
  have hg : Integrable g := by
    dsimp [g]
    simpa [mul_assoc] using
      (HTGeometry.integrable_abs_pow_mul_exp_neg_abs N hrate).const_mul C
  have hcont : Continuous (barnesTwoGammaIntegrand ξ η c) :=
    continuous_barnesTwoGammaIntegrand ξ η c hc hcξ hη
  have hmid : IntegrableOn (barnesTwoGammaIntegrand ξ η c) (Icc (-R) R) :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  have htailOn : IntegrableOn (barnesTwoGammaIntegrand ξ η c) (Icc (-R) R)ᶜ := by
    refine Integrable.mono' hg.integrableOn hcont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with t ht
    have hR : R ≤ |t| := by
      by_contra hnot
      have hlt : |t| < R := lt_of_not_ge hnot
      apply ht
      constructor
      · nlinarith [neg_abs_le t]
      · nlinarith [le_abs_self t]
    dsimp only [g]
    have hexp : -((Real.pi - |Complex.arg η|) * |t|) =
        -(Real.pi - |Complex.arg η|) * |t| := by ring
    rw [← hexp]
    exact htail t (by simpa [R] using hR)
  rw [← integrableOn_univ, ← union_compl_self (Icc (-R) R)]
  exact hmid.union htailOn

end

end RHTower
