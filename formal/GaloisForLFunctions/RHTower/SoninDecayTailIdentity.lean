import GaloisForLFunctions.RHTower.SoninExtendedMellinExtension

/-!
# The continued Mellin tail is the convergent tail integral

For a vector of `(centralFourierForbidden a)ᗮ` the corpus continues the Mellin tail from the
half-plane of absolute convergence `Re s > 1/2` to `Re s > 0`.  When the vector also decays like
`C/|t|` the tail integral itself already converges on `Re s > 0`, and the two agree: both are
holomorphic on the connected half-plane and coincide on `Re s > 1/2`, so the identity theorem
finishes.

## Main results

* `isPreconnected_re_pos`
* `soninMellinExtension_eq_decayTailMellin`
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

theorem isPreconnected_re_pos : IsPreconnected {v : ℂ | 0 < v.re} :=
  (convex_halfSpace_gt ⟨Complex.add_re, fun c z => Complex.smul_re c z⟩ 0).isPreconnected

/-- **The continuation is the convergent tail integral.** -/
theorem soninMellinExtension_eq_decayTailMellin {a : ℝ} (ha : 0 < a) {g : SoninL2} {C : ℝ}
    (hdec : HasInverseDecay g C) (hg : g ∈ (centralFourierForbidden a)ᗮ) {s : ℂ}
    (hs : 0 < s.re) :
    soninMellinExtension g a s = decayTailMellin g a s := by
  have hopen : IsOpen {v : ℂ | 0 < v.re} := isOpen_lt continuous_const Complex.continuous_re
  have hA : AnalyticOnNhd ℂ (soninMellinExtension g a) {v : ℂ | 0 < v.re} :=
    (differentiableOn_soninMellinExtension ha hg).analyticOnNhd hopen
  have hB : AnalyticOnNhd ℂ (decayTailMellin g a) {v : ℂ | 0 < v.re} :=
    (differentiableOn_decayTailMellin hdec ha).analyticOnNhd hopen
  have hz₀ : (1 : ℂ) ∈ {v : ℂ | 0 < v.re} := by
    simp only [Set.mem_setOf_eq, Complex.one_re]
    norm_num
  have hopen2 : IsOpen {v : ℂ | 1 / 2 < v.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev₀ : soninMellinExtension g a =ᶠ[𝓝 (1 : ℂ)] decayTailMellin g a := by
    have hmem : (1 : ℂ) ∈ {v : ℂ | 1 / 2 < v.re} := by
      simp only [Set.mem_setOf_eq, Complex.one_re]
      norm_num
    filter_upwards [hopen2.mem_nhds hmem] with w hw
    rw [soninMellinExtension_eq_tail ha hg hw, decayTailMellin]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
  exact hA.eqOn_of_preconnected_of_eventuallyEq hB isPreconnected_re_pos hz₀ hev₀ hs

end RHTower

end
