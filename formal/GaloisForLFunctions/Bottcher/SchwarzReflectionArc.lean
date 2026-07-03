/-
# Reflection across the unit circle

A specialisation of the biholomorphism-conjugated reflection engine
(`differentiableOn_of_off_biholom_preimage_line`) to the unit circle: on a slit-plane region, a
function continuous and holomorphic off `{‖z‖ = 1}` is holomorphic everywhere.  The uniformiser is the
principal logarithm `ψ = Complex.log`, whose global inverse is `Complex.exp` (no implicit-function
theorem needed); it carries `{‖z‖ = 1}` to the line `{(I·log z).im = 0} = {Re (log z) = 0}`.

This is the building block for reflection across a general analytic modulus-one arc `{‖g‖ = 1}`: after
composing with a local inverse of `g` (and a rotation onto the slit plane), the arc becomes a
unit-circle arc and this lemma applies.  The modulus-one Julia arc of the smooth-piece obstruction is
exactly such a `{‖wfam k‖ = 1}` locus.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.OpenMapping
import GaloisForLFunctions.Bottcher.SchwarzReflection

open Complex Set

namespace Bottcher

/-- **Reflection across the unit circle.**  On an open, preconnected slit-plane region `V`, a function
continuous on `V` and holomorphic off the unit circle `{‖z‖ = 1}` is holomorphic on all of `V`. -/
theorem differentiableOn_of_off_unit_circle
    {f : ℂ → ℂ} {V : Set ℂ} (hVo : IsOpen V) (hVc : IsPreconnected V)
    (hVslit : V ⊆ Complex.slitPlane)
    (hcont : ContinuousOn f V)
    (hdiff : DifferentiableOn ℂ f (V ∩ {z : ℂ | ‖z‖ ≠ 1})) :
    DifferentiableOn ℂ f V := by
  have hlogDiff : DifferentiableOn ℂ Complex.log V :=
    fun z hz => (Complex.differentiableAt_log (hVslit hz)).differentiableWithinAt
  have hlogAn : AnalyticOnNhd ℂ Complex.log V := hlogDiff.analyticOnNhd hVo
  have hVimg : IsOpen (Complex.log '' V) := by
    rcases hlogAn.is_constant_or_isOpen hVc with hconst | hopen
    · rcases V.eq_empty_or_nonempty with hVe | ⟨z₀, hz₀⟩
      · simp [hVe]
      · exfalso
        obtain ⟨c, hc⟩ := hconst
        obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hVo z₀ hz₀
        set p : ℂ := z₀ + ((ε / 2 : ℝ) : ℂ) with hp
        have hmem : p ∈ Metric.ball z₀ ε := by
          have hd : p - z₀ = ((ε / 2 : ℝ) : ℂ) := by rw [hp]; ring
          rw [Metric.mem_ball, Complex.dist_eq, hd, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by linarith)]
          linarith
        have hpV : p ∈ V := hball hmem
        have e1 : z₀ = Complex.exp c := by
          rw [← Complex.exp_log (Complex.slitPlane_ne_zero (hVslit hz₀)), hc z₀ hz₀]
        have e2 : p = Complex.exp c := by
          rw [← Complex.exp_log (Complex.slitPlane_ne_zero (hVslit hpV)), hc p hpV]
        have hpz : z₀ + ((ε / 2 : ℝ) : ℂ) = z₀ := by rw [← hp, e2, ← e1]
        have hz : ((ε / 2 : ℝ) : ℂ) = 0 := by linear_combination hpz
        rw [Complex.ofReal_eq_zero] at hz
        linarith
    · exact hopen V subset_rfl hVo
  have hexpDiff : DifferentiableOn ℂ Complex.exp (Complex.log '' V) :=
    Complex.differentiable_exp.differentiableOn
  have hleft : ∀ z ∈ V, Complex.exp (Complex.log z) = z :=
    fun z hz => Complex.exp_log (Complex.slitPlane_ne_zero (hVslit hz))
  have hset : V ∩ {z : ℂ | (I * Complex.log z + 0).im ≠ 0} = V ∩ {z : ℂ | ‖z‖ ≠ 1} := by
    ext z
    simp only [mem_inter_iff, mem_setOf_eq, add_zero, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.log_re, zero_mul, one_mul, zero_add]
    refine and_congr_right fun hzV => ?_
    have hpos : 0 < ‖z‖ := norm_pos_iff.mpr (Complex.slitPlane_ne_zero (hVslit hzV))
    rw [not_iff_not, Real.log_eq_zero]
    constructor
    · rintro (h | h | h)
      · exact absurd h hpos.ne'
      · exact h
      · exact absurd h (by linarith)
    · intro h; right; left; exact h
  rw [← hset] at hdiff
  exact differentiableOn_of_off_biholom_preimage_line (c := I) (d := 0) Complex.I_ne_zero
    hVimg hlogDiff hexpDiff hleft hcont hdiff

end Bottcher
