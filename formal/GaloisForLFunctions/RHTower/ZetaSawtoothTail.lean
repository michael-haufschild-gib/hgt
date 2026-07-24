import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# The sawtooth tail of the truncated ζ-representation

The Euler–Maclaurin tail `∫_N^∞ {u}·u^{-s-1} du` behind the truncated
Dirichlet-series representation of `ζ` on `Re s > 0`:

`ζ(s) = Σ_{n ≤ N} n^{-s} + N^{1-s}/(s-1) - s·∫_N^∞ {u}·u^{-s-1} du`.

This file supplies the tail's integrability and the exact norm bound
`‖tail‖ ≤ N^{-Re s}/Re s` — the seed of the vertical growth estimates
`|ζ(σ+it)| = O(log t)` near `Re = 1` feeding the de la Vallée Poussin
zero-free region.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set

/-- The sawtooth tail `∫_N^∞ {u}·u^{-s-1} du`. -/
def zetaSawtoothTail (N : ℕ) (s : ℂ) : ℂ :=
  ∫ u in Set.Ioi (N : ℝ), ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)

/-- Integrability of the sawtooth integrand on `(N, ∞)` for `Re s > 0`. -/
theorem integrableOn_sawtooth_cpow {s : ℂ} (hs : 0 < s.re) {N : ℕ}
    (hN : 1 ≤ N) :
    IntegrableOn (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))
      (Set.Ioi (N : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hexp : -s.re - 1 < -1 := by linarith
  have hg : IntegrableOn (fun u : ℝ => u ^ (-s.re - 1)) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt hexp hN0
  have hmeas : AEStronglyMeasurable
      (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))
      (volume.restrict (Set.Ioi (N : ℝ))) := by
    apply AEStronglyMeasurable.mul
    · exact (Complex.measurable_ofReal.comp
        measurable_fract).aestronglyMeasurable
    · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      intro u hu
      have hu0 : (0 : ℝ) < u := lt_trans hN0 hu
      have h2 : Continuous fun v : ℝ => (v, (-s - 1 : ℂ)) := by fun_prop
      exact ((Complex.continuousAt_ofReal_cpow u (-s - 1)
        (Or.inr (ne_of_gt hu0))).comp
          (f := fun v : ℝ => (v, (-s - 1 : ℂ)))
          h2.continuousAt).continuousWithinAt
  apply Integrable.mono hg hmeas
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with u hu
  have hu0 : (0 : ℝ) < u := lt_trans hN0 hu
  have h1 : ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖
      = Int.fract u * u ^ ((-s - 1).re) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg u)]
  rw [h1]
  have h2 : (-s - 1).re = -s.re - 1 := by
    simp [Complex.sub_re, Complex.neg_re]
  rw [h2]
  have h3 : ‖u ^ (-s.re - 1)‖ = u ^ (-s.re - 1) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hu0.le _)]
  rw [h3]
  have h4 : Int.fract u ≤ 1 := le_of_lt (Int.fract_lt_one u)
  nlinarith [Real.rpow_nonneg hu0.le (-s.re - 1), Int.fract_nonneg u]

/-- **Exact tail bound**: `‖∫_N^∞ {u}·u^{-s-1}‖ ≤ N^{-Re s}/Re s`. -/
theorem norm_zetaSawtoothTail_le {s : ℂ} (hs : 0 < s.re) {N : ℕ}
    (hN : 1 ≤ N) :
    ‖zetaSawtoothTail N s‖ ≤ (N : ℝ) ^ (-s.re) / s.re := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hexp : -s.re - 1 < -1 := by linarith
  have hint := integrableOn_sawtooth_cpow hs hN
  calc ‖zetaSawtoothTail N s‖
      ≤ ∫ u in Set.Ioi (N : ℝ),
          ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ u in Set.Ioi (N : ℝ), u ^ (-s.re - 1) := by
        apply setIntegral_mono_on hint.norm
          (integrableOn_Ioi_rpow_of_lt hexp hN0) measurableSet_Ioi
        intro u hu
        have hu0 : (0 : ℝ) < u := lt_trans hN0 hu
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0,
          Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Int.fract_nonneg u),
          show (-s - 1).re = -s.re - 1 by
            simp [Complex.sub_re, Complex.neg_re]]
        have h4 : Int.fract u ≤ 1 := le_of_lt (Int.fract_lt_one u)
        nlinarith [Real.rpow_nonneg hu0.le (-s.re - 1), Int.fract_nonneg u]
    _ = -(N : ℝ) ^ (-s.re - 1 + 1) / (-s.re - 1 + 1) :=
        integral_Ioi_rpow_of_lt hexp hN0
    _ = (N : ℝ) ^ (-s.re) / s.re := by
        rw [show -s.re - 1 + 1 = -s.re by ring]
        rw [div_eq_div_iff (by linarith) (by linarith)]
        ring

end RHTower
