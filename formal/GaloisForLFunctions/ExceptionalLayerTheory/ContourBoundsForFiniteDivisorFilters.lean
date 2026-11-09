import GaloisForLFunctions.ExceptionalLayerTheory.ZeroFreeBoundsForDampingFilters
import GaloisForLFunctions.RHTower.Sieve.ZetaResidueUnitRectanglePeeling
import GaloisForLFunctions.RHTower.Sieve.ZetaResidueUnitGlobalZeroCount
import GaloisForLFunctions.RHTower.CompletedSplitRightHalfPlane

/-!
# Positive-strip contours for finite divisor filters

Shifting the complete prime integral within the positive Mellin strip crosses
the exceptional zeta divisor without introducing a Gamma pole. The filter
retains its full spacing factor in the remaining vertical integral.
-/

open Complex Filter Set Topology MeasureTheory RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem norm_logDeriv_line_abs (x v : ℝ) :
    ‖logDeriv riemannZeta ((x : ℂ) + v * I)‖ =
      ‖logDeriv riemannZeta ((x : ℂ) + (|v| : ℂ) * I)‖ := by
  by_cases hv : 0 ≤ v
  · rw [abs_of_nonneg hv]
  · have he : (x : ℂ) + v * I =
        (starRingEnd ℂ) ((x : ℂ) + (|v| : ℂ) * I) := by
      apply Complex.ext <;> simp [abs_of_neg (lt_of_not_ge hv)]
    rw [he, logDeriv_riemannZeta_conj, Complex.norm_conj]

/-- Above a finite exceptional packet, a horizontal gap gives polynomial
control of the actual logarithmic derivative across the whole strip. -/
theorem finite_layer_high_strip_logDeriv_bounds (F : Finset XiZeroCopy)
    {θ c : ℝ} (hc : 1 / 2 ≤ c) (hgap : θ < c)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ) :
    ∃ H C : ℝ, 4 ≤ H ∧ 0 < C ∧ ∀ x v : ℝ,
      c ≤ x → x ≤ 2 → H ≤ |v| →
      riemannZeta ((x : ℂ) + v * I) ≠ 0 ∧
      ‖logDeriv riemannZeta ((x : ℂ) + v * I)‖ ≤ C * (1 + |v|) := by
  classical
  let δ := min (c - θ) 1
  let M := ∑ q ∈ F, |(xiZero q).im|
  let H := M + δ + 4
  have hδ : 0 < δ := lt_min (sub_pos.mpr hgap) zero_lt_one
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hH : 4 ≤ H := by dsimp only [H]; linarith only [hM, hδ]
  have hsep : ∀ x v : ℝ, c ≤ x → H ≤ |v| → ∀ q : XiZeroCopy,
      δ ≤ ‖((x : ℂ) + v * I) - xiZero q‖ := by
    intro x v hx hv q
    by_cases hq : q ∈ F
    · have hqi : |(xiZero q).im| ≤ M :=
        Finset.single_le_sum (fun p _ => abs_nonneg (xiZero p).im) hq
      have hn := Complex.abs_im_le_norm (((x : ℂ) + v * I) - xiZero q)
      have he : (((x : ℂ) + v * I) - xiZero q).im = v - (xiZero q).im := by simp
      rw [he] at hn
      have ha := abs_add_le (v - (xiZero q).im) (xiZero q).im
      rw [sub_add_cancel] at ha
      dsimp only [H] at hv
      linarith only [ha, hn, hv, hqi]
    · have hn := Complex.re_le_norm (((x : ℂ) + v * I) - xiZero q)
      have he : (((x : ℂ) + v * I) - xiZero q).re = x - (xiZero q).re := by simp
      rw [he] at hn
      have hd : δ ≤ c - θ := min_le_left _ _
      linarith only [hn, hd, hx, hrest q hq]
  let C := logDerivZetaConstant / δ + 1
  have hbase : 0 ≤ logDerivZetaConstant / δ := by
    unfold logDerivZetaConstant
    positivity
  have hC : 0 < C := by dsimp only [C]; linarith only [hbase]
  refine ⟨H, C, hH, hC, ?_⟩
  intro x v hx hx2 hv
  have hv4 : 4 ≤ |v| := hH.trans hv
  have hx0 : 0 < x := by linarith only [hc, hx]
  have hs1 : (x : ℂ) + v * I ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
      add_zero, zero_add, Complex.one_im] at hi
    rw [hi, abs_zero] at hv4
    linarith only [hv4]
  have hs0 : (x : ℂ) + v * I ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp at hh
    linarith only [hx0, hh]
  have hz : riemannZeta ((x : ℂ) + v * I) ≠ 0 := by
    intro hz
    have hxi : xi ((x : ℂ) + v * I) = 0 := by
      rw [xi_eq_xiUnit_mul_zeta hs0 hs1 (by simpa using hx0), hz, mul_zero]
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
    have hh := hsep x v hx hv q
    change δ ≤ ‖((x : ℂ) + v * I) - (q.1 : ℂ)‖ at hh
    rw [hq, sub_self, norm_zero] at hh
    exact (not_le_of_gt hδ) hh
  refine ⟨hz, ?_⟩
  have hb := norm_logDeriv_zeta_le (hc.trans hx) hx2 hv4 hδ hδ1
    (fun q => by simpa only [abs_abs] using hsep x |v| hx (by simpa only [abs_abs] using hv) q)
  rw [norm_logDeriv_line_abs]
  calc
    _ ≤ (logDerivZetaConstant / δ) * Real.log |v| := by convert hb using 1 <;> ring
    _ ≤ (logDerivZetaConstant / δ) * (1 + |v|) :=
      mul_le_mul_of_nonneg_left (by linarith only [Real.log_le_self (abs_nonneg v)]) hbase
    _ ≤ C * (1 + |v|) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      dsimp only [C]
      linarith

/-- A line between the complementary divisor and the exceptional abscissae
is globally zero-free, including its bounded-height segment. -/
theorem finite_layer_regular_line_zeta_ne_zero (F : Finset XiZeroCopy)
    {θ c : ℝ} (hc : 0 < c) (hc1 : c < 1) (hgap : θ < c)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (havoid : ∀ q ∈ F, c ≠ (xiZero q).re) (v : ℝ) :
    riemannZeta ((c : ℂ) + v * I) ≠ 0 := by
  have hs0 : (c : ℂ) + v * I ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp at hh
    linarith only [hc, hh]
  have hs1 : (c : ℂ) + v * I ≠ 1 := by
    intro he
    have hh := congrArg Complex.re he
    simp at hh
    linarith only [hc1, hh]
  intro hz
  have hxi : xi ((c : ℂ) + v * I) = 0 := by
    rw [xi_eq_xiUnit_mul_zeta hs0 hs1 (by simpa using hc), hz, mul_zero]
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
  have hre : (xiZero q).re = c := by
    change (q.1 : ℂ).re = c
    rw [hq]
    simp
  by_cases hqF : q ∈ F
  · exact havoid q hqF hre.symm
  · linarith only [hrest q hqF, hre, hgap]

/-- The actual logarithmic derivative has polynomial growth on a globally
regular line above the complementary divisor. -/
theorem exists_finite_layer_regular_line_logDeriv_bound (F : Finset XiZeroCopy)
    {θ c : ℝ} (hc : 1 / 2 ≤ c) (hc1 : c < 1) (hgap : θ < c)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (havoid : ∀ q ∈ F, c ≠ (xiZero q).re) :
    ∃ E : ℝ, 0 < E ∧ ∀ v : ℝ,
      ‖logDeriv riemannZeta ((c : ℂ) + v * I)‖ ≤ E * (1 + |v|) := by
  obtain ⟨H, C, _, hC, hb⟩ := finite_layer_high_strip_logDeriv_bounds F hc hgap hrest
  have hc0 : 0 < c := by linarith only [hc]
  have hnz := finite_layer_regular_line_zeta_ne_zero F hc0 hc1 hgap hrest havoid
  have hcont : Continuous (fun v : ℝ => logDeriv riemannZeta ((c : ℂ) + v * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    have hs1 : (c : ℂ) + v * I ≠ 1 := by
      intro he
      have hh := congrArg Complex.re he
      simp at hh
      linarith only [hc1, hh]
    have ha := analyticOn_riemannZeta ((c : ℂ) + v * I) hs1
    have hld : ContinuousAt (logDeriv riemannZeta) ((c : ℂ) + v * I) := by
      change ContinuousAt (fun z => deriv riemannZeta z / riemannZeta z) _
      exact ha.deriv.continuousAt.div ha.continuousAt (hnz v)
    exact hld.comp (f := fun v : ℝ => (c : ℂ) + v * I) (by fun_prop)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-H) H) hcont.continuousOn
  let E := |B| + C + 1
  have hE : 0 < E := by dsimp only [E]; positivity
  refine ⟨E, hE, fun v => ?_⟩
  by_cases hv : |v| ≤ H
  · have hvI : v ∈ Icc (-H) H := abs_le.mp hv
    calc
      _ ≤ B := hB v hvI
      _ ≤ E := by dsimp only [E]; linarith only [le_abs_self B, hC]
      _ ≤ E * (1 + |v|) := le_mul_of_one_le_right hE.le (by linarith only [abs_nonneg v])
  · have hv' : H ≤ |v| := (lt_of_not_ge hv).le
    refine (hb c v le_rfl (by linarith only [hc1]) hv').2.trans ?_
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    dsimp only [E]
    linarith only [abs_nonneg B]

end GaloisForLFunctions.ExceptionalLayerTheory
end GaloisForLFunctions.ExceptionalLayerTheory
