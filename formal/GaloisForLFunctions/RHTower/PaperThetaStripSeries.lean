import GaloisForLFunctions.RHTower.PaperThetaContourControl
import GaloisForLFunctions.RHTower.PaperThetaBVParameterDifferentiation
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! # Summation with one global theta variation control -/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint

theorem eVariationOn_le_strip_control {f : ℝ → ℂ} {B C : ℝ} (hC : 0 ≤ C)
    (hi : ∀ x y, ‖f y-f x‖ ≤ C*|stripCutControl B y-stripCutControl B x|) :
    eVariationOn f univ ≤ ENNReal.ofReal (C*(4*stripTailControl B 0)) := by
  apply iSup_le
  rintro ⟨N, ⟨u, hu, _⟩⟩
  let V := stripCutControl B
  have hinc (i : ℕ) : 0 ≤ V (u (i+1))-V (u i) :=
    sub_nonneg.mpr (monotone_stripCutControl B (hu (Nat.le_succ i)))
  calc
    (∑ i ∈ Finset.range N, edist (f (u (i+1))) (f (u i))) ≤
        ∑ i ∈ Finset.range N, ENNReal.ofReal (C*(V (u (i+1))-V (u i))) := by
      apply Finset.sum_le_sum
      intro i _
      rw [edist_dist, dist_eq_norm]
      apply ENNReal.ofReal_le_ofReal
      simpa only [V, abs_of_nonneg (hinc i)] using hi (u i) (u (i+1))
    _ = ENNReal.ofReal (C*(V (u N)-V (u 0))) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i (_ : i ∈ Finset.range N) =>
        mul_nonneg hC (hinc i)), ← Finset.mul_sum, Finset.sum_range_sub (fun i => V (u i)) N]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ hC
      exact (sub_le_self _ (stripCutControl_bounds B (u 0)).1).trans
        (stripCutControl_bounds B (u N)).2

theorem boundedVariationOn_of_strip_control {f : ℝ → ℂ} {B C : ℝ} (hC : 0 ≤ C)
    (hi : ∀ x y, ‖f y-f x‖ ≤ C*|stripCutControl B y-stripCutControl B x|) :
    BoundedVariationOn f univ :=
  ((eVariationOn_le_strip_control hC hi).trans_lt ENNReal.ofReal_lt_top).ne

theorem stripSeries_increment {f : ℕ → NativeContinuousSpace} {c : ℕ → ℝ} {B : ℝ}
    (hc : Summable c) (hn : ∀ n, ‖f n‖ ≤ c n)
    (hi : ∀ n x y, ‖f n y-f n x‖ ≤ c n*|stripCutControl B y-stripCutControl B x|)
    (x y : ℝ) :
    ‖(∑' n, f n) y-(∑' n, f n) x‖ ≤ (∑' n, c n)*|stripCutControl B y-stripCutControl B x| := by
  have hf := hc.of_norm_bounded hn
  have he : (∑' n, f n) y-(∑' n, f n) x = ∑' n, (f n y-f n x) :=
    ((BoundedContinuousFunction.evalCLM ℂ y : NativeContinuousSpace →L[ℂ] ℂ)-
      BoundedContinuousFunction.evalCLM ℂ x).map_tsum hf
  rw [he]
  exact tsum_of_norm_bounded (hc.hasSum.mul_right _) (fun n => hi n x y)

theorem stripSeries_boundedVariation {f : ℕ → NativeContinuousSpace} {c : ℕ → ℝ} {B : ℝ}
    (hc : Summable c) (hn : ∀ n, ‖f n‖ ≤ c n)
    (hi : ∀ n x y, ‖f n y-f n x‖ ≤ c n*|stripCutControl B y-stripCutControl B x|) :
    BoundedVariationOn (fun x => (∑' n, f n) x) univ :=
  boundedVariationOn_of_strip_control (tsum_nonneg fun n => (norm_nonneg _).trans (hn n))
    (stripSeries_increment hc hn hi)

/-- The original functions converge in point value plus their entire variation. -/
theorem stripSeries_globalBV {f : ℕ → NativeContinuousSpace} {c : ℕ → ℝ} {B : ℝ}
    (hc : Summable c) (hn : ∀ n, ‖f n‖ ≤ c n)
    (hi : ∀ n x y, ‖f n y-f n x‖ ≤ c n*|stripCutControl B y-stripCutControl B x|) :
    Tendsto (fun N => globalBVSize
      (fun x => ((∑' n, f n)-(∑ n ∈ Finset.range N, f n)) x)) atTop (𝓝 0) := by
  have hf := hc.of_norm_bounded hn
  let r (N : ℕ) : ℝ := ∑' k, c (k+N)
  have hr : ∀ N, 0 ≤ r N := fun N => tsum_nonneg fun k => (norm_nonneg _).trans (hn (k+N))
  have hrt : Tendsto r atTop (𝓝 0) := tendsto_sum_nat_add c
  have he (N : ℕ) : (∑' n, f n)-(∑ n ∈ Finset.range N, f n) = ∑' k, f (k+N) := by
    rw [← hf.sum_add_tsum_nat_add N, add_sub_cancel_left]
  have hnorm (N : ℕ) : ‖∑' k, f (k+N)‖ ≤ r N :=
    tsum_of_norm_bounded ((summable_nat_add_iff N).mpr hc).hasSum (fun k => hn (k+N))
  have hvar (N : ℕ) : eVariationOn (fun x => (∑' k, f (k+N)) x) univ ≤
      ENNReal.ofReal (r N*(4*stripTailControl B 0)) :=
    eVariationOn_le_strip_control (hr N)
      (stripSeries_increment ((summable_nat_add_iff N).mpr hc)
        (fun k => hn (k+N)) (fun k => hi (k+N)))
  have hp : Tendsto (fun N => ENNReal.ofReal ‖((∑' n, f n)-(∑ n ∈ Finset.range N, f n)) 0‖)
      atTop (𝓝 0) := by
    have ht : Tendsto (fun N => ENNReal.ofReal (r N)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp hrt
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
      (Eventually.of_forall fun _ => bot_le)
    exact Eventually.of_forall fun N => by
      rw [he]
      exact ENNReal.ofReal_le_ofReal (((∑' k, f (k+N)).norm_coe_le_norm 0).trans (hnorm N))
  have hv : Tendsto (fun N => eVariationOn
      (fun x => ((∑' n, f n)-(∑ n ∈ Finset.range N, f n)) x) univ) atTop (𝓝 0) := by
    have ht : Tendsto (fun N => ENNReal.ofReal (r N*(4*stripTailControl B 0))) atTop (𝓝 0) := by
      simpa only [Function.comp_def, zero_mul, ENNReal.ofReal_zero] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hrt.mul_const (4*stripTailControl B 0))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
      (Eventually.of_forall fun _ => bot_le)
    exact Eventually.of_forall fun N => by rw [he]; exact hvar N
  simpa only [globalBVSize, zero_add] using hp.add hv

end RHTower.PaperThetaEndpoint
