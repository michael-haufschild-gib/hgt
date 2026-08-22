import GaloisForLFunctions.RHTower.ConnesBesovCutoffDecay
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Transferring the Besov estimate from one place to the product `A_S`

§VII (41)-(42) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068,

are proved one place at a time; (49) uses them on `A_S = ∏_{v ∈ S} k_v`, where `C_{α,v}` acts in
the `v`-th coordinate only.  Passing from one place to the product is two steps, both proved here:

* **Fibrewise integration.**  The `L¹` norm on a product is the integral over the complementary
  coordinates of the per-fibre `L¹` norm (Fubini), so a per-fibre bound `b(Λ)·w(x')` with `w`
  integrable gives a bound `b(Λ)·‖w‖₁` on the whole product — and rapid decay of `b` transfers.
* **The finite sum over `S`.**  A finite sum of rapidly decreasing families is rapidly decreasing.

Nothing here is specific to `A_S`: the complementary coordinates are an arbitrary measure space.
What the transfer consumes is the per-place estimate `ConnesBesovCutoffDecay`, applied on each
fibre, together with integrability of the fibre constants — which is what membership in the
Bruhat–Schwartz space of `A_S` supplies.
-/

open MeasureTheory Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- **The fibrewise mass bound.**  A per-fibre bound with an integrable profile integrates. -/
theorem connes_fibrewise_mass_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {G : X → ℝ} {b : ℝ} {w : X → ℝ} (hw : Integrable w μ)
    (hGnn : ∀ x, 0 ≤ G x) (hbound : ∀ x, G x ≤ b * w x) :
    (∫ x, G x ∂μ) ≤ b * ∫ x, w x ∂μ := by
  have hmaj : Integrable (fun x => b * w x) μ := hw.const_mul b
  have h := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall hGnn) hmaj (Filter.Eventually.of_forall hbound)
  rwa [MeasureTheory.integral_const_mul] at h

/-- **The fibrewise transfer.**  If each fibre's mass is at most `b(Λ)·w(x')` with `w` integrable
and `b` rapidly decreasing, the total mass is rapidly decreasing. -/
theorem connes_fibrewise_rapidDecay {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {G : ℝ → X → ℝ} {b : ℝ → ℝ} {w : X → ℝ} (hw : Integrable w μ)
    (hGnn : ∀ T x, 0 ≤ G T x) (hbound : ∀ T x, G T x ≤ b T * w x)
    (N : ℕ) (hlim : Tendsto (fun T : ℝ => T ^ N * b T) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => T ^ N * ∫ x, G T x ∂μ) atTop (𝓝 0) := by
  set W : ℝ := ∫ x, w x ∂μ with hW
  have hlimW : Tendsto (fun T : ℝ => (T ^ N * b T) * W) atTop (𝓝 0) := by
    simpa using hlim.mul_const W
  refine squeeze_zero' ?_ ?_ hlimW
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    refine mul_nonneg (by positivity) ?_
    exact integral_nonneg fun x => hGnn T x
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    have hmass := connes_fibrewise_mass_le hw (hGnn T) (hbound T)
    have hTN : (0 : ℝ) ≤ T ^ N := by positivity
    calc T ^ N * ∫ x, G T x ∂μ ≤ T ^ N * (b T * W) := by
          rw [← hW] at hmass
          exact mul_le_mul_of_nonneg_left hmass hTN
      _ = (T ^ N * b T) * W := by ring

/-- **The finite sum over the places.**  A finite sum of rapidly decreasing families is rapidly
decreasing. -/
theorem connes_finsetSum_rapidDecay {ι : Type*} (S : Finset ι) {G : ι → ℝ → ℝ}
    (hG : ∀ i ∈ S, Tendsto (fun T : ℝ => G i T) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => ∑ i ∈ S, G i T) atTop (𝓝 0) := by
  have := tendsto_finsetSum S (fun i (hi : i ∈ S) => hG i hi)
  simpa using this

/-- **Fubini for the fibrewise mass.**  The `L¹` norm on the product is the integral over the
complementary coordinates of the per-fibre `L¹` norm. -/
theorem connes_prodMass_eq_fibrewise {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [SigmaFinite μ] {ν : Measure ℝ} [SigmaFinite ν] {f : X × ℝ → ℂ}
    (hf : Integrable f (μ.prod ν)) :
    (∫ z, ‖f z‖ ∂(μ.prod ν)) = ∫ x, (∫ t, ‖f (x, t)‖ ∂ν) ∂μ :=
  MeasureTheory.integral_prod (fun z => ‖f z‖) hf.norm

end

end GaloisForLFunctions.RHTower
