import GaloisForLFunctions.RHTower.EvenOrderOnePartialFractionZeroCount
import GaloisForLFunctions.RHTower.OrderOneEvenLaguerrePolya
import GaloisForLFunctions.RHTower.PhotonicLosslessHeatFlowFiniteDefect

/-!
# Real exterior zeros dissipate vertical heat energy

Symmetric finite zero sums recover the logarithmic derivative of an even
order-one entire function. After removing every nonreal zero, the remaining
field has nonpositive vertical work. This applies to the actual heat divisor
at every positive time.
-/

open Complex Filter Topology Set
open GaloisForLFunctions.EntireZeroDivisor
open RHTower.OrderOneHadamard

namespace GaloisForLFunctions.ArithmeticElectrostatics

noncomputable section

variable {f : ℂ → ℂ}

/-- Reflection cancels the genus-one counterterms on each centered zero ball. -/
theorem tendsto_sum_reciprocal_zeroCopyBall {C : ℝ} (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f univ) (hf0 : f 0 ≠ 0)
    (heven : ∀ z, f (-z) = f z)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    {z : ℂ} (hz : f z ≠ 0) :
    Tendsto (fun n => ∑ q ∈ zeroCopyBall hf n, (z - zeroCopyPoint f q)⁻¹)
      atTop (𝓝 (logDeriv f z)) := by
  have ha (q : ZeroCopy f) : zeroCopyPoint f q ≠ 0 := zeroCopyPoint_ne_zero hf hf0 q
  have hza (q : ZeroCopy f) : z ≠ zeroCopyPoint f q :=
    fun h => hz (h ▸ RHTower.DeBruijn.apply_zeroCopyPoint hf q)
  have hp (q : ZeroCopy f) : -z / (zeroCopyPoint f q * (zeroCopyPoint f q - z)) =
      (z - zeroCopyPoint f q)⁻¹ + (zeroCopyPoint f q)⁻¹ := by
    field_simp [ha q, sub_ne_zero.mpr (hza q), sub_ne_zero.mpr (hza q).symm]
    ring
  have h := (RHTower.summable_neg_div_zeroCopyPoint hC hf hf0 hbound z).hasSum.comp
    (tendsto_zeroCopyBall hf)
  rw [← RHTower.logDeriv_eq_tsum_of_even hC hf hf0 heven hbound hz] at h
  simpa only [Function.comp_def, hp, Finset.sum_add_distrib, sum_inv_zeroCopyBall_eq_zero hf heven,
    add_zero] using h

/-- Every real exterior zero contributes `-Im(z)² / |z-a|²`. -/
theorem im_mul_exterior_logDeriv_nonpos {C : ℝ} (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f univ) (hf0 : f 0 ≠ 0)
    (heven : ∀ z, f (-z) = f z)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    (N : Finset (ZeroCopy f))
    (hreal : ∀ q, q ∉ N → (zeroCopyPoint f q).im = 0)
    {z : ℂ} (hz : f z ≠ 0) :
    z.im * (logDeriv f z - ∑ q ∈ N, (z - zeroCopyPoint f q)⁻¹).im ≤ 0 := by
  classical
  have hlim := tendsto_sum_reciprocal_zeroCopyBall hC hf hf0 heven hbound hz
  have hwork : Tendsto (fun n : ℕ => z.im *
      ((∑ q ∈ zeroCopyBall hf n, (z - zeroCopyPoint f q)⁻¹) -
        ∑ q ∈ N, (z - zeroCopyPoint f q)⁻¹).im) atTop
      (𝓝 (z.im * (logDeriv f z - ∑ q ∈ N, (z - zeroCopyPoint f q)⁻¹).im)) :=
    tendsto_const_nhds.mul
      (Complex.continuous_im.tendsto _ |>.comp (hlim.sub tendsto_const_nhds))
  apply le_of_tendsto hwork
  filter_upwards [(tendsto_zeroCopyBall hf).eventually (eventually_ge_atTop N)] with n hn
  have heq : (∑ q ∈ zeroCopyBall hf n, (z - zeroCopyPoint f q)⁻¹) -
      ∑ q ∈ N, (z - zeroCopyPoint f q)⁻¹ =
      ∑ q ∈ zeroCopyBall hf n \ N, (z - zeroCopyPoint f q)⁻¹ := by
    rw [← Finset.sum_sdiff hn, add_sub_cancel_right]
  rw [heq, Complex.im_sum, Finset.mul_sum]
  apply Finset.sum_nonpos
  intro q hq
  rw [Complex.inv_im, Complex.sub_im, hreal q (Finset.mem_sdiff.mp hq).2, sub_zero]
  have heq' : z.im * (-z.im / normSq (z - zeroCopyPoint f q)) =
      -(z.im ^ 2) / normSq (z - zeroCopyPoint f q) := by ring
  rw [heq']
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (normSq_nonneg _)

/-- The finite nonreal heat divisor, with analytic multiplicities. -/
def heatNonrealCopies (t : ℝ) :
    Finset (ZeroCopy (RHTower.DeBruijn.riemannHeat t)) :=
  if ht : 0 < t then (RHTower.finite_nonreal_zeroCopy_riemannHeat ht).toFinset else ∅

theorem mem_heatNonrealCopies {t : ℝ} (ht : 0 < t)
    (q : ZeroCopy (RHTower.DeBruijn.riemannHeat t)) :
    q ∈ heatNonrealCopies t ↔ (zeroCopyPoint (RHTower.DeBruijn.riemannHeat t) q).im ≠ 0 := by
  simp only [heatNonrealCopies, dif_pos ht, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

/-- The real part of the heat divisor cannot increase vertical energy. -/
theorem riemannHeat_realExteriorWork_nonpos {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : RHTower.DeBruijn.riemannHeat t z ≠ 0) :
    z.im * (logDeriv (RHTower.DeBruijn.riemannHeat t) z -
      ∑ q ∈ heatNonrealCopies t,
        (z - zeroCopyPoint (RHTower.DeBruijn.riemannHeat t) q)⁻¹).im ≤ 0 := by
  obtain ⟨C, hC, hbound⟩ :=
    (RHTower.DeBruijn.riemannKernel_superExp.mul_exp_sq ht.le).exists_envelope
  refine im_mul_exterior_logDeriv_nonpos hC
    (RHTower.DeBruijn.riemannHeat_analytic ht.le)
    (RHTower.riemannHeat_zero_ne ht.le) (RHTower.DeBruijn.riemannHeat_neg ht.le)
    hbound (heatNonrealCopies t) (fun q hq => ?_) hz
  by_contra h
  exact hq ((mem_heatNonrealCopies ht q).mpr h)

#print axioms riemannHeat_realExteriorWork_nonpos

end

end GaloisForLFunctions.ArithmeticElectrostatics

