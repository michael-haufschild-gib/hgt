import GaloisForLFunctions.RHTower.WeilWorkExposingRayCriticalAbel
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# A uniform boundary ceiling for actual critical separators

The positive harmonic factor has residue one. Dividing the actual signed
Abel ceiling therefore gives a single first-order upper bound, uniform
in every real twist. In particular, after quadratic scaling, every
positive upper bound holds on one neighborhood for all twists at once.
No Laurent expansion, residue, coefficient sign or full positivity is
assumed. This pays the arithmetic part of CRITICAL-ONE-POLE-PROOF.md;
the source-kernel derivation of its Laurent expansion remains separate.
-/

open MeasureTheory Filter Topology Set
noncomputable section
namespace RHTower.ExposingRayTransfer
open WeilOneSided

private theorem criticalHarmonicFactor_residue :
    Tendsto (fun s : ℝ => s*criticalHarmonicFactor s) (𝓝[>] 0) (𝓝 1) := by
  have hx : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hshift : Tendsto (fun s : ℝ => 1+s) (𝓝[>] 0) (𝓝[>] 1) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa only [add_zero] using (tendsto_const_nhds.add hx :
        Tendsto (fun s : ℝ => 1+s) (𝓝[>] 0) (𝓝 (1+0)))
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change 1 < 1+s
      linarith [show 0 < s from hs]
  have hz := tendsto_sub_mul_tsum_nat_rpow.comp hshift
  simpa only [criticalHarmonicFactor,Function.comp_def,add_sub_cancel_left,
    Real.rpow_neg (Nat.cast_nonneg _),one_div] using hz

/-- Every actual critical polar separator has one first-order upper bound
on its absolutely convergent cosine series, uniformly in the frequency. -/
theorem critical_uniform_dirichlet_ceiling
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 (by norm_num : (0 : ℝ) ≤ 1) le_rfl f)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ t : ℝ,
      s*criticalCosineSeries b s t ≤ M := by
  obtain ⟨K,hK,hceil⟩ := critical_cosine_dirichlet_product_ceiling h
  refine ⟨6*K,by positivity,?_⟩
  have hlo := criticalHarmonicFactor_residue.eventually
    (lt_mem_nhds (show (1/2 : ℝ) < 1 by norm_num))
  have hx : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hsmall := hx.eventually_lt_const (show (0 : ℝ)<1 by norm_num)
  filter_upwards [hlo,hsmall,self_mem_nhdsWithin] with s hsH hs1 hs t
  have hs0 : 0 < s := hs
  have hp := hceil s hs0 t
  have hs2 : s^2 ≤ 1 := by nlinarith
  have hright : K*(2+s^2) ≤ 3*K := by nlinarith
  have hp' : (s*criticalCosineSeries b s t)*(s*criticalHarmonicFactor s) ≤ 3*K := by
    nlinarith only [hp,hright]
  by_cases hB : s*criticalCosineSeries b s t ≤ 0
  · linarith
  · have hBp : 0 ≤ s*criticalCosineSeries b s t := (lt_of_not_ge hB).le
    have hmul := mul_le_mul_of_nonneg_left hsH.le hBp
    nlinarith only [hp',hmul]

/-- Quadratically rescaled upper tails vanish uniformly over ALL real
frequencies. The neighborhood is independent of the frequency. -/
theorem critical_uniform_quadratic_upper
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 (by norm_num : (0 : ℝ) ≤ 1) le_rfl f))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ t : ℝ, s^2*criticalCosineSeries b s t ≤ ε := by
  obtain ⟨M,_,hM⟩ := critical_uniform_dirichlet_ceiling h
  have hx : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hlim : Tendsto (fun s : ℝ => s*M) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_mul] using hx.mul_const M
  filter_upwards [hM,hlim.eventually_lt_const hε,self_mem_nhdsWithin] with s hs hm hs0 t
  have hp := mul_le_mul_of_nonneg_left (hs t) (show 0 ≤ s from le_of_lt hs0)
  nlinarith only [hp,hm.le]

end RHTower.ExposingRayTransfer
