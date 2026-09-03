import GaloisForLFunctions.RHTower.PoleFactorCayleySqrtApproximation
import GaloisForLFunctions.HTGeometry.VitaliConvergence
import GaloisForLFunctions.HTGeometry.PrincipalPartMatching

/-!
# Normal-family obstruction for pole-factor square-root approximants

The rational Cayley-binomial approximants converge to a square root of `s - 1` in the Euler
chamber, but they cannot form a locally bounded family on the full half-plane `Re s > 1/2`.
Otherwise Vitali and the identity theorem would produce a holomorphic square root of `s - 1`
through its simple zero at `s = 1`.

This closes pole-factor normality as a standalone producer.  In the combined arithmetic sequence,
any full-half-plane bound must come from synchronized cancellation with the convolution-half
Dirichlet polynomials.
-/

open Complex Filter Metric Set Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Local boundedness of the rational Cayley square-root approximants on `rightHalf`. -/
def PoleFactorSqrtApproxLocallyBounded : Prop :=
  ∀ z ∈ rightHalf, ∃ R : ℝ, 0 < R ∧ ball z R ⊆ rightHalf ∧ ∃ C : ℝ,
    ∀ N, ∀ w ∈ ball z R, ‖poleFactorSqrtApprox N w‖ ≤ C

/-- **[LEAN-PROVED] [NO-GO]** The Cayley pole-factor approximants are not locally bounded on the
full strict right half-plane. -/
theorem not_poleFactorSqrtApproxLocallyBounded :
    ¬ PoleFactorSqrtApproxLocallyBounded := by
  intro hloc
  obtain ⟨G, hGdiff, hGlim⟩ :=
    vitali_tendstoLocallyUniformlyOn_of_isPreconnected
      convex_rightHalf.isPreconnected
      (fun N => (analyticOnNhd_poleFactorSqrtApprox_rightHalf N).differentiableOn)
      hloc
      (farHalf_subset_rightHalf two_mem_farHalf)
      (Filter.Eventually.frequently
        (Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (isOpen_farHalf.mem_nhds two_mem_farHalf)))
      (fun s hs => ⟨poleFactorSqrtCayleyLimit s,
        tendstoLocallyUniformlyOn_poleFactorSqrtApprox.tendsto_at hs⟩)
  have hGana : AnalyticOnNhd ℂ G rightHalf := hGdiff.analyticOnNhd isOpen_rightHalf
  have hGeq : EqOn G poleFactorSqrtCayleyLimit farHalf := by
    intro s hs
    exact tendsto_nhds_unique
      (hGlim.tendsto_at (farHalf_subset_rightHalf hs))
      (tendstoLocallyUniformlyOn_poleFactorSqrtApprox.tendsto_at hs)
  let H : ℂ → ℂ := fun s => G s ^ 2 - (s - 1)
  have hlinear : AnalyticOnNhd ℂ (fun s : ℂ => s - 1) rightHalf := by
    intro s hs
    fun_prop
  have hHana : AnalyticOnNhd ℂ H rightHalf :=
    (hGana.pow 2).sub hlinear
  have hfreq : ∃ᶠ s in 𝓝[≠] (2 : ℂ), H s = 0 := by
    have hmem : ∀ᶠ s in 𝓝 (2 : ℂ), s ∈ farHalf := isOpen_farHalf.mem_nhds two_mem_farHalf
    have hzero : ∀ᶠ s in 𝓝 (2 : ℂ), H s = 0 := hmem.mono fun s hs => by
      dsimp [H]
      rw [hGeq hs, poleFactorSqrtCayleyLimit_sq (mem_farHalf.mp hs), sub_self]
    exact (Filter.Eventually.filter_mono nhdsWithin_le_nhds hzero).frequently
  have hHall := hHana.eqOn_zero_of_preconnected_of_frequently_eq_zero
    convex_rightHalf.isPreconnected (farHalf_subset_rightHalf two_mem_farHalf) hfreq
  have hsq : ∀ s ∈ rightHalf, G s ^ 2 = s - 1 := by
    intro s hs
    have hzero := hHall hs
    change G s ^ 2 - (s - 1) = 0 at hzero
    exact sub_eq_zero.mp hzero
  have hone : (1 : ℂ) ∈ rightHalf := by
    rw [mem_rightHalf]
    norm_num
  have hdiv := root_orders_dvd isOpen_rightHalf hGana hsq hone
  have horder : analyticOrderAt (fun s : ℂ => s - 1) 1 = 1 := by
    apply analyticOrderAt_eq_one_of_simple_zero
    · fun_prop
    · norm_num
    · simp
  rw [horder] at hdiv
  have hnat : (2 : ℕ) ∣ 1 := natCast_dvd_natCast_of_enat two_ne_zero hdiv
  omega

end

end RHTower
