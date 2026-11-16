import GaloisForLFunctions.OrderSixMetaplecticTheory.TheEisensteinCorrectionIsHolomorphicOnTheRealSegment

/-!
# The Eisenstein correction on the strip `Re s > 1`

Off the real axis the correction `Corr(s) = R(s(2 − s)) defect(s)` is analytic (MMD); on the real
segment it has removable singularities except at `4/3` (`correction_removable`). This module glues the
two and bounds the resolvent:

* `analyticOnNhd_limUnder`: a function with a removable singularity at every point of a set extends,
  by its punctured limits, to a function analytic on the set;
* `correctionExt`: the extension of `Corr` to `{Re s > 1} \ {4/3}`, analytic there and equal to `Corr`
  off the real axis (`correctionExt_analyticOnNhd`, `correctionExt_eq`);
* `norm_resolvent_le`: `‖R(z)F‖ ≤ ‖F‖/|Im z|` — the self-adjoint resolvent bound, from
  `⟨u, T(z)u⟩ = ‖∇u‖² − z‖mu‖²`;
* `norm_correction_le`: `‖Corr(s)‖ ≤ ‖defect(s)‖/(2|Im s|(Re s − 1))` for `Re s > 1`, `Im s ≠ 0`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators Classical InnerProductSpace ComplexConjugate MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein SpectralTheoryOfTheCubicCover

/-! ### Removable singularities on an open set -/

/-- If at every point `z` of the open set `U` the function `f` agrees off `z` with a function analytic
at `z`, then `z ↦ lim_{w → z, w ≠ z} f(w)` is analytic on `U`. -/
theorem analyticOnNhd_limUnder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : ℂ → E} {U : Set ℂ}
    (hf : ∀ z ∈ U, ∃ g : ℂ → E, AnalyticAt ℂ g z ∧ ∀ᶠ w in 𝓝[≠] z, g w = f w) :
    AnalyticOnNhd ℂ (fun z => limUnder (𝓝[≠] z) f) U := by
  intro z hz
  obtain ⟨g, hg, hgf⟩ := hf z hz
  -- `f = g` on a punctured ball around `z`, and `g` is analytic on a ball
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (eventually_nhdsWithin_iff.mp hgf)
  have hgan : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ g w := hg.eventually_analyticAt
  refine hg.congr ?_
  filter_upwards [Metric.ball_mem_nhds z hε, hgan] with w hw hgw
  -- the punctured limit at `w` is `g w`
  have hlim : Tendsto f (𝓝[≠] w) (𝓝 (g w)) := by
    have hcont : Tendsto g (𝓝[≠] w) (𝓝 (g w)) := hgw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine hcont.congr' ?_
    by_cases hwz : w = z
    · subst hwz
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds w hε)] with u hu hub
      exact hball u hub hu
    · have hopen : IsOpen (Metric.ball z ε \ {z}) := Metric.isOpen_ball.sdiff isClosed_singleton
      have hmem : w ∈ Metric.ball z ε \ {z} := ⟨hw, hwz⟩
      filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hmem)] with u hu
      exact hball u hu.1 hu.2
  exact (hlim.limUnder_eq).symm

/-! ### The extension of the correction -/

/-- The strip `Re s > 1` without `4/3`. -/
def correctionDomain : Set ℂ := {s | 1 < s.re ∧ s ≠ 4 / 3}

theorem correctionDomain_isOpen : IsOpen correctionDomain :=
  (isOpen_lt continuous_const Complex.continuous_re).inter isClosed_singleton.isOpen_compl

/-- The correction continued to `Re s > 1`, `s ≠ 4/3`, by its punctured limits. -/
def correctionExt (s : ℂ) : KernelQuotientL2 := limUnder (𝓝[≠] s) correction

theorem correction_locally_removable (z : ℂ) (hz : z ∈ correctionDomain) :
    ∃ g : ℂ → KernelQuotientL2, AnalyticAt ℂ g z ∧ ∀ᶠ w in 𝓝[≠] z, g w = correction w := by
  by_cases him : z.im = 0
  · have hz' : z = ((z.re : ℝ) : ℂ) := Complex.ext rfl (by simp [him])
    have h43 : z.re ≠ 4 / 3 := by
      intro h
      apply hz.2
      rw [hz', h]
      push_cast
      ring
    obtain ⟨C, hC, hCe⟩ := correction_removable z.re hz.1 h43
    rw [hz']
    exact ⟨C, hC, hCe⟩
  · exact ⟨correction, kernelEisensteinL2Correction_analyticAt_nonreal 5 6 (by norm_num) (by norm_num) z
      (ne_of_gt hz.1) him, Eventually.of_forall fun _ => rfl⟩

/-- **The correction is analytic on the strip minus `4/3`.** -/
theorem correctionExt_analyticOnNhd : AnalyticOnNhd ℂ correctionExt correctionDomain :=
  analyticOnNhd_limUnder correction_locally_removable

/-- Off the real axis the extension is the correction itself. -/
theorem correctionExt_eq {s : ℂ} (hs : 1 < s.re) (hi : s.im ≠ 0) : correctionExt s = correction s := by
  have han := kernelEisensteinL2Correction_analyticAt_nonreal 5 6 (by norm_num) (by norm_num) s
    (ne_of_gt hs) hi
  exact (han.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq

/-! ### The resolvent bound -/

/-- **The self-adjoint resolvent bound.** For `Im z ≠ 0`: `‖R(z)F‖ ≤ ‖F‖/|Im z|`. -/
theorem norm_resolvent_le (z : ℂ) (hz : z.im ≠ 0) (F : KernelQuotientL2) :
    ‖kernelSpectralResolvent z F‖ ≤ ‖F‖ / |z.im| := by
  have hU := kernelSpectralFormOperator_isUnit_nonreal z hz
  set u := Ring.inverse (kernelSpectralFormOperator z) (kernelVariationalSolution F)
  have hu : kernelSpectralFormOperator z u = kernelVariationalSolution F :=
    congrArg (fun A : KernelEnergyGraph →L[ℂ] KernelEnergyGraph => A (kernelVariationalSolution F))
      (Ring.mul_inverse_cancel _ hU)
  have hR : kernelSpectralResolvent z F = kernelEnergyMass u := kernelSpectralResolvent_apply z F
  -- `⟨u, T(z)u⟩ = ‖∇u‖² − z‖mu‖² = ⟨mu, F⟩`
  have h1 := kernelSpectralFormOperator_inner z u
  rw [hu] at h1
  have h2 : inner ℂ u (kernelVariationalSolution F) = inner ℂ (kernelEnergyMass u) F := by
    rw [kernelVariationalSolution, ContinuousLinearMap.adjoint_inner_right]
  rw [h2] at h1
  -- imaginary parts: `−Im z ‖mu‖² = Im ⟨mu, F⟩`
  have him := congrArg Complex.im h1
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, mul_zero,
    zero_add, zero_sub] at him
  have hbound : |z.im| * ‖kernelEnergyMass u‖ ^ 2 ≤ ‖kernelEnergyMass u‖ * ‖F‖ := by
    calc |z.im| * ‖kernelEnergyMass u‖ ^ 2 = |(inner ℂ (kernelEnergyMass u) F).im| := by
          rw [him, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg ‖kernelEnergyMass u‖)]
      _ ≤ ‖inner ℂ (kernelEnergyMass u) F‖ := Complex.abs_im_le_norm _
      _ ≤ ‖kernelEnergyMass u‖ * ‖F‖ := norm_inner_le_norm _ _
  have hpos : 0 < |z.im| := abs_pos.mpr hz
  rw [hR, le_div_iff₀ hpos]
  by_cases h0 : ‖kernelEnergyMass u‖ = 0
  · rw [h0, zero_mul]
    positivity
  · have hp : 0 < ‖kernelEnergyMass u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

/-- `Im(s(2 − s)) = 2 Im s (1 − Re s)`. -/
theorem spectralParameter_im (s : ℂ) :
    (kernelEisensteinSpectralParameter s).im = 2 * s.im * (1 - s.re) := by
  unfold kernelEisensteinSpectralParameter
  simp only [Complex.mul_im, Complex.sub_im, Complex.sub_re]
  norm_num
  ring

/-- **The correction bound.** For `Re s > 1`, `Im s ≠ 0`:
`‖Corr(s)‖ ≤ ‖defect(s)‖ / (2 |Im s| (Re s − 1))`. -/
theorem norm_correction_le {s : ℂ} (hs : 1 < s.re) (hi : s.im ≠ 0) :
    ‖correction s‖ ≤ ‖seedDefect s‖ / (2 * |s.im| * (s.re - 1)) := by
  have him : (kernelEisensteinSpectralParameter s).im ≠ 0 := by
    rw [spectralParameter_im]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hi) (by linarith)
  have h := norm_resolvent_le _ him (seedDefect s)
  rw [correction_eq]
  calc ‖kernelSpectralResolvent (kernelEisensteinSpectralParameter s) (seedDefect s)‖
      ≤ ‖seedDefect s‖ / |(kernelEisensteinSpectralParameter s).im| := h
    _ = ‖seedDefect s‖ / (2 * |s.im| * (s.re - 1)) := by
        rw [spectralParameter_im, abs_mul, abs_mul, abs_two, abs_of_neg (by linarith : 1 - s.re < 0)]
        congr 1
        ring

end GaloisForLFunctions.OrderSixMetaplecticTheory
