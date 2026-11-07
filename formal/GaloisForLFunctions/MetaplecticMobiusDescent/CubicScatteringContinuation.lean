/-
Scattering continuation adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.PositiveCubicWhittakerFactors

/-!
# Meromorphic continuation of nonzero cubic scattering coefficients

Divide each bounded Fourier test by its analytic Whittaker height factor.
Positivity at the residual parameter makes that factor nonzero there.
Initial source matching and analytic uniqueness identify the resulting
meromorphic scalar with the original scattering series on an open set.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified

lemma cuspWhittakerHeightFactor_analyticAt (h : O) (s : ℂ) (hs : 1<s.re) :
    AnalyticAt ℂ (fun w => cuspWhittakerHeightFactor w h) s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have hopen : IsOpen {w : ℂ | 1<w.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with w hw
  exact cuspWhittakerAverage_differentiableAt (cuspFrequency h) w hw

lemma kernelCuspFourierFamily_analyticAt_nonreal (h : O) (a b : ℝ)
    (ha : 0<a) (hab : a<b) (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (kernelCuspFourierFamily h a b ha hab) s := by
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := ℂ)
    (kernelCuspFourier h) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal kernelCuspAverageCompact
        kernelCuspAverageCompact_isCompact a b ha hab s hs hi) rfl

def continuedNonzeroScattering (h : O) (s : ℂ) : ℂ :=
  kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s /
    (((9*Real.sqrt 3/2:ℝ):ℂ)*cuspWhittakerHeightFactor s h)

def nonzeroScatteringResidue (h : O) : ℂ :=
  kernelCuspFourier h cubicEisensteinResidue /
    (((9*Real.sqrt 3/2:ℝ):ℂ)*cuspWhittakerHeightFactor (4/3:ℂ) h)

lemma continuedNonzeroScattering_meromorphicAt_center (h : O) :
    MeromorphicAt (continuedNonzeroScattering h) (4/3:ℂ) := by
  exact (kernelCuspFourierFamily_meromorphicAt h 2 3 (by norm_num) (by norm_num)).div
    ((analyticAt_const.mul (cuspWhittakerHeightFactor_analyticAt h (4/3) (by norm_num))).meromorphicAt)

lemma continuedNonzeroScattering_meromorphicOn_upper (h : O) :
    MeromorphicOn (continuedNonzeroScattering h) {s : ℂ | 1<s.re ∧ 0<s.im} := by
  intro s hs
  exact (kernelCuspFourierFamily_analyticAt_nonreal h 2 3 (by norm_num) (by norm_num)
    s (ne_of_gt hs.1) (ne_of_gt hs.2)).meromorphicAt.div
    ((analyticAt_const.mul (cuspWhittakerHeightFactor_analyticAt h s hs.1)).meromorphicAt)

lemma continuedNonzeroScattering_residue_limit (h : O) :
    Tendsto (fun s : ℂ => (s-4/3)*continuedNonzeroScattering h s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (nonzeroScatteringResidue h)) := by
  have hden : Tendsto (fun s : ℂ => ((9*Real.sqrt 3/2:ℝ):ℂ)*cuspWhittakerHeightFactor s h)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (((9*Real.sqrt 3/2:ℝ):ℂ)*cuspWhittakerHeightFactor (4/3:ℂ) h)) := (continuousAt_const.mul
    (cuspWhittakerHeightFactor_analyticAt h (4/3) (by norm_num)).continuousAt).tendsto.mono_left
      (show 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ) from nhdsWithin_le_nhds)
  have hlimit := (kernelCuspFourierFamily_residue_limit h 2 3 (by norm_num) (by norm_num)).div hden
    (mul_ne_zero cusp_volume_ne_zero (cuspWhittakerHeightFactor_center_ne_zero h))
  change Tendsto (fun s : ℂ =>
      ((s-4/3)*kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s)/
        (((9*Real.sqrt 3/2:ℝ):ℂ)*cuspWhittakerHeightFactor s h))
      (𝓝[≠] (4/3:ℂ)) (𝓝 (nonzeroScatteringResidue h)) at hlimit
  convert hlimit using 1
  funext s
  exact (mul_div_assoc _ _ _).symm

lemma continuedNonzeroScattering_initial (h : O) (hh : h≠0) (s : ℂ)
    (hs : 4<s.re) (hi : 0<s.im) (hH : cuspWhittakerHeightFactor s h≠0) :
    continuedNonzeroScattering h s=scatteringCoefficient s h := by
  unfold continuedNonzeroScattering
  rw [kernelCuspFourierFamily_nonzero_of_initial_overlap h hh 2 3
    (by norm_num) (by norm_num) s (by linarith)
    (kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi)]
  field_simp [cusp_volume_ne_zero,hH]

lemma cuspWhittakerHeightFactor_ne_zero_near_five (h : O) :
    ∀ᶠ s : ℂ in 𝓝 (5:ℂ),4<s.re ∧ cuspWhittakerHeightFactor s h≠0 := by
  have hpos := cuspWhittakerHeightFactor_real_re_pos 5 (by norm_num) h
  have hH : cuspWhittakerHeightFactor (5:ℂ) h≠0 := by
    intro he
    norm_num only [Complex.ofReal_ofNat] at hpos
    rw [he,Complex.zero_re] at hpos
    exact lt_irrefl 0 hpos
  have hre : ∀ᶠ s : ℂ in 𝓝 (5:ℂ),4<s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  exact hre.and ((cuspWhittakerHeightFactor_analyticAt h 5 (by norm_num)).continuousAt.eventually_ne hH)

lemma kernelCuspFourierFamily_eq_upper (h : O) (hh : h≠0) :
    Set.EqOn (kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num))
      (fun s => ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWhittakerHeightFactor s h)
      {s : ℂ | 2<s.re ∧ 0<s.im} := by
  let domain : Set ℂ := {s | 2<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (2:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hleft : AnalyticOnNhd ℂ (kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num)) domain := by
    intro s hs
    exact kernelCuspFourierFamily_analyticAt_nonreal h 2 3 (by norm_num) (by norm_num)
      s (by linarith [hs.1]) hs.2.ne'
  have hright : AnalyticOnNhd ℂ
      (fun s => ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWhittakerHeightFactor s h) domain := by
    intro s hs
    exact (analyticAt_const.mul (scatteringCoefficient_analyticOnNhd h s hs.1)).mul
      (cuspWhittakerHeightFactor_analyticAt h s (by linarith [hs.1]))
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s : ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : (kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num))
      =ᶠ[𝓝 (5+Complex.I:ℂ)]
        (fun s => ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWhittakerHeightFactor s h) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    exact kernelCuspFourierFamily_nonzero_of_initial_overlap h hh 2 3
      (by norm_num) (by norm_num) s (by linarith [hs.1])
      (kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs.1 hs.2)
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright hconvex.isPreconnected hstart hevent

lemma continuedNonzeroScattering_eq_upper (h : O) (hh : h≠0) (s : ℂ)
    (hs : 2<s.re) (hi : 0<s.im) (hH : cuspWhittakerHeightFactor s h≠0) :
    continuedNonzeroScattering h s=scatteringCoefficient s h := by
  unfold continuedNonzeroScattering
  rw [kernelCuspFourierFamily_eq_upper h hh ⟨hs,hi⟩]
  field_simp [cusp_volume_ne_zero,hH]

lemma continuedNonzeroScattering_initial_open (h : O) (hh : h≠0) :
    ∃U : Set ℂ,IsOpen U ∧ U.Nonempty ∧ U⊆{s : ℂ | 4<s.re ∧ 0<s.im} ∧
      Set.EqOn (continuedNonzeroScattering h) (fun s => scatteringCoefficient s h) U := by
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp (cuspWhittakerHeightFactor_ne_zero_near_five h)
  let z : ℂ := 5+(ε/2:ℝ)*Complex.I
  have hz : dist z (5:ℂ)<ε := by
    have hdist : dist z (5:ℂ)=ε/2 := by
      simp [z,dist_eq_norm,hε.le]
    rw [hdist]
    linarith
  have hzim : 0<z.im := by simpa [z] using half_pos hε
  refine ⟨Metric.ball (5:ℂ) ε ∩ {s : ℂ | 0<s.im},
    Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im),⟨z,hz,hzim⟩,?_,?_⟩
  · intro s hs
    exact ⟨(hball hs.1).1,hs.2⟩
  · intro s hs
    exact continuedNonzeroScattering_initial h hh s (hball hs.1).1 hs.2 (hball hs.1).2


#print axioms continuedNonzeroScattering_meromorphicAt_center
#print axioms continuedNonzeroScattering_residue_limit
#print axioms continuedNonzeroScattering_initial_open
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
