import GaloisForLFunctions.RHTower.CCM.CCMPrimePoleSchurKernel
import GaloisForLFunctions.RHTower.CCM.CCMCoherentGammaPhysicalStability

/-!
# A genuine mixed Gamma and actual-prime edge bound

Exact local prime rigidity and compactness of the actual archimedean embedding
give an infinitesimal interpolation bound on the complete constrained source.
The coefficient of the form norm can be arbitrarily small. The compensating
edge constant is proved to exist, but no cofinal aperture rate is asserted.
That quantitative issue is essential before this bound can pay the full signed
restricted-Weil residual.
-/

open Complex MeasureTheory Set Filter
open scoped InnerProduct Topology
noncomputable section
namespace RHTower

private theorem edge_smul (a : SuzukiPositiveAperture) (h : ℝ) (c : ℂ) (f : SoninL2) :
    ccmPrimePoleEdgeEnergy a h (c • f) = ‖c‖ ^ 2 * ccmPrimePoleEdgeEnergy a h f := by
  unfold ccmPrimePoleEdgeEnergy
  rw [← integral_const_mul]
  have hs := Lp.coeFn_smul c f
  have ht := hs.comp_tendsto (measurePreserving_add_right volume h).quasiMeasurePreserving.tendsto_ae
  apply integral_congr_ae
  filter_upwards [hs,ht] with x hs ht
  change (c • f) (x+h) = c * f (x+h) at ht
  change (c • f) x = c * f x at hs
  unfold ccmPrimePoleEdgeDensity
  by_cases hx : x ∈ centralInterval a.1 ∩ (fun y : ℝ => y+h) ⁻¹' centralInterval a.1
  · simp only [indicator_of_mem hx]
    rw [hs,ht, show (primePoleProfile x : ℂ)*(c*f (x+h))-
        (primePoleProfile (x+h) : ℂ)*(c*f x) =
      c*((primePoleProfile x : ℂ)*f (x+h)-(primePoleProfile (x+h) : ℂ)*f x) by ring,
      norm_mul, mul_pow]
    ring
  · simp only [indicator_of_notMem hx,mul_zero]

private theorem schur_smul (a : SuzukiPositiveAperture) (c : ℂ) (f : SoninL2) :
    ccmPrimePoleSchurEnergy a (c • f) = ‖c‖ ^ 2 * ccmPrimePoleSchurEnergy a f := by
  unfold ccmPrimePoleSchurEnergy
  simp_rw [edge_smul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Any positive fraction of actual archimedean energy, combined with a
finite multiple of actual-prime edge energy, controls every constrained
physical source at this aperture. No finite-dimensional cutoff is imposed. -/
theorem exists_ccmPolarConstrained_gamma_schur_interpolation
    (a : SuzukiPositiveAperture) (ha : Real.log 2 + Real.log 3 ≤ 2*a.1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ccmPolarConstraintSubmodule a,
      ‖ccmArchimedeanFormToAperture a u.1‖ ^ 2 ≤
        ε * ‖u.1‖ ^ 2 + C *
          ccmPrimePoleSchurEnergy a (ccmArchimedeanFormToAperture a u.1).1 := by
  classical
  by_contra h
  push Not at h
  let J := ccmArchimedeanFormToAperture a
  have bad (n : ℕ) : ∃ u : ccmPolarConstraintSubmodule a,
      ε * ‖u.1‖ ^ 2 + (n+1 : ℝ) * ccmPrimePoleSchurEnergy a (J u.1).1 < ‖J u.1‖ ^ 2 :=
    h (n+1 : ℝ) (by positivity)
  choose u hu using bad
  have hpos (n : ℕ) : 0 < ‖(u n).1‖ := by
    apply norm_pos_iff.mpr
    intro hz
    have hn := hu n
    simp only [hz,map_zero,norm_zero,zero_pow two_ne_zero,mul_zero,zero_add,
      ZeroMemClass.coe_zero] at hn
    exact (not_lt_of_ge (mul_nonneg (by positivity)
      (ccmPrimePoleSchurEnergy_nonneg a 0))) hn
  let v : ℕ → CCMArchimedeanFormDomain a :=
    fun n => (‖(u n).1‖⁻¹ : ℂ) • (u n).1
  have hscalar (n : ℕ) : ‖(‖(u n).1‖⁻¹ : ℂ)‖ = ‖(u n).1‖⁻¹ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hpos n)]
  have hvnorm (n : ℕ) : ‖v n‖ = 1 := by
    dsimp only [v]
    rw [norm_smul,hscalar,inv_mul_cancel₀ (hpos n).ne']
  have hvpolar (n : ℕ) : IsPolarConstrained a (v n) :=
    (show IsPolarConstrained a (u n).1 from (u n).2).smul _
  have hscaled (n : ℕ) : ε + (n+1 : ℝ) * ccmPrimePoleSchurEnergy a (J (v n)).1 <
      ‖J (v n)‖ ^ 2 := by
    have hm := mul_lt_mul_of_pos_left (hu n) (sq_pos_of_pos (inv_pos.mpr (hpos n)))
    have hc : ‖(u n).1‖⁻¹ ^ 2 * ‖(u n).1‖ ^ 2 = 1 := by
      rw [← mul_pow,inv_mul_cancel₀ (hpos n).ne',one_pow]
    simp only [v,map_smul,Submodule.coe_smul,schur_smul,norm_smul,hscalar,mul_pow]
    nlinarith
  let B := ‖J‖ ^ 2
  have hJbound (n : ℕ) : ‖J (v n)‖ ^ 2 ≤ B := by
    have hn := J.le_opNorm (v n)
    rw [hvnorm,mul_one] at hn
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg J)).mpr hn
  have henergy : Tendsto (fun n => ccmPrimePoleSchurEnergy a (J (v n)).1) atTop (𝓝 0) := by
    have hi : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    have hb : Tendsto (fun n : ℕ => B/(n+1 : ℝ)) atTop (𝓝 0) := by
      simpa only [Nat.cast_add,Nat.cast_one,div_eq_mul_inv,mul_zero] using hi.const_mul B
    apply squeeze_zero (fun _ => ccmPrimePoleSchurEnergy_nonneg a _) _ hb
    intro n
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < n+1)).mpr
    nlinarith [hscaled n,hJbound n]
  have hK := (isCompactOperator_ccmArchimedeanFormToAperture a).isCompact_closure_image_closedBall
    (1 : ℝ)
  have hmem : ∀ᶠ n in atTop,
      J (v n) ∈ closure (J '' Metric.closedBall (0 : CCMArchimedeanFormDomain a) 1) := by
    apply Eventually.of_forall
    intro n
    apply subset_closure
    refine ⟨v n, ?_, rfl⟩
    simp only [Metric.mem_closedBall,dist_zero_right,hvnorm,le_refl]
  obtain ⟨f,_,φ,hφ,hconv⟩ := hK.isSeqCompact.subseq_of_frequently_in hmem.frequently
  change Tendsto (fun n => J (v (φ n))) atTop (𝓝 f) at hconv
  have hmass : ε ≤ ‖f‖ ^ 2 := by
    have hn := ((show Continuous (fun g : suzukiApertureHilbert a => ‖g‖ ^ 2) from
      continuous_norm.pow 2).tendsto f).comp hconv
    change Tendsto (fun n => ‖J (v (φ n))‖ ^ 2) atTop (𝓝 (‖f‖ ^ 2)) at hn
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hn
    apply Eventually.of_forall
    intro n
    have he := mul_nonneg (show (0 : ℝ) ≤ φ n+1 by positivity)
      (ccmPrimePoleSchurEnergy_nonneg a (J (v (φ n))).1)
    change ε ≤ ‖J (v (φ n))‖ ^ 2
    exact (le_add_of_nonneg_right he).trans (hscaled (φ n)).le
  have hpole (s : ℝ) (hs : ∀ n, inner ℂ (ccmPolarApertureVector a s) (J (v n)) = 0) :
      inner ℂ (ccmPolarApertureVector a s) f = 0 := by
    have ht := ((innerSL ℂ (ccmPolarApertureVector a s)).continuous.tendsto f).comp hconv
    have hz : Tendsto (fun n => inner ℂ (ccmPolarApertureVector a s) (J (v (φ n))))
        atTop (𝓝 0) := by
      simp only [hs]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique ht hz
  have hdiff : Tendsto (fun n => ‖J (v (φ n))-f‖ ^ 2) atTop (𝓝 0) := by
    have hn := ((show Continuous (fun g : suzukiApertureHilbert a => ‖g-f‖ ^ 2) from
      (continuous_id.sub continuous_const).norm.pow 2).tendsto f).comp hconv
    simp only [sub_self,norm_zero,zero_pow two_ne_zero] at hn
    change Tendsto (fun n => ‖J (v (φ n))-f‖ ^ 2) atTop (𝓝 0) at hn
    exact hn
  have hezero : ccmPrimePoleSchurEnergy a f.1 = 0 := by
    apply le_antisymm _ (ccmPrimePoleSchurEnergy_nonneg a _)
    have hb := ((henergy.comp hφ.tendsto_atTop).const_mul 2).add
      (hdiff.const_mul (4*ccmPrimePoleSchurEnvelope a))
    simp only [mul_zero,zero_add] at hb
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hb
    apply Eventually.of_forall
    intro n
    change ccmPrimePoleSchurEnergy a f.1 ≤
      2 * ccmPrimePoleSchurEnergy a (J (v (φ n))).1 +
        4 * ccmPrimePoleSchurEnvelope a * ‖J (v (φ n))-f‖ ^ 2
    have hs := ccmPrimePoleSchurEnergy_sub_le a (J (v (φ n))) (J (v (φ n))-f)
    rw [sub_sub_cancel] at hs
    have hd := ccmPrimePoleSchurEnergy_le_two_envelope a (J (v (φ n))-f)
    linarith only [hs,hd]
  have hfzero := eq_zero_of_ccmSchurEnergy_zero_of_polar a ha f
    (hpole (1/2) (fun n => (hvpolar n).1))
    (hpole (-1/2) (fun n => (hvpolar n).2)) hezero
  rw [hfzero,norm_zero,zero_pow two_ne_zero] at hmass
  exact (not_le_of_gt hε) hmass

private theorem supported_cost_le_physical (a : SuzukiPositiveAperture) (N : ℕ) (f : SoninL2) :
    ccmActualHeadSupportedCoherentGammaCost a N f ≤
      ccmCoherentGammaPhysicalBound (2*a.1) N * ‖f‖ ^ 2 := by
  have hz : ccmActualHeadSupportedCoherentGammaCost a N 0 = 0 := by
    simp [ccmActualHeadSupportedCoherentGammaCost,ccmActualHeadSupportedCoherentField,
      ccmActualHeadQuantileCompletedCoherentField,ccmActualHeadQuantileBulkCoherentField,
      ccmActualHeadQuantileCellCoherentField,ccmActualHeadQuantileTerminalCoherentField]
  have h := abs_ccmActualHeadSupportedCoherentGammaCost_sub_le a N f 0
  rw [hz,sub_zero,sub_zero,norm_zero,add_zero,
    abs_of_nonneg (ccmActualHeadSupportedCoherentGammaCost_nonneg a N f)] at h
  nlinarith

/-- Supported coherent cost can be absorbed by a genuinely mixed form/edge
bound. All prime-prime and prime-terminal cross terms remain in the cost. -/
theorem exists_ccmPolarConstrained_supportedGammaCost_mixed_bound
    (a : SuzukiPositiveAperture) (ha : Real.log 2 + Real.log 3 ≤ 2*a.1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ccmPolarConstraintSubmodule a,
      ccmActualHeadSupportedCoherentGammaCost a (⌊Real.exp (2*a.1)⌋₊+1)
          (ccmArchimedeanFormToAperture a u.1).1 ≤
        ε * ‖u.1‖ ^ 2 + C *
          ccmPrimePoleSchurEnergy a (ccmArchimedeanFormToAperture a u.1).1 := by
  let N := ⌊Real.exp (2*a.1)⌋₊+1
  let B := max 1 (ccmCoherentGammaPhysicalBound (2*a.1) N)
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨C,hC,hbound⟩ := exists_ccmPolarConstrained_gamma_schur_interpolation a ha
    (ε/B) (div_pos hε hB)
  refine ⟨B*C,mul_nonneg hB.le hC,fun u => ?_⟩
  have hphysical := supported_cost_le_physical a N (ccmArchimedeanFormToAperture a u.1).1
  have hmajor := mul_le_mul_of_nonneg_right (le_max_right 1
    (ccmCoherentGammaPhysicalBound (2*a.1) N)) (sq_nonneg ‖ccmArchimedeanFormToAperture a u.1‖)
  have hm := mul_le_mul_of_nonneg_left (hbound u) hB.le
  have hid : B*(ε/B) = ε := mul_div_cancel₀ ε hB.ne'
  simp only [Submodule.norm_coe] at hphysical
  nlinarith

end RHTower
