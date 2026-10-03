import GaloisForLFunctions.RHTower.PMRamanujanBandTestedContinuation
import GaloisForLFunctions.RHTower.PMRamanujanBandProfileRemainder
import GaloisForLFunctions.RHTower.HardyDyadicWindowTheorem
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Uniform cofinal separation of the complete normalized Ramanujan bands

For every positive damping, the actual complete normalized critical-frequency
vectors cannot converge strongly to any fixed L2 profile. An unconditional
positive critical zero, the literal cleared identity, the complete positive
residue test, and the actual Abel zero supply the contradiction. No simplicity
assumption is used. Completeness strengthens this to one positive cofinal
separation radius independent of the proposed profile.

This does not bound the complete small-damping energy or prove or refute RH.
-/

open MeasureTheory Set Complex Filter Topology
noncomputable section
namespace RHTower

private theorem pmbe_zeta_slope {ρ : ℂ} (hρ : ρ ≠ 1) (hzero : riemannZeta ρ = 0) :
    Tendsto (fun δ : ℝ => riemannZeta (ρ+(δ : ℂ))/(δ : ℂ))
      (𝓝[>] 0) (𝓝 (deriv riemannZeta ρ)) := by
  have hd : HasDerivAt (fun w : ℂ => riemannZeta (ρ+w)) (deriv riemannZeta ρ) 0 := by
    have hz : HasDerivAt riemannZeta (deriv riemannZeta ρ) (ρ+0) := by
      simpa only [add_zero] using (differentiableAt_riemannZeta hρ).hasDerivAt
    have hi : HasDerivAt (fun w : ℂ => ρ+w) 1 0 :=
      (hasDerivAt_id (0 : ℂ)).const_add ρ
    simpa only [mul_one] using! hz.comp (0 : ℂ) hi
  have hdr : HasDerivAt (fun t : ℝ => riemannZeta (ρ+(t : ℂ))) (deriv riemannZeta ρ) 0 :=
    hd.comp_ofReal
  simpa only [zero_add,Complex.ofReal_zero,add_zero,hzero,sub_zero,
    Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv,mul_comm] using
      hdr.tendsto_slope_zero_right

private theorem pmbe_not_tendsto_of_critical_zero {ε : ℝ} (hε : 0 < ε)
    {ρ : ℂ} (hρ : ρ.re = 1/2) (hρi : 0 < ρ.im) (hzero : riemannZeta ρ = 0)
    (F : Lp ℂ 2 (volume : Measure ℝ)) :
    ¬ Tendsto (pmRamanujanNormalizedBandMellinVector ε) atTop (𝓝 F) := by
  intro hc
  obtain ⟨a,b,ha,hab,h,hrep,hgap,_hint,hpos⟩ :=
    exists_pmRamanujanBandResidue_positive_L2_test hε hρ hzero
  have hsupp : ∀ᵐ τ : ℝ, τ ∉ Icc a b → h τ = 0 := by
    filter_upwards [hrep] with τ hτ
    intro ht
    rw [hτ,pmRamanujanBandResidueTest,indicator_of_notMem ht]
  let Q : ℝ → ℂ := fun δ => ∫ X in Ici (1 : ℝ),
    (X : ℂ)^(-(ρ+(δ : ℂ))-(1/2 : ℂ)) * pmRamanujanBandTestedScale ε h X
  let R : ℂ → ℂ := fun w => ∫ τ : ℝ, (starRingEnd ℂ) (h τ) *
    (Icc a b).indicator (pmRamanujanBandClearedKernel ε w) τ
  have hρ1 : ρ ≠ 1 := by intro he; have hh := hρi; simp [he] at hh
  have hl := (pmbe_zeta_slope hρ1 hzero).mul
    (pmRamanujanBandTestedScale_abel_zero hε.le hc h hρ (sub_pos.mpr ha) hgap)
  rw [mul_zero] at hl
  have hleft : Tendsto (fun δ : ℝ => riemannZeta (ρ+(δ : ℂ))*Q δ) (𝓝[>] 0) (𝓝 0) := by
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hn : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (show (0 : ℝ) < δ from hδ).ne'
    rw [← mul_assoc,div_mul_cancel₀ _ hn]
  have hcont : ContinuousAt R ρ :=
    (differentiableAt_pmRamanujanBandClearedKernel_test hε.le h
      (show ρ ∈ pmRamanujanBandKernelTube a from ⟨by rw [hρ]; norm_num,hρi,ha⟩)).continuousAt
  have hshift : Tendsto (fun δ : ℝ => ρ+(δ : ℂ)) (𝓝[>] 0) (𝓝 ρ) := by
    simpa only [Complex.ofReal_zero,add_zero] using
      tendsto_const_nhds.add (Complex.continuous_ofReal.tendsto 0 |>.mono_left nhdsWithin_le_nhds)
  have hright : Tendsto (fun δ : ℝ => R (ρ+(δ : ℂ))) (𝓝[>] 0) (𝓝 (R ρ)) :=
    hcont.tendsto.comp hshift
  have heq : (fun δ : ℝ => riemannZeta (ρ+(δ : ℂ))*Q δ) =ᶠ[𝓝[>] 0]
      (fun δ => R (ρ+(δ : ℂ))) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    apply pmRamanujanBandTestedScale_cleared_continuation hε hc h (hρi.trans ha) hsupp
    · simp only [Complex.add_re,Complex.ofReal_re,hρ]
      exact lt_add_of_pos_right _ hδ
    · simpa using hρi
    · simpa using ha
  have hRzero : R ρ = 0 := tendsto_nhds_unique hright (hleft.congr' heq)
  have hpair : R ρ = ∫ τ : ℝ, (starRingEnd ℂ) (h τ)*pmRamanujanBandResidueNumerator ε ρ τ := by
    apply integral_congr_ae
    filter_upwards [hsupp] with τ hτ
    by_cases ht : τ ∈ Icc a b
    · rw [indicator_of_mem ht,pmRamanujanBandClearedKernel_at_zero ε hzero τ]
    · simp [indicator_of_notMem ht,hτ ht]
  rw [← hpair,hRzero] at hpos
  exact (lt_irrefl 0) hpos

theorem not_tendsto_pmRamanujanNormalizedBandMellinVector {ε : ℝ} (hε : 0 < ε)
    (F : Lp ℂ 2 (volume : Measure ℝ)) :
    ¬ Tendsto (pmRamanujanNormalizedBandMellinVector ε) atTop (𝓝 F) := by
  obtain ⟨T,hT,hzeros⟩ := exists_riemannZeta_line_zero_dyadic
  obtain ⟨γ,hγ,hzero⟩ := hzeros T le_rfl
  apply pmbe_not_tendsto_of_critical_zero hε (ρ := linePt γ) _ _ hzero F
  · norm_num [linePt]
  · simpa only [linePt,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
      Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] using
        hT.trans_le hγ.1

theorem exists_cofinal_pmRamanujanBandProfile_separation {ε : ℝ} (hε : 0 < ε)
    (F : Lp ℂ 2 (volume : Measure ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ B : ℝ, ∃ X : ℝ, B ≤ X ∧
      c ≤ ‖pmRamanujanNormalizedBandMellinVector ε X-F‖ := by
  have hn := not_tendsto_pmRamanujanNormalizedBandMellinVector hε F
  rw [Metric.tendsto_atTop] at hn
  push Not at hn
  simpa only [dist_eq_norm] using hn

theorem not_cauchySeq_pmRamanujanNormalizedBandMellinVector {ε : ℝ} (hε : 0 < ε) :
    ¬ CauchySeq (pmRamanujanNormalizedBandMellinVector ε) := by
  intro hc
  obtain ⟨F,hF⟩ := cauchySeq_tendsto_of_complete hc
  exact not_tendsto_pmRamanujanNormalizedBandMellinVector hε F hF

theorem exists_uniform_pmRamanujanBandProfile_separation {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ F : Lp ℂ 2 (volume : Measure ℝ), ∀ B : ℝ,
      ∃ X : ℝ, B ≤ X ∧ c ≤ ‖pmRamanujanNormalizedBandMellinVector ε X-F‖ := by
  have hn := not_cauchySeq_pmRamanujanNormalizedBandMellinVector hε
  rw [Metric.cauchySeq_iff] at hn
  push Not at hn
  obtain ⟨c,hc,h⟩ := hn
  refine ⟨c/2,half_pos hc,?_⟩
  intro F B
  obtain ⟨X,hX,Y,hY,hXY⟩ := h B
  by_cases hXF : c/2 ≤ dist (pmRamanujanNormalizedBandMellinVector ε X) F
  · exact ⟨X,hX,by simpa only [dist_eq_norm] using hXF⟩
  · refine ⟨Y,hY,?_⟩
    have ht := dist_triangle (pmRamanujanNormalizedBandMellinVector ε X) F
      (pmRamanujanNormalizedBandMellinVector ε Y)
    rw [dist_comm F] at ht
    rw [← dist_eq_norm]
    exact le_of_lt (by linarith [lt_of_not_ge hXF])

end RHTower
