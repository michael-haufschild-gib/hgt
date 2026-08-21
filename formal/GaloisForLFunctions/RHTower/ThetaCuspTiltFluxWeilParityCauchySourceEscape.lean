import GaloisForLFunctions.RHTower.ThetaCuspTiltFluxWeilParityCauchyLocalization
import GaloisForLFunctions.RHTower.CCMTwoPoleSourceCriterion

/-!
# Exact prime--archimedean source escape along an off-line Xi fiber

The parity-localized two-Cauchy detector can be chosen inside the full continued CCM source domain,
with all pole/reflection collisions excluded at every stage. Along this admissible sequence the
reflection-even energy tends to zero, the reflection-odd energy tends to exact reflected-fiber
multiplicity `N`, and the explicit continued prime--archimedean rank-two source energy tends to
`-N`. In particular, the actual semilocal source energy is eventually strictly negative.

This is stronger than the abstract two-pole RH criterion: it identifies the unique asymptotic
failure geometry and its exact source defect. Any source-side proof of RH need only exclude this
cofinal reflection-antisymmetric escape, while any unconditional local positivity law that does
not control these moving off-line fibers cannot close the route.
-/

open Complex Metric Function Filter
open scoped Topology

namespace RHTower

noncomputable section

/-- Every pair lies in the continued source domain and avoids every pole/reflection collision
needed by the exact rank-two CCM source formula. -/
def CCMAdmissibleTwoPoleSequence
    (z w : ℕ → XiCRegularPoint) : Prop :=
  ∀ n,
    CCMContinuedCauchyDomain (z n : ℂ) ∧
    CCMContinuedCauchyDomain (w n : ℂ) ∧
    (z n : ℂ) ≠ (w n : ℂ) ∧
    (z n : ℂ) ≠ (starRingEnd ℂ) (z n : ℂ) ∧
    (z n : ℂ) ≠ (starRingEnd ℂ) (w n : ℂ) ∧
    (w n : ℂ) ≠ (starRingEnd ℂ) (z n : ℂ) ∧
    (w n : ℂ) ≠ (starRingEnd ℂ) (w n : ℂ)

/-- An off-line Xi fiber forces an admissible cofinal source sequence with exact parity limit
`(even, odd) → (0, N)`, exact source limit `-N`, and eventual strict source negativity. -/
theorem exists_admissibleTwoPoleSource_parity_escape
    (q : XiZeroCopy)
    (h : (starRingEnd ℂ) (xiSpectralPoint q) ≠ xiSpectralPoint q) :
    ∃ z w : ℕ → XiCRegularPoint,
      CCMAdmissibleTwoPoleSequence z w ∧
      let alpha := xiSpectralPoint q
      let beta := (starRingEnd ℂ) alpha
      let F : ℕ → ℂ → ℂ := fun n =>
        xiWeilTwoCauchyPacket (z n) (w n)
          (alpha - (z n : ℂ)) (-(beta - (w n : ℂ)))
      let N : ℝ := (((finite_xiSpectralPoint_fiber alpha).toFinset ∪
        (finite_xiSpectralPoint_fiber beta).toFinset).card : ℝ)
      Tendsto (fun n => xiWeilEvenEnergy (F n)) atTop (𝓝 0) ∧
      Tendsto (fun n => xiWeilOddEnergy (F n)) atTop (𝓝 N) ∧
      Tendsto (fun n => (ccmTwoPoleSourceEnergy
        (z n : ℂ) (w n : ℂ)
        (alpha - (z n : ℂ)) (-(beta - (w n : ℂ)))).re)
        atTop (𝓝 (-N)) ∧
      (∀ᶠ n in atTop, (ccmTwoPoleSourceEnergy
        (z n : ℂ) (w n : ℂ)
        (alpha - (z n : ℂ)) (-(beta - (w n : ℂ)))).re < 0) := by
  let alpha : ℂ := xiSpectralPoint q
  let beta : ℂ := (starRingEnd ℂ) alpha
  have halphaIm : alpha.im ≠ 0 := by
    intro him
    apply h
    exact Complex.conj_eq_iff_im.mpr him
  obtain ⟨c, hc, _hc1, z, hzform, hz⟩ :=
    exists_normalizedCauchyLp_tendsto_fiberIndicator_with_cap alpha zero_lt_one
  obtain ⟨d, hd, hdc, w, hwform, hw⟩ :=
    exists_normalizedCauchyLp_tendsto_fiberIndicator_with_cap beta (half_pos hc)
  have hdc_lt : d < c := hdc.trans_lt (half_lt_self hc)
  have hzIm : ∀ n, (z n : ℂ).im = alpha.im := by
    intro n
    rw [hzform n]
    simp only [Complex.add_im, Complex.ofReal_im, add_zero]
  have hwIm : ∀ n, (w n : ℂ).im = beta.im := by
    intro n
    rw [hwform n]
    simp only [Complex.add_im, Complex.ofReal_im, add_zero]
  have hzRe : ∀ n, (z n : ℂ).re = alpha.re + c / (n + 1 : ℕ) := by
    intro n
    rw [hzform n]
    simp only [Complex.add_re, Complex.ofReal_re]
  have hwRe : ∀ n, (w n : ℂ).re = beta.re + d / (n + 1 : ℕ) := by
    intro n
    rw [hwform n]
    simp only [Complex.add_re, Complex.ofReal_re]
  have hzne : ∀ n, (z n : ℂ) ≠ (w n : ℂ) := by
    intro n heq
    have him := congrArg Complex.im heq
    rw [hzIm n, hwIm n] at him
    simp [beta] at him
    exact halphaIm (by linarith)
  have hzz : ∀ n, (z n : ℂ) ≠ (starRingEnd ℂ) (z n : ℂ) := by
    intro n heq
    have him : (z n : ℂ).im = 0 := Complex.conj_eq_iff_im.mp heq.symm
    rw [hzIm n] at him
    exact halphaIm him
  have hww : ∀ n, (w n : ℂ) ≠ (starRingEnd ℂ) (w n : ℂ) := by
    intro n heq
    have him : (w n : ℂ).im = 0 := Complex.conj_eq_iff_im.mp heq.symm
    rw [hwIm n] at him
    simp [beta] at him
    exact halphaIm (by linarith)
  have hzwc : ∀ n, (z n : ℂ) ≠ (starRingEnd ℂ) (w n : ℂ) := by
    intro n heq
    have hre : (z n : ℂ).re = (w n : ℂ).re := by
      simpa using congrArg Complex.re heq
    rw [hzRe n, hwRe n] at hre
    simp [beta] at hre
    have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have hn0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hn
    field_simp [hn0] at hre
    linarith
  have hwzc : ∀ n, (w n : ℂ) ≠ (starRingEnd ℂ) (z n : ℂ) := by
    intro n heq
    have hre : (w n : ℂ).re = (z n : ℂ).re := by
      simpa using congrArg Complex.re heq
    rw [hzRe n, hwRe n] at hre
    simp [beta] at hre
    have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have hn0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hn
    field_simp [hn0] at hre
    linarith
  have hzdom : ∀ n, CCMContinuedCauchyDomain (z n : ℂ) := by
    intro n
    apply ccmContinuedCauchyDomain_of_regular_same_spectral_im q (z n).property
    exact hzIm n
  have hwdom : ∀ n, CCMContinuedCauchyDomain (w n : ℂ) := by
    intro n
    apply ccmContinuedCauchyDomain_of_regular_same_spectral_im
      (xiZeroCopyLineConjEquiv q) (w n).property
    rw [xiSpectralPoint_lineConj]
    exact hwIm n
  let F : ℕ → ℂ → ℂ := fun n =>
    xiWeilTwoCauchyPacket (z n) (w n)
      (alpha - (z n : ℂ)) (-(beta - (w n : ℂ)))
  have hFsum : ∀ n, XiWeilSquareSummable (F n) := by
    intro n
    exact xiWeilTwoCauchyPacket_squareSummable _ _ _ _
  let V : ℕ → lp (fun _ : XiZeroCopy => ℂ) 2 := fun n =>
    xiWeilEvaluationLp (F n) (hFsum n)
  let Vlim : lp (fun _ : XiZeroCopy => ℂ) 2 :=
    xiWeilEvaluationLp (xiOffRealSignTest alpha)
      (xiOffRealSignTest_squareSummable alpha)
  have hV : Tendsto V atTop (𝓝 Vlim) := by
    have hsub := hz.sub hw
    have heq : V = fun n =>
        (alpha - (z n : ℂ)) • xiWeilCauchyLp (z n) -
          (beta - (w n : ℂ)) • xiWeilCauchyLp (w n) := by
      funext n
      apply Subtype.ext
      funext q'
      change F n (xiSpectralPoint q') =
        (alpha - (z n : ℂ)) * xiWeilCauchyTest (z n) (xiSpectralPoint q') -
          (beta - (w n : ℂ)) * xiWeilCauchyTest (w n) (xiSpectralPoint q')
      simp only [F, xiWeilTwoCauchyPacket]
      ring
    have helim : Vlim = xiWeilFiberIndicatorLp alpha -
        xiWeilFiberIndicatorLp beta := by
      exact xiWeilEvaluationLp_offRealSignTest h
    rw [heq, helim]
    exact hsub
  have henergy := tendsto_xiWeilParityEnergies hFsum
    (xiOffRealSignTest_squareSummable alpha) hV
  have heven := henergy.1
  rw [xiWeilEvenEnergy_offRealSignTest_eq_zero h] at heven
  have hodd := henergy.2
  rw [xiWeilOddEnergy_offRealSignTest_eq_card h] at hodd
  let N : ℝ := (((finite_xiSpectralPoint_fiber alpha).toFinset ∪
    (finite_xiSpectralPoint_fiber beta).toFinset).card : ℝ)
  have hN : 0 < N := by
    have hmem : q ∈ (finite_xiSpectralPoint_fiber alpha).toFinset ∪
        (finite_xiSpectralPoint_fiber beta).toFinset := by
      apply Finset.mem_union_left
      simp [alpha]
    have hNat : 0 < ((finite_xiSpectralPoint_fiber alpha).toFinset ∪
        (finite_xiSpectralPoint_fiber beta).toFinset).card :=
      Finset.card_pos.mpr ⟨q, hmem⟩
    change 0 < (((finite_xiSpectralPoint_fiber alpha).toFinset ∪
      (finite_xiSpectralPoint_fiber beta).toFinset).card : ℝ)
    exact_mod_cast hNat
  have hsourceParity : ∀ n,
      (ccmTwoPoleSourceEnergy (z n : ℂ) (w n : ℂ)
        (alpha - (z n : ℂ)) (-(beta - (w n : ℂ)))).re =
      xiWeilEvenEnergy (F n) - xiWeilOddEnergy (F n) := by
    intro n
    have hs := xiWeilPolarization_twoCauchy_eq_continuedSourceEnergy
      (hzdom n) (hwdom n) (hzne n) (hzz n) (hzwc n) (hwzc n) (hww n)
      (a := alpha - (z n : ℂ)) (b := -(beta - (w n : ℂ)))
    have hp := xiWeilPolarization_self_eq_evenEnergy_sub_oddEnergy (hFsum n)
    change xiWeilPolarization (F n) (F n) = _ at hs
    rw [hp] at hs
    have hre := congrArg Complex.re hs
    norm_num at hre
    simpa only [neg_sub] using hre.symm
  have hsource : Tendsto (fun n => (ccmTwoPoleSourceEnergy
      (z n : ℂ) (w n : ℂ)
      (alpha - (z n : ℂ)) (-(beta - (w n : ℂ)))).re)
      atTop (𝓝 (-N)) := by
    have hfun : (fun n => (ccmTwoPoleSourceEnergy
        (z n : ℂ) (w n : ℂ)
        (alpha - (z n : ℂ)) (-(beta - (w n : ℂ)))).re) =
      fun n => xiWeilEvenEnergy (F n) - xiWeilOddEnergy (F n) := by
      funext n
      exact hsourceParity n
    rw [hfun]
    simpa [N, beta] using heven.sub hodd
  have hsourceNeg : ∀ᶠ n in atTop, (ccmTwoPoleSourceEnergy
      (z n : ℂ) (w n : ℂ)
      (alpha - (z n : ℂ)) (-(beta - (w n : ℂ)))).re < 0 :=
    hsource.eventually_lt_const (by linarith)
  refine ⟨z, w, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact ⟨hzdom n, hwdom n, hzne n, hzz n, hzwc n, hwzc n, hww n⟩
  · simpa only [F, alpha, beta] using heven
  · simpa only [F, N, alpha, beta] using hodd
  · simpa only [N, alpha, beta] using hsource
  · simpa only [alpha, beta] using hsourceNeg

end
end RHTower
