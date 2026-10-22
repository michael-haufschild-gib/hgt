import GaloisForLFunctions.RHTower.XiWeilCauchyPoleExhaustion
import GaloisForLFunctions.RHTower.XiWeilResolventSource
import GaloisForLFunctions.RHTower.SeamStripRamification

/-!
# The explicit two-pole CCM source form

The Xi-Weil square of a regular two-pole Cauchy packet is exactly a four-term
divided-difference form in the meromorphically continued prime--archimedean
relative trace.  This is the source-side form on which the remaining CCM
positivity problem lives.
-/

open Complex

namespace RHTower

noncomputable section

/-- The continued prime--archimedean divided-difference kernel. -/
def ccmContinuedCauchyKernel (z w : ℂ) : ℂ :=
  (continuedPrimeArchSourceRelativeTrace ((starRingEnd ℂ) w) -
    continuedPrimeArchSourceRelativeTrace z) /
      (z - (starRingEnd ℂ) w)

/-- The explicit rank-two CCM source energy. -/
def ccmTwoPoleSourceEnergy (z w a b : ℂ) : ℂ :=
  a * (starRingEnd ℂ) a * ccmContinuedCauchyKernel z z +
  a * (starRingEnd ℂ) b * ccmContinuedCauchyKernel z w +
  b * (starRingEnd ℂ) a * ccmContinuedCauchyKernel w z +
  b * (starRingEnd ℂ) b * ccmContinuedCauchyKernel w w

def ccmTwoPoleCoeff (z : ℂ) (a b : ℂ) (u : ℂ) : ℂ :=
  if u = z then a else b

/-- Natural pole-free domain for both a pole and its reflected source point. -/
def CCMContinuedCauchyDomain (z : ℂ) : Prop :=
  0 < (1 / 2 + z * I).re ∧
  1 / 2 + z * I ≠ 1 ∧
  riemannZeta (1 / 2 + z * I) ≠ 0 ∧
  0 < (1 / 2 + (starRingEnd ℂ) z * I).re ∧
  1 / 2 + (starRingEnd ℂ) z * I ≠ 1 ∧
  riemannZeta (1 / 2 + (starRingEnd ℂ) z * I) ≠ 0

/-- A regular point with the same imaginary centered coordinate as an actual Xi
divisor point belongs to the full continued source domain.  Real pole motion
therefore preserves both open-strip source evaluations. -/
theorem ccmContinuedCauchyDomain_of_regular_same_spectral_im
    (q : XiZeroCopy) {z : ℂ} (hz : XiC z ≠ 0)
    (him : z.im = (xiSpectralPoint q).im) :
    CCMContinuedCauchyDomain z := by
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hsre : (1 / 2 + z * I).re = (q.1 : ℂ).re := by
    simp [xiSpectralPoint] at him ⊢
    linarith
  have htsre : (1 / 2 + (starRingEnd ℂ) z * I).re = 1 - (q.1 : ℂ).re := by
    simp [xiSpectralPoint] at him ⊢
    linarith
  have hs0 : 0 < (1 / 2 + z * I).re := hsre.symm ▸ hstrip.1
  have hs1 : (1 / 2 + z * I).re < 1 := hsre.symm ▸ hstrip.2
  have ht0 : 0 < (1 / 2 + (starRingEnd ℂ) z * I).re := by
    rw [htsre]
    linarith
  have ht1 : (1 / 2 + (starRingEnd ℂ) z * I).re < 1 := by
    rw [htsre]
    linarith
  have htz : XiC ((starRingEnd ℂ) z) ≠ 0 := by
    rw [XiC_conj]
    intro h
    apply hz
    have := congrArg (starRingEnd ℂ) h
    simpa using this
  refine ⟨hs0, ?_, ?_, ht0, ?_, ?_⟩
  · intro h
    rw [h] at hs1
    norm_num at hs1
  · intro hzero
    apply hz
    exact (xi_zero_iff_zeta_zero_of_mem_strip hs0 hs1).mpr hzero
  · intro h
    rw [h] at ht1
    norm_num at ht1
  · intro hzero
    apply htz
    exact (xi_zero_iff_zeta_zero_of_mem_strip ht0 ht1).mpr hzero

lemma xiWeilCauchyPacket_pair_eq_two
    {z w a b : ℂ} (hz : XiC z ≠ 0) (hw : XiC w ≠ 0) (hzw : z ≠ w) :
    xiWeilCauchyPacket {z, w} (ccmTwoPoleCoeff z a b) =
      xiWeilTwoCauchyPacket
        ⟨z, hz⟩ ⟨w, hw⟩ a b := by
  funext x
  simp [xiWeilCauchyPacket, ccmTwoPoleCoeff, xiWeilTwoCauchyPacket,
    hzw, Ne.symm hzw]

/-- Exact equality between the Xi-Weil square and the explicit continued
prime--archimedean rank-two source form. -/
theorem xiWeilPolarization_twoCauchy_eq_continuedSourceEnergy
    {z w a b : ℂ}
    (hzdom : CCMContinuedCauchyDomain z)
    (hwdom : CCMContinuedCauchyDomain w)
    (hzw : z ≠ w)
    (hzz : z ≠ (starRingEnd ℂ) z)
    (hzwc : z ≠ (starRingEnd ℂ) w)
    (hwzc : w ≠ (starRingEnd ℂ) z)
    (hww : w ≠ (starRingEnd ℂ) w) :
    xiWeilPolarization
        (xiWeilTwoCauchyPacket
          ⟨z, XiC_ne_zero_of_continuedPrimeArch_domain hzdom.1 hzdom.2.1 hzdom.2.2.1⟩
          ⟨w, XiC_ne_zero_of_continuedPrimeArch_domain hwdom.1 hwdom.2.1 hwdom.2.2.1⟩
          a b)
        (xiWeilTwoCauchyPacket
          ⟨z, XiC_ne_zero_of_continuedPrimeArch_domain hzdom.1 hzdom.2.1 hzdom.2.2.1⟩
          ⟨w, XiC_ne_zero_of_continuedPrimeArch_domain hwdom.1 hwdom.2.1 hwdom.2.2.1⟩
          a b) =
      ccmTwoPoleSourceEnergy z w a b := by
  let hzXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_continuedPrimeArch_domain hzdom.1 hzdom.2.1 hzdom.2.2.1
  let hwXi : XiC w ≠ 0 :=
    XiC_ne_zero_of_continuedPrimeArch_domain hwdom.1 hwdom.2.1 hwdom.2.2.1
  have hsource := xiWeilPolarization_cauchyPacket_eq_continuedPrimeArchSource
    (s := {z, w}) (t := {z, w})
    (c := ccmTwoPoleCoeff z a b) (d := ccmTwoPoleCoeff z a b)
    (hzpos := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact hzdom.1
      · exact hwdom.1)
    (hz1 := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact hzdom.2.1
      · exact hwdom.2.1)
    (hzzeta := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact hzdom.2.2.1
      · exact hwdom.2.2.1)
    (hwpos := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact hzdom.2.2.2.1
      · exact hwdom.2.2.2.1)
    (hw1 := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact hzdom.2.2.2.2.1
      · exact hwdom.2.2.2.2.1)
    (hwzeta := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact hzdom.2.2.2.2.2
      · exact hwdom.2.2.2.2.2)
    (hsep := by
      intro u hu v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact hzz
      · exact hzwc
      · exact hwzc
      · exact hww)
  rw [xiWeilCauchyPacket_pair_eq_two hzXi hwXi hzw] at hsource
  rw [hsource]
  simp [ccmTwoPoleSourceEnergy, ccmContinuedCauchyKernel, ccmTwoPoleCoeff,
    hzw, Ne.symm hzw]
  ring

end
end RHTower
open Complex Metric Function Filter
open scoped Topology

namespace RHTower
noncomputable section

/-- Positivity of the explicit continued prime--archimedean source form on all
admissible separated two-pole packets. -/
def CCMContinuedTwoPoleSourcePassivity : Prop :=
  ∀ (z w a b : ℂ),
    CCMContinuedCauchyDomain z →
    CCMContinuedCauchyDomain w →
    z ≠ w →
    z ≠ (starRingEnd ℂ) z →
    z ≠ (starRingEnd ℂ) w →
    w ≠ (starRingEnd ℂ) z →
    w ≠ (starRingEnd ℂ) w →
    0 ≤ (ccmTwoPoleSourceEnergy z w a b).re

/-- Exact source-side RH criterion.  If an off-line Xi fiber existed, two
admissible normalized poles approaching it and its conjugate would converge to
the negative divisor-sign direction. -/
theorem riemannHypothesis_iff_ccmContinuedTwoPoleSourcePassivity :
    RiemannHypothesis ↔ CCMContinuedTwoPoleSourcePassivity := by
  constructor
  · intro hRH z w a b hzdom hwdom hzw hzz hzwc hwzc hww
    rw [← xiWeilPolarization_twoCauchy_eq_continuedSourceEnergy
      hzdom hwdom hzw hzz hzwc hwzc hww]
    exact xiWeilPolarization_diagonal_nonneg_of_riemannHypothesis hRH _
      (xiWeilTwoCauchyPacket_squareSummable _ _ _ _)
  · intro hpos
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    let alpha : ℂ := xiSpectralPoint q
    let beta : ℂ := (starRingEnd ℂ) alpha
    by_cases hreal : beta = alpha
    · exact ⟨alpha.re, (Complex.conj_eq_iff_re.mp hreal).symm⟩
    · have halphaIm : alpha.im ≠ 0 := by
        intro h
        apply hreal
        exact Complex.conj_eq_iff_im.mpr h
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
        have him : (z n : ℂ).im = 0 :=
          Complex.conj_eq_iff_im.mp heq.symm
        rw [hzIm n] at him
        exact halphaIm him
      have hww : ∀ n, (w n : ℂ) ≠ (starRingEnd ℂ) (w n : ℂ) := by
        intro n heq
        have him : (w n : ℂ).im = 0 :=
          Complex.conj_eq_iff_im.mp heq.symm
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
          (alpha - (z n : ℂ))
          (-(beta - (w n : ℂ)))
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
              (beta - (w n : ℂ)) *
                xiWeilCauchyTest (w n) (xiSpectralPoint q')
          simp only [F, xiWeilTwoCauchyPacket]
          ring
        have helim : Vlim = xiWeilFiberIndicatorLp alpha -
            xiWeilFiberIndicatorLp beta := by
          exact xiWeilEvaluationLp_offRealSignTest hreal
        rw [heq, helim]
        exact hsub
      have hJV := tendsto_xiWeilLineConjLp hV
      have hinner : Tendsto
          (fun n => inner ℂ (xiWeilLineConjLp (V n)) (V n))
          atTop (𝓝 (inner ℂ (xiWeilLineConjLp Vlim) Vlim)) :=
        hJV.inner hV
      have hpol : Tendsto
          (fun n => xiWeilPolarization (F n) (F n))
          atTop (𝓝 (xiWeilPolarization (xiOffRealSignTest alpha)
            (xiOffRealSignTest alpha))) := by
        have hfun : (fun n => inner ℂ (xiWeilLineConjLp (V n)) (V n)) =
            fun n => xiWeilPolarization (F n) (F n) := by
          funext n
          dsimp [V]
          exact inner_xiWeilLineConjLp_evaluation_eq_polarization
            (F n) (F n) (hFsum n) (hFsum n)
        have hlim : inner ℂ (xiWeilLineConjLp Vlim) Vlim =
            xiWeilPolarization (xiOffRealSignTest alpha)
              (xiOffRealSignTest alpha) := by
          dsimp [Vlim]
          exact inner_xiWeilLineConjLp_evaluation_eq_polarization
            (xiOffRealSignTest alpha) (xiOffRealSignTest alpha)
            (xiOffRealSignTest_squareSummable alpha)
            (xiOffRealSignTest_squareSummable alpha)
        rwa [hfun, hlim] at hinner
      have hpolre : Tendsto
          (fun n => (xiWeilPolarization (F n) (F n)).re)
          atTop (𝓝 (xiWeilPolarization (xiOffRealSignTest alpha)
            (xiOffRealSignTest alpha)).re) :=
        Complex.continuous_re.continuousAt.tendsto.comp hpol
      have hnonneg : ∀ n, 0 ≤ (xiWeilPolarization (F n) (F n)).re := by
        intro n
        have hs := hpos (z n) (w n)
          (alpha - (z n : ℂ)) (-(beta - (w n : ℂ)))
          (hzdom n) (hwdom n) (hzne n) (hzz n) (hzwc n) (hwzc n) (hww n)
        rw [← xiWeilPolarization_twoCauchy_eq_continuedSourceEnergy
          (hzdom n) (hwdom n) (hzne n) (hzz n) (hzwc n) (hwzc n) (hww n)] at hs
        exact hs
      have hlimnonneg :
          0 ≤ (xiWeilPolarization (xiOffRealSignTest alpha)
            (xiOffRealSignTest alpha)).re :=
        ge_of_tendsto hpolre (Eventually.of_forall hnonneg)
      have hneg := xiWeilPolarization_offRealSignTest_re_neg q hreal
      exact False.elim (not_lt_of_ge hlimnonneg hneg)

end
end RHTower
