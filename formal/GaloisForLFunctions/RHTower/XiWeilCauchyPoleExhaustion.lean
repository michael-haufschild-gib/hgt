import GaloisForLFunctions.RHTower.XiWeilLineConjHilbert
import GaloisForLFunctions.RHTower.XiWeilPositivityCriterion
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Normalized Cauchy-pole exhaustion of Xi divisor fibers

Regular Cauchy kernels already exhaust every RH-deciding conjugate-fiber sign
direction.  At a centered divisor location `alpha`, normalized kernels

`(alpha - z) / (xiSpectralPoint q - z)`

converge in the multiplicity-exact divisor `ell^(2 : ℕ)` carrier to the indicator of
the complete `alpha` fiber as regular points `z` approach `alpha`.  The proof
uses analytic isolation of Xi zeros and a Cauchy-square majorant.

Consequently positivity on regular two-pole Cauchy packets is equivalent to RH.
This removes full Cauchy-core density from the CCM route: the remaining input is
positivity of the actual semilocal prime--archimedean source form on these
moving two-pole packets.
-/

open Complex Metric Function Filter
open scoped Topology

namespace RHTower

noncomputable section

def xiWeilFiberIndicator (alpha z : ℂ) : ℂ :=
  if z = alpha then 1 else 0

theorem xiWeilFiberIndicator_squareSummable (alpha : ℂ) :
    XiWeilSquareSummable (xiWeilFiberIndicator alpha) := by
  let S : Finset XiZeroCopy := (finite_xiSpectralPoint_fiber alpha).toFinset
  refine summable_of_ne_finset_zero (s := S) ?_
  intro q hq
  have hne : xiSpectralPoint q ≠ alpha := by
    intro h
    apply hq
    simpa only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using h
  simp [xiWeilFiberIndicator, hne]

def xiWeilFiberIndicatorLp (alpha : ℂ) : lp (fun _ : XiZeroCopy => ℂ) 2 :=
  xiWeilEvaluationLp (xiWeilFiberIndicator alpha)
    (xiWeilFiberIndicator_squareSummable alpha)

@[simp] theorem xiWeilFiberIndicatorLp_apply (alpha : ℂ) (q : XiZeroCopy) :
    xiWeilFiberIndicatorLp alpha q =
      if xiSpectralPoint q = alpha then 1 else 0 := rfl

theorem exists_xiSpectralPoint_gap (alpha : ℂ) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ q : XiZeroCopy, xiSpectralPoint q ≠ alpha →
        delta ≤ ‖xiSpectralPoint q - alpha‖ := by
  have hnotEventuallyZero : ¬ ∀ᶠ w in 𝓝 alpha, XiC w = 0 := by
    intro hev
    have hall := XiC_analytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ alpha) hev (Set.mem_univ 0)
    exact XiC_zero_ne hall
  have hpunct : ∀ᶠ w in 𝓝[≠] alpha, XiC w ≠ 0 :=
    (XiC_analytic alpha (Set.mem_univ alpha)).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      hnotEventuallyZero
  obtain ⟨delta, hdelta, hdeltasub⟩ := Metric.mem_nhdsWithin_iff.mp hpunct
  refine ⟨delta, hdelta, ?_⟩
  intro q hq
  by_contra hgap
  have hlt : ‖xiSpectralPoint q - alpha‖ < delta := lt_of_not_ge hgap
  have hmem : xiSpectralPoint q ∈ Metric.ball alpha delta ∩ {alpha}ᶜ := by
    constructor
    · rw [Metric.mem_ball, dist_eq_norm]
      simpa [norm_neg] using hlt
    · exact Set.mem_compl_singleton_iff.mpr hq
  exact hdeltasub hmem (XiC_xiSpectralPoint_eq_zero q)

theorem norm_normalizedCauchy_le
    {alpha z lam : ℂ} (hlam : lam ≠ alpha)
    (hz : ‖z - alpha‖ ≤ ‖lam - alpha‖ / 2) :
    ‖(alpha - z) * (lam - z)⁻¹‖ ≤
      2 * ‖z - alpha‖ / ‖lam - alpha‖ := by
  have hlampos : 0 < ‖lam - alpha‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hlam)
  have hrev := norm_sub_norm_le (lam - alpha) (z - alpha)
  have hid : (lam - alpha) - (z - alpha) = lam - z := by ring
  rw [hid] at hrev
  have hden : ‖lam - alpha‖ / 2 ≤ ‖lam - z‖ := by linarith
  have hdenpos : 0 < ‖lam - z‖ := lt_of_lt_of_le (half_pos hlampos) hden
  rw [norm_mul, norm_inv, norm_sub_rev alpha z]
  rw [show ‖lam - z‖⁻¹ = 1 / ‖lam - z‖ by rw [one_div]]
  have hdiv : 1 / ‖lam - z‖ ≤ 2 / ‖lam - alpha‖ := by
    apply (one_div_le_one_div_of_le (half_pos hlampos) hden).trans_eq
    field_simp
  calc
    ‖z - alpha‖ * (1 / ‖lam - z‖) ≤
        ‖z - alpha‖ * (2 / ‖lam - alpha‖) :=
      mul_le_mul_of_nonneg_left hdiv (norm_nonneg _)
    _ = 2 * ‖z - alpha‖ / ‖lam - alpha‖ := by ring

theorem xiOffRealSignTest_eq_fiberIndicator_sub
    {alpha : ℂ} (h : (starRingEnd ℂ) alpha ≠ alpha) :
    xiOffRealSignTest alpha = fun z =>
      xiWeilFiberIndicator alpha z -
        xiWeilFiberIndicator ((starRingEnd ℂ) alpha) z := by
  funext z
  by_cases hza : z = alpha
  · subst z
    simp [xiOffRealSignTest, xiWeilFiberIndicator, Ne.symm h]
  · by_cases hzb : z = (starRingEnd ℂ) alpha
    · subst z
      simp [xiOffRealSignTest, xiWeilFiberIndicator, h]
    · simp [xiOffRealSignTest, xiWeilFiberIndicator, hza, hzb]

theorem exists_normalizedCauchyLp_tendsto_fiberIndicator_with_cap
    (alpha : ℂ) {cap : ℝ} (hcap : 0 < cap) :
    ∃ c : ℝ, 0 < c ∧ c ≤ cap ∧
      ∃ z : ℕ → XiCRegularPoint,
        (∀ n, (z n : ℂ) = alpha + ((c / (n + 1 : ℕ) : ℝ) : ℂ)) ∧
        Tendsto
          (fun n => (alpha - (z n : ℂ)) • xiWeilCauchyLp (z n))
          atTop (𝓝 (xiWeilFiberIndicatorLp alpha)) := by
  obtain ⟨delta, hdelta, hgap⟩ := exists_xiSpectralPoint_gap alpha
  let c : ℝ := min (delta / 2) (min 1 cap)
  have hcpos : 0 < c := lt_min (half_pos hdelta) (lt_min zero_lt_one hcap)
  have hcdelta : c ≤ delta / 2 := min_le_left _ _
  have hcmin : c ≤ min 1 cap := min_le_right _ _
  have hcone : c ≤ 1 := hcmin.trans (min_le_left _ _)
  have hccap : c ≤ cap := hcmin.trans (min_le_right _ _)
  let r : ℕ → ℝ := fun n => c / (n + 1 : ℕ)
  have hrpos : ∀ n, 0 < r n := by
    intro n
    exact div_pos hcpos (by positivity)
  have hrc : ∀ n, r n ≤ c := by
    intro n
    have hden : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
    exact div_le_self hcpos.le hden
  have hrdelta : ∀ n, r n < delta := by
    intro n
    exact (hrc n).trans_lt (hcdelta.trans_lt (half_lt_self hdelta))
  have hrone : ∀ n, r n ≤ 1 := fun n => (hrc n).trans hcone
  let zval : ℕ → ℂ := fun n => alpha + (r n : ℂ)
  have hznorm : ∀ n, ‖zval n - alpha‖ = r n := by
    intro n
    simp [zval, Complex.norm_real, abs_of_pos (hrpos n)]
  have hzne : ∀ n, zval n ≠ alpha := by
    intro n h
    have hre := congrArg Complex.re h
    simp [zval, (hrpos n).ne'] at hre
  have hzregular : ∀ n, XiC (zval n) ≠ 0 := by
    intro n hzero
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy (zval n)).mp hzero
    have hqne : xiSpectralPoint q ≠ alpha := hq.trans_ne (hzne n)
    have hqgap := hgap q hqne
    rw [hq, hznorm] at hqgap
    linarith [hrdelta n]
  let z : ℕ → XiCRegularPoint := fun n => ⟨zval n, hzregular n⟩
  have hrtend : Tendsto r atTop (𝓝 0) := by
    exact (tendsto_const_div_atTop_nhds_zero_nat c).comp (tendsto_add_atTop_nat 1)
  have hztend : Tendsto zval atTop (𝓝 alpha) := by
    simpa [zval] using tendsto_const_nhds.add (Complex.ofRealCLM.continuous.tendsto 0 |>.comp hrtend)
  let term : ℕ → XiZeroCopy → ℝ := fun n q =>
    ‖(alpha - zval n) * xiWeilCauchyTest (zval n) (xiSpectralPoint q) -
      xiWeilFiberIndicator alpha (xiSpectralPoint q)‖ ^ (2 : ℕ)
  let bound : XiZeroCopy → ℝ := fun q =>
    4 * ‖xiWeilCauchyTest alpha (xiSpectralPoint q)‖ ^ (2 : ℕ)
  have hboundsum : Summable bound := by
    exact (XiWeilSquareSummable_cauchy alpha).mul_left 4
  have hterm_tend : ∀ q, Tendsto (fun n => term n q) atTop (𝓝 0) := by
    intro q
    by_cases hq : xiSpectralPoint q = alpha
    · have hzero : ∀ n, term n q = 0 := by
        intro n
        simp only [term, hq]
        rw [show xiWeilFiberIndicator alpha alpha = 1 by
          simp [xiWeilFiberIndicator], xiWeilCauchyTest]
        have hne : alpha - zval n ≠ 0 := sub_ne_zero.mpr (Ne.symm (hzne n))
        rw [mul_inv_cancel₀ hne]
        norm_num
      simpa only [hzero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · have hden : xiSpectralPoint q - alpha ≠ 0 := sub_ne_zero.mpr hq
      have hfrac : Tendsto
          (fun n => (alpha - zval n) *
            xiWeilCauchyTest (zval n) (xiSpectralPoint q))
          atTop (𝓝 0) := by
        have hnum : Tendsto (fun n => alpha - zval n) atTop (𝓝 0) := by
          have h := (tendsto_const_nhds.sub hztend :
            Tendsto (fun n => alpha - zval n) atTop (𝓝 (alpha - alpha)))
          simpa using h
        have hdenT : Tendsto (fun n => xiSpectralPoint q - zval n)
            atTop (𝓝 (xiSpectralPoint q - alpha)) := tendsto_const_nhds.sub hztend
        simpa [xiWeilCauchyTest] using hnum.mul (hdenT.inv₀ hden)
      have hind : xiWeilFiberIndicator alpha (xiSpectralPoint q) = 0 := by
        simp [xiWeilFiberIndicator, hq]
      simpa [term, hind] using (hfrac.norm.pow 2)
  have hbound : ∀ n q, ‖term n q‖ ≤ bound q := by
    intro n q
    by_cases hq : xiSpectralPoint q = alpha
    · subst hq
      simp [term, bound, xiWeilFiberIndicator, xiWeilCauchyTest,
        sub_ne_zero.mpr (Ne.symm (hzne n))]
    · have hqgap := hgap q hq
      have hzhalf : ‖zval n - alpha‖ ≤ ‖xiSpectralPoint q - alpha‖ / 2 := by
        rw [hznorm]
        exact (hrc n).trans (hcdelta.trans (div_le_div_of_nonneg_right hqgap zero_le_two))
      have hnorm := norm_normalizedCauchy_le hq hzhalf
      have hind : xiWeilFiberIndicator alpha (xiSpectralPoint q) = 0 := by
        simp [xiWeilFiberIndicator, hq]
      have hnorm' :
          ‖(alpha - zval n) * xiWeilCauchyTest (zval n) (xiSpectralPoint q)‖ ≤
            2 / ‖xiSpectralPoint q - alpha‖ := by
        rw [xiWeilCauchyTest]
        exact hnorm.trans (by
          have hp : 0 < ‖xiSpectralPoint q - alpha‖ :=
            norm_pos_iff.mpr (sub_ne_zero.mpr hq)
          apply div_le_div_of_nonneg_right ?_ hp.le
          nlinarith [hznorm n, hrone n])
      have hsq :
          ‖(alpha - zval n) * xiWeilCauchyTest (zval n) (xiSpectralPoint q)‖ ^ (2 : ℕ) ≤
            (2 / ‖xiSpectralPoint q - alpha‖) ^ (2 : ℕ) := by
        gcongr
      dsimp only [term, bound]
      rw [hind, sub_zero, Real.norm_of_nonneg (sq_nonneg _)]
      simp only [xiWeilCauchyTest]
      rw [norm_inv]
      calc
        ‖(alpha - zval n) * (xiSpectralPoint q - zval n)⁻¹‖ ^ (2 : ℕ) ≤
            (2 / ‖xiSpectralPoint q - alpha‖) ^ (2 : ℕ) := hsq
        _ = 4 * ‖xiSpectralPoint q - alpha‖⁻¹ ^ (2 : ℕ) := by
          field_simp
          ring
  have htsum : Tendsto (fun n => ∑' q, term n q) atTop (𝓝 0) := by
    simpa using tendsto_tsum_of_dominated_convergence hboundsum hterm_tend
      (Eventually.of_forall hbound)
  let V : ℕ → lp (fun _ : XiZeroCopy => ℂ) 2 := fun n =>
    (alpha - (z n : ℂ)) • xiWeilCauchyLp (z n)
  let Ialpha : lp (fun _ : XiZeroCopy => ℂ) 2 := xiWeilFiberIndicatorLp alpha
  have hnormsq : ∀ n, ‖V n - Ialpha‖ ^ (2 : ℕ) = ∑' q, term n q := by
    intro n
    rw [HilbertSchmidt.lp_norm_sq_eq]
    apply tsum_congr
    intro q
    rfl
  have hsqzero : Tendsto (fun n => ‖V n - Ialpha‖ ^ (2 : ℕ)) atTop (𝓝 0) := by
    exact htsum.congr' (Eventually.of_forall fun n => (hnormsq n).symm)
  have hnormzero : Tendsto (fun n => ‖V n - Ialpha‖) atTop (𝓝 0) := by
    have hsqrt := hsqzero.sqrt
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hsqrt
  refine ⟨c, hcpos, hccap, z, ?_, ?_⟩
  · intro n
    rfl
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact hnormzero

theorem exists_normalizedCauchyLp_tendsto_fiberIndicator (alpha : ℂ) :
    ∃ z : ℕ → XiCRegularPoint,
      Tendsto
        (fun n => (alpha - (z n : ℂ)) • xiWeilCauchyLp (z n))
        atTop (𝓝 (xiWeilFiberIndicatorLp alpha)) := by
  obtain ⟨_c, _hc, _hcone, z, _hzform, hz⟩ :=
    exists_normalizedCauchyLp_tendsto_fiberIndicator_with_cap alpha zero_lt_one
  exact ⟨z, hz⟩

/-- A regular two-pole Cauchy packet. -/
def xiWeilTwoCauchyPacket
    (z w : XiCRegularPoint) (a b : ℂ) (x : ℂ) : ℂ :=
  a * xiWeilCauchyTest z x + b * xiWeilCauchyTest w x

theorem xiWeilTwoCauchyPacket_squareSummable
    (z w : XiCRegularPoint) (a b : ℂ) :
    XiWeilSquareSummable (xiWeilTwoCauchyPacket z w a b) := by
  have hv := HilbertSchmidt.summable_coe_sq
    (a • xiWeilCauchyLp z + b • xiWeilCauchyLp w)
  simpa [XiWeilSquareSummable, xiWeilTwoCauchyPacket] using hv

theorem xiWeilEvaluationLp_twoCauchyPacket
    (z w : XiCRegularPoint) (a b : ℂ) :
    xiWeilEvaluationLp (xiWeilTwoCauchyPacket z w a b)
        (xiWeilTwoCauchyPacket_squareSummable z w a b) =
      a • xiWeilCauchyLp z + b • xiWeilCauchyLp w := by
  apply Subtype.ext
  funext q
  rfl

theorem xiWeilEvaluationLp_offRealSignTest
    {alpha : ℂ} (h : (starRingEnd ℂ) alpha ≠ alpha) :
    xiWeilEvaluationLp (xiOffRealSignTest alpha)
        (xiOffRealSignTest_squareSummable alpha) =
      xiWeilFiberIndicatorLp alpha -
        xiWeilFiberIndicatorLp ((starRingEnd ℂ) alpha) := by
  apply Subtype.ext
  funext q
  rw [xiWeilEvaluationLp_apply]
  rw [xiOffRealSignTest_eq_fiberIndicator_sub h]
  rfl

theorem xiWeilLineConjLp_sub
    (v w : lp (fun _ : XiZeroCopy => ℂ) 2) :
    xiWeilLineConjLp (v - w) = xiWeilLineConjLp v - xiWeilLineConjLp w := by
  apply Subtype.ext
  funext q
  rfl

theorem tendsto_xiWeilLineConjLp
    {v : ℕ → lp (fun _ : XiZeroCopy => ℂ) 2}
    {x : lp (fun _ : XiZeroCopy => ℂ) 2}
    (h : Tendsto v atTop (𝓝 x)) :
    Tendsto (fun n => xiWeilLineConjLp (v n)) atTop
      (𝓝 (xiWeilLineConjLp x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  rw [tendsto_iff_norm_sub_tendsto_zero] at h
  convert h using 1
  funext n
  rw [← xiWeilLineConjLp_sub, norm_xiWeilLineConjLp]

/-- Positivity on every regular two-pole packet. -/
def XiWeilRegularTwoCauchyNonneg : Prop :=
  ∀ (z w : XiCRegularPoint) (a b : ℂ),
    0 ≤ (xiWeilPolarization (xiWeilTwoCauchyPacket z w a b)
      (xiWeilTwoCauchyPacket z w a b)).re

theorem riemannHypothesis_iff_regularTwoCauchy_nonneg :
    RiemannHypothesis ↔ XiWeilRegularTwoCauchyNonneg := by
  constructor
  · intro hRH z w a b
    exact xiWeilPolarization_diagonal_nonneg_of_riemannHypothesis hRH _
      (xiWeilTwoCauchyPacket_squareSummable z w a b)
  · intro hpos
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    let alpha : ℂ := xiSpectralPoint q
    by_cases hreal : (starRingEnd ℂ) alpha = alpha
    · exact ⟨alpha.re, (Complex.conj_eq_iff_re.mp hreal).symm⟩
    · obtain ⟨z, hz⟩ := exists_normalizedCauchyLp_tendsto_fiberIndicator alpha
      obtain ⟨w, hw⟩ :=
        exists_normalizedCauchyLp_tendsto_fiberIndicator ((starRingEnd ℂ) alpha)
      let F : ℕ → ℂ → ℂ := fun n =>
        xiWeilTwoCauchyPacket (z n) (w n)
          (alpha - (z n : ℂ))
          (-((starRingEnd ℂ) alpha - (w n : ℂ)))
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
              ((starRingEnd ℂ) alpha - (w n : ℂ)) • xiWeilCauchyLp (w n) := by
          funext n
          apply Subtype.ext
          funext q'
          change F n (xiSpectralPoint q') =
            (alpha - (z n : ℂ)) * xiWeilCauchyTest (z n) (xiSpectralPoint q') -
              ((starRingEnd ℂ) alpha - (w n : ℂ)) *
                xiWeilCauchyTest (w n) (xiSpectralPoint q')
          simp only [F, xiWeilTwoCauchyPacket]
          ring
        have helim : Vlim = xiWeilFiberIndicatorLp alpha -
            xiWeilFiberIndicatorLp ((starRingEnd ℂ) alpha) := by
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
        exact hpos (z n) (w n) _ _
      have hlimnonneg :
          0 ≤ (xiWeilPolarization (xiOffRealSignTest alpha)
            (xiOffRealSignTest alpha)).re :=
        ge_of_tendsto hpolre (Eventually.of_forall hnonneg)
      have hneg := xiWeilPolarization_offRealSignTest_re_neg q hreal
      exact False.elim (not_lt_of_ge hlimnonneg hneg)

end
end RHTower
