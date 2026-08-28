import GaloisForLFunctions.RHTower.XiEntireGaussianReflectionFibreCovariance
import GaloisForLFunctions.RHTower.ProjectiveReciprocalHorizonWardSeamSaturation
import GaloisForLFunctions.RHTower.SlabFullWidthAdmissibility

/-!
# Centered real-shift extraction of Xi diagonal multiplicity

For a finite-order analytic zero `x`, the symmetric positive-real shift packet

`eps / 2 * (f'/f (x + eps) - f'/f (x - eps))`

converges to the exact analytic multiplicity at `x`.  Specializing to centered Xi and replacing
both regular logarithmic derivatives by the continued prime--archimedean source gives a source-only
diagonal extractor.  It remains valid for arbitrary multiplicity and arbitrarily small nonzero
real shifts.  Thus diagonal collision mass can be separated before a divisor projector is formed.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Centered positive-real shift packet for the logarithmic derivative of an analytic function. -/
def centeredLogDerivRealShiftExtractor
    (f : ℂ → ℂ) (x : ℂ) (n : ℕ) : ℂ :=
  let eps : ℝ := 1 / ((n : ℝ) + 1)
  (eps / 2 : ℂ) * (logDeriv f (x + (eps : ℂ)) -
    logDeriv f (x - (eps : ℂ)))

/-- A centered pair of positive real displacements extracts exact analytic multiplicity. -/
theorem tendsto_centeredLogDerivRealShiftExtractor
    {f : ℂ → ℂ} {x : ℂ} {d : ℕ}
    (hf : AnalyticAt ℂ f x) (horder : analyticOrderAt f x = d) :
    Tendsto (centeredLogDerivRealShiftExtractor f x) atTop (nhds (d : ℂ)) := by
  let eps : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have heps : Tendsto eps atTop (nhds 0) := by
    simpa only [eps] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hepsC : Tendsto (fun n => (eps n : ℂ)) atTop (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp heps
  have heps_ne : ∀ n, eps n ≠ 0 := by
    intro n
    exact one_div_ne_zero (by positivity)
  have hplusN : Tendsto (fun n => x + (eps n : ℂ)) atTop (nhds x) := by
    simpa using tendsto_const_nhds.add hepsC
  have hplusWithin : Tendsto (fun n => x + (eps n : ℂ)) atTop (𝓝[≠] x) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hplusN, Filter.Eventually.of_forall fun n => ?_⟩
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, add_eq_left] using
      (ofReal_ne_zero.mpr (heps_ne n))
  have hminusN : Tendsto (fun n => x - (eps n : ℂ)) atTop (nhds x) := by
    simpa using tendsto_const_nhds.sub hepsC
  have hminusWithin : Tendsto (fun n => x - (eps n : ℂ)) atTop (𝓝[≠] x) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hminusN, Filter.Eventually.of_forall fun n => ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    apply ofReal_ne_zero.mpr (heps_ne n)
    linear_combination -h
  have hres :=
    RHTower.AnalyticAt.tendsto_sub_mul_logDeriv_of_analyticOrderAt_eq_natCast_complex
      hf horder
  have hplus := hres.comp hplusWithin
  have hminus := hres.comp hminusWithin
  have hhalf : Tendsto (fun _ : ℕ => (1 / 2 : ℂ)) atTop (nhds (1 / 2 : ℂ)) :=
    tendsto_const_nhds
  have havg := hhalf.mul (hplus.add hminus)
  change Tendsto
      (fun n : ℕ => (eps n / 2 : ℂ) *
        (logDeriv f (x + (eps n : ℂ)) -
          logDeriv f (x - (eps n : ℂ))))
      atTop (nhds (d : ℂ))
  convert havg using 1
  · funext n
    simp only [Function.comp_apply]
    ring
  · ring

/-- Xi specialization: the centered shift packet converges to exact Xi multiplicity at every
point, with zero multiplicity at regular points. -/
theorem tendsto_centeredXiCRealShiftExtractor (x : ℂ) :
    Tendsto (centeredLogDerivRealShiftExtractor XiC x) atTop
      (nhds (((analyticOrderAt XiC x).toNat : ℕ) : ℂ)) := by
  apply tendsto_centeredLogDerivRealShiftExtractor
    (XiC_analytic x (Set.mem_univ _))
  exact (ENat.coe_toNat (XiC_order_ne_top x)).symm

/-- Same centered shift packet, defined literally from continued prime--archimedean source values. -/
def centeredPrimeArchRealShiftDiagonalExtractor (x : ℂ) (n : ℕ) : ℂ :=
  let eps : ℝ := 1 / ((n : ℝ) + 1)
  (eps / 2 : ℂ) *
    (continuedPrimeArchSourceRelativeTrace (x + (eps : ℂ)) -
      continuedPrimeArchSourceRelativeTrace (x - (eps : ℂ)))

theorem continuedPrimeArchSourceRelativeTrace_eq_logDeriv_XiC
    {z : ℂ} (hz : XiExplicitAdmissible z) :
    continuedPrimeArchSourceRelativeTrace z = logDeriv XiC z :=
  (continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      hz.re_pos hz.ne_one hz.zeta_ne).trans
    (logDeriv_XiC_eq_relativeResolventTrace
      (XiC_ne_zero_of_admissible hz)).symm

/-- **Pre-divisor diagonal-multiplicity law.**  Inside the open critical band, centered positive
real shifts of the continued pole--Gamma--von-Mangoldt trace converge to exact Xi multiplicity.
No zero enumeration, simplicity assumption, or post-divisor projector occurs in the definition. -/
theorem tendsto_centeredPrimeArchRealShiftDiagonalExtractor
    {x : ℂ} (him : |x.im| < 1 / 2) :
    Tendsto (centeredPrimeArchRealShiftDiagonalExtractor x) atTop
      (nhds (((analyticOrderAt XiC x).toNat : ℕ) : ℂ)) := by
  let eps : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have heps : Tendsto eps atTop (nhds 0) := by
    simpa only [eps] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hepsC : Tendsto (fun n => (eps n : ℂ)) atTop (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp heps
  have heps_ne : ∀ n, eps n ≠ 0 := by
    intro n
    exact one_div_ne_zero (by positivity)
  have hplusN : Tendsto (fun n => x + (eps n : ℂ)) atTop (nhds x) := by
    simpa using tendsto_const_nhds.add hepsC
  have hplusWithin : Tendsto (fun n => x + (eps n : ℂ)) atTop (𝓝[≠] x) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hplusN, Filter.Eventually.of_forall fun n => ?_⟩
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, add_eq_left] using
      (ofReal_ne_zero.mpr (heps_ne n))
  have hminusN : Tendsto (fun n => x - (eps n : ℂ)) atTop (nhds x) := by
    simpa using tendsto_const_nhds.sub hepsC
  have hminusWithin : Tendsto (fun n => x - (eps n : ℂ)) atTop (𝓝[≠] x) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hminusN, Filter.Eventually.of_forall fun n => ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    apply ofReal_ne_zero.mpr (heps_ne n)
    linear_combination -h
  have hpunct : ∀ᶠ w in 𝓝[≠] x, XiC w ≠ 0 :=
    (XiC_analytic x (Set.mem_univ x)).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun hzero => XiC_order_ne_top x (analyticOrderAt_eq_top.mpr hzero))
  have hplus_ne : ∀ᶠ n in atTop, XiC (x + (eps n : ℂ)) ≠ 0 :=
    hplusWithin.eventually hpunct
  have hminus_ne : ∀ᶠ n in atTop, XiC (x - (eps n : ℂ)) ≠ 0 :=
    hminusWithin.eventually hpunct
  apply (tendsto_centeredXiCRealShiftExtractor x).congr'
  filter_upwards [hplus_ne, hminus_ne] with n hpn hmn
  have hAp : XiExplicitAdmissible (x + (eps n : ℂ)) := by
    apply SlabFullWidthAdmissibility.XiExplicitAdmissible_of_abs_im_lt_half
    · simpa using him
    · exact hpn
  have hAm : XiExplicitAdmissible (x - (eps n : ℂ)) := by
    apply SlabFullWidthAdmissibility.XiExplicitAdmissible_of_abs_im_lt_half
    · simpa using him
    · exact hmn
  rw [centeredPrimeArchRealShiftDiagonalExtractor,
    centeredLogDerivRealShiftExtractor]
  rw [continuedPrimeArchSourceRelativeTrace_eq_logDeriv_XiC hAp,
    continuedPrimeArchSourceRelativeTrace_eq_logDeriv_XiC hAm]

/-! ## Finite diagonal-square budget -/

/-- Finite source-only diagonal packet, weighted by exact analytic order.  In the intended nested
contour application the weights are supplied by the inner argument-principle contour. -/
def finitePrimeArchRealShiftDiagonalSquareBudget
    (s : Finset ℂ) (n : ℕ) : ℂ :=
  ∑ x ∈ s, (((analyticOrderAt XiC x).toNat : ℕ) : ℂ) *
    centeredPrimeArchRealShiftDiagonalExtractor x n

/-- Summing before taking the shrinking-shift limit recovers the exact square-multiplicity
diagonal `sum_x m_x²`. -/
theorem tendsto_finitePrimeArchRealShiftDiagonalSquareBudget
    (s : Finset ℂ) (him : ∀ x ∈ s, |x.im| < 1 / 2) :
    Tendsto (finitePrimeArchRealShiftDiagonalSquareBudget s) atTop
      (nhds (∑ x ∈ s,
        ((((analyticOrderAt XiC x).toNat : ℕ) : ℂ)) ^ 2)) := by
  change Tendsto
    (fun n : ℕ => ∑ x ∈ s,
      (((analyticOrderAt XiC x).toNat : ℕ) : ℂ) *
        centeredPrimeArchRealShiftDiagonalExtractor x n)
    atTop (nhds (∑ x ∈ s,
      ((((analyticOrderAt XiC x).toNat : ℕ) : ℂ)) ^ 2))
  apply tendsto_finsetSum s
  intro x hx
  have hconst : Tendsto
      (fun _ : ℕ => (((analyticOrderAt XiC x).toNat : ℕ) : ℂ))
      atTop (nhds (((analyticOrderAt XiC x).toNat : ℕ) : ℂ)) :=
    tendsto_const_nhds
  have hmul := hconst.mul
    (tendsto_centeredPrimeArchRealShiftDiagonalExtractor (him x hx))
  simpa only [pow_two] using hmul

/-! ## Multiplicity-normalized diagonal contraction -/

/-- Shrinking fixed-pole diagonal kernel normalized by the source-only multiplicity extractor. -/
def primeArchMultiplicityNormalizedCauchyDiagonalKernel
    (x y : ℂ) (n : ℕ) : ℂ :=
  meromorphicCauchyDiagonalKernel (1 / ((n : ℝ) + 1)) x y /
    centeredPrimeArchRealShiftDiagonalExtractor x n

/-- On the diagonal, source normalization removes one residue multiplicity. -/
theorem tendsto_primeArchMultiplicityNormalizedCauchyDiagonalKernel_self
    {x : ℂ} (him : |x.im| < 1 / 2)
    (hm : 0 < (analyticOrderAt XiC x).toNat) :
    Tendsto (primeArchMultiplicityNormalizedCauchyDiagonalKernel x x) atTop
      (nhds ((((analyticOrderAt XiC x).toNat : ℕ) : ℂ)⁻¹)) := by
  let m : ℂ := (((analyticOrderAt XiC x).toNat : ℕ) : ℂ)
  have hmC : m ≠ 0 := by
    dsimp only [m]
    exact_mod_cast (Nat.ne_of_gt hm)
  have hone : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hdiv := hone.div
    (tendsto_centeredPrimeArchRealShiftDiagonalExtractor him) hmC
  have hfun :
      (fun n : ℕ => (1 : ℂ) /
        centeredPrimeArchRealShiftDiagonalExtractor x n) =
      (fun _ : ℕ => (1 : ℂ)) /
        centeredPrimeArchRealShiftDiagonalExtractor x := by
    funext n
    rfl
  rw [← hfun] at hdiv
  change Tendsto
      (fun n : ℕ => meromorphicCauchyDiagonalKernel
          (1 / ((n : ℝ) + 1)) x x /
        centeredPrimeArchRealShiftDiagonalExtractor x n)
      atTop (nhds m⁻¹)
  simpa only [meromorphicCauchyDiagonalKernel_self, one_div] using hdiv

/-- At distinct support locations, the same normalized kernel vanishes. -/
theorem tendsto_primeArchMultiplicityNormalizedCauchyDiagonalKernel_of_ne
    {x y : ℂ} (hxy : x ≠ y) (him : |x.im| < 1 / 2)
    (hm : 0 < (analyticOrderAt XiC x).toNat) :
    Tendsto (primeArchMultiplicityNormalizedCauchyDiagonalKernel x y) atTop
      (nhds 0) := by
  let m : ℂ := (((analyticOrderAt XiC x).toNat : ℕ) : ℂ)
  have hmC : m ≠ 0 := by
    dsimp only [m]
    exact_mod_cast (Nat.ne_of_gt hm)
  have hdiv := (tendsto_meromorphicCauchyDiagonalKernel_of_ne hxy).div
    (tendsto_centeredPrimeArchRealShiftDiagonalExtractor him) hmC
  have hfun :
      (fun n : ℕ => meromorphicCauchyDiagonalKernel
          (1 / ((n : ℝ) + 1)) x y /
        centeredPrimeArchRealShiftDiagonalExtractor x n) =
      (fun n : ℕ => meromorphicCauchyDiagonalKernel
          (1 / ((n : ℝ) + 1)) x y) /
        centeredPrimeArchRealShiftDiagonalExtractor x := by
    funext n
    rfl
  rw [← hfun] at hdiv
  change Tendsto
      (fun n : ℕ => meromorphicCauchyDiagonalKernel
          (1 / ((n : ℝ) + 1)) x y /
        centeredPrimeArchRealShiftDiagonalExtractor x n)
      atTop (nhds 0)
  simpa only [zero_div] using hdiv

/-- Finite same-copy contraction of two source factors.  The fixed-pole projector forces equal
support locations and the Euler--Gamma extractor removes the extra residue multiplicity. -/
def finitePrimeArchNormalizedDiagonalContraction {ι : Type*}
    (s : Finset ι) (z : ι → ℂ) (A B : ι → ℂ) (n : ℕ) : ℂ :=
  ∑ p ∈ s.product s,
    ((((analyticOrderAt XiC (z p.1)).toNat : ℕ) : ℂ) *
      (((analyticOrderAt XiC (z p.2)).toNat : ℕ) : ℂ)) *
      primeArchMultiplicityNormalizedCauchyDiagonalKernel (z p.1) (z p.2) n *
        A p.1 * B p.2

/-- **Finite coefficient-faithful contraction law.**  For any finite distinct support packet
inside the critical band, multiplicity-normalized fixed-pole contraction converges to the desired
same-copy product with weight `m_i`, not the scalarized weight `m_i²`.  This finite landing does
not itself define a clean source contour: the inverse extractor may have additional zeros, hence
additional contour poles.  `XiCriticalLineThinStripSourceProjector` supplies the denominator-free
source replacement for the critical-line channel. -/
theorem tendsto_finitePrimeArchNormalizedDiagonalContraction
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (z : ι → ℂ) (A B : ι → ℂ)
    (hz : Set.InjOn z s)
    (him : ∀ i ∈ s, |(z i).im| < 1 / 2)
    (hm : ∀ i ∈ s, 0 < (analyticOrderAt XiC (z i)).toNat) :
    Tendsto (finitePrimeArchNormalizedDiagonalContraction s z A B) atTop
      (nhds (∑ i ∈ s,
        (((analyticOrderAt XiC (z i)).toNat : ℕ) : ℂ) * A i * B i)) := by
  let mass : ι → ℂ := fun i =>
    (((analyticOrderAt XiC (z i)).toNat : ℕ) : ℂ)
  have hpair : Tendsto
      (fun n : ℕ => ∑ p ∈ s.product s,
        (mass p.1 * mass p.2) *
          primeArchMultiplicityNormalizedCauchyDiagonalKernel
            (z p.1) (z p.2) n * A p.1 * B p.2)
      atTop (nhds (∑ p ∈ s.product s,
        if p.1 = p.2 then mass p.1 * A p.1 * B p.1 else 0)) := by
    apply tendsto_finsetSum (s.product s)
    intro p hp
    rcases p with ⟨i, j⟩
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hp
    by_cases hij : i = j
    · subst j
      have hkernel :=
        tendsto_primeArchMultiplicityNormalizedCauchyDiagonalKernel_self
          (him i hi) (hm i hi)
      change Tendsto
        (primeArchMultiplicityNormalizedCauchyDiagonalKernel (z i) (z i))
        atTop (nhds (mass i)⁻¹) at hkernel
      have hscaled := hkernel.const_mul
        (mass i * mass i * A i * B i)
      convert hscaled using 1
      · funext n
        ring
      · simp
        have hmass : mass i ≠ 0 := by
          dsimp only [mass]
          exact_mod_cast Nat.ne_of_gt (hm i hi)
        field_simp [hmass]
    · have hzij : z i ≠ z j := fun h => hij (hz hi hj h)
      have hkernel :=
        tendsto_primeArchMultiplicityNormalizedCauchyDiagonalKernel_of_ne
          hzij (him i hi) (hm i hi)
      have hscaled := hkernel.const_mul
        (mass i * mass j * A i * B j)
      convert hscaled using 1
      · funext n
        ring
      · simp [hij]
  change Tendsto
    (fun n : ℕ => ∑ p ∈ s.product s,
      (mass p.1 * mass p.2) *
        primeArchMultiplicityNormalizedCauchyDiagonalKernel
          (z p.1) (z p.2) n * A p.1 * B p.2)
    atTop (nhds (∑ i ∈ s, mass i * A i * B i))
  have hsum :
      (∑ p ∈ s.product s,
        if p.1 = p.2 then mass p.1 * A p.1 * B p.1 else 0) =
      ∑ i ∈ s, mass i * A i * B i := by
    calc
      (∑ p ∈ s.product s,
          if p.1 = p.2 then mass p.1 * A p.1 * B p.1 else 0) =
          ∑ i ∈ s, ∑ j ∈ s,
            if i = j then mass i * A i * B i else 0 :=
        Finset.sum_product s s _
      _ = ∑ i ∈ s, mass i * A i * B i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_ite_eq, if_pos hi]
  rw [hsum] at hpair
  exact hpair

end

end RHTower
