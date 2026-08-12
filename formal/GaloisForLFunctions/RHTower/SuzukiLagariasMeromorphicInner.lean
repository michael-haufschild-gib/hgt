import GaloisForLFunctions.RHTower.SuzukiCanonicalShiftRatio
import GaloisForLFunctions.RHTower.XiHadamardGrowth
import GaloisForLFunctions.RHTower.XiWeilPolarization
import GaloisForLFunctions.RHTower.XiHeatShellMinimum
import GaloisForLFunctions.RHTower.XiWeilCauchyCoreMultiplicity

/-!
# Lagarias--Suzuki modulus theorem and Suzuki's meromorphic-inner equivalence

This module formalizes the hard dependency behind Suzuki (2012), Proposition `intro_2`.
Lagarias--Suzuki (2006), Theorem 4 compares opposite shifts of a genus-zero/one entire function
whose zeros lie in a symmetric strip.  For Xi, the proof is carried out from the
multiplicity-exact Hadamard product: functional-equation reflection removes the genus-one
exponentials, critical-line reflection pairs the denominator factors, and a positive-real
infinite-product argument preserves strictness.

The final theorem is the exact closed source statement.  `SuzukiZetaZeroFreeRightOf` excludes
`s = 1` because mathlib totalizes the meromorphic pole of `riemannZeta`; this expresses
meromorphic nonvanishing rather than falsely classifying the pole as a zero.
-/

open Complex Set Filter Topology

noncomputable section

namespace RHTower

private instance : IsTopologicalGroup {x : ℝ // 0 < x} :=
  { continuous_mul := by
      rw [Topology.IsEmbedding.subtypeVal.continuous_iff]
      fun_prop
    continuous_inv := by
      rw [Topology.IsEmbedding.subtypeVal.continuous_iff]
      rw [continuous_iff_continuousAt]
      exact fun x => ContinuousAt.inv₀ (by fun_prop) x.2.ne' }

private lemma coe_positiveReal_finsetProd {ι : Type*}
    (s : Finset ι) (f : ι → {x : ℝ // 0 < x}) :
    ((↑(∏ i ∈ s, f i) : {x : ℝ // 0 < x}) : ℝ) =
      ∏ i ∈ s, (f i : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      change (f a : ℝ) * (↑(∏ i ∈ s, f i) : ℝ) =
        (f a : ℝ) * ∏ i ∈ s, (f i : ℝ)
      rw [ih]

def xiCanonicalReflectionPairFactor (z : ℂ) (q : XiZeroCopy) : ℂ :=
  weierstrassE1 (z / xiSpectralPoint q) *
    weierstrassE1 (z / xiSpectralPoint (xiZeroCopyReflectEquiv q))

lemma xiCanonicalReflectionPairFactor_eq (z : ℂ) (q : XiZeroCopy) :
    xiCanonicalReflectionPairFactor z q =
      (1 - (z / xiSpectralPoint q) ^ 2) := by
  rw [xiCanonicalReflectionPairFactor, xiSpectralPoint_reflect]
  simp only [weierstrassE1]
  have hneg : z / -xiSpectralPoint q = -(z / xiSpectralPoint q) := by ring
  rw [hneg, Complex.exp_neg]
  field_simp [Complex.exp_ne_zero]
  ring

lemma multipliable_xiCanonicalReflectionPairFactor (z : ℂ) :
    Multipliable (xiCanonicalReflectionPairFactor z) := by
  have h := xiCanonicalProduct_multipliable z
  have hreflect : Multipliable (fun q : XiZeroCopy =>
      weierstrassE1 (z / xiSpectralPoint (xiZeroCopyReflectEquiv q))) :=
    (xiZeroCopyReflectEquiv.multipliable_iff).mpr h
  exact h.mul hreflect

lemma tprod_xiCanonicalReflectionPairFactor (z : ℂ) :
    (∏' q : XiZeroCopy, xiCanonicalReflectionPairFactor z q) =
      xiCanonicalProduct z ^ 2 := by
  have h := xiCanonicalProduct_multipliable z
  have hreflectMultipliable : Multipliable (fun q : XiZeroCopy =>
      weierstrassE1 (z / xiSpectralPoint (xiZeroCopyReflectEquiv q))) :=
    (xiZeroCopyReflectEquiv.multipliable_iff).mpr h
  change (∏' q : XiZeroCopy,
      weierstrassE1 (z / xiSpectralPoint q) *
        weierstrassE1 (z / xiSpectralPoint (xiZeroCopyReflectEquiv q))) = _
  rw [h.tprod_mul hreflectMultipliable]
  change xiCanonicalProduct z *
      (∏' q : XiZeroCopy,
        weierstrassE1 (z / xiSpectralPoint (xiZeroCopyReflectEquiv q))) = _
  have hreflect :
      (∏' q : XiZeroCopy,
        weierstrassE1 (z / xiSpectralPoint (xiZeroCopyReflectEquiv q))) =
          xiCanonicalProduct z := by
    simpa only [xiCanonicalProduct, canonicalProductE1Indexed, Function.comp_apply] using
      (xiZeroCopyReflectEquiv.tprod_eq
        (fun q : XiZeroCopy => weierstrassE1 (z / xiSpectralPoint q)))
  rw [hreflect]
  ring

lemma norm_sub_lt_norm_sub_vertical_shift
    (w lambda : ℂ) (c : ℝ)
    (hw : w.im < 0) (hlower : -c < lambda.im) :
    ‖(w + (c : ℂ) * I) - (starRingEnd ℂ) lambda‖ <
      ‖(w - (c : ℂ) * I) - lambda‖ := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq]
  norm_num [Complex.normSq_apply, sub_re, sub_im, add_re, add_im, mul_re, mul_im]
  nlinarith [sq_nonneg (w.re - lambda.re)]

lemma norm_add_lt_norm_add_vertical_shift
    (w lambda : ℂ) (c : ℝ)
    (hw : w.im < 0) (hupper : lambda.im < c) :
    ‖(w + (c : ℂ) * I) + (starRingEnd ℂ) lambda‖ <
      ‖(w - (c : ℂ) * I) + lambda‖ := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq]
  norm_num [Complex.normSq_apply, add_re, add_im, sub_re, sub_im, mul_re, mul_im]
  nlinarith [sq_nonneg (w.re + lambda.re)]

lemma norm_xiCanonicalReflectionPairFactor_lineConj_lt
    {alpha c : ℝ} (hc : alpha < c)
    (hzeros : XiZeroHalfPlaneBound alpha)
    (w : ℂ) (hw : w.im < 0) (q : XiZeroCopy) :
    ‖xiCanonicalReflectionPairFactor (w + (c : ℂ) * I)
        (xiZeroCopyLineConjEquiv q)‖ <
      ‖xiCanonicalReflectionPairFactor (w - (c : ℂ) * I) q‖ := by
  let lambda := xiSpectralPoint q
  have habs : |lambda.im| ≤ alpha := by
    dsimp only [lambda]
    rw [xiSpectralPoint_im_eq]
    simpa [abs_sub_comm] using
      abs_xiZero_re_sub_half_le_of_halfPlaneBound hzeros q
  have hlower : -c < lambda.im := by
    have := (abs_le.mp habs).1
    linarith
  have hupper : lambda.im < c := by
    have := (abs_le.mp habs).2
    linarith
  have hminus := norm_sub_lt_norm_sub_vertical_shift w lambda c hw hlower
  have hplus := norm_add_lt_norm_add_vertical_shift w lambda c hw hupper
  rw [xiCanonicalReflectionPairFactor_eq, xiCanonicalReflectionPairFactor_eq,
    xiSpectralPoint_lineConj]
  change ‖1 - ((w + (c : ℂ) * I) / (starRingEnd ℂ) lambda) ^ 2‖ <
    ‖1 - ((w - (c : ℂ) * I) / lambda) ^ 2‖
  have hlambda : lambda ≠ 0 := xiSpectralPoint_ne_zero q
  have hconj : (starRingEnd ℂ) lambda ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).mpr hlambda
  have hleft :
      ‖1 - ((w + (c : ℂ) * I) / (starRingEnd ℂ) lambda) ^ 2‖ =
        (‖(w + (c : ℂ) * I) - (starRingEnd ℂ) lambda‖ *
          ‖(w + (c : ℂ) * I) + (starRingEnd ℂ) lambda‖) /
            ‖lambda‖ ^ 2 := by
    rw [show 1 - ((w + (c : ℂ) * I) / (starRingEnd ℂ) lambda) ^ 2 =
        (((starRingEnd ℂ) lambda - (w + (c : ℂ) * I)) *
          ((starRingEnd ℂ) lambda + (w + (c : ℂ) * I))) /
            ((starRingEnd ℂ) lambda) ^ 2 by field_simp; ring]
    rw [norm_div, norm_mul, norm_pow, norm_conj]
    congr 2
    · rw [norm_sub_rev]
    · congr 1
      ring_nf
  have hright :
      ‖1 - ((w - (c : ℂ) * I) / lambda) ^ 2‖ =
        (‖(w - (c : ℂ) * I) - lambda‖ *
          ‖(w - (c : ℂ) * I) + lambda‖) / ‖lambda‖ ^ 2 := by
    rw [show 1 - ((w - (c : ℂ) * I) / lambda) ^ 2 =
        ((lambda - (w - (c : ℂ) * I)) *
          (lambda + (w - (c : ℂ) * I))) / lambda ^ 2 by field_simp; ring]
    rw [norm_div, norm_mul, norm_pow]
    congr 2
    · rw [norm_sub_rev]
    · congr 1
      ring_nf
  rw [hleft, hright]
  apply div_lt_div_of_pos_right _ (sq_pos_of_pos (norm_pos_iff.mpr hlambda))
  have hrightSub : (w - (c : ℂ) * I) - lambda ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num [sub_im, mul_im] at him
    linarith
  have hrightAdd : (w - (c : ℂ) * I) + lambda ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num [sub_im, add_im, mul_im] at him
    linarith
  by_cases hleftAdd : (w + (c : ℂ) * I) + (starRingEnd ℂ) lambda = 0
  · rw [hleftAdd, norm_zero, mul_zero]
    exact mul_pos (norm_pos_iff.mpr hrightSub) (norm_pos_iff.mpr hrightAdd)
  · exact mul_lt_mul hminus hplus.le (norm_pos_iff.mpr hleftAdd) (norm_nonneg _)

lemma xiCanonicalProduct_ne_zero_of_im_lt_neg_halfPlaneBound
    {alpha : ℝ} (hzeros : XiZeroHalfPlaneBound alpha)
    {z : ℂ} (hz : z.im < -alpha) :
    xiCanonicalProduct z ≠ 0 := by
  intro hzero
  have hXi : XiC z = 0 := by
    rw [XiC_eq_constant_mul_canonicalProduct]
    simp only [Pi.mul_apply, hzero, mul_zero]
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy z).mp hXi
  have habs : |(xiSpectralPoint q).im| ≤ alpha := by
    rw [xiSpectralPoint_im_eq]
    simpa [abs_sub_comm] using
      abs_xiZero_re_sub_half_le_of_halfPlaneBound hzeros q
  have him := congrArg Complex.im hq
  linarith [(abs_le.mp habs).1]

lemma xiCanonicalReflectionPairFactor_ne_zero_of_canonicalProduct_ne_zero
    {z : ℂ} (hz : xiCanonicalProduct z ≠ 0) (q : XiZeroCopy) :
    xiCanonicalReflectionPairFactor z q ≠ 0 := by
  intro hzero
  have htprod : (∏' q : XiZeroCopy, xiCanonicalReflectionPairFactor z q) = 0 :=
    tprod_of_exists_eq_zero ⟨q, hzero⟩
  rw [tprod_xiCanonicalReflectionPairFactor] at htprod
  exact hz (mul_self_eq_zero.mp (by simpa only [pow_two] using htprod))

theorem norm_xiCanonicalProduct_vertical_shift_lt_of_halfPlaneBound
    {alpha c : ℝ} (hc : alpha < c)
    (hzeros : XiZeroHalfPlaneBound alpha)
    (w : ℂ) (hw : w.im < 0) :
    ‖xiCanonicalProduct (w + (c : ℂ) * I)‖ <
      ‖xiCanonicalProduct (w - (c : ℂ) * I)‖ := by
  let zplus : ℂ := w + (c : ℂ) * I
  let zminus : ℂ := w - (c : ℂ) * I
  have hzminusIm : zminus.im < -alpha := by
    dsimp only [zminus]
    norm_num [sub_im, mul_im]
    linarith
  have hPminus : xiCanonicalProduct zminus ≠ 0 :=
    xiCanonicalProduct_ne_zero_of_im_lt_neg_halfPlaneBound hzeros hzminusIm
  by_cases hPplus : xiCanonicalProduct zplus = 0
  · rw [hPplus, norm_zero]
    exact norm_pos_iff.mpr hPminus
  have hPplusNe : xiCanonicalProduct zplus ≠ 0 := hPplus
  let plusFactor : XiZeroCopy → {x : ℝ // 0 < x} := fun q =>
    ⟨‖xiCanonicalReflectionPairFactor zplus (xiZeroCopyLineConjEquiv q)‖,
      norm_pos_iff.mpr
        (xiCanonicalReflectionPairFactor_ne_zero_of_canonicalProduct_ne_zero
          hPplusNe (xiZeroCopyLineConjEquiv q))⟩
  let minusFactor : XiZeroCopy → {x : ℝ // 0 < x} := fun q =>
    ⟨‖xiCanonicalReflectionPairFactor zminus q‖,
      norm_pos_iff.mpr
        (xiCanonicalReflectionPairFactor_ne_zero_of_canonicalProduct_ne_zero hPminus q)⟩
  let plusLimit : {x : ℝ // 0 < x} :=
    ⟨‖xiCanonicalProduct zplus ^ 2‖, norm_pos_iff.mpr (pow_ne_zero 2 hPplusNe)⟩
  let minusLimit : {x : ℝ // 0 < x} :=
    ⟨‖xiCanonicalProduct zminus ^ 2‖, norm_pos_iff.mpr (pow_ne_zero 2 hPminus)⟩
  have hplusComplex : HasProd
      (fun q : XiZeroCopy =>
        xiCanonicalReflectionPairFactor zplus (xiZeroCopyLineConjEquiv q))
      (xiCanonicalProduct zplus ^ 2) := by
    have hbase : HasProd (xiCanonicalReflectionPairFactor zplus)
        (xiCanonicalProduct zplus ^ 2) := by
      rw [← tprod_xiCanonicalReflectionPairFactor zplus]
      exact (multipliable_xiCanonicalReflectionPairFactor zplus).hasProd
    convert (xiZeroCopyLineConjEquiv.hasProd_iff).mpr hbase using 1
    rfl
  have hminusComplex : HasProd
      (xiCanonicalReflectionPairFactor zminus)
      (xiCanonicalProduct zminus ^ 2) := by
    rw [← tprod_xiCanonicalReflectionPairFactor zminus]
    exact (multipliable_xiCanonicalReflectionPairFactor zminus).hasProd
  have hplusPos : HasProd plusFactor plusLimit := by
    change Tendsto (fun s : Finset XiZeroCopy => ∏ q ∈ s, plusFactor q) _ (𝓝 plusLimit)
    apply Topology.IsInducing.subtypeVal.tendsto_nhds_iff.mpr
    have hr := hplusComplex.norm
    change Tendsto (fun s : Finset XiZeroCopy =>
      ∏ q ∈ s, ‖xiCanonicalReflectionPairFactor zplus (xiZeroCopyLineConjEquiv q)‖)
      _ (𝓝 ‖xiCanonicalProduct zplus ^ 2‖) at hr
    convert hr using 1
    funext s
    exact coe_positiveReal_finsetProd s plusFactor
  have hminusPos : HasProd minusFactor minusLimit := by
    change Tendsto (fun s : Finset XiZeroCopy => ∏ q ∈ s, minusFactor q) _ (𝓝 minusLimit)
    apply Topology.IsInducing.subtypeVal.tendsto_nhds_iff.mpr
    have hr := hminusComplex.norm
    change Tendsto (fun s : Finset XiZeroCopy =>
      ∏ q ∈ s, ‖xiCanonicalReflectionPairFactor zminus q‖)
      _ (𝓝 ‖xiCanonicalProduct zminus ^ 2‖) at hr
    convert hr using 1
    funext s
    exact coe_positiveReal_finsetProd s minusFactor
  let q0 : XiZeroCopy := Classical.choice nonempty_xiZeroCopy
  have hfactor : ∀ q : XiZeroCopy, plusFactor q < minusFactor q := by
    intro q
    apply Subtype.coe_lt_coe.mp
    simpa only [plusFactor, minusFactor, zplus, zminus] using
      norm_xiCanonicalReflectionPairFactor_lineConj_lt
        hc hzeros w hw q
  have hprod : (∏' q, plusFactor q) < ∏' q, minusFactor q :=
    hplusPos.multipliable.tprod_lt_tprod
      (fun q => (hfactor q).le) (hfactor q0) hminusPos.multipliable
  rw [hplusPos.tprod_eq, hminusPos.tprod_eq] at hprod
  have hsq : ‖xiCanonicalProduct zplus‖ ^ 2 <
      ‖xiCanonicalProduct zminus‖ ^ 2 := by
    have hprodReal : ‖xiCanonicalProduct zplus ^ 2‖ <
        ‖xiCanonicalProduct zminus ^ 2‖ := by
      change (plusLimit : ℝ) < (minusLimit : ℝ)
      exact hprod
    simpa only [norm_pow] using hprodReal
  dsimp only [zplus, zminus] at hsq ⊢
  nlinarith [norm_nonneg (xiCanonicalProduct (w + (c : ℂ) * I)),
    norm_nonneg (xiCanonicalProduct (w - (c : ℂ) * I))]

theorem norm_XiC_vertical_shift_lt_of_halfPlaneBound
    {alpha c : ℝ} (hc : alpha < c)
    (hzeros : XiZeroHalfPlaneBound alpha)
    (w : ℂ) (hw : w.im < 0) :
    ‖XiC (w + (c : ℂ) * I)‖ < ‖XiC (w - (c : ℂ) * I)‖ := by
  have hP := norm_xiCanonicalProduct_vertical_shift_lt_of_halfPlaneBound
    hc hzeros w hw
  have hXi0 : 0 < ‖XiC 0‖ := norm_pos_iff.mpr XiC_zero_ne
  rw [congrFun XiC_eq_constant_mul_canonicalProduct
      (w + (c : ℂ) * I),
    congrFun XiC_eq_constant_mul_canonicalProduct
      (w - (c : ℂ) * I)]
  simp only [Pi.mul_apply, norm_mul]
  exact mul_lt_mul_of_pos_left hP hXi0

/-- Meromorphic nonvanishing of zeta strictly right of Suzuki's shifted critical line.
The exception at `s = 1` records the pole, which is not a meromorphic zero. -/
def SuzukiZetaZeroFreeRightOf (alpha : ℝ) : Prop :=
  ∀ s : ℂ, 1 / 2 + alpha < s.re → s ≠ 1 → riemannZeta s ≠ 0

theorem suzukiZetaZeroFreeRightOf_iff_xiZeroHalfPlaneBound
    {alpha : ℝ} (halpha : 0 ≤ alpha) :
    SuzukiZetaZeroFreeRightOf alpha ↔ XiZeroHalfPlaneBound alpha := by
  constructor
  · intro hzeta rho hxi
    by_contra hnot
    have hright : 1 / 2 + alpha < rho.re := lt_of_not_ge hnot
    have hrhoPos : 0 < rho.re := by linarith
    have hrhoOne : rho ≠ 1 := by
      intro hrho
      rw [hrho, xi_one] at hxi
      norm_num at hxi
    exact hzeta rho hright hrhoOne ((xi_eq_zero_iff hrhoPos hrhoOne).mp hxi)
  · intro hzeros s hs hsOne hzeta
    have hsPos : 0 < s.re := by linarith
    have hxi : xi s = 0 := (xi_eq_zero_iff hsPos hsOne).mpr hzeta
    linarith [hzeros s hxi]

/-- Source-faithful upper-half-plane definition used for Suzuki's meromorphic inner functions:
global meromorphic continuation, holomorphy and strict disk image in the open upper half-plane,
and unimodular values on the real boundary. -/
def MeromorphicInnerUpperHalfPlane (theta : ℂ → ℂ) : Prop :=
  MeromorphicOn theta Set.univ ∧
    AnalyticOnNhd ℂ theta xiCenteredUpperHalfPlane ∧
    (∀ z : ℂ, 0 < z.im → ‖theta z‖ < 1) ∧
    ∀ u : ℝ, ‖theta (u : ℂ)‖ = 1

/-- Suzuki's literal shifted-Xi quotient is meromorphic inner. -/
def SuzukiCanonicalThetaMeromorphicInner (omega : ℝ) : Prop :=
  MeromorphicInnerUpperHalfPlane (suzukiCanonicalTheta omega)

theorem XiC_ne_zero_of_im_lt_neg_halfPlaneBound
    {alpha : ℝ} (hzeros : XiZeroHalfPlaneBound alpha)
    {z : ℂ} (hz : z.im < -alpha) : XiC z ≠ 0 := by
  rw [congrFun XiC_eq_constant_mul_canonicalProduct z]
  simp only [Pi.mul_apply]
  exact mul_ne_zero XiC_zero_ne
    (xiCanonicalProduct_ne_zero_of_im_lt_neg_halfPlaneBound hzeros hz)

/-- Lagarias--Suzuki (2006), Theorem 4, specialized to the completed Riemann Xi function and
translated into Suzuki's 2012 `E^omega` coordinates. -/
theorem suzukiCanonicalHermiteBiehler_of_halfPlaneBound
    {alpha omega : ℝ} (hzeros : XiZeroHalfPlaneBound alpha)
    (homega : alpha < omega) : SuzukiCanonicalHermiteBiehler omega := by
  intro z hz
  have hshift := norm_XiC_vertical_shift_lt_of_halfPlaneBound
    homega hzeros (-z) (by simp; linarith)
  rw [suzukiCanonicalESharp_eq_E_neg,
    suzukiCanonicalE_eq_XiC_shift, suzukiCanonicalE_eq_XiC_shift]
  simp only [neg_neg]
  have heven := XiC_even (z - (omega : ℂ) * I)
  have hleft : ‖XiC (z - (omega : ℂ) * I)‖ =
      ‖XiC (-z + (omega : ℂ) * I)‖ := by
    rw [show -z + (omega : ℂ) * I = -(z - (omega : ℂ) * I) by ring,
      heven]
  rw [hleft]
  simpa only [neg_sub, neg_add_rev] using hshift

theorem suzukiCanonicalTheta_meromorphicInner_of_halfPlaneBound
    {alpha omega : ℝ} (hzeros : XiZeroHalfPlaneBound alpha)
    (homega : alpha < omega) : SuzukiCanonicalThetaMeromorphicInner omega := by
  have hHB := suzukiCanonicalHermiteBiehler_of_halfPlaneBound hzeros homega
  have hdisk := (suzukiCanonicalHermiteBiehler_iff_theta_disk omega).mp hHB
  refine ⟨meromorphicOn_suzukiCanonicalTheta omega, ?_, (fun z hz => (hdisk z hz).2), ?_⟩
  · intro z hz
    rw [xiCenteredUpperHalfPlane, Set.mem_setOf_eq] at hz
    rw [show suzukiCanonicalTheta omega = fun w =>
        suzukiCanonicalESharp omega w / suzukiCanonicalE omega w by
      funext w
      exact suzukiCanonicalTheta_eq_ESharp_div_E omega w]
    exact (differentiable_suzukiCanonicalESharp omega).analyticAt z |>.div
      ((differentiable_suzukiCanonicalE omega).analyticAt z) (hdisk z hz).1
  · intro u
    apply norm_suzukiCanonicalTheta_ofReal_eq_one
    rw [suzukiCanonicalE_eq_XiC_shift]
    apply XiC_ne_zero_of_im_lt_neg_halfPlaneBound hzeros
    norm_num [sub_im, mul_im]
    linarith

theorem suzukiZetaZeroFreeRightOf_implies_theta_meromorphicInner
    {alpha : ℝ} (halpha : 0 ≤ alpha) (hzeta : SuzukiZetaZeroFreeRightOf alpha) :
    ∀ omega : ℝ, alpha < omega → SuzukiCanonicalThetaMeromorphicInner omega := by
  have hzeros := (suzukiZetaZeroFreeRightOf_iff_xiZeroHalfPlaneBound halpha).mp hzeta
  exact fun omega homega =>
    suzukiCanonicalTheta_meromorphicInner_of_halfPlaneBound hzeros homega

lemma meromorphicOrderAt_div_neg_of_analyticAt_num_ne_den_zero
    {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (hf0 : f z ≠ 0) (hg0 : g z = 0)
    (hgTop : analyticOrderAt g z ≠ ⊤) :
    meromorphicOrderAt (f / g) z < 0 := by
  have hfOrder : analyticOrderAt f z = 0 := hf.analyticOrderAt_eq_zero.mpr hf0
  have hgOrder0 : analyticOrderAt g z ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨hg, hg0⟩
  let m : ℕ := (analyticOrderAt g z).toNat
  have hm : (m : ℕ∞) = analyticOrderAt g z := ENat.coe_toNat hgTop
  have hm0 : m ≠ 0 := by
    intro hmzero
    apply hgOrder0
    rw [← hm, hmzero]
    rfl
  rw [meromorphicOrderAt_div hf.meromorphicAt hg.meromorphicAt,
    hf.meromorphicOrderAt_eq, hg.meromorphicOrderAt_eq, hfOrder, ← hm]
  simp only [ENat.map_zero, ENat.map_coe]
  have hmposZ : (0 : ℤ) < (m : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hm0
  change (((0 : ℤ) : WithTop ℤ) - ((m : ℤ) : WithTop ℤ)) <
    ((0 : ℤ) : WithTop ℤ)
  rw [← WithTop.LinearOrderedAddCommGroup.coe_sub]
  exact WithTop.coe_lt_coe.mpr (sub_neg.mpr hmposZ)

lemma exists_suzuki_shift_avoiding_xi_zero
    {alpha delta : ℝ} (hgap : alpha < delta) (rho : ℂ) :
    ∃ omega : ℝ, alpha < omega ∧ omega < delta ∧
      xi (rho - 2 * (omega : ℂ)) ≠ 0 := by
  let a : ℂ := (rho - 2 * (delta : ℂ) - 1 / 2) * (-I)
  have hev := eventually_XiC_ne_zero_punctured a
  change {w : ℂ | XiC w ≠ 0} ∈ 𝓝[{a}ᶜ] a at hev
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.mp hev
  let epsilon : ℝ := min ((delta - alpha) / 4) (r / 4)
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    exact lt_min (by linarith) (by positivity)
  have hepsilonGap : epsilon < delta - alpha := by
    calc
      epsilon ≤ (delta - alpha) / 4 := min_le_left _ _
      _ < delta - alpha := by linarith
  have hepsilonR : 2 * epsilon < r := by
    have hle : epsilon ≤ r / 4 := min_le_right _ _
    linarith
  let omega : ℝ := delta - epsilon
  let p : ℂ := (rho - 2 * (omega : ℂ) - 1 / 2) * (-I)
  have homegaLeft : alpha < omega := by
    dsimp only [omega]
    linarith
  have homegaRight : omega < delta := by
    dsimp only [omega]
    linarith
  have hpDist : dist p a = 2 * epsilon := by
    rw [dist_eq_norm]
    have hdiff : p - a = (2 * epsilon : ℝ) * (-I) := by
      dsimp only [p, a, omega]
      push_cast
      ring
    rw [hdiff, norm_mul, norm_real, norm_neg, norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * epsilon)]
  have hpBall : p ∈ Metric.ball a r := by
    rw [Metric.mem_ball, hpDist]
    exact hepsilonR
  have hpNe : p ≠ a := by
    intro hpa
    have : dist p a = 0 := by rw [hpa, dist_self]
    rw [hpDist] at this
    linarith
  have hpXi : XiC p ≠ 0 := hball ⟨hpBall, hpNe⟩
  refine ⟨omega, homegaLeft, homegaRight, ?_⟩
  intro hxi
  apply hpXi
  rw [XiC]
  convert hxi using 1
  dsimp only [p]
  have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
  rw [mul_assoc, hI, mul_one]
  ring

theorem xiZeroHalfPlaneBound_of_forall_suzukiCanonicalTheta_meromorphicInner
    {alpha : ℝ}
    (hinner : ∀ omega : ℝ, alpha < omega →
      SuzukiCanonicalThetaMeromorphicInner omega) :
    XiZeroHalfPlaneBound alpha := by
  intro rho hxi
  by_contra hnot
  have hrho : 1 / 2 + alpha < rho.re := lt_of_not_ge hnot
  let delta : ℝ := rho.re - 1 / 2
  have hgap : alpha < delta := by dsimp only [delta]; linarith
  obtain ⟨omega, homegaLeft, homegaRight, hnumXi⟩ :=
    exists_suzuki_shift_avoiding_xi_zero hgap rho
  let zroot : ℂ := (1 / 2 + (omega : ℂ) - rho) * (-I)
  have hzrootIm : 0 < zroot.im := by
    dsimp only [zroot]
    norm_num [mul_im, sub_im, add_im]
    dsimp only [delta] at homegaRight
    linarith
  have hdenZero : suzukiCanonicalE omega zroot = 0 := by
    rw [suzukiCanonicalE]
    convert hxi using 1
    dsimp only [zroot]
    have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
    rw [mul_assoc, hI, mul_one]
    ring
  have hnumNe : suzukiCanonicalESharp omega zroot ≠ 0 := by
    rw [suzukiCanonicalESharp_eq_E_neg,
      suzukiCanonicalE_neg_eq_thetaNumerator]
    convert hnumXi using 1
    dsimp only [zroot]
    have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
    rw [mul_assoc, hI, mul_one]
    ring
  have hthetaAt : AnalyticAt ℂ (suzukiCanonicalTheta omega) zroot := by
    have h := (hinner omega homegaLeft).2.1
    exact h zroot (by
      rw [xiCenteredUpperHalfPlane, Set.mem_setOf_eq]
      exact hzrootIm)
  have hnumAt : AnalyticAt ℂ (suzukiCanonicalESharp omega) zroot :=
    (differentiable_suzukiCanonicalESharp omega).analyticAt zroot
  have hdenAt : AnalyticAt ℂ (suzukiCanonicalE omega) zroot :=
    (differentiable_suzukiCanonicalE omega).analyticAt zroot
  have hdenTop : analyticOrderAt (suzukiCanonicalE omega) zroot ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have hEall : AnalyticOnNhd ℂ (suzukiCanonicalE omega) Set.univ :=
      fun z _ => (differentiable_suzukiCanonicalE omega).analyticAt z
    have hall := hEall.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ zroot) htop (Set.mem_univ 0)
    exact suzukiCanonicalE_zero_ne_zero omega hall
  have hpole : meromorphicOrderAt
      (suzukiCanonicalESharp omega / suzukiCanonicalE omega) zroot < 0 :=
    meromorphicOrderAt_div_neg_of_analyticAt_num_ne_den_zero
      hnumAt hdenAt hnumNe hdenZero hdenTop
  have hnonneg := hthetaAt.meromorphicOrderAt_nonneg
  rw [show suzukiCanonicalTheta omega =
      suzukiCanonicalESharp omega / suzukiCanonicalE omega by
    funext z
    exact suzukiCanonicalTheta_eq_ESharp_div_E omega z] at hnonneg
  exact (not_lt_of_ge hnonneg) hpole

theorem forall_suzukiCanonicalTheta_meromorphicInner_implies_zetaZeroFreeRightOf
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hinner : ∀ omega : ℝ, alpha < omega →
      SuzukiCanonicalThetaMeromorphicInner omega) :
    SuzukiZetaZeroFreeRightOf alpha := by
  apply (suzukiZetaZeroFreeRightOf_iff_xiZeroHalfPlaneBound halpha).mpr
  exact xiZeroHalfPlaneBound_of_forall_suzukiCanonicalTheta_meromorphicInner hinner

/-- **Suzuki (2012), Proposition `intro_2`, exact closed form.** For every nonnegative
`omega_0`, zeta has no meromorphic zeros in `Re(s) > 1/2 + omega_0` iff every literal shifted-Xi
quotient `Theta_omega` with `omega > omega_0` is meromorphic inner in the upper half-plane. -/
theorem suzuki2012_zetaZeroFree_iff_forall_theta_meromorphicInner :
    ∀ omega0 : ℝ, 0 ≤ omega0 →
      (SuzukiZetaZeroFreeRightOf omega0 ↔
        ∀ omega : ℝ, omega0 < omega →
          SuzukiCanonicalThetaMeromorphicInner omega) := by
  intro omega0 homega0
  constructor
  · exact suzukiZetaZeroFreeRightOf_implies_theta_meromorphicInner homega0
  · exact forall_suzukiCanonicalTheta_meromorphicInner_implies_zetaZeroFreeRightOf homega0

end RHTower
