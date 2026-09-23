import GaloisForLFunctions.RHTower.SuzukiShiftedXiDivisorFactorization

open Complex Set Filter Topology

namespace RHTower

noncomputable section

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

/-- Multiplicity copies in the Xi core of transverse width `omega`. -/
abbrev XiShiftCoreZeroCopy (omega : ℝ) :=
  {q : XiZeroCopy // |(I * xiSpectralPoint q).re| ≤ omega}

/-- Canonical product over the symmetric Xi core. -/
def xiShiftCoreCanonicalProduct (omega : ℝ) : ℂ → ℂ :=
  canonicalProductE1IndexedSelected xiSpectralPoint
    (fun q => |(I * xiSpectralPoint q).re| ≤ omega)

theorem xiShiftCoreCanonicalProduct_analytic (omega : ℝ) :
    AnalyticOnNhd ℂ (xiShiftCoreCanonicalProduct omega) Set.univ :=
  canonicalProductE1IndexedSelected_analytic xiSpectralPoint
    (fun q => |(I * xiSpectralPoint q).re| ≤ omega)
    xiSpectralPoint_ne_zero xiSpectralPoint_inv_sq_summable

theorem xiShiftCoreCanonicalProduct_multipliable (omega : ℝ) (z : ℂ) :
    Multipliable (fun q : XiShiftCoreZeroCopy omega =>
      weierstrassE1 (z / xiSpectralPoint q.1)) :=
  canonicalProductE1IndexedSelected_multipliable xiSpectralPoint
    (fun q => |(I * xiSpectralPoint q).re| ≤ omega)
    xiSpectralPoint_ne_zero xiSpectralPoint_inv_sq_summable z

/-- Functional-equation reflection preserves every symmetric Xi core. -/
def xiShiftCoreReflectEquiv (omega : ℝ) :
    XiShiftCoreZeroCopy omega ≃ XiShiftCoreZeroCopy omega :=
  Equiv.subtypeEquiv xiZeroCopyReflectEquiv (fun q => by
    rw [xiSpectralPoint_reflect]
    have h : (I * -xiSpectralPoint q).re = -(I * xiSpectralPoint q).re := by
      norm_num [mul_re]
    rw [h, abs_neg])

/-- Critical-line reflection preserves every symmetric Xi core. -/
def xiShiftCoreLineConjEquiv (omega : ℝ) :
    XiShiftCoreZeroCopy omega ≃ XiShiftCoreZeroCopy omega :=
  Equiv.subtypeEquiv xiZeroCopyLineConjEquiv (fun q => by
    rw [xiSpectralPoint_lineConj]
    have h :
        (I * (starRingEnd ℂ) (xiSpectralPoint q)).re =
          -(I * xiSpectralPoint q).re := by
      norm_num [mul_re]
    rw [h, abs_neg])

theorem xiShiftCoreCanonicalProduct_even (omega : ℝ) (z : ℂ) :
    xiShiftCoreCanonicalProduct omega (-z) =
      xiShiftCoreCanonicalProduct omega z := by
  rw [xiShiftCoreCanonicalProduct, canonicalProductE1IndexedSelected,
    canonicalProductE1Indexed]
  let e := xiShiftCoreReflectEquiv omega
  calc
    (∏' q : XiShiftCoreZeroCopy omega,
        weierstrassE1 (-z / xiSpectralPoint q.1)) =
      ∏' q : XiShiftCoreZeroCopy omega,
        weierstrassE1 (-z / xiSpectralPoint (e q).1) := by
          exact (e.tprod_eq (fun q : XiShiftCoreZeroCopy omega =>
            weierstrassE1 (-z / xiSpectralPoint q.1))).symm
    _ = ∏' q : XiShiftCoreZeroCopy omega,
        weierstrassE1 (z / xiSpectralPoint q.1) := by
          apply tprod_congr
          intro q
          change weierstrassE1
              (-z / xiSpectralPoint (xiZeroCopyReflectEquiv q.1)) = _
          rw [xiSpectralPoint_reflect]
          congr 1
          field_simp

/-- Reflection-paired factor in the symmetric Xi core. -/
def xiShiftCoreReflectionPairFactor (omega : ℝ) (z : ℂ)
    (q : XiShiftCoreZeroCopy omega) : ℂ :=
  weierstrassE1 (z / xiSpectralPoint q.1) *
    weierstrassE1
      (z / xiSpectralPoint (xiZeroCopyReflectEquiv q.1))

theorem multipliable_xiShiftCoreReflectionPairFactor (omega : ℝ) (z : ℂ) :
    Multipliable (xiShiftCoreReflectionPairFactor omega z) := by
  have h := xiShiftCoreCanonicalProduct_multipliable omega z
  have hreflect : Multipliable (fun q : XiShiftCoreZeroCopy omega =>
      weierstrassE1
        (z / xiSpectralPoint (xiZeroCopyReflectEquiv q.1))) := by
    let e := xiShiftCoreReflectEquiv omega
    change Multipliable ((fun q : XiShiftCoreZeroCopy omega =>
      weierstrassE1 (z / xiSpectralPoint q.1)) ∘ e)
    exact e.multipliable_iff.mpr h
  exact h.mul hreflect

theorem tprod_xiShiftCoreReflectionPairFactor (omega : ℝ) (z : ℂ) :
    (∏' q : XiShiftCoreZeroCopy omega,
      xiShiftCoreReflectionPairFactor omega z q) =
        xiShiftCoreCanonicalProduct omega z ^ (2 : ℕ) := by
  have h := xiShiftCoreCanonicalProduct_multipliable omega z
  let e := xiShiftCoreReflectEquiv omega
  have hreflect : Multipliable (fun q : XiShiftCoreZeroCopy omega =>
      weierstrassE1
        (z / xiSpectralPoint (xiZeroCopyReflectEquiv q.1))) := by
    change Multipliable ((fun q : XiShiftCoreZeroCopy omega =>
      weierstrassE1 (z / xiSpectralPoint q.1)) ∘ e)
    exact e.multipliable_iff.mpr h
  change (∏' q : XiShiftCoreZeroCopy omega,
      weierstrassE1 (z / xiSpectralPoint q.1) *
        weierstrassE1
          (z / xiSpectralPoint (xiZeroCopyReflectEquiv q.1))) = _
  rw [h.tprod_mul hreflect]
  change xiShiftCoreCanonicalProduct omega z *
      (∏' q : XiShiftCoreZeroCopy omega,
        weierstrassE1
          (z / xiSpectralPoint (xiZeroCopyReflectEquiv q.1))) = _
  have hreflectEq :
      (∏' q : XiShiftCoreZeroCopy omega,
        weierstrassE1
          (z / xiSpectralPoint (xiZeroCopyReflectEquiv q.1))) =
        xiShiftCoreCanonicalProduct omega z := by
    rw [xiShiftCoreCanonicalProduct, canonicalProductE1IndexedSelected,
      canonicalProductE1Indexed]
    change (∏' q : XiShiftCoreZeroCopy omega,
        ((fun r : XiShiftCoreZeroCopy omega =>
          weierstrassE1 (z / xiSpectralPoint r.1)) ∘ e) q) =
      ∏' q : XiShiftCoreZeroCopy omega,
        weierstrassE1 (z / xiSpectralPoint q.1)
    exact e.tprod_eq (fun q : XiShiftCoreZeroCopy omega =>
      weierstrassE1 (z / xiSpectralPoint q.1))
  rw [hreflectEq]
  ring

lemma norm_sub_le_norm_sub_vertical_shift
    (w lambda : ℂ) (c : ℝ)
    (hw : w.im ≤ 0) (hlower : -c ≤ lambda.im) :
    ‖(w + (c : ℂ) * I) - (starRingEnd ℂ) lambda‖ ≤
      ‖(w - (c : ℂ) * I) - lambda‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  norm_num [Complex.normSq_apply, sub_re, sub_im, add_re, add_im,
    mul_re, mul_im]
  nlinarith [sq_nonneg (w.re - lambda.re)]

lemma norm_add_le_norm_add_vertical_shift
    (w lambda : ℂ) (c : ℝ)
    (hw : w.im ≤ 0) (hupper : lambda.im ≤ c) :
    ‖(w + (c : ℂ) * I) + (starRingEnd ℂ) lambda‖ ≤
      ‖(w - (c : ℂ) * I) + lambda‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  norm_num [Complex.normSq_apply, add_re, add_im, sub_re, sub_im,
    mul_re, mul_im]
  nlinarith [sq_nonneg (w.re + lambda.re)]

/-- The exponential contacts cancel exactly in a reflection-paired genus-one factor. -/
lemma norm_weierstrassE1_mul_div_neg (z lam : ℂ) :
    ‖weierstrassE1 (z / lam) * weierstrassE1 (z / -lam)‖ =
      ‖1 - z / lam‖ * ‖1 - z / -lam‖ := by
  rw [weierstrassE1, weierstrassE1, norm_mul, norm_mul, norm_mul]
  simp only [norm_exp, div_eq_mul_inv, inv_neg, mul_neg, neg_re,
    sub_neg_eq_add]
  have hexp : Real.exp (z * lam⁻¹).re *
      Real.exp (-(z * lam⁻¹).re) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    ‖1 - z * lam⁻¹‖ * Real.exp (z * lam⁻¹).re *
          (‖1 + z * lam⁻¹‖ * Real.exp (-(z * lam⁻¹).re)) =
        (‖1 - z * lam⁻¹‖ * ‖1 + z * lam⁻¹‖) *
          (Real.exp (z * lam⁻¹).re * Real.exp (-(z * lam⁻¹).re)) := by
      ring
    _ = _ := by rw [hexp, mul_one]

theorem norm_xiShiftCoreReflectionPairFactor_lineConj_le
    {omega : ℝ} (w : ℂ) (hw : w.im ≤ 0)
    (q : XiShiftCoreZeroCopy omega) :
    ‖xiShiftCoreReflectionPairFactor omega
        (w + (omega : ℂ) * I) (xiShiftCoreLineConjEquiv omega q)‖ ≤
      ‖xiShiftCoreReflectionPairFactor omega
        (w - (omega : ℂ) * I) q‖ := by
  let lambda := xiSpectralPoint q.1
  have habs : |lambda.im| ≤ omega := by
    have hq := q.2
    have ht : (I * lambda).re = -lambda.im := by
      norm_num [mul_re]
    rw [ht, abs_neg] at hq
    exact hq
  have hminus := norm_sub_le_norm_sub_vertical_shift w lambda omega hw
    (abs_le.mp habs).1
  have hplus := norm_add_le_norm_add_vertical_shift w lambda omega hw
    (abs_le.mp habs).2
  have hline :
      xiSpectralPoint (xiShiftCoreLineConjEquiv omega q).1 =
        (starRingEnd ℂ) lambda := by
    exact xiSpectralPoint_lineConj q.1
  have hrefLine :
      xiSpectralPoint
          (xiZeroCopyReflectEquiv (xiShiftCoreLineConjEquiv omega q).1) =
        -(starRingEnd ℂ) lambda := by
    rw [xiSpectralPoint_reflect, hline]
  have href :
      xiSpectralPoint (xiZeroCopyReflectEquiv q.1) = -lambda := by
    exact xiSpectralPoint_reflect q.1
  rw [xiShiftCoreReflectionPairFactor,
    xiShiftCoreReflectionPairFactor, hline, hrefLine, href]
  change ‖weierstrassE1
        ((w + (omega : ℂ) * I) / (starRingEnd ℂ) lambda) *
      weierstrassE1
        ((w + (omega : ℂ) * I) / -(starRingEnd ℂ) lambda)‖ ≤
    ‖weierstrassE1 ((w - (omega : ℂ) * I) / lambda) *
      weierstrassE1 ((w - (omega : ℂ) * I) / -lambda)‖
  have hlambda : lambda ≠ 0 := xiSpectralPoint_ne_zero q.1
  have hconj : (starRingEnd ℂ) lambda ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).mpr hlambda
  have hleftSub :
      ‖1 - (w + (omega : ℂ) * I) / (starRingEnd ℂ) lambda‖ =
        ‖(w + (omega : ℂ) * I) - (starRingEnd ℂ) lambda‖ /
          ‖lambda‖ := by
    rw [show 1 - (w + (omega : ℂ) * I) / (starRingEnd ℂ) lambda =
        ((starRingEnd ℂ) lambda - (w + (omega : ℂ) * I)) /
          (starRingEnd ℂ) lambda by field_simp]
    rw [norm_div, norm_sub_rev, norm_conj]
  have hleftAdd :
      ‖1 - (w + (omega : ℂ) * I) / -(starRingEnd ℂ) lambda‖ =
        ‖(w + (omega : ℂ) * I) + (starRingEnd ℂ) lambda‖ /
          ‖lambda‖ := by
    rw [show 1 - (w + (omega : ℂ) * I) / -(starRingEnd ℂ) lambda =
        (-((starRingEnd ℂ) lambda) - (w + (omega : ℂ) * I)) /
          -((starRingEnd ℂ) lambda) by field_simp; ring]
    rw [norm_div, norm_neg, norm_conj]
    congr 1
    rw [norm_sub_rev]
    congr 1
    ring
  have hrightSub :
      ‖1 - (w - (omega : ℂ) * I) / lambda‖ =
        ‖(w - (omega : ℂ) * I) - lambda‖ / ‖lambda‖ := by
    rw [show 1 - (w - (omega : ℂ) * I) / lambda =
        (lambda - (w - (omega : ℂ) * I)) / lambda by field_simp]
    rw [norm_div, norm_sub_rev]
  have hrightAdd :
      ‖1 - (w - (omega : ℂ) * I) / -lambda‖ =
        ‖(w - (omega : ℂ) * I) + lambda‖ / ‖lambda‖ := by
    rw [show 1 - (w - (omega : ℂ) * I) / -lambda =
        (-lambda - (w - (omega : ℂ) * I)) / -lambda by field_simp; ring]
    rw [norm_div, norm_neg]
    congr 1
    rw [norm_sub_rev]
    congr 1
    ring
  rw [norm_weierstrassE1_mul_div_neg,
    norm_weierstrassE1_mul_div_neg,
    hleftSub, hleftAdd, hrightSub, hrightAdd]
  gcongr

theorem xiShiftCoreCanonicalProduct_ne_zero_below
    {omega : ℝ} {z : ℂ} (hz : z.im < -omega) :
    xiShiftCoreCanonicalProduct omega z ≠ 0 := by
  apply canonicalProductE1IndexedSelected_ne_zero xiSpectralPoint
    (fun q => |(I * xiSpectralPoint q).re| ≤ omega)
    xiSpectralPoint_ne_zero xiSpectralPoint_inv_sq_summable z
  intro q heq
  have hq := q.2
  have ht : (I * xiSpectralPoint q.1).re = -(xiSpectralPoint q.1).im := by
    norm_num [mul_re]
  rw [ht, abs_neg] at hq
  have him := congrArg Complex.im heq
  linarith [(abs_le.mp hq).1]

theorem xiShiftCoreReflectionPairFactor_ne_zero_of_product_ne_zero
    {omega : ℝ} {z : ℂ}
    (hz : xiShiftCoreCanonicalProduct omega z ≠ 0)
    (q : XiShiftCoreZeroCopy omega) :
    xiShiftCoreReflectionPairFactor omega z q ≠ 0 := by
  intro hzero
  have htprod :
      (∏' q : XiShiftCoreZeroCopy omega,
        xiShiftCoreReflectionPairFactor omega z q) = 0 :=
    tprod_of_exists_eq_zero ⟨q, hzero⟩
  rw [tprod_xiShiftCoreReflectionPairFactor] at htprod
  exact hz (mul_self_eq_zero.mp (by simpa only [pow_two] using htprod))

theorem norm_xiShiftCoreCanonicalProduct_vertical_shift_le
    {omega : ℝ} (w : ℂ) (hw : w.im < 0) :
    ‖xiShiftCoreCanonicalProduct omega (w + (omega : ℂ) * I)‖ ≤
      ‖xiShiftCoreCanonicalProduct omega (w - (omega : ℂ) * I)‖ := by
  let zplus : ℂ := w + (omega : ℂ) * I
  let zminus : ℂ := w - (omega : ℂ) * I
  have hzminusIm : zminus.im < -omega := by
    dsimp only [zminus]
    norm_num [sub_im, mul_im]
    linarith
  have hPminus : xiShiftCoreCanonicalProduct omega zminus ≠ 0 :=
    xiShiftCoreCanonicalProduct_ne_zero_below hzminusIm
  by_cases hPplus : xiShiftCoreCanonicalProduct omega zplus = 0
  · rw [hPplus, norm_zero]
    exact norm_nonneg _
  let plusFactor : XiShiftCoreZeroCopy omega → {x : ℝ // 0 < x} := fun q =>
    ⟨‖xiShiftCoreReflectionPairFactor omega zplus
        (xiShiftCoreLineConjEquiv omega q)‖,
      norm_pos_iff.mpr
        (xiShiftCoreReflectionPairFactor_ne_zero_of_product_ne_zero
          hPplus (xiShiftCoreLineConjEquiv omega q))⟩
  let minusFactor : XiShiftCoreZeroCopy omega → {x : ℝ // 0 < x} := fun q =>
    ⟨‖xiShiftCoreReflectionPairFactor omega zminus q‖,
      norm_pos_iff.mpr
        (xiShiftCoreReflectionPairFactor_ne_zero_of_product_ne_zero hPminus q)⟩
  let plusLimit : {x : ℝ // 0 < x} :=
    ⟨‖xiShiftCoreCanonicalProduct omega zplus ^ (2 : ℕ)‖,
      norm_pos_iff.mpr (pow_ne_zero 2 hPplus)⟩
  let minusLimit : {x : ℝ // 0 < x} :=
    ⟨‖xiShiftCoreCanonicalProduct omega zminus ^ (2 : ℕ)‖,
      norm_pos_iff.mpr (pow_ne_zero 2 hPminus)⟩
  have hplusComplex : HasProd
      (fun q : XiShiftCoreZeroCopy omega =>
        xiShiftCoreReflectionPairFactor omega zplus
          (xiShiftCoreLineConjEquiv omega q))
      (xiShiftCoreCanonicalProduct omega zplus ^ (2 : ℕ)) := by
    have hbase : HasProd (xiShiftCoreReflectionPairFactor omega zplus)
        (xiShiftCoreCanonicalProduct omega zplus ^ (2 : ℕ)) := by
      rw [← tprod_xiShiftCoreReflectionPairFactor omega zplus]
      exact (multipliable_xiShiftCoreReflectionPairFactor omega zplus).hasProd
    exact (xiShiftCoreLineConjEquiv omega).hasProd_iff.mpr hbase
  have hminusComplex : HasProd
      (xiShiftCoreReflectionPairFactor omega zminus)
      (xiShiftCoreCanonicalProduct omega zminus ^ (2 : ℕ)) := by
    rw [← tprod_xiShiftCoreReflectionPairFactor omega zminus]
    exact (multipliable_xiShiftCoreReflectionPairFactor omega zminus).hasProd
  have hplusPos : HasProd plusFactor plusLimit := by
    change Tendsto (fun s : Finset (XiShiftCoreZeroCopy omega) =>
      ∏ q ∈ s, plusFactor q) _ (𝓝 plusLimit)
    apply Topology.IsInducing.subtypeVal.tendsto_nhds_iff.mpr
    have hr := hplusComplex.norm
    change Tendsto (fun s : Finset (XiShiftCoreZeroCopy omega) =>
      ∏ q ∈ s, ‖xiShiftCoreReflectionPairFactor omega zplus
        (xiShiftCoreLineConjEquiv omega q)‖) _
      (𝓝 ‖xiShiftCoreCanonicalProduct omega zplus ^ (2 : ℕ)‖) at hr
    convert hr using 1
    funext s
    exact coe_positiveReal_finsetProd s plusFactor
  have hminusPos : HasProd minusFactor minusLimit := by
    change Tendsto (fun s : Finset (XiShiftCoreZeroCopy omega) =>
      ∏ q ∈ s, minusFactor q) _ (𝓝 minusLimit)
    apply Topology.IsInducing.subtypeVal.tendsto_nhds_iff.mpr
    have hr := hminusComplex.norm
    change Tendsto (fun s : Finset (XiShiftCoreZeroCopy omega) =>
      ∏ q ∈ s, ‖xiShiftCoreReflectionPairFactor omega zminus q‖) _
      (𝓝 ‖xiShiftCoreCanonicalProduct omega zminus ^ (2 : ℕ)‖) at hr
    convert hr using 1
    funext s
    exact coe_positiveReal_finsetProd s minusFactor
  have hfactor : ∀ q : XiShiftCoreZeroCopy omega,
      plusFactor q ≤ minusFactor q := by
    intro q
    apply Subtype.coe_le_coe.mp
    simpa only [plusFactor, minusFactor, zplus, zminus] using
      norm_xiShiftCoreReflectionPairFactor_lineConj_le w hw.le q
  have hprod : (∏' q, plusFactor q) ≤ ∏' q, minusFactor q :=
    Multipliable.tprod_le_tprod hfactor hplusPos.multipliable
      hminusPos.multipliable
  rw [hplusPos.tprod_eq, hminusPos.tprod_eq] at hprod
  have hsq : ‖xiShiftCoreCanonicalProduct omega zplus‖ ^ (2 : ℕ) ≤
      ‖xiShiftCoreCanonicalProduct omega zminus‖ ^ (2 : ℕ) := by
    have hprodReal : ‖xiShiftCoreCanonicalProduct omega zplus ^ (2 : ℕ)‖ ≤
        ‖xiShiftCoreCanonicalProduct omega zminus ^ (2 : ℕ)‖ := by
      change (plusLimit : ℝ) ≤ (minusLimit : ℝ)
      exact hprod
    simpa only [norm_pow] using hprodReal
  nlinarith [norm_nonneg (xiShiftCoreCanonicalProduct omega zplus),
    norm_nonneg (xiShiftCoreCanonicalProduct omega zminus)]

/-- Entire shifted core denominator. -/
def xiShiftCoreE (omega : ℝ) (z : ℂ) : ℂ :=
  xiShiftCoreCanonicalProduct omega (-z - (omega : ℂ) * I)

/-- Shifted core quotient after deleting every transverse Xi zero beyond `omega`. -/
def xiShiftCoreTheta (omega : ℝ) (z : ℂ) : ℂ :=
  xiShiftCoreE omega (-z) / xiShiftCoreE omega z

theorem xiShiftCoreE_ne_zero_upperHalfPlane
    {omega : ℝ} {z : ℂ} (hz : 0 < z.im) :
    xiShiftCoreE omega z ≠ 0 := by
  rw [xiShiftCoreE]
  apply xiShiftCoreCanonicalProduct_ne_zero_below
  norm_num [sub_im, neg_im, mul_im]
  linarith

/-- The symmetric shifted core quotient is Schur on the upper half-plane. -/
theorem norm_xiShiftCoreTheta_le_one
    {omega : ℝ} {z : ℂ} (hz : 0 < z.im) :
    ‖xiShiftCoreTheta omega z‖ ≤ 1 := by
  have hden := xiShiftCoreE_ne_zero_upperHalfPlane (omega := omega) hz
  have hcomp := norm_xiShiftCoreCanonicalProduct_vertical_shift_le
    (omega := omega) (-z) (by simp; linarith)
  have hnum :
      ‖xiShiftCoreE omega (-z)‖ =
        ‖xiShiftCoreCanonicalProduct omega
          (-z + (omega : ℂ) * I)‖ := by
    rw [xiShiftCoreE]
    rw [show - -z - (omega : ℂ) * I =
      -(-z + (omega : ℂ) * I) by ring]
    exact congrArg norm (xiShiftCoreCanonicalProduct_even omega
      (-z + (omega : ℂ) * I))
  have hdenEq :
      ‖xiShiftCoreE omega z‖ =
        ‖xiShiftCoreCanonicalProduct omega
          (-z - (omega : ℂ) * I)‖ := rfl
  rw [xiShiftCoreTheta, norm_div, hnum, hdenEq]
  exact (div_le_one (norm_pos_iff.mpr hden)).mpr hcomp

end

end RHTower
