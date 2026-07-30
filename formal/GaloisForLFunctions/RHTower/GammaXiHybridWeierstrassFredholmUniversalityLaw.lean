import GaloisForLFunctions.HTGeometry.GammaFactorialObservabilitySpectrum
import GaloisForLFunctions.HTGeometry.GammaWeierstrass
import GaloisForLFunctions.RHTower.XiHedenmalmReciprocalOperator

/-!
# Gamma--Xi hybrid Weierstrass--Fredholm universality

One diagonal operator on the disjoint union of the archimedean Weierstrass modes and the
multiplicity-exact Xi divisor is compact, injective, and observability-unstable. Its
self-adjointness is exactly RH, while its regularized determinant is the product of the
reciprocal Gamma factor and the Xi canonical product.
-/

open Filter Topology
open scoped ENNReal

namespace RHTower

open GaloisForLFunctions HilbertSchmidt

noncomputable section

/-- Disjoint archimedean/Xi spectrum at real nonzero archimedean scale `s`. -/
def gammaXiHybridWeierstrassEigenvalue
    (s : ℝ) : ℕ ⊕ XiZeroCopy → ℂ
  | Sum.inl n => -(s : ℂ) / ((n : ℂ) + 1)
  | Sum.inr q => (xiSpectralPoint q)⁻¹

/-- Square summability of the archimedean reciprocal-integer branch. -/
theorem summable_normSq_gammaWeierstrassEigenvalue (s : ℝ) :
    Summable (fun n : ℕ => ‖-(s : ℂ) / ((n : ℂ) + 1)‖ ^ 2) := by
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
    have htwo : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have htail :=
      (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr htwo
    simpa using htail
  have hmul := hbase.mul_left (‖(s : ℂ)‖ ^ 2)
  apply hmul.congr
  intro n
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hnorm : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
    rw [show (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnpos]
  rw [norm_div, norm_neg, hnorm, div_pow]
  ring

/-- The complete disjoint-union spectrum is square summable. -/
theorem summable_normSq_gammaXiHybridWeierstrassEigenvalue (s : ℝ) :
    Summable (fun i : ℕ ⊕ XiZeroCopy =>
      ‖gammaXiHybridWeierstrassEigenvalue s i‖ ^ 2) := by
  apply Summable.sum _
  · simpa only [Function.comp_def, gammaXiHybridWeierstrassEigenvalue] using
      summable_normSq_gammaWeierstrassEigenvalue s
  · simpa only [Function.comp_def, gammaXiHybridWeierstrassEigenvalue] using
      summable_norm_xiSpectralPoint_inv_sq

/-- Hybrid diagonal kernel. -/
def gammaXiHybridWeierstrassKernel (s : ℝ) :
    (ℕ ⊕ XiZeroCopy) × (ℕ ⊕ XiZeroCopy) → ℂ :=
  diagMul (gammaXiHybridWeierstrassEigenvalue s)

theorem gammaXiHybridWeierstrassKernel_isHS (s : ℝ) :
    IsHS (gammaXiHybridWeierstrassKernel s) :=
  isHS_diagMul_infinite _
    (summable_normSq_gammaXiHybridWeierstrassEigenvalue s)

/-- Hybrid operator on the square-summable disjoint spectral carrier. -/
def gammaXiHybridWeierstrassOperator (s : ℝ) :
    lp (fun _ : ℕ ⊕ XiZeroCopy => ℂ) 2 →L[ℂ]
      lp (fun _ : ℕ ⊕ XiZeroCopy => ℂ) 2 :=
  toOperator (gammaXiHybridWeierstrassKernel_isHS s)

theorem gammaXiHybridWeierstrassOperator_apply
    (s : ℝ) (f : lp (fun _ : ℕ ⊕ XiZeroCopy => ℂ) 2)
    (i : ℕ ⊕ XiZeroCopy) :
    gammaXiHybridWeierstrassOperator s f i =
      gammaXiHybridWeierstrassEigenvalue s i * f i := by
  rw [gammaXiHybridWeierstrassOperator,
    toOperator_apply (gammaXiHybridWeierstrassKernel_isHS s),
    tsum_eq_single i]
  · simp [gammaXiHybridWeierstrassKernel, diagMul]
  · intro j hji
    simp [gammaXiHybridWeierstrassKernel, diagMul, hji.symm]

/-- The hybrid operator is compact without RH. -/
theorem gammaXiHybridWeierstrassOperator_isCompact (s : ℝ) :
    IsCompactOperator (gammaXiHybridWeierstrassOperator s) :=
  (isHilbertSchmidt_toOperator
    (gammaXiHybridWeierstrassKernel_isHS s)).isCompactOperator

theorem gammaXiHybridWeierstrassEigenvalue_ne_zero
    {s : ℝ} (hs : s ≠ 0) (i : ℕ ⊕ XiZeroCopy) :
    gammaXiHybridWeierstrassEigenvalue s i ≠ 0 := by
  cases i with
  | inl n =>
      have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs
      have hnC : (n : ℂ) + 1 ≠ 0 := by
        intro hn
        have hre := congrArg Complex.re hn
        have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        exact hpos.ne' (by simpa using hre)
      exact div_ne_zero
        (neg_ne_zero.mpr hsC) hnC
  | inr q =>
      exact inv_ne_zero (xiSpectralPoint_ne_zero q)

/-- Every diagonal coordinate is nonzero at nonzero archimedean scale. -/
theorem gammaXiHybridWeierstrassOperator_injective
    {s : ℝ} (hs : s ≠ 0) :
    Function.Injective (gammaXiHybridWeierstrassOperator s) := by
  intro x y hxy
  apply lp.ext
  funext i
  have hi := congrArg
    (fun z : lp (fun _ : ℕ ⊕ XiZeroCopy => ℂ) 2 => z i) hxy
  change gammaXiHybridWeierstrassOperator s x i =
    gammaXiHybridWeierstrassOperator s y i at hi
  rw [gammaXiHybridWeierstrassOperator_apply,
    gammaXiHybridWeierstrassOperator_apply] at hi
  exact mul_left_cancel₀ (gammaXiHybridWeierstrassEigenvalue_ne_zero hs i) hi

theorem gammaXiHybridWeierstrassOperator_single_inl
    (s : ℝ) (n : ℕ) :
    gammaXiHybridWeierstrassOperator s
        (lp.single 2 (Sum.inl n : ℕ ⊕ XiZeroCopy) 1) =
      (-(s : ℂ) / ((n : ℂ) + 1)) •
        lp.single 2 (Sum.inl n : ℕ ⊕ XiZeroCopy) 1 := by
  apply lp.ext
  funext i
  rw [gammaXiHybridWeierstrassOperator_apply]
  by_cases hi : i = Sum.inl n
  · subst i
    simp [gammaXiHybridWeierstrassEigenvalue]
  · simp [gammaXiHybridWeierstrassEigenvalue, hi]

/-- Natural-number modes form an approximate unit kernel for every real scale. -/
theorem gammaXiHybridWeierstrassOperator_hasApproximateUnitKernel (s : ℝ) :
    HasApproximateUnitKernel (gammaXiHybridWeierstrassOperator s) := by
  refine ⟨fun n => lp.single 2 (Sum.inl n : ℕ ⊕ XiZeroCopy) (1 : ℂ), ?_, ?_⟩
  · intro n
    rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
    norm_num
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have ht :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul |s|
    have htzero :
        Tendsto (fun n : ℕ => |s| * (1 / ((n : ℝ) + 1)))
          atTop (nhds 0) := by
      simpa using ht
    convert htzero using 1
    funext n
    rw [gammaXiHybridWeierstrassOperator_single_inl, norm_smul,
      lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), norm_one, mul_one,
      norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [show ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 by
      rw [show (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnpos]]
    ring

/-- Approximate blindness is exact nonclosedness of the injective hybrid range. -/
theorem gammaXiHybridWeierstrassOperator_not_isClosed_range
    {s : ℝ} (hs : s ≠ 0) :
    ¬ IsClosed (Set.range (gammaXiHybridWeierstrassOperator s)) :=
  (hasApproximateUnitKernel_iff_not_isClosed_range
    (gammaXiHybridWeierstrassOperator s)
    (gammaXiHybridWeierstrassOperator_injective hs)).mp
      (gammaXiHybridWeierstrassOperator_hasApproximateUnitKernel s)

theorem hsAdjoint_gammaXiHybridWeierstrassKernel_eq
    {s : ℝ} (hRH : RiemannHypothesis) :
    hsAdjoint (gammaXiHybridWeierstrassKernel s) =
      gammaXiHybridWeierstrassKernel s := by
  funext p
  rcases p with ⟨i, j⟩
  by_cases hij : i = j
  · subst j
    cases i with
    | inl n =>
        simp [hsAdjoint, gammaXiHybridWeierstrassKernel, diagMul,
          gammaXiHybridWeierstrassEigenvalue]
    | inr q =>
        obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
        simp [hsAdjoint, gammaXiHybridWeierstrassKernel, diagMul,
          gammaXiHybridWeierstrassEigenvalue, ht]
  · have hji : j ≠ i := Ne.symm hij
    simp [hsAdjoint, gammaXiHybridWeierstrassKernel, diagMul, hij, hji]

theorem gammaXiHybridWeierstrassOperator_isSelfAdjoint_of_rh
    (s : ℝ) (hRH : RiemannHypothesis) :
    IsSelfAdjoint (gammaXiHybridWeierstrassOperator s) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  rw [gammaXiHybridWeierstrassOperator,
    adjoint_toOperator (gammaXiHybridWeierstrassKernel_isHS s)]
  exact toOperator_congr _ _
    (hsAdjoint_gammaXiHybridWeierstrassKernel_eq hRH)

theorem riemannHypothesis_of_gammaXiHybridWeierstrassOperator_isSelfAdjoint
    {s : ℝ}
    (hself : IsSelfAdjoint (gammaXiHybridWeierstrassOperator s)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  have hop :
      ContinuousLinearMap.adjoint (gammaXiHybridWeierstrassOperator s) =
        gammaXiHybridWeierstrassOperator s :=
    hself.adjoint_eq
  have hmatrix := congrArg matrixOf hop
  rw [matrixOf_adjoint, gammaXiHybridWeierstrassOperator,
    matrixOf_toOperator] at hmatrix
  have hdiag := congrFun hmatrix
    (Sum.inr q, Sum.inr q)
  simp [hsAdjoint, gammaXiHybridWeierstrassKernel, diagMul,
    gammaXiHybridWeierstrassEigenvalue] at hdiag
  have hstar :
      (starRingEnd ℂ) (xiSpectralPoint q) = xiSpectralPoint q := by
    have hinv := congrArg Inv.inv hdiag
    simpa [map_inv₀, xiSpectralPoint_ne_zero q] using hinv
  have him := congrArg Complex.im hstar
  have himzero : (xiSpectralPoint q).im = 0 := by
    have hneg : -(xiSpectralPoint q).im = (xiSpectralPoint q).im := by
      simpa using him
    linarith
  refine ⟨(xiSpectralPoint q).re, ?_⟩
  apply Complex.ext
  · simp
  · simp [himzero]

/-- The hybrid reality condition is exactly RH; the Gamma block contributes no extra premise. -/
theorem gammaXiHybridWeierstrassOperator_isSelfAdjoint_iff_rh (s : ℝ) :
    IsSelfAdjoint (gammaXiHybridWeierstrassOperator s) ↔
      RiemannHypothesis :=
  ⟨riemannHypothesis_of_gammaXiHybridWeierstrassOperator_isSelfAdjoint,
    gammaXiHybridWeierstrassOperator_isSelfAdjoint_of_rh s⟩

set_option maxHeartbeats 800000 in
/-- The hybrid Fredholm determinant factors into the reciprocal archimedean Gamma factor at
`z*s` and the multiplicity-exact Xi canonical product at `z`. -/
theorem fredholmDet_gammaXiHybridWeierstrassKernel_eq_gammaFactor_mul_xiCanonicalProduct
    (s : ℝ) (r : ℝ)
    (hr : r * hsNorm (gammaXiHybridWeierstrassKernel s) < 1)
    (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) r)
    (hregular : ∀ m : ℕ, z * (s : ℂ) ≠ -(m : ℂ)) :
    fredholmDet (gammaXiHybridWeierstrassKernel s) z =
      (z * (s : ℂ) *
          Complex.exp ((Real.eulerMascheroniConstant : ℂ) * (z * (s : ℂ))) *
          Complex.Gamma (z * (s : ℂ)))⁻¹ *
        xiCanonicalProduct z := by
  rw [gammaXiHybridWeierstrassKernel,
    fredholmDet_tprod_diagMul
      (gammaXiHybridWeierstrassEigenvalue s)
      (summable_normSq_gammaXiHybridWeierstrassEigenvalue s)
      r hr z hz]
  let factor : ℕ ⊕ XiZeroCopy → ℂ := fun i =>
    (1 - z * gammaXiHybridWeierstrassEigenvalue s i) *
      Complex.exp (z * gammaXiHybridWeierstrassEigenvalue s i)
  let t : ℂ := z * (s : ℂ)
  have hgammaMult :
      Multipliable (fun n : ℕ => factor (Sum.inl n)) := by
    apply (multipliable_weierstrassFactor t).congr
    intro n
    simp only [factor, gammaXiHybridWeierstrassEigenvalue, t]
    congr 1 <;> ring_nf
  have hxiHas :
      HasProd
        (fun q : XiZeroCopy =>
          weierstrassE1 (z / xiSpectralPoint q))
        (xiCanonicalProduct z) :=
    xiCanonicalProduct_hasProdLocallyUniformlyOn.hasProd
      (Set.mem_univ z)
  have hxiMult :
      Multipliable (fun q : XiZeroCopy => factor (Sum.inr q)) := by
    apply hxiHas.multipliable.congr
    intro q
    simp [factor, gammaXiHybridWeierstrassEigenvalue,
      weierstrassE1, div_eq_mul_inv]
  change (∏' i : ℕ ⊕ XiZeroCopy, factor i) = _
  rw [hgammaMult.tprod_sum hxiMult]
  have hgammaProduct :
      (∏' n : ℕ, factor (Sum.inl n)) =
        (t * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * t) *
          Complex.Gamma t)⁻¹ := by
    let W : ℂ :=
      ∏' n : ℕ,
        (1 + t / ((n : ℂ) + 1)) *
          Complex.exp (-(t / ((n : ℂ) + 1)))
    have hW :
        W = (t * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * t) *
          Complex.Gamma t)⁻¹ := by
      have hweierstrass := Gamma_inv_weierstrass t (by simpa [t] using hregular)
      have hGamma : Complex.Gamma t ≠ 0 :=
        Complex.Gamma_ne_zero (by simpa [t] using hregular)
      refine eq_inv_of_mul_eq_one_right ?_
      calc
        (t * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * t) *
              Complex.Gamma t) * W =
            Complex.Gamma t *
              (t * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * t) * W) := by
                ring
        _ = Complex.Gamma t * (Complex.Gamma t)⁻¹ := by
              rw [← hweierstrass]
        _ = 1 := mul_inv_cancel₀ hGamma
    calc
      (∏' n : ℕ, factor (Sum.inl n)) = W := by
        apply tprod_congr
        intro n
        simp only [factor, gammaXiHybridWeierstrassEigenvalue, t]
        congr 1 <;> ring_nf
      _ = _ := hW
  have hxiProduct :
      (∏' q : XiZeroCopy, factor (Sum.inr q)) =
        xiCanonicalProduct z := by
    calc
      (∏' q : XiZeroCopy, factor (Sum.inr q)) =
          ∏' q : XiZeroCopy,
            weierstrassE1 (z / xiSpectralPoint q) := by
              apply tprod_congr
              intro q
              simp [factor, gammaXiHybridWeierstrassEigenvalue,
                weierstrassE1, div_eq_mul_inv]
      _ = xiCanonicalProduct z := hxiHas.tprod_eq
  rw [hgammaProduct, hxiProduct]

/-- **Gamma--Xi hybrid Weierstrass--Fredholm universality law.**

One hybrid operator is unconditionally compact and observability-unstable, is injective at every
nonzero real archimedean scale, is self-adjoint exactly under RH, and carries the exact product of
the archimedean Gamma and Xi-divisor Fredholm factors. -/
theorem gammaXiHybrid_weierstrassFredholmUniversality
    (s : ℝ) (hs : s ≠ 0) :
    IsCompactOperator (gammaXiHybridWeierstrassOperator s) ∧
      Function.Injective (gammaXiHybridWeierstrassOperator s) ∧
      HasApproximateUnitKernel (gammaXiHybridWeierstrassOperator s) ∧
      ¬ IsClosed (Set.range (gammaXiHybridWeierstrassOperator s)) ∧
      (IsSelfAdjoint (gammaXiHybridWeierstrassOperator s) ↔
        RiemannHypothesis) ∧
      ∀ (r : ℝ) (z : ℂ),
        r * hsNorm (gammaXiHybridWeierstrassKernel s) < 1 →
        z ∈ Metric.ball (0 : ℂ) r →
        (∀ m : ℕ, z * (s : ℂ) ≠ -(m : ℂ)) →
        fredholmDet (gammaXiHybridWeierstrassKernel s) z =
          (z * (s : ℂ) *
              Complex.exp
                ((Real.eulerMascheroniConstant : ℂ) * (z * (s : ℂ))) *
              Complex.Gamma (z * (s : ℂ)))⁻¹ *
            xiCanonicalProduct z := by
  exact ⟨gammaXiHybridWeierstrassOperator_isCompact s,
    gammaXiHybridWeierstrassOperator_injective hs,
    gammaXiHybridWeierstrassOperator_hasApproximateUnitKernel s,
    gammaXiHybridWeierstrassOperator_not_isClosed_range hs,
    gammaXiHybridWeierstrassOperator_isSelfAdjoint_iff_rh s,
    fun r z hr hz hregular =>
      fredholmDet_gammaXiHybridWeierstrassKernel_eq_gammaFactor_mul_xiCanonicalProduct
        s r hr z hz hregular⟩

end

end RHTower
