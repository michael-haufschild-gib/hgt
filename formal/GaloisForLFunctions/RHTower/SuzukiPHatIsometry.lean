import GaloisForLFunctions.RHTower.SuzukiScrewTestRayEnergy
import GaloisForLFunctions.RHTower.SuzukiWeilTransformRaySeries
import GaloisForLFunctions.RHTower.SuzukiWeilPropOneThree

/-!
# Suzuki Theorem 4.4: the transform is an isometry from the screw form

`RH` holds if and only if

```text
‖𝒫̂_φ‖²_{L²(ℝ)} = π ⟨φ, φ⟩_{G_g}
```

for every smooth compactly supported test `φ` of zero mean.

The forward direction runs the transform through the same Cauchy-kernel isometry that produced
the screw line: `suzukiPHatConj_eq_tsum` exhibits `𝒫̂_φ` as `i · conj(A/E)` times a Cauchy series
whose `q`-th coefficient is `(∫ (e^{-iγ_q t} - 1) conj(φ(t)) dt)/γ_q`, so its squared `L²` norm is
`π` times the coefficients' `ℓ²` norm.  Matching that against the ray energy of `⟨φ,φ⟩_{G_g}` is
the reflection `γ ↦ -γ` of the divisor.

The converse needs no new analysis: the hypothesis makes the screw form nonnegative on exactly
the class of tests appearing in Su22 Theorem 1.3, already formalized here, so RH follows.  In
particular Suzuki's own argument by contradiction — a nonreal zero together with Yoshida's test
functions — is not needed.
-/

open Complex Filter Topology MeasureTheory Set

namespace RHTower
noncomputable section

/-- The ray coefficient of the transform, as a function of the spectral point. -/
def suzukiPHatCoefFn {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (w : ℂ) : ℂ :=
  (∫ t : ℝ, (Complex.exp (-(I * w * (t : ℂ))) - 1) * (starRingEnd ℂ) ((φ : ℝ → ℂ) t)) / w

theorem suzukiPHatRayTerm_eq {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (z : ℂ)
    (q : XiZeroCopy) :
    suzukiPHatRayTerm (fun t => (φ : ℝ → ℂ) t) z q
      = suzukiPHatCoefFn φ (xiSpectralPoint q) * (z - xiSpectralPoint q)⁻¹ := by
  rw [suzukiPHatRayTerm, suzukiPHatCoefFn, div_mul_eq_div_div, div_eq_mul_inv]

theorem norm_expSlopeConj_test_le {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (q : XiZeroCopy)
    (t : ℝ) :
    ‖(Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1) * (starRingEnd ℂ) ((φ : ℝ → ℂ) t)‖
      ≤ (Real.exp (|a| / 2) + 1) * ‖(φ : ℝ → ℂ) t‖ := by
  have h := norm_expSlope_test_le φ q t
  rw [norm_mul] at h
  rw [norm_mul, RCLike.norm_conj]
  exact h

theorem integrable_expSlopeConj_test {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (q : XiZeroCopy) :
    Integrable (fun t : ℝ => (Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1)
      * (starRingEnd ℂ) ((φ : ℝ → ℂ) t)) := by
  refine Integrable.mono'
    ((integrable_suzukiSmoothZeroMeanTest φ).norm.const_mul (Real.exp (|a| / 2) + 1)) ?_
    (Filter.Eventually.of_forall (norm_expSlopeConj_test_le φ q))
  refine AEStronglyMeasurable.mul ?_
    (Complex.continuous_conj.comp φ.continuous).aestronglyMeasurable
  exact ((Complex.continuous_exp.comp (by continuity)).sub continuous_const).aestronglyMeasurable

theorem norm_suzukiPHatCoefFn_le {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (q : XiZeroCopy) :
    ‖suzukiPHatCoefFn φ (xiSpectralPoint q)‖
      ≤ ((Real.exp (|a| / 2) + 1) * ∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖) / ‖xiSpectralPoint q‖ := by
  rw [suzukiPHatCoefFn, norm_div]
  have hpos : (0 : ℝ) < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  rw [div_le_div_iff_of_pos_right hpos]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  refine le_trans (MeasureTheory.integral_mono (integrable_expSlopeConj_test φ q).norm
    ((integrable_suzukiSmoothZeroMeanTest φ).norm.const_mul _)
    (norm_expSlopeConj_test_le φ q)) ?_
  rw [MeasureTheory.integral_const_mul]

theorem suzukiSmoothZeroMeanTest_supp {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) :
    ∀ t : ℝ, |a| < |t| → (φ : ℝ → ℂ) t = 0 := by
  intro t ht
  by_contra h0
  have hmem : t ∈ Icc (-a) a := φ.support_subset (by simpa [Function.mem_support] using h0)
  have : |t| ≤ |a| := le_trans (abs_le.mpr ⟨hmem.1, hmem.2⟩) (le_abs_self a)
  linarith

theorem summable_suzukiPHatRay {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (x : ℝ) :
    Summable fun q : XiZeroCopy =>
      suzukiPHatCoefFn φ (xiSpectralPoint q) * (((x : ℝ) : ℂ) - xiSpectralPoint q)⁻¹ := by
  set Mφ : ℝ := (Real.exp (|a| / 2) + 1) * ∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖ with hM
  refine Summable.of_norm_bounded
    ((summable_xiResolventProduct_norm (((x : ℝ) : ℂ))).mul_left Mφ) fun q => ?_
  have hγ : (0 : ℝ) < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hMnn : 0 ≤ Mφ :=
    mul_nonneg (by positivity) (MeasureTheory.integral_nonneg fun u => norm_nonneg _)
  have hswap : ‖(xiSpectralPoint q * (xiSpectralPoint q - ((x : ℝ) : ℂ)))⁻¹‖
      = 1 / (‖xiSpectralPoint q‖ * ‖(((x : ℝ) : ℂ)) - xiSpectralPoint q‖) := by
    rw [norm_inv, norm_mul, one_div]
    congr 2
    rw [show xiSpectralPoint q - ((x : ℝ) : ℂ) = -((((x : ℝ) : ℂ)) - xiSpectralPoint q) by ring,
      norm_neg]
  rw [hswap, norm_mul, norm_inv]
  rcases eq_or_ne ((((x : ℝ) : ℂ)) - xiSpectralPoint q) 0 with h0 | h0
  · rw [h0]
    simp
  · have hd : (0 : ℝ) < ‖(((x : ℝ) : ℂ)) - xiSpectralPoint q‖ := norm_pos_iff.mpr h0
    rw [mul_one_div, ← div_div, ← div_eq_mul_inv, div_le_div_iff_of_pos_right hd]
    exact norm_suzukiPHatCoefFn_le φ q


/-- Support-level coefficient of the transform's Cauchy series. -/
def suzukiPHatSupportCoef {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (ρ : XiDivisorSupport) : ℂ :=
  (xiSupportMult ρ : ℂ) * suzukiPHatCoefFn φ ((xiRealSpectralPointSupport ρ : ℝ) : ℂ)

/-- The energy-weighted form of the transform's ray series. -/
def suzukiPHatEnergyFun {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (x : ℝ) : ℂ :=
  suzukiHalfInner ((x : ℝ) : ℂ) *
    ∑' q : XiZeroCopy,
      suzukiPHatCoefFn φ (xiSpectralPoint q) * (((x : ℝ) : ℂ) - xiSpectralPoint q)⁻¹

theorem hasSum_suzukiPHatEnergy (hRH : RiemannHypothesis) {a : ℝ}
    (φ : SuzukiSmoothZeroMeanTest a) (x : ℝ) :
    HasSum (fun ρ : XiDivisorSupport =>
        suzukiPHatSupportCoef φ ρ * suzukiEnergyKernelFun ρ x) (suzukiPHatEnergyFun φ x) := by
  have h := (hasSum_supportCauchy hRH (suzukiPHatCoefFn φ) x
    (summable_suzukiPHatRay φ x)).mul_left (suzukiHalfInner ((x : ℝ) : ℂ))
  refine h.congr_fun fun ρ => ?_
  rw [suzukiEnergyKernelFun, suzukiPHatSupportCoef]
  ring

theorem summable_norm_sq_suzukiPHatCoefFn {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) :
    Summable fun q : XiZeroCopy => ‖suzukiPHatCoefFn φ (xiSpectralPoint q)‖ ^ (2 : ℕ) := by
  set Mφ : ℝ := (Real.exp (|a| / 2) + 1) * ∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖ with hM
  have hMnn : 0 ≤ Mφ :=
    mul_nonneg (by positivity) (MeasureTheory.integral_nonneg fun u => norm_nonneg _)
  refine Summable.of_nonneg_of_le (fun q => sq_nonneg _) (fun q => ?_)
    (xiSpectralPoint_inv_sq_summable.mul_left (Mφ ^ (2 : ℕ)))
  have h := norm_suzukiPHatCoefFn_le φ q
  have hγ : (0 : ℝ) < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hnn : (0 : ℝ) ≤ ‖suzukiPHatCoefFn φ (xiSpectralPoint q)‖ := norm_nonneg _
  calc ‖suzukiPHatCoefFn φ (xiSpectralPoint q)‖ ^ (2 : ℕ)
      ≤ (Mφ / ‖xiSpectralPoint q‖) ^ (2 : ℕ) := by nlinarith
    _ = Mφ ^ (2 : ℕ) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
        rw [div_pow]
        ring

theorem summable_weighted_suzukiPHatSupportCoef (hRH : RiemannHypothesis) {a : ℝ}
    (φ : SuzukiSmoothZeroMeanTest a) :
    Summable fun ρ : XiDivisorSupport =>
      ‖suzukiPHatSupportCoef φ ρ‖ ^ (2 : ℕ) * suzukiCauchyWeight ρ := by
  have hbase := summable_norm_sq_suzukiPHatCoefFn φ
  have hsig := (summable_sigma_of_nonneg
    (f := fun q : XiZeroCopy => ‖suzukiPHatCoefFn φ (xiSpectralPoint q)‖ ^ (2 : ℕ))
    (fun q => sq_nonneg _)).mp hbase
  refine ((hsig.2).mul_left Real.pi).congr fun ρ => ?_
  have hpos := xiSupportMult_pos ρ
  have hi : Fin (xiSupportMult ρ) := ⟨0, hpos⟩
  show Real.pi * (∑' j : Fin (xiSupportMult ρ),
      ‖suzukiPHatCoefFn φ (xiSpectralPoint (⟨ρ, j⟩ : XiZeroCopy))‖ ^ (2 : ℕ))
      = ‖suzukiPHatSupportCoef φ ρ‖ ^ (2 : ℕ) * suzukiCauchyWeight ρ
  · have hconst : ∀ j : Fin (xiSupportMult ρ),
        ‖suzukiPHatCoefFn φ (xiSpectralPoint (⟨ρ, j⟩ : XiZeroCopy))‖ ^ (2 : ℕ)
          = ‖suzukiPHatCoefFn φ ((xiRealSpectralPointSupport ρ : ℝ) : ℂ)‖ ^ (2 : ℕ) := by
      intro j
      rw [xiSpectralPoint_copy_eq hRH]
    rw [tsum_fintype, Finset.sum_congr rfl (fun j _ => hconst j), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, suzukiPHatSupportCoef,
      suzukiCauchyWeight, norm_mul, Complex.norm_natCast, mul_pow]
    have hmR : ((xiSupportMult ρ : ℝ)) ≠ 0 := by
      have : (0 : ℝ) < (xiSupportMult ρ : ℝ) := by exact_mod_cast hpos
      exact ne_of_gt this
    field_simp

theorem tsum_weighted_suzukiPHatSupportCoef (hRH : RiemannHypothesis) {a : ℝ}
    (φ : SuzukiSmoothZeroMeanTest a) :
    (∑' ρ : XiDivisorSupport, (starRingEnd ℂ) (suzukiPHatSupportCoef φ ρ)
        * suzukiPHatSupportCoef φ ρ * ((suzukiCauchyWeight ρ : ℝ) : ℂ))
      = ((Real.pi : ℝ) : ℂ) * ∑' q : XiZeroCopy,
        ((‖suzukiPHatCoefFn φ (xiSpectralPoint q)‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  have hbase : Summable fun q : XiZeroCopy =>
      ((‖suzukiPHatCoefFn φ (xiSpectralPoint q)‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    refine Summable.of_norm_bounded (summable_norm_sq_suzukiPHatCoefFn φ) fun q => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hsigma := hbase.tsum_sigma
  rw [hsigma, ← tsum_mul_left]
  refine tsum_congr fun ρ => ?_
  have hpos := xiSupportMult_pos ρ
  have hi : Fin (xiSupportMult ρ) := ⟨0, hpos⟩
  have hconst : ∀ j : Fin (xiSupportMult ρ),
      ((‖suzukiPHatCoefFn φ (xiSpectralPoint (⟨ρ, j⟩ : XiZeroCopy))‖ ^ (2 : ℕ) : ℝ) : ℂ)
        = ((‖suzukiPHatCoefFn φ ((xiRealSpectralPointSupport ρ : ℝ) : ℂ)‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    intro j
    rw [xiSpectralPoint_copy_eq hRH]
  show _ = ((Real.pi : ℝ) : ℂ) * ∑' j : Fin (xiSupportMult ρ),
    ((‖suzukiPHatCoefFn φ (xiSpectralPoint (⟨ρ, j⟩ : XiZeroCopy))‖ ^ (2 : ℕ) : ℝ) : ℂ)
  rw [tsum_fintype, Finset.sum_congr rfl (fun j _ => hconst j), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, suzukiPHatSupportCoef,
    suzukiCauchyWeight]
  have hmC : ((xiSupportMult ρ : ℂ)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hnorm : (starRingEnd ℂ) (suzukiPHatCoefFn φ ((xiRealSpectralPointSupport ρ : ℝ) : ℂ))
      * suzukiPHatCoefFn φ ((xiRealSpectralPointSupport ρ : ℝ) : ℂ)
      = ((‖suzukiPHatCoefFn φ ((xiRealSpectralPointSupport ρ : ℝ) : ℂ)‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.sq_norm]
  rw [map_mul, Complex.conj_natCast]
  push_cast
  rw [show ((xiSupportMult ρ : ℂ)
      * (starRingEnd ℂ) (suzukiPHatCoefFn φ ((xiRealSpectralPointSupport ρ : ℝ) : ℂ)))
      * ((xiSupportMult ρ : ℂ) * suzukiPHatCoefFn φ ((xiRealSpectralPointSupport ρ : ℝ) : ℂ))
      = (xiSupportMult ρ : ℂ) ^ (2 : ℕ) *
        ((starRingEnd ℂ) (suzukiPHatCoefFn φ ((xiRealSpectralPointSupport ρ : ℝ) : ℂ))
          * suzukiPHatCoefFn φ ((xiRealSpectralPointSupport ρ : ℝ) : ℂ)) by ring, hnorm]
  field_simp
  push_cast
  ring


theorem integral_conj_suzukiPHatEnergy (hRH : RiemannHypothesis) {a : ℝ}
    (φ : SuzukiSmoothZeroMeanTest a) :
    (∫ x : ℝ, (starRingEnd ℂ) (suzukiPHatEnergyFun φ x) * suzukiPHatEnergyFun φ x)
      = ((Real.pi : ℝ) : ℂ) * ∑' q : XiZeroCopy,
        ((‖suzukiPHatCoefFn φ (xiSpectralPoint q)‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [integral_conj_of_hasSum hRH (suzukiPHatSupportCoef φ) (suzukiPHatSupportCoef φ)
    (summable_weighted_suzukiPHatSupportCoef hRH φ)
    (summable_weighted_suzukiPHatSupportCoef hRH φ) _ _
    (Filter.Eventually.of_forall fun x => hasSum_suzukiPHatEnergy hRH φ x)
    (Filter.Eventually.of_forall fun x => hasSum_suzukiPHatEnergy hRH φ x)]
  exact tsum_weighted_suzukiPHatSupportCoef hRH φ

theorem norm_suzukiPHat_ofReal_eq {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) {x : ℝ}
    (hx : XiC ((x : ℝ) : ℂ) ≠ 0) :
    ‖suzukiPHat (fun t => (φ : ℝ → ℂ) t) ((x : ℝ) : ℂ)‖ = ‖suzukiPHatEnergyFun φ x‖ := by
  rw [suzukiPHat_ofReal_eq_conj, RCLike.norm_conj]
  rw [suzukiPHatConj_eq_tsum φ.continuous.measurable (integrable_suzukiSmoothZeroMeanTest φ)
    (suzukiSmoothZeroMeanTest_supp φ)]
  have hsharp : (1 + suzukiThetaSharp ((x : ℝ) : ℂ)) / 2
      = (starRingEnd ℂ) (suzukiHalfInner ((x : ℝ) : ℂ)) := by
    have hE := xiHedenmalmDeBrangesESharp_ofReal_ne_zero hx
    have hadd := xiHedenmalmDeBrangesE_add_sharp (((x : ℝ) : ℂ))
    have hXiconj : (starRingEnd ℂ) (XiC ((x : ℝ) : ℂ)) = XiC ((x : ℝ) : ℂ) :=
      Complex.conj_eq_iff_im.mpr (XiC_ofReal_im x)
    have hrhs : (starRingEnd ℂ) (suzukiHalfInner ((x : ℝ) : ℂ))
        = XiC ((x : ℝ) : ℂ) / xiHedenmalmDeBrangesESharp ((x : ℝ) : ℂ) := by
      rw [suzukiHalfInner, map_div₀, hXiconj, xiHedenmalmDeBrangesESharp_ofReal_eq_conj]
    rw [hrhs, suzukiThetaSharp]
    field_simp
    linear_combination hadd
  have hray : (∑' q : XiZeroCopy, suzukiPHatRayTerm (fun t => (φ : ℝ → ℂ) t) ((x : ℝ) : ℂ) q)
      = ∑' q : XiZeroCopy,
        suzukiPHatCoefFn φ (xiSpectralPoint q) * (((x : ℝ) : ℂ) - xiSpectralPoint q)⁻¹ :=
    tsum_congr fun q => suzukiPHatRayTerm_eq φ ((x : ℝ) : ℂ) q
  rw [show I * (1 + suzukiThetaSharp ((x : ℝ) : ℂ)) / 2
      = I * ((1 + suzukiThetaSharp ((x : ℝ) : ℂ)) / 2) by ring, hsharp, hray,
    suzukiPHatEnergyFun]
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, RCLike.norm_conj]

theorem integral_normSq_suzukiPHat (hRH : RiemannHypothesis) {a : ℝ}
    (φ : SuzukiSmoothZeroMeanTest a) :
    ((∫ x : ℝ, ‖suzukiPHat (fun t => (φ : ℝ → ℂ) t) ((x : ℝ) : ℂ)‖ ^ (2 : ℕ) : ℝ) : ℂ)
      = ∫ x : ℝ, (starRingEnd ℂ) (suzukiPHatEnergyFun φ x) * suzukiPHatEnergyFun φ x := by
  rw [← integral_complex_ofReal]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [ae_ne_zero_and_XiC_ne_zero] with x hx
  rw [norm_suzukiPHat_ofReal_eq φ hx.2, mul_comm, Complex.mul_conj, Complex.sq_norm]


theorem suzukiTestRayCoefBar_eq_conj (hRH : RiemannHypothesis) {a : ℝ}
    (φ : SuzukiSmoothZeroMeanTest a) (q : XiZeroCopy) :
    suzukiTestRayCoefBar φ q = (starRingEnd ℂ) (suzukiTestRayCoef φ q) := by
  have hreal : (starRingEnd ℂ) (xiSpectralPoint q) = xiSpectralPoint q := by
    rw [xiSpectralPoint_eq_ofReal_of_rh hRH, Complex.conj_ofReal]
  rw [suzukiTestRayCoef, suzukiTestRayCoefBar, ← integral_conj]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show (Complex.exp (I * xiSpectralPoint q * (u : ℂ)) - 1) * (starRingEnd ℂ) ((φ : ℝ → ℂ) u)
      = (starRingEnd ℂ)
        ((Complex.exp (-(I * xiSpectralPoint q * (u : ℂ))) - 1) * (φ : ℝ → ℂ) u)
  rw [map_mul, map_sub, map_one, ← Complex.exp_conj]
  congr 2
  rw [map_neg, map_mul, map_mul, hreal, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem tsum_normSq_suzukiPHatCoefFn (hRH : RiemannHypothesis) {a : ℝ}
    (φ : SuzukiSmoothZeroMeanTest a) :
    (∑' q : XiZeroCopy, ((‖suzukiPHatCoefFn φ (xiSpectralPoint q)‖ ^ (2 : ℕ) : ℝ) : ℂ))
      = suzukiScrewSmoothForm φ φ := by
  rw [suzukiScrewSmoothForm_eq_tsum φ,
    ← xiZeroCopyReflectEquiv.tsum_eq
      (fun q : XiZeroCopy => ((‖suzukiPHatCoefFn φ (xiSpectralPoint q)‖ ^ (2 : ℕ) : ℝ) : ℂ))]
  refine tsum_congr fun q => ?_
  have hrefl : xiSpectralPoint (xiZeroCopyReflectEquiv q) = -xiSpectralPoint q :=
    xiSpectralPoint_reflect q
  have hγ : (0 : ℝ) < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hN : suzukiPHatCoefFn φ (xiSpectralPoint (xiZeroCopyReflectEquiv q))
      = suzukiTestRayCoefBar φ q / (-xiSpectralPoint q) := by
    rw [hrefl, suzukiPHatCoefFn, suzukiTestRayCoefBar]
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show (Complex.exp (-(I * (-xiSpectralPoint q) * (t : ℂ))) - 1)
        * (starRingEnd ℂ) ((φ : ℝ → ℂ) t)
        = (Complex.exp (I * xiSpectralPoint q * (t : ℂ)) - 1)
          * (starRingEnd ℂ) ((φ : ℝ → ℂ) t)
    rw [show -(I * (-xiSpectralPoint q) * (t : ℂ)) = I * xiSpectralPoint q * (t : ℂ) by ring]
  have hsq : xiSpectralPoint q ^ (2 : ℕ) = ((‖xiSpectralPoint q‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [xiSpectralPoint_eq_ofReal_of_rh hRH]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    push_cast
    ring
  rw [hN, norm_div, norm_neg, suzukiTestRayCoefBar_eq_conj hRH φ q, RCLike.norm_conj, hsq]
  rw [show (starRingEnd ℂ) (suzukiTestRayCoef φ q) * suzukiTestRayCoef φ q
      = ((‖suzukiTestRayCoef φ q‖ ^ (2 : ℕ) : ℝ) : ℂ) by
    rw [mul_comm, Complex.mul_conj, Complex.sq_norm]]
  have hne : ((‖xiSpectralPoint q‖ : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hγ
  push_cast
  field_simp

/-- **Suzuki Theorem 4.4, forward direction.**  Under the Riemann hypothesis the squared `L²`
norm of the transform of a smooth zero-mean test is `π` times its screw form. -/
theorem normSq_suzukiPHat_eq_pi_mul_screwForm (hRH : RiemannHypothesis) {a : ℝ}
    (φ : SuzukiSmoothZeroMeanTest a) :
    ((∫ x : ℝ, ‖suzukiPHat (fun t => (φ : ℝ → ℂ) t) ((x : ℝ) : ℂ)‖ ^ (2 : ℕ) : ℝ) : ℂ)
      = ((Real.pi : ℝ) : ℂ) * suzukiScrewSmoothForm φ φ := by
  rw [integral_normSq_suzukiPHat hRH φ, integral_conj_suzukiPHatEnergy hRH φ,
    tsum_normSq_suzukiPHatCoefFn hRH φ]

/-- **Suzuki Theorem 4.4.**  RH holds if and only if the transform is an isometry from the screw
form to `L²(ℝ)` on smooth zero-mean tests. -/
theorem riemannHypothesis_iff_normSq_suzukiPHat :
    RiemannHypothesis ↔ ∀ (a : ℝ), 0 < a → ∀ φ : SuzukiSmoothZeroMeanTest a,
      (∫ x : ℝ, ‖suzukiPHat (fun t => (φ : ℝ → ℂ) t) ((x : ℝ) : ℂ)‖ ^ (2 : ℕ))
        = Real.pi * (suzukiScrewSmoothForm φ φ).re := by
  constructor
  · intro hRH a _ φ
    have h := normSq_suzukiPHat_eq_pi_mul_screwForm hRH φ
    have hre := congrArg Complex.re h
    rw [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero] at hre
    exact hre
  · intro h
    refine riemannHypothesis_of_suzukiSmoothTestFormNonnegative fun a ha φ => ?_
    have h1 := h a ha φ
    have h2 : (0 : ℝ) ≤ ∫ x : ℝ, ‖suzukiPHat (fun t => (φ : ℝ → ℂ) t) ((x : ℝ) : ℂ)‖ ^ (2 : ℕ) :=
      MeasureTheory.integral_nonneg fun x => sq_nonneg _
    rw [h1] at h2
    nlinarith [Real.pi_pos]


end
end RHTower
