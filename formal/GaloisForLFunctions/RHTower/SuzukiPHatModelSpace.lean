import GaloisForLFunctions.RHTower.SuzukiPHatIsometry
import GaloisForLFunctions.RHTower.SuzukiFGammaBasis

noncomputable section

/-!
# The transform lies in the model space

Equation (3.8) of the source: away from the divisor the transform `𝒫̂_φ` is the series over the
spectrum with the reproducing vectors as building blocks.  Conjugating the ray representation and
using that the zeros are real turns `𝒫̂_φ` into a Cauchy series with conjugated coefficients, which
the support summation converts into the energy-kernel series.

The energy kernel at a spectral point is a nonzero scalar multiple of `F_γ`, so every partial sum
lies in the model space; the model space is closed, so the `L²` limit — which is `𝒫̂_φ` almost
everywhere — lies in it too.  This is the inclusion `K_0 ⊆ K(Θ)` of Theorem 5.6.
-/

open MeasureTheory Set Complex Filter Topology

namespace RHTower

/-- The coefficient of `F_ρ` in the transform's expansion. -/
def suzukiPHatEnergyCoef {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (ρ : XiDivisorSupport) : ℂ :=
  (-I) * ((xiSupportMult ρ : ℂ)
    * (starRingEnd ℂ) (suzukiPHatCoefFn φ ((xiRealSpectralPointSupport ρ : ℝ) : ℂ)))

theorem summable_conj_suzukiPHatRay {a : ℝ}
    (φ : SuzukiSmoothZeroMeanTest a) (x : ℝ) :
    Summable fun q : XiZeroCopy =>
      (starRingEnd ℂ) (suzukiPHatCoefFn φ (xiSpectralPoint q))
        * (((x : ℝ) : ℂ) - xiSpectralPoint q)⁻¹ := by
  have hbase := summable_suzukiPHatRay φ x
  refine Summable.of_norm_bounded hbase.norm fun q => ?_
  rw [norm_mul, norm_mul, RCLike.norm_conj]

/-- On the axis the sharp half of the inner function is the conjugate of `A/E`. -/
theorem suzukiThetaSharp_half_ofReal {x : ℝ}
    (hx : XiC ((x : ℝ) : ℂ) ≠ 0) :
    (1 + suzukiThetaSharp ((x : ℝ) : ℂ)) / 2
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

/-- **The pointwise expansion (3.8).**  Away from the divisor the transform is the basis series. -/
theorem hasSum_suzukiPHat_energy (hRH : RiemannHypothesis) {a : ℝ}
    (φ : SuzukiSmoothZeroMeanTest a) {x : ℝ} (hx : XiC ((x : ℝ) : ℂ) ≠ 0) :
    HasSum (fun ρ : XiDivisorSupport =>
        suzukiPHatEnergyCoef φ ρ * suzukiEnergyKernelFun ρ x)
      (suzukiPHat (fun t => (φ : ℝ → ℂ) t) ((x : ℝ) : ℂ)) := by
  have hcauchy := (hasSum_supportCauchy hRH
    (fun w : ℂ => (starRingEnd ℂ) (suzukiPHatCoefFn φ w)) x
    (summable_conj_suzukiPHatRay φ x)).mul_left ((-I) * suzukiHalfInner ((x : ℝ) : ℂ))
  have hval : ((-I) * suzukiHalfInner ((x : ℝ) : ℂ))
      * (∑' q : XiZeroCopy, (starRingEnd ℂ) (suzukiPHatCoefFn φ (xiSpectralPoint q))
        * (((x : ℝ) : ℂ) - xiSpectralPoint q)⁻¹)
      = suzukiPHat (fun t => (φ : ℝ → ℂ) t) ((x : ℝ) : ℂ) := by
    have hconjsum : (starRingEnd ℂ) (∑' q : XiZeroCopy,
          suzukiPHatCoefFn φ (xiSpectralPoint q) * (((x : ℝ) : ℂ) - xiSpectralPoint q)⁻¹)
        = ∑' q : XiZeroCopy, (starRingEnd ℂ) (suzukiPHatCoefFn φ (xiSpectralPoint q))
          * (((x : ℝ) : ℂ) - xiSpectralPoint q)⁻¹ := by
      have h := ((summable_suzukiPHatRay φ x).hasSum).map (starRingEnd ℂ)
        Complex.continuous_conj
      refine (HasSum.tsum_eq (h.congr_fun ?_)).symm
      intro q
      have hreal : xiSpectralPoint q = ((xiRealSpectralPoint q : ℝ) : ℂ) :=
        xiSpectralPoint_eq_ofReal_of_rh hRH q
      show (starRingEnd ℂ) (suzukiPHatCoefFn φ (xiSpectralPoint q))
          * (((x : ℝ) : ℂ) - xiSpectralPoint q)⁻¹
        = (starRingEnd ℂ) (suzukiPHatCoefFn φ (xiSpectralPoint q)
            * (((x : ℝ) : ℂ) - xiSpectralPoint q)⁻¹)
      rw [map_mul, map_inv₀, map_sub, Complex.conj_ofReal, hreal, Complex.conj_ofReal]
    rw [suzukiPHat_ofReal_eq_conj,
      suzukiPHatConj_eq_tsum φ.continuous.measurable (integrable_suzukiSmoothZeroMeanTest φ)
        (suzukiSmoothZeroMeanTest_supp φ)]
    have hray : (∑' q : XiZeroCopy,
        suzukiPHatRayTerm (fun t => (φ : ℝ → ℂ) t) ((x : ℝ) : ℂ) q)
        = ∑' q : XiZeroCopy, suzukiPHatCoefFn φ (xiSpectralPoint q)
          * (((x : ℝ) : ℂ) - xiSpectralPoint q)⁻¹ :=
      tsum_congr fun q => suzukiPHatRayTerm_eq φ ((x : ℝ) : ℂ) q
    rw [hray, show I * (1 + suzukiThetaSharp ((x : ℝ) : ℂ)) / 2
        = I * ((1 + suzukiThetaSharp ((x : ℝ) : ℂ)) / 2) by ring,
      suzukiThetaSharp_half_ofReal hx, map_mul, map_mul, Complex.conj_I,
      Complex.conj_conj, hconjsum]
  rw [hval] at hcauchy
  refine hcauchy.congr_fun fun ρ => ?_
  rw [suzukiPHatEnergyCoef, suzukiEnergyKernelFun]
  ring

/-! ## The transform lies in the model space -/

theorem suzukiFGammaFamily_eq_smul_energyKernel (hRH : RiemannHypothesis)
    (ρ : XiDivisorSupport) :
    suzukiFGammaFamily hRH ρ
      = (((Real.sqrt ((xiSupportMult ρ : ℝ) / Real.pi) : ℝ) : ℂ) * I)
        • suzukiEnergyKernel hRH ρ := by
  refine MeasureTheory.Lp.ext ?_
  have hnull : volume ({xiRealSpectralPointSupport ρ} : Set ℝ) = 0 := by simp
  filter_upwards [coeFn_suzukiFGammaFamily hRH ρ,
    MeasureTheory.Lp.coeFn_smul
      (((Real.sqrt ((xiSupportMult ρ : ℝ) / Real.pi) : ℝ) : ℂ) * I)
      (suzukiEnergyKernel hRH ρ),
    (memLp_suzukiEnergyKernelFun hRH ρ).coeFn_toLp,
    MeasureTheory.compl_mem_ae_iff.mpr hnull] with x h1 h2 h3 hx
  have hne : x ≠ xiRealSpectralPointSupport ρ := fun h => hx (by simp [h])
  have hxne : ((x : ℝ) : ℂ) ≠ ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) := by simpa using hne
  rw [h1, h2, Pi.smul_apply]
  simp only [suzukiEnergyKernel]
  rw [h3, smul_eq_mul, suzukiFGammaFun,
    dslope_suzukiHalfInner_apply (XiC_xiRealSpectralPointSupport hRH ρ) hxne,
    suzukiEnergyKernelFun, suzukiCauchyKernel]
  rw [div_eq_mul_inv]
  ring

theorem suzukiEnergyKernel_mem_suzukiModelSpace (hRH : RiemannHypothesis)
    (ρ : XiDivisorSupport) : suzukiEnergyKernel hRH ρ ∈ suzukiModelSpace := by
  have hpi := Real.pi_pos
  have hm : (0 : ℝ) < (xiSupportMult ρ : ℝ) := by exact_mod_cast xiSupportMult_pos ρ
  have hs : (0 : ℝ) < Real.sqrt ((xiSupportMult ρ : ℝ) / Real.pi) :=
    Real.sqrt_pos.mpr (by positivity)
  have hc : (((Real.sqrt ((xiSupportMult ρ : ℝ) / Real.pi) : ℝ) : ℂ) * I) ≠ 0 := by
    refine mul_ne_zero ?_ Complex.I_ne_zero
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hs
  have hbase := suzukiFGammaLp_mem_suzukiModelSpace hRH (xiSupportMult_pos ρ)
    (analyticOrderAt_xiRealSpectralPointSupport hRH ρ) (XiC_xiRealSpectralPointSupport hRH ρ)
  have heq := suzukiFGammaFamily_eq_smul_energyKernel hRH ρ
  have hsmul : suzukiEnergyKernel hRH ρ
      = ((((Real.sqrt ((xiSupportMult ρ : ℝ) / Real.pi) : ℝ) : ℂ) * I)⁻¹)
        • suzukiFGammaFamily hRH ρ := by
    rw [heq, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [hsmul]
  exact Submodule.smul_mem _ _ hbase


theorem norm_suzukiPHatEnergyCoef {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a)
    (ρ : XiDivisorSupport) :
    ‖suzukiPHatEnergyCoef φ ρ‖ = ‖suzukiPHatSupportCoef φ ρ‖ := by
  rw [suzukiPHatEnergyCoef, suzukiPHatSupportCoef, norm_mul, norm_neg, Complex.norm_I,
    one_mul, norm_mul, norm_mul, RCLike.norm_conj]

theorem suzukiCauchyPartial_mem_suzukiModelSpace (hRH : RiemannHypothesis)
    (c : XiDivisorSupport → ℂ) (N : ℕ) :
    suzukiCauchyPartial hRH c N ∈ suzukiModelSpace := by
  rw [suzukiCauchyPartial]
  refine Submodule.sum_mem _ fun n _ => ?_
  exact Submodule.smul_mem _ _ (suzukiEnergyKernel_mem_suzukiModelSpace hRH _)

/-- **The transform is an element of the model space.** -/
theorem exists_suzukiPHat_lp (hRH : RiemannHypothesis) {a : ℝ}
    (φ : SuzukiSmoothZeroMeanTest a) :
    ∃ S : Lp ℂ 2 (volume : Measure ℝ), S ∈ suzukiModelSpace ∧
      Tendsto (suzukiCauchyPartial hRH (suzukiPHatEnergyCoef φ)) atTop (𝓝 S) ∧
      (S : ℝ → ℂ) =ᵐ[volume]
        fun x : ℝ => suzukiPHat (fun t => (φ : ℝ → ℂ) t) ((x : ℝ) : ℂ) := by
  have hsa : Summable fun ρ : XiDivisorSupport =>
      ‖suzukiPHatEnergyCoef φ ρ‖ ^ (2 : ℕ) * suzukiCauchyWeight ρ := by
    refine (summable_weighted_suzukiPHatSupportCoef hRH φ).congr fun ρ => ?_
    rw [norm_suzukiPHatEnergyCoef]
  have hg : ∀ᵐ x ∂(volume : Measure ℝ),
      HasSum (fun ρ : XiDivisorSupport =>
        suzukiPHatEnergyCoef φ ρ * suzukiEnergyKernelFun ρ x)
        (suzukiPHat (fun t => (φ : ℝ → ℂ) t) ((x : ℝ) : ℂ)) := by
    filter_upwards [ae_XiC_ofReal_ne_zero] with x hx
    exact hasSum_suzukiPHat_energy hRH φ hx
  obtain ⟨S, hS, hae⟩ := exists_lp_of_hasSum hRH (suzukiPHatEnergyCoef φ) hsa _ hg
  refine ⟨S, ?_, hS, hae⟩
  refine IsClosed.mem_of_tendsto isClosed_suzukiModelSpace hS ?_
  filter_upwards with N
  exact suzukiCauchyPartial_mem_suzukiModelSpace hRH _ N


end RHTower
