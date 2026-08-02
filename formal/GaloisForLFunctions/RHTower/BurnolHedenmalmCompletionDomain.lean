import GaloisForLFunctions.RHTower.XiThetaL2Cyclicity
import GaloisForLFunctions.RHTower.XiFirstDividedSourceNumericalSector
import GaloisForLFunctions.RHTower.DeningerEulerStirling

/-!
# Burnol--Hedenmalm archimedean completion and maximal coordinate domain

This module supplies the concrete analytic layer missing from the intrinsic Xi divided-chain
theory.  The first removable quotient of the actual centered Xi function is proved to lie in
`L²(ℝ)` at every Xi divisor point, including a multiple or off-axis point.  Both that quotient and
the actual completed Xi source lie in the maximal domain of multiplication by the real spectral
coordinate, where the exact source-defect recurrence holds.

No root location, simplicity, asymptotic computation, or abstract landing map is assumed.
-/

open Complex MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap LinearPMap InnerProductSpace

namespace RHTower

noncomputable section

def completedXiFirstDividedFunction (rho : XiDivisorSupport) (x : ℝ) : ℂ :=
  xiThetaDividedChain (xiSpectralPointSupport rho) 1 (x : ℂ)

theorem continuous_completedXiFirstDividedFunction (rho : XiDivisorSupport) :
    Continuous (completedXiFirstDividedFunction rho) := by
  rw [continuous_iff_continuousAt]
  intro x
  change ContinuousAt (fun y : ℝ =>
    xiThetaDividedChain (xiSpectralPointSupport rho) 1 (y : ℂ)) x
  simpa only [Function.comp_def] using
    (xiThetaDividedChain_analyticAt
      (xiSpectralPointSupport rho) 1 (x : ℂ)).continuousAt.comp
        Complex.continuous_ofReal.continuousAt

theorem memLp_XiC_ofReal :
    MemLp (fun x : ℝ => XiC (x : ℂ)) 2 volume := by
  rw [show (fun x : ℝ => XiC (x : ℂ)) = (𝓕 xiThetaSchwartzSource) by
    funext x
    exact (fourier_xiThetaSchwartzSource x).symm]
  exact (𝓕 xiThetaSchwartzSource).memLp 2 volume

theorem integrable_sq_norm_XiC_ofReal :
    Integrable (fun x : ℝ => ‖XiC (x : ℂ)‖ ^ 2) volume :=
  (memLp_two_iff_integrable_sq_norm
    ((continuous_iff_continuousAt.mpr fun x => by
      simpa only [Function.comp_def] using
        (XiC_analytic (x : ℂ) (Set.mem_univ _)).continuousAt.comp
          Complex.continuous_ofReal.continuousAt).aestronglyMeasurable)).mp
      memLp_XiC_ofReal

def completedXiDividedRadius (rho : XiDivisorSupport) : ℝ :=
  ‖xiSpectralPointSupport rho‖ + 1

theorem one_le_norm_ofReal_sub_xiSpectralPointSupport_of_not_mem_Icc
    (rho : XiDivisorSupport) {x : ℝ}
    (hx : x ∉ Icc (-completedXiDividedRadius rho) (completedXiDividedRadius rho)) :
    1 ≤ ‖(x : ℂ) - xiSpectralPointSupport rho‖ := by
  have habs : completedXiDividedRadius rho < |x| := by
    have hR : 0 < completedXiDividedRadius rho := by
      dsimp only [completedXiDividedRadius]
      linarith [norm_nonneg (xiSpectralPointSupport rho)]
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · have hxneg : x < 0 := lt_trans hx (neg_neg_of_pos hR)
      rw [abs_of_neg hxneg]
      linarith
    · have hxpos : 0 < x := lt_trans hR hx
      rw [abs_of_pos hxpos]
      exact hx
  have hrev := norm_sub_norm_le (x : ℂ) (xiSpectralPointSupport rho)
  rw [Complex.norm_real, Real.norm_eq_abs] at hrev
  dsimp only [completedXiDividedRadius] at habs
  linarith

theorem norm_completedXiFirstDividedFunction_le_norm_XiC_of_not_mem_Icc
    (rho : XiDivisorSupport) {x : ℝ}
    (hx : x ∉ Icc (-completedXiDividedRadius rho) (completedXiDividedRadius rho)) :
    ‖completedXiFirstDividedFunction rho x‖ ≤ ‖XiC (x : ℂ)‖ := by
  have hden :=
    one_le_norm_ofReal_sub_xiSpectralPointSupport_of_not_mem_Icc rho hx
  have hne : (x : ℂ) ≠ xiSpectralPointSupport rho := by
    intro heq
    rw [heq, sub_self, norm_zero] at hden
    linarith
  rw [completedXiFirstDividedFunction,
    xiThetaDividedChain_one_apply_of_ne _ _ hne
      (XiC_xiSpectralPointSupport_eq_zero rho), norm_div]
  exact div_le_self (norm_nonneg _) hden

theorem memLp_completedXiFirstDividedFunction (rho : XiDivisorSupport) :
    MemLp (completedXiFirstDividedFunction rho) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (continuous_completedXiFirstDividedFunction rho).aestronglyMeasurable).mpr
  let R := completedXiDividedRadius rho
  have hcompact : IntegrableOn
      (fun x : ℝ => ‖completedXiFirstDividedFunction rho x‖ ^ 2)
      (Icc (-R) R) :=
    ((continuous_completedXiFirstDividedFunction rho).norm.pow 2).continuousOn
      |>.integrableOn_compact isCompact_Icc
  have htail : IntegrableOn
      (fun x : ℝ => ‖completedXiFirstDividedFunction rho x‖ ^ 2)
      (Icc (-R) R)ᶜ := by
    refine integrable_sq_norm_XiC_ofReal.integrableOn.mono' ?_ ?_
    · exact ((continuous_completedXiFirstDividedFunction rho).norm.pow 2).aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with x hx
      simpa only [Real.norm_of_nonneg (sq_nonneg _)] using
        pow_le_pow_left₀ (norm_nonneg _)
          (norm_completedXiFirstDividedFunction_le_norm_XiC_of_not_mem_Icc rho hx) 2
  have hunion := hcompact.union htail
  rw [union_compl_self] at hunion
  exact (integrableOn_univ.mp hunion)

abbrev BurnolCompletedSpectralL2 := Lp ℂ 2 (volume : Measure ℝ)

/-- Maximal `L²` domain of multiplication by the real spectral coordinate. -/
def maximalRealCoordinateDomain : Submodule ℂ BurnolCompletedSpectralL2 where
  carrier := {f | MemLp (fun x : ℝ => (x : ℂ) * f x) 2 volume}
  zero_mem' := by
    refine (memLp_congr_ae ?_).mpr MemLp.zero
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx
    change (x : ℂ) * (0 : BurnolCompletedSpectralL2) x = (0 : ℝ → ℂ) x
    rw [hx]
    simp
  add_mem' := by
    intro f g hf hg
    refine (memLp_congr_ae ?_).mpr (hf.add hg)
    filter_upwards [Lp.coeFn_add f g] with x hx
    change (x : ℂ) * (f + g) x =
      (x : ℂ) * f x + (x : ℂ) * g x
    rw [hx, Pi.add_apply, mul_add]
  smul_mem' := by
    intro c f hf
    refine (memLp_congr_ae ?_).mpr (hf.const_mul c)
    filter_upwards [Lp.coeFn_smul c f] with x hx
    rw [hx, Pi.smul_apply, smul_eq_mul]
    ring

/-- Multiplication by the real coordinate on its maximal `L²` domain. -/
def maximalRealCoordinate :
    BurnolCompletedSpectralL2 →ₗ.[ℂ] BurnolCompletedSpectralL2 where
  domain := maximalRealCoordinateDomain
  toFun :=
    { toFun := fun f => f.property.toLp _
      map_add' := by
        intro f g
        rw [← MemLp.toLp_add f.property g.property]
        apply MemLp.toLp_congr
        filter_upwards [Lp.coeFn_add (f : BurnolCompletedSpectralL2)
          (g : BurnolCompletedSpectralL2)] with x hx
        change (x : ℂ) * ((f : BurnolCompletedSpectralL2) +
          (g : BurnolCompletedSpectralL2)) x =
            ((fun y : ℝ => (y : ℂ) * (f : BurnolCompletedSpectralL2) y) +
              fun y : ℝ => (y : ℂ) * (g : BurnolCompletedSpectralL2) y) x
        rw [hx, Pi.add_apply, Pi.add_apply, mul_add]
      map_smul' := by
        intro c f
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul c f.property]
        apply MemLp.toLp_congr
        filter_upwards [Lp.coeFn_smul c (f : BurnolCompletedSpectralL2)] with x hx
        change (x : ℂ) * (c • (f : BurnolCompletedSpectralL2)) x =
          (c • fun y : ℝ => (y : ℂ) * (f : BurnolCompletedSpectralL2) y) x
        rw [hx, Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
        ring }

theorem maximalRealCoordinate_apply_ae (f : maximalRealCoordinate.domain) :
    (maximalRealCoordinate f : ℝ → ℂ) =ᵐ[volume]
      fun x => (x : ℂ) * (f : BurnolCompletedSpectralL2) x :=
  MemLp.coeFn_toLp f.property

/-- Real-coordinate multiplication is symmetric on its maximal domain. -/
theorem maximalRealCoordinate_formalSelfAdjoint :
    maximalRealCoordinate.IsFormalAdjoint maximalRealCoordinate := by
  intro f g
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [maximalRealCoordinate_apply_ae f,
    maximalRealCoordinate_apply_ae g] with x hf hg
  rw [hf, hg]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

/-- The actual first completed Xi quotient as an `L²(ℝ)` vector. -/
def completedXiFirstDividedL2 (rho : XiDivisorSupport) : BurnolCompletedSpectralL2 :=
  (memLp_completedXiFirstDividedFunction rho).toLp _

theorem completedXiFirstDividedL2_ae (rho : XiDivisorSupport) :
    (completedXiFirstDividedL2 rho : ℝ → ℂ) =ᵐ[volume]
      completedXiFirstDividedFunction rho :=
  (memLp_completedXiFirstDividedFunction rho).coeFn_toLp

theorem memLp_coordinate_XiC_ofReal :
    MemLp (fun x : ℝ => (x : ℂ) * XiC (x : ℂ)) 2 volume := by
  rw [show (fun x : ℝ => (x : ℂ) * XiC (x : ℂ)) =
      (GaloisForLFunctions.mulXCLM (𝓕 xiThetaSchwartzSource) : ℝ → ℂ) by
    funext x
    rw [GaloisForLFunctions.mulXCLM_apply, fourier_xiThetaSchwartzSource]]
  exact (GaloisForLFunctions.mulXCLM (𝓕 xiThetaSchwartzSource)).memLp 2 volume

theorem xiThetaFourierSourceL2_mem_maximalRealCoordinateDomain :
    xiThetaFourierSourceL2 ∈ maximalRealCoordinateDomain := by
  refine (memLp_congr_ae ?_).mpr memLp_coordinate_XiC_ofReal
  filter_upwards [xiThetaFourierSourceL2_ae] with x hx
  rw [hx]

theorem xiThetaFourierSourceL2_ne_zero : xiThetaFourierSourceL2 ≠ 0 := by
  intro hzero
  have hzero_ae : (xiThetaFourierSourceL2 : ℝ → ℂ) =ᵐ[volume]
      (0 : ℝ → ℂ) := by
    rw [hzero]
    exact Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)
  have hxi_ae : (fun x : ℝ => XiC (x : ℂ)) =ᵐ[volume] (0 : ℝ → ℂ) :=
    xiThetaFourierSourceL2_ae.symm.trans hzero_ae
  have hxiContinuous : Continuous (fun x : ℝ => XiC (x : ℂ)) :=
    continuous_iff_continuousAt.mpr fun x => by
      simpa only [Function.comp_def] using
        (XiC_analytic (x : ℂ) (Set.mem_univ _)).continuousAt.comp
          Complex.continuous_ofReal.continuousAt
  have hident := (Continuous.ae_eq_iff_eq (volume : Measure ℝ)
    hxiContinuous continuous_zero).mp hxi_ae
  exact XiC_zero_ne (congrFun hident 0)

theorem completedXiFirstDividedL2_mem_maximalRealCoordinateDomain
    (rho : XiDivisorSupport) :
    completedXiFirstDividedL2 rho ∈ maximalRealCoordinateDomain := by
  have hq := memLp_completedXiFirstDividedFunction rho
  have hxi := memLp_XiC_ofReal
  have hsum : MemLp (fun x : ℝ =>
      xiSpectralPointSupport rho * completedXiFirstDividedFunction rho x +
        XiC (x : ℂ)) 2 volume := (hq.const_mul _).add hxi
  refine (memLp_congr_ae ?_).mpr hsum
  filter_upwards [completedXiFirstDividedL2_ae rho] with x hx
  rw [hx]
  exact xiThetaDividedChain_multiplication_step rho
    (xiSupportMultiplicity_pos rho) (x : ℂ)

/-- Exact genuine `L²` completed source-defect recurrence. -/
theorem maximalRealCoordinate_completedXiFirstDividedL2 (rho : XiDivisorSupport) :
    maximalRealCoordinate
        ⟨completedXiFirstDividedL2 rho,
          completedXiFirstDividedL2_mem_maximalRealCoordinateDomain rho⟩ =
      xiSpectralPointSupport rho • completedXiFirstDividedL2 rho +
        xiThetaFourierSourceL2 := by
  apply Lp.ext
  filter_upwards [maximalRealCoordinate_apply_ae
      ⟨completedXiFirstDividedL2 rho,
        completedXiFirstDividedL2_mem_maximalRealCoordinateDomain rho⟩,
    completedXiFirstDividedL2_ae rho, xiThetaFourierSourceL2_ae,
    Lp.coeFn_add (xiSpectralPointSupport rho • completedXiFirstDividedL2 rho)
      xiThetaFourierSourceL2,
    Lp.coeFn_smul (xiSpectralPointSupport rho)
      (completedXiFirstDividedL2 rho)] with x hcoord hq hxi hadd hsmul
  rw [hcoord, hq, hadd]
  rw [Pi.add_apply, hsmul, Pi.smul_apply, smul_eq_mul, hq, hxi]
  exact xiThetaDividedChain_multiplication_step rho
    (xiSupportMultiplicity_pos rho) (x : ℂ)

theorem completedXiFirstDividedL2_ne_zero (rho : XiDivisorSupport) :
    completedXiFirstDividedL2 rho ≠ 0 := by
  intro hq
  let qDom : maximalRealCoordinate.domain :=
    ⟨completedXiFirstDividedL2 rho,
      completedXiFirstDividedL2_mem_maximalRealCoordinateDomain rho⟩
  have hqDom : qDom = 0 := Subtype.ext hq
  have hrec := maximalRealCoordinate_completedXiFirstDividedL2 rho
  change maximalRealCoordinate qDom =
    xiSpectralPointSupport rho • completedXiFirstDividedL2 rho +
      xiThetaFourierSourceL2 at hrec
  have hz : maximalRealCoordinate (0 : maximalRealCoordinate.domain) = 0 :=
    maximalRealCoordinate.toFun.map_zero
  rw [hqDom, hz, hq, smul_zero, zero_add] at hrec
  exact xiThetaFourierSourceL2_ne_zero hrec.symm

/-- **Concrete completion-domain package.**  Archimedean completion puts the nonzero Xi source
and every nonzero first divided Xi vector into the same maximal real-coordinate domain, but the
coordinate action retains the nonzero common source as its exact defect. -/
theorem burnolHedenmalm_archimedeanCompletion_domain_radicalExchange
    (rho : XiDivisorSupport) :
    xiThetaFourierSourceL2 ∈ maximalRealCoordinate.domain ∧
      completedXiFirstDividedL2 rho ∈ maximalRealCoordinate.domain ∧
      maximalRealCoordinate
          ⟨completedXiFirstDividedL2 rho,
            completedXiFirstDividedL2_mem_maximalRealCoordinateDomain rho⟩ =
        xiSpectralPointSupport rho • completedXiFirstDividedL2 rho +
          xiThetaFourierSourceL2 ∧
      xiThetaFourierSourceL2 ≠ 0 ∧ completedXiFirstDividedL2 rho ≠ 0 := by
  exact ⟨xiThetaFourierSourceL2_mem_maximalRealCoordinateDomain,
    completedXiFirstDividedL2_mem_maximalRealCoordinateDomain rho,
    maximalRealCoordinate_completedXiFirstDividedL2 rho,
    xiThetaFourierSourceL2_ne_zero,
    completedXiFirstDividedL2_ne_zero rho⟩

end
end RHTower
