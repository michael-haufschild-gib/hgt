import GaloisForLFunctions.RHTower.CCM.CCMConnesConsaniCircleDirac
import GaloisForLFunctions.RHTower.Deninger.DeningerSmoothPeriodic
import GaloisForLFunctions.HTGeometry.FourierMultiplierTruncation

open Module Topology Filter
open MeasureTheory intervalIntegral
open scoped InnerProductSpace

namespace RHTower

open HilbertSchmidt GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

local instance (L : CCMCircleLength) : Fact (0 < (L : ℝ)) := ⟨L.property⟩

abbrev CCMCirclePhysicalL2 (L : CCMCircleLength) :=
  Lp ℂ 2 (AddCircle.haarAddCircle (T := (L : ℝ)))

def ccmSmoothCircleFunction (L : CCMCircleLength)
    (a : DeningerSmoothPeriodic (L : ℝ)) : AddCircle (L : ℝ) → ℂ := by
  exact AddCircle.liftIoc (L : ℝ) 0 (a : ℝ → ℂ)

theorem continuous_ccmSmoothCircleFunction (L : CCMCircleLength)
    (a : DeningerSmoothPeriodic (L : ℝ)) :
    Continuous (ccmSmoothCircleFunction L a) := by
  apply AddCircle.liftIoc_continuous
  · simpa using (deningerSmoothPeriodic_periodic a 0).symm
  · exact (deningerSmoothPeriodic_contDiff a).continuous.continuousOn

def ccmSmoothCircleContinuous (L : CCMCircleLength)
    (a : DeningerSmoothPeriodic (L : ℝ)) : C(AddCircle (L : ℝ), ℂ) :=
  ⟨ccmSmoothCircleFunction L a, continuous_ccmSmoothCircleFunction L a⟩

def ccmSmoothCirclePhysicalMultiplier (L : CCMCircleLength)
    (a : DeningerSmoothPeriodic (L : ℝ)) :
    CCMCirclePhysicalL2 L →L[ℂ] CCMCirclePhysicalL2 L :=
  lpBoundedMulCLM
    (continuous_ccmSmoothCircleFunction L a).measurable
    (norm_nonneg (ccmSmoothCircleContinuous L a))
    (fun x => ContinuousMap.norm_coe_le_norm (ccmSmoothCircleContinuous L a) x)

def ccmSmoothCircleMultiplier (L : CCMCircleLength)
    (a : DeningerSmoothPeriodic (L : ℝ)) :
    DiagonalL2 ℤ →L[ℂ] DiagonalL2 ℤ := by
  exact (fourierBasis (T := (L : ℝ))).repr.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    ccmSmoothCirclePhysicalMultiplier L a ∘L
    (fourierBasis (T := (L : ℝ))).repr.toContinuousLinearEquiv.symm.toContinuousLinearMap

theorem deningerFourierCoeff_eq_fourierCoeffOn (L : CCMCircleLength)
    (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn L.property f n = deningerFourierCoeff (L : ℝ) f n := by
  rw [fourierCoeffOn_eq_integral, deningerFourierCoeff]
  simp only [sub_zero, Complex.real_smul, one_div]
  push_cast
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [fourier_coe_apply, deningerFourierKernel]
  congr 2
  push_cast
  ring

private theorem fourierCoeff_physicalMultiplier_fourierLp
    (L : CCMCircleLength) (a : DeningerSmoothPeriodic (L : ℝ)) (j l : ℤ) :
    fourierCoeff
        (((ccmSmoothCirclePhysicalMultiplier L a
            (fourierLp (T := (L : ℝ)) 2 j) : CCMCirclePhysicalL2 L) :
          AddCircle (L : ℝ) → ℂ)) l =
      fourierCoeffOn L.property (a : ℝ → ℂ) (l - j) := by
  have hae :
      (((ccmSmoothCirclePhysicalMultiplier L a
          (fourierLp (T := (L : ℝ)) 2 j) : CCMCirclePhysicalL2 L) :
        AddCircle (L : ℝ) → ℂ)) =ᵐ[AddCircle.haarAddCircle]
        fun z => fourier j z * ccmSmoothCircleFunction L a z := by
    filter_upwards [lpBoundedMulCLM_coeFn
      (continuous_ccmSmoothCircleFunction L a).measurable
      (norm_nonneg (ccmSmoothCircleContinuous L a))
      (fun x => ContinuousMap.norm_coe_le_norm (ccmSmoothCircleContinuous L a) x)
      (fourierLp (T := (L : ℝ)) 2 j),
      coeFn_fourierLp (T := (L : ℝ)) 2 j] with z h1 h2
    rw [show ccmSmoothCirclePhysicalMultiplier L a =
        lpBoundedMulCLM
          (continuous_ccmSmoothCircleFunction L a).measurable
          (norm_nonneg (ccmSmoothCircleContinuous L a))
          (fun x => ContinuousMap.norm_coe_le_norm
            (ccmSmoothCircleContinuous L a) x) by rfl]
    rw [h1, h2, mul_comm]
  rw [fourierCoeff_congr_ae hae,
    GaloisForLFunctions.fourierCoeff_fourier_mul]
  rw [ccmSmoothCircleFunction, fourierCoeff_liftIoc_eq]
  congr 1
  simp

theorem ccmSmoothCircleMultiplier_apply_basis
    (L : CCMCircleLength) (a : DeningerSmoothPeriodic (L : ℝ)) (j l : ℤ) :
    ccmSmoothCircleMultiplier L a (lpBasis ℤ j) l =
      deningerFourierCoeff (L : ℝ) (a : ℝ → ℂ) (l - j) := by
  change
    (fourierBasis (T := (L : ℝ))).repr
        (ccmSmoothCirclePhysicalMultiplier L a
          ((fourierBasis (T := (L : ℝ))).repr.toContinuousLinearEquiv.symm
            (lpBasis ℤ j))) l = _
  have hb : lpBasis ℤ j =
      (fourierBasis (T := (L : ℝ))).repr
        (fourierBasis (T := (L : ℝ)) j) := by
    rw [HilbertBasis.repr_self, lpBasis_apply]
  have hinv :
      (fourierBasis (T := (L : ℝ))).repr.toContinuousLinearEquiv.symm
          (lpBasis ℤ j) = fourierBasis (T := (L : ℝ)) j := by
    rw [hb]
    exact ContinuousLinearEquiv.symm_apply_apply _ _
  rw [hinv]
  rw [show fourierBasis (T := (L : ℝ)) j =
      (fourierLp (T := (L : ℝ)) 2 j : CCMCirclePhysicalL2 L) by
    rw [coe_fourierBasis]]
  rw [fourierBasis_repr,
    fourierCoeff_physicalMultiplier_fourierLp]
  exact deningerFourierCoeff_eq_fourierCoeffOn L (a : ℝ → ℂ) (l - j)

def ccmSmoothCircleDerivative (L : CCMCircleLength)
    (a : DeningerSmoothPeriodic (L : ℝ)) :
    DeningerSmoothPeriodic (L : ℝ) :=
  ⟨deriv (a : ℝ → ℂ),
    (contDiff_infty_iff_deriv.mp (deningerSmoothPeriodic_contDiff a)).2,
    deningerPeriodic_deriv (deningerSmoothPeriodic_periodic a)⟩

theorem ccmSmoothCircleDerivative_apply (L : CCMCircleLength)
    (a : DeningerSmoothPeriodic (L : ℝ)) (x : ℝ) :
    (ccmSmoothCircleDerivative L a : ℝ → ℂ) x =
      deriv (a : ℝ → ℂ) x := rfl

def ccmSmoothCircleCommutator (L : CCMCircleLength)
    (a : DeningerSmoothPeriodic (L : ℝ)) :
    DiagonalL2 ℤ →L[ℂ] DiagonalL2 ℤ :=
  (-Complex.I) • ccmSmoothCircleMultiplier L (ccmSmoothCircleDerivative L a)

theorem ccmSmoothCircleCommutator_apply_basis
    (L : CCMCircleLength) (a : DeningerSmoothPeriodic (L : ℝ)) (j l : ℤ) :
    ccmSmoothCircleCommutator L a (lpBasis ℤ j) l =
      (ccmCircleFrequency (L : ℝ) (l - j) : ℂ) *
        deningerFourierCoeff (L : ℝ) (a : ℝ → ℂ) (l - j) := by
  rw [ccmSmoothCircleCommutator, smul_apply]
  change
    -Complex.I *
        ccmSmoothCircleMultiplier L (ccmSmoothCircleDerivative L a)
          (lpBasis ℤ j) l = _
  rw [ccmSmoothCircleMultiplier_apply_basis]
  have hderiv : ∀ x, HasDerivAt (a : ℝ → ℂ)
      (deriv (a : ℝ → ℂ) x) x := by
    intro x
    exact (deningerSmoothPeriodic_contDiff a).differentiable (by simp) x |>.hasDerivAt
  have hcoeff := deningerFourierCoeff_deriv L.property.ne' hderiv
    ((contDiff_infty_iff_deriv.mp
      (deningerSmoothPeriodic_contDiff a)).2.continuous)
    (by simpa using deningerSmoothPeriodic_periodic a 0) (l - j)
  change -Complex.I * deningerFourierCoeff (L : ℝ)
      (deriv (a : ℝ → ℂ)) (l - j) = _
  rw [hcoeff]
  rw [ccmCircleFrequency]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  norm_num
  simp only [sub_eq_add_neg]

theorem ccmCircleFrequency_sub_add (L : CCMCircleLength) (l j : ℤ) :
    ccmCircleFrequency (L : ℝ) j + ccmCircleFrequency (L : ℝ) (l - j) =
      ccmCircleFrequency (L : ℝ) l := by
  rw [ccmCircleFrequency, ccmCircleFrequency, ccmCircleFrequency]
  push_cast
  ring

theorem ccmSmoothCircleMultiplier_basis_mem_domain
    (L : CCMCircleLength) (a : DeningerSmoothPeriodic (L : ℝ)) (j : ℤ) :
    ccmSmoothCircleMultiplier L a (lpBasis ℤ j) ∈
      (ccmCircleDirac (L : ℝ)).domain := by
  let y : DiagonalL2 ℤ :=
    (ccmCircleFrequency (L : ℝ) j : ℂ) •
        ccmSmoothCircleMultiplier L a (lpBasis ℤ j) +
      ccmSmoothCircleCommutator L a (lpBasis ℤ j)
  change Memℓp (fun l =>
    (ccmCircleFrequency (L : ℝ) l : ℂ) *
      ccmSmoothCircleMultiplier L a (lpBasis ℤ j) l) 2
  rw [show (fun l =>
      (ccmCircleFrequency (L : ℝ) l : ℂ) *
        ccmSmoothCircleMultiplier L a (lpBasis ℤ j) l) =
      fun l => y l by
    funext l
    rw [show ccmCircleFrequency (L : ℝ) l =
        ccmCircleFrequency (L : ℝ) j +
          ccmCircleFrequency (L : ℝ) (l - j) by
      exact (ccmCircleFrequency_sub_add L l j).symm]
    dsimp only [y]
    change
      ((ccmCircleFrequency (L : ℝ) j +
          ccmCircleFrequency (L : ℝ) (l - j) : ℝ) : ℂ) *
          ccmSmoothCircleMultiplier L a (lpBasis ℤ j) l =
        (ccmCircleFrequency (L : ℝ) j : ℂ) *
            ccmSmoothCircleMultiplier L a (lpBasis ℤ j) l +
          ccmSmoothCircleCommutator L a (lpBasis ℤ j) l
    rw [ccmSmoothCircleCommutator_apply_basis,
      ccmSmoothCircleMultiplier_apply_basis]
    push_cast
    ring]
  exact lp.memℓp y

theorem ccmCircleDirac_mul_smoothCircleMultiplier_basis
    (L : CCMCircleLength) (a : DeningerSmoothPeriodic (L : ℝ)) (j : ℤ) :
    ccmCircleDirac (L : ℝ)
        ⟨ccmSmoothCircleMultiplier L a (lpBasis ℤ j),
          ccmSmoothCircleMultiplier_basis_mem_domain L a j⟩ =
      ccmSmoothCircleMultiplier L a
          (ccmCircleDirac (L : ℝ)
            ⟨lpBasis ℤ j,
              lpBasis_mem_maximalRealDiagonalDomain
                (ccmCircleFrequency (L : ℝ)) j⟩) +
        ccmSmoothCircleCommutator L a (lpBasis ℤ j) := by
  rw [show ccmCircleDirac (L : ℝ)
      ⟨lpBasis ℤ j,
        lpBasis_mem_maximalRealDiagonalDomain
          (ccmCircleFrequency (L : ℝ)) j⟩ =
      (ccmCircleFrequency (L : ℝ) j : ℂ) • lpBasis ℤ j by
    exact deningerPhaseGenerator_apply_basis (ccmCircleFrequency (L : ℝ)) j]
  rw [map_smul]
  apply lp.ext
  funext l
  change
    (ccmCircleFrequency (L : ℝ) l : ℂ) *
        ccmSmoothCircleMultiplier L a (lpBasis ℤ j) l =
      (ccmCircleFrequency (L : ℝ) j : ℂ) *
          ccmSmoothCircleMultiplier L a (lpBasis ℤ j) l +
        ccmSmoothCircleCommutator L a (lpBasis ℤ j) l
  rw [ccmSmoothCircleCommutator_apply_basis,
    ccmSmoothCircleMultiplier_apply_basis]
  rw [show ccmCircleFrequency (L : ℝ) l =
      ccmCircleFrequency (L : ℝ) j +
        ccmCircleFrequency (L : ℝ) (l - j) by
    exact (ccmCircleFrequency_sub_add L l j).symm]
  push_cast
  ring

def ccmCircleFourierTruncate (S : Finset ℤ) (x : DiagonalL2 ℤ) :
    DiagonalL2 ℤ :=
  ∑ j ∈ S, x j • lpBasis ℤ j

theorem ccmCircleFourierTruncate_apply (S : Finset ℤ)
    (x : DiagonalL2 ℤ) (l : ℤ) :
    ccmCircleFourierTruncate S x l = if l ∈ S then x l else 0 := by
  rw [ccmCircleFourierTruncate]
  change (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 l)
      (∑ j ∈ S, x j • lpBasis ℤ j) = _
  rw [map_sum]
  simp_rw [map_smul]
  change (∑ j ∈ S, x j * (lpBasis ℤ j) l) = _
  simp_rw [lpBasis_apply, lp.single_apply]
  by_cases hl : l ∈ S
  · rw [if_pos hl, Finset.sum_eq_single l]
    · simp
    · intro b hb hbl
      rw [Pi.single_apply]
      split_ifs with h
      · exact (hbl h.symm).elim
      · simp
    · exact fun h => (h hl).elim
  · rw [if_neg hl]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Pi.single_apply]
    split_ifs with h
    · exact (hl (h ▸ hj)).elim
    · simp

theorem hasSum_ccmCircleFourierBasis (x : DiagonalL2 ℤ) :
    HasSum (fun j : ℤ => x j • lpBasis ℤ j) x := by
  convert lp.hasSum_single (p := 2) (by norm_num) x using 1
  funext j
  rw [lpBasis_apply, ← lp.single_smul]
  simp

theorem tendsto_ccmCircleFourierTruncate (x : DiagonalL2 ℤ) :
    Tendsto (fun S : Finset ℤ => ccmCircleFourierTruncate S x)
      atTop (𝓝 x) :=
  hasSum_ccmCircleFourierBasis x

theorem ccmCircleFourierTruncate_mem_domain
    (L : CCMCircleLength) (S : Finset ℤ) (x : DiagonalL2 ℤ) :
    ccmCircleFourierTruncate S x ∈ (ccmCircleDirac (L : ℝ)).domain := by
  rw [ccmCircleFourierTruncate]
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  exact lpBasis_mem_maximalRealDiagonalDomain
    (ccmCircleFrequency (L : ℝ)) j

@[simp] theorem ccmCircleDirac_apply (L : CCMCircleLength)
    (x : (ccmCircleDirac (L : ℝ)).domain) (l : ℤ) :
    ccmCircleDirac (L : ℝ) x l =
      (ccmCircleFrequency (L : ℝ) l : ℂ) * (x : DiagonalL2 ℤ) l := rfl

theorem ccmCircleDirac_fourierTruncate
    (L : CCMCircleLength) (S : Finset ℤ)
    (x : (ccmCircleDirac (L : ℝ)).domain) :
    ccmCircleDirac (L : ℝ)
        ⟨ccmCircleFourierTruncate S x,
          ccmCircleFourierTruncate_mem_domain L S x⟩ =
      ccmCircleFourierTruncate S (ccmCircleDirac (L : ℝ) x) := by
  apply lp.ext
  funext l
  change
    (ccmCircleFrequency (L : ℝ) l : ℂ) *
        ccmCircleFourierTruncate S x l =
      ccmCircleFourierTruncate S (ccmCircleDirac (L : ℝ) x) l
  rw [ccmCircleFourierTruncate_apply,
    ccmCircleFourierTruncate_apply]
  by_cases hl : l ∈ S
  · rw [if_pos hl, if_pos hl, ccmCircleDirac_apply]
  · rw [if_neg hl, if_neg hl, mul_zero]

theorem ccmCircleDirac_fourierTruncate_eq_sum
    (L : CCMCircleLength) (S : Finset ℤ) (x : DiagonalL2 ℤ) :
    ccmCircleDirac (L : ℝ)
        ⟨ccmCircleFourierTruncate S x,
          ccmCircleFourierTruncate_mem_domain L S x⟩ =
      ∑ j ∈ S, x j •
        ccmCircleDirac (L : ℝ)
          ⟨lpBasis ℤ j,
            lpBasis_mem_maximalRealDiagonalDomain
              (ccmCircleFrequency (L : ℝ)) j⟩ := by
  apply lp.ext
  funext l
  rw [ccmCircleDirac_apply, ccmCircleFourierTruncate_apply]
  change
    (ccmCircleFrequency (L : ℝ) l : ℂ) *
        (if l ∈ S then x l else 0) =
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 l)
        (∑ j ∈ S, x j •
          ccmCircleDirac (L : ℝ)
            ⟨lpBasis ℤ j,
              lpBasis_mem_maximalRealDiagonalDomain
                (ccmCircleFrequency (L : ℝ)) j⟩)
  have hDbasis (j : ℤ) :
      ccmCircleDirac (L : ℝ)
          ⟨lpBasis ℤ j,
            lpBasis_mem_maximalRealDiagonalDomain
              (ccmCircleFrequency (L : ℝ)) j⟩ =
        (ccmCircleFrequency (L : ℝ) j : ℂ) • lpBasis ℤ j :=
    deningerPhaseGenerator_apply_basis (ccmCircleFrequency (L : ℝ)) j
  rw [map_sum]
  by_cases hl : l ∈ S
  · rw [if_pos hl, Finset.sum_eq_single l]
    · rw [map_smul, hDbasis, map_smul]
      have hdiag : (lpBasis ℤ l) l = (1 : ℂ) := by
        rw [lpBasis_apply, lp.single_apply]
        simp
      change
        (ccmCircleFrequency (L : ℝ) l : ℂ) * x l =
          x l * ((ccmCircleFrequency (L : ℝ) l : ℂ) * (lpBasis ℤ l) l)
      rw [hdiag]
      ring
    · intro b hb hbl
      rw [map_smul, hDbasis, map_smul]
      have hbasis : (lpBasis ℤ b) l = (0 : ℂ) := by
        rw [lpBasis_apply]
        exact lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 b (1 : ℂ) hbl.symm
      change x b * ((ccmCircleFrequency (L : ℝ) b : ℂ) * (lpBasis ℤ b) l) = 0
      rw [hbasis, mul_zero, mul_zero]
    · exact fun h => (h hl).elim
  · rw [if_neg hl, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    rw [map_smul, hDbasis, map_smul]
    have hjl : j ≠ l := fun h => hl (h ▸ hj)
    have hbasis : (lpBasis ℤ j) l = (0 : ℂ) := by
      rw [lpBasis_apply]
      exact lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 j (1 : ℂ) hjl.symm
    change x j * ((ccmCircleFrequency (L : ℝ) j : ℂ) * (lpBasis ℤ j) l) = 0
    rw [hbasis, mul_zero, mul_zero]

theorem ccmSmoothCircleMultiplier_fourierTruncate_mem_domain
    (L : CCMCircleLength) (a : DeningerSmoothPeriodic (L : ℝ))
    (S : Finset ℤ) (x : DiagonalL2 ℤ) :
    ccmSmoothCircleMultiplier L a (ccmCircleFourierTruncate S x) ∈
      (ccmCircleDirac (L : ℝ)).domain := by
  rw [ccmCircleFourierTruncate, map_sum]
  apply Submodule.sum_mem
  intro j hj
  rw [map_smul]
  exact Submodule.smul_mem _ _
    (ccmSmoothCircleMultiplier_basis_mem_domain L a j)

theorem ccmCircleDirac_mul_smoothCircleMultiplier_fourierTruncate
    (L : CCMCircleLength) (a : DeningerSmoothPeriodic (L : ℝ))
    (S : Finset ℤ) (x : DiagonalL2 ℤ) :
    ccmCircleDirac (L : ℝ)
        ⟨ccmSmoothCircleMultiplier L a (ccmCircleFourierTruncate S x),
          ccmSmoothCircleMultiplier_fourierTruncate_mem_domain L a S x⟩ =
      ccmSmoothCircleMultiplier L a
          (ccmCircleDirac (L : ℝ)
            ⟨ccmCircleFourierTruncate S x,
              ccmCircleFourierTruncate_mem_domain L S x⟩) +
        ccmSmoothCircleCommutator L a (ccmCircleFourierTruncate S x) := by
  apply lp.ext
  funext l
  change
    (ccmCircleFrequency (L : ℝ) l : ℂ) *
        ccmSmoothCircleMultiplier L a (ccmCircleFourierTruncate S x) l =
      ccmSmoothCircleMultiplier L a
          (ccmCircleDirac (L : ℝ)
            ⟨ccmCircleFourierTruncate S x,
              ccmCircleFourierTruncate_mem_domain L S x⟩) l +
        ccmSmoothCircleCommutator L a (ccmCircleFourierTruncate S x) l
  rw [ccmCircleDirac_fourierTruncate_eq_sum]
  rw [ccmCircleFourierTruncate, map_sum, map_sum, map_sum]
  simp_rw [map_smul]
  change
    (ccmCircleFrequency (L : ℝ) l : ℂ) *
        (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 l)
          (∑ j ∈ S, x j •
            ccmSmoothCircleMultiplier L a (lpBasis ℤ j)) =
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 l)
          (∑ j ∈ S, x j •
            ccmSmoothCircleMultiplier L a
              (ccmCircleDirac (L : ℝ)
                ⟨lpBasis ℤ j,
                  lpBasis_mem_maximalRealDiagonalDomain
                    (ccmCircleFrequency (L : ℝ)) j⟩)) +
        (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 l)
          (∑ j ∈ S, x j •
            ccmSmoothCircleCommutator L a (lpBasis ℤ j))
  rw [map_sum, map_sum, map_sum]
  simp_rw [map_smul]
  simp only [smul_eq_mul]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hb := ccmCircleDirac_mul_smoothCircleMultiplier_basis L a j
  have hc := congrArg (fun z : DiagonalL2 ℤ => z l) hb
  change
    (ccmCircleFrequency (L : ℝ) l : ℂ) *
        ccmSmoothCircleMultiplier L a (lpBasis ℤ j) l =
      (ccmSmoothCircleMultiplier L a
          (ccmCircleDirac (L : ℝ)
            ⟨lpBasis ℤ j,
              lpBasis_mem_maximalRealDiagonalDomain
                (ccmCircleFrequency (L : ℝ)) j⟩)) l +
        ccmSmoothCircleCommutator L a (lpBasis ℤ j) l at hc
  change
    (ccmCircleFrequency (L : ℝ) l : ℂ) *
        (x j * ccmSmoothCircleMultiplier L a (lpBasis ℤ j) l) =
      x j * (ccmSmoothCircleMultiplier L a
          (ccmCircleDirac (L : ℝ)
            ⟨lpBasis ℤ j,
              lpBasis_mem_maximalRealDiagonalDomain
                (ccmCircleFrequency (L : ℝ)) j⟩)) l +
        x j * ccmSmoothCircleCommutator L a (lpBasis ℤ j) l
  calc
    (ccmCircleFrequency (L : ℝ) l : ℂ) *
        (x j * ccmSmoothCircleMultiplier L a (lpBasis ℤ j) l) =
      x j * ((ccmCircleFrequency (L : ℝ) l : ℂ) *
        ccmSmoothCircleMultiplier L a (lpBasis ℤ j) l) := by ring
    _ = x j * ((ccmSmoothCircleMultiplier L a
          (ccmCircleDirac (L : ℝ)
            ⟨lpBasis ℤ j,
              lpBasis_mem_maximalRealDiagonalDomain
                (ccmCircleFrequency (L : ℝ)) j⟩)) l +
        ccmSmoothCircleCommutator L a (lpBasis ℤ j) l) :=
      congrArg (fun z : ℂ => x j * z) hc
    _ = _ := by ring

private theorem ccmSmoothCircleMultiplier_graph_mem
    (L : CCMCircleLength) (a : DeningerSmoothPeriodic (L : ℝ))
    (x : (ccmCircleDirac (L : ℝ)).domain) :
    (ccmSmoothCircleMultiplier L a (x : DiagonalL2 ℤ),
        ccmSmoothCircleMultiplier L a (ccmCircleDirac (L : ℝ) x) +
          ccmSmoothCircleCommutator L a (x : DiagonalL2 ℤ)) ∈
      (ccmCircleDirac (L : ℝ)).graph := by
  let trunc : Finset ℤ → DiagonalL2 ℤ :=
    fun S => ccmCircleFourierTruncate S (x : DiagonalL2 ℤ)
  let dtrunc : Finset ℤ → DiagonalL2 ℤ := fun S =>
    ccmCircleDirac (L : ℝ)
      ⟨trunc S, ccmCircleFourierTruncate_mem_domain L S x⟩
  have htrunc : Tendsto trunc atTop (𝓝 (x : DiagonalL2 ℤ)) := by
    exact tendsto_ccmCircleFourierTruncate (x : DiagonalL2 ℤ)
  have hdtrunc : Tendsto dtrunc atTop
      (𝓝 (ccmCircleDirac (L : ℝ) x)) := by
    have h := tendsto_ccmCircleFourierTruncate
      (ccmCircleDirac (L : ℝ) x)
    have heq : dtrunc = fun S =>
        ccmCircleFourierTruncate S (ccmCircleDirac (L : ℝ) x) := by
      funext S
      exact ccmCircleDirac_fourierTruncate L S x
    rw [heq]
    exact h
  have hfirst : Tendsto
      (fun S => ccmSmoothCircleMultiplier L a (trunc S)) atTop
      (𝓝 (ccmSmoothCircleMultiplier L a (x : DiagonalL2 ℤ))) :=
    by
      change Tendsto (ccmSmoothCircleMultiplier L a ∘ trunc) atTop
        (𝓝 (ccmSmoothCircleMultiplier L a (x : DiagonalL2 ℤ)))
      exact ((ccmSmoothCircleMultiplier L a).continuous.tendsto
        (x : DiagonalL2 ℤ)).comp htrunc
  have hsecond : Tendsto
      (fun S =>
        ccmSmoothCircleMultiplier L a (dtrunc S) +
          ccmSmoothCircleCommutator L a (trunc S)) atTop
      (𝓝 (ccmSmoothCircleMultiplier L a (ccmCircleDirac (L : ℝ) x) +
        ccmSmoothCircleCommutator L a (x : DiagonalL2 ℤ))) :=
    by
      have hA := ((ccmSmoothCircleMultiplier L a).continuous.tendsto
        (ccmCircleDirac (L : ℝ) x)).comp hdtrunc
      have hB := ((ccmSmoothCircleCommutator L a).continuous.tendsto
        (x : DiagonalL2 ℤ)).comp htrunc
      have hab := hA.add hB
      change Tendsto
        (fun S =>
          ccmSmoothCircleMultiplier L a (dtrunc S) +
            ccmSmoothCircleCommutator L a (trunc S)) atTop
        (𝓝 (ccmSmoothCircleMultiplier L a (ccmCircleDirac (L : ℝ) x) +
          ccmSmoothCircleCommutator L a (x : DiagonalL2 ℤ))) at hab
      exact hab
  have hpair := hfirst.prodMk_nhds hsecond
  have hevent : ∀ᶠ S : Finset ℤ in atTop,
      (ccmSmoothCircleMultiplier L a (trunc S),
          ccmSmoothCircleMultiplier L a (dtrunc S) +
            ccmSmoothCircleCommutator L a (trunc S)) ∈
        (ccmCircleDirac (L : ℝ)).graph := by
    exact Filter.Eventually.of_forall fun S => by
      rw [LinearPMap.mem_graph_iff]
      refine ⟨⟨ccmSmoothCircleMultiplier L a (trunc S), ?_⟩, rfl, ?_⟩
      · exact ccmSmoothCircleMultiplier_fourierTruncate_mem_domain L a S x
      · exact ccmCircleDirac_mul_smoothCircleMultiplier_fourierTruncate L a S x
  have hclosed : IsClosed
      ((ccmCircleDirac (L : ℝ)).graph :
        Set (DiagonalL2 ℤ × DiagonalL2 ℤ)) :=
    (ccmCircleDirac_isSelfAdjoint (L : ℝ)).isClosed
  exact hclosed.mem_of_tendsto hpair hevent

/-- Every smooth circle multiplier preserves the maximal `H¹` domain of the circle Dirac
operator.  This is the graph-closed extension from the finite Fourier core. -/
theorem ccmSmoothCircleMultiplier_mem_domain
    (L : CCMCircleLength) (a : DeningerSmoothPeriodic (L : ℝ))
    (x : (ccmCircleDirac (L : ℝ)).domain) :
    ccmSmoothCircleMultiplier L a (x : DiagonalL2 ℤ) ∈
      (ccmCircleDirac (L : ℝ)).domain := by
  have hgraph := ccmSmoothCircleMultiplier_graph_mem L a x
  rw [LinearPMap.mem_graph_iff] at hgraph
  obtain ⟨y, hy, _⟩ := hgraph
  have hyval : (y : DiagonalL2 ℤ) =
      ccmSmoothCircleMultiplier L a (x : DiagonalL2 ℤ) := by
    simpa using hy
  rw [← hyval]
  exact y.property

/-- **Exact bounded commutator for the full smooth circle algebra.**  On the maximal domain,
`[D₀,Mₐ]` is the bounded operator `-i M_{a'}`. -/
theorem ccmCircleDirac_smooth_commutator
    (L : CCMCircleLength) (a : DeningerSmoothPeriodic (L : ℝ))
    (x : (ccmCircleDirac (L : ℝ)).domain) :
    ccmCircleDirac (L : ℝ)
        ⟨ccmSmoothCircleMultiplier L a (x : DiagonalL2 ℤ),
          ccmSmoothCircleMultiplier_mem_domain L a x⟩ =
      ccmSmoothCircleMultiplier L a (ccmCircleDirac (L : ℝ) x) +
        ccmSmoothCircleCommutator L a (x : DiagonalL2 ℤ) := by
  have hgraph := ccmSmoothCircleMultiplier_graph_mem L a x
  rw [LinearPMap.mem_graph_iff] at hgraph
  obtain ⟨y, hy, hout⟩ := hgraph
  have hy' : y =
      ⟨ccmSmoothCircleMultiplier L a (x : DiagonalL2 ℤ),
        ccmSmoothCircleMultiplier_mem_domain L a x⟩ := Subtype.ext hy
  rw [← hy', hout]

/-- Bounded commutator of a smooth circle multiplier with the exact finite packet compression. -/
def ccmConnesConsaniSmoothCommutator
    (L : CCMCircleLength) {k : ℕ} (v : CCMCircleSmoothPacket L k)
    (a : DeningerSmoothPeriodic (L : ℝ)) :
    DiagonalL2 ℤ →L[ℂ] DiagonalL2 ℤ :=
  ccmSmoothCircleCommutator L a +
    (smoothPacketCompressionPerturbation (ccmCircleDirac (L : ℝ)) v).comp
      (ccmSmoothCircleMultiplier L a) -
    (ccmSmoothCircleMultiplier L a).comp
      (smoothPacketCompressionPerturbation (ccmCircleDirac (L : ℝ)) v)

theorem ccmSmoothCircleMultiplier_mem_compressedDomain
    (L : CCMCircleLength) {k : ℕ} (v : CCMCircleSmoothPacket L k)
    (a : DeningerSmoothPeriodic (L : ℝ))
    (x : (ccmConnesConsaniCompressedDirac L v).domain) :
    ccmSmoothCircleMultiplier L a (x : DiagonalL2 ℤ) ∈
      (ccmConnesConsaniCompressedDirac L v).domain := by
  let xD : (ccmCircleDirac (L : ℝ)).domain :=
    ⟨(x : DiagonalL2 ℤ), by
      simpa only [ccmConnesConsaniCompressedDirac,
        smoothPacketCompressedOperator, boundedShift_domain] using x.property⟩
  simpa only [ccmConnesConsaniCompressedDirac,
    smoothPacketCompressedOperator, boundedShift_domain] using
      ccmSmoothCircleMultiplier_mem_domain L a xD

/-- **Full Connes--Consani `propDpert`, bounded-commutator clause.**

For every smooth function on the circle and every finite packet compression, the represented
function preserves the compressed Dirac domain and its commutator is the explicit bounded operator
`-iM_{a'} + [K,M_a]`, where `K` is the finite-rank compression perturbation. -/
theorem connesConsani_propDpert_boundedCommutator
    (L : CCMCircleLength) {k : ℕ} (v : CCMCircleSmoothPacket L k)
    (a : DeningerSmoothPeriodic (L : ℝ))
    (x : (ccmConnesConsaniCompressedDirac L v).domain) :
    ccmConnesConsaniCompressedDirac L v
        ⟨ccmSmoothCircleMultiplier L a (x : DiagonalL2 ℤ),
          ccmSmoothCircleMultiplier_mem_compressedDomain L v a x⟩ =
      ccmSmoothCircleMultiplier L a (ccmConnesConsaniCompressedDirac L v x) +
        ccmConnesConsaniSmoothCommutator L v a (x : DiagonalL2 ℤ) := by
  let K : DiagonalL2 ℤ →L[ℂ] DiagonalL2 ℤ :=
    smoothPacketCompressionPerturbation (ccmCircleDirac (L : ℝ)) v
  let xD : (ccmCircleDirac (L : ℝ)).domain :=
    ⟨(x : DiagonalL2 ℤ), by
      simpa only [ccmConnesConsaniCompressedDirac,
        smoothPacketCompressedOperator, boundedShift_domain] using x.property⟩
  have hcomm := ccmCircleDirac_smooth_commutator L a xD
  change
    boundedShift (ccmCircleDirac (L : ℝ)) K
        ⟨ccmSmoothCircleMultiplier L a (x : DiagonalL2 ℤ),
          ccmSmoothCircleMultiplier_mem_compressedDomain L v a x⟩ =
      ccmSmoothCircleMultiplier L a
          (boundedShift (ccmCircleDirac (L : ℝ)) K x) +
        (ccmSmoothCircleCommutator L a + K.comp (ccmSmoothCircleMultiplier L a) -
          (ccmSmoothCircleMultiplier L a).comp K) (x : DiagonalL2 ℤ)
  rw [boundedShift_apply, boundedShift_apply]
  change
    ccmCircleDirac (L : ℝ)
        ⟨ccmSmoothCircleMultiplier L a (x : DiagonalL2 ℤ),
          ccmSmoothCircleMultiplier_mem_domain L a xD⟩ +
        K (ccmSmoothCircleMultiplier L a (x : DiagonalL2 ℤ)) =
      ccmSmoothCircleMultiplier L a
          (ccmCircleDirac (L : ℝ) xD + K (x : DiagonalL2 ℤ)) +
        (ccmSmoothCircleCommutator L a + K.comp (ccmSmoothCircleMultiplier L a) -
          (ccmSmoothCircleMultiplier L a).comp K) (x : DiagonalL2 ℤ)
  rw [hcomm, map_add]
  simp only [_root_.add_apply, _root_.sub_apply,
    ContinuousLinearMap.comp_apply]
  abel

end
end RHTower
