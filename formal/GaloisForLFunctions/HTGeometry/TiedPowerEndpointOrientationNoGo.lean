import GaloisForLFunctions.HTGeometry.TiedPowerSectorOrientationNoGo

/-!
# Endpoint-sized tied-power orientation no-go

Positive rescaling places both opposite-orientation sources inside both exact corpus atom bounds:
the narrow `85/84` sector and the radius `2/41`.  Their current positive singular Hankel face
still agrees, their monic remainders still have opposite signs, and inherited tied-power Möbius
transport remains exact.
-/

open Matrix Polynomial
open scoped ComplexConjugate

namespace HTGeometry

noncomputable section

def tiedPowerScaleNodes (a : ℝ) (nodes : Fin 4 → ℂ) (i : Fin 4) : ℂ :=
  (a : ℂ) * nodes i

theorem tiedPowerMoment_scale (a : ℝ) (nodes : Fin 4 → ℂ) (k : ℕ) :
    tiedPowerMoment (tiedPowerScaleNodes a nodes) k =
      a ^ (k + 1) * tiedPowerMoment nodes k := by
  rw [tiedPowerMoment, tiedPowerMoment]
  simp_rw [tiedPowerScaleNodes, mul_pow]
  rw [← Finset.mul_sum]
  have hpow : (a : ℂ) ^ (k + 1) = ((a ^ (k + 1) : ℝ) : ℂ) := by
    exact (map_pow (algebraMap ℝ ℂ) a (k + 1)).symm
  have hre : ((a : ℂ) ^ (k + 1)).re = a ^ (k + 1) := by rw [hpow]; rfl
  have him : ((a : ℂ) ^ (k + 1)).im = 0 := by rw [hpow]; rfl
  rw [Complex.mul_re, hre, him, zero_mul, sub_zero]

def tiedPowerEndpointPositiveNodes : Fin 4 → ℂ :=
  tiedPowerScaleNodes (1 / 256) tiedPowerPositiveNodes

def tiedPowerEndpointNegativeNodes : Fin 4 → ℂ :=
  tiedPowerScaleNodes (1 / 256) tiedPowerNegativeNodes

theorem tiedPowerEndpointPositiveNodes_geometry :
    ∀ i, 0 < (tiedPowerEndpointPositiveNodes i).re ∧
      (84 : ℝ) ^ (2 : ℕ) * Complex.normSq (tiedPowerEndpointPositiveNodes i) <
        (85 : ℝ) ^ (2 : ℕ) * (tiedPowerEndpointPositiveNodes i).re ^ (2 : ℕ) ∧
      (41 : ℝ) ^ (2 : ℕ) * Complex.normSq (tiedPowerEndpointPositiveNodes i) < 4 := by
  intro i
  fin_cases i <;>
    norm_num [tiedPowerEndpointPositiveNodes, tiedPowerScaleNodes,
      tiedPowerPositiveNodes, Complex.normSq_apply]

theorem tiedPowerEndpointNegativeNodes_geometry :
    ∀ i, 0 < (tiedPowerEndpointNegativeNodes i).re ∧
      (84 : ℝ) ^ (2 : ℕ) * Complex.normSq (tiedPowerEndpointNegativeNodes i) <
        (85 : ℝ) ^ (2 : ℕ) * (tiedPowerEndpointNegativeNodes i).re ^ (2 : ℕ) ∧
      (41 : ℝ) ^ (2 : ℕ) * Complex.normSq (tiedPowerEndpointNegativeNodes i) < 4 := by
  intro i
  fin_cases i <;>
    norm_num [tiedPowerEndpointNegativeNodes, tiedPowerScaleNodes,
      tiedPowerNegativeNodes, Complex.normSq_apply]

theorem tiedPowerEndpointPositiveNodes_conjugationClosed :
    ∀ i, ∃ j, conj (tiedPowerEndpointPositiveNodes i) = tiedPowerEndpointPositiveNodes j := by
  intro i
  obtain ⟨j, hj⟩ := tiedPowerPositiveNodes_conjugationClosed i
  refine ⟨j, ?_⟩
  rw [tiedPowerEndpointPositiveNodes, tiedPowerScaleNodes, map_mul,
    Complex.conj_ofReal, hj]
  rfl

theorem tiedPowerEndpointNegativeNodes_conjugationClosed :
    ∀ i, ∃ j, conj (tiedPowerEndpointNegativeNodes i) = tiedPowerEndpointNegativeNodes j := by
  intro i
  obtain ⟨j, hj⟩ := tiedPowerNegativeNodes_conjugationClosed i
  refine ⟨j, ?_⟩
  rw [tiedPowerEndpointNegativeNodes, tiedPowerScaleNodes, map_mul,
    Complex.conj_ofReal, hj]
  rfl

@[simp] theorem tiedPowerEndpointPositiveMoment_zero :
    tiedPowerMoment tiedPowerEndpointPositiveNodes 0 = 5 / 32 := by
  rw [tiedPowerEndpointPositiveNodes, tiedPowerMoment_scale,
    tiedPowerPositiveMoment_zero]
  norm_num

@[simp] theorem tiedPowerEndpointPositiveMoment_one :
    tiedPowerMoment tiedPowerEndpointPositiveNodes 1 = 25 / 4096 := by
  rw [tiedPowerEndpointPositiveNodes, tiedPowerMoment_scale,
    tiedPowerPositiveMoment_one]
  norm_num

@[simp] theorem tiedPowerEndpointPositiveMoment_two :
    tiedPowerMoment tiedPowerEndpointPositiveNodes 2 = 125 / 524288 := by
  rw [tiedPowerEndpointPositiveNodes, tiedPowerMoment_scale,
    tiedPowerPositiveMoment_two]
  norm_num

@[simp] theorem tiedPowerEndpointPositiveMoment_three :
    tiedPowerMoment tiedPowerEndpointPositiveNodes 3 = 10001 / 1073741824 := by
  rw [tiedPowerEndpointPositiveNodes, tiedPowerMoment_scale,
    tiedPowerPositiveMoment_three]
  norm_num

@[simp] theorem tiedPowerEndpointNegativeMoment_zero :
    tiedPowerMoment tiedPowerEndpointNegativeNodes 0 = 5 / 32 := by
  rw [tiedPowerEndpointNegativeNodes, tiedPowerMoment_scale,
    tiedPowerNegativeMoment_zero]
  norm_num

@[simp] theorem tiedPowerEndpointNegativeMoment_one :
    tiedPowerMoment tiedPowerEndpointNegativeNodes 1 = 25 / 4096 := by
  rw [tiedPowerEndpointNegativeNodes, tiedPowerMoment_scale,
    tiedPowerNegativeMoment_one]
  norm_num

@[simp] theorem tiedPowerEndpointNegativeMoment_two :
    tiedPowerMoment tiedPowerEndpointNegativeNodes 2 = 125 / 524288 := by
  rw [tiedPowerEndpointNegativeNodes, tiedPowerMoment_scale,
    tiedPowerNegativeMoment_two]
  norm_num

@[simp] theorem tiedPowerEndpointNegativeMoment_three :
    tiedPowerMoment tiedPowerEndpointNegativeNodes 3 = 2499 / 268435456 := by
  rw [tiedPowerEndpointNegativeNodes, tiedPowerMoment_scale,
    tiedPowerNegativeMoment_three]
  norm_num

def tiedPowerEndpointNoGoKernel : Fin 2 → ℝ := ![-5 / 128, 1]

theorem tiedPowerEndpointPositive_head_posDef :
    (momentHankelMatrix (tiedPowerMoment tiedPowerEndpointPositiveNodes) 1).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · exact momentHankelMatrix_isHermitian _ _
  · intro x hx
    have hx0 : x 0 ≠ 0 := by
      intro hx0
      apply hx
      funext i
      fin_cases i
      exact hx0
    simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_one,
      momentHankelMatrix]
    norm_num only [Fin.val_zero, zero_add]
    rw [tiedPowerEndpointPositiveMoment_zero]
    nlinarith [sq_pos_of_ne_zero hx0]

theorem tiedPowerEndpointPositive_kernel :
    momentHankelMatrix (tiedPowerMoment tiedPowerEndpointPositiveNodes) 2 *ᵥ
      tiedPowerEndpointNoGoKernel = 0 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, momentHankelMatrix, tiedPowerEndpointNoGoKernel] <;>
    norm_num

theorem tiedPowerEndpointNegative_kernel :
    momentHankelMatrix (tiedPowerMoment tiedPowerEndpointNegativeNodes) 2 *ᵥ
      tiedPowerEndpointNoGoKernel = 0 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, momentHankelMatrix, tiedPowerEndpointNoGoKernel] <;>
    norm_num

theorem tiedPowerEndpoint_sameFace :
    momentHankelMatrix (tiedPowerMoment tiedPowerEndpointPositiveNodes) 2 =
      momentHankelMatrix (tiedPowerMoment tiedPowerEndpointNegativeNodes) 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [momentHankelMatrix]

theorem tiedPowerEndpointPositive_monicRemainder :
    finiteHankelBoundaryMonicRemainder
      (tiedPowerMoment tiedPowerEndpointPositiveNodes) tiedPowerEndpointNoGoKernel =
        1 / 1073741824 := by
  have hraw : finiteHankelNullPolynomial tiedPowerEndpointNoGoKernel = X - C (5 / 128) := by
    rw [finiteHankelNullPolynomial, Polynomial.ofFn_eq_sum_monomial, Fin.sum_univ_two]
    simp [tiedPowerEndpointNoGoKernel, monomial_one_right_eq_X_pow]
    rw [show (-5 / 128 : ℝ) = -(5 / 128) by ring, map_neg]
    ring
  have hmonic : finiteHankelNullMonicPolynomial tiedPowerEndpointNoGoKernel = X - C (5 / 128) := by
    rw [finiteHankelNullMonicPolynomial, hraw]
    simp
  rw [finiteHankelBoundaryMonicRemainder, hmonic]
  norm_num only [Nat.reduceAdd]
  have hpoly : (X : Polynomial ℝ) ^ (2 : ℕ) * (X - C (5 / 128)) =
      X ^ (3 : ℕ) - C (5 / 128) * X ^ (2 : ℕ) := by ring
  calc
    momentFunctional (tiedPowerMoment tiedPowerEndpointPositiveNodes)
        (X ^ (2 : ℕ) * (X - C (5 / 128))) =
      momentFunctional (tiedPowerMoment tiedPowerEndpointPositiveNodes)
        (X ^ (3 : ℕ) - C (5 / 128) * X ^ (2 : ℕ)) := congrArg _ hpoly
    _ = 1 / 1073741824 := by
      rw [sub_eq_add_neg, momentFunctional_add]
      rw [show -((C (5 / 128) * X ^ (2 : ℕ) : Polynomial ℝ)) =
          (-1 : ℝ) • (C (5 / 128) * X ^ (2 : ℕ) : Polynomial ℝ) by rw [neg_one_smul],
        momentFunctional_smul, momentFunctional_X_pow]
      rw [show (C (5 / 128) * X ^ (2 : ℕ) : Polynomial ℝ) =
          (5 / 128 : ℝ) • X ^ (2 : ℕ) by rw [Polynomial.smul_eq_C_mul],
        momentFunctional_smul, momentFunctional_X_pow]
      rw [tiedPowerEndpointPositiveMoment_three, tiedPowerEndpointPositiveMoment_two]
      norm_num

theorem tiedPowerEndpointNegative_monicRemainder :
    finiteHankelBoundaryMonicRemainder
      (tiedPowerMoment tiedPowerEndpointNegativeNodes) tiedPowerEndpointNoGoKernel =
        -(1 / 268435456) := by
  have hraw : finiteHankelNullPolynomial tiedPowerEndpointNoGoKernel = X - C (5 / 128) := by
    rw [finiteHankelNullPolynomial, Polynomial.ofFn_eq_sum_monomial, Fin.sum_univ_two]
    simp [tiedPowerEndpointNoGoKernel, monomial_one_right_eq_X_pow]
    rw [show (-5 / 128 : ℝ) = -(5 / 128) by ring, map_neg]
    ring
  have hmonic : finiteHankelNullMonicPolynomial tiedPowerEndpointNoGoKernel = X - C (5 / 128) := by
    rw [finiteHankelNullMonicPolynomial, hraw]
    simp
  rw [finiteHankelBoundaryMonicRemainder, hmonic]
  norm_num only [Nat.reduceAdd]
  have hpoly : (X : Polynomial ℝ) ^ (2 : ℕ) * (X - C (5 / 128)) =
      X ^ (3 : ℕ) - C (5 / 128) * X ^ (2 : ℕ) := by ring
  calc
    momentFunctional (tiedPowerMoment tiedPowerEndpointNegativeNodes)
        (X ^ (2 : ℕ) * (X - C (5 / 128))) =
      momentFunctional (tiedPowerMoment tiedPowerEndpointNegativeNodes)
        (X ^ (3 : ℕ) - C (5 / 128) * X ^ (2 : ℕ)) := congrArg _ hpoly
    _ = -(1 / 268435456) := by
      rw [sub_eq_add_neg, momentFunctional_add]
      rw [show -((C (5 / 128) * X ^ (2 : ℕ) : Polynomial ℝ)) =
          (-1 : ℝ) • (C (5 / 128) * X ^ (2 : ℕ) : Polynomial ℝ) by rw [neg_one_smul],
        momentFunctional_smul, momentFunctional_X_pow]
      rw [show (C (5 / 128) * X ^ (2 : ℕ) : Polynomial ℝ) =
          (5 / 128 : ℝ) • X ^ (2 : ℕ) by rw [Polynomial.smul_eq_C_mul],
        momentFunctional_smul, momentFunctional_X_pow]
      rw [tiedPowerEndpointNegativeMoment_three, tiedPowerEndpointNegativeMoment_two]
      norm_num

/-- **Endpoint-complete local-source no-go.**  Both conjugation-stable tied-power sources satisfy
the strict corpus sector and radius bounds, evolve by exact Möbius power transport, and share one
positive singular current Hankel face, but their first unseen projective remainders have opposite
signs.  Finite local spectral geometry plus transport therefore cannot supply Xi orientation. -/
theorem tiedPowerEndpointOrientationNoGo :
    (∀ i, ∃ j, conj (tiedPowerEndpointPositiveNodes i) = tiedPowerEndpointPositiveNodes j) ∧
    (∀ i, ∃ j, conj (tiedPowerEndpointNegativeNodes i) = tiedPowerEndpointNegativeNodes j) ∧
    (∀ i, 0 < (tiedPowerEndpointPositiveNodes i).re ∧
      (84 : ℝ) ^ (2 : ℕ) * Complex.normSq (tiedPowerEndpointPositiveNodes i) <
        (85 : ℝ) ^ (2 : ℕ) * (tiedPowerEndpointPositiveNodes i).re ^ (2 : ℕ) ∧
      (41 : ℝ) ^ (2 : ℕ) * Complex.normSq (tiedPowerEndpointPositiveNodes i) < 4) ∧
    (∀ i, 0 < (tiedPowerEndpointNegativeNodes i).re ∧
      (84 : ℝ) ^ (2 : ℕ) * Complex.normSq (tiedPowerEndpointNegativeNodes i) <
        (85 : ℝ) ^ (2 : ℕ) * (tiedPowerEndpointNegativeNodes i).re ^ (2 : ℕ) ∧
      (41 : ℝ) ^ (2 : ℕ) * Complex.normSq (tiedPowerEndpointNegativeNodes i) < 4) ∧
    momentHankelMatrix (tiedPowerMoment tiedPowerEndpointPositiveNodes) 2 =
      momentHankelMatrix (tiedPowerMoment tiedPowerEndpointNegativeNodes) 2 ∧
    (momentHankelMatrix (tiedPowerMoment tiedPowerEndpointPositiveNodes) 1).PosDef ∧
    momentHankelMatrix (tiedPowerMoment tiedPowerEndpointPositiveNodes) 2 *ᵥ
      tiedPowerEndpointNoGoKernel = 0 ∧
    momentHankelMatrix (tiedPowerMoment tiedPowerEndpointNegativeNodes) 2 *ᵥ
      tiedPowerEndpointNoGoKernel = 0 ∧
    finiteHankelBoundaryMonicRemainder
      (tiedPowerMoment tiedPowerEndpointPositiveNodes) tiedPowerEndpointNoGoKernel =
        1 / 1073741824 ∧
    finiteHankelBoundaryMonicRemainder
      (tiedPowerMoment tiedPowerEndpointNegativeNodes) tiedPowerEndpointNoGoKernel =
        -(1 / 268435456) ∧
    (∀ k, HasDerivAt (tiedPowerMobiusTrajectory tiedPowerEndpointPositiveNodes k)
      (-((k + 1 : ℕ) : ℂ) * ∑ i, tiedPowerEndpointPositiveNodes i ^ (k + 2)) 0) ∧
    (∀ k, HasDerivAt (tiedPowerMobiusTrajectory tiedPowerEndpointNegativeNodes k)
      (-((k + 1 : ℕ) : ℂ) * ∑ i, tiedPowerEndpointNegativeNodes i ^ (k + 2)) 0) := by
  exact ⟨tiedPowerEndpointPositiveNodes_conjugationClosed,
    tiedPowerEndpointNegativeNodes_conjugationClosed,
    tiedPowerEndpointPositiveNodes_geometry,
    tiedPowerEndpointNegativeNodes_geometry,
    tiedPowerEndpoint_sameFace,
    tiedPowerEndpointPositive_head_posDef,
    tiedPowerEndpointPositive_kernel,
    tiedPowerEndpointNegative_kernel,
    tiedPowerEndpointPositive_monicRemainder,
    tiedPowerEndpointNegative_monicRemainder,
    fun k => tiedPowerMobiusTrajectory_hasDerivAt tiedPowerEndpointPositiveNodes k,
    fun k => tiedPowerMobiusTrajectory_hasDerivAt tiedPowerEndpointNegativeNodes k⟩

end
end HTGeometry
