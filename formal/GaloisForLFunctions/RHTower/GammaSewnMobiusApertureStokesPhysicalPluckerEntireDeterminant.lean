import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesPhysicalOverlapPluckerFaithfulness
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantEigenvalueLimit

/-!
# Source-native physical Pluecker entire determinant

The physical-overlap Pluecker operator already carries the literal prime/depth sewing, source
weights, positivity, Schatten-one summability, and faithfulness.  This file passes that operator to
the coordinate Hilbert--Schmidt determinant without changing its normalization.

The resulting finite principal determinants are strictly stable: positivity makes every compressed
eigenvalue nonnegative, while faithfulness rules out zero compression energy.  Hence every zero of
`det2 (1 - z T_s)` is positive real.  Reflection gives the signed-permutation convention with every
zero strictly negative real.  The finite reflected determinants converge locally uniformly to an
entire function, and the same strict zero-ray law holds for the cofinal limit.

This closes the source-normalized stable-determinant existence gate.  It does not identify the
determinant with completed Xi; that arithmetic identification remains the RH-bearing obstruction.
-/

open Real Set Filter Topology Matrix
open scoped BigOperators InnerProductSpace ComplexOrder

noncomputable section

namespace RHTower.HedenmalmThetaSource

open HilbertSchmidt

/-- Schatten-one summability gives the Hilbert--Schmidt input required by the coordinate determinant. -/
theorem gammaSewnCriticalPhysicalPluckerSpectralOperator_isHilbertSchmidt :
    gammaSewnCriticalPhysicalPluckerSpectralOperator.IsHilbertSchmidt := by
  obtain ⟨S, U, _hS, hU, hfac⟩ :=
    gammaSewnCriticalPhysicalPluckerSpectralOperator_memSchattenClass_one.one_isTraceClass
  rw [hfac]
  exact hU.comp_left S

/-- Coordinate kernel of the literal physical-overlap Pluecker operator. -/
def gammaSewnCriticalPhysicalPluckerKernel :
    GammaSewnCriticalPhysicalPluckerIndex ×
      GammaSewnCriticalPhysicalPluckerIndex → ℂ :=
  HilbertSchmidt.matrixOf gammaSewnCriticalPhysicalPluckerSpectralOperator

theorem gammaSewnCriticalPhysicalPluckerKernel_isHS :
    HilbertSchmidt.IsHS gammaSewnCriticalPhysicalPluckerKernel :=
  HilbertSchmidt.isHS_matrixOf
    gammaSewnCriticalPhysicalPluckerSpectralOperator_isHilbertSchmidt

/-- The coordinate kernel recovers the physical source operator exactly. -/
theorem gammaSewnCriticalPhysicalPluckerKernel_toOperator :
    HilbertSchmidt.toOperator gammaSewnCriticalPhysicalPluckerKernel_isHS =
      gammaSewnCriticalPhysicalPluckerSpectralOperator :=
  HilbertSchmidt.toOperator_matrixOf
    gammaSewnCriticalPhysicalPluckerSpectralOperator_isHilbertSchmidt

/-- On a zero-extended finite vector, double coordinate truncation does not change the quadratic
form.  The right truncation is invisible because the vector is supported on the block; the left
truncation is invisible because the first slot of the inner product has the same support. -/
theorem inner_liftBlockLp_physicalPlucker_toOperator_truncKernel_eq
    (s : Finset GammaSewnCriticalPhysicalPluckerIndex) (v : ↥s → ℂ) :
    inner ℂ (HilbertSchmidt.liftBlockLp v)
        (HilbertSchmidt.toOperator
          (HilbertSchmidt.isHS_truncKernel
            gammaSewnCriticalPhysicalPluckerKernel_isHS s)
          (HilbertSchmidt.liftBlockLp v)) =
      inner ℂ (HilbertSchmidt.liftBlockLp v)
        (HilbertSchmidt.toOperator gammaSewnCriticalPhysicalPluckerKernel_isHS
          (HilbertSchmidt.liftBlockLp v)) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  by_cases hi : i ∈ s
  · congr 1
    rw [HilbertSchmidt.toOperator_apply, HilbertSchmidt.toOperator_apply]
    apply tsum_congr
    intro j
    by_cases hj : j ∈ s
    · simp [HilbertSchmidt.truncKernel, hi, hj]
    · rw [HilbertSchmidt.liftBlockLp_apply,
        HilbertSchmidt.liftBlock_apply_of_notMem v hj]
      simp
  · rw [HilbertSchmidt.liftBlockLp_apply,
      HilbertSchmidt.liftBlock_apply_of_notMem v hi]
    simp

/-- Entire regularized determinant `det2 (1 - z T)` of the physical-overlap source operator. -/
def gammaSewnCriticalPhysicalPluckerEntireDet2 : ℂ → ℂ :=
  GaloisForLFunctions.HTGeometry.entireDet2
    gammaSewnCriticalPhysicalPluckerKernel

/-- Signed-permutation stability convention: reflect the determinant variable. -/
def gammaSewnCriticalPhysicalPluckerStableEntireDet2 (u : ℂ) : ℂ :=
  gammaSewnCriticalPhysicalPluckerEntireDet2 (-u)

/-- Finite principal source determinant before reflection. -/
def gammaSewnCriticalPhysicalPluckerFiniteDet2
    (s : Finset GammaSewnCriticalPhysicalPluckerIndex) (z : ℂ) : ℂ :=
  GaloisForLFunctions.HTGeometry.finiteDet2
    (-(HilbertSchmidt.blockMatrix gammaSewnCriticalPhysicalPluckerKernel s)) z

/-- Finite principal determinant in the negative-real-zero stability convention. -/
def gammaSewnCriticalPhysicalPluckerStableFiniteDet2
    (s : Finset GammaSewnCriticalPhysicalPluckerIndex) (u : ℂ) : ℂ :=
  gammaSewnCriticalPhysicalPluckerFiniteDet2 s (-u)

theorem differentiable_gammaSewnCriticalPhysicalPluckerEntireDet2 :
    Differentiable ℂ gammaSewnCriticalPhysicalPluckerEntireDet2 :=
  GaloisForLFunctions.HTGeometry.differentiable_entireDet2
    gammaSewnCriticalPhysicalPluckerKernel_isHS

theorem differentiable_gammaSewnCriticalPhysicalPluckerStableEntireDet2 :
    Differentiable ℂ gammaSewnCriticalPhysicalPluckerStableEntireDet2 := by
  exact differentiable_gammaSewnCriticalPhysicalPluckerEntireDet2.comp differentiable_neg

/-- Every zero of the cofinal unreflected source determinant is strictly positive real. -/
theorem gammaSewnCriticalPhysicalPluckerEntireDet2_zero_pos {z : ℂ}
    (hz : gammaSewnCriticalPhysicalPluckerEntireDet2 z = 0) : 0 < z := by
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    have hone :=
      (GaloisForLFunctions.HTGeometry.isRegularizedDet_entireDet2
        gammaSewnCriticalPhysicalPluckerKernel_isHS).eq_one_at_zero
    exact one_ne_zero (hone.symm.trans hz)
  obtain ⟨w, hw0, hw⟩ :=
    GaloisForLFunctions.HTGeometry.exists_eigenvector_of_entireDet2_eq_zero
      gammaSewnCriticalPhysicalPluckerKernel_isHS hz0 hz
  rw [gammaSewnCriticalPhysicalPluckerKernel_toOperator] at hw
  have hnonneg :=
    gammaSewnCriticalPhysicalPluckerSpectralOperator_isPositive.inner_nonneg_right w
  rw [hw, inner_smul_right, inner_self_eq_norm_sq_to_K] at hnonneg
  have hnormpos : 0 < ‖w‖ ^ (2 : ℕ) := sq_pos_of_pos (norm_pos_iff.mpr hw0)
  have hprodne : (((‖w‖ ^ (2 : ℕ) : ℝ) : ℂ) * z⁻¹) ≠ 0 := by
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hnormpos.ne') (inv_ne_zero hz0)
  have hprodpos : 0 < (((‖w‖ ^ (2 : ℕ) : ℝ) : ℂ) * z⁻¹) := by
    apply lt_of_le_of_ne
    · simpa [mul_comm] using hnonneg
    · exact hprodne.symm
  rcases (RCLike.ofReal_mul_pos_iff (K := ℂ) (‖w‖ ^ (2 : ℕ)) z⁻¹).mp hprodpos with
      hneg | hpos
  · exact (not_lt_of_ge hnormpos.le hneg.1).elim
  · exact RCLike.inv_pos.mp hpos.2

theorem gammaSewnCriticalPhysicalPluckerEntireDet2_zero_re_im {z : ℂ}
    (hz : gammaSewnCriticalPhysicalPluckerEntireDet2 z = 0) :
    0 < z.re ∧ z.im = 0 :=
  (RCLike.pos_iff (K := ℂ)).mp
    (gammaSewnCriticalPhysicalPluckerEntireDet2_zero_pos hz)

/-- Cofinal SP-E determinant has only strictly negative-real zeros. -/
theorem gammaSewnCriticalPhysicalPluckerStableEntireDet2_zero_neg {u : ℂ}
    (hu : gammaSewnCriticalPhysicalPluckerStableEntireDet2 u = 0) : u < 0 := by
  exact neg_pos.mp (gammaSewnCriticalPhysicalPluckerEntireDet2_zero_pos hu)

theorem gammaSewnCriticalPhysicalPluckerStableEntireDet2_zero_re_im {u : ℂ}
    (hu : gammaSewnCriticalPhysicalPluckerStableEntireDet2 u = 0) :
    u.re < 0 ∧ u.im = 0 :=
  (RCLike.neg_iff (K := ℂ)).mp
    (gammaSewnCriticalPhysicalPluckerStableEntireDet2_zero_neg hu)

/-- Every finite principal source determinant is already strictly positive-real-rooted.  Positivity
supplies nonnegative compression energy; global faithfulness makes it strict on every nonzero
finite vector. -/
theorem gammaSewnCriticalPhysicalPluckerFiniteDet2_zero_pos
    (s : Finset GammaSewnCriticalPhysicalPluckerIndex) {z : ℂ}
    (hz : gammaSewnCriticalPhysicalPluckerFiniteDet2 s z = 0) : 0 < z := by
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    simp [gammaSewnCriticalPhysicalPluckerFiniteDet2,
      GaloisForLFunctions.HTGeometry.finiteDet2] at hz
  obtain ⟨v, hv0, hv⟩ :=
    (GaloisForLFunctions.HTGeometry.finiteDet2_eq_zero_iff_exists_eigenvector
      (-(HilbertSchmidt.blockMatrix gammaSewnCriticalPhysicalPluckerKernel s)) hz0).mp hz
  have hv' :
      (HilbertSchmidt.blockMatrix gammaSewnCriticalPhysicalPluckerKernel s) *ᵥ v =
        z⁻¹ • v := by
    rw [Matrix.neg_mulVec] at hv
    simpa using congrArg Neg.neg hv
  let w := HilbertSchmidt.liftBlockLp v
  have hw0 : w ≠ 0 := HilbertSchmidt.liftBlockLp_ne_zero hv0
  have hwtrunc :
      HilbertSchmidt.toOperator
          (HilbertSchmidt.isHS_truncKernel
            gammaSewnCriticalPhysicalPluckerKernel_isHS s) w = z⁻¹ • w := by
    exact HilbertSchmidt.toOperator_truncKernel_liftBlockLp
      gammaSewnCriticalPhysicalPluckerKernel_isHS s hv'
  have hinner_nonneg :=
    gammaSewnCriticalPhysicalPluckerSpectralOperator_isPositive.inner_nonneg_right w
  have hinner_ne :
      inner ℂ w (gammaSewnCriticalPhysicalPluckerSpectralOperator w) ≠ 0 := by
    intro hzero
    have hwker :=
      gammaSewnCriticalPhysicalPluckerSpectralOperator_isPositive.apply_eq_zero_of_inner_eq_zero
        hzero
    exact hw0 (gammaSewnCriticalPhysicalPluckerSpectralOperator_injective
      (by simpa using hwker))
  rw [← gammaSewnCriticalPhysicalPluckerKernel_toOperator] at hinner_nonneg hinner_ne
  rw [← inner_liftBlockLp_physicalPlucker_toOperator_truncKernel_eq s v,
    hwtrunc, inner_smul_right, inner_self_eq_norm_sq_to_K] at hinner_nonneg hinner_ne
  have hnormpos : 0 < ‖w‖ ^ (2 : ℕ) := sq_pos_of_pos (norm_pos_iff.mpr hw0)
  have hprodpos : 0 < (((‖w‖ ^ (2 : ℕ) : ℝ) : ℂ) * z⁻¹) := by
    apply lt_of_le_of_ne
    · simpa [mul_comm] using hinner_nonneg
    · simpa [mul_comm] using hinner_ne.symm
  rcases (RCLike.ofReal_mul_pos_iff (K := ℂ) (‖w‖ ^ (2 : ℕ)) z⁻¹).mp hprodpos with
      hneg | hpos
  · exact (not_lt_of_ge hnormpos.le hneg.1).elim
  · exact RCLike.inv_pos.mp hpos.2

theorem gammaSewnCriticalPhysicalPluckerFiniteDet2_zero_re_im
    (s : Finset GammaSewnCriticalPhysicalPluckerIndex) {z : ℂ}
    (hz : gammaSewnCriticalPhysicalPluckerFiniteDet2 s z = 0) :
    0 < z.re ∧ z.im = 0 :=
  (RCLike.pos_iff (K := ℂ)).mp
    (gammaSewnCriticalPhysicalPluckerFiniteDet2_zero_pos s hz)

/-- Every finite reflected SP-E approximant has only strictly negative-real zeros. -/
theorem gammaSewnCriticalPhysicalPluckerStableFiniteDet2_zero_re_im
    (s : Finset GammaSewnCriticalPhysicalPluckerIndex) {u : ℂ}
    (hu : gammaSewnCriticalPhysicalPluckerStableFiniteDet2 s u = 0) :
    u.re < 0 ∧ u.im = 0 := by
  exact (RCLike.neg_iff (K := ℂ)).mp
    (neg_pos.mp (gammaSewnCriticalPhysicalPluckerFiniteDet2_zero_pos s hu))

/-- Pointwise cofinal convergence of finite physical source determinants. -/
theorem tendsto_gammaSewnCriticalPhysicalPluckerFiniteDet2
    (z : ℂ) :
    Tendsto
      (fun s : Finset GammaSewnCriticalPhysicalPluckerIndex =>
        gammaSewnCriticalPhysicalPluckerFiniteDet2 s z)
      atTop (nhds (gammaSewnCriticalPhysicalPluckerEntireDet2 z)) := by
  exact GaloisForLFunctions.HTGeometry.tendsto_finiteDet2_entireDet2
    gammaSewnCriticalPhysicalPluckerKernel_isHS z

theorem tendsto_gammaSewnCriticalPhysicalPluckerStableFiniteDet2
    (u : ℂ) :
    Tendsto
      (fun s : Finset GammaSewnCriticalPhysicalPluckerIndex =>
        gammaSewnCriticalPhysicalPluckerStableFiniteDet2 s u)
      atTop (nhds (gammaSewnCriticalPhysicalPluckerStableEntireDet2 u)) := by
  exact tendsto_gammaSewnCriticalPhysicalPluckerFiniteDet2 (-u)

/-- Locally uniform convergence on every closed disc, sufficient for Hurwitz transfer. -/
theorem tendstoUniformlyOn_gammaSewnCriticalPhysicalPluckerFiniteDet2
    {rho : ℝ} (hrho : 0 < rho) :
    TendstoUniformlyOn
      (fun (s : Finset GammaSewnCriticalPhysicalPluckerIndex) (z : ℂ) =>
        gammaSewnCriticalPhysicalPluckerFiniteDet2 s z)
      gammaSewnCriticalPhysicalPluckerEntireDet2 atTop
      (Metric.closedBall (0 : ℂ) rho) := by
  exact GaloisForLFunctions.HTGeometry.tendstoUniformlyOn_finiteDet2_entireDet2
    gammaSewnCriticalPhysicalPluckerKernel_isHS hrho

theorem tendstoUniformlyOn_gammaSewnCriticalPhysicalPluckerStableFiniteDet2
    {rho : ℝ} (hrho : 0 < rho) :
    TendstoUniformlyOn
      (fun (s : Finset GammaSewnCriticalPhysicalPluckerIndex) (u : ℂ) =>
        gammaSewnCriticalPhysicalPluckerStableFiniteDet2 s u)
      gammaSewnCriticalPhysicalPluckerStableEntireDet2 atTop
      (Metric.closedBall (0 : ℂ) rho) := by
  have hbase :=
    tendstoUniformlyOn_gammaSewnCriticalPhysicalPluckerFiniteDet2 hrho
  rw [Metric.tendstoUniformlyOn_iff] at hbase ⊢
  intro epsilon hepsilon
  filter_upwards [hbase epsilon hepsilon] with s hs u hu
  exact hs (-u) (by
    rw [Metric.mem_closedBall, dist_zero_right, norm_neg]
    simpa [Metric.mem_closedBall, dist_zero_right] using hu)

end RHTower.HedenmalmThetaSource
