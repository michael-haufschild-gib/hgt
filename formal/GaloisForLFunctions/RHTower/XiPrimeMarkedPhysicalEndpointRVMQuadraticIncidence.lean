import GaloisForLFunctions.RHTower.XiPrimeMarkedPhysicalEndpointRVMRelocation
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstMoment
import GaloisForLFunctions.RHTower.XiOrderFourteenCornerSourceExclusion
import GaloisForLFunctions.RHTower.ThetaCuspCassiniCalibratedReciprocalMomentNoGo
import GaloisForLFunctions.HTGeometry.OperatorFredholmGerm
import GaloisForLFunctions.HTGeometry.ScheffeCounting

/-!
# Exact quadratic source incidence with an RVM-locked tail

The raw marked-prime RVM relocation has a fixed Hilbert--Schmidt energy, so its first
centered-determinant coefficient need not agree automatically with the completed
prime--Gamma source moment.  A global rescaling would force that coefficient but would also
rescale the Riemann--von Mangoldt tail.

This module removes that false dichotomy.  It cuts off only finitely many diagonal RVM modes,
rescales the finite head together with the source relocation, and leaves the diagonal RVM tail
exactly unchanged.  Positivity of the source moment and summability of the reciprocal RVM
skeleton give a finite cut for which a unique positive scale makes the reflected quadratic trace
equal the source moment.  The scale is nonzero, so every cofinal source cycle survives.

This is unconditional and does not use the Xi divisor.  It closes degree two only; quartic and
all higher source-moment incidence remain separate.
-/

open scoped BigOperators InnerProductSpace Nat.Prime

namespace RHTower

noncomputable section

open ContinuousLinearMap

/-- Zeroth even moment of the completed prime--Gamma source. -/
def routeKSourceZerothMoment : ℝ :=
  analyticTraceMoments
    (normalizedTraceMomentGerm continuedPrimeArchSourceRelativeTrace) 0

theorem routeKSourceZerothMoment_pos :
    0 < routeKSourceZerothMoment :=
  analyticTraceMoments_normalizedPrimeArchSource_zero_pos

/-- First higher even moment of the same completed prime--Gamma source. -/
def routeKSourceFirstMoment : ℝ :=
  analyticTraceMoments
    (normalizedTraceMomentGerm continuedPrimeArchSourceRelativeTrace) 1

theorem routeKSourceFirstMoment_eq_normalizedPrimeArchMoment :
    routeKSourceFirstMoment = normalizedPrimeArchMoment 1 := rfl

theorem routeKSourceZerothMoment_eq_normalizedPrimeArchMoment :
    routeKSourceZerothMoment = normalizedPrimeArchMoment 0 := rfl

theorem routeKSourceFirstMoment_pos :
    0 < routeKSourceFirstMoment := by
  rw [routeKSourceFirstMoment_eq_normalizedPrimeArchMoment]
  exact normalizedPrimeArchMoment_one_pos

/-- **Strict two-moment feasibility cone.**  The completed source's quartic target lies strictly
inside the universal reflected self-adjoint moment bound `M₁ ≤ M₀²/2`.  Thus quartic incidence is
not ruled out by positivity or Schatten purity; the remaining issue is exact prime-source matrix
incidence. -/
theorem routeKSourceFirstMoment_lt_half_sq_zeroth :
    routeKSourceFirstMoment < routeKSourceZerothMoment ^ 2 / 2 := by
  have hzero :
      (1 / 25 : ℝ) < routeKSourceZerothMoment := by
    rw [routeKSourceZerothMoment_eq_normalizedPrimeArchMoment]
    exact one_div_twentyFive_lt_normalizedPrimeArchMoment_zero
  have hone :
      routeKSourceFirstMoment < (1 / 5000 : ℝ) := by
    rw [routeKSourceFirstMoment_eq_normalizedPrimeArchMoment]
    exact normalizedPrimeArchMoment_one_lt_one_over_fiveThousand
  have hsquare :
      (1 / 25 : ℝ) ^ 2 < routeKSourceZerothMoment ^ 2 := by
    have hprod :=
      mul_pos (sub_pos.mpr hzero)
        (add_pos (by norm_num : (0 : ℝ) < 1 / 25)
          routeKSourceZerothMoment_pos)
    nlinarith
  nlinarith

/-- Finite diagonal head of the reciprocal RVM skeleton. -/
def routeKRVMHeadWeight
    (s : Finset Nat.Primes) (p : Nat.Primes) : ℝ :=
  if p ∈ s then routeKPrimeRVMReciprocal p else 0

/-- Cofinite diagonal tail of the reciprocal RVM skeleton. -/
def routeKRVMTailWeight
    (s : Finset Nat.Primes) (p : Nat.Primes) : ℝ :=
  if p ∈ s then 0 else routeKPrimeRVMReciprocal p

theorem summable_routeKRVMHeadWeight_sq
    (s : Finset Nat.Primes) :
    Summable (fun p => routeKRVMHeadWeight s p ^ 2) := by
  apply Summable.of_nonneg_of_le
    (fun p => sq_nonneg (routeKRVMHeadWeight s p))
    (fun p => ?_) summable_routeKPrimeRVMReciprocal_sq
  by_cases hp : p ∈ s
  · simp [routeKRVMHeadWeight, hp]
  · simp [routeKRVMHeadWeight, hp, sq_nonneg]

theorem summable_routeKRVMTailWeight_sq
    (s : Finset Nat.Primes) :
    Summable (fun p => routeKRVMTailWeight s p ^ 2) := by
  apply Summable.of_nonneg_of_le
    (fun p => sq_nonneg (routeKRVMTailWeight s p))
    (fun p => ?_) summable_routeKPrimeRVMReciprocal_sq
  by_cases hp : p ∈ s
  · simp [routeKRVMTailWeight, hp, sq_nonneg]
  · simp [routeKRVMTailWeight, hp]

def routeKRVMHeadKernel
    (s : Finset Nat.Primes) (pq : Nat.Primes × Nat.Primes) : ℂ :=
  HilbertSchmidt.diagMul
    (fun p => (routeKRVMHeadWeight s p : ℂ)) pq

def routeKRVMTailKernel
    (s : Finset Nat.Primes) (pq : Nat.Primes × Nat.Primes) : ℂ :=
  HilbertSchmidt.diagMul
    (fun p => (routeKRVMTailWeight s p : ℂ)) pq

theorem routeKRVMHeadKernel_isHS
    (s : Finset Nat.Primes) :
    HilbertSchmidt.IsHS (routeKRVMHeadKernel s) := by
  apply HilbertSchmidt.isHS_diagMul_infinite
  exact (summable_routeKRVMHeadWeight_sq s).congr fun p => by
    simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem routeKRVMTailKernel_isHS
    (s : Finset Nat.Primes) :
    HilbertSchmidt.IsHS (routeKRVMTailKernel s) := by
  apply HilbertSchmidt.isHS_diagMul_infinite
  exact (summable_routeKRVMTailWeight_sq s).congr fun p => by
    simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]

def routeKRVMHeadOperator
    (s : Finset Nat.Primes) :
    RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
  HilbertSchmidt.toOperator (routeKRVMHeadKernel_isHS s)

def routeKRVMTailOperator
    (s : Finset Nat.Primes) :
    RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
  HilbertSchmidt.toOperator (routeKRVMTailKernel_isHS s)

theorem routeKRVMHeadOperator_isHilbertSchmidt
    (s : Finset Nat.Primes) :
    (routeKRVMHeadOperator s).IsHilbertSchmidt :=
  HilbertSchmidt.isHilbertSchmidt_toOperator
    (routeKRVMHeadKernel_isHS s)

theorem routeKRVMTailOperator_isHilbertSchmidt
    (s : Finset Nat.Primes) :
    (routeKRVMTailOperator s).IsHilbertSchmidt :=
  HilbertSchmidt.isHilbertSchmidt_toOperator
    (routeKRVMTailKernel_isHS s)

theorem routeKRVMHeadOperator_basis
    (s : Finset Nat.Primes) (p : Nat.Primes) :
    routeKRVMHeadOperator s (routeKPrimeBasis p) =
      (routeKRVMHeadWeight s p : ℂ) • routeKPrimeBasis p := by
  apply lp.ext
  funext q
  rw [routeKRVMHeadOperator, routeKPrimeBasis,
    HilbertSchmidt.toOperator_single (routeKRVMHeadKernel_isHS s)]
  change routeKRVMHeadKernel s (q, p) =
    ((routeKRVMHeadWeight s p : ℂ) •
      (lp.single 2 p 1 : RouteKPrimeHilbert)) q
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hqp : q = p
  · subst q
    simp [routeKRVMHeadKernel, HilbertSchmidt.diagMul]
  · simp [routeKRVMHeadKernel, HilbertSchmidt.diagMul, hqp]

theorem routeKRVMTailOperator_basis
    (s : Finset Nat.Primes) (p : Nat.Primes) :
    routeKRVMTailOperator s (routeKPrimeBasis p) =
      (routeKRVMTailWeight s p : ℂ) • routeKPrimeBasis p := by
  apply lp.ext
  funext q
  rw [routeKRVMTailOperator, routeKPrimeBasis,
    HilbertSchmidt.toOperator_single (routeKRVMTailKernel_isHS s)]
  change routeKRVMTailKernel s (q, p) =
    ((routeKRVMTailWeight s p : ℂ) •
      (lp.single 2 p 1 : RouteKPrimeHilbert)) q
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hqp : q = p
  · subst q
    simp [routeKRVMTailKernel, HilbertSchmidt.diagMul]
  · simp [routeKRVMTailKernel, HilbertSchmidt.diagMul, hqp]

theorem routeKRVMHeadKernel_hsAdjoint
    (s : Finset Nat.Primes) :
    HilbertSchmidt.hsAdjoint (routeKRVMHeadKernel s) =
      routeKRVMHeadKernel s := by
  funext pq
  rcases pq with ⟨p, q⟩
  by_cases hpq : p = q
  · subst q
    simp [HilbertSchmidt.hsAdjoint, routeKRVMHeadKernel,
      HilbertSchmidt.diagMul]
  · have hqp : q ≠ p := Ne.symm hpq
    simp [HilbertSchmidt.hsAdjoint, routeKRVMHeadKernel,
      HilbertSchmidt.diagMul, hpq, hqp]

theorem routeKRVMTailKernel_hsAdjoint
    (s : Finset Nat.Primes) :
    HilbertSchmidt.hsAdjoint (routeKRVMTailKernel s) =
      routeKRVMTailKernel s := by
  funext pq
  rcases pq with ⟨p, q⟩
  by_cases hpq : p = q
  · subst q
    simp [HilbertSchmidt.hsAdjoint, routeKRVMTailKernel,
      HilbertSchmidt.diagMul]
  · have hqp : q ≠ p := Ne.symm hpq
    simp [HilbertSchmidt.hsAdjoint, routeKRVMTailKernel,
      HilbertSchmidt.diagMul, hpq, hqp]

theorem routeKRVMHeadOperator_isSelfAdjoint
    (s : Finset Nat.Primes) :
    IsSelfAdjoint (routeKRVMHeadOperator s) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff',
    routeKRVMHeadOperator, HilbertSchmidt.adjoint_toOperator]
  exact HilbertSchmidt.toOperator_congr _ _
    (routeKRVMHeadKernel_hsAdjoint s)

theorem routeKRVMTailOperator_isSelfAdjoint
    (s : Finset Nat.Primes) :
    IsSelfAdjoint (routeKRVMTailOperator s) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff',
    routeKRVMTailOperator, HilbertSchmidt.adjoint_toOperator]
  exact HilbertSchmidt.toOperator_congr _ _
    (routeKRVMTailKernel_hsAdjoint s)

theorem routeKRVMHeadOperator_add_tail
    (s : Finset Nat.Primes) :
    routeKRVMHeadOperator s + routeKRVMTailOperator s =
      routeKRVMSkeletonOperator := by
  refine ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (HilbertSchmidt.lpBasis Nat.Primes).dense_span) ?_
  rintro x ⟨p, rfl⟩
  rw [HilbertSchmidt.lpBasis_apply]
  change
    (routeKRVMHeadOperator s + routeKRVMTailOperator s)
        (routeKPrimeBasis p) =
      routeKRVMSkeletonOperator (routeKPrimeBasis p)
  rw [add_apply, routeKRVMHeadOperator_basis,
    routeKRVMTailOperator_basis,
    routeKRVMSkeletonOperator_basis, ← add_smul]
  by_cases hp : p ∈ s <;>
    simp [routeKRVMHeadWeight, routeKRVMTailWeight, hp]

theorem hsNormSq_routeKRVMTailOperator
    (s : Finset Nat.Primes) :
    hsNormSq (routeKRVMTailOperator s) =
      ∑' p : Nat.Primes, routeKRVMTailWeight s p ^ 2 := by
  rw [routeKRVMTailOperator,
    HilbertSchmidt.hsNormSq_toOperator]
  change
    HilbertSchmidt.hsNormSq
        (HilbertSchmidt.diagMul
          (fun p => (routeKRVMTailWeight s p : ℂ))) =
      ∑' p : Nat.Primes, routeKRVMTailWeight s p ^ 2
  rw [HilbertSchmidt.hsNormSq_diagMul_infinite]
  apply tsum_congr
  intro p
  simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Reciprocal RVM energy has a cofinite tail smaller than half the positive source moment. -/
theorem exists_routeKRVM_tail_energy_lt_source_half :
    ∃ s : Finset Nat.Primes,
      hsNormSq (routeKRVMTailOperator s) <
        routeKSourceZerothMoment / 2 := by
  obtain ⟨s, hs⟩ :=
    GaloisForLFunctions.HTGeometry.exists_finset_tsum_compl_lt
      summable_routeKPrimeRVMReciprocal_sq.hasSum
      (half_pos routeKSourceZerothMoment_pos)
  refine ⟨s, ?_⟩
  rw [hsNormSq_routeKRVMTailOperator]
  calc
    ∑' p : Nat.Primes, routeKRVMTailWeight s p ^ 2 =
        ∑' p : Nat.Primes,
          ({p : Nat.Primes | p ∉ s}.indicator
            (fun p => routeKPrimeRVMReciprocal p ^ 2)) p := by
      apply tsum_congr
      intro p
      by_cases hp : p ∈ s <;>
        simp [routeKRVMTailWeight, Set.indicator, hp]
    _ = ∑' p : {p : Nat.Primes // p ∉ s},
          routeKPrimeRVMReciprocal p ^ 2 := by
      exact
        (tsum_subtype {p : Nat.Primes | p ∉ s}
          (fun p => routeKPrimeRVMReciprocal p ^ 2)).symm
    _ < routeKSourceZerothMoment / 2 := by
      change
        (∑' p : {p : Nat.Primes // p ∉ s},
          routeKPrimeRVMReciprocal p ^ 2) <
            routeKSourceZerothMoment / 2 at hs
      exact hs

/-- Source-selected finite head.  Only existence and the tail inequality matter; no numerical
cutoff is evaluated. -/
def routeKQuadraticAdmissionFinset : Finset Nat.Primes :=
  Classical.choose exists_routeKRVM_tail_energy_lt_source_half

theorem routeKQuadraticAdmissionFinset_tail_lt :
    hsNormSq
        (routeKRVMTailOperator routeKQuadraticAdmissionFinset) <
      routeKSourceZerothMoment / 2 :=
  Classical.choose_spec exists_routeKRVM_tail_energy_lt_source_half

theorem hsInner_routeKRVMDiagonal_physicalEndpointRVMRelocation_eq_zero
    (D : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert)
    (hD : D.IsHilbertSchmidt)
    (d : Nat.Primes → ℝ)
    (hDbasis : ∀ p, D (routeKPrimeBasis p) =
      (d p : ℂ) • routeKPrimeBasis p) :
    hsInner D routeKPhysicalEndpointRVMRelocation = 0 := by
  rw [hsInner_eq_tsum_basis hD
    routeKPhysicalEndpointRVMRelocation_isHilbertSchmidt
    (HilbertSchmidt.lpBasis Nat.Primes)]
  have hterm :
      (fun p : Nat.Primes =>
        inner ℂ
          (D (HilbertSchmidt.lpBasis Nat.Primes p))
          (routeKPhysicalEndpointRVMRelocation
            (HilbertSchmidt.lpBasis Nat.Primes p))) = 0 := by
    funext p
    rw [HilbertSchmidt.lpBasis_apply]
    change inner ℂ
      (D (routeKPrimeBasis p))
      (routeKPhysicalEndpointRVMRelocation (routeKPrimeBasis p)) = 0
    rw [hDbasis, inner_smul_left,
      routeKPhysicalEndpointRVMRelocation_diagonal_zero]
    simp
  rw [hterm]
  exact tsum_zero

theorem hsInner_routeKRVMHeadOperator_physicalEndpointRVMRelocation_eq_zero
    (s : Finset Nat.Primes) :
    hsInner (routeKRVMHeadOperator s)
      routeKPhysicalEndpointRVMRelocation = 0 :=
  hsInner_routeKRVMDiagonal_physicalEndpointRVMRelocation_eq_zero
    (routeKRVMHeadOperator s)
    (routeKRVMHeadOperator_isHilbertSchmidt s)
    (routeKRVMHeadWeight s)
    (routeKRVMHeadOperator_basis s)

theorem hsInner_routeKRVMTailOperator_physicalEndpointRVMRelocation_eq_zero
    (s : Finset Nat.Primes) :
    hsInner (routeKRVMTailOperator s)
      routeKPhysicalEndpointRVMRelocation = 0 :=
  hsInner_routeKRVMDiagonal_physicalEndpointRVMRelocation_eq_zero
    (routeKRVMTailOperator s)
    (routeKRVMTailOperator_isHilbertSchmidt s)
    (routeKRVMTailWeight s)
    (routeKRVMTailOperator_basis s)

theorem hsInner_routeKRVMTailOperator_head_eq_zero
    (s : Finset Nat.Primes) :
    hsInner (routeKRVMTailOperator s)
      (routeKRVMHeadOperator s) = 0 := by
  rw [hsInner_eq_tsum_basis
    (routeKRVMTailOperator_isHilbertSchmidt s)
    (routeKRVMHeadOperator_isHilbertSchmidt s)
    (HilbertSchmidt.lpBasis Nat.Primes)]
  have hterm :
      (fun p : Nat.Primes =>
        inner ℂ
          (routeKRVMTailOperator s
            (HilbertSchmidt.lpBasis Nat.Primes p))
          (routeKRVMHeadOperator s
            (HilbertSchmidt.lpBasis Nat.Primes p))) = 0 := by
    funext p
    rw [HilbertSchmidt.lpBasis_apply]
    change inner ℂ
      (routeKRVMTailOperator s (routeKPrimeBasis p))
      (routeKRVMHeadOperator s (routeKPrimeBasis p)) = 0
    rw [routeKRVMTailOperator_basis, routeKRVMHeadOperator_basis,
      inner_smul_left, inner_smul_right]
    by_cases hp : p ∈ s <;>
      simp [routeKRVMHeadWeight, routeKRVMTailWeight, hp]
  rw [hterm]
  exact tsum_zero

/-- Energy of the rescaled block: finite RVM head and off-diagonal source relocation remain
orthogonal. -/
theorem hsNormSq_routeKRVMHead_add_physicalEndpointRVMRelocation
    (s : Finset Nat.Primes) :
    hsNormSq
        (routeKRVMHeadOperator s +
          routeKPhysicalEndpointRVMRelocation) =
      hsNormSq (routeKRVMHeadOperator s) +
        hsNormSq routeKPhysicalEndpointRVMRelocation :=
  hsNormSq_add_eq_of_hsInner_eq_zero
    (routeKRVMHeadOperator_isHilbertSchmidt s)
    routeKPhysicalEndpointRVMRelocation_isHilbertSchmidt
    (hsInner_routeKRVMHeadOperator_physicalEndpointRVMRelocation_eq_zero s)

theorem hsNormSq_routeKRVMHead_add_physicalEndpointRVMRelocation_pos
    (s : Finset Nat.Primes) :
    0 <
      hsNormSq
        (routeKRVMHeadOperator s +
          routeKPhysicalEndpointRVMRelocation) := by
  rw [hsNormSq_routeKRVMHead_add_physicalEndpointRVMRelocation]
  exact add_pos_of_nonneg_of_pos
    (hsNormSq_nonneg _)
    hsNormSq_routeKPhysicalEndpointRVMRelocation_pos

theorem hsInner_routeKRVMTailOperator_head_add_relocation_eq_zero
    (s : Finset Nat.Primes) :
    hsInner (routeKRVMTailOperator s)
      (routeKRVMHeadOperator s +
        routeKPhysicalEndpointRVMRelocation) = 0 := by
  rw [hsInner_add_right
    (routeKRVMTailOperator_isHilbertSchmidt s)
    (routeKRVMHeadOperator_isHilbertSchmidt s)
    routeKPhysicalEndpointRVMRelocation_isHilbertSchmidt,
    hsInner_routeKRVMTailOperator_head_eq_zero,
    hsInner_routeKRVMTailOperator_physicalEndpointRVMRelocation_eq_zero,
    zero_add]

/-- Unique positive scale used on the finite RVM head and the full source relocation. -/
def routeKQuadraticAdmissionScale : ℝ :=
  Real.sqrt
    ((routeKSourceZerothMoment / 2 -
        hsNormSq
          (routeKRVMTailOperator routeKQuadraticAdmissionFinset)) /
      hsNormSq
        (routeKRVMHeadOperator routeKQuadraticAdmissionFinset +
          routeKPhysicalEndpointRVMRelocation))

theorem routeKQuadraticAdmissionScale_pos :
    0 < routeKQuadraticAdmissionScale := by
  rw [routeKQuadraticAdmissionScale, Real.sqrt_pos]
  exact div_pos
    (sub_pos.mpr routeKQuadraticAdmissionFinset_tail_lt)
    (hsNormSq_routeKRVMHead_add_physicalEndpointRVMRelocation_pos _)

theorem routeKQuadraticAdmissionScale_sq :
    routeKQuadraticAdmissionScale ^ 2 =
      (routeKSourceZerothMoment / 2 -
          hsNormSq
            (routeKRVMTailOperator routeKQuadraticAdmissionFinset)) /
        hsNormSq
          (routeKRVMHeadOperator routeKQuadraticAdmissionFinset +
            routeKPhysicalEndpointRVMRelocation) := by
  rw [routeKQuadraticAdmissionScale]
  exact Real.sq_sqrt
    (div_nonneg
      (sub_nonneg.mpr routeKQuadraticAdmissionFinset_tail_lt.le)
      (hsNormSq_nonneg _))

/-- The admission scale is forced once the finite head is fixed. -/
theorem routeKQuadraticAdmissionScale_unique
    {c : ℝ} (hc : 0 < c)
    (henergy :
      2 * (c ^ 2 *
            hsNormSq
              (routeKRVMHeadOperator routeKQuadraticAdmissionFinset +
                routeKPhysicalEndpointRVMRelocation) +
          hsNormSq
            (routeKRVMTailOperator routeKQuadraticAdmissionFinset)) =
        routeKSourceZerothMoment) :
    c = routeKQuadraticAdmissionScale := by
  have hE :
      0 <
        hsNormSq
          (routeKRVMHeadOperator routeKQuadraticAdmissionFinset +
            routeKPhysicalEndpointRVMRelocation) :=
    hsNormSq_routeKRVMHead_add_physicalEndpointRVMRelocation_pos _
  have hsquare :
      c ^ 2 = routeKQuadraticAdmissionScale ^ 2 := by
    rw [routeKQuadraticAdmissionScale_sq]
    apply (eq_div_iff hE.ne').2
    nlinarith
  nlinarith [hc, routeKQuadraticAdmissionScale_pos]

/-- Quadratically admitted Route K operator.  Outside one source-selected finite prime set its
diagonal is the exact reciprocal smooth-RVM skeleton; every off-diagonal source edge is rescaled
by one positive scalar. -/
def routeKQuadraticallyAdmittedOperator :
    RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
  (routeKQuadraticAdmissionScale : ℂ) •
      (routeKRVMHeadOperator routeKQuadraticAdmissionFinset +
        routeKPhysicalEndpointRVMRelocation) +
    routeKRVMTailOperator routeKQuadraticAdmissionFinset

theorem routeKQuadraticallyAdmittedOperator_isHilbertSchmidt :
    routeKQuadraticallyAdmittedOperator.IsHilbertSchmidt :=
  ((routeKRVMHeadOperator_isHilbertSchmidt _).add
    routeKPhysicalEndpointRVMRelocation_isHilbertSchmidt).smul
      (routeKQuadraticAdmissionScale : ℂ) |>.add
        (routeKRVMTailOperator_isHilbertSchmidt _)

theorem routeKQuadraticallyAdmittedOperator_isSelfAdjoint :
    IsSelfAdjoint routeKQuadraticallyAdmittedOperator := by
  apply IsSelfAdjoint.add
  · apply IsSelfAdjoint.smul
    · simp [IsSelfAdjoint]
    · exact (routeKRVMHeadOperator_isSelfAdjoint _).add
        routeKPhysicalEndpointRVMRelocation_isSelfAdjoint
  · exact routeKRVMTailOperator_isSelfAdjoint _

theorem hsInner_smul_head_add_relocation_tail_eq_zero :
    hsInner
        ((routeKQuadraticAdmissionScale : ℂ) •
          (routeKRVMHeadOperator routeKQuadraticAdmissionFinset +
            routeKPhysicalEndpointRVMRelocation))
        (routeKRVMTailOperator routeKQuadraticAdmissionFinset) = 0 := by
  rw [hsInner_smul_left]
  have hconj :=
    hsInner_conj_symm
      (routeKRVMHeadOperator routeKQuadraticAdmissionFinset +
        routeKPhysicalEndpointRVMRelocation)
      (routeKRVMTailOperator routeKQuadraticAdmissionFinset)
  rw [hsInner_routeKRVMTailOperator_head_add_relocation_eq_zero] at hconj
  rw [hconj]
  simp

/-- **Exact degree-two source incidence.**  Centered reflection doubles the positive-half square
trace, and that doubled trace equals the completed prime--Gamma source's zeroth even moment. -/
theorem two_mul_hsNormSq_routeKQuadraticallyAdmittedOperator :
    2 * hsNormSq routeKQuadraticallyAdmittedOperator =
      routeKSourceZerothMoment := by
  rw [routeKQuadraticallyAdmittedOperator,
    hsNormSq_add_eq_of_hsInner_eq_zero
      (((routeKRVMHeadOperator_isHilbertSchmidt _).add
        routeKPhysicalEndpointRVMRelocation_isHilbertSchmidt).smul _)
      (routeKRVMTailOperator_isHilbertSchmidt _)
      hsInner_smul_head_add_relocation_tail_eq_zero,
    hsNormSq_smul_eq
      ((routeKRVMHeadOperator_isHilbertSchmidt _).add
        routeKPhysicalEndpointRVMRelocation_isHilbertSchmidt),
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos routeKQuadraticAdmissionScale_pos,
    routeKQuadraticAdmissionScale_sq]
  have hden :
      hsNormSq
          (routeKRVMHeadOperator routeKQuadraticAdmissionFinset +
            routeKPhysicalEndpointRVMRelocation) ≠ 0 :=
    (hsNormSq_routeKRVMHead_add_physicalEndpointRVMRelocation_pos _).ne'
  field_simp [hden]
  ring

theorem two_mul_opTrace_sq_routeKQuadraticallyAdmittedOperator :
    2 * opTrace (routeKQuadraticallyAdmittedOperator ^ 2) =
      (routeKSourceZerothMoment : ℂ) := by
  rw [HTGeometry.opTrace_sq_eq_ofReal_hsNormSq
    routeKQuadraticallyAdmittedOperator_isHilbertSchmidt
    routeKQuadraticallyAdmittedOperator_isSelfAdjoint]
  exact_mod_cast
    two_mul_hsNormSq_routeKQuadraticallyAdmittedOperator

/-- The reciprocal RVM diagonal is exactly unchanged off the selected finite head. -/
theorem routeKQuadraticallyAdmittedOperator_diagonal_of_not_mem
    {p : Nat.Primes} (hp : p ∉ routeKQuadraticAdmissionFinset) :
    inner ℂ (routeKPrimeBasis p)
        (routeKQuadraticallyAdmittedOperator (routeKPrimeBasis p)) =
      (routeKPrimeRVMReciprocal p : ℂ) := by
  rw [routeKQuadraticallyAdmittedOperator,
    add_apply, smul_apply, inner_add_right, inner_smul_right,
    add_apply, inner_add_right, routeKRVMHeadOperator_basis,
    routeKPhysicalEndpointRVMRelocation_diagonal_zero,
    routeKRVMTailOperator_basis, inner_smul_right,
    inner_smul_right]
  simp [routeKRVMHeadWeight, routeKRVMTailWeight, hp]
  simp [routeKPrimeBasis]

/-- Exact admitted diagonal weight: finite head is positively rescaled, cofinite tail is fixed. -/
def routeKQuadraticallyAdmittedDiagonalWeight
    (p : Nat.Primes) : ℝ :=
  if p ∈ routeKQuadraticAdmissionFinset then
    routeKQuadraticAdmissionScale * routeKPrimeRVMReciprocal p
  else
    routeKPrimeRVMReciprocal p

theorem routeKQuadraticallyAdmittedDiagonalWeight_pos
    (p : Nat.Primes) :
    0 < routeKQuadraticallyAdmittedDiagonalWeight p := by
  by_cases hp : p ∈ routeKQuadraticAdmissionFinset
  · simp only [routeKQuadraticallyAdmittedDiagonalWeight, if_pos hp]
    exact mul_pos routeKQuadraticAdmissionScale_pos
      (routeKPrimeRVMReciprocal_pos p)
  · simp only [routeKQuadraticallyAdmittedDiagonalWeight, if_neg hp]
    exact routeKPrimeRVMReciprocal_pos p

theorem routeKQuadraticallyAdmittedOperator_diagonal
    (p : Nat.Primes) :
    inner ℂ (routeKPrimeBasis p)
        (routeKQuadraticallyAdmittedOperator (routeKPrimeBasis p)) =
      (routeKQuadraticallyAdmittedDiagonalWeight p : ℂ) := by
  rw [routeKQuadraticallyAdmittedOperator,
    add_apply, smul_apply, inner_add_right, inner_smul_right,
    add_apply, inner_add_right, routeKRVMHeadOperator_basis,
    routeKPhysicalEndpointRVMRelocation_diagonal_zero,
    routeKRVMTailOperator_basis, inner_smul_right,
    inner_smul_right]
  by_cases hp : p ∈ routeKQuadraticAdmissionFinset <;>
    simp [routeKQuadraticallyAdmittedDiagonalWeight,
      routeKRVMHeadWeight, routeKRVMTailWeight, hp,
      routeKPrimeBasis]

/-- Every off-diagonal source matrix entry survives, multiplied by the one positive admission
scale. -/
theorem routeKQuadraticallyAdmittedOperator_offDiagonal
    {p q : Nat.Primes} (hpq : p ≠ q) :
    inner ℂ (routeKPrimeBasis p)
        (routeKQuadraticallyAdmittedOperator (routeKPrimeBasis q)) =
      (routeKQuadraticAdmissionScale : ℂ) *
        inner ℂ (routeKPrimeBasis p)
          (routeKPhysicalEndpointRVMRelocation (routeKPrimeBasis q)) := by
  rw [routeKQuadraticallyAdmittedOperator,
    add_apply, smul_apply, inner_add_right, inner_smul_right,
    add_apply, inner_add_right, routeKRVMHeadOperator_basis,
    routeKRVMTailOperator_basis, inner_smul_right,
    inner_smul_right]
  have horth :
      inner ℂ (routeKPrimeBasis p) (routeKPrimeBasis q) = 0 := by
    simp [routeKPrimeBasis, lp.inner_single_left, hpq]
  rw [horth]
  simp

/-- Three-prime diagonal of the quadratically admitted operator. -/
def routeKQuadraticallyAdmittedTriangleSkeleton
    (p q r : Nat.Primes) : Fin 3 → ℝ :=
  ![routeKQuadraticallyAdmittedDiagonalWeight p,
    routeKQuadraticallyAdmittedDiagonalWeight q,
    routeKQuadraticallyAdmittedDiagonalWeight r]

/-- Three cyclic edges of the admitted operator. -/
def routeKQuadraticallyAdmittedTriangleEdge
    (p q r : Nat.Primes) : Fin 3 → ℝ :=
  fun i =>
    routeKQuadraticAdmissionScale *
      routeKPhysicalEndpointRVMTriangleEdge p q r i

theorem routeKQuadraticallyAdmittedTriangleSkeleton_pos
    (p q r : Nat.Primes) :
    ∀ i, 0 < routeKQuadraticallyAdmittedTriangleSkeleton p q r i := by
  intro i
  fin_cases i <;>
    simp [routeKQuadraticallyAdmittedTriangleSkeleton,
      routeKQuadraticallyAdmittedDiagonalWeight_pos]

theorem routeKQuadraticallyAdmittedTriangleEdge_ne_zero
    {p q r : Nat.Primes} (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p)
    (hpqB : xiPhysicalEndpointCompletedPairResponse p q ≠ 0)
    (hqrB : xiPhysicalEndpointCompletedPairResponse q r ≠ 0)
    (hrpB : xiPhysicalEndpointCompletedPairResponse r p ≠ 0) :
    ∀ i, routeKQuadraticallyAdmittedTriangleEdge p q r i ≠ 0 := by
  intro i
  exact mul_ne_zero routeKQuadraticAdmissionScale_pos.ne'
    (routeKPhysicalEndpointRVMTriangleEdge_ne_zero hpq hqr hrp
      hpqB hqrB hrpB i)

/-- The first reflection-even determinant-visible source signal survives the exact quadratic
admission normalization on arbitrarily late consecutive-prime triangles. -/
theorem exists_cofinal_quadraticallyAdmitted_quarticPairedTrace_ne_edgeFlip
    (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      routeKThreePrimePairedTracePower
          (routeKQuadraticallyAdmittedTriangleSkeleton
            (nthPrimeSubtype n) (nthPrimeSubtype (n + 1))
              (nthPrimeSubtype (n + 2)))
          (routeKQuadraticallyAdmittedTriangleEdge
            (nthPrimeSubtype n) (nthPrimeSubtype (n + 1))
              (nthPrimeSubtype (n + 2))) 4 ≠
        routeKThreePrimePairedTracePower
          (routeKQuadraticallyAdmittedTriangleSkeleton
            (nthPrimeSubtype n) (nthPrimeSubtype (n + 1))
              (nthPrimeSubtype (n + 2)))
          (routeKThreePrimeEdgeFlip
            (routeKQuadraticallyAdmittedTriangleEdge
              (nthPrimeSubtype n) (nthPrimeSubtype (n + 1))
                (nthPrimeSubtype (n + 2)))) 4 := by
  obtain ⟨n, hn, hpq, hqr, hrp⟩ :=
    exists_cofinal_positive_physicalEndpoint_pair_triangle N
  refine ⟨n, hn, ?_⟩
  apply routeKThreePrimePairedTracePower_four_ne_edgeFlip
  · exact routeKQuadraticallyAdmittedTriangleSkeleton_pos _ _ _
  · apply routeKQuadraticallyAdmittedTriangleEdge_ne_zero
    · exact nthPrimeSubtype_injective.ne (by omega)
    · exact nthPrimeSubtype_injective.ne (by omega)
    · exact nthPrimeSubtype_injective.ne (by omega)
    · exact hpq.ne'
    · exact hqr.ne'
    · exact hrp.ne'

/-- Cofinal nonzero source holonomy survives exact quadratic normalization. -/
theorem exists_cofinal_nonzero_quadraticallyAdmitted_triangleHolonomy
    (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      inner ℂ (routeKPrimeBasis (nthPrimeSubtype n))
          (routeKQuadraticallyAdmittedOperator
            (routeKPrimeBasis (nthPrimeSubtype (n + 1)))) *
        inner ℂ (routeKPrimeBasis (nthPrimeSubtype (n + 1)))
          (routeKQuadraticallyAdmittedOperator
            (routeKPrimeBasis (nthPrimeSubtype (n + 2)))) *
        inner ℂ (routeKPrimeBasis (nthPrimeSubtype (n + 2)))
          (routeKQuadraticallyAdmittedOperator
            (routeKPrimeBasis (nthPrimeSubtype n))) ≠ 0 := by
  obtain ⟨n, hn, hcycle⟩ :=
    exists_cofinal_nonzero_physicalEndpointRVMRelocation_triangleHolonomy N
  refine ⟨n, hn, ?_⟩
  rw [routeKQuadraticallyAdmittedOperator_offDiagonal
      (nthPrimeSubtype_injective.ne (by omega)),
    routeKQuadraticallyAdmittedOperator_offDiagonal
      (nthPrimeSubtype_injective.ne (by omega)),
    routeKQuadraticallyAdmittedOperator_offDiagonal
      (nthPrimeSubtype_injective.ne (by omega))]
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero
        (Complex.ofReal_ne_zero.mpr routeKQuadraticAdmissionScale_pos.ne')
        (fun hzero => hcycle (by rw [hzero]; simp))
    · exact mul_ne_zero
        (Complex.ofReal_ne_zero.mpr routeKQuadraticAdmissionScale_pos.ne')
        (fun hzero => hcycle (by rw [hzero]; simp))
  · exact mul_ne_zero
      (Complex.ofReal_ne_zero.mpr routeKQuadraticAdmissionScale_pos.ne')
      (fun hzero => hcycle (by rw [hzero]; simp))

end

end RHTower
