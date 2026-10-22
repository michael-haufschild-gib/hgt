import GaloisForLFunctions.RHTower.RouteRDegreeSixBVGreenPhysicalCyclicDescentWall
import Mathlib.Analysis.PSeries

/-!
# The literal ordinary-integer Gibbs domain and physical exchange

Weighted summation of the existing operator diagonal defines a linear reader on its
actual summability submodule. The reciprocal Green operator is admitted exactly for
`1/2 < sigma`; normalization requires that proof. Every admitted operator satisfies
a Wold exchange law with the already fixed physical half-density gain. The normalized
literal Hochschild boundary therefore has its fixed physical value, nonzero in this
convergence chamber.

Both chain factors are admitted even at the critical parameter, while their product
is not. Reflection does not preserve Green admission. These domain and exchange
statements do not establish cyclic-to-physical agreement at Xi divisor copies or RH.
The functional is a weighted diagonal sum in the specified ordinary-integer basis;
no basis-independent trace on every sequence endomorphism is asserted.
-/

open Complex
namespace RHTower
noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Positive-integer Gibbs mass relative to the reciprocal Green operator. -/
def deningerOrdinaryIntegerGibbsMass (sigma : ℝ) (k : PNat) : ℝ :=
  ((k : ℕ) : ℝ) ^ (-(2 * sigma))

theorem deningerOrdinaryIntegerGibbsMass_pos (sigma : ℝ) (k : PNat) :
    0 < deningerOrdinaryIntegerGibbsMass sigma k :=
  Real.rpow_pos_of_pos (by exact_mod_cast k.pos) _

theorem summable_deningerOrdinaryIntegerGibbsMass_iff (sigma : ℝ) :
    Summable (deningerOrdinaryIntegerGibbsMass sigma) ↔ 1 / 2 < sigma := by
  unfold deningerOrdinaryIntegerGibbsMass
  rw [summable_pnat_iff_summable_nat (f := fun n : ℕ => (n : ℝ) ^ (-(2 * sigma))),
    Real.summable_nat_rpow]
  constructor <;> intro h <;> linarith

/-- Literal weighted diagonal: `k^(1-2*sigma) * (T e_k)(k)`. -/
def deningerOrdinaryIntegerGibbsDiagonal (sigma : ℝ) (k : PNat) :
    DeningerOrdinaryIntegerEnd →ₗ[ℂ] ℂ :=
  ((deningerOrdinaryIntegerGibbsMass sigma k : ℂ) * ((k : ℕ) : ℂ)) •
    deningerOrdinaryIntegerDiagonalCoefficient k

@[simp] theorem deningerOrdinaryIntegerGibbsDiagonal_reciprocalGreen
    (sigma : ℝ) (k : PNat) :
    deningerOrdinaryIntegerGibbsDiagonal sigma k
      deningerOrdinaryIntegerReciprocalGreen =
      (deningerOrdinaryIntegerGibbsMass sigma k : ℂ) := by
  have hk : ((k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast k.ne_zero
  simp [deningerOrdinaryIntegerGibbsDiagonal, hk]

/-- The actual domain on which weighted diagonal summation defines a linear map. -/
def deningerOrdinaryIntegerGibbsDomain (sigma : ℝ) :
    Submodule ℂ DeningerOrdinaryIntegerEnd where
  carrier := {T | Summable (fun k => deningerOrdinaryIntegerGibbsDiagonal sigma k T)}
  zero_mem' := by simp
  add_mem' := by
    intro T U hT hU
    simpa using hT.add hU
  smul_mem' := by
    intro c T hT
    simpa using hT.mul_left c

/-- The domain is an analytic condition, not an assumed cyclicity relation. -/
theorem deningerOrdinaryIntegerReciprocalGreen_mem_gibbsDomain_iff (sigma : ℝ) :
    deningerOrdinaryIntegerReciprocalGreen ∈
      deningerOrdinaryIntegerGibbsDomain sigma ↔ 1 / 2 < sigma := by
  change Summable (fun k => deningerOrdinaryIntegerGibbsDiagonal sigma k
    deningerOrdinaryIntegerReciprocalGreen) ↔ _
  simp only [deningerOrdinaryIntegerGibbsDiagonal_reciprocalGreen]
  rw [Complex.summable_ofReal, summable_deningerOrdinaryIntegerGibbsMass_iff]

/-- Summation on its genuine admitted operator domain. -/
def deningerOrdinaryIntegerGibbsTrace (sigma : ℝ) :
    deningerOrdinaryIntegerGibbsDomain sigma →ₗ[ℂ] ℂ where
  toFun T := ∑' k, deningerOrdinaryIntegerGibbsDiagonal sigma k T.val
  map_add' T U := by
    change (∑' k, deningerOrdinaryIntegerGibbsDiagonal sigma k (T.val + U.val)) = _
    simp only [map_add]
    exact Summable.tsum_add T.property U.property
  map_smul' c T := by
    change (∑' k, deningerOrdinaryIntegerGibbsDiagonal sigma k (c • T.val)) = _
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    exact tsum_mul_left

/-- Positive normalizing trace of the literal reciprocal Green operator. -/
def deningerOrdinaryIntegerGibbsPartition (sigma : ℝ) : ℝ :=
  ∑' k, deningerOrdinaryIntegerGibbsMass sigma k

theorem deningerOrdinaryIntegerGibbsPartition_pos {sigma : ℝ} (h : 1 / 2 < sigma) :
    0 < deningerOrdinaryIntegerGibbsPartition sigma :=
  ((summable_deningerOrdinaryIntegerGibbsMass_iff sigma).2 h).tsum_pos
    (fun k => (deningerOrdinaryIntegerGibbsMass_pos sigma k).le)
    1 (deningerOrdinaryIntegerGibbsMass_pos sigma 1)

/-- Normalized operator reader, defined only on the summable diagonal domain. -/
def deningerOrdinaryIntegerGibbsReader (sigma : ℝ) (_h : 1 / 2 < sigma) :
    deningerOrdinaryIntegerGibbsDomain sigma →ₗ[ℂ] ℂ :=
  ((deningerOrdinaryIntegerGibbsPartition sigma : ℂ))⁻¹ •
    deningerOrdinaryIntegerGibbsTrace sigma

theorem deningerOrdinaryIntegerGibbsTrace_reciprocalGreen
    {sigma : ℝ} (h : 1 / 2 < sigma) :
    deningerOrdinaryIntegerGibbsTrace sigma
      ⟨deningerOrdinaryIntegerReciprocalGreen,
        (deningerOrdinaryIntegerReciprocalGreen_mem_gibbsDomain_iff sigma).2 h⟩ =
      (deningerOrdinaryIntegerGibbsPartition sigma : ℂ) := by
  simp only [deningerOrdinaryIntegerGibbsTrace, LinearMap.coe_mk, AddHom.coe_mk,
    deningerOrdinaryIntegerGibbsDiagonal_reciprocalGreen]
  exact (Complex.ofRealCLM.map_tsum
    ((summable_deningerOrdinaryIntegerGibbsMass_iff sigma).2 h)).symm

theorem deningerOrdinaryIntegerGibbsReader_reciprocalGreen
    {sigma : ℝ} (h : 1 / 2 < sigma) :
    deningerOrdinaryIntegerGibbsReader sigma h
      ⟨deningerOrdinaryIntegerReciprocalGreen,
        (deningerOrdinaryIntegerReciprocalGreen_mem_gibbsDomain_iff sigma).2 h⟩ = 1 := by
  have hZ : (deningerOrdinaryIntegerGibbsPartition sigma : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (deningerOrdinaryIntegerGibbsPartition_pos h).ne'
  rw [deningerOrdinaryIntegerGibbsReader, LinearMap.smul_apply,
    deningerOrdinaryIntegerGibbsTrace_reciprocalGreen h, smul_eq_mul, inv_mul_cancel₀ hZ]

theorem deningerOrdinaryIntegerGibbsMass_mul (sigma : ℝ) (n k : PNat) :
    deningerOrdinaryIntegerGibbsMass sigma (n * k) =
      deningerOrdinaryIntegerGibbsMass sigma n *
        deningerOrdinaryIntegerGibbsMass sigma k := by
  unfold deningerOrdinaryIntegerGibbsMass
  push_cast
  exact Real.mul_rpow (by positivity) (by positivity)

@[simp] theorem deningerOrdinaryIntegerGibbsDiagonal_projectionGreen
    (sigma : ℝ) (n k : PNat) :
    deningerOrdinaryIntegerGibbsDiagonal sigma k
      (deningerOrdinaryIntegerDivisibilityProjection n *
        deningerOrdinaryIntegerReciprocalGreen) =
      if n ∣ k then (deningerOrdinaryIntegerGibbsMass sigma k : ℂ) else 0 := by
  classical
  have hk : ((k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast k.ne_zero
  by_cases h : n ∣ k <;>
    simp [deningerOrdinaryIntegerGibbsDiagonal,
      deningerOrdinaryIntegerDiagonalCoefficient,
      deningerOrdinaryIntegerDivisibilityProjection,
      deningerOrdinaryIntegerReciprocalGreen, Module.End.mul_apply, h, hk]

set_option backward.isDefEq.respectTransparency false in
theorem deningerOrdinaryIntegerProjectionGreen_mem_gibbsDomain
    {sigma : ℝ} (h : 1 / 2 < sigma) (n : PNat) :
    deningerOrdinaryIntegerDivisibilityProjection n *
      deningerOrdinaryIntegerReciprocalGreen ∈ deningerOrdinaryIntegerGibbsDomain sigma := by
  classical
  change Summable _
  simp only [deningerOrdinaryIntegerGibbsDiagonal_projectionGreen]
  have hs := (Complex.summable_ofReal.mpr
    ((summable_deningerOrdinaryIntegerGibbsMass_iff sigma).2 h)).indicator {k | n ∣ k}
  exact hs

/-- Reindexing the actual divisibility sublattice gives its full Gibbs mass. -/
theorem deningerOrdinaryIntegerGibbsMass_multiples (sigma : ℝ) (n : PNat) :
    (∑' k : PNat, if n ∣ k then deningerOrdinaryIntegerGibbsMass sigma k else 0) =
      deningerOrdinaryIntegerGibbsMass sigma n *
        deningerOrdinaryIntegerGibbsPartition sigma := by
  classical
  have hs : Function.support (fun k : PNat =>
      if n ∣ k then deningerOrdinaryIntegerGibbsMass sigma k else 0) ⊆
      Set.range (fun k : PNat => n * k) := by
    intro k hk
    have hnk : n ∣ k := by
      by_contra hnk
      exact hk (if_neg hnk)
    obtain ⟨j, hj⟩ := dvd_iff_exists_eq_mul_right.mp hnk
    exact ⟨j, hj.symm⟩
  rw [← (show Function.Injective (fun k : PNat => n * k) from fun _ _ h => mul_left_cancel h).tsum_eq hs]
  simp only [dvd_mul_right, if_true, deningerOrdinaryIntegerGibbsMass_mul]
  exact tsum_mul_left

theorem deningerOrdinaryIntegerGibbsTrace_projectionGreen
    {sigma : ℝ} (h : 1 / 2 < sigma) (n : PNat) :
    deningerOrdinaryIntegerGibbsTrace sigma
      ⟨deningerOrdinaryIntegerDivisibilityProjection n *
        deningerOrdinaryIntegerReciprocalGreen,
        deningerOrdinaryIntegerProjectionGreen_mem_gibbsDomain h n⟩ =
      (deningerOrdinaryIntegerGibbsMass sigma n : ℂ) *
        (deningerOrdinaryIntegerGibbsPartition sigma : ℂ) := by
  classical
  change (∑' k, deningerOrdinaryIntegerGibbsDiagonal sigma k
    (deningerOrdinaryIntegerDivisibilityProjection n *
      deningerOrdinaryIntegerReciprocalGreen)) = _
  simp only [deningerOrdinaryIntegerGibbsDiagonal_projectionGreen]
  have hs := (((summable_deningerOrdinaryIntegerGibbsMass_iff sigma).2 h).indicator
    {k : PNat | n ∣ k})
  rw [← Complex.ofReal_mul, ← deningerOrdinaryIntegerGibbsMass_multiples]
  have hc := Complex.ofRealCLM.map_tsum hs
  change ((∑' k : PNat, if n ∣ k then deningerOrdinaryIntegerGibbsMass sigma k else 0 : ℝ) : ℂ) =
    ∑' k : PNat, ((if n ∣ k then deningerOrdinaryIntegerGibbsMass sigma k else 0 : ℝ) : ℂ) at hc
  simpa only [apply_ite, Complex.ofReal_zero] using hc.symm

theorem deningerOrdinaryIntegerGibbsReader_projectionGreen
    {sigma : ℝ} (h : 1 / 2 < sigma) (n : PNat) :
    deningerOrdinaryIntegerGibbsReader sigma h
      ⟨deningerOrdinaryIntegerDivisibilityProjection n *
        deningerOrdinaryIntegerReciprocalGreen,
        deningerOrdinaryIntegerProjectionGreen_mem_gibbsDomain h n⟩ =
      (deningerOrdinaryIntegerGibbsMass sigma n : ℂ) := by
  have hZ : (deningerOrdinaryIntegerGibbsPartition sigma : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (deningerOrdinaryIntegerGibbsPartition_pos h).ne'
  rw [deningerOrdinaryIntegerGibbsReader, LinearMap.smul_apply,
    deningerOrdinaryIntegerGibbsTrace_projectionGreen h n, smul_eq_mul]
  field_simp

/-- No reflected pair of ordinary convergent readers admits the source Green operator. -/
theorem deningerOrdinaryIntegerGibbsDomain_not_reflected (sigma : ℝ) :
    ¬ (deningerOrdinaryIntegerReciprocalGreen ∈ deningerOrdinaryIntegerGibbsDomain sigma ∧
      deningerOrdinaryIntegerReciprocalGreen ∈ deningerOrdinaryIntegerGibbsDomain (1 - sigma)) := by
  rw [deningerOrdinaryIntegerReciprocalGreen_mem_gibbsDomain_iff,
    deningerOrdinaryIntegerReciprocalGreen_mem_gibbsDomain_iff]
  rintro ⟨h, hreflect⟩
  linarith

theorem deningerOrdinaryIntegerBVGreenStokesBoundary_mem_gibbsDomain
    {sigma : ℝ} (h : 1 / 2 < sigma) (n : PNat) :
    deningerOrdinaryIntegerBVGreenStokesBoundary n ∈
      deningerOrdinaryIntegerGibbsDomain sigma := by
  rw [deningerOrdinaryIntegerBVGreenStokesBoundary_eq]
  exact (deningerOrdinaryIntegerGibbsDomain sigma).sub_mem
    ((deningerOrdinaryIntegerGibbsDomain sigma).smul_mem _
      ((deningerOrdinaryIntegerReciprocalGreen_mem_gibbsDomain_iff sigma).2 h))
    (deningerOrdinaryIntegerProjectionGreen_mem_gibbsDomain h n)

set_option backward.isDefEq.respectTransparency false in
/-- Value on the literal Hochschild boundary, derived by summing its two admitted products. -/
theorem deningerOrdinaryIntegerGibbsReader_boundary
    {sigma : ℝ} (h : 1 / 2 < sigma) (n : PNat) :
    deningerOrdinaryIntegerGibbsReader sigma h
      ⟨deningerOrdinaryIntegerBVGreenStokesBoundary n,
        deningerOrdinaryIntegerBVGreenStokesBoundary_mem_gibbsDomain h n⟩ =
      (((n : ℕ) : ℂ))⁻¹ - (deningerOrdinaryIntegerGibbsMass sigma n : ℂ) := by
  let Q : deningerOrdinaryIntegerGibbsDomain sigma :=
    ⟨deningerOrdinaryIntegerReciprocalGreen,
      (deningerOrdinaryIntegerReciprocalGreen_mem_gibbsDomain_iff sigma).2 h⟩
  let P : deningerOrdinaryIntegerGibbsDomain sigma :=
    ⟨deningerOrdinaryIntegerDivisibilityProjection n *
      deningerOrdinaryIntegerReciprocalGreen,
      deningerOrdinaryIntegerProjectionGreen_mem_gibbsDomain h n⟩
  have heq : (⟨deningerOrdinaryIntegerBVGreenStokesBoundary n,
      deningerOrdinaryIntegerBVGreenStokesBoundary_mem_gibbsDomain h n⟩ :
        deningerOrdinaryIntegerGibbsDomain sigma) =
      (((n : ℕ) : ℂ))⁻¹ • Q - P :=
    Subtype.ext (deningerOrdinaryIntegerBVGreenStokesBoundary_eq n)
  rw [heq, (deningerOrdinaryIntegerGibbsReader sigma h).map_sub
    ((((n : ℕ) : ℂ))⁻¹ • Q) P,
    (deningerOrdinaryIntegerGibbsReader sigma h).map_smul (((n : ℕ) : ℂ))⁻¹ Q]
  change (((n : ℕ) : ℂ))⁻¹ *
    deningerOrdinaryIntegerGibbsReader sigma h Q -
      deningerOrdinaryIntegerGibbsReader sigma h P = _
  rw [deningerOrdinaryIntegerGibbsReader_reciprocalGreen h,
    deningerOrdinaryIntegerGibbsReader_projectionGreen h n, mul_one]

/-- The arithmetic scaling weight is exactly the previously fixed half-density gain. -/
theorem deningerOrdinaryIntegerGibbsMass_eq_gain (n : PNat) (s : ℂ) :
    deningerOrdinaryIntegerGibbsMass s.re n =
      (((n : ℕ) : ℝ))⁻¹ * (deningerHalfDensityMateGain n s)⁻¹ := by
  have hn : 0 < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  rw [deningerOrdinaryIntegerGibbsMass, Real.rpow_def_of_pos hn,
    deningerHalfDensityMateGain]
  calc
    Real.exp (Real.log (n : ℕ) * -(2 * s.re)) =
        Real.exp (-Real.log (n : ℕ)) *
          Real.exp (-((2 * s.re - 1) * Real.log (n : ℕ))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = _ := by rw [Real.exp_neg, Real.exp_log hn, Real.exp_neg]

/-- Source-to-fixed-physical agreement in the full, exact convergence chamber. -/
theorem deningerOrdinaryIntegerGibbsReader_eq_physicalBV
    (n : PNat) (s : ℂ) (h : 1 / 2 < s.re) :
    deningerOrdinaryIntegerGibbsReader s.re h
      ⟨deningerOrdinaryIntegerBVGreenStokesBoundary n,
        deningerOrdinaryIntegerBVGreenStokesBoundary_mem_gibbsDomain h n⟩ =
      (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation n s : ℂ) := by
  rw [deningerOrdinaryIntegerGibbsReader_boundary h n,
    deningerOrdinaryIntegerGibbsMass_eq_gain,
    deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation]
  push_cast
  ring

/-- In its honest convergence chamber this source-defined reader does not kill the boundary. -/
theorem deningerOrdinaryIntegerGibbsReader_boundary_ne_zero
    (n : PNat) (hn : 2 ≤ (n : ℕ)) (s : ℂ) (h : 1 / 2 < s.re) :
    deningerOrdinaryIntegerGibbsReader s.re h
      ⟨deningerOrdinaryIntegerBVGreenStokesBoundary n,
        deningerOrdinaryIntegerBVGreenStokesBoundary_mem_gibbsDomain h n⟩ ≠ 0 := by
  rw [deningerOrdinaryIntegerGibbsReader_eq_physicalBV n s h,
    Complex.ofReal_ne_zero]
  intro hz
  have hw := (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation_eq_zero_iff hn s).1 hz
  linarith

@[simp] theorem deningerOrdinaryIntegerWoldShift_basisVector (n k : PNat) :
    deningerOrdinaryIntegerWoldShift n (deningerOrdinaryIntegerBasisVector k) =
      deningerOrdinaryIntegerBasisVector (n * k) := by
  funext j
  rw [deningerOrdinaryIntegerWoldShift_apply]
  by_cases h : n ∣ j
  · rw [dif_pos h]
    have hq : pnatDvdQuotient n j h = k ↔ j = n * k := by
      constructor
      · intro heq
        exact (pnatDvdQuotient_spec n j h).symm.trans (congrArg (n * ·) heq)
      · intro heq
        exact mul_left_cancel ((pnatDvdQuotient_spec n j h).trans heq)
    simp only [deningerOrdinaryIntegerBasisVector, hq]
  · rw [dif_neg h]
    have hj : j ≠ n * k := by
      intro heq
      exact h (heq ▸ dvd_mul_right n k)
    simp [deningerOrdinaryIntegerBasisVector, hj]

@[simp] theorem deningerOrdinaryIntegerDiagonalCoefficient_compression
    (n k : PNat) (T : DeningerOrdinaryIntegerEnd) :
    deningerOrdinaryIntegerDiagonalCoefficient k
      (deningerOrdinaryIntegerWoldBackward n * (T * deningerOrdinaryIntegerWoldShift n)) =
      deningerOrdinaryIntegerDiagonalCoefficient (n * k) T := by
  change (T (deningerOrdinaryIntegerWoldShift n (deningerOrdinaryIntegerBasisVector k))) (n * k) = _
  rw [deningerOrdinaryIntegerWoldShift_basisVector]
  rfl

@[simp] theorem deningerOrdinaryIntegerDiagonalCoefficient_rightProjection
    (n k : PNat) (T : DeningerOrdinaryIntegerEnd) :
    deningerOrdinaryIntegerDiagonalCoefficient k
      (T * deningerOrdinaryIntegerDivisibilityProjection n) =
      if n ∣ k then deningerOrdinaryIntegerDiagonalCoefficient k T else 0 := by
  have hp : deningerOrdinaryIntegerDivisibilityProjection n
      (deningerOrdinaryIntegerBasisVector k) =
      if n ∣ k then deningerOrdinaryIntegerBasisVector k else 0 := by
    funext j
    by_cases hj : j = k
    · subst j
      by_cases h : n ∣ k <;>
        simp [deningerOrdinaryIntegerDivisibilityProjection_apply, h]
    · by_cases h : n ∣ k <;>
        simp [deningerOrdinaryIntegerDivisibilityProjection_apply,
          deningerOrdinaryIntegerBasisVector, hj, h]
  change (T (deningerOrdinaryIntegerDivisibilityProjection n
    (deningerOrdinaryIntegerBasisVector k))) k = _
  rw [hp]
  by_cases h : n ∣ k <;> simp [h, deningerOrdinaryIntegerDiagonalCoefficient]

theorem deningerOrdinaryIntegerGibbsDiagonal_compression
    (sigma : ℝ) (n k : PNat) (T : DeningerOrdinaryIntegerEnd) :
    deningerOrdinaryIntegerGibbsDiagonal sigma k
      (deningerOrdinaryIntegerWoldBackward n * (T * deningerOrdinaryIntegerWoldShift n)) =
      ((deningerOrdinaryIntegerGibbsMass sigma n : ℂ) * ((n : ℕ) : ℂ))⁻¹ *
        deningerOrdinaryIntegerGibbsDiagonal sigma (n * k) T := by
  have hm : (deningerOrdinaryIntegerGibbsMass sigma n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (deningerOrdinaryIntegerGibbsMass_pos sigma n).ne'
  have hn : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  simp only [deningerOrdinaryIntegerGibbsDiagonal, LinearMap.smul_apply, smul_eq_mul,
    deningerOrdinaryIntegerDiagonalCoefficient_compression,
    deningerOrdinaryIntegerGibbsMass_mul, Complex.ofReal_mul, PNat.mul_coe, Nat.cast_mul]
  field_simp

@[simp] theorem deningerOrdinaryIntegerGibbsDiagonal_rightProjection
    (sigma : ℝ) (n k : PNat) (T : DeningerOrdinaryIntegerEnd) :
    deningerOrdinaryIntegerGibbsDiagonal sigma k
      (T * deningerOrdinaryIntegerDivisibilityProjection n) =
      if n ∣ k then deningerOrdinaryIntegerGibbsDiagonal sigma k T else 0 := by
  simp only [deningerOrdinaryIntegerGibbsDiagonal, LinearMap.smul_apply, smul_eq_mul,
    deningerOrdinaryIntegerDiagonalCoefficient_rightProjection]
  by_cases h : n ∣ k <;> simp [h]

theorem deningerOrdinaryIntegerGibbsDomain_compression
    {sigma : ℝ} (T : deningerOrdinaryIntegerGibbsDomain sigma) (n : PNat) :
    deningerOrdinaryIntegerWoldBackward n * (T.val * deningerOrdinaryIntegerWoldShift n) ∈
      deningerOrdinaryIntegerGibbsDomain sigma := by
  change Summable _
  simp only [deningerOrdinaryIntegerGibbsDiagonal_compression]
  exact (T.property.comp_injective (show Function.Injective (fun k : PNat => n * k) from fun _ _ h => mul_left_cancel h)).mul_left _

theorem deningerOrdinaryIntegerGibbsDomain_rightProjection
    {sigma : ℝ} (T : deningerOrdinaryIntegerGibbsDomain sigma) (n : PNat) :
    T.val * deningerOrdinaryIntegerDivisibilityProjection n ∈
      deningerOrdinaryIntegerGibbsDomain sigma := by
  change Summable _
  simp only [deningerOrdinaryIntegerGibbsDiagonal_rightProjection]
  exact T.property.indicator {k | n ∣ k}

/-- Exact weighted exchange on every admitted operator, before divisor specialization. -/
theorem deningerOrdinaryIntegerGibbsTrace_compression
    {sigma : ℝ} (T : deningerOrdinaryIntegerGibbsDomain sigma) (n : PNat) :
    deningerOrdinaryIntegerGibbsTrace sigma
      ⟨deningerOrdinaryIntegerWoldBackward n * (T.val * deningerOrdinaryIntegerWoldShift n),
        deningerOrdinaryIntegerGibbsDomain_compression T n⟩ =
      ((deningerOrdinaryIntegerGibbsMass sigma n : ℂ) * ((n : ℕ) : ℂ))⁻¹ *
        deningerOrdinaryIntegerGibbsTrace sigma
          ⟨T.val * deningerOrdinaryIntegerDivisibilityProjection n,
            deningerOrdinaryIntegerGibbsDomain_rightProjection T n⟩ := by
  change (∑' k, deningerOrdinaryIntegerGibbsDiagonal sigma k
    (deningerOrdinaryIntegerWoldBackward n * (T.val * deningerOrdinaryIntegerWoldShift n))) =
    _ * (∑' k, deningerOrdinaryIntegerGibbsDiagonal sigma k
      (T.val * deningerOrdinaryIntegerDivisibilityProjection n))
  simp only [deningerOrdinaryIntegerGibbsDiagonal_compression,
    deningerOrdinaryIntegerGibbsDiagonal_rightProjection, tsum_mul_left]
  congr 1
  have hs : Function.support (fun k : PNat =>
      if n ∣ k then deningerOrdinaryIntegerGibbsDiagonal sigma k T.val else 0) ⊆
      Set.range (fun k : PNat => n * k) := by
    intro k hk
    have hnk : n ∣ k := by
      by_contra hnk
      exact hk (if_neg hnk)
    obtain ⟨j, hj⟩ := dvd_iff_exists_eq_mul_right.mp hnk
    exact ⟨j, hj.symm⟩
  simpa only [dvd_mul_right, if_true] using (show Function.Injective (fun k : PNat => n * k) from fun _ _ h => mul_left_cancel h).tsum_eq hs

theorem deningerOrdinaryIntegerGibbsMass_inverseWeight_eq_gain (n : PNat) (s : ℂ) :
    ((deningerOrdinaryIntegerGibbsMass s.re n : ℂ) * ((n : ℕ) : ℂ))⁻¹ =
      (deningerHalfDensityMateGain n s : ℂ) := by
  have hn : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  rw [deningerOrdinaryIntegerGibbsMass_eq_gain]
  push_cast
  field_simp

/-- The fixed physical gain is forced by the ordinary-integer source exchange law. -/
theorem deningerOrdinaryIntegerGibbsReader_physicalExchange
    (s : ℂ) (h : 1 / 2 < s.re) (T : deningerOrdinaryIntegerGibbsDomain s.re) (n : PNat) :
    deningerOrdinaryIntegerGibbsReader s.re h
      ⟨deningerOrdinaryIntegerWoldBackward n * (T.val * deningerOrdinaryIntegerWoldShift n),
        deningerOrdinaryIntegerGibbsDomain_compression T n⟩ =
      (deningerHalfDensityMateGain n s : ℂ) *
        deningerOrdinaryIntegerGibbsReader s.re h
          ⟨T.val * deningerOrdinaryIntegerDivisibilityProjection n,
            deningerOrdinaryIntegerGibbsDomain_rightProjection T n⟩ := by
  simp only [deningerOrdinaryIntegerGibbsReader, LinearMap.smul_apply, smul_eq_mul]
  rw [deningerOrdinaryIntegerGibbsTrace_compression T n,
    deningerOrdinaryIntegerGibbsMass_inverseWeight_eq_gain n s]
  ring

/-- The actual Hochschild factors are admitted at every real parameter, but their left
product is admitted exactly in the open convergence chamber. In particular, admission of
both factors at the neutral parameter does not make their product readable. -/
theorem deningerOrdinaryIntegerGibbs_actualChainAdmission
    (sigma : ℝ) (n : PNat) (hn : n ≠ 1) :
    deningerOrdinaryIntegerWoldBackward n ∈ deningerOrdinaryIntegerGibbsDomain sigma ∧
    deningerOrdinaryIntegerReciprocalGreen * deningerOrdinaryIntegerWoldShift n ∈
      deningerOrdinaryIntegerGibbsDomain sigma ∧
    (deningerOrdinaryIntegerWoldBackward n *
        (deningerOrdinaryIntegerReciprocalGreen * deningerOrdinaryIntegerWoldShift n) ∈
      deningerOrdinaryIntegerGibbsDomain sigma ↔ 1 / 2 < sigma) := by
  have hnk (k : PNat) : n * k ≠ k := by
    intro heq
    exact hn (mul_right_cancel (heq.trans (one_mul k).symm))
  have hkn (k : PNat) : k ≠ n * k := (hnk k).symm
  refine ⟨?_, ?_, ?_⟩
  · change Summable _
    convert (summable_zero : Summable (fun _ : PNat => (0 : ℂ))) using 1
    funext k
    simp [deningerOrdinaryIntegerGibbsDiagonal,
      deningerOrdinaryIntegerDiagonalCoefficient,
      deningerOrdinaryIntegerWoldBackward_apply,
      deningerOrdinaryIntegerBasisVector, hnk]
  · change Summable _
    convert (summable_zero : Summable (fun _ : PNat => (0 : ℂ))) using 1
    funext k
    simp [deningerOrdinaryIntegerGibbsDiagonal,
      deningerOrdinaryIntegerDiagonalCoefficient, Module.End.mul_apply,
      deningerOrdinaryIntegerWoldShift_basisVector,
      deningerOrdinaryIntegerReciprocalGreen_apply,
      deningerOrdinaryIntegerBasisVector, hkn]
  · rw [deningerOrdinaryIntegerWoldBackward_reciprocalGreen_WoldShift]
    have hnc : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
    constructor
    · intro hp
      have hQ := (deningerOrdinaryIntegerGibbsDomain sigma).smul_mem ((n : ℕ) : ℂ) hp
      simp only [smul_smul, mul_inv_cancel₀ hnc, one_smul] at hQ
      exact (deningerOrdinaryIntegerReciprocalGreen_mem_gibbsDomain_iff sigma).1 hQ
    · intro h
      exact (deningerOrdinaryIntegerGibbsDomain sigma).smul_mem _
        ((deningerOrdinaryIntegerReciprocalGreen_mem_gibbsDomain_iff sigma).2 h)

end
end RHTower
