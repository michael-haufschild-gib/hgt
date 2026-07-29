import GaloisForLFunctions.HTGeometry.EventComplementaryRecord

/-!
# An involution selects its complementary event record

For a complex matrix involution `A`, this file studies its two spectral projections

`C = (1 + A) / 2` and `R = (1 - A) / 2`.

They are complementary idempotents.  The continuation kernel is exactly the record range, the
record kernel is exactly the continuation range, and the combined continuation-record map is
injective.  The record also induces a canonical linear equivalence from the continuation
cokernel to the record range.

On a ten-dimensional carrier, trace `2` forces record rank `4` and continuation rank `6`, hence
the continuation has the exact `4/6/4` kernel/range/cokernel index.

These are unconditional spectral-projector facts.  They do not prove that a physical event is an
involution, that the record is spacetime, or that either projection is a quantum channel.
-/

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Positive spectral projection of an involution, interpreted algebraically as continuation. -/
def involutionContinuationProjection
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 : ℂ)⁻¹ • (1 + A)

/-- Continuation plus the negative spectral record reconstructs the identity. -/
theorem involutionContinuation_add_record
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) :
    involutionContinuationProjection A + involutionProjection A = 1 := by
  simp only [involutionContinuationProjection, involutionProjection]
  module

/-- The continuation annihilates the complementary record range. -/
theorem involutionContinuation_mul_record
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A * A = 1) :
    involutionContinuationProjection A * involutionProjection A = 0 := by
  simp only [involutionContinuationProjection, involutionProjection, Matrix.smul_mul,
    Matrix.mul_smul, add_mul, mul_sub, one_mul, mul_one, hA]
  module

/-- The complementary record annihilates the continuation range. -/
theorem involutionRecord_mul_continuation
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A * A = 1) :
    involutionProjection A * involutionContinuationProjection A = 0 := by
  simp only [involutionContinuationProjection, involutionProjection, Matrix.smul_mul,
    Matrix.mul_smul, sub_mul, mul_add, one_mul, mul_one, hA]
  module

/-- The continuation map is an idempotent whenever the source map is an involution. -/
theorem involutionContinuation_isIdempotent
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A * A = 1) :
    involutionContinuationProjection A * involutionContinuationProjection A =
      involutionContinuationProjection A := by
  simp only [involutionContinuationProjection, Matrix.smul_mul, Matrix.mul_smul,
    add_mul, mul_add, one_mul, mul_one, hA]
  module

/-- Pointwise reconstruction by continuation plus record. -/
theorem involutionContinuation_add_record_apply
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (x : n → ℂ) :
    (involutionContinuationProjection A).toLin' x +
      (involutionProjection A).toLin' x = x := by
  have h := congrArg (fun M => M *ᵥ x) (involutionContinuation_add_record A)
  simpa only [add_mulVec, one_mulVec] using h

/-- The directions erased by continuation are exactly the complementary record directions. -/
theorem involutionContinuation_ker_eq_record_range
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A * A = 1) :
    LinearMap.ker (involutionContinuationProjection A).toLin' =
      LinearMap.range (involutionProjection A).toLin' := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    refine ⟨x, ?_⟩
    have hsum := involutionContinuation_add_record_apply A x
    rw [hx, zero_add] at hsum
    exact hsum
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, ← Matrix.toLin'_mul_apply,
      involutionContinuation_mul_record A hA]
    simp

/-- The directions erased by the record are exactly the continued directions. -/
theorem involutionRecord_ker_eq_continuation_range
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A * A = 1) :
    LinearMap.ker (involutionProjection A).toLin' =
      LinearMap.range (involutionContinuationProjection A).toLin' := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    refine ⟨x, ?_⟩
    have hsum := involutionContinuation_add_record_apply A x
    rw [hx, add_zero] at hsum
    exact hsum
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, ← Matrix.toLin'_mul_apply,
      involutionRecord_mul_continuation A hA]
    simp

/-- Corestrict the complementary record to its intrinsic range. -/
def involutionRecordToRange
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) :
    (n → ℂ) →ₗ[ℂ] LinearMap.range (involutionProjection A).toLin' :=
  (involutionProjection A).toLin'.codRestrict _ fun x => ⟨x, rfl⟩

/-- The intrinsic record reporter reaches every record direction. -/
theorem involutionRecordToRange_surjective
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) :
    Function.Surjective (involutionRecordToRange A) := by
  rintro ⟨y, ⟨x, hx⟩⟩
  exact ⟨x, Subtype.ext hx⟩

/--
Continuation together with the intrinsic complementary record is faithful on the source
carrier.
-/
theorem involutionContinuation_prod_record_injective
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) :
    Function.Injective
      ((involutionContinuationProjection A).toLin'.prod (involutionRecordToRange A)) := by
  intro x y hxy
  have hc := congrArg Prod.fst hxy
  have hr := congrArg (fun z => ((z.2 : LinearMap.range
    (involutionProjection A).toLin') : n → ℂ)) hxy
  change (involutionContinuationProjection A).toLin' x =
    (involutionContinuationProjection A).toLin' y at hc
  change (involutionProjection A).toLin' x =
    (involutionProjection A).toLin' y at hr
  rw [← involutionContinuation_add_record_apply A x,
    ← involutionContinuation_add_record_apply A y, hc, hr]

/-- The intrinsic record reporter erases exactly the continuation range. -/
theorem involutionRecordToRange_ker_eq_continuation_range
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A * A = 1) :
    LinearMap.ker (involutionRecordToRange A) =
      LinearMap.range (involutionContinuationProjection A).toLin' := by
  rw [← involutionRecord_ker_eq_continuation_range A hA]
  ext x
  simp [involutionRecordToRange]

/--
The continuation cokernel is canonically the complementary record range selected by the same
involution.
-/
noncomputable def involutionContinuationCokernelEquivRecordRange
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A * A = 1) :
    ((n → ℂ) ⧸ LinearMap.range (involutionContinuationProjection A).toLin') ≃ₗ[ℂ]
      LinearMap.range (involutionProjection A).toLin' :=
  (Submodule.quotEquivOfEq _ _
    (involutionRecordToRange_ker_eq_continuation_range A hA).symm).trans
    ((involutionRecordToRange A).quotKerEquivOfSurjective
      (involutionRecordToRange_surjective A))

/--
The part of a law which is even under conjugation by the source involution.  For an involution,
this is exactly the sum of the continuation and record self-blocks.
-/
def involutionEvenPart
    {n : Type*} [Fintype n] [DecidableEq n]
    (A T : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 : ℂ)⁻¹ • (T + A * T * A)

/--
The part of a law which is odd under conjugation by the source involution.  For an involution,
this is exactly the sum of the two reciprocal continuation-record transfer blocks.
-/
def involutionOddPart
    {n : Type*} [Fintype n] [DecidableEq n]
    (A T : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 : ℂ)⁻¹ • (T - A * T * A)

/-- Every law is the sum of its actuality-even self-sector and actuality-odd transfer sector. -/
theorem involutionEven_add_odd
    {n : Type*} [Fintype n] [DecidableEq n]
    (A T : Matrix n n ℂ) :
    involutionEvenPart A T + involutionOddPart A T = T := by
  simp only [involutionEvenPart, involutionOddPart]
  module

/-- The even sector is fixed by conjugation with the source involution. -/
theorem involutionEven_conjugate
    {n : Type*} [Fintype n] [DecidableEq n]
    (A T : Matrix n n ℂ) (hA : A * A = 1) :
    A * involutionEvenPart A T * A = involutionEvenPart A T := by
  simp only [involutionEvenPart, Matrix.mul_smul, Matrix.smul_mul, mul_add,
    add_mul, ← Matrix.mul_assoc, hA, one_mul]
  rw [Matrix.mul_assoc T A A, hA, mul_one]
  module

/-- The transfer sector changes sign under conjugation with the source involution. -/
theorem involutionOdd_conjugate
    {n : Type*} [Fintype n] [DecidableEq n]
    (A T : Matrix n n ℂ) (hA : A * A = 1) :
    A * involutionOddPart A T * A = -involutionOddPart A T := by
  simp only [involutionOddPart, Matrix.mul_smul, Matrix.smul_mul, mul_sub,
    sub_mul, ← Matrix.mul_assoc, hA, one_mul, smul_sub]
  rw [Matrix.mul_assoc T A A, hA, mul_one]
  module

/--
The event-selected transfer sector vanishes exactly when the law preserves the source
involution.
-/
theorem involutionOdd_eq_zero_iff_commute
    {n : Type*} [Fintype n] [DecidableEq n]
    (A T : Matrix n n ℂ) (hA : A * A = 1) :
    involutionOddPart A T = 0 ↔ T * A = A * T := by
  constructor
  · intro hodd
    have hconj : T = A * T * A := by
      have hsub : T - A * T * A = 0 := by
        simpa [involutionOddPart] using hodd
      exact sub_eq_zero.mp hsub
    calc
      T * A = (A * T * A) * A := congrArg (fun X => X * A) hconj
      _ = A * T := by rw [Matrix.mul_assoc, hA, mul_one]
  · intro hcomm
    simp only [involutionOddPart, smul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, false_or]
    calc
      T - A * T * A = T - (T * A) * A := by rw [hcomm]
      _ = 0 := by rw [Matrix.mul_assoc, hA, mul_one, sub_self]

/--
**Event-selected colligation decomposition.**  Continuation and complementary record projections
canonically split every law into two self-blocks and two reciprocal transfer blocks.
-/
theorem involution_full_block_decomposition
    {n : Type*} [Fintype n] [DecidableEq n]
    (A T : Matrix n n ℂ) :
    T =
      involutionContinuationProjection A * T * involutionContinuationProjection A +
      involutionContinuationProjection A * T * involutionProjection A +
      involutionProjection A * T * involutionContinuationProjection A +
      involutionProjection A * T * involutionProjection A := by
  let P := involutionContinuationProjection A
  let Q := involutionProjection A
  have hsum : P + Q = 1 := by
    simpa [P, Q] using involutionContinuation_add_record A
  calc
    T = (P + Q) * T * (P + Q) := by rw [hsum, one_mul, mul_one]
    _ = P * T * P + P * T * Q + Q * T * P + Q * T * Q := by
      noncomm_ring
    _ = involutionContinuationProjection A * T * involutionContinuationProjection A +
        involutionContinuationProjection A * T * involutionProjection A +
        involutionProjection A * T * involutionContinuationProjection A +
        involutionProjection A * T * involutionProjection A := by
      rfl

/-- The actuality-even sector is exactly continuation self-law plus record self-law. -/
theorem involutionEven_eq_self_blocks
    {n : Type*} [Fintype n] [DecidableEq n]
    (A T : Matrix n n ℂ) :
    involutionEvenPart A T =
      involutionContinuationProjection A * T * involutionContinuationProjection A +
      involutionProjection A * T * involutionProjection A := by
  simp only [involutionEvenPart, involutionContinuationProjection, involutionProjection,
    Matrix.smul_mul, Matrix.mul_smul, add_mul, sub_mul, mul_add, mul_sub,
    one_mul, mul_one]
  module

/-- The actuality-odd sector is exactly the sum of outgoing and incoming transfer blocks. -/
theorem involutionOdd_eq_transfer_blocks
    {n : Type*} [Fintype n] [DecidableEq n]
    (A T : Matrix n n ℂ) :
    involutionOddPart A T =
      involutionContinuationProjection A * T * involutionProjection A +
      involutionProjection A * T * involutionContinuationProjection A := by
  simp only [involutionOddPart, involutionContinuationProjection, involutionProjection,
    Matrix.smul_mul, Matrix.mul_smul, add_mul, sub_mul, mul_add, mul_sub,
    one_mul, mul_one]
  module

/-- A trace-two involution on ten directions selects record rank four and continuation rank six. -/
theorem traceTwoInvolution_record_four_continuation_six
    (A : Matrix (Fin 10) (Fin 10) ℂ)
    (hA : A * A = 1) (htrace : Matrix.trace A = 2) :
    Module.finrank ℂ (LinearMap.range (involutionProjection A).toLin') = 4 ∧
      Module.finrank ℂ
        (LinearMap.range (involutionContinuationProjection A).toLin') = 6 := by
  have hformula := involution_trace_eq_card_sub_two_mul_finrank A hA
  have hrecordC :
      (Module.finrank ℂ (LinearMap.range (involutionProjection A).toLin') : ℂ) = 4 := by
    rw [htrace] at hformula
    norm_num at hformula ⊢
    linear_combination hformula / 2
  have hrecord :
      Module.finrank ℂ (LinearMap.range (involutionProjection A).toLin') = 4 := by
    exact_mod_cast hrecordC
  have hrankNullity := (involutionProjection A).toLin'.finrank_range_add_finrank_ker
  rw [involutionRecord_ker_eq_continuation_range A hA] at hrankNullity
  simp only [Module.finrank_pi, Fintype.card_fin, hrecord] at hrankNullity
  exact ⟨hrecord, by omega⟩

/-- The canonical continuation of a trace-two ten-involution has exact `4/6/4` index. -/
theorem traceTwoInvolution_continuation_four_six_four
    (A : Matrix (Fin 10) (Fin 10) ℂ)
    (hA : A * A = 1) (htrace : Matrix.trace A = 2) :
    Module.finrank ℂ
        (LinearMap.ker (involutionContinuationProjection A).toLin') = 4 ∧
      Module.finrank ℂ
        (LinearMap.range (involutionContinuationProjection A).toLin') = 6 ∧
      Module.finrank ℂ
        ((Fin 10 → ℂ) ⧸
          LinearMap.range (involutionContinuationProjection A).toLin') = 4 := by
  have hrank := (traceTwoInvolution_record_four_continuation_six A hA htrace).2
  have hindex :=
    rank_six_map_has_four_kernel_and_cokernel
      (involutionContinuationProjection A) hrank
  exact ⟨hindex.1, hrank, hindex.2⟩

end GaloisForLFunctions.HTGeometry
