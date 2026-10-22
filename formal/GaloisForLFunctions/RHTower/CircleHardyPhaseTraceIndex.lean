import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanCircleTraceCocycle
import GaloisForLFunctions.RHTower.RestrictedUnitaryFredholmCompression

/-!
# Relative index of a circle phase equals its signed first Fourier moment

Let `u` be a measurable unimodular function on the circle `ℝ/ℤ` whose Fourier coefficients have
absolutely summable first moments, `∑ |k| |û(k)| < ∞`.  With `P` the Hardy projection on
`L²(ℝ/ℤ)` and `U = M_u`, the pair `(U† P U, P)` has Schatten-one displacement and

`Tr (U† P U - P) = ∑_{k ≥ 1} k |û(k)|² - ∑_{k ≥ 1} k |û(-k)|²`.

For a trace-class displacement of two orthogonal projections the linear and the cubic trace
agree, so the relative index of the pair (dimension of `Ran(U†PU) ∩ Ker P` minus dimension of
`Ran P ∩ Ker(U†PU)`) is this signed first moment.  The Fredholm index of the Toeplitz
compression `P M_u P` is its negative.

The trace is computed by the corpus circle trace cocycle
(`opTrace_ccmCircleMultiplier_mul_quantizedDifferential`), applied to the symbol pair `(ū, u)`.
This is the Gohberg–Krein index theorem in trace form; it carries no novelty claim.  For the
boundary phase of a holomorphic function the moment is the number of zeros inside
(`CircleArgumentPhaseRelativeIndex`).
-/

noncomputable section

open Complex MeasureTheory ContinuousLinearMap
open scoped ENNReal InnerProductSpace

namespace RHTower

/-! ## Trace-class displacements: the linear and the cubic trace agree -/

section TwoProjections

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For two idempotents with Schatten-one displacement `D`, `Tr D³ = Tr D`.  With
`C = 1 - R - P` one has `D² + C² = 1` and `DC = -CD`, so `Tr (D C²) = -Tr (D C²)`. -/
theorem opTrace_restrictedProjectionCubicDefect_eq_opTrace_displacement
    (R P : H →L[ℂ] H) (hR : IsIdempotentElem R) (hP : IsIdempotentElem P)
    (hD : MemSchattenClass 1 (restrictedProjectionDisplacement R P)) :
    opTrace (restrictedProjectionCubicDefect R P) =
      opTrace (restrictedProjectionDisplacement R P) := by
  set D := restrictedProjectionDisplacement R P with hDdef
  set C := restrictedProjectionComplement R P with hCdef
  have hanti : D * C + C * D = 0 :=
    restrictedProjectionDisplacement_anticommutes_complement R P hR hP
  have hsq : D * D + C * C = 1 :=
    restrictedProjectionDisplacement_sq_add_complement_sq R P hR hP
  have hDC : D * C = -(C * D) := eq_neg_of_add_eq_zero_left hanti
  have hcube : D ^ 3 = D - D * C * C := by
    have hDD : D * D = 1 - C * C := eq_sub_of_add_eq hsq
    calc D ^ 3 = D * (D * D) := by rw [pow_succ, pow_two, mul_assoc]
      _ = D - D * C * C := by rw [hDD, mul_sub, mul_one, mul_assoc]
  have hDCC : MemSchattenClass 1 (D * C * C) := by
    have h1 : MemSchattenClass 1 (D ∘L C) := memSchattenClass_one_comp_right hD C
    exact memSchattenClass_one_comp_right h1 C
  have hzero : opTrace (D * C * C) = 0 := by
    have hDC1 : MemSchattenClass 1 (D ∘L C) := memSchattenClass_one_comp_right hD C
    have e1 : opTrace (D * C * C) = opTrace (C ∘L (D ∘L C)) :=
      (hDC1.one_opTrace_comp_comm C).symm
    have e2 : C ∘L (D ∘L C) = -((C * C) ∘L D) := by
      change C * (D * C) = -((C * C) * D)
      rw [hDC, mul_neg, mul_assoc]
    have e3 : opTrace ((C * C) ∘L D) = opTrace (D * C * C) := by
      rw [hD.one_opTrace_comp_comm (C * C)]
      change opTrace (D * (C * C)) = opTrace (D * C * C)
      rw [mul_assoc]
    have hx : opTrace (D * C * C) = -opTrace (D * C * C) :=
      calc opTrace (D * C * C) = opTrace (C ∘L (D ∘L C)) := e1
        _ = opTrace (-((C * C) ∘L D)) := by rw [e2]
        _ = -opTrace ((C * C) ∘L D) := opTrace_neg _
        _ = -opTrace (D * C * C) := by rw [e3]
    have h2 : (2 : ℂ) * opTrace (D * C * C) = 0 := by
      linear_combination hx
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  rw [restrictedProjectionCubicDefect, ← hDdef, hcube,
    opTrace_sub_of_memSchattenClass_one hD hDCC, hzero, sub_zero]

/-- **Linear trace formula for the relative index.**  For orthogonal projections with Schatten-one
displacement, the relative index is the ordinary trace of `R - P`. -/
theorem opTrace_restrictedProjectionDisplacement_eq_relativeIndex
    (R P : H →L[ℂ] H) (hR : IsIdempotentElem R) (hP : IsIdempotentElem P)
    (hRadj : adjoint R = R) (hPadj : adjoint P = P)
    (hD : MemSchattenClass 1 (restrictedProjectionDisplacement R P))
    (hDHS : (restrictedProjectionDisplacement R P).IsHilbertSchmidt) :
    opTrace (restrictedProjectionDisplacement R P) =
      (restrictedProjectionRelativeIndex R P : ℂ) := by
  rw [← opTrace_restrictedProjectionCubicDefect_eq_opTrace_displacement R P hR hP hD]
  exact opTrace_restrictedProjectionCubicDefect_eq_relativeIndex R P hR hP hRadj hPadj hDHS

end TwoProjections

/-! ## The circle Hardy projection is self-adjoint -/

theorem ccmCircleHardyProjection_adjoint :
    adjoint ccmCircleHardyProjection = ccmCircleHardyProjection := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  have hb : ∀ i : ℤ, (fourierBasis (T := (1 : ℝ))) i =
      (fourierLp (T := (1 : ℝ)) 2 i : CCMCircleL2) := fun i => by rw [coe_fourierBasis]
  rw [← (fourierBasis (T := (1 : ℝ))).tsum_inner_mul_inner (ccmCircleHardyProjection x) y,
    ← (fourierBasis (T := (1 : ℝ))).tsum_inner_mul_inner x (ccmCircleHardyProjection y)]
  refine tsum_congr fun i => ?_
  rw [hb]
  rw [← inner_conj_symm (ccmCircleHardyProjection x),
    inner_fourierLp_ccmCircleHardyProjection, inner_fourierLp_ccmCircleHardyProjection]
  by_cases hi : 0 ≤ i
  · rw [if_pos hi, if_pos hi, inner_conj_symm]
  · rw [if_neg hi, if_neg hi]
    simp

/-! ## Unimodular circle phases -/

/-- A measurable unimodular circle phase whose first Fourier moments are absolutely summable. -/
structure CCMCirclePhase where
  toFun : AddCircle (1 : ℝ) → ℂ
  measurable : Measurable toFun
  norm_eq_one : ∀ z, ‖toFun z‖ = 1
  positiveMoment : Summable fun n : ℕ =>
    ((n + 1 : ℕ) : ℝ) * ‖fourierCoeff toFun ((n + 1 : ℕ) : ℤ)‖
  negativeMoment : Summable fun n : ℕ =>
    ((n + 1 : ℕ) : ℝ) * ‖fourierCoeff toFun (-((n + 1 : ℕ) : ℤ))‖

namespace CCMCirclePhase

variable (u : CCMCirclePhase)

/-- The phase as a trace-regular circle symbol. -/
def toTraceSymbol : CCMCircleTraceSymbol where
  toFun := u.toFun
  bound := 1
  bound_nonneg := zero_le_one
  measurable := u.measurable
  norm_le z := (u.norm_eq_one z).le
  positiveMoment := u.positiveMoment
  negativeMoment := u.negativeMoment

/-- The conjugate phase as a bounded circle symbol. -/
def conjSymbol : CCMCircleBoundedSymbol where
  toFun z := starRingEnd ℂ (u.toFun z)
  bound := 1
  bound_nonneg := zero_le_one
  measurable := Complex.continuous_conj.measurable.comp u.measurable
  norm_le z := by rw [Complex.norm_conj]; exact (u.norm_eq_one z).le

/-- Multiplication by the phase. -/
def multiplier : CCMCircleL2 →L[ℂ] CCMCircleL2 :=
  ccmCircleMultiplier u.toTraceSymbol.toCCMCircleBoundedSymbol

/-- Multiplication by the conjugate phase. -/
def conjMultiplier : CCMCircleL2 →L[ℂ] CCMCircleL2 :=
  ccmCircleMultiplier u.conjSymbol

theorem multiplier_coeFn (f : CCMCircleL2) :
    ((u.multiplier f : CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) =ᵐ[AddCircle.haarAddCircle]
      fun z => u.toFun z * (f : AddCircle (1 : ℝ) → ℂ) z :=
  lpBoundedMulCLM_coeFn _ _ _ f

theorem conjMultiplier_coeFn (f : CCMCircleL2) :
    ((u.conjMultiplier f : CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) =ᵐ[AddCircle.haarAddCircle]
      fun z => starRingEnd ℂ (u.toFun z) * (f : AddCircle (1 : ℝ) → ℂ) z :=
  lpBoundedMulCLM_coeFn _ _ _ f

theorem conj_mul_self (z : AddCircle (1 : ℝ)) :
    starRingEnd ℂ (u.toFun z) * u.toFun z = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, u.norm_eq_one]
  norm_num

theorem conjMultiplier_mul_multiplier : u.conjMultiplier * u.multiplier = 1 := by
  ext1 f
  apply Lp.ext
  change ((u.conjMultiplier (u.multiplier f) : CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) =ᵐ[_] _
  filter_upwards [u.conjMultiplier_coeFn (u.multiplier f), u.multiplier_coeFn f] with z h1 h2
  rw [h1, h2, ← mul_assoc, u.conj_mul_self, one_mul]
  rfl

theorem multiplier_mul_conjMultiplier : u.multiplier * u.conjMultiplier = 1 := by
  ext1 f
  apply Lp.ext
  change ((u.multiplier (u.conjMultiplier f) : CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) =ᵐ[_] _
  filter_upwards [u.multiplier_coeFn (u.conjMultiplier f), u.conjMultiplier_coeFn f] with z h1 h2
  rw [h1, h2, ← mul_assoc, mul_comm (u.toFun z), u.conj_mul_self, one_mul]
  rfl

theorem adjoint_multiplier : adjoint u.multiplier = u.conjMultiplier := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [u.conjMultiplier_coeFn x, u.multiplier_coeFn y] with z h1 h2
  rw [h1, h2, RCLike.inner_apply', RCLike.inner_apply', map_mul, Complex.conj_conj]
  ring

/-- The Hardy commutator of the phase is half the corpus quantized differential. -/
theorem commutator_eq_half_quantizedDifferential :
    ccmCircleHardyProjection * u.multiplier - u.multiplier * ccmCircleHardyProjection =
      (1 / 2 : ℂ) • ccmCircleQuantizedDifferential u.toTraceSymbol := by
  rw [ccmCircleQuantizedDifferential, smul_smul]
  norm_num
  rfl

theorem commutator_memSchattenClass_one :
    MemSchattenClass 1
      (ccmCircleHardyProjection * u.multiplier - u.multiplier * ccmCircleHardyProjection) := by
  rw [u.commutator_eq_half_quantizedDifferential,
    ← ccmCircleNuclearQuantizedDifferential_coe_eq_quantizedDifferential]
  exact ((1 / 2 : ℂ) • ccmCircleNuclearQuantizedDifferential u.toTraceSymbol).property

/-- The restricted-unitary datum of a circle phase: Hardy projection and phase multiplier. -/
def datum : RestrictedUnitaryDatum CCMCircleL2 where
  projection := ccmCircleHardyProjection
  unitary := u.multiplier
  projection_idempotent := ccmCircleHardyProjection_idempotent
  projection_adjoint := ccmCircleHardyProjection_adjoint
  adjoint_mul_unitary := by rw [u.adjoint_multiplier, u.conjMultiplier_mul_multiplier]
  unitary_mul_adjoint := by rw [u.adjoint_multiplier, u.multiplier_mul_conjMultiplier]
  commutator_isHilbertSchmidt := by
    obtain ⟨S, V, _, hV, hfac⟩ := u.commutator_memSchattenClass_one.one_isTraceClass
    rw [hfac]
    exact hV.comp_left S

theorem displacement_eq :
    restrictedProjectionDisplacement u.datum.conjugateProjection u.datum.projection =
      (1 / 2 : ℂ) • (u.conjMultiplier * ccmCircleQuantizedDifferential u.toTraceSymbol) := by
  rw [u.datum.displacement_eq_adjoint_mul_commutator]
  change adjoint u.multiplier *
      (ccmCircleHardyProjection * u.multiplier - u.multiplier * ccmCircleHardyProjection) = _
  rw [u.adjoint_multiplier, u.commutator_eq_half_quantizedDifferential, mul_smul_comm]

theorem displacement_memSchattenClass_one :
    MemSchattenClass 1
      (restrictedProjectionDisplacement u.datum.conjugateProjection u.datum.projection) := by
  rw [u.datum.displacement_eq_adjoint_mul_commutator]
  exact memSchattenClass_one_comp_left u.commutator_memSchattenClass_one _

/-- Conjugation reflects the Fourier index. -/
theorem fourierCoeff_conjSymbol (n : ℤ) :
    fourierCoeff u.conjSymbol.toFun n = starRingEnd ℂ (fourierCoeff u.toFun (-n)) := by
  rw [fourierCoeff, fourierCoeff, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  change (fourier (-n)) z • starRingEnd ℂ (u.toFun z) =
    starRingEnd ℂ ((fourier (-(-n))) z • u.toFun z)
  rw [neg_neg, smul_eq_mul, smul_eq_mul, map_mul, fourier_neg]

/-- **Signed first Fourier moment** of the phase. -/
def windingMoment : ℝ :=
  (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * ‖fourierCoeff u.toFun ((n + 1 : ℕ) : ℤ)‖ ^ 2) -
    ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * ‖fourierCoeff u.toFun (-((n + 1 : ℕ) : ℤ))‖ ^ 2

private theorem mul_conj_cast (k : ℕ) (c : ℂ) :
    (((k : ℝ) * ‖c‖ ^ 2 : ℝ) : ℂ) = (k : ℂ) * (c * starRingEnd ℂ c) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- **Trace formula.**  `Tr (U† P U - P) = ∑_{k ≥ 1} k |û(k)|² - ∑_{k ≥ 1} k |û(-k)|²`. -/
theorem opTrace_displacement :
    opTrace (restrictedProjectionDisplacement u.datum.conjugateProjection u.datum.projection) =
      (u.windingMoment : ℂ) := by
  rw [u.displacement_eq, opTrace_smul]
  change (1 / 2 : ℂ) * opTrace (ccmCircleMultiplier u.conjSymbol *
    ccmCircleQuantizedDifferential u.toTraceSymbol) = _
  rw [opTrace_ccmCircleMultiplier_mul_quantizedDifferential]
  rw [windingMoment, Complex.ofReal_sub, Complex.ofReal_tsum, Complex.ofReal_tsum]
  have hpos : ∀ n : ℕ,
      (((n + 1 : ℕ) : ℂ) *
        (fourierCoeff u.toTraceSymbol.toFun ((n + 1 : ℕ) : ℤ) *
          fourierCoeff u.conjSymbol.toFun (-((n + 1 : ℕ) : ℤ)))) =
        ((((n + 1 : ℕ) : ℝ) * ‖fourierCoeff u.toFun ((n + 1 : ℕ) : ℤ)‖ ^ 2 : ℝ) : ℂ) := by
    intro n
    rw [mul_conj_cast, u.fourierCoeff_conjSymbol, neg_neg]
    rfl
  have hneg : ∀ n : ℕ,
      (((n + 1 : ℕ) : ℂ) *
        (fourierCoeff u.toTraceSymbol.toFun (-((n + 1 : ℕ) : ℤ)) *
          fourierCoeff u.conjSymbol.toFun ((n + 1 : ℕ) : ℤ))) =
        ((((n + 1 : ℕ) : ℝ) * ‖fourierCoeff u.toFun (-((n + 1 : ℕ) : ℤ))‖ ^ 2 : ℝ) : ℂ) := by
    intro n
    rw [mul_conj_cast, u.fourierCoeff_conjSymbol]
    rfl
  simp_rw [hpos, hneg]
  ring

/-- **Relative index = signed first Fourier moment.**  The relative index of the pair
`(U† P U, P)` is the signed first Fourier moment of the phase. -/
theorem relativeIndex_eq_windingMoment :
    (restrictedProjectionRelativeIndex u.datum.conjugateProjection u.datum.projection : ℝ) =
      u.windingMoment := by
  have h := opTrace_restrictedProjectionDisplacement_eq_relativeIndex
    u.datum.conjugateProjection u.datum.projection
    u.datum.conjugateProjection_idempotent u.datum.projection_idempotent
    u.datum.conjugateProjection_adjoint u.datum.projection_adjoint
    u.displacement_memSchattenClass_one u.datum.displacement_isHilbertSchmidt
  rw [u.opTrace_displacement] at h
  exact_mod_cast h.symm

/-- The signed first Fourier moment of a unimodular phase is an integer. -/
theorem windingMoment_eq_intCast :
    ∃ m : ℤ, u.windingMoment = m :=
  ⟨_, u.relativeIndex_eq_windingMoment.symm⟩

/-- The cubic trace of the phase pair is the signed first Fourier moment. -/
theorem opTrace_cubicDefect :
    opTrace (restrictedProjectionCubicDefect u.datum.conjugateProjection u.datum.projection) =
      (u.windingMoment : ℂ) := by
  rw [u.datum.opTrace_cubicDefect_eq_relativeIndex, ← u.relativeIndex_eq_windingMoment]
  simp

end CCMCirclePhase

end RHTower
