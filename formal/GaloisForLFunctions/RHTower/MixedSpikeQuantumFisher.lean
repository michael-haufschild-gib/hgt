import GaloisForLFunctions.HTGeometry.HilbertSchmidtRankOne

/-!
# Quantum Fisher information of a rank-one mixed spike

For the full-rank state `ρ = bI + c|ψ⟩⟨ψ|` evolving under a bounded
self-adjoint Hamiltonian, this file constructs the symmetric logarithmic
derivative, verifies its defining equation, and evaluates the resulting
quantum Fisher information exactly.
-/

open Complex
open scoped InnerProductSpace

namespace RHTower

noncomputable section

open ContinuousLinearMap InnerProductSpace

/-- Commutator `[|ψ⟩⟨ψ|,H]` controlling a mixed-spike unitary tangent. -/
def rankOneHamiltonianCommutator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (H : E →L[ℂ] E) (ψ : E) : E →L[ℂ] E :=
  (rankOne ℂ ψ ψ) * H - H * (rankOne ℂ ψ ψ)

/-- Rank-two expansion of the rank-one Hamiltonian commutator. -/
theorem rankOneHamiltonianCommutator_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (H : E →L[ℂ] E) (hH : adjoint H = H) (ψ : E) :
    rankOneHamiltonianCommutator H ψ =
      rankOne ℂ ψ (H ψ) - rankOne ℂ (H ψ) ψ := by
  unfold rankOneHamiltonianCommutator
  change (rankOne ℂ ψ ψ) ∘L H - H ∘L (rankOne ℂ ψ ψ) = _
  rw [rankOne_comp, comp_rankOne, hH]

/-- The rank-one Hamiltonian commutator is Hilbert--Schmidt. -/
theorem isHilbertSchmidt_rankOneHamiltonianCommutator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (H : E →L[ℂ] E) (ψ : E) :
    IsHilbertSchmidt (rankOneHamiltonianCommutator H ψ) := by
  unfold rankOneHamiltonianCommutator
  exact
    ((GaloisForLFunctions.HTGeometry.isHilbertSchmidt_rankOne ψ ψ).comp_right H).sub
      ((GaloisForLFunctions.HTGeometry.isHilbertSchmidt_rankOne ψ ψ).comp_left H)

/-- The expectation of a self-adjoint operator has zero imaginary part. -/
theorem inner_selfadjoint_apply_im_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (H : E →L[ℂ] E) (hH : adjoint H = H) (ψ : E) :
    (inner ℂ ψ (H ψ)).im = 0 := by
  have hsym : inner ℂ ψ (H ψ) = inner ℂ (H ψ) ψ := by
    calc
      inner ℂ ψ (H ψ) = inner ℂ ψ ((adjoint H) ψ) := by rw [hH]
      _ = inner ℂ (H ψ) ψ := H.adjoint_inner_right ψ ψ
  have hconj : starRingEnd ℂ (inner ℂ ψ (H ψ)) = inner ℂ ψ (H ψ) := by
    rw [inner_conj_symm]
    exact hsym.symm
  apply_fun Complex.im at hconj
  simp only [Complex.conj_im] at hconj
  linarith

/--
Exact rank-one commutator law: its squared Hilbert--Schmidt norm is twice
the Hamiltonian variance in the unit spike direction.
-/
theorem hsNormSq_rankOneHamiltonianCommutator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (H : E →L[ℂ] E) (hH : adjoint H = H)
    (ψ : E) (hψ : ‖ψ‖ = 1) :
    hsNormSq (rankOneHamiltonianCommutator H ψ) =
      2 * (‖H ψ‖ ^ 2 - ‖inner ℂ ψ (H ψ)‖ ^ 2) := by
  rw [rankOneHamiltonianCommutator_eq H hH ψ]
  let S := rankOne ℂ ψ (H ψ)
  let T := rankOne ℂ (H ψ) ψ
  have hS : IsHilbertSchmidt S :=
    GaloisForLFunctions.HTGeometry.isHilbertSchmidt_rankOne ψ (H ψ)
  have hT : IsHilbertSchmidt T :=
    GaloisForLFunctions.HTGeometry.isHilbertSchmidt_rankOne (H ψ) ψ
  change hsNormSq (S - T) = _
  rw [sub_eq_add_neg,
    GaloisForLFunctions.HTGeometry.hsNormSq_add hS hT.neg,
    hsNormSq_neg_eq_self,
    show hsNormSq S = ‖ψ‖ ^ 2 * ‖H ψ‖ ^ 2 by
      exact GaloisForLFunctions.HTGeometry.hsNormSq_rankOne ψ (H ψ),
    show hsNormSq T = ‖H ψ‖ ^ 2 * ‖ψ‖ ^ 2 by
      exact GaloisForLFunctions.HTGeometry.hsNormSq_rankOne (H ψ) ψ]
  rw [show hsInner S (-T) = -hsInner S T by
    simpa only [neg_one_smul ℂ T, neg_mul, one_mul] using
      hsInner_smul_right (-1 : ℂ) S T]
  rw [show hsInner S T =
      inner ℂ ψ (H ψ) * inner ℂ ψ (H ψ) by
    exact GaloisForLFunctions.HTGeometry.hsInner_rankOne ψ (H ψ) (H ψ) ψ]
  rw [hψ, one_pow]
  have him := inner_selfadjoint_apply_im_eq_zero H hH ψ
  simp only [Complex.neg_re, Complex.mul_re]
  rw [him]
  rw [Complex.sq_norm, Complex.normSq_apply, him]
  simp only [mul_zero, add_zero]
  nlinarith

/-- Full-rank mixed-spike state operator `bI+c|ψ⟩⟨ψ|`. -/
def mixedSpikeState
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b c : ℝ) (ψ : E) : E →L[ℂ] E :=
  (b : ℂ) • 1 + (c : ℂ) • rankOne ℂ ψ ψ

/-- A unit spike direction has eigenvalue `b+c`. -/
theorem mixedSpikeState_apply_self
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (b c : ℝ) {ψ : E} (hψ : ‖ψ‖ = 1) :
    mixedSpikeState b c ψ ψ = ((b + c : ℝ) : ℂ) • ψ := by
  simp [mixedSpikeState, InnerProductSpace.rankOne_apply,
    inner_self_eq_norm_sq_to_K, hψ]
  module

/-- Every direction orthogonal to the spike has eigenvalue `b`. -/
theorem mixedSpikeState_apply_of_orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b c : ℝ) {ψ x : E} (horth : inner ℂ ψ x = 0) :
    mixedSpikeState b c ψ x = (b : ℂ) • x := by
  simp [mixedSpikeState, InnerProductSpace.rankOne_apply, horth]

/-- Quadratic form of a mixed-spike state. -/
theorem mixedSpikeState_inner_re
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b c : ℝ) (ψ x : E) :
    (inner ℂ x (mixedSpikeState b c ψ x)).re =
      b * ‖x‖ ^ 2 + c * ‖inner ℂ ψ x‖ ^ 2 := by
  simp only [mixedSpikeState, add_apply, smul_apply, one_apply,
    InnerProductSpace.rankOne_apply, inner_add_right, inner_smul_right,
    ]
  rw [← inner_conj_symm ψ x]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    zero_mul, sub_zero, neg_mul, mul_neg, neg_neg]
  have hxx : (inner ℂ x x).re = ‖x‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) x
  rw [hxx]
  ring

/--
Projective survival loss of a mixed spike: measuring a unit reference
direction loses exactly `c(1-|⟨φ,ψ⟩|²)`.
-/
theorem mixedSpikeState_survivalLoss
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b c : ℝ) (φ : E) {ψ : E} (hψ : ‖ψ‖ = 1) :
    (b + c) - (inner ℂ ψ (mixedSpikeState b c φ ψ)).re =
      c * (1 - ‖inner ℂ φ ψ‖ ^ 2) := by
  rw [mixedSpikeState_inner_re, hψ, one_pow]
  ring

/-- Positive background makes a mixed-spike state strictly positive. -/
theorem mixedSpikeState_inner_re_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {b c : ℝ} (hb : 0 < b) (hc : 0 ≤ c) (ψ : E) {x : E} (hx : x ≠ 0) :
    0 < (inner ℂ x (mixedSpikeState b c ψ x)).re := by
  rw [mixedSpikeState_inner_re]
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hmain : 0 < b * ‖x‖ ^ 2 := mul_pos hb (sq_pos_of_pos hxnorm)
  have hspike : 0 ≤ c * ‖inner ℂ ψ x‖ ^ 2 :=
    mul_nonneg hc (sq_nonneg _)
  linarith

/-- A positive-background mixed spike has zero kernel. -/
theorem mixedSpikeState_injective
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {b c : ℝ} (hb : 0 < b) (hc : 0 ≤ c) (ψ : E) :
    Function.Injective (mixedSpikeState b c ψ) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hne
  have hpos := mixedSpikeState_inner_re_pos hb hc ψ hne
  rw [hx, inner_zero_right, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

/-- Unitary time tangent `i c[|ψ⟩⟨ψ|,H]` of a mixed spike. -/
def mixedSpikeUnitaryTangent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (c : ℝ) (H : E →L[ℂ] E) (ψ : E) : E →L[ℂ] E :=
  (Complex.I * (c : ℂ)) • rankOneHamiltonianCommutator H ψ

/-- Squared Hilbert--Schmidt speed of a mixed-spike unitary orbit. -/
theorem mixedSpikeUnitaryTangent_hsNormSq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (c : ℝ) (H : E →L[ℂ] E)
    (hH : adjoint H = H) (ψ : E) (hψ : ‖ψ‖ = 1) :
    hsNormSq (mixedSpikeUnitaryTangent c H ψ) =
      2 * c ^ 2 *
        (‖H ψ‖ ^ 2 - ‖inner ℂ ψ (H ψ)‖ ^ 2) := by
  have hK := isHilbertSchmidt_rankOneHamiltonianCommutator H ψ
  rw [mixedSpikeUnitaryTangent,
    GaloisForLFunctions.HTGeometry.hsNormSq_smul hK,
    hsNormSq_rankOneHamiltonianCommutator H hH ψ hψ]
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  rw [sq_abs]
  ring

/-- Candidate symmetric logarithmic derivative of a mixed-spike time orbit. -/
def mixedSpikeSymmetricLogDerivative
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b c : ℝ) (H : E →L[ℂ] E) (ψ : E) : E →L[ℂ] E :=
  (2 * Complex.I * (c : ℂ) / ((2 * b + c : ℝ) : ℂ)) •
    rankOneHamiltonianCommutator H ψ

/-- A unit rank-one operator is a projection. -/
theorem rankOneProjection_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {ψ : E} (hψ : ‖ψ‖ = 1) :
    (rankOne ℂ ψ ψ) * (rankOne ℂ ψ ψ) = rankOne ℂ ψ ψ := by
  change (rankOne ℂ ψ ψ) ∘L (rankOne ℂ ψ ψ) = _
  rw [rankOne_comp_rankOne]
  rw [inner_self_eq_norm_sq_to_K, hψ]
  simp

/--
The proposed logarithmic derivative satisfies the defining SLD equation
`(ρL+Lρ)/2 = ∂ρ` whenever `2b+c` is nonzero.
-/
theorem mixedSpikeSymmetricLogDerivative_equation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (b c : ℝ) (hden : 2 * b + c ≠ 0)
    (H : E →L[ℂ] E) (ψ : E) (hψ : ‖ψ‖ = 1) :
    (1 / 2 : ℂ) •
        (mixedSpikeState b c ψ *
            mixedSpikeSymmetricLogDerivative b c H ψ +
          mixedSpikeSymmetricLogDerivative b c H ψ *
            mixedSpikeState b c ψ) =
      mixedSpikeUnitaryTangent c H ψ := by
  let P := rankOne ℂ ψ ψ
  let K := P * H - H * P
  have hP : P * P = P := rankOneProjection_sq hψ
  have hPK : P * K + K * P = K := by
    dsimp [K]
    calc
      P * (P * H - H * P) + (P * H - H * P) * P =
          (P * P) * H - H * (P * P) := by noncomm_ring
      _ = P * H - H * P := by rw [hP]
  have hdenC : ((2 * b + c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hden
  change (1 / 2 : ℂ) •
      (((b : ℂ) • 1 + (c : ℂ) • P) *
          ((2 * I * (c : ℂ) / ((2 * b + c : ℝ) : ℂ)) • K) +
        ((2 * I * (c : ℂ) / ((2 * b + c : ℝ) : ℂ)) • K) *
          ((b : ℂ) • 1 + (c : ℂ) • P)) =
    (I * (c : ℂ)) • K
  have hanti :
      (((b : ℂ) • 1 + (c : ℂ) • P) *
          ((2 * I * (c : ℂ) / ((2 * b + c : ℝ) : ℂ)) • K) +
        ((2 * I * (c : ℂ) / ((2 * b + c : ℝ) : ℂ)) • K) *
          ((b : ℂ) • 1 + (c : ℂ) • P)) =
        (2 * I * (c : ℂ) / ((2 * b + c : ℝ) : ℂ)) •
          (((2 * b : ℝ) : ℂ) • K + (c : ℂ) • (P * K + K * P)) := by
    ext x
    simp only [mul_apply, smul_apply, one_apply, add_apply,
      map_smul, map_add]
    module
  rw [hanti, hPK]
  have hsum :
      (((2 * b : ℝ) : ℂ) • K + (c : ℂ) • K) =
        (((2 * b + c : ℝ) : ℂ) • K) := by
    module
  rw [hsum, smul_smul]
  have hcoef :
      (1 / 2 : ℂ) *
          ((2 * I * (c : ℂ) / ((2 * b + c : ℝ) : ℂ)) *
            (((2 * b + c : ℝ) : ℂ))) =
        I * (c : ℂ) := by
    field_simp [hdenC]
  rw [smul_smul, mul_assoc, hcoef]

/-- SLD quantum Fisher information `Re Tr((∂ρ)†L)` of a mixed spike. -/
def mixedSpikeSLDQuantumFisher
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (b c : ℝ) (H : E →L[ℂ] E) (ψ : E) : ℝ :=
  Complex.re
    (hsInner (mixedSpikeUnitaryTangent c H ψ)
      (mixedSpikeSymmetricLogDerivative b c H ψ))

/--
Exact mixed-spike quantum Fisher law:
`F_Q = 4c² Var_ψ(H)/(2b+c)`.
-/
theorem mixedSpikeSLDQuantumFisher_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (b c : ℝ) (hden : 2 * b + c ≠ 0)
    (H : E →L[ℂ] E) (hH : adjoint H = H)
    (ψ : E) (hψ : ‖ψ‖ = 1) :
    mixedSpikeSLDQuantumFisher b c H ψ =
      4 * c ^ 2 / (2 * b + c) *
        (‖H ψ‖ ^ 2 - ‖inner ℂ ψ (H ψ)‖ ^ 2) := by
  unfold mixedSpikeSLDQuantumFisher mixedSpikeUnitaryTangent
    mixedSpikeSymmetricLogDerivative
  let K := rankOneHamiltonianCommutator H ψ
  have hK : IsHilbertSchmidt K :=
    isHilbertSchmidt_rankOneHamiltonianCommutator H ψ
  rw [hsInner_smul_left, hsInner_smul_right]
  have hscalar :
      (starRingEnd ℂ) (I * (c : ℂ)) *
          (2 * I * (c : ℂ) / ((2 * b + c : ℝ) : ℂ)) =
        ((2 * c ^ 2 / (2 * b + c) : ℝ) : ℂ) := by
    have hnum :
        (starRingEnd ℂ) (I * (c : ℂ)) * (2 * I * (c : ℂ)) =
          ((2 * c ^ 2 : ℝ) : ℂ) := by
      rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
      push_cast
      ring_nf
      rw [show I ^ 2 = (-1 : ℂ) by norm_num]
      ring
    rw [div_eq_mul_inv, ← mul_assoc, hnum]
    push_cast [div_eq_mul_inv]
    ring
  change Complex.re
      ((starRingEnd ℂ) (I * (c : ℂ)) *
        ((2 * I * (c : ℂ) / ((2 * b + c : ℝ) : ℂ)) * hsInner K K)) = _
  rw [← mul_assoc, hscalar, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero,
    show (hsInner K K).re = hsNormSq K from hsInner_self_re hK,
    hsNormSq_rankOneHamiltonianCommutator H hH ψ hψ]
  field_simp
  ring

end

end RHTower
