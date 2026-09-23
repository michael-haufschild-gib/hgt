import GaloisForLFunctions.HTGeometry.FiniteQuantumOperationalMemoryLaw
import GaloisForLFunctions.HTGeometry.TwoOutcomePinchingKadison

open scoped BigOperators Matrix

noncomputable section

namespace HTGeometry

/-- Algebraic projector-dephasing generator.  On a Hermitian projector this is the usual
Lindblad dissipator, with adjoints eliminated by self-adjointness. -/
def projectorDephasingGenerator
    {k R : Type*} [RCLike k] [Ring R] [Algebra k R]
    (P X : R) : R :=
  P * X * P - (2 : k)⁻¹ • (P * P * X + X * (P * P))

/-- Projector dephasing is half the nonselective pinching disturbance. -/
theorem projectorDephasingGenerator_eq_half_pinching_sub
    {k R : Type*} [RCLike k] [Ring R] [Algebra k R]
    (P X : R) (hP : IsIdempotentElem P) :
    projectorDephasingGenerator (k := k) P X =
      (2 : k)⁻¹ • (twoOutcomePinching P X - X) := by
  have hPP : P * P = P := hP
  rw [projectorDephasingGenerator, hPP]
  have hpinch : twoOutcomePinching P X - X =
      P * X * P + P * X * P - (P * X + X * P) := by
    simp only [twoOutcomePinching]
    noncomm_ring [hPP]
  rw [hpinch]
  have hhalf : (2 : k)⁻¹ * 2 = 1 := by
    rw [inv_mul_cancel₀]
    exact OfNat.ofNat_ne_zero 2
  module

/-- Exact kernel of an algebraic projector-dephasing generator. -/
theorem projectorDephasingGenerator_eq_zero_iff_commute
    {k R : Type*} [RCLike k] [Ring R] [Algebra k R]
    (P X : R) (hP : IsIdempotentElem P) :
    projectorDephasingGenerator (k := k) P X = 0 ↔ P * X = X * P := by
  rw [projectorDephasingGenerator_eq_half_pinching_sub (k := k) P X hP]
  constructor
  · intro h
    have hsub : twoOutcomePinching P X - X = 0 := by
      exact (smul_eq_zero.mp h).resolve_left (by norm_num)
    exact (twoOutcomePinching_eq_self_iff_commute hP X).mp
      (sub_eq_zero.mp hsub) |>.symm
  · intro h
    have hfixed : twoOutcomePinching P X = X :=
      (twoOutcomePinching_eq_self_iff_commute hP X).mpr h.symm
    rw [hfixed, sub_self, smul_zero]

/-- Once an observable is pinched, repeating the corresponding dephasing has no effect. -/
theorem projectorDephasingGenerator_pinching_eq_zero
    {k R : Type*} [RCLike k] [Ring R] [Algebra k R]
    (P X : R) (hP : IsIdempotentElem P) :
    projectorDephasingGenerator (k := k) P (twoOutcomePinching P X) = 0 := by
  rw [projectorDephasingGenerator_eq_zero_iff_commute (k := k) P _ hP]
  exact twoOutcomePinching_commutes hP X

variable {k E : Type*} [RCLike k]
  [NormedAddCommGroup E] [InnerProductSpace k E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Every orthogonal-subspace score already pinched into blocks is immune to another
projective-dephasing step.  Projection laws are carried by the subspace, not hypotheses. -/
theorem projectorDephasingGenerator_starProjection_pinching_eq_zero
    (S : Submodule k E) [S.HasOrthogonalProjection] (X : E →L[k] E) :
    projectorDephasingGenerator (k := k) S.starProjection
      (twoOutcomePinching S.starProjection X) = 0 := by
  exact projectorDephasingGenerator_pinching_eq_zero (k := k)
    S.starProjection X S.isIdempotentElem_starProjection

end HTGeometry

namespace RHTower

/-- Gain term of one finite-dimensional Lindblad jump. -/
def finiteLindbladGain {d : ℕ} (L X : QuantumMatrix d) : QuantumMatrix d :=
  L * X * Lᴴ

/-- Anticommutator drain term of one finite-dimensional Lindblad jump. -/
def finiteLindbladDrain {d : ℕ} (L X : QuantumMatrix d) : QuantumMatrix d :=
  (2 : ℂ)⁻¹ • (Lᴴ * L * X + X * (Lᴴ * L))

/-- Schrödinger-picture dissipator `L X L† - {L†L,X}/2`. -/
def finiteLindbladDissipator {d : ℕ} (L X : QuantumMatrix d) : QuantumMatrix d :=
  finiteLindbladGain L X - finiteLindbladDrain L X

/-- Change of a final observable produced by one Lindblad generator. -/
def finiteLindbladObservableResponse {d : ℕ}
    (L A ρ : QuantumMatrix d) : ℝ :=
  (Matrix.trace (A * finiteLindbladDissipator L ρ)).re

/-- Paper's damage convention: positive values mean lost score. -/
def finiteLindbladObservableDamage {d : ℕ}
    (L A ρ : QuantumMatrix d) : ℝ :=
  -finiteLindbladObservableResponse L A ρ

/-- Every finite Lindblad dissipator has zero trace. -/
theorem trace_finiteLindbladDissipator {d : ℕ} (L X : QuantumMatrix d) :
    Matrix.trace (finiteLindbladDissipator L X) = 0 := by
  rw [finiteLindbladDissipator, finiteLindbladGain, finiteLindbladDrain,
    Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_add]
  have hgain : Matrix.trace (L * X * Lᴴ) = Matrix.trace (Lᴴ * L * X) := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle L X Lᴴ
  have hright : Matrix.trace (X * (Lᴴ * L)) = Matrix.trace (Lᴴ * L * X) := by
    rw [Matrix.trace_mul_comm]
  rw [hgain, hright]
  ring

/-- The identity observable is immune to every Lindblad jump. -/
theorem finiteLindbladObservableResponse_one_eq_zero
    {d : ℕ} (L ρ : QuantumMatrix d) :
    finiteLindbladObservableResponse L 1 ρ = 0 := by
  simp [finiteLindbladObservableResponse, trace_finiteLindbladDissipator]

/-- A scalar baseline cannot contribute to a Lindblad observable response. -/
theorem finiteLindbladObservableResponse_add_real_smul_one
    {d : ℕ} (L A ρ : QuantumMatrix d) (c : ℝ) :
    finiteLindbladObservableResponse L (A + (c : ℂ) • 1) ρ =
      finiteLindbladObservableResponse L A ρ := by
  simp only [finiteLindbladObservableResponse, Matrix.add_mul,
    Matrix.smul_mul, Matrix.one_mul, Matrix.trace_add, Matrix.trace_smul,
    Complex.add_re, trace_finiteLindbladDissipator]
  simp

/-- A Hermitian projector dissipator is half the change caused by its nonselective pinching. -/
theorem finiteLindbladDissipator_projector_eq_half_pinching_sub
    {d : ℕ} (P X : QuantumMatrix d) (hP : P * P = P) (hPstar : Pᴴ = P) :
    finiteLindbladDissipator P X =
      (2 : ℂ)⁻¹ • (HTGeometry.twoOutcomePinching P X - X) := by
  rw [finiteLindbladDissipator, finiteLindbladGain, finiteLindbladDrain, hPstar, hP]
  have hpinch : HTGeometry.twoOutcomePinching P X - X =
      P * X * P + P * X * P - (P * X + X * P) := by
    simp only [HTGeometry.twoOutcomePinching]
    noncomm_ring [hP]
  rw [hpinch]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
  ring

/-- Hermitian-projector dephasing is minus one half of its double commutator. -/
theorem finiteLindbladDissipator_projector_eq_neg_half_doubleCommutator
    {d : ℕ} (P X : QuantumMatrix d) (hP : P * P = P) (hPstar : Pᴴ = P) :
    finiteLindbladDissipator P X =
      -(2 : ℂ)⁻¹ • (P * (P * X - X * P) - (P * X - X * P) * P) := by
  rw [finiteLindbladDissipator, finiteLindbladGain, finiteLindbladDrain, hPstar, hP]
  have hdouble : P * (P * X - X * P) - (P * X - X * P) * P =
      P * X + X * P - (P * X * P + P * X * P) := by
    simp only [mul_sub, sub_mul, ← Matrix.mul_assoc, hP]
    rw [Matrix.mul_assoc X P P, hP]
    abel
  rw [hdouble]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
  ring

/-- A Hermitian-projector dissipator vanishes exactly on its commutant. -/
theorem finiteLindbladDissipator_projector_eq_zero_iff_commute
    {d : ℕ} (P X : QuantumMatrix d) (hP : P * P = P) (hPstar : Pᴴ = P) :
    finiteLindbladDissipator P X = 0 ↔ P * X = X * P := by
  rw [finiteLindbladDissipator_projector_eq_half_pinching_sub P X hP hPstar]
  constructor
  · intro h
    have hsub : HTGeometry.twoOutcomePinching P X - X = 0 := by
      exact (smul_eq_zero.mp h).resolve_left (by norm_num)
    have hfixed : HTGeometry.twoOutcomePinching P X = X := sub_eq_zero.mp hsub
    exact (HTGeometry.twoOutcomePinching_eq_self_iff_commute
      (show IsIdempotentElem P from hP) X).mp hfixed |>.symm
  · intro h
    have hfixed : HTGeometry.twoOutcomePinching P X = X :=
      (HTGeometry.twoOutcomePinching_eq_self_iff_commute
        (show IsIdempotentElem P from hP) X).mpr h.symm
    rw [hfixed, sub_self, smul_zero]

/-- A projector dissipator is self-dual for the trace pairing. -/
theorem trace_mul_finiteLindbladDissipator_projector_duality
    {d : ℕ} (P A ρ : QuantumMatrix d) (hPstar : Pᴴ = P) :
    Matrix.trace (A * finiteLindbladDissipator P ρ) =
      Matrix.trace (finiteLindbladDissipator P A * ρ) := by
  simp only [finiteLindbladDissipator, finiteLindbladGain, finiteLindbladDrain,
    hPstar, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_add, Matrix.add_mul, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_add]
  have hgain : Matrix.trace (A * (P * ρ * P)) =
      Matrix.trace (P * A * P * ρ) := by
    calc
      Matrix.trace (A * (P * ρ * P)) = Matrix.trace ((A * P * ρ) * P) := by
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace (P * (A * P * ρ)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (P * A * P * ρ) := by simp only [Matrix.mul_assoc]
  have hright : Matrix.trace (A * (ρ * (P * P))) =
      Matrix.trace (P * P * A * ρ) := by
    calc
      Matrix.trace (A * (ρ * (P * P))) = Matrix.trace ((A * ρ) * (P * P)) := by
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((P * P) * (A * ρ)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (P * P * A * ρ) := by simp only [Matrix.mul_assoc]
  rw [hgain, hright]
  simp only [Matrix.mul_assoc]
  abel

/-- Every observable commuting with the measured projector has zero dephasing response. -/
theorem finiteLindbladObservableResponse_projector_eq_zero_of_commute
    {d : ℕ} (P A ρ : QuantumMatrix d) (hP : P * P = P)
    (hPstar : Pᴴ = P) (hcomm : P * A = A * P) :
    finiteLindbladObservableResponse P A ρ = 0 := by
  rw [finiteLindbladObservableResponse,
    trace_mul_finiteLindbladDissipator_projector_duality P A ρ hPstar]
  rw [(finiteLindbladDissipator_projector_eq_zero_iff_commute
    P A hP hPstar).2 hcomm, Matrix.zero_mul, Matrix.trace_zero]
  rfl

/-- In the paper's sign convention, every commuting score has zero terminal dephasing damage. -/
theorem finiteLindbladObservableDamage_projector_eq_zero_of_commute
    {d : ℕ} (P A ρ : QuantumMatrix d) (hP : P * P = P)
    (hPstar : Pᴴ = P) (hcomm : P * A = A * P) :
    finiteLindbladObservableDamage P A ρ = 0 := by
  simp [finiteLindbladObservableDamage,
    finiteLindbladObservableResponse_projector_eq_zero_of_commute
      P A ρ hP hPstar hcomm]

/-- Adding a real scalar to a Hermitian jump operator does not change its dissipator. -/
theorem finiteLindbladDissipator_sub_real_smul_one
    {d : ℕ} (L X : QuantumMatrix d) (c : ℝ) (hL : Lᴴ = L) :
    finiteLindbladDissipator (L - (c : ℂ) • 1) X =
      finiteLindbladDissipator L X := by
  have hc : star (c : ℂ) = (c : ℂ) := by simp
  simp only [finiteLindbladDissipator, finiteLindbladGain, finiteLindbladDrain,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    hL, hc]
  have hgain :
      (L - (c : ℂ) • 1) * X * (L - (c : ℂ) • 1) =
        L * X * L - (c : ℂ) • (L * X + X * L) + (c ^ (2 : ℕ) : ℂ) • X := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul]
    module
  have heffect :
      (L - (c : ℂ) • 1) * (L - (c : ℂ) • 1) =
        L * L - (2 * c : ℂ) • L + (c ^ (2 : ℕ) : ℂ) • 1 := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul]
    module
  rw [hgain, heffect]
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  norm_num
  module

/-- Lindblad jumps with the same `L†L` have exactly the same drain. -/
theorem finiteLindbladDrain_eq_of_effect_eq
    {d : ℕ} (L K X : QuantumMatrix d) (h : Lᴴ * L = Kᴴ * K) :
    finiteLindbladDrain L X = finiteLindbladDrain K X := by
  simp [finiteLindbladDrain, h]

/-- With a common `L†L`, the entire channel difference is the difference of gain terms. -/
theorem finiteLindbladDissipator_sub_eq_gain_sub_of_effect_eq
    {d : ℕ} (L K X : QuantumMatrix d) (h : Lᴴ * L = Kᴴ * K) :
    finiteLindbladDissipator L X - finiteLindbladDissipator K X =
      finiteLindbladGain L X - finiteLindbladGain K X := by
  rw [finiteLindbladDissipator, finiteLindbladDissipator,
    finiteLindbladDrain_eq_of_effect_eq L K X h]
  abel

end RHTower
