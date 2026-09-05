import GaloisForLFunctions.HTGeometry.RydbergProjectorDephasing

/-!
# First-order Lindblad channel additivity

This module formalizes the channel-additivity mechanism used in arXiv:2608.29858.
It applies to arbitrary finite jump families and arbitrary finite protocol schedules;
no positivity, perturbative approximation, or numerical calibration is assumed.
-/

open scoped BigOperators Matrix

noncomputable section

namespace RHTower

/-- Rate-weighted sum of a finite family of Lindblad generators. -/
def finiteLindbladFamilyDissipator
    {ι : Type*} [Fintype ι] {d : ℕ}
    (rate : ι → ℝ) (jump : ι → QuantumMatrix d) (X : QuantumMatrix d) :
    QuantumMatrix d :=
  ∑ i, (rate i : ℂ) • finiteLindbladDissipator (jump i) X

/-- Observable response of the complete channel family. -/
def finiteLindbladFamilyObservableResponse
    {ι : Type*} [Fintype ι] {d : ℕ}
    (rate : ι → ℝ) (jump : ι → QuantumMatrix d) (A X : QuantumMatrix d) : ℝ :=
  (Matrix.trace (A * finiteLindbladFamilyDissipator rate jump X)).re

/-- Damage convention for the complete channel family. -/
def finiteLindbladFamilyObservableDamage
    {ι : Type*} [Fintype ι] {d : ℕ}
    (rate : ι → ℝ) (jump : ι → QuantumMatrix d) (A X : QuantumMatrix d) : ℝ :=
  -finiteLindbladFamilyObservableResponse rate jump A X

/-- A weighted finite family remains trace preserving. -/
theorem trace_finiteLindbladFamilyDissipator
    {ι : Type*} [Fintype ι] {d : ℕ}
    (rate : ι → ℝ) (jump : ι → QuantumMatrix d) (X : QuantumMatrix d) :
    Matrix.trace (finiteLindbladFamilyDissipator rate jump X) = 0 := by
  simp [finiteLindbladFamilyDissipator, Matrix.trace_sum, Matrix.trace_smul,
    trace_finiteLindbladDissipator]

/-- First-order observable response is exactly additive across independent channels. -/
theorem finiteLindbladFamilyObservableResponse_eq_sum
    {ι : Type*} [Fintype ι] {d : ℕ}
    (rate : ι → ℝ) (jump : ι → QuantumMatrix d) (A X : QuantumMatrix d) :
    finiteLindbladFamilyObservableResponse rate jump A X =
      ∑ i, rate i * finiteLindbladObservableResponse (jump i) A X := by
  simp only [finiteLindbladFamilyObservableResponse, finiteLindbladFamilyDissipator,
    finiteLindbladObservableResponse, Matrix.mul_sum, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Complex.mul_re]

/-- The paper's damage convention inherits the same channel additivity. -/
theorem finiteLindbladFamilyObservableDamage_eq_sum
    {ι : Type*} [Fintype ι] {d : ℕ}
    (rate : ι → ℝ) (jump : ι → QuantumMatrix d) (A X : QuantumMatrix d) :
    finiteLindbladFamilyObservableDamage rate jump A X =
      ∑ i, rate i * finiteLindbladObservableDamage (jump i) A X := by
  rw [finiteLindbladFamilyObservableDamage,
    finiteLindbladFamilyObservableResponse_eq_sum]
  simp only [finiteLindbladObservableDamage]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Finite sampling model for an integrated first-order protocol cost. -/
structure RydbergFiniteFirstOrderProtocol
    (τ ι : Type*) [Fintype τ] [Fintype ι] (d : ℕ) where
  exposure : τ → ℝ
  rate : ι → ℝ
  jump : ι → QuantumMatrix d
  observable : τ → QuantumMatrix d
  state : τ → QuantumMatrix d

namespace RydbergFiniteFirstOrderProtocol

/-- Cost attributable to one channel over the complete protocol schedule. -/
def channelDamage
    {τ ι : Type*} [Fintype τ] [Fintype ι] {d : ℕ}
    (P : RydbergFiniteFirstOrderProtocol τ ι d) (i : ι) : ℝ :=
  ∑ t, P.exposure t *
    finiteLindbladObservableDamage (P.jump i) (P.observable t) (P.state t)

/-- Total cost obtained from the rate-weighted family generator at every schedule point. -/
def totalDamage
    {τ ι : Type*} [Fintype τ] [Fintype ι] {d : ℕ}
    (P : RydbergFiniteFirstOrderProtocol τ ι d) : ℝ :=
  ∑ t, P.exposure t *
    finiteLindbladFamilyObservableDamage P.rate P.jump (P.observable t) (P.state t)

/-- Exact protocol-level decomposition into channel-specific first-order costs. -/
theorem totalDamage_eq_sum_channelDamage
    {τ ι : Type*} [Fintype τ] [Fintype ι] {d : ℕ}
    (P : RydbergFiniteFirstOrderProtocol τ ι d) :
    P.totalDamage = ∑ i, P.rate i * P.channelDamage i := by
  rw [totalDamage]
  simp_rw [finiteLindbladFamilyObservableDamage_eq_sum]
  calc
    (∑ t, P.exposure t *
        ∑ i, P.rate i *
          finiteLindbladObservableDamage (P.jump i) (P.observable t) (P.state t)) =
        ∑ t, ∑ i, P.exposure t *
          (P.rate i *
            finiteLindbladObservableDamage (P.jump i) (P.observable t) (P.state t)) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mul_sum]
    _ = ∑ i, ∑ t, P.exposure t *
          (P.rate i *
            finiteLindbladObservableDamage (P.jump i) (P.observable t) (P.state t)) :=
      Finset.sum_comm
    _ = ∑ i, P.rate i * P.channelDamage i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [channelDamage, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      ring

end RydbergFiniteFirstOrderProtocol

/-- Two-channel generator in the decay/dephasing notation of the paper. -/
def finiteTwoChannelLindbladDissipator
    {d : ℕ} (decayRate dephasingRate : ℝ)
    (decayJump dephasingJump X : QuantumMatrix d) : QuantumMatrix d :=
  (decayRate : ℂ) • finiteLindbladDissipator decayJump X +
    (dephasingRate : ℂ) • finiteLindbladDissipator dephasingJump X

def finiteTwoChannelObservableDamage
    {d : ℕ} (decayRate dephasingRate : ℝ)
    (decayJump dephasingJump A X : QuantumMatrix d) : ℝ :=
  -(Matrix.trace
    (A * finiteTwoChannelLindbladDissipator
      decayRate dephasingRate decayJump dephasingJump X)).re

/-- Exact two-channel first-order cost law `Γ C_decay + γ C_dephasing`. -/
theorem finiteTwoChannelObservableDamage_eq
    {d : ℕ} (decayRate dephasingRate : ℝ)
    (decayJump dephasingJump A X : QuantumMatrix d) :
    finiteTwoChannelObservableDamage decayRate dephasingRate
        decayJump dephasingJump A X =
      decayRate * finiteLindbladObservableDamage decayJump A X +
        dephasingRate * finiteLindbladObservableDamage dephasingJump A X := by
  simp only [finiteTwoChannelObservableDamage, finiteTwoChannelLindbladDissipator,
    finiteLindbladObservableDamage, finiteLindbladObservableResponse,
    Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    Complex.add_re]
  simp [Complex.mul_re]
  ring

end RHTower
