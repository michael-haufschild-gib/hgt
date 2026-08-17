import GaloisForLFunctions.HTGeometry.QuasiLocalInfiniteLBitEvolutionLaw
import GaloisForLFunctions.HTGeometry.L2MultiplierContinuity

/-!
# Standard Hilbert-space dynamics for the infinite l-bit energy

The bounded continuous infinite-volume l-bit energy acts by multiplication on `L²` of the
configuration space with respect to any Borel measure.  This file proves that the resulting
Hamiltonian is bounded and self-adjoint and that its phase multipliers form a strongly continuous
one-parameter unitary group.
-/

open Filter MeasureTheory Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- `L²` Hilbert space of infinite Boolean configurations for an arbitrary Borel measure. -/
abbrev InfiniteLBitHilbertSpace
    (μ : Measure InfiniteLBitConfiguration) :=
  Lp ℂ 2 μ

/-- The total absolute interaction mass is nonnegative. -/
theorem quasiLocalInfiniteLBitMass_nonneg :
    0 ≤ quasiLocalInfiniteLBitMass := by
  exact tsum_nonneg fun _ => abs_nonneg _

/-- Complex-valued real energy symbol used by the Hilbert-space Hamiltonian. -/
def quasiLocalInfiniteLBitHamiltonianSymbol
    (σ : InfiniteLBitConfiguration) : ℂ :=
  quasiLocalInfiniteLBitEnergy σ

theorem measurable_quasiLocalInfiniteLBitHamiltonianSymbol :
    Measurable quasiLocalInfiniteLBitHamiltonianSymbol :=
  (Complex.continuous_ofReal.comp
    continuous_quasiLocalInfiniteLBitEnergy).measurable

theorem norm_quasiLocalInfiniteLBitHamiltonianSymbol_le
    (σ : InfiniteLBitConfiguration) :
    ‖quasiLocalInfiniteLBitHamiltonianSymbol σ‖ ≤
      quasiLocalInfiniteLBitMass := by
  simpa [quasiLocalInfiniteLBitHamiltonianSymbol, Complex.norm_real,
    Real.norm_eq_abs] using
      abs_quasiLocalInfiniteLBitEnergy_le_mass σ

/-- Bounded infinite-volume multiplication Hamiltonian on `L²`. -/
noncomputable def quasiLocalInfiniteLBitHamiltonian
    (μ : Measure InfiniteLBitConfiguration) :
    InfiniteLBitHilbertSpace μ →L[ℂ]
      InfiniteLBitHilbertSpace μ :=
  lpBoundedMulCLM
    measurable_quasiLocalInfiniteLBitHamiltonianSymbol
    quasiLocalInfiniteLBitMass_nonneg
    norm_quasiLocalInfiniteLBitHamiltonianSymbol_le

/-- The infinite-volume Hamiltonian is self-adjoint on every `L²` representation. -/
theorem quasiLocalInfiniteLBitHamiltonian_isSelfAdjoint
    (μ : Measure InfiniteLBitConfiguration) :
    IsSelfAdjoint (quasiLocalInfiniteLBitHamiltonian μ) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  exact lpBoundedMulCLM_inner_real
    measurable_quasiLocalInfiniteLBitHamiltonianSymbol
    quasiLocalInfiniteLBitMass_nonneg
    norm_quasiLocalInfiniteLBitHamiltonianSymbol_le
    (fun σ => by
      simp [quasiLocalInfiniteLBitHamiltonianSymbol]) f g

/-- Schrödinger phase evolution as a bounded `L²` multiplier. -/
noncomputable def quasiLocalInfiniteLBitHilbertEvolution
    (μ : Measure InfiniteLBitConfiguration) (t : ℝ) :
    InfiniteLBitHilbertSpace μ →L[ℂ]
      InfiniteLBitHilbertSpace μ :=
  lpBoundedMulCLM
    (continuous_quasiLocalInfiniteLBitPhase t).measurable
    zero_le_one
    (fun σ => by simp)

/-- The `L²` evolution acts almost everywhere by the expected Schrödinger phase. -/
theorem quasiLocalInfiniteLBitHilbertEvolution_coeFn
    (μ : Measure InfiniteLBitConfiguration) (t : ℝ)
    (ψ : InfiniteLBitHilbertSpace μ) :
    ((quasiLocalInfiniteLBitHilbertEvolution μ t ψ :
        InfiniteLBitHilbertSpace μ) : InfiniteLBitConfiguration → ℂ) =ᵐ[μ]
      fun σ => quasiLocalInfiniteLBitPhase t σ * ψ σ :=
  lpBoundedMulCLM_coeFn
    (continuous_quasiLocalInfiniteLBitPhase t).measurable
    zero_le_one (fun σ => by simp) ψ

/-- Time zero is the identity on `L²`. -/
@[simp]
theorem quasiLocalInfiniteLBitHilbertEvolution_zero
    (μ : Measure InfiniteLBitConfiguration)
    (ψ : InfiniteLBitHilbertSpace μ) :
    quasiLocalInfiniteLBitHilbertEvolution μ 0 ψ = ψ := by
  apply Lp.ext
  filter_upwards
    [quasiLocalInfiniteLBitHilbertEvolution_coeFn μ 0 ψ] with σ hσ
  rw [hσ]
  simp

/-- Exact one-parameter group law on `L²`. -/
theorem quasiLocalInfiniteLBitHilbertEvolution_add
    (μ : Measure InfiniteLBitConfiguration) (t s : ℝ)
    (ψ : InfiniteLBitHilbertSpace μ) :
    quasiLocalInfiniteLBitHilbertEvolution μ (t + s) ψ =
      quasiLocalInfiniteLBitHilbertEvolution μ t
        (quasiLocalInfiniteLBitHilbertEvolution μ s ψ) := by
  apply Lp.ext
  filter_upwards
    [quasiLocalInfiniteLBitHilbertEvolution_coeFn μ (t + s) ψ,
      quasiLocalInfiniteLBitHilbertEvolution_coeFn μ s ψ,
      quasiLocalInfiniteLBitHilbertEvolution_coeFn μ t
        (quasiLocalInfiniteLBitHilbertEvolution μ s ψ)] with σ hts hs ht
  rw [hts, ht, hs, quasiLocalInfiniteLBitPhase_add]
  ring

/-- Negative time is the inverse evolution. -/
@[simp]
theorem quasiLocalInfiniteLBitHilbertEvolution_neg_left
    (μ : Measure InfiniteLBitConfiguration) (t : ℝ)
    (ψ : InfiniteLBitHilbertSpace μ) :
    quasiLocalInfiniteLBitHilbertEvolution μ (-t)
      (quasiLocalInfiniteLBitHilbertEvolution μ t ψ) = ψ := by
  rw [← quasiLocalInfiniteLBitHilbertEvolution_add]
  simp

@[simp]
theorem quasiLocalInfiniteLBitHilbertEvolution_neg_right
    (μ : Measure InfiniteLBitConfiguration) (t : ℝ)
    (ψ : InfiniteLBitHilbertSpace μ) :
    quasiLocalInfiniteLBitHilbertEvolution μ t
      (quasiLocalInfiniteLBitHilbertEvolution μ (-t) ψ) = ψ := by
  rw [← quasiLocalInfiniteLBitHilbertEvolution_add]
  simp

/-- Every time evolution is norm-nonexpanding. -/
theorem norm_quasiLocalInfiniteLBitHilbertEvolution_le
    (μ : Measure InfiniteLBitConfiguration) (t : ℝ)
    (ψ : InfiniteLBitHilbertSpace μ) :
    ‖quasiLocalInfiniteLBitHilbertEvolution μ t ψ‖ ≤ ‖ψ‖ := by
  calc
    ‖quasiLocalInfiniteLBitHilbertEvolution μ t ψ‖
        ≤ ‖quasiLocalInfiniteLBitHilbertEvolution μ t‖ * ‖ψ‖ :=
          (quasiLocalInfiniteLBitHilbertEvolution μ t).le_opNorm ψ
    _ ≤ 1 * ‖ψ‖ := by
      gcongr
      exact norm_lpBoundedMulCLM_le
        (continuous_quasiLocalInfiniteLBitPhase t).measurable
        zero_le_one (fun σ => by simp)
    _ = ‖ψ‖ := one_mul _

/-- Exact `L²` norm preservation. -/
@[simp]
theorem norm_quasiLocalInfiniteLBitHilbertEvolution
    (μ : Measure InfiniteLBitConfiguration) (t : ℝ)
    (ψ : InfiniteLBitHilbertSpace μ) :
    ‖quasiLocalInfiniteLBitHilbertEvolution μ t ψ‖ = ‖ψ‖ := by
  apply le_antisymm
    (norm_quasiLocalInfiniteLBitHilbertEvolution_le μ t ψ)
  calc
    ‖ψ‖ =
        ‖quasiLocalInfiniteLBitHilbertEvolution μ (-t)
          (quasiLocalInfiniteLBitHilbertEvolution μ t ψ)‖ := by simp
    _ ≤ ‖quasiLocalInfiniteLBitHilbertEvolution μ t ψ‖ :=
      norm_quasiLocalInfiniteLBitHilbertEvolution_le μ (-t) _

/-- Evolution at each time is a unitary linear isometric equivalence. -/
noncomputable def quasiLocalInfiniteLBitHilbertUnitary
    (μ : Measure InfiniteLBitConfiguration) (t : ℝ) :
    InfiniteLBitHilbertSpace μ ≃ₗᵢ[ℂ]
      InfiniteLBitHilbertSpace μ where
  toFun := quasiLocalInfiniteLBitHilbertEvolution μ t
  invFun := quasiLocalInfiniteLBitHilbertEvolution μ (-t)
  left_inv := quasiLocalInfiniteLBitHilbertEvolution_neg_left μ t
  right_inv := quasiLocalInfiniteLBitHilbertEvolution_neg_right μ t
  map_add' := (quasiLocalInfiniteLBitHilbertEvolution μ t).map_add
  map_smul' := (quasiLocalInfiniteLBitHilbertEvolution μ t).map_smul
  norm_map' := norm_quasiLocalInfiniteLBitHilbertEvolution μ t

/-- Pointwise continuity of the infinite-volume Schrödinger phase in time. -/
theorem continuous_quasiLocalInfiniteLBitPhase_time
    (σ : InfiniteLBitConfiguration) :
    Continuous (fun t : ℝ => quasiLocalInfiniteLBitPhase t σ) := by
  unfold quasiLocalInfiniteLBitPhase
  fun_prop

/-- **Strong continuity.**  Every `L²` orbit is continuous in Hilbert norm. -/
theorem continuous_quasiLocalInfiniteLBitHilbertEvolution_time
    (μ : Measure InfiniteLBitConfiguration)
    (ψ : InfiniteLBitHilbertSpace μ) :
    Continuous
      (fun t : ℝ =>
        quasiLocalInfiniteLBitHilbertEvolution μ t ψ) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact tendsto_lpBoundedMulCLM_apply
    (fun s => (continuous_quasiLocalInfiniteLBitPhase s).measurable)
    (continuous_quasiLocalInfiniteLBitPhase t).measurable
    zero_le_one
    (fun _ _ => by simp)
    (fun _ => by simp)
    (fun σ => (continuous_quasiLocalInfiniteLBitPhase_time σ).continuousAt)
    ψ

/-- **Standard infinite-volume Hilbert dynamics capstone.**  The same infinite l-bit energy is a
bounded self-adjoint `L²` Hamiltonian and generates a strongly continuous unitary group. -/
theorem quasiLocalInfiniteLBitHilbertDynamicsLaw
    (μ : Measure InfiniteLBitConfiguration) :
    IsSelfAdjoint (quasiLocalInfiniteLBitHamiltonian μ) ∧
    (∀ t s ψ,
      quasiLocalInfiniteLBitHilbertEvolution μ (t + s) ψ =
        quasiLocalInfiniteLBitHilbertEvolution μ t
          (quasiLocalInfiniteLBitHilbertEvolution μ s ψ)) ∧
    (∀ t ψ,
      ‖quasiLocalInfiniteLBitHilbertEvolution μ t ψ‖ = ‖ψ‖) ∧
    (∀ ψ,
      Continuous
        (fun t : ℝ =>
          quasiLocalInfiniteLBitHilbertEvolution μ t ψ)) := by
  exact ⟨quasiLocalInfiniteLBitHamiltonian_isSelfAdjoint μ,
    fun t s ψ => quasiLocalInfiniteLBitHilbertEvolution_add μ t s ψ,
    fun t ψ => norm_quasiLocalInfiniteLBitHilbertEvolution μ t ψ,
    continuous_quasiLocalInfiniteLBitHilbertEvolution_time μ⟩

end

end GaloisForLFunctions.HTGeometry

