import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAPeakGibbsAllOrderLimits
import GaloisForLFunctions.QuantumAlg.Primitives.QKernel.Fidelity
import GaloisForLFunctions.QuantumAlg.Primitives.QKernel.Concentration

/-!
# Quantum feature realization of the critical Gibbs profile

A normalized real one-qubit state has cosine overlap. Two tensor
copies therefore have the quartic-cosine fidelity kernel. This is
an exact bridge to the corpus quantum-kernel machinery, not a claim
that the black-hole model has a microscopic two-qubit realization.
-/
noncomputable section
open Real Filter Set
open scoped Topology BigOperators ComplexOrder
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAQubitVector (ψ : ℝ) : QuantumAlg.StateVector (QuantumAlg.Qubits 1) :=
  WithLp.toLp 2 ![(cos ψ : ℂ), (sin ψ : ℂ)]

theorem egbFixedChargeAQubitVector_norm (ψ : ℝ) : ‖egbFixedChargeAQubitVector ψ‖ = 1 := by
  unfold egbFixedChargeAQubitVector
  rw [EuclideanSpace.norm_eq]
  change sqrt (∑ i : Fin 2, ‖(![(cos ψ : ℂ), (sin ψ : ℂ)] : Fin 2 → ℂ) i‖ ^ (2 : ℕ)) = 1
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h : cos ψ ^ (2 : ℕ) + sin ψ ^ (2 : ℕ) = 1 := by linarith [sin_sq_add_cos_sq ψ]
  rw [h, sqrt_one]

def egbFixedChargeAQubitFeature (ψ : ℝ) : QuantumAlg.PureState (QuantumAlg.Qubits 1) :=
  QuantumAlg.PureState.ofVec (egbFixedChargeAQubitVector ψ) (egbFixedChargeAQubitVector_norm ψ)

theorem egbFixedChargeAQubitFeature_inner (ψ θ : ℝ) :
    inner ℂ (egbFixedChargeAQubitFeature ψ) (egbFixedChargeAQubitFeature θ) = (cos (ψ - θ) : ℂ) := by
  change inner ℂ (egbFixedChargeAQubitVector ψ) (egbFixedChargeAQubitVector θ) = _
  unfold egbFixedChargeAQubitVector
  rw [PiLp.inner_apply]
  change (∑ i : Fin 2, inner ℂ ((![(cos ψ : ℂ), (sin ψ : ℂ)] : Fin 2 → ℂ) i)
    ((![(cos θ : ℂ), (sin θ : ℂ)] : Fin 2 → ℂ) i)) = _
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, RCLike.inner_apply, Complex.conj_ofReal]
  rw [cos_sub]
  push_cast
  ring

def egbFixedChargeAPairQubitFeature (ψ : ℝ) : QuantumAlg.PureState (QuantumAlg.Qubits 2) :=
  (egbFixedChargeAQubitFeature ψ).tensor (egbFixedChargeAQubitFeature ψ)

theorem egbFixedChargeAPairQubitFeature_inner (ψ θ : ℝ) :
    inner ℂ (egbFixedChargeAPairQubitFeature ψ) (egbFixedChargeAPairQubitFeature θ) =
      (cos (ψ - θ) ^ (2 : ℕ) : ℂ) := by
  unfold egbFixedChargeAPairQubitFeature
  rw [QuantumAlg.PureState.inner_tensor_tensor, egbFixedChargeAQubitFeature_inner]
  ring

theorem egbFixedChargeAPairQubitFeature_kernel (ψ θ : ℝ) :
    QuantumAlg.quantumKernel egbFixedChargeAPairQubitFeature ψ θ = (cos (ψ - θ) ^ (4 : ℕ) : ℂ) := by
  unfold QuantumAlg.quantumKernel
  rw [egbFixedChargeAPairQubitFeature_inner]
  simp only [map_pow, Complex.conj_ofReal]
  ring

theorem egbFixedChargeAPairQubitFeature_kernel_real (ψ θ : ℝ) :
    (QuantumAlg.quantumKernel egbFixedChargeAPairQubitFeature ψ θ).re = cos (ψ - θ) ^ (4 : ℕ) := by
  rw [egbFixedChargeAPairQubitFeature_kernel]
  norm_cast

theorem egbFixedChargeAQuarticProfile_ryKernel (ψ : ℝ) :
    QuantumAlg.ryKernel 2 (fun _ => ψ) = cos ψ ^ (4 : ℕ) := by
  unfold QuantumAlg.ryKernel
  rw [Fin.prod_const]
  ring

theorem egbFixedChargeAQuarticProfile_gram_posSemidef (n : ℕ) (x : Fin n → ℝ) :
    (Matrix.of (fun i j : Fin n => (cos (x i - x j) ^ (4 : ℕ) : ℂ))).PosSemidef := by
  have h := QuantumAlg.quantumKernel_gram_posSemidef egbFixedChargeAPairQubitFeature x
  simpa only [egbFixedChargeAPairQubitFeature_kernel] using h

end GaloisForLFunctions.HTGeometry
