import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinEnergy
import GaloisForLFunctions.HTGeometry.GomesQubitGibbsClosure

/-!
# Exact Landau–Lifshitz spin / qubit Gibbs correspondence

Applications of the conservative–dissipative spin mechanism in Schaffer–Exl,
arXiv:2609.04530, to the corpus's Böttcher stereographic flow and Gomes qubit
Gibbs closure. The spin latitude is a Gibbs Z expectation; squared torque is
its genuine quantum variance. The full pure spin is not identified with the
mixed Gibbs density. All parameters are unrestricted; every proof is closed.
-/

set_option autoImplicit false
open scoped Matrix RealInnerProductSpace Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- Unrestricted logarithmic amplitude and phase for a nonzero stereographic spin coordinate. -/
def spinLogSeed (x phase : ℝ) : ℂ := Complex.exp ((x : ℂ) + (phase : ℂ) * Complex.I)

/-- The initial phase has no effect on the chart radius. -/
theorem spinLogSeed_norm_sq (x phase : ℝ) : ‖spinLogSeed x phase‖ ^ 2 = Real.exp (2 * x) := by
  rw [spinLogSeed, Complex.norm_exp]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- Exponential latitude odds are the hyperbolic tangent polarization. -/
theorem spinLatitude_exp_tanh (b : ℝ) :
    (Real.exp (2 * b) - 1) / (1 + Real.exp (2 * b)) = Real.tanh b := by
  rw [Real.tanh_eq, Real.exp_neg]
  have he : Real.exp (2 * b) = Real.exp b ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  have hb := Real.exp_ne_zero b
  have hd : 1 + Real.exp b ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- Exact hyperbolic-tangent spin latitude, including zero damping and arbitrary initial phase. -/
theorem spinSphereFlow_log_latitude (a x phase t : ℝ) :
    spinSphereFlow a (spinLogSeed x phase) t (2 : Fin 3) = Real.tanh (x - a ^ 2 * t) := by
  rw [spinSphereFlow_energy, spinLogSeed_norm_sq]
  have he : Real.exp (-2 * a ^ 2 * t) * Real.exp (2 * x) = Real.exp (2 * (x - a ^ 2 * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, spinLatitude_exp_tanh]

/-- The zero-coupling qubit Gibbs mean has its signed hyperbolic-tangent formula everywhere. -/
theorem qubitMean_zero_coupling (b : ℝ) : qubitMean 0 b = Real.tanh b := by
  rw [qubitMean, qubitRadius, zero_pow (two_ne_zero : (2 : ℕ) ≠ 0), add_zero, Real.sqrt_sq_eq_abs]
  by_cases hb : b = 0
  · subst b
    simp
  · rcases le_total 0 b with hpos | hneg
    · rw [abs_of_nonneg hpos, div_self hb, one_mul]
    · simp [abs_of_nonpos hneg, Real.tanh_neg, hb]

/-- Spin latitude is the literal Z expectation of the existing zero-coupling qubit Gibbs state. -/
theorem spinSphereFlow_gibbs_Z (a x phase t : ℝ) :
    spinSphereFlow a (spinLogSeed x phase) t (2 : Fin 3) =
      (Matrix.trace (qubitDensity 0 (x - a ^ 2 * t) * QuantumAlg.pauliZ)).re := by
  rw [spinSphereFlow_log_latitude, gomesQubitDensity_expectation_Z, qubitMean_zero_coupling]

/-- The north-directed torque and latitude form the exact Euclidean spin-length decomposition. -/
theorem spinTorqueEnergy_add_latitude_sq (m : EuclideanSpace ℝ (Fin 3)) :
    spinTorqueEnergy m + m 2 ^ 2 = ‖m‖ ^ 2 := by
  rw [spinTorqueEnergy_components, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

/-- Actual quantum Z variance in the existing zero-coupling Gibbs density. -/
def qubitThermalZVariance (b : ℝ) : ℝ :=
  (Matrix.trace (qubitDensity 0 b * (QuantumAlg.pauliZ * QuantumAlg.pauliZ))).re -
    (Matrix.trace (qubitDensity 0 b * QuantumAlg.pauliZ)).re ^ 2

/-- The Gibbs Z variance is one minus its squared signed polarization. -/
theorem qubitThermalZVariance_eq (b : ℝ) :
    qubitThermalZVariance b = 1 - Real.tanh b ^ 2 := by
  have hZ : QuantumAlg.pauliZ * QuantumAlg.pauliZ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    simpa [qubitHamiltonian, qubitRadius] using qubitHamiltonian_sq 0 1
  rw [qubitThermalZVariance, hZ, Matrix.mul_one, gomesQubitDensity_trace_one,
    gomesQubitDensity_expectation_Z, qubitMean_zero_coupling]
  rfl

/-- Squared spin torque is precisely the quantum Gibbs variance at the matching bias. -/
theorem spinTorqueEnergy_gibbs_variance (a x phase t : ℝ) :
    spinTorqueEnergy (spinSphereFlow a (spinLogSeed x phase) t) =
      qubitThermalZVariance (x - a ^ 2 * t) := by
  have h := spinTorqueEnergy_add_latitude_sq (spinSphereFlow a (spinLogSeed x phase) t)
  rw [spinSphereFlow_norm, spinSphereFlow_log_latitude] at h
  rw [qubitThermalZVariance_eq]
  linarith

/-- The homogeneous denominator-one trajectory is the exact finite stereographic trajectory. -/
theorem projectiveSpinFlow_one (a : ℝ) (z : ℂ) (t : ℝ) :
    projectiveSpinFlow a z 1 t = spinSphereFlow a z t := by
  rw [projectiveSpinFlow_chart, if_neg one_ne_zero, div_one]

/-- The paper's spin energy loss is a genuine Gibbs-variance loss along the existing qubit family. -/
theorem hasDerivAt_spinSphereFlow_gibbs_energy (a x phase t : ℝ) :
    HasDerivAt (fun s => spinSphereFlow a (spinLogSeed x phase) s (2 : Fin 3))
      (-a ^ 2 * qubitThermalZVariance (x - a ^ 2 * t)) t := by
  have h := hasDerivAt_projectiveSpinFlow_energy a (spinLogSeed x phase) 1 t
  simpa only [projectiveSpinFlow_one, spinTorqueEnergy_gibbs_variance] using h

/-- Exact integrated Gibbs-variance interpretation of the spin energy drop. -/
theorem spinSphereFlow_integral_gibbs_variance (a x phase s t : ℝ) :
    (∫ v in s..t, a ^ 2 * qubitThermalZVariance (x - a ^ 2 * v)) =
      spinSphereFlow a (spinLogSeed x phase) s (2 : Fin 3) -
        spinSphereFlow a (spinLogSeed x phase) t (2 : Fin 3) := by
  simpa only [projectiveSpinFlow_one, spinTorqueEnergy_gibbs_variance] using
    projectiveSpinFlow_integral_loss a (spinLogSeed x phase) 1 s t

/-- The existing quantum Jeffreys divergence is elapsed damping times the spin energy drop. -/
theorem spinSphereFlow_quantum_jeffreys (a x phase s t : ℝ) :
    qubitQuantumJeffreys 0 (x - a ^ 2 * s) (x - a ^ 2 * t) =
      a ^ 2 * (t - s) *
        (spinSphereFlow a (spinLogSeed x phase) s (2 : Fin 3) -
          spinSphereFlow a (spinLogSeed x phase) t (2 : Fin 3)) := by
  rw [gomesQubitJeffreys_closed, qubitMean_zero_coupling, qubitMean_zero_coupling,
    spinSphereFlow_log_latitude, spinSphereFlow_log_latitude]
  ring

end
end GaloisForLFunctions.HTGeometry.SchafferExl
