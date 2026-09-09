import GaloisForLFunctions.HTGeometry.GomesDilatonCommutatorObservations

/-!
# What the full first-order connection recovers from a dilaton profile

The reconstruction experiment prompted by arXiv:2607.24901v1 section 4 distinguishes the
full first-order connection from its commutator. The first-order Schwartz operator loses
only a constant log-weight; the commutator loses an affine log-weight. The constant changes
the positive density amplitude while leaving both factors and the Hamiltonian unchanged.
One density value restores exact profile recovery from the full first-order operator.
-/

noncomputable section
open Polynomial
open scoped SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- The actual first-order Schwartz connection determines precisely the derivative of the profile. -/
theorem gomesDilatonConnection_eq_iff (H K : ℝ[X]) :
    dilatonSuperchargeCLM H = dilatonSuperchargeCLM K ↔ H.derivative = K.derivative := by
  constructor
  · intro h
    apply Polynomial.funext
    intro x
    have hx := congrArg (fun T : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) => T gaussianSchwartz x) h
    rw [dilatonSuperchargeCLM_apply, dilatonSuperchargeCLM_apply] at hx
    have he : ((H.derivative.eval x : ℝ) : ℂ) / 2 * gaussianSchwartz x =
        ((K.derivative.eval x : ℝ) : ℂ) / 2 * gaussianSchwartz x := by
      linear_combination -hx
    have hg : gaussianSchwartz x ≠ 0 := by
      rw [gaussianSchwartz_apply]
      exact Complex.ofReal_ne_zero.mpr (gaussReal_pos x).ne'
    have hd := mul_right_cancel₀ hg he
    have hp : ((H.derivative.eval x : ℝ) : ℂ) = ((K.derivative.eval x : ℝ) : ℂ) := by
      linear_combination 2 * hd
    exact_mod_cast hp
  · intro h
    ext ψ x
    simp only [dilatonSuperchargeCLM_apply, h]

/-- The derivative forgets exactly the constant coefficient of a real polynomial profile. -/
theorem gomesDilatonDerivative_eq_iff (H K : ℝ[X]) :
    H.derivative = K.derivative ↔ ∃ c : ℝ, H = K + C c := by
  constructor
  · intro h
    have hz : (H - K).derivative = 0 := by rw [derivative_sub, h, sub_self]
    have hc := eq_C_of_derivative_eq_zero hz
    refine ⟨(H - K).coeff 0, ?_⟩
    linear_combination hc
  · rintro ⟨c, rfl⟩
    simp

/-- Equality of full first-order connections is precisely constant-profile ambiguity. -/
theorem gomesDilatonConnection_constant_iff (H K : ℝ[X]) :
    dilatonSuperchargeCLM H = dilatonSuperchargeCLM K ↔ ∃ c : ℝ, H = K + C c := by
  rw [gomesDilatonConnection_eq_iff, gomesDilatonDerivative_eq_iff]

/-- Adding any constant log-amplitude leaves the full first-order connection unchanged. -/
theorem gomesDilatonConnection_constant (H : ℝ[X]) (c : ℝ) :
    dilatonSuperchargeCLM (H + C c) = dilatonSuperchargeCLM H :=
  (gomesDilatonConnection_constant_iff _ _).mpr ⟨c, rfl⟩

/-- The second first-order factor is also insensitive to constant log-amplitude. -/
theorem gomesDilatonAdjointCharge_constant (H : ℝ[X]) (c : ℝ) :
    dilatonAdjointChargeCLM (H + C c) = dilatonAdjointChargeCLM H := by
  ext ψ x
  simp only [dilatonAdjointChargeCLM_apply, derivative_add, derivative_C, add_zero]

/-- The exact Hamiltonian is unchanged throughout the constant-amplitude family. -/
theorem gomesDilatonHamiltonian_constant (H : ℝ[X]) (c : ℝ) :
    dilatonHamiltonianCLM (H + C c) = dilatonHamiltonianCLM H := by
  rw [dilatonHamiltonianCLM, dilatonHamiltonianCLM,
    gomesDilatonAdjointCharge_constant, gomesDilatonConnection_constant]

/-- The invisible constant does change the density by its exact exponential scale. -/
theorem gomesDilatonWeight_constant (H : ℝ[X]) (c x : ℝ) :
    dilatonWeight (H + C c) x = Real.exp c * dilatonWeight H x := by
  simp only [dilatonWeight, eval_add, eval_C, Real.exp_add]
  ring

/-- A constant perturbation preserves the complete density exactly when it is zero. -/
theorem gomesDilatonWeight_constant_eq_iff (H : ℝ[X]) (c : ℝ) :
    dilatonWeight (H + C c) = dilatonWeight H ↔ c = 0 := by
  constructor
  · intro h
    have hx : Real.exp ((H + C c).eval 0) = Real.exp (H.eval 0) := congrFun h 0
    have he := Real.exp_injective hx
    simp only [eval_add, eval_C] at he
    linarith
  · rintro rfl
    simp

/-- One origin value removes the constant ambiguity of the full first-order connection. -/
theorem gomesDilatonConnection_origin_iff (H K : ℝ[X]) :
    (dilatonSuperchargeCLM H = dilatonSuperchargeCLM K ∧ H.eval 0 = K.eval 0) ↔ H = K := by
  constructor
  · rintro ⟨hc, hv⟩
    obtain ⟨c, h⟩ := (gomesDilatonConnection_constant_iff H K).mp hc
    have he := congrArg (fun p : ℝ[X] => p.eval 0) h
    simp only [eval_add, eval_C] at he
    have hz : c = 0 := by linarith
    simpa only [hz, C_0, add_zero] using h
  · rintro rfl
    exact ⟨rfl, rfl⟩

/-- A single positive density amplitude suffices to restore faithful connection-based recovery. -/
theorem gomesDilatonConnection_density_origin_iff (H K : ℝ[X]) :
    (dilatonSuperchargeCLM H = dilatonSuperchargeCLM K ∧ dilatonWeight H 0 = dilatonWeight K 0) ↔
      H = K := by
  constructor
  · rintro ⟨hc, hw⟩
    have hx : Real.exp (H.eval 0) = Real.exp (K.eval 0) := hw
    exact (gomesDilatonConnection_origin_iff H K).mp ⟨hc, Real.exp_injective hx⟩
  · rintro rfl
    exact ⟨rfl, rfl⟩

/-- The entire density profile itself retains every coefficient of the generating polynomial. -/
theorem gomesDilatonWeight_injective : Function.Injective dilatonWeight := by
  intro H K h
  apply Polynomial.funext
  intro x
  have hx : Real.exp (H.eval x) = Real.exp (K.eval x) := congrFun h x
  exact Real.exp_injective hx

end GaloisForLFunctions.HTGeometry
