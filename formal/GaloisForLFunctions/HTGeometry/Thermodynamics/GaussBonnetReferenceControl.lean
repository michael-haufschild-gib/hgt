import GaloisForLFunctions.HTGeometry.GaussBonnetGibbsAGauge

/-!
# Reference changes across Gauss--Bonnet couplings

The existing logarithmic-entropy Gibbs energy has reference invariance
within each fixed coupling. Across couplings, the shift is quadratic in
the coupling root. The control-covariance law of arXiv:2611.16364, section
4.4, therefore preserves the full family when the source is conjugate to
the squared coupling. A source conjugate to its root cannot absorb this
shift except in the exactly classified zero-shift case.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.Thermodynamics

def egbSquaredCouplingControl (P T Q l z a u : ℝ) : ℝ :=
  egbOffShellGibbsA P T Q a l (Real.exp u) - z * a ^ 2

/-- One constant source translation compensates the entire family in the squared coordinate. -/
theorem egbSquaredCouplingControl_reference_covariance (P T Q l z c a u : ℝ) :
    egbSquaredCouplingControl P T Q (l + c) (z + 4 * Real.pi * T * c) a u =
      egbSquaredCouplingControl P T Q l z a u := by
  unfold egbSquaredCouplingControl
  rw [egbOffShellGibbsA_reference_shift]
  ring

/-- Couplings and radii may both differ in this ordering comparison. -/
theorem egbSquaredCouplingControl_order_covariance (P T Q l z c a b u v : ℝ) :
    egbSquaredCouplingControl P T Q (l + c) (z + 4 * Real.pi * T * c) a u ≤
        egbSquaredCouplingControl P T Q (l + c) (z + 4 * Real.pi * T * c) b v ↔
      egbSquaredCouplingControl P T Q l z a u ≤
        egbSquaredCouplingControl P T Q l z b v := by
  rw [egbSquaredCouplingControl_reference_covariance,
    egbSquaredCouplingControl_reference_covariance]

def egbRootCouplingControl (P T Q l z a u : ℝ) : ℝ :=
  egbOffShellGibbsA P T Q a l (Real.exp u) - z * a

theorem egbRootCouplingControl_reference_defect (P T Q l z c d a u : ℝ) :
    egbRootCouplingControl P T Q (l + c) (z + d) a u -
      egbRootCouplingControl P T Q l z a u =
        4 * Real.pi * a ^ 2 * T * c - d * a := by
  unfold egbRootCouplingControl
  rw [egbOffShellGibbsA_reference_shift]
  ring

/-- A constant root-source change works exactly when the thermal reference shift vanishes. -/
theorem egbRootCouplingControl_constant_compensation_iff (P T Q l z c : ℝ) :
    (∃ d e : ℝ, ∀ a u : ℝ,
      egbRootCouplingControl P T Q (l + c) (z + d) a u -
        egbRootCouplingControl P T Q l z a u = e) ↔ T * c = 0 := by
  simp only [egbRootCouplingControl_reference_defect]
  constructor
  · rintro ⟨d, e, h⟩
    have h₀ := h 0 0
    have h₁ := h 1 0
    have h₂ := h 2 0
    have hz : 4 * Real.pi * (T * c) = 0 := by nlinarith only [h₀, h₁, h₂]
    exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  · intro h
    refine ⟨0, 0, ?_⟩
    intro a u
    calc
      4 * Real.pi * a ^ 2 * T * c - 0 * a = 4 * Real.pi * a ^ 2 * (T * c) := by ring
      _ = 0 := by rw [h, mul_zero]

/-- The squared coordinate retains exact compensation even when root-linear control fails. -/
theorem egb_reference_control_boundary (P t Q l z w : ℝ) :
    (∀ a u, egbSquaredCouplingControl P (Real.exp t) Q (l + Real.exp w)
      (z + 4 * Real.pi * Real.exp t * Real.exp w) a u =
        egbSquaredCouplingControl P (Real.exp t) Q l z a u) ∧
    ¬ (∃ d e : ℝ, ∀ a u : ℝ,
      egbRootCouplingControl P (Real.exp t) Q (l + Real.exp w) (z + d) a u -
        egbRootCouplingControl P (Real.exp t) Q l z a u = e) := by
  constructor
  · exact fun a u => egbSquaredCouplingControl_reference_covariance _ _ _ _ _ _ a u
  · rw [egbRootCouplingControl_constant_compensation_iff]
    exact mul_ne_zero (Real.exp_ne_zero t) (Real.exp_ne_zero w)

#print axioms egbSquaredCouplingControl_order_covariance
#print axioms egbRootCouplingControl_constant_compensation_iff
#print axioms egb_reference_control_boundary

end GaloisForLFunctions.HTGeometry.Thermodynamics
