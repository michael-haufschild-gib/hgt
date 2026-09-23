import Mathlib

/-!
# Energy and clock geometry of the Coppo--Pranzini--Verrucchi map

Exact algebra behind arXiv:2601.07437, equations (16)--(19) and (32).
Positive physical constants are parametrized by exponentials, so every result is
unconditional. The map preserves energy and the `(p,q)` area orientation; the
usual `(q,p)` Hamiltonian orientation requires reversing the clock parameter.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.CPV

/-- Constant-force Hamiltonian, with logarithmic mass and acceleration. -/
def energy (mu alpha p q : ℝ) : ℝ :=
  p ^ (2 : ℕ) / (2 * Real.exp mu) + Real.exp mu * Real.exp alpha * q

/-- Momentum in equation (16). -/
def momentum (mu alpha j v : ℝ) : ℝ :=
  Real.exp mu * Real.exp alpha * v / Real.exp j

/-- Position in equation (17), before imposing the exterior-domain restriction. -/
def position (mu alpha j v w : ℝ) : ℝ :=
  Real.exp j * w / (Real.exp mu * Real.exp alpha) -
    Real.exp alpha / 2 * (v / Real.exp j) ^ (2 : ℕ)

/-- The coordinate transformation exactly transports the Hamiltonian. -/
theorem energy_map (mu alpha j v w : ℝ) :
    energy mu alpha (momentum mu alpha j v) (position mu alpha j v w) =
      Real.exp j * w := by
  unfold energy momentum position
  field_simp
  ring

/-- Inverse time coordinate recovered from particle momentum. -/
def inverseV (mu alpha j p : ℝ) : ℝ :=
  Real.exp j * p / (Real.exp mu * Real.exp alpha)

/-- Inverse energy coordinate recovered from the particle Hamiltonian. -/
def inverseW (mu alpha j p q : ℝ) : ℝ := energy mu alpha p q / Real.exp j

@[simp] theorem momentum_inverseV (mu alpha j p : ℝ) :
    momentum mu alpha j (inverseV mu alpha j p) = p := by
  unfold momentum inverseV
  field_simp

@[simp] theorem position_inverse (mu alpha j p q : ℝ) :
    position mu alpha j (inverseV mu alpha j p) (inverseW mu alpha j p q) = q := by
  unfold position inverseV inverseW energy
  field_simp
  ring

@[simp] theorem inverseV_momentum (mu alpha j v : ℝ) :
    inverseV mu alpha j (momentum mu alpha j v) = v := by
  unfold inverseV momentum
  field_simp

@[simp] theorem inverseW_map (mu alpha j v w : ℝ) :
    inverseW mu alpha j (momentum mu alpha j v) (position mu alpha j v w) = w := by
  rw [inverseW, energy_map]
  field_simp

/-- The map is an explicit equivalence of real planes. -/
def phaseEquiv (mu alpha j : ℝ) : (ℝ × ℝ) ≃ (ℝ × ℝ) where
  toFun x := (momentum mu alpha j x.1, position mu alpha j x.1 x.2)
  invFun y := (inverseV mu alpha j y.1, inverseW mu alpha j y.1 y.2)
  left_inv x := by simp
  right_inv y := by simp

/-- Exact exterior-domain boundary at fixed clock energy. -/
theorem exterior_iff (mu alpha j v w : ℝ) :
    0 < position mu alpha j v w ↔
      momentum mu alpha j v ^ (2 : ℕ) < 2 * Real.exp mu * (Real.exp j * w) := by
  have he := energy_map mu alpha j v w
  unfold energy at he
  have hm := Real.exp_pos mu
  have ha := Real.exp_pos alpha
  have he' : momentum mu alpha j v ^ (2 : ℕ) +
      (2 * Real.exp mu) * (Real.exp mu * Real.exp alpha) *
        position mu alpha j v w = (2 * Real.exp mu) * (Real.exp j * w) := by
    field_simp at he
    nlinarith [he]
  constructor <;> intro h
  · nlinarith [mul_pos (mul_pos (by positivity : 0 < 2 * Real.exp mu)
      (mul_pos hm ha)) h]
  · have hc : 0 < (2 * Real.exp mu) * (Real.exp mu * Real.exp alpha) := by positivity
    nlinarith

/-- Every exterior particle state has strictly positive inverse clock energy. -/
theorem inverseW_exterior_pos (mu alpha j p x : ℝ) :
    0 < inverseW mu alpha j p (Real.exp x) := by
  unfold inverseW energy
  positivity

/-- A positive-half-plane family whose image lies strictly inside the horizon. -/
theorem halfPlane_not_all_exterior (mu alpha j : ℝ) :
    0 < Real.exp mu * Real.exp alpha ^ (2 : ℕ) / Real.exp j ∧
    position mu alpha j (2 * Real.exp j)
      (Real.exp mu * Real.exp alpha ^ (2 : ℕ) / Real.exp j) = -Real.exp alpha := by
  constructor
  · positivity
  · unfold position
    field_simp
    ring

/-- Derivative of the momentum with respect to the clock coordinate. -/
theorem momentum_hasDerivAt (mu alpha j v : ℝ) :
    HasDerivAt (momentum mu alpha j)
      (Real.exp mu * Real.exp alpha / Real.exp j) v := by
  convert! ((hasDerivAt_id v).const_mul (Real.exp mu * Real.exp alpha)).div_const
    (Real.exp j) using 1
  simp

/-- Position derivative in the time coordinate. -/
theorem position_v_hasDerivAt (mu alpha j v w : ℝ) :
    HasDerivAt (fun x => position mu alpha j x w)
      (-Real.exp alpha * v / Real.exp j ^ (2 : ℕ)) v := by
  convert! (hasDerivAt_const v (Real.exp j * w / (Real.exp mu * Real.exp alpha))).sub
    ((((hasDerivAt_id v).div_const (Real.exp j)).pow 2).const_mul (Real.exp alpha / 2)) using 1
  simp only [id_eq]
  ring

/-- Position derivative in the energy coordinate. -/
theorem position_w_hasDerivAt (mu alpha j v w : ℝ) :
    HasDerivAt (position mu alpha j v)
      (Real.exp j / (Real.exp mu * Real.exp alpha)) w := by
  convert! (((hasDerivAt_id w).const_mul (Real.exp j)).div_const
      (Real.exp mu * Real.exp alpha)).sub_const (Real.exp alpha / 2 * (v / Real.exp j) ^ (2 : ℕ))
    using 1
  simp

/-- Jacobian determinant in the `(p,q)` order is exactly one. -/
theorem clock_jacobian (mu alpha j : ℝ) :
    (Real.exp mu * Real.exp alpha / Real.exp j) *
      (Real.exp j / (Real.exp mu * Real.exp alpha)) = 1 := by
  field_simp

/-- Exact constant-force Hamiltonian flow for arbitrary initial state. -/
def flow (mu alpha t : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.1 - Real.exp mu * Real.exp alpha * t,
   x.2 + x.1 / Real.exp mu * t - Real.exp alpha / 2 * t ^ (2 : ℕ))

@[simp] theorem flow_zero (mu alpha : ℝ) (x : ℝ × ℝ) : flow mu alpha 0 x = x := by
  simp [flow]

/-- Time addition is exactly composition of the accelerated flow. -/
theorem flow_add (mu alpha s t : ℝ) (x : ℝ × ℝ) :
    flow mu alpha (s + t) x = flow mu alpha s (flow mu alpha t x) := by
  ext <;> simp only [flow] <;> field_simp <;> ring

/-- Energy is conserved along every orbit. -/
theorem energy_flow (mu alpha t : ℝ) (x : ℝ × ℝ) :
    energy mu alpha (flow mu alpha t x).1 (flow mu alpha t x).2 =
      energy mu alpha x.1 x.2 := by
  unfold flow energy
  dsimp
  field_simp
  ring

/-- The momentum component satisfies Hamilton's force equation. -/
theorem flow_momentum_hasDerivAt (mu alpha t : ℝ) (x : ℝ × ℝ) :
    HasDerivAt (fun s => (flow mu alpha s x).1)
      (-(Real.exp mu * Real.exp alpha)) t := by
  convert! (hasDerivAt_const t x.1).sub
    ((hasDerivAt_id t).const_mul (Real.exp mu * Real.exp alpha)) using 1
  simp

/-- The position component satisfies Hamilton's velocity equation. -/
theorem flow_position_hasDerivAt (mu alpha t : ℝ) (x : ℝ × ℝ) :
    HasDerivAt (fun s => (flow mu alpha s x).2)
      ((flow mu alpha t x).1 / Real.exp mu) t := by
  convert! ((hasDerivAt_const t x.2).add
    ((hasDerivAt_id t).const_mul (x.1 / Real.exp mu))).sub
    (((hasDerivAt_id t).pow 2).const_mul (Real.exp alpha / 2)) using 1
  simp only [flow, id_eq]
  field_simp
  ring

/-- The paper's coordinate orbit is the zero-momentum orbit with reversed time. -/
theorem map_eq_reverse_flow (mu alpha j t w : ℝ) :
    (momentum mu alpha j (Real.exp j * t),
      position mu alpha j (Real.exp j * t) w) =
    flow mu alpha (-t) (0, Real.exp j * w / (Real.exp mu * Real.exp alpha)) := by
  ext <;> dsimp [momentum, position, flow] <;> field_simp <;> ring

/-- Residual produced by the extra mass factor in the printed equation (32). -/
theorem printed_trajectory_energy_defect (mu alpha E t : ℝ) :
    energy mu alpha (Real.exp mu * Real.exp alpha * t)
      (E / (Real.exp mu * Real.exp alpha) -
        Real.exp mu * Real.exp alpha / 2 * t ^ (2 : ℕ)) - E =
      Real.exp mu * Real.exp alpha ^ (2 : ℕ) * (1 - Real.exp mu) * t ^ (2 : ℕ) / 2 := by
  unfold energy
  field_simp
  ring

end GaloisForLFunctions.HTGeometry.CPV
