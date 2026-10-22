import Mathlib.Analysis.Complex.Exponential
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic.Module

/-!
# Suzuki two-port projective wedge law

The ground multiplier in the restricted-Weil equation is common to every ground coordinate.
Projective geometry therefore removes it exactly.  After the multiplier is removed, the literal
antipodal port decomposition

`β(x) = exp(iax) u(x) + exp(-iax) v(x)`

has an aperture-leading exterior derivative `-2ia (u ∧ v)` plus four transport terms.  This file
proves both statements in the universal exterior algebra of an arbitrary complex module.  Hence no
coordinate choice, ground-multiplicity bound, analytic regularity assumption, RH hypothesis, or
numerical computation enters the identities.

The results are the dependency-closed algebraic content of Corollaries G.3--G.4 in the
coalescing-anchor paper card.  They do not assert that Suzuki's Hardy ports have derivatives; that
separate analytic regularity theorem is exactly the G.5 interface.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-! ## Universal two-vector exterior product -/

/-- Universal exterior product of two ground-coordinate vectors. -/
def suzukiPortWedge (u v : V) : ExteriorAlgebra ℂ V :=
  ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ v

theorem suzukiPortWedge_add_left (u v w : V) :
    suzukiPortWedge (u + v) w = suzukiPortWedge u w + suzukiPortWedge v w := by
  simp [suzukiPortWedge, add_mul]

theorem suzukiPortWedge_add_right (u v w : V) :
    suzukiPortWedge u (v + w) = suzukiPortWedge u v + suzukiPortWedge u w := by
  simp [suzukiPortWedge, mul_add]

theorem suzukiPortWedge_smul_left (a : ℂ) (u v : V) :
    suzukiPortWedge (a • u) v = a • suzukiPortWedge u v := by
  simp [suzukiPortWedge]

theorem suzukiPortWedge_smul_right (a : ℂ) (u v : V) :
    suzukiPortWedge u (a • v) = a • suzukiPortWedge u v := by
  simp only [suzukiPortWedge, map_smul, Algebra.smul_def]
  rw [← mul_assoc, ← Algebra.commutes a (ExteriorAlgebra.ι ℂ u), mul_assoc]

@[simp] theorem suzukiPortWedge_self (u : V) :
    suzukiPortWedge u u = 0 := by
  simp [suzukiPortWedge]

theorem suzukiPortWedge_swap (u v : V) :
    suzukiPortWedge v u = -suzukiPortWedge u v := by
  rw [suzukiPortWedge, suzukiPortWedge]
  exact eq_neg_of_add_eq_zero_right
    (ExteriorAlgebra.ι_add_mul_swap (R := ℂ) u v)

/-! ## Common-gauge projective cancellation -/

/-- **Exact common-gauge cancellation.**  Differentiating a common scalar multiple contributes
the radial term `dm • u`; its exterior product with the carrier vanishes.  The transverse wedge is
therefore multiplied only by `m²`. -/
theorem suzukiPortWedge_commonGauge
    (m dm : ℂ) (u du : V) :
    suzukiPortWedge (m • u) (dm • u + m • du) =
      (m ^ (2 : ℕ)) • suzukiPortWedge u du := by
  simp only [suzukiPortWedge_add_right, suzukiPortWedge_smul_left,
    suzukiPortWedge_smul_right, suzukiPortWedge_self, smul_zero, zero_add, smul_smul]
  rw [pow_two]

/-- A nonzero common multiplier preserves the carrier line exactly. -/
theorem span_suzukiCommonGauge_eq
    {m : ℂ} (hm : m ≠ 0) (u : V) :
    Submodule.span ℂ {m • u} = Submodule.span ℂ {u} := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact Submodule.smul_mem _ m (Submodule.subset_span (Set.mem_singleton u))
  · rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    have hmemb : m • u ∈ Submodule.span ℂ {m • u} :=
      Submodule.subset_span (Set.mem_singleton (m • u))
    have hinv := Submodule.smul_mem (Submodule.span ℂ {m • u}) m⁻¹ hmemb
    simpa [smul_smul, hm] using hinv

/-! ## Literal antipodal phases -/

/-- Right-moving aperture phase `exp(iax)`. -/
def suzukiRightPortPhase (a x : ℝ) : ℂ :=
  Complex.exp (I * ((a * x : ℝ) : ℂ))

/-- Left-moving aperture phase `exp(-iax)`. -/
def suzukiLeftPortPhase (a x : ℝ) : ℂ :=
  Complex.exp (-I * ((a * x : ℝ) : ℂ))

@[simp] theorem suzukiRightPortPhase_mul_leftPortPhase (a x : ℝ) :
    suzukiRightPortPhase a x * suzukiLeftPortPhase a x = 1 := by
  rw [suzukiRightPortPhase, suzukiLeftPortPhase, ← Complex.exp_add]
  ring_nf
  simp

@[simp] theorem suzukiLeftPortPhase_mul_rightPortPhase (a x : ℝ) :
    suzukiLeftPortPhase a x * suzukiRightPortPhase a x = 1 := by
  rw [mul_comm, suzukiRightPortPhase_mul_leftPortPhase]

/-- Two-port ground residual vector at one physical frequency. -/
def suzukiTwoPortCarrier (a x : ℝ) (u v : V) : V :=
  suzukiRightPortPhase a x • u + suzukiLeftPortPhase a x • v

/-- Formal derivative of the two-port carrier when `du,dv` are the two port derivatives. -/
def suzukiTwoPortVelocity (a x : ℝ) (u v du dv : V) : V :=
  suzukiRightPortPhase a x • ((I * (a : ℂ)) • u + du) +
    suzukiLeftPortPhase a x • ((-(I * (a : ℂ))) • v + dv)

/-- Four non-aperture-leading transport wedges in the two-port derivative. -/
def suzukiTwoPortWedgeRemainder (a x : ℝ) (u v du dv : V) :
    ExteriorAlgebra ℂ V :=
  (suzukiRightPortPhase a x) ^ (2 : ℕ) • suzukiPortWedge u du +
    (suzukiLeftPortPhase a x) ^ (2 : ℕ) • suzukiPortWedge v dv +
      suzukiPortWedge u dv + suzukiPortWedge v du

/-! ## Exact port-wedge decomposition -/

/-- Algebraic two-port identity with any reciprocal phase pair. -/
theorem suzukiPortWedge_reciprocalPhases
    (apertureFrequency p q : ℂ) (u v du dv : V) (hpq : p * q = 1) :
    suzukiPortWedge (p • u + q • v)
        (p • (apertureFrequency • u + du) +
          q • ((-apertureFrequency) • v + dv)) =
      (-2 * apertureFrequency) • suzukiPortWedge u v +
        (p ^ (2 : ℕ)) • suzukiPortWedge u du +
          (q ^ (2 : ℕ)) • suzukiPortWedge v dv +
            suzukiPortWedge u dv + suzukiPortWedge v du := by
  have hpAq : p * apertureFrequency * q = apertureFrequency := by
    calc
      p * apertureFrequency * q = apertureFrequency * (p * q) := by ring
      _ = apertureFrequency := by rw [hpq, mul_one]
  simp only [suzukiPortWedge_add_left, suzukiPortWedge_add_right,
    suzukiPortWedge_smul_left, suzukiPortWedge_smul_right, suzukiPortWedge_self,
    smul_zero, add_zero, smul_smul]
  rw [suzukiPortWedge_swap]
  simp only [zero_add, smul_add, smul_smul, smul_neg]
  match_scalars <;> ring_nf
  all_goals first | exact hpq | simpa [mul_comm] using hpq | rw [hpAq]

/-- **Exact Suzuki two-port residual identity.**  For the literal antipodal phases, the aperture
derivative contributes exactly `-2ia (u ∧ v)` and every remaining term is recorded in
`suzukiTwoPortWedgeRemainder`. -/
theorem suzukiTwoPortCarrier_wedge_velocity
    (a x : ℝ) (u v du dv : V) :
    suzukiPortWedge (suzukiTwoPortCarrier a x u v)
        (suzukiTwoPortVelocity a x u v du dv) =
      (-2 * I * (a : ℂ)) • suzukiPortWedge u v +
        suzukiTwoPortWedgeRemainder a x u v du dv := by
  rw [suzukiTwoPortCarrier, suzukiTwoPortVelocity, suzukiTwoPortWedgeRemainder]
  have h := suzukiPortWedge_reciprocalPhases
    (V := V) (I * (a : ℂ)) (suzukiRightPortPhase a x)
      (suzukiLeftPortPhase a x) u v du dv
      (suzukiRightPortPhase_mul_leftPortPhase a x)
  simpa only [mul_assoc, add_assoc] using h

/-! ## Quantitative death criterion -/

/-- Projective speed written as transverse wedge size divided by carrier size squared. -/
def suzukiProjectiveWedgeSpeed (wedgeSize carrierSize : ℝ) : ℝ :=
  wedgeSize / carrierSize ^ (2 : ℕ)

/-- **Port-wedge death inequality.**  If the aperture-leading wedge dominates the remainder by
`δ a S²` and the carrier norm is at most `S`, then projective speed is at least `δ a`.  This is the
exact scalar implication used after the universal wedge identity. -/
theorem suzukiProjectiveWedgeSpeed_ge_aperture
    {a δ S carrierSize wedgeSize leadingSize remainderSize : ℝ}
    (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hS : 0 ≤ S) (hcarrier : 0 < carrierSize)
    (hcarrierS : carrierSize ≤ S)
    (hdominates : δ * a * S ^ (2 : ℕ) ≤ 2 * a * leadingSize - remainderSize)
    (hwedge : 2 * a * leadingSize - remainderSize ≤ wedgeSize) :
    δ * a ≤ suzukiProjectiveWedgeSpeed wedgeSize carrierSize := by
  have hδa : 0 ≤ δ * a := mul_nonneg hδ ha
  have hsq : carrierSize ^ (2 : ℕ) ≤ S ^ (2 : ℕ) := by nlinarith
  have hbudget : δ * a * carrierSize ^ (2 : ℕ) ≤ wedgeSize := by
    calc
      δ * a * carrierSize ^ (2 : ℕ) ≤ δ * a * S ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hsq hδa
      _ ≤ 2 * a * leadingSize - remainderSize := hdominates
      _ ≤ wedgeSize := hwedge
  rw [suzukiProjectiveWedgeSpeed, le_div_iff₀ (sq_pos_of_pos hcarrier)]
  exact hbudget

end GaloisForLFunctions.RHTower
