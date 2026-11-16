import GaloisForLFunctions.HTGeometry.JordanWignerSpinFermionBridge
import Mathlib.Analysis.Matrix.Order

/-!
# Cubic Majorana anticommutators have no six-generator term

Moving one odd cubic word through another cancels the leading product. The
remainder is an explicit sum of nine contractions times quartic words. This
is the algebraic cancellation behind the partial three-particle positivity
conditions, realized here by the existing Jordan--Wigner matrices.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.Quantum

open Matrix
open scoped ComplexOrder

/-- The leading terms cancel in the anticommutator of two cubic words. -/
theorem cubic_anticommutator_expansion {R : Type*} [Ring R] (a b c d e f : R) :
    (a * b * c) * (d * e * f) + (d * e * f) * (a * b * c) =
      a * b * (c * d + d * c) * e * f -
      a * (b * d + d * b) * c * e * f +
      (a * d + d * a) * b * c * e * f -
      d * a * b * (c * e + e * c) * f +
      d * a * (b * e + e * b) * c * f -
      d * (a * e + e * a) * b * c * f +
      d * e * a * b * (c * f + f * c) -
      d * e * a * (b * f + f * b) * c +
      d * e * (a * f + f * a) * b * c := by
  noncomm_ring

/-- The scalar CAR contraction of two concrete Majorana labels. -/
def majoranaContraction {n : ℕ} (p q : Fin n × Fin 2) : ℂ :=
  if p = q then 2 else 0

theorem jordanWignerMajorana_anticommutator {n : ℕ} (p q : Fin n × Fin 2) :
    jordanWignerMajorana p * jordanWignerMajorana q +
      jordanWignerMajorana q * jordanWignerMajorana p =
        majoranaContraction p q • (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) := by
  by_cases h : p = q
  · subst q
    rw [jordanWignerMajorana_sq]
    simp only [majoranaContraction, if_pos rfl, two_smul]
  · rw [jordanWignerMajorana_anticommutes h]
    simp [majoranaContraction, h]

local notation "γ" => jordanWignerMajorana
local notation "κ" => majoranaContraction

/-- Exact nine-term quartic remainder, valid also for repeated Majorana indices. -/
theorem cubicMajorana_anticommutator {n : ℕ} (a b c d e f : Fin n × Fin 2) :
    (γ a * γ b * γ c) * (γ d * γ e * γ f) +
      (γ d * γ e * γ f) * (γ a * γ b * γ c) =
      κ c d • (γ a * γ b * γ e * γ f) -
      κ b d • (γ a * γ c * γ e * γ f) +
      κ a d • (γ b * γ c * γ e * γ f) -
      κ c e • (γ d * γ a * γ b * γ f) +
      κ b e • (γ d * γ a * γ c * γ f) -
      κ a e • (γ d * γ b * γ c * γ f) +
      κ c f • (γ d * γ e * γ a * γ b) -
      κ b f • (γ d * γ e * γ a * γ c) +
      κ a f • (γ d * γ e * γ b * γ c) := by
  rw [cubic_anticommutator_expansion]
  simp only [jordanWignerMajorana_anticommutator, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul]

/-- Particle and hole squares are jointly positive for every polynomial operator. -/
theorem particleHoleSquare_posSemidef {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) : (A * Aᴴ + Aᴴ * A).PosSemidef :=
  (Matrix.posSemidef_self_mul_conjTranspose A).add
    (Matrix.posSemidef_conjTranspose_mul_self A)

end GaloisForLFunctions.HTGeometry.Quantum
