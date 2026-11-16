import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Convex.Exposed

/-!
# Positive constraints and exact state support

The support mechanism in Mazziotti, arXiv:2611.18503: a positive constraint has
zero expectation precisely when it annihilates the state. Sums of squared
constraints select the common kernel, including every contracted identity.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.Quantum

open Matrix
open scoped ComplexOrder MatrixOrder

variable {ι κ σ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [Fintype σ]

/-- Squared constraint energy, with no normalization imposed on the positive state. -/
def constraintEnergy (C : Matrix κ ι ℂ) (ρ : Matrix ι ι ℂ) : ℝ :=
  (C * ρ * Cᴴ).trace.re

omit [DecidableEq ι] in
theorem constraintEnergy_nonneg (C : Matrix κ ι ℂ)
    {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) : 0 ≤ constraintEnergy C ρ :=
  (RCLike.nonneg_iff.mp (hρ.mul_mul_conjTranspose_same C).trace_nonneg).1

omit [DecidableEq ι] in
/-- The positive quadratic expression is the usual linear expectation of `Cᴴ C`. -/
theorem constraintEnergy_eq_trace (C : Matrix κ ι ℂ) (ρ : Matrix ι ι ℂ) :
    constraintEnergy C ρ = (Cᴴ * C * ρ).trace.re := by
  exact congrArg Complex.re (Matrix.trace_mul_cycle C ρ Cᴴ)

/-- Zero energy forces exact annihilation, not merely a vanishing scalar pairing. -/
theorem constraintEnergy_eq_zero_iff (C : Matrix κ ι ℂ)
    {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) :
    constraintEnergy C ρ = 0 ↔ C * ρ = 0 := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hρ.nonneg
  have hfactor : ρ = Bᴴ * B := by
    simpa only [Matrix.star_eq_conjTranspose] using hB
  constructor
  · intro h
    have hpos := (hρ.mul_mul_conjTranspose_same C).trace_nonneg
    have ht : (C * ρ * Cᴴ).trace = 0 := by
      apply Complex.ext
      · exact h
      · exact (RCLike.nonneg_iff.mp hpos).2
    have hz : C * Bᴴ = 0 := by
      apply Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp
      simpa only [hfactor, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc] using ht
    rw [hfactor, ← Matrix.mul_assoc, hz, Matrix.zero_mul]
  · intro h
    simp only [constraintEnergy, h, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re]

/-- Contracting a zero-energy constraint against any observable still gives zero. -/
theorem constraintEnergy_eq_zero_iff_all_contractions (C : Matrix ι ι ℂ)
    {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) :
    constraintEnergy C ρ = 0 ↔ ∀ A : Matrix ι ι ℂ, A * C * ρ = 0 := by
  rw [constraintEnergy_eq_zero_iff C hρ]
  constructor
  · intro h A
    rw [Matrix.mul_assoc, h, mul_zero]
  · intro h
    simpa only [one_mul] using h 1

/-- Nonnegative constraint energies cannot cancel in a finite sum. -/
theorem sum_constraintEnergy_eq_zero_iff (C : σ → Matrix κ ι ℂ)
    {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) :
    (∑ s, constraintEnergy (C s) ρ) = 0 ↔ ∀ s, C s * ρ = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun s _ => constraintEnergy_nonneg (C s) hρ)]
  simp only [Finset.mem_univ, forall_const, constraintEnergy_eq_zero_iff _ hρ]

/-- The positive operator exposing the common constraint kernel. -/
def constraintHamiltonian (C : σ → Matrix κ ι ℂ) : Matrix ι ι ℂ :=
  ∑ s, (C s)ᴴ * C s

omit [DecidableEq ι] in
theorem constraintHamiltonian_posSemidef (C : σ → Matrix κ ι ℂ) :
    (constraintHamiltonian C).PosSemidef :=
  Matrix.posSemidef_sum _ fun s _ => Matrix.posSemidef_conjTranspose_mul_self (C s)

omit [DecidableEq ι] in
theorem trace_constraintHamiltonian (C : σ → Matrix κ ι ℂ) (ρ : Matrix ι ι ℂ) :
    (constraintHamiltonian C * ρ).trace.re = ∑ s, constraintEnergy (C s) ρ := by
  simp only [constraintHamiltonian, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum,
    constraintEnergy_eq_trace]

/-- One scalar zero selects the intersection of every operator kernel. -/
theorem trace_constraintHamiltonian_eq_zero_iff (C : σ → Matrix κ ι ℂ)
    {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) :
    (constraintHamiltonian C * ρ).trace.re = 0 ↔ ∀ s, C s * ρ = 0 := by
  rw [trace_constraintHamiltonian, sum_constraintEnergy_eq_zero_iff C hρ]

/-- Negative constraint energy as a continuous real linear functional. -/
def constraintExposure (C : σ → Matrix κ ι ℂ) : Matrix ι ι ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ρ => -(constraintHamiltonian C * ρ).trace.re
      map_add' := by
        intro A B
        simp only [Matrix.mul_add, Matrix.trace_add, Complex.add_re, neg_add]
      map_smul' := by
        intro a A
        simp [Matrix.trace_smul] }

/-- The zero-constraint portion of any chosen collection of positive states. -/
def constraintFace (C : σ → Matrix κ ι ℂ) (S : Set (Matrix ι ι ℂ)) :
    Set (Matrix ι ι ℂ) :=
  {ρ ∈ S | ρ.PosSemidef ∧ ∀ s, C s * ρ = 0}

/-- A single supporting functional exposes all squared constraints simultaneously. -/
theorem constraintFace_isExposed (C : σ → Matrix κ ι ℂ)
    (S : Set (Matrix ι ι ℂ)) :
    IsExposed ℝ {ρ ∈ S | ρ.PosSemidef} (constraintFace C S) := by
  rintro ⟨ρ₀, hρ₀⟩
  refine ⟨constraintExposure C, ?_⟩
  have hz : (constraintHamiltonian C * ρ₀).trace.re = 0 :=
    (trace_constraintHamiltonian_eq_zero_iff C hρ₀.2.1).mpr hρ₀.2.2
  ext ρ
  constructor
  · rintro ⟨hS, hρ, hC⟩
    refine ⟨⟨hS, hρ⟩, ?_⟩
    intro τ hτ
    change -(constraintHamiltonian C * τ).trace.re ≤
      -(constraintHamiltonian C * ρ).trace.re
    rw [(trace_constraintHamiltonian_eq_zero_iff C hρ).mpr hC,
      trace_constraintHamiltonian]
    rw [neg_zero]
    exact neg_nonpos.mpr (Finset.sum_nonneg fun s _ => constraintEnergy_nonneg (C s) hτ.2)
  · rintro ⟨⟨hS, hρ⟩, hmax⟩
    refine ⟨hS, hρ, (trace_constraintHamiltonian_eq_zero_iff C hρ).mp ?_⟩
    have hm := hmax ρ₀ ⟨hρ₀.1, hρ₀.2.1⟩
    change -(constraintHamiltonian C * ρ₀).trace.re ≤
      -(constraintHamiltonian C * ρ).trace.re at hm
    rw [hz] at hm
    apply le_antisymm (by linarith)
    rw [trace_constraintHamiltonian]
    exact Finset.sum_nonneg fun s _ => constraintEnergy_nonneg (C s) hρ

/-- No convex mixture can enter the common kernel from outside its face. -/
theorem constraintFace_isExtreme (C : σ → Matrix κ ι ℂ)
    (S : Set (Matrix ι ι ℂ)) :
    IsExtreme ℝ {ρ ∈ S | ρ.PosSemidef} (constraintFace C S) :=
  (constraintFace_isExposed C S).isExtreme

end GaloisForLFunctions.HTGeometry.Quantum
