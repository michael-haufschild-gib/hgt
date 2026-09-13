import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

/-!
# Algebraic core of arXiv:2607.29504

This file formalizes the paper's exact causal interaction selection for sampled
retarded Green-function assembly.  A positive time step is represented as `exp logStep`,
so every theorem is premise-free: the active delay condition is equivalent to an
integer ceil/floor shell, and summing zero-extended interaction terms is exactly the
same as summing only over that shell.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Retarded interaction `(k, τ)` is active when its delayed sample lies in the
available time window `[tₐ, tᵦ]`. -/
def causalInteractionActive
    (logStep tₐ tᵦ τ : ℝ) (k : ℤ) : Prop :=
  (k : ℝ) * Real.exp logStep - τ ∈ Set.Icc tₐ tᵦ

/-- The exact integer shell produced by the paper's ceil/floor selection rule. -/
def causalInteractionShell
    (logStep tₐ tᵦ τ : ℝ) : Finset ℤ :=
  Finset.Icc
    ⌈(τ + tₐ) / Real.exp logStep⌉
    ⌊(τ + tᵦ) / Real.exp logStep⌋

/-- Paper's causal interval test and integer shell test are exactly equivalent. -/
theorem causalInteractionActive_iff_shellBounds
    (logStep tₐ tᵦ τ : ℝ) (k : ℤ) :
    causalInteractionActive logStep tₐ tᵦ τ k ↔
      ⌈(τ + tₐ) / Real.exp logStep⌉ ≤ k ∧
        k ≤ ⌊(τ + tᵦ) / Real.exp logStep⌋ := by
  rw [causalInteractionActive, Set.mem_Icc, Int.ceil_le, Int.le_floor]
  constructor
  · rintro ⟨hₐ, hᵦ⟩
    constructor
    · rw [div_le_iff₀ (Real.exp_pos logStep)]
      linarith
    · rw [le_div_iff₀ (Real.exp_pos logStep)]
      linarith
  · rintro ⟨hₐ, hᵦ⟩
    constructor
    · rw [div_le_iff₀ (Real.exp_pos logStep)] at hₐ
      linarith
    · rw [le_div_iff₀ (Real.exp_pos logStep)] at hᵦ
      linarith

theorem causalInteractionActive_iff_mem_shell
    (logStep tₐ tᵦ τ : ℝ) (k : ℤ) :
    causalInteractionActive logStep tₐ tᵦ τ k ↔
      k ∈ causalInteractionShell logStep tₐ tᵦ τ := by
  rw [causalInteractionActive_iff_shellBounds]
  simp [causalInteractionShell]

/-- Zero extension of a retarded interaction outside its exact causal shell. -/
def causalInteractionTerm {A : Type*} [Zero A]
    (logStep tₐ tᵦ τ : ℝ) (raw : ℤ → A) (k : ℤ) : A :=
  if k ∈ causalInteractionShell logStep tₐ tᵦ τ then raw k else 0

/-- Full finite-batch assembly with inactive interactions zero-extended. -/
def causalBatchResponse {A : Type*} [AddCommMonoid A]
    (batch : Finset ℤ) (logStep tₐ tᵦ τ : ℝ) (raw : ℤ → A) : A :=
  ∑ k ∈ batch, causalInteractionTerm logStep tₐ tᵦ τ raw k

/-- Assembly restricted a priori to the exact causal shell. -/
def causalPrunedBatchResponse {A : Type*} [AddCommMonoid A]
    (batch : Finset ℤ) (logStep tₐ tᵦ τ : ℝ) (raw : ℤ → A) : A :=
  ∑ k ∈ batch ∩ causalInteractionShell logStep tₐ tᵦ τ, raw k

/-- Exact-pruning theorem: shell selection changes cost, never the assembled result. -/
theorem causalBatchResponse_eq_causalPrunedBatchResponse
    {A : Type*} [AddCommMonoid A]
    (batch : Finset ℤ) (logStep tₐ tᵦ τ : ℝ) (raw : ℤ → A) :
    causalBatchResponse batch logStep tₐ tᵦ τ raw =
      causalPrunedBatchResponse batch logStep tₐ tᵦ τ raw := by
  classical
  rw [causalBatchResponse, causalPrunedBatchResponse]
  calc
    (∑ k ∈ batch, causalInteractionTerm logStep tₐ tᵦ τ raw k) =
        ∑ k ∈ batch.filter
          (fun k => k ∈ causalInteractionShell logStep tₐ tᵦ τ), raw k := by
      symm
      rw [Finset.sum_filter]
      simp [causalInteractionTerm]
    _ = ∑ k ∈ batch ∩ causalInteractionShell logStep tₐ tᵦ τ, raw k := by
      congr 1

/-- Relabeling both source delay and sample index by the same integer number of
time steps leaves causal activity unchanged. -/
theorem causalInteractionActive_shift
    (logStep tₐ tᵦ τ : ℝ) (k m : ℤ) :
    causalInteractionActive logStep tₐ tᵦ
        (τ + (m : ℝ) * Real.exp logStep) (k + m) ↔
      causalInteractionActive logStep tₐ tᵦ τ k := by
  simp only [causalInteractionActive, Set.mem_Icc, Int.cast_add]
  constructor <;> rintro ⟨hₐ, hᵦ⟩ <;> constructor <;> linarith

end

end GaloisForLFunctions.HTGeometry
