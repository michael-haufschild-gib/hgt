import GaloisForLFunctions.HTGeometry.AbeRealCoordinateDamping
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Abe's `Φ₂` translation-growth clause

Section 7 of Abe's paper defines `Φ₂` by an entire-function condition together with the displayed
subquadratic translation-growth estimate. This file formalizes that exact growth clause and the
closure operation used by Abe's multiplier: a lattice-uniformly bounded multiplier preserves the
clause. The literal real-coordinate damping multiplier has precisely that uniform bound whenever
the relevant period-coordinate shifts are real.

This does not identify the complete period-matrix lattice or prove the seed's convergence property;
it is the concrete growth half of that remaining bridge.
-/

open Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The translation-growth part of Abe's Section-7 class `Φ₂`. The companion requirement that the
function be entire is carried separately by `MultivariateEntire`. -/
def AbePhi2TranslationGrowth {d : ℕ} (Γ : AddSubgroup (Fin d → ℂ))
    (f : (Fin d → ℂ) → ℂ) : Prop :=
  ∀ K : Set (Fin d → ℂ), IsCompact K → ∃ C₁ C₂ ρ : ℝ,
    0 < C₁ ∧ 0 < C₂ ∧ 0 < ρ ∧ ρ < 2 ∧
      ∀ x ∈ K, ∀ γ : Γ, ‖f (x + γ.1)‖ ≤
        C₁ * Real.exp (C₂ * ‖γ.1‖ ^ ρ)

/-- A multiplier is bounded uniformly over lattice translates of every compact set. -/
def AbeLatticeUniformlyBounded {d : ℕ} (Γ : AddSubgroup (Fin d → ℂ))
    (m : (Fin d → ℂ) → ℂ) : Prop :=
  ∀ K : Set (Fin d → ℂ), IsCompact K → ∃ M : ℝ, 0 ≤ M ∧
    ∀ x ∈ K, ∀ γ : Γ, ‖m (x + γ.1)‖ ≤ M

/-- Multiplication by a lattice-uniformly bounded function preserves Abe's subquadratic
translation-growth clause. -/
theorem AbePhi2TranslationGrowth.mul_of_latticeUniformlyBounded {d : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)} {f m : (Fin d → ℂ) → ℂ}
    (hf : AbePhi2TranslationGrowth Γ f) (hm : AbeLatticeUniformlyBounded Γ m) :
    AbePhi2TranslationGrowth Γ (fun x => f x * m x) := by
  intro K hK
  obtain ⟨C₁, C₂, ρ, hC₁, hC₂, hρ, hρtwo, hfgrowth⟩ := hf K hK
  obtain ⟨M, hM, hmbound⟩ := hm K hK
  refine ⟨C₁ * (M + 1), C₂, ρ, mul_pos hC₁ (by linarith),
    hC₂, hρ, hρtwo, ?_⟩
  intro x hx γ
  rw [norm_mul]
  calc ‖f (x + γ.1)‖ * ‖m (x + γ.1)‖
      ≤ (C₁ * Real.exp (C₂ * ‖γ.1‖ ^ ρ)) * (M + 1) := by
        gcongr
        · exact hfgrowth x hx γ
        · exact (hmbound x hx γ).trans (by linarith)
    _ = (C₁ * (M + 1)) * Real.exp (C₂ * ‖γ.1‖ ^ ρ) := by ring

/-- The literal real-coordinate damping multiplier, viewed on a chosen coordinate of `ℂᵈ`. -/
def abeRealCoordinateDampingOn {d : ℕ} (k : Fin d) (t ω : ℂ)
    (x : Fin d → ℂ) : ℂ :=
  abeRealCoordinateDamping t (x k) ω

/-- In a coordinate whose lattice shifts are real, Abe's literal damping multiplier is bounded
uniformly over all lattice translates of any fixed compact set. -/
theorem abeRealCoordinateDampingOn_latticeUniformlyBounded {d : ℕ}
    (k : Fin d) (t ω : ℂ) (Γ : AddSubgroup (Fin d → ℂ))
    (hreal : ∀ γ : Γ, ∃ r : ℝ, γ.1 k = (r : ℂ)) :
    AbeLatticeUniformlyBounded Γ (abeRealCoordinateDampingOn k t ω) := by
  intro K hK
  have hcontinuous : Continuous (fun x : Fin d → ℂ =>
      abeRealCoordinateCharacter (x k)) := by
    unfold abeRealCoordinateCharacter
    fun_prop
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (f := fun x : Fin d → ℂ => ‖abeRealCoordinateCharacter (x k)‖)
    hcontinuous.norm.continuousOn
  refine ⟨Real.exp (‖t‖ * (|C| + ‖ω‖)), Real.exp_nonneg _, ?_⟩
  intro x hx γ
  obtain ⟨r, hr⟩ := hreal γ
  have hcharacter : ‖abeRealCoordinateCharacter (x k)‖ ≤ |C| :=
    (show ‖abeRealCoordinateCharacter (x k)‖ ≤ C by
      simpa using hC x hx).trans (le_abs_self C)
  change ‖abeRealCoordinateDamping t ((x + γ.1) k) ω‖ ≤ _
  rw [show (x + γ.1) k = x k + (r : ℂ) by simp [hr]]
  refine (norm_abeRealCoordinateDamping_translate_le t (x k) ω r).trans ?_
  apply Real.exp_le_exp.mpr
  have hinter : ‖abeRealCoordinateCharacter (x k)‖ + ‖ω‖ ≤ |C| + ‖ω‖ := by
    linarith
  exact mul_le_mul_of_nonneg_left hinter (norm_nonneg _)

/-- Abe's `Φ₂` translation-growth clause is preserved by the literal damping multiplier in a
real-period coordinate. -/
theorem AbePhi2TranslationGrowth.mul_abeRealCoordinateDampingOn {d : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)} {f : (Fin d → ℂ) → ℂ}
    (hf : AbePhi2TranslationGrowth Γ f) (k : Fin d) (t ω : ℂ)
    (hreal : ∀ γ : Γ, ∃ r : ℝ, γ.1 k = (r : ℂ)) :
    AbePhi2TranslationGrowth Γ (fun x => f x * abeRealCoordinateDampingOn k t ω x) :=
  hf.mul_of_latticeUniformlyBounded
    (abeRealCoordinateDampingOn_latticeUniformlyBounded k t ω Γ hreal)

end

end GaloisForLFunctions.HTGeometry
