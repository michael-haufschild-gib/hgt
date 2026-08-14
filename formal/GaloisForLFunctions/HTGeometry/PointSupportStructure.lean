import GaloisForLFunctions.HTGeometry.JetTestFunctions
import GaloisForLFunctions.HTGeometry.PointSupportVanishing

/-!
# Distributions supported at the origin are finite combinations of derivatives of the delta

A tempered distribution annihilating every Schwartz function that vanishes near the origin is
determined by finitely many jet coefficients:

`u φ = ∑_{j ≤ N} φ^{(j)}(0) c_j`,

with `c_j = u(jetTest j)`.  The vanishing theorem kills the difference between `φ` and its jet
interpolation, and the jet test functions realise every prescribed finite jet.
-/

open Set SchwartzMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- **The structure theorem for distributions supported at a point.** -/
theorem exists_delta_representation (u : SchwartzMap ℝ ℂ →L[ℂ] X)
    (hu : ∀ ψ : SchwartzMap ℝ ℂ, (∃ δ > 0, ∀ x : ℝ, |x| ≤ δ → (ψ : ℝ → ℂ) x = 0) → u ψ = 0) :
    ∃ (N : ℕ) (c : ℕ → X), ∀ φ : SchwartzMap ℝ ℂ,
      u φ = ∑ j ∈ Finset.range (N+1), (iteratedDeriv j (φ : ℝ → ℂ) 0) • c j := by
  obtain ⟨N, hN⟩ := exists_order_apply_eq_zero u hu
  refine ⟨N, fun j => u (jetTest j), fun φ => ?_⟩
  set c : ℕ → ℂ := fun j => iteratedDeriv j (φ : ℝ → ℂ) 0 with hc
  set Ψ : SchwartzMap ℝ ℂ := ∑ j ∈ Finset.range (N+1), c j • jetTest j with hΨdef
  set ψ : SchwartzMap ℝ ℂ := φ - Ψ with hψdef
  have hΨcoe : (Ψ : ℝ → ℂ) = ∑ j ∈ Finset.range (N+1), c j • (jetTest j : ℝ → ℂ) := by
    rw [hΨdef]
    push_cast
    rfl
  have hcoe : (ψ : ℝ → ℂ) = (φ : ℝ → ℂ) - (Ψ : ℝ → ℂ) := by
    rw [hψdef]
    push_cast
    rfl
  have hcdsum : ∀ i : ℕ, ContDiffAt ℝ (i : ℕ∞) (Ψ : ℝ → ℂ) 0 := fun i =>
    ((Ψ.smooth').of_le (by exact_mod_cast le_top)).contDiffAt
  have hjet : ∀ i, i ≤ N → iteratedDeriv i (ψ : ℝ → ℂ) 0 = 0 := by
    intro i hi
    rw [hcoe]
    have hφcd : ContDiffAt ℝ (i : ℕ∞) (φ : ℝ → ℂ) 0 :=
      ((φ.smooth').of_le (by exact_mod_cast le_top)).contDiffAt
    rw [iteratedDeriv_sub hφcd (hcdsum i), hΨcoe]
    rw [iteratedDeriv_sum (f := fun j => c j • ((jetTest j : SchwartzMap ℝ ℂ) : ℝ → ℂ))
      (I := Finset.range (N+1)) (n := i) (x := 0)
      (fun j _ => ((((jetTest j).smooth').of_le
        (by exact_mod_cast le_top)).contDiffAt : ContDiffAt ℝ (i : ℕ∞)
          ((jetTest j : SchwartzMap ℝ ℂ) : ℝ → ℂ) 0).const_smul (c j))]
    have hterm : ∀ j ∈ Finset.range (N+1),
        iteratedDeriv i (c j • (jetTest j : ℝ → ℂ)) 0
          = if i = j then c j else 0 := by
      intro j _
      have hcd : ContDiffAt ℝ (i : ℕ∞) (jetTest j : ℝ → ℂ) 0 :=
        (((jetTest j).smooth').of_le (by exact_mod_cast le_top)).contDiffAt
      rw [iteratedDeriv_const_smul hcd, iteratedDeriv_jetTest_zero]
      by_cases h : i = j
      · rw [if_pos h, if_pos h, smul_eq_mul, mul_one]
      · rw [if_neg h, if_neg h, smul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq (Finset.range (N+1)) i c]
    rw [if_pos (Finset.mem_range.mpr (by omega))]
    rw [hc]
    exact sub_self _
  have huψ := hN ψ hjet
  have hlin : u ψ = u φ - ∑ j ∈ Finset.range (N+1), c j • u (jetTest j) := by
    rw [hψdef, map_sub, hΨdef, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul]
  rw [hlin] at huψ
  have := sub_eq_zero.mp huψ
  exact this

end

end GaloisForLFunctions.HTGeometry
