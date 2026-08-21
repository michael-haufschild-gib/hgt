import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Normed.Group.Constructions

/-!
# A basis of directions avoiding the zero set of a continuous function

If `Ψ` is continuous and does not vanish at `v`, then it does not vanish on a whole ball around
`v`, and the `d` vectors `v + s e_i` lie in that ball for small `s`.  They are linearly
independent as soon as `s ≠ 0` and `s + ∑ v_j ≠ 0`, and at most one value of `s` is excluded by
the second condition, so a basis of directions on which `Ψ` does not vanish always exists.

This replaces the "appropriate rotation of the coordinate system" of Kleinbock–Margulis.

## Main results

* `exists_directions` — an invertible linear map whose columns avoid the zero set of `Ψ`.
-/

open Metric

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

variable {d : ℕ}

theorem norm_single_le_one (i : Fin d) : ‖(Pi.single i (1 : ℝ) : Fin d → ℝ)‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  by_cases h : j = i <;> simp [h]

theorem smul_single (c : ℝ) (i : Fin d) :
    c • (Pi.single i (1 : ℝ) : Fin d → ℝ) = Pi.single i c := by
  funext j
  by_cases h : j = i <;> simp [h]

/-- The `d` vectors `v + s e_i` are linearly independent when `s ≠ 0` and `s + ∑ v_j ≠ 0`. -/
theorem linearIndependent_shifted_single {v : Fin d → ℝ} {s : ℝ} (hs : s ≠ 0)
    (hsum : (∑ j, v j) + s ≠ 0) :
    LinearIndependent ℝ fun i : Fin d => v + s • (Pi.single i (1 : ℝ) : Fin d → ℝ) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have hexp : (∑ i, a i) • v + s • a = 0 := by
    rw [← ha]
    have h1 : ∀ i : Fin d, a i • (v + s • (Pi.single i (1 : ℝ) : Fin d → ℝ))
        = a i • v + Pi.single i (a i * s) := by
      intro i
      rw [smul_add, smul_smul, smul_single]
    rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_add_distrib, ← Finset.sum_smul]
    congr 1
    have h2 : ∑ i, (Pi.single i (a i * s) : Fin d → ℝ) = fun i => a i * s :=
      Finset.univ_sum_single _
    rw [h2]
    funext j
    simp [mul_comm]
  have hcoord : ∀ j, (∑ i, a i) * v j + s * a j = 0 := by
    intro j
    have h := congrFun hexp j
    simpa using h
  have hA : (∑ i, a i) * ((∑ j, v j) + s) = 0 := by
    have h2 : ∑ j, ((∑ i, a i) * v j + s * a j) = 0 := by
      rw [Finset.sum_congr rfl fun j _ => hcoord j]
      simp
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h2
    linarith [h2]
  have hA0 : (∑ i, a i) = 0 := by
    rcases mul_eq_zero.mp hA with h | h
    · exact h
    · exact absurd h hsum
  intro i
  have := hcoord i
  rw [hA0, zero_mul, zero_add] at this
  exact (mul_eq_zero.mp this).resolve_left hs

/-- **A basis of directions on which `Ψ` does not vanish.** -/
theorem exists_directions [NeZero d] {Ψ : (Fin d → ℝ) → ℝ} (hΨ : Continuous Ψ)
    {v : Fin d → ℝ} (hv : Ψ v ≠ 0) :
    ∃ T : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ), ∀ i : Fin d, Ψ (T (Pi.single i (1 : ℝ))) ≠ 0 := by
  classical
  have hopen : IsOpen {y : Fin d → ℝ | Ψ y ≠ 0} := isOpen_ne_fun hΨ continuous_const
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen v hv
  -- choose the shift
  set V : ℝ := ∑ j, v j with hV
  obtain ⟨s, hs0, hsδ, hsum⟩ : ∃ s : ℝ, 0 < s ∧ s < δ ∧ V + s ≠ 0 := by
    by_cases h : V + δ / 2 = 0
    · refine ⟨δ / 3, by linarith, by linarith, ?_⟩
      intro hc
      have : δ / 2 = δ / 3 := by linarith
      linarith
    · exact ⟨δ / 2, by linarith, by linarith, h⟩
  set u : Fin d → (Fin d → ℝ) := fun i => v + s • (Pi.single i (1 : ℝ)) with hu
  have hli : LinearIndependent ℝ u := linearIndependent_shifted_single (ne_of_gt hs0) hsum
  have hne : ∀ i, Ψ (u i) ≠ 0 := by
    intro i
    refine hball ?_
    rw [mem_ball, dist_eq_norm, hu]
    have : v + s • (Pi.single i (1 : ℝ) : Fin d → ℝ) - v = s • (Pi.single i (1 : ℝ)) := by abel
    simp only []
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
    calc s * ‖(Pi.single i (1 : ℝ) : Fin d → ℝ)‖ ≤ s * 1 :=
          mul_le_mul_of_nonneg_left (norm_single_le_one i) hs0.le
      _ = s := by ring
      _ < δ := hsδ
  -- turn the basis into a linear equivalence
  have hcard : Fintype.card (Fin d) = Module.finrank ℝ (Fin d → ℝ) := by simp
  set B : Module.Basis (Fin d) ℝ (Fin d → ℝ) := basisOfLinearIndependentOfCardEqFinrank hli hcard
    with hB
  have hBapply : ∀ i, B i = u i := fun i =>
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli hcard) i
  set L : (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ) := (Pi.basisFun ℝ (Fin d)).equiv B (Equiv.refl _) with hL
  refine ⟨L.toContinuousLinearEquiv, fun i => ?_⟩
  have happ : L.toContinuousLinearEquiv (Pi.single i (1 : ℝ)) = u i := by
    show L (Pi.single i (1 : ℝ)) = u i
    rw [hL, ← Pi.basisFun_apply ℝ (Fin d) i, Module.Basis.equiv_apply, Equiv.refl_apply, hBapply]
  rw [happ]
  exact hne i

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
