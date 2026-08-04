import GaloisForLFunctions.HTGeometry.AlgebraicProximityBound

/-!
# The algebraic growth bound in any number of state variables

The two-variable estimate suffices only for a cascade of length two: reading a relation among
`(z, F_1, …, F_n)` in its last variable leaves coefficients in all the earlier states.  This file
carries the pointwise algebraic bound, and the no-go it produces, to an arbitrary number of variables.

Nothing changes in the argument — only the joint scale of the point becomes a sum over the whole state
family.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The pointwise algebraic bound over a family of states.**  The constant depends only on the
coefficient polynomials. -/
theorem exists_bound_posLog_of_multi_var_relation {m D : ℕ} (hD : 1 ≤ D)
    {X : Fin m → ℂ → ℂ} {A : ℕ → MvPolynomial (Fin m) ℂ} :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (g : ℂ → ℂ) (z : ℂ) (ε : ℝ), 0 < ε →
      ε ≤ ‖MvPolynomial.eval (fun j => X j z) (A D)‖ →
      (∑ i ∈ Finset.range (D + 1),
        MvPolynomial.eval (fun j => X j z) (A i) * (g z) ^ i = 0) →
      Real.posLog ‖g z‖
        ≤ c * (1 + (∑ j : Fin m, Real.posLog ‖X j z‖) + Real.posLog ε⁻¹) := by
  classical
  set K : ℝ := ∑ i ∈ Finset.range D, Real.posLog (mvCoeffNormSum (A i)) with hK
  set Dg : ℝ := ∑ i ∈ Finset.range D, ((A i).totalDegree : ℝ) with hDg
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => Real.posLog_nonneg
  have hDg0 : 0 ≤ Dg := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hDpos : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
  refine ⟨max (max (Real.log D + D * K + D * m * Dg * Real.log 2) (D * Dg)) D, ?_, ?_⟩
  · exact le_trans hDpos (le_max_right _ _)
  · intro g z ε hε hfloor hrel
    set S : ℝ := ∑ j : Fin m, Real.posLog ‖X j z‖ with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Real.posLog_nonneg
    have hε0 : (0 : ℝ) ≤ Real.posLog ε⁻¹ := Real.posLog_nonneg
    have hbase := posLog_norm_le_of_root_floor hD hε hfloor hrel
    have hterm : ∀ i ∈ Finset.range D,
        Real.posLog ‖MvPolynomial.eval (fun j => X j z) (A i)‖ + Real.posLog ε⁻¹
        ≤ (K + Dg * ((m : ℝ) * Real.log 2 + S)) + Real.posLog ε⁻¹ := by
      intro i hi
      have h0 := posLog_norm_eval_le_general (A i) (fun j => X j z)
      have h1 : Real.posLog (mvCoeffNormSum (A i)) ≤ K := by
        rw [hK]
        exact Finset.single_le_sum
          (f := fun j => Real.posLog (mvCoeffNormSum (A j)))
          (fun _ _ => Real.posLog_nonneg) hi
      have h2 : ((A i).totalDegree : ℝ) ≤ Dg := by
        rw [hDg]
        exact Finset.single_le_sum (f := fun j => ((A j).totalDegree : ℝ))
          (fun _ _ => Nat.cast_nonneg _) hi
      have h3 : ∑ j : Fin m, ((A i).totalDegree : ℝ) * (Real.log 2 + Real.posLog ‖X j z‖)
          ≤ ∑ j : Fin m, Dg * (Real.log 2 + Real.posLog ‖X j z‖) := by
        refine Finset.sum_le_sum ?_
        intro j _
        refine mul_le_mul_of_nonneg_right h2 ?_
        have := Real.posLog_nonneg (x := ‖X j z‖)
        linarith
      have h4 : ∑ j : Fin m, Dg * (Real.log 2 + Real.posLog ‖X j z‖)
          = Dg * ((m : ℝ) * Real.log 2 + S) := by
        rw [hS, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
      rw [h4] at h3
      linarith
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have hexp : (D : ℝ) * ((K + Dg * ((m : ℝ) * Real.log 2 + S)) + Real.posLog ε⁻¹)
        = (D * K + D * m * Dg * Real.log 2) + D * Dg * S + D * Real.posLog ε⁻¹ := by ring
    rw [hexp] at hsum
    set c : ℝ := max (max (Real.log D + D * K + D * m * Dg * Real.log 2) (D * Dg)) D with hc
    have hc1 : Real.log D + D * K + D * m * Dg * Real.log 2 ≤ c :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    have hc2 : D * Dg ≤ c := le_trans (le_max_right _ _) (le_max_left _ _)
    have hc3 : (D : ℝ) ≤ c := le_max_right _ _
    have hp2 : D * Dg * S ≤ c * S := mul_le_mul_of_nonneg_right hc2 hS0
    have hp3 : (D : ℝ) * Real.posLog ε⁻¹ ≤ c * Real.posLog ε⁻¹ :=
      mul_le_mul_of_nonneg_right hc3 hε0
    have hgoal : c * (1 + S + Real.posLog ε⁻¹)
        = c + c * S + c * Real.posLog ε⁻¹ := by ring
    rw [hgoal]
    linarith [hbase, hsum, hc1, hp2, hp3]

/-- **The separation forbids an algebraic relation over a family of states.** -/
theorem not_multi_var_relation_of_separation {m D : ℕ} (hD : 1 ≤ D)
    {X : Fin m → ℂ → ℂ} {g : ℂ → ℂ} {A : ℕ → MvPolynomial (Fin m) ℂ}
    (hsel : ∀ c : ℝ, 0 ≤ c → ∃ (z : ℂ) (ε : ℝ), 0 < ε ∧
      ε ≤ ‖MvPolynomial.eval (fun j => X j z) (A D)‖ ∧
      c * (1 + (∑ j : Fin m, Real.posLog ‖X j z‖) + Real.posLog ε⁻¹)
        < Real.posLog ‖g z‖) :
    ¬ (∀ z : ℂ, ∑ i ∈ Finset.range (D + 1),
        MvPolynomial.eval (fun j => X j z) (A i) * (g z) ^ i = 0) := by
  intro hrel
  obtain ⟨c, hc0, hbound⟩ :=
    exists_bound_posLog_of_multi_var_relation (m := m) (D := D) (X := X) (A := A) hD
  obtain ⟨z, ε, hε, hfloor, hsep⟩ := hsel c hc0
  exact absurd (hbound g z ε hε hfloor (hrel z)) (not_le.mpr hsep)

end GaloisForLFunctions.HTGeometry
