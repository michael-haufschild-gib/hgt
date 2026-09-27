import GaloisForLFunctions.RHTower.FiniteCliqueCollectiveGap
import GaloisForLFunctions.RHTower.CCMFiniteTriangleBound
import GaloisForLFunctions.RHTower.CCMPositiveNoetherPhaseWitness

/-!
# Whole-group correction in the actual full Weil form

The triangle and clique corrections both apply to every finite source family.
An actual positive-energy source, repeated four times, witnesses strict loss
of the triangle estimate. The clique correction recovers its entire quadratic
exactly. This is a limitation of the estimate, not a negative Weil energy.
-/

noncomputable section

open scoped BigOperators

namespace RHTower

theorem ccmRestrictedWeilSourceQuadratic_finite_collective_lower {ι : Type*}
    [Fintype ι] [DecidableEq ι] (a : SuzukiPositiveAperture)
    (u : ι → CCMArchimedeanFormDomain a) (x : ι → ℝ) :
    finiteSignedSeparateLower (fun i j => ccmWeilRealPolar a (u i) (u j)) x +
      max (finiteSignedTriangleCorrection (fun i j => ccmWeilRealPolar a (u i) (u j)) x)
        (finiteSignedCliqueCorrection (fun i j => ccmWeilRealPolar a (u i) (u j)) x) ≤
      ccmRestrictedWeilSourceQuadratic a (∑ i, (x i : ℂ) • u i) := by
  rw [ccmRestrictedWeilSourceQuadratic_real_sum]
  exact finiteSigned_triangle_clique_lower _ (fun i j => ccmWeilRealPolar_symm a (u i) (u j)) x

/-- An internally constructed positive source defeats triangle-only certification;
the whole-clique correction repairs it for every coefficient vector. -/
theorem exists_ccmPositive_source_triangle_loss_repaired :
    ∃ (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a),
      0 < ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector ∧
      let M := fun (_ _ : Fin 4) => ccmWeilRealPolar a u.toCCMFormVector u.toCCMFormVector
      (∀ x : Fin 4 → ℝ, 0 ≤ ccmRestrictedWeilSourceQuadratic a (∑ i, (x i : ℂ) • u.toCCMFormVector)) ∧
      finiteSignedSeparateLower M (fun _ => 1) + finiteSignedTriangleCorrection M (fun _ => 1) < 0 ∧
      (∀ x : Fin 4 → ℝ, finiteSignedSeparateLower M x + finiteSignedCliqueCorrection M x =
        ccmRestrictedWeilSourceQuadratic a (∑ i, (x i : ℂ) • u.toCCMFormVector)) := by
  obtain ⟨a, u, _, _, hu, _, _, _, _, _⟩ := exists_ccmArithmetic_positive_baseline_phase_potential
  refine ⟨a, u, hu, ?_⟩
  dsimp only
  simp_rw [ccmWeilRealPolar_self]
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [ccmRestrictedWeilSourceQuadratic_real_sum]
    simp_rw [ccmWeilRealPolar_self]
    rw [finiteSignedQuadratic_constant]
    exact mul_nonneg hu.le (sq_nonneg _)
  · have h := finiteSignedTriangle_lower_constant_exact (ι := Fin 4) hu.le
      (by norm_num) (fun _ => 1)
    norm_num only [Fintype.card_fin, Nat.cast_ofNat, one_pow, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul] at h
    nlinarith only [h, hu]
  · intro x
    rw [ccmRestrictedWeilSourceQuadratic_real_sum]
    simp_rw [ccmWeilRealPolar_self]
    apply finiteSignedClique_constant_exact hu.le
    refine ⟨(0, 1), ?_⟩
    simp

end RHTower
