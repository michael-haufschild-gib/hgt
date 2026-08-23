import GaloisForLFunctions.HTGeometry.EvaluationMinorGeneralDomain

/-!
# Evaluation minors for involution-odd families

A finite independent family of functions which is odd under a coordinate involution has a
nonsingular evaluation minor supported on pairwise disjoint free involution orbits.  This is the
finite observability law behind multiplicity-exact reflection-index bounds.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

/-- A finite independent family of functions odd under a map admits a nonsingular evaluation
minor which never samples both a coordinate and its partner.  In particular, no selected
coordinate can be fixed.  Involutivity is not needed: oddness and nonsingularity force the stronger
one-step separation directly. -/
theorem exists_orbitSeparated_evaluation_minor_of_linearIndependent_antiInvariant
    {J α : Type*} [Fintype J] [DecidableEq J]
    (σ : α → α) (u : J → α → ℂ) (hu : LinearIndependent ℂ u)
    (hanti : ∀ j q, u j (σ q) = -u j q) :
    ∃ (e : J → α) (P : Matrix J J ℂ),
      Function.Injective e ∧
      (∀ r s, σ (e r) ≠ e s) ∧
      IsUnit P.det ∧
      ∀ r s, P r s = u s (e r) := by
  obtain ⟨e, P, he, hPdet, hP⟩ :=
    exists_injective_evaluation_minor_of_linearIndependent u hu
  refine ⟨e, P, he, ?_, hPdet, hP⟩
  intro r s hrs
  have hrow : ∀ j, P s j = -P r j := by
    intro j
    rw [hP, hP, ← hrs, hanti]
  have hunit : P * P⁻¹ = 1 := P.mul_nonsing_inv hPdet
  have hss := congrArg (fun M : Matrix J J ℂ => M s s) hunit
  have hrsEntry := congrArg (fun M : Matrix J J ℂ => M r s) hunit
  simp only [Matrix.mul_apply, Matrix.one_apply] at hss hrsEntry
  have hneg : (∑ j, P s j * P⁻¹ j s) = -(∑ j, P r j * P⁻¹ j s) := by
    simp_rw [hrow]
    calc
      (∑ j, -P r j * P⁻¹ j s) = ∑ j, -(P r j * P⁻¹ j s) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = -(∑ j, P r j * P⁻¹ j s) := by
        simp only [Finset.sum_neg_distrib]
  rw [hss, hrsEntry] at hneg
  by_cases hsr : s = r
  · subst s
    norm_num at hneg
  · have hrs' : r ≠ s := Ne.symm hsr
    simp [hrs'] at hneg

end

end GaloisForLFunctions.HTGeometry
