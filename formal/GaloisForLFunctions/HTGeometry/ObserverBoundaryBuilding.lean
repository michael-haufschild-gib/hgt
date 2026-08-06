import GaloisForLFunctions.HTGeometry.ObserverBoundaryAtInfinity
import GaloisForLFunctions.HTGeometry.HermitianFlagRealization

/-!
# Boundary points and flags of the horizon building

Every flag of the building is the degeneration flag of a *traceless* Hermitian direction, so it is
the asymptote class of a ray that stays inside the determinant-one space of observer metrics; and
two rays of traceless directions are asymptotic exactly when their flags agree.  Together these
say that asymptote classes of rays based at the reference metric and flags of the building
correspond bijectively — the point-level content of the card's identification of the Tits boundary
with the horizon building.

Making the realizing direction traceless costs nothing, because adding a scalar shifts the flag
thresholds without moving the flag.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
theorem isSymmetric_id : (LinearMap.id : E →ₗ[ℂ] E).IsSymmetric := fun _ _ => rfl

/-- **Every flag of the building is the degeneration flag of a traceless direction.**  So every
simplex of the horizon building is the boundary point of a ray that stays inside the
determinant-one space of observer metrics. -/
theorem exists_traceless_isSymmetric_eigenSum_eq {m : ℕ}
    (f : Fin (m + 1) → properPart (Submodule ℂ E)) (hf : StrictMono f) :
    ∃ T : E →ₗ[ℂ] E, T.IsSymmetric ∧ LinearMap.trace ℂ E T = 0 ∧
      ∀ j, ∃ c : ℝ, eigenSum T c = (f j : Submodule ℂ E) := by
  obtain ⟨T, hT, hflag⟩ := exists_isSymmetric_eigenSum_eq f hf
  -- the space is nontrivial, since it has a nonzero proper subspace
  haveI : Nontrivial E := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (ne_of_gt (f 0).2.1)
    exact nontrivial_of_ne x 0 hx0
  have hNpos : 0 < finrank ℂ E := Module.finrank_pos
  have hN : ((finrank ℂ E : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 hNpos.ne'
  have hNC : ((finrank ℂ E : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hNpos.ne'
  set r : ℝ := ∑ i, hT.eigenvalues (rfl : finrank ℂ E = finrank ℂ E) i with hr
  set a : ℝ := -r / (finrank ℂ E : ℝ) with ha
  have htrT : LinearMap.trace ℂ E T = ((r : ℝ) : ℂ) := trace_eq_sum_eigenvalues hT rfl
  refine ⟨T + (a : ℂ) • LinearMap.id, hT.add (isSymmetric_smul_real isSymmetric_id a), ?_, ?_⟩
  · rw [map_add, map_smul, htrT, LinearMap.trace_id, ha, smul_eq_mul]
    push_cast
    field_simp
    ring
  · intro j
    obtain ⟨c, hc⟩ := hflag j
    exact ⟨c + a, by rw [eigenSum_add_smul_id a c, hc]⟩

/-- **Boundary points and flags correspond.**  A flag is realized by the asymptote class of a ray
of a traceless direction, and two rays of traceless directions are asymptotic exactly when their
flags agree at every threshold. -/
theorem exists_observerRay_eigenSum_eq {m : ℕ}
    (f : Fin (m + 1) → properPart (Submodule ℂ E)) (hf : StrictMono f) :
    ∃ (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric), LinearMap.trace ℂ E T = 0 ∧
      (∀ j, ∃ c : ℝ, eigenSum T c = (f j : Submodule ℂ E)) ∧
      ∀ (S : E →ₗ[ℂ] E) (hS : S.IsSymmetric), LinearMap.trace ℂ E (S - T) = 0 →
        (Asymptotic (observerRay hT) (observerRay hS) ↔ ∀ c : ℝ, eigenSum T c = eigenSum S c) := by
  obtain ⟨T, hT, htr, hflag⟩ := exists_traceless_isSymmetric_eigenSum_eq f hf
  exact ⟨T, hT, htr, hflag, fun S hS hSt => asymptotic_iff_eigenSum_eq hT hS hSt⟩

end GaloisForLFunctions.HTGeometry
