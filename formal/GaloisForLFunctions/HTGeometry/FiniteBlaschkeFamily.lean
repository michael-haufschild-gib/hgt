import GaloisForLFunctions.HTGeometry.HardyDiskBlaschke

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A finite family of strict disk points has one uniform strict radius. -/
theorem exists_finiteFamily_norm_bound_lt_one {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (ha : ∀ i, ‖a i‖ < 1) :
    ∃ b : ℝ, 0 ≤ b ∧ b < 1 ∧ ∀ i, ‖a i‖ ≤ b := by
  classical
  by_cases hι : Nonempty ι
  · letI : Nonempty ι := hι
    obtain ⟨i0, hi0⟩ := Finite.exists_max (fun i : ι => ‖a i‖)
    exact ⟨‖a i0‖, norm_nonneg _, ha i0, hi0⟩
  · exact ⟨0, le_rfl, zero_lt_one, fun i => False.elim (hι ⟨i⟩)⟩

/-- Finite disk points, counted with repetitions, as finite Blaschke data. -/
def finiteBlaschkeOfFiniteFamily {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (ha : ∀ i, ‖a i‖ < 1) : FiniteBlaschke :=
  let hex := exists_finiteFamily_norm_bound_lt_one a ha
  let b := Classical.choose hex
  { deg := Fintype.card ι
    zeros := fun j => a ((Fintype.equivFin ι).symm j)
    bound := b
    bound_nonneg := (Classical.choose_spec hex).1
    bound_lt := (Classical.choose_spec hex).2.1
    zeros_le := fun j =>
      (Classical.choose_spec hex).2.2 ((Fintype.equivFin ι).symm j) }

@[simp]
theorem finiteBlaschkeOfFiniteFamily_deg {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (ha : ∀ i, ‖a i‖ < 1) :
    (finiteBlaschkeOfFiniteFamily a ha).deg = Fintype.card ι := by
  classical
  rfl

theorem finiteBlaschkeOfFiniteFamily_fn {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (ha : ∀ i, ‖a i‖ < 1) (z : ℂ) :
    (finiteBlaschkeOfFiniteFamily a ha).fn z =
      ∏ i : ι, blaschkeFactor (a i) z := by
  classical
  rw [FiniteBlaschke.fn, blaschkeProd]
  let e := Fintype.equivFin ι
  have hreindex :
      (∏ i : ι, blaschkeFactor (a i) z) =
        ∏ j : Fin (Fintype.card ι),
          blaschkeFactor (a (e.symm j)) z := by
    simpa only [e, Equiv.symm_apply_apply] using
      (e.prod_comp (fun j => blaschkeFactor (a (e.symm j)) z))
  rw [hreindex]
  rfl

end


end GaloisForLFunctions.HTGeometry
