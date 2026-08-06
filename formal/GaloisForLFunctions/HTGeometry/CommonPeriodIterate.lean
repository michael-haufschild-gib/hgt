import GaloisForLFunctions.HTGeometry.EigenvolumeRamificationSystem

/-!
# A common period on a finite set

Each component of the divisorial support is periodic, but with its own period.  Replacing the map
by an iterate makes every component fixed at once: the product of the individual periods is a
period for all of them simultaneously.

This is the step that lets the horizon be treated as a set of fixed components rather than a union
of cycles.
-/

namespace GaloisForLFunctions.HTGeometry

section Period

variable {α : Type*} {F : α → α}

/-- A period is a period for every multiple. -/
theorem iterate_mul_eq_self {x : α} {n : ℕ} (h : F^[n] x = x) (m : ℕ) :
    F^[m * n] x = x := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hmn : (m + 1) * n = m * n + n := by ring
    rw [hmn, Function.iterate_add_apply, h, ih]

/-- **A finite set of periodic points has a common period.** -/
theorem exists_common_period (s : Finset α)
    (hper : ∀ x ∈ s, ∃ n, 0 < n ∧ F^[n] x = x) :
    ∃ N, 0 < N ∧ ∀ x ∈ s, F^[N] x = x := by
  classical
  refine ⟨∏ x ∈ s.attach, (hper x.1 x.2).choose, ?_, ?_⟩
  · exact Finset.prod_pos fun x _ => (hper x.1 x.2).choose_spec.1
  · intro x hx
    obtain ⟨m, hm⟩ : (hper x hx).choose ∣ ∏ y ∈ s.attach, (hper y.1 y.2).choose :=
      Finset.dvd_prod_of_mem _ (Finset.mem_attach s ⟨x, hx⟩)
    rw [hm, mul_comm]
    exact iterate_mul_eq_self (hper x hx).choose_spec.2 m

end Period

section Support

variable {α : Type*} {F : α → α} {c : α → ℤ} {e : α → ℕ}

/-- **The divisorial support becomes pointwise fixed under an iterate.**  Every component of the
support is periodic, and a finite support therefore admits a single iterate fixing all of them. -/
theorem exists_iterate_fixing_support
    (hF : Function.Surjective F)
    (hlaw : ∀ x, c x + 1 = (e x : ℤ) * (c (F x) + 1))
    (hfin : {y : α | c y ≠ 0}.Finite) :
    ∃ N, 0 < N ∧ ∀ x, c x ≠ 0 → F^[N] x = x := by
  classical
  obtain ⟨N, hN, hfix⟩ := exists_common_period (F := F) hfin.toFinset (fun x hx => by
    refine exists_pos_iterate_eq_self_of_backwardStable hF hfin ?_ ?_
    · exact fun y hy => order_ne_zero_of_image_ne_zero hlaw hy
    · exact hfin.mem_toFinset.mp hx)
  refine ⟨N, hN, fun x hx => hfix x ?_⟩
  exact hfin.mem_toFinset.mpr hx

end Support

end GaloisForLFunctions.HTGeometry
