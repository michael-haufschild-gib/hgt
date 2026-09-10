import GaloisForLFunctions.HTGeometry.GomesFiniteFockExponentialCoordinate

/-!
# Complete symmetry and generation laws for a single actual Fock translation

Every nonzero parameter already determines the full clock symmetry algebra.
At parameter zero the matrix is the identity: its commutant is the full matrix
algebra and its generated algebra is the scalar algebra. All statements include
zero-dimensional and one-dimensional jet spaces.
-/

noncomputable section
open Matrix Polynomial
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- A single actual Taylor value detects the entire clock commutation law, except at zero parameter. -/
theorem gomesFiniteFock_singleTaylor_commute_iff (N : ℕ) (z : ℂ) (M : Matrix (Fin N) (Fin N) ℂ) :
    Commute M (fockTaylorMatrix N z) ↔ z = 0 ∨ Commute M (fockShiftMatrix N) := by
  by_cases hz : z = 0
  · subst z
    simp only [fockTaylorMatrix_zero, true_or]
    exact iff_true_intro (Commute.one_right M)
  · rw [or_iff_right hz]
    let u : ℂˣ := Units.mk0 z hz
    have hc := gomesFiniteFockCoordinate_commute_iff N (gomesFiniteFockExponentialCoordinate u) M
    rw [gomesFiniteFockExponentialCoordinate_matrix] at hc
    change Commute M (fockTaylorMatrix N z - 1) ↔ Commute M (fockShiftMatrix N) at hc
    constructor
    · intro h
      exact hc.mp (h.sub_right (Commute.one_right M))
    · intro h
      have hh := (hc.mpr h).add_right (Commute.one_right M)
      simpa only [sub_add_cancel] using hh

/-- The exact full matrix commutant of every literal Taylor matrix, with the zero-parameter jump explicit. -/
theorem gomesFiniteFock_singleTaylor_centralizer (N : ℕ) (z : ℂ) :
    Subalgebra.centralizer ℂ {fockTaylorMatrix N z} =
      if z = 0 then ⊤ else gomesFiniteFockCommutant N := by
  ext M
  simp only [Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  by_cases hz : z = 0
  · simp [hz, fockTaylorMatrix_zero]
  · rw [if_neg hz, gomesFiniteFockCommutant_mem_iff]
    exact eq_comm.trans ((gomesFiniteFock_singleTaylor_commute_iff N z M).trans (or_iff_right hz))

/-- A single nonzero Taylor value generates the whole clock algebra; the zero value generates only scalars. -/
theorem gomesFiniteFock_singleTaylor_adjoin (N : ℕ) (z : ℂ) :
    Algebra.adjoin ℂ {fockTaylorMatrix N z} =
      if z = 0 then ⊥ else gomesFiniteFockCommutant N := by
  by_cases hz : z = 0
  · subst z
    rw [fockTaylorMatrix_zero, if_pos rfl, Algebra.adjoin_singleton_one]
  · rw [if_neg hz]
    let u : ℂˣ := Units.mk0 z hz
    have hg := gomesFiniteFockCoordinate_adjoin N (gomesFiniteFockExponentialCoordinate u)
    rw [gomesFiniteFockExponentialCoordinate_matrix] at hg
    change gomesFiniteFockCommutant N = Algebra.adjoin ℂ {fockTaylorMatrix N z - 1} at hg
    apply le_antisymm
    · apply Algebra.adjoin_singleton_le
      rw [← gomesFiniteFockFormalHom_exp]
      exact gomesFiniteFockFormalHom_mem N _
    · rw [hg]
      apply Algebra.adjoin_singleton_le
      exact (Algebra.adjoin ℂ {fockTaylorMatrix N z}).sub_mem
        (Algebra.subset_adjoin (Set.mem_singleton _)) (Subalgebra.one_mem _)

/-- Commuting with every existing Taylor translation is exactly commuting with the actual clock. -/
theorem gomesFiniteFock_allTaylor_commute_iff (N : ℕ) (M : Matrix (Fin N) (Fin N) ℂ) :
    (∀ z : ℂ, Commute M (fockTaylorMatrix N z)) ↔ Commute M (fockShiftMatrix N) := by
  constructor
  · intro h
    exact ((gomesFiniteFock_singleTaylor_commute_iff N 1 M).mp (h 1)).resolve_left one_ne_zero
  · intro h z
    exact (gomesFiniteFock_singleTaylor_commute_iff N z M).mpr (Or.inr h)

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
