import GaloisForLFunctions.RHTower.XiTraceHankelCriterion
import GaloisForLFunctions.HTGeometry.MomentFunctionalPositivity

/-!
# The algebraic trace-Hankel cone on moment sequences

This is the coefficient-level core of the critical-centre instability theorem.
It is intentionally independent of holomorphic-germ topology.  The analytic
capstone must additionally prove that changing a sufficiently remote even
coefficient can be made arbitrarily small in the compact-open topology.
-/

noncomputable section

namespace RHTower

open scoped BigOperators
open Polynomial

/-- The Hankel quadratic form attached to a real moment sequence.  Writing it
through the coefficients of `p * p` packages the usual double sum
`Σ i,j, p_i p_j m_(i+j)`. -/
def sequenceTraceHankel (m : ℕ → ℝ) (p : Polynomial ℝ) : ℝ :=
  ∑ n ∈ (p * p).support, (p * p).coeff n * m n

/-- The coefficient-level trace-Hankel form is exactly the moment functional evaluated on the
polynomial square. -/
theorem sequenceTraceHankel_eq_momentFunctional (m : ℕ → ℝ) (p : Polynomial ℝ) :
    sequenceTraceHankel m p = HTGeometry.momentFunctional m (p ^ 2) := by
  rw [sequenceTraceHankel, HTGeometry.momentFunctional_eq_support_sum, pow_two]

/-- Membership in the all-order real trace-Hankel-positive cone. -/
def SequenceTraceHankelNonnegative (m : ℕ → ℝ) : Prop :=
  ∀ p : Polynomial ℝ, 0 ≤ sequenceTraceHankel m p

/-- A monomial square reads one even moment coordinate exactly. -/
@[simp]
theorem sequenceTraceHankel_X_pow (m : ℕ → ℝ) (N : ℕ) :
    sequenceTraceHankel m (X ^ N) = m (N + N) := by
  unfold sequenceTraceHankel
  rw [← pow_add]
  simp

/-- Positivity of the full Hankel form forces every even moment coordinate to
be nonnegative. -/
theorem even_moment_nonnegative_of_sequenceTraceHankel
    {m : ℕ → ℝ} (hm : SequenceTraceHankelNonnegative m) (N : ℕ) :
    0 ≤ m (N + N) := by
  simpa using hm (X ^ N)

/-- Replacing one even moment by a negative value gives an explicit polynomial
square witnessing failure of Hankel positivity. -/
theorem not_sequenceTraceHankelNonnegative_update_even
    (m : ℕ → ℝ) (N : ℕ) (a : ℝ) (ha : a < 0) :
    ¬ SequenceTraceHankelNonnegative (Function.update m (N + N) a) := by
  intro h
  have hmono := h (X ^ N)
  rw [sequenceTraceHankel_X_pow] at hmono
  simp only [Function.update_self] at hmono
  linarith

/-- The normalized perturbation used in the analytic proof sets the selected
even moment to exactly `-1`. -/
theorem normalized_even_moment_perturbation_fails
    (m : ℕ → ℝ) (N : ℕ) :
    ¬ SequenceTraceHankelNonnegative
      (Function.update m (N + N) (-1)) :=
  not_sequenceTraceHankelNonnegative_update_even m N (-1) (by norm_num)

/-- Every finite Hankel test depends on only finitely many moment coordinates. -/
theorem sequenceTraceHankel_eq_of_eqOn_support
    {m n : ℕ → ℝ} {p : Polynomial ℝ}
    (h : Set.EqOn m n (p * p).support) :
    sequenceTraceHankel m p = sequenceTraceHankel n p := by
  unfold sequenceTraceHankel
  apply Finset.sum_congr rfl
  intro k hk
  rw [h hk]

/-- Every fixed polynomial Hankel test is continuous for the product topology
on moment sequences. -/
theorem continuous_sequenceTraceHankel (p : Polynomial ℝ) :
    Continuous (fun m : ℕ → ℝ ↦ sequenceTraceHankel m p) := by
  unfold sequenceTraceHankel
  fun_prop

/-- The all-order Hankel-positive sequence cone is closed in the coefficient
product topology. This is the formal coefficient-level parent of compact-open
closedness for analytic moment germs. -/
theorem isClosed_sequenceTraceHankelNonnegative :
    IsClosed {m : ℕ → ℝ | SequenceTraceHankelNonnegative m} := by
  rw [show {m : ℕ → ℝ | SequenceTraceHankelNonnegative m} =
      ⋂ p : Polynomial ℝ, {m : ℕ → ℝ | 0 ≤ sequenceTraceHankel m p} by
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_iInter, SequenceTraceHankelNonnegative]]
  apply isClosed_iInter
  intro p
  exact isClosed_Ici.preimage (continuous_sequenceTraceHankel p)

/-- In the coefficient product topology, the complement of the all-order
Hankel-positive cone is dense: every neighborhood controls only finitely many
coordinates, so a remote even moment can be set to `-1`. -/
theorem dense_not_sequenceTraceHankelNonnegative :
    Dense {m : ℕ → ℝ | ¬ SequenceTraceHankelNonnegative m} := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨m, hmU⟩ := hUne
  have hUnhds : U ∈ nhds m := hU.mem_nhds hmU
  obtain ⟨I, hIU⟩ :=
    exists_finset_piecewise_mem_of_mem_nhds hUnhds (fun _ : ℕ ↦ (-1 : ℝ))
  obtain ⟨k, hk⟩ := I.exists_nat_subset_range
  let N : ℕ := k + 1
  have hNN : N + N ∉ I := by
    intro hmem
    have hlt : N + N < k := Finset.mem_range.mp (hk hmem)
    dsimp [N] at hlt
    omega
  let m' : ℕ → ℝ := I.piecewise m (fun _ ↦ -1)
  have hm'coord : m' (N + N) = -1 := by
    simp only [m', Finset.piecewise, hNN, ↓reduceIte]
  have hm'fail : ¬ SequenceTraceHankelNonnegative m' := by
    intro hpos
    have hmono := hpos (X ^ N)
    rw [sequenceTraceHankel_X_pow, hm'coord] at hmono
    linarith
  exact ⟨m', hIU, hm'fail⟩

/-- The coefficient-level Hankel-positive cone is nowhere dense. -/
theorem sequenceTraceHankelNonnegative_isNowhereDense :
    IsNowhereDense {m : ℕ → ℝ | SequenceTraceHankelNonnegative m} := by
  have hopen : IsOpen ({m : ℕ → ℝ | SequenceTraceHankelNonnegative m}ᶜ) :=
    isClosed_sequenceTraceHankelNonnegative.isOpen_compl
  have hdense : Dense ({m : ℕ → ℝ | SequenceTraceHankelNonnegative m}ᶜ) := by
    simpa only [Set.compl_setOf] using dense_not_sequenceTraceHankelNonnegative
  exact (isClosed_isNowhereDense_iff_compl.mpr ⟨hopen, hdense⟩).2

end RHTower
