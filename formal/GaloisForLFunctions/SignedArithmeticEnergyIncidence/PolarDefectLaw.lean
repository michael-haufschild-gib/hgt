import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Topology.Algebra.Module.Basic

/-!
# The polar defect law

A critical form is a positive energy minus finitely many **polar charges**, squares of linear
functionals.  With the positive energy written as the norm of an inner product space and the
charges represented by vectors `g_j` (`v ↦ ⟪g_j, v⟫`), the form is
`Q(v) = ‖v‖² − Σ_j ⟪g_j, v⟫²`.

* **Rank-`r` law** (`polarDefect_nonneg_iff`): `Q ≥ 0` iff the synthesis of the polar vectors is a
  contraction, `‖Σ_j c_j g_j‖² ≤ Σ_j c_j²` for all coefficients, i.e. the polar Gram matrix is at
  most the identity.  The sign of the whole form is decided by `r` numbers' worth of data.
* **Rank-one law** (`polarDefect_nonneg_iff_norm_le_one`, `polarDefect_ge`, `polarDefect_self`):
  `Q ≥ 0` iff `‖g‖ ≤ 1`; the ground ratio `inf Q(v)/‖v‖²` is exactly `1 − ‖g‖²`, attained on the
  polar direction itself.  The only adverse profile of a rank-one defect is its representer.
* **Completion** (`polarDefect_nonneg_of_dense`, `exists_polarDefect_lt_of_unbounded`): positivity
  on a dense subspace transfers to the completion when the polar functional is continuous; when it
  is unbounded on the subspace no floor survives at all, `inf_{‖v‖ = 1} Q(v) = −∞`.  Completion
  keeps the sign exactly when it keeps the polar functional.

Together with `FrustrationIsTheLocalGlobalGap` (a rank-one charge is never locally payable on
three points) this fixes how a pole may be paid: by one global dual-norm bound, not by an
allocation.
-/

open Finset RealInnerProductSpace

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The form `‖v‖² − Σ_j ⟪g_j, v⟫²` with polar vectors `g`. -/
def polarDefectForm {ι : Type*} [Fintype ι] (g : ι → E) (v : E) : ℝ :=
  ‖v‖ ^ 2 - ∑ j, ⟪g j, v⟫ ^ 2

/-- **Rank-`r` polar defect law.**  The form is nonnegative iff the synthesis map of the polar
vectors is a contraction. -/
theorem polarDefect_nonneg_iff {ι : Type*} [Fintype ι] (g : ι → E) :
    (∀ v, 0 ≤ polarDefectForm g v) ↔ ∀ c : ι → ℝ, ‖∑ j, c j • g j‖ ^ 2 ≤ ∑ j, c j ^ 2 := by
  simp only [polarDefectForm, sub_nonneg]
  constructor
  · intro h c
    set v := ∑ j, c j • g j with hv
    have hvv : ‖v‖ ^ 2 = ∑ j, c j * ⟪g j, v⟫ := by
      rw [← real_inner_self_eq_norm_sq]
      conv_lhs => rw [hv]
      rw [sum_inner]
      exact sum_congr rfl fun j _ => real_inner_smul_left _ _ _
    have hcs : (∑ j, c j * ⟪g j, v⟫) ^ 2 ≤ (∑ j, c j ^ 2) * ∑ j, ⟪g j, v⟫ ^ 2 :=
      sum_mul_sq_le_sq_mul_sq _ _ _
    have hS : 0 ≤ ∑ j, c j ^ 2 := sum_nonneg fun j _ => sq_nonneg _
    have hx : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
    have h1 : (‖v‖ ^ 2) ^ 2 ≤ (∑ j, c j ^ 2) * ‖v‖ ^ 2 := by
      rw [hvv] at hx ⊢
      calc _ ≤ _ := hcs
        _ ≤ (∑ j, c j ^ 2) * (∑ j, c j * ⟪g j, v⟫) := by
          rw [← hvv]; exact mul_le_mul_of_nonneg_left (h v) hS
    rcases hx.eq_or_lt with h0 | hpos
    · rw [← h0]; exact hS
    · nlinarith
  · intro h v
    set c : ι → ℝ := fun j => ⟪g j, v⟫ with hc
    have hsum : ∑ j, c j ^ 2 = ⟪∑ j, c j • g j, v⟫ := by
      rw [sum_inner]
      exact sum_congr rfl fun j _ => by rw [real_inner_smul_left, hc, sq]
    have hS : 0 ≤ ∑ j, c j ^ 2 := sum_nonneg fun j _ => sq_nonneg _
    have hcs : (∑ j, c j ^ 2) ^ 2 ≤ ‖∑ j, c j • g j‖ ^ 2 * ‖v‖ ^ 2 := by
      rw [hsum, ← mul_pow]
      exact pow_le_pow_left₀ (by rw [← hsum]; exact hS) (real_inner_le_norm _ _) 2
    have h2 : (∑ j, c j ^ 2) ^ 2 ≤ (∑ j, c j ^ 2) * ‖v‖ ^ 2 :=
      hcs.trans (mul_le_mul_of_nonneg_right (h c) (sq_nonneg _))
    rcases hS.eq_or_lt with h0 | hpos
    · rw [← h0]; exact sq_nonneg _
    · nlinarith

/-- **Rank-one ground ratio**: `Q(v) ≥ (1 − ‖g‖²) ‖v‖²`. -/
theorem polarDefect_ge (g v : E) :
    (1 - ‖g‖ ^ 2) * ‖v‖ ^ 2 ≤ ‖v‖ ^ 2 - ⟪g, v⟫ ^ 2 := by
  have h := abs_real_inner_le_norm g v
  have h2 : ⟪g, v⟫ ^ 2 ≤ (‖g‖ * ‖v‖) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  nlinarith

/-- The ground ratio is attained on the polar direction. -/
theorem polarDefect_self (g : E) : ‖g‖ ^ 2 - ⟪g, g⟫ ^ 2 = (1 - ‖g‖ ^ 2) * ‖g‖ ^ 2 := by
  rw [real_inner_self_eq_norm_sq]
  ring

/-- **Rank-one law**: the defect form is nonnegative iff the polar vector has norm at most one. -/
theorem polarDefect_nonneg_iff_norm_le_one (g : E) :
    (∀ v, 0 ≤ ‖v‖ ^ 2 - ⟪g, v⟫ ^ 2) ↔ ‖g‖ ≤ 1 := by
  constructor
  · intro h
    have := h g
    rw [polarDefect_self] at this
    by_contra hg
    have hg := not_le.mp hg
    have h1 : 0 < ‖g‖ ^ 2 := by positivity
    have h2 : 1 < ‖g‖ ^ 2 := by nlinarith
    nlinarith
  · intro hg v
    have h := polarDefect_ge g v
    have : 0 ≤ 1 - ‖g‖ ^ 2 := by
      have := norm_nonneg g
      nlinarith
    nlinarith [sq_nonneg ‖v‖]

/-- **Completion keeps the sign of a continuous polar charge.**  If `|ℓ v| ≤ ‖v‖` on a dense set,
it holds everywhere. -/
theorem polarDefect_nonneg_of_dense (ℓ : E →L[ℝ] ℝ) {D : Set E} (hD : Dense D)
    (h : ∀ v ∈ D, ℓ v ^ 2 ≤ ‖v‖ ^ 2) (v : E) : ℓ v ^ 2 ≤ ‖v‖ ^ 2 := by
  have hclosed : IsClosed {w : E | ℓ w ^ 2 ≤ ‖w‖ ^ 2} :=
    isClosed_le ((ℓ.continuous).pow 2) (continuous_norm.pow 2)
  have hsub : closure D ⊆ {w : E | ℓ w ^ 2 ≤ ‖w‖ ^ 2} := hclosed.closure_subset_iff.mpr h
  exact hsub (hD.closure_eq ▸ Set.mem_univ v)

/-- **An unbounded polar charge leaves no floor.**  If the polar functional is unbounded on unit
vectors of a subspace, the defect form takes arbitrarily negative values there. -/
theorem exists_polarDefect_lt_of_unbounded {D : Submodule ℝ E} (ℓ : D →ₗ[ℝ] ℝ)
    (hunb : ∀ C : ℝ, ∃ v : D, ‖(v : E)‖ ≤ 1 ∧ C < |ℓ v|) (M : ℝ) :
    ∃ v : D, ‖(v : E)‖ ≤ 1 ∧ ‖(v : E)‖ ^ 2 - ℓ v ^ 2 < -M := by
  obtain ⟨v, hv, hC⟩ := hunb (|M| + 1)
  refine ⟨v, hv, ?_⟩
  have h1 : ‖(v : E)‖ ^ 2 ≤ 1 := by
    have := norm_nonneg (v : E)
    nlinarith
  have h2 : (|M| + 1) ^ 2 < ℓ v ^ 2 := by
    rw [← sq_abs (ℓ v)]
    exact pow_lt_pow_left₀ hC (by positivity) (by norm_num)
  have h3 : M ≤ |M| := le_abs_self M
  nlinarith [abs_nonneg M, sq_nonneg |M|]

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
