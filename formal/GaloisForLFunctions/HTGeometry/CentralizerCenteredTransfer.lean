import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Centralizer-centered transfer

A propagator that fixes the kernel of its generator moves a vector only inside the orthogonal
complement of that kernel.  A matrix coefficient of the moved vector therefore differs from its
completed baseline by a pairing that sees only the complementary part of the target, and any
subspace of the kernel gives an even larger complement.  All of this is exact: no time averaging
and no ensemble averaging is used, and a target lying inside the kernel subspace has no defect at
any time.

The circuit union enters through one scalar: if a single word already meets the fidelity
threshold, the scaled replica average of the whole family is already at least one.
-/

open scoped InnerProductSpace BigOperators

namespace GaloisForLFunctions.HTGeometry

section Projections

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A symmetric idempotent splits every vector orthogonally. -/
theorem inner_selfAdjointIdempotent_complement_eq_zero
    (P : E →ₗ[ℂ] E) (hPsymm : ∀ y z : E, ⟪P y, z⟫_ℂ = ⟪y, P z⟫_ℂ)
    (hPP : ∀ y, P (P y) = P y) (x : E) :
    ⟪P x, x - P x⟫_ℂ = 0 := by
  rw [inner_sub_right, hPsymm x (P x), hPP, hPsymm x x, sub_self]

/-- A symmetric idempotent has contractive complement. -/
theorem norm_sub_selfAdjointIdempotent_le
    (P : E →ₗ[ℂ] E) (hPsymm : ∀ y z : E, ⟪P y, z⟫_ℂ = ⟪y, P z⟫_ℂ)
    (hPP : ∀ y, P (P y) = P y) (x : E) :
    ‖x - P x‖ ≤ ‖x‖ := by
  have hsplit : ‖P x + (x - P x)‖ * ‖P x + (x - P x)‖ =
      ‖P x‖ * ‖P x‖ + ‖x - P x‖ * ‖x - P x‖ :=
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P x) (x - P x)
      (inner_selfAdjointIdempotent_complement_eq_zero P hPsymm hPP x)
  have hx : P x + (x - P x) = x := by abel
  rw [hx] at hsplit
  nlinarith [norm_nonneg (P x), norm_nonneg (x - P x), norm_nonneg x]

end Projections

section Transfer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **`(3)`, first equality.**  A propagator that fixes the kernel projection moves a vector only
inside the complement, so its matrix coefficient sees only the complementary part of the target. -/
theorem centralizerCentered_inner_eq_complement
    (U P : E →ₗ[ℂ] E) (hPsymm : ∀ y z : E, ⟪P y, z⟫_ℂ = ⟪y, P z⟫_ℂ)
    (hPU : ∀ y, P (U y) = P y) (hPP : ∀ y, P (P y) = P y) (x M : E) :
    ⟪U x - P x, M⟫_ℂ = ⟪U x - P x, M - P M⟫_ℂ := by
  have hzero : P (U x - P x) = 0 := by
    rw [map_sub, hPU, hPP, sub_self]
  rw [inner_sub_right, ← hPsymm (U x - P x) M, hzero, inner_zero_left, sub_zero]

/-- **`(3)`, second equality.**  A subspace of the kernel sees no more of the moving part than the
kernel itself. -/
theorem centralizerCentered_inner_eq_subspace_complement
    (U P Pi : E →ₗ[ℂ] E) (_hPsymm : ∀ y z : E, ⟪P y, z⟫_ℂ = ⟪y, P z⟫_ℂ)
    (hPisymm : ∀ y z : E, ⟪Pi y, z⟫_ℂ = ⟪y, Pi z⟫_ℂ)
    (hPU : ∀ y, P (U y) = P y) (hPP : ∀ y, P (P y) = P y)
    (hPiP : ∀ y, Pi (P y) = Pi y) (x M : E) :
    ⟪U x - P x, M⟫_ℂ = ⟪U x - P x, M - Pi M⟫_ℂ := by
  have hzero : P (U x - P x) = 0 := by
    rw [map_sub, hPU, hPP, sub_self]
  have hPizero : Pi (U x - P x) = 0 := by
    rw [← hPiP, hzero, map_zero]
  rw [inner_sub_right, ← hPisymm (U x - P x) M, hPizero, inner_zero_left, sub_zero]

/-- **`(3)`.**  The physical matrix coefficient equals its completed centralizer baseline plus a
defect supported in the complement of the kernel. -/
theorem centralizerCentered_defect_eq
    (U P : E →ₗ[ℂ] E) (hPsymm : ∀ y z : E, ⟪P y, z⟫_ℂ = ⟪y, P z⟫_ℂ)
    (hPU : ∀ y, P (U y) = P y) (hPP : ∀ y, P (P y) = P y) (x M : E) :
    ⟪U x, M⟫_ℂ - ⟪P x, M⟫_ℂ = ⟪U x - P x, M - P M⟫_ℂ := by
  rw [← centralizerCentered_inner_eq_complement U P hPsymm hPU hPP x M, inner_sub_left]

/-- **`(4)`, first inequality.** -/
theorem norm_centralizerCentered_defect_le
    (U P : E →ₗ[ℂ] E) (hPsymm : ∀ y z : E, ⟪P y, z⟫_ℂ = ⟪y, P z⟫_ℂ)
    (hUP : ∀ y, U (P y) = P y) (hPU : ∀ y, P (U y) = P y) (hPP : ∀ y, P (P y) = P y)
    (hUiso : ∀ y, ‖U y‖ = ‖y‖) (x M : E) :
    ‖⟪U x, M⟫_ℂ - ⟪P x, M⟫_ℂ‖ ≤ ‖x - P x‖ * ‖M - P M‖ := by
  rw [centralizerCentered_defect_eq U P hPsymm hPU hPP x M]
  have hmove : U x - P x = U (x - P x) := by
    rw [map_sub, hUP]
  rw [hmove]
  refine le_trans (norm_inner_le_norm (U (x - P x)) (M - P M)) ?_
  rw [hUiso]

/-- **`(4)`, second inequality.**  Both projections are contractions and the smaller kernel
subspace gives the larger complement. -/
theorem norm_centralizerCentered_defect_le_subspace
    (U P Pi : E →ₗ[ℂ] E) (hPsymm : ∀ y z : E, ⟪P y, z⟫_ℂ = ⟪y, P z⟫_ℂ)
    (hUP : ∀ y, U (P y) = P y) (hPU : ∀ y, P (U y) = P y) (hPP : ∀ y, P (P y) = P y)
    (hPPi : ∀ y, P (Pi y) = Pi y) (hUiso : ∀ y, ‖U y‖ = ‖y‖) (x M : E) :
    ‖⟪U x, M⟫_ℂ - ⟪P x, M⟫_ℂ‖ ≤ ‖x‖ * ‖M - Pi M‖ := by
  refine le_trans (norm_centralizerCentered_defect_le U P hPsymm hUP hPU hPP hUiso x M) ?_
  have hx : ‖x - P x‖ ≤ ‖x‖ :=
    norm_sub_selfAdjointIdempotent_le P hPsymm hPP x
  have hM : ‖M - P M‖ ≤ ‖M - Pi M‖ := by
    have hrewrite : M - P M = (M - Pi M) - P (M - Pi M) := by
      rw [map_sub, hPPi]
      abel
    rw [hrewrite]
    exact norm_sub_selfAdjointIdempotent_le P hPsymm hPP (M - Pi M)
  exact mul_le_mul hx hM (norm_nonneg _) (norm_nonneg x)

/-- **`(12)`.**  A target already in the kernel subspace has no defect at all. -/
theorem centralizerCentered_defect_eq_zero
    (U P Pi : E →ₗ[ℂ] E) (hPsymm : ∀ y z : E, ⟪P y, z⟫_ℂ = ⟪y, P z⟫_ℂ)
    (hUP : ∀ y, U (P y) = P y) (hPU : ∀ y, P (U y) = P y) (hPP : ∀ y, P (P y) = P y)
    (hPPi : ∀ y, P (Pi y) = Pi y) (hUiso : ∀ y, ‖U y‖ = ‖y‖) (x M : E)
    (hM : Pi M = M) :
    ⟪U x, M⟫_ℂ = ⟪P x, M⟫_ℂ := by
  have hle := norm_centralizerCentered_defect_le_subspace U P Pi hPsymm hUP hPU hPP hPPi
    hUiso x M
  rw [hM, sub_self, norm_zero, mul_zero] at hle
  have : ‖⟪U x, M⟫_ℂ - ⟪P x, M⟫_ℂ‖ = 0 := le_antisymm hle (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

end Transfer

section CircuitUnion

/-- **`(9)`.**  One word above the fidelity threshold makes the replica moment absorb the whole
circuit union: the scaled average is already at least one. -/
theorem one_le_card_mul_inv_pow_mul_average
    {iota : Type*} [Fintype iota] (f : iota → ℝ) (hf : ∀ w, 0 ≤ f w)
    {a : ℝ} (ha : 0 < a) (r : ℕ) {w0 : iota} (hw0 : a ≤ f w0) :
    1 ≤ (Fintype.card iota : ℝ) * (a ^ r)⁻¹ *
      ((Fintype.card iota : ℝ)⁻¹ * ∑ w, f w ^ r) := by
  have hcard : 0 < (Fintype.card iota : ℝ) := by
    have : 0 < Fintype.card iota := Fintype.card_pos_iff.mpr ⟨w0⟩
    exact_mod_cast this
  have hsum : a ^ r ≤ ∑ w, f w ^ r := by
    refine le_trans (pow_le_pow_left₀ ha.le hw0 r) ?_
    exact Finset.single_le_sum (f := fun w => f w ^ r)
      (fun w _ => pow_nonneg (hf w) r) (Finset.mem_univ w0)
  have hapow : (0 : ℝ) < a ^ r := pow_pos ha r
  rw [show (Fintype.card iota : ℝ) * (a ^ r)⁻¹ *
      ((Fintype.card iota : ℝ)⁻¹ * ∑ w, f w ^ r) =
      (a ^ r)⁻¹ * ∑ w, f w ^ r by field_simp]
  calc
    (1 : ℝ) = (a ^ r)⁻¹ * a ^ r := by field_simp
    _ ≤ (a ^ r)⁻¹ * ∑ w, f w ^ r :=
      mul_le_mul_of_nonneg_left hsum (by positivity)

end CircuitUnion

end GaloisForLFunctions.HTGeometry
