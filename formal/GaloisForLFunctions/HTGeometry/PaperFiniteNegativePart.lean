import GaloisForLFunctions.HTGeometry.CompactOperatorBoundedBelow
import GaloisForLFunctions.RHTower.PositiveOperatorKernel

/-! # The canonical finite negative part of identity minus a compact operator

The full negative spectral part has finite-dimensional range. Its range is
strictly negative for the original form, while its orthogonal complement is
nonnegative. No eigenbasis or injectivity assumption on the compact operator is
needed.
-/

noncomputable section

open scoped CStarAlgebra

namespace GaloisForLFunctions.HTGeometry.PaperNegativePart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def repair (Q : E →L[ℂ] E) : E →L[ℂ] E := Q⁻

def negativeSpace (Q : E →L[ℂ] E) : Submodule ℂ E := (repair Q).toLinearMap.range

def negativeRank (Q : E →L[ℂ] E) : ℕ := Module.finrank ℂ (negativeSpace Q)

theorem repair_positive (Q : E →L[ℂ] E) : (repair Q).IsPositive :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).1 (CFC.negPart_nonneg Q)

theorem source_add_repair (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q) : Q + repair Q = Q⁺ := by
  have h := CFC.posPart_sub_negPart Q hQ
  change Q + Q⁻ = Q⁺
  exact (sub_eq_iff_eq_add.1 h).symm

theorem repaired_positive (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q) :
    (Q + repair Q).IsPositive := by
  rw [source_add_repair Q hQ]
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).1 (CFC.posPart_nonneg Q)

theorem negativeSpace_le_positive_ker (Q : E →L[ℂ] E) :
    negativeSpace Q ≤ Q⁺.toLinearMap.ker := by
  rintro x ⟨y, rfl⟩
  change Q⁺ (Q⁻ y) = 0
  have h := congrArg (fun T : E →L[ℂ] E => T y) (CFC.posPart_mul_negPart Q)
  exact h

theorem source_apply_negative_closure (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q)
    {x : E} (hx : x ∈ (negativeSpace Q).topologicalClosure) : Q x = -(repair Q x) := by
  have hk := (negativeSpace Q).topologicalClosure_minimal
    (negativeSpace_le_positive_ker Q) Q⁺.isClosed_ker hx
  have he := congrArg (fun T : E →L[ℂ] E => T x) (source_add_repair Q hQ)
  change Q x + repair Q x = Q⁺ x at he
  change Q⁺ x = 0 at hk
  rw [hk] at he
  exact eq_neg_of_add_eq_zero_left he

theorem source_apply_negative (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q)
    {x : E} (hx : x ∈ negativeSpace Q) : Q x = -(repair Q x) :=
  source_apply_negative_closure Q hQ ((negativeSpace Q).le_topologicalClosure hx)

theorem finiteDimensional_negativeSpace (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q)
    (hcompact : IsCompactOperator (1 - Q : E →L[ℂ] E)) : FiniteDimensional ℂ (negativeSpace Q) := by
  let N := (negativeSpace Q).topologicalClosure
  have hN : FiniteDimensional ℂ N := by
    apply finiteDimensional_of_isCompactOperator_of_bounded_below hcompact N
      (negativeSpace Q).isClosed_topologicalClosure (c := 1) zero_lt_one
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    have hneg : (inner ℂ (Q x) x).re ≤ 0 := by
      rw [source_apply_negative_closure Q hQ hx, inner_neg_left, Complex.neg_re]
      exact neg_nonpos.2 ((repair_positive Q).re_inner_nonneg_left x)
    have hinner : ‖x‖ ^ 2 ≤ (inner ℂ ((1 - Q) x) x).re := by
      simp only [sub_apply, one_apply_eq_self, inner_sub_left, Complex.sub_re]
      have hself : (inner ℂ x x).re = ‖x‖ ^ 2 :=
        (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
      rw [hself]
      linarith
    have hcs := (Complex.re_le_norm (inner ℂ ((1 - Q) x) x)).trans
      (norm_inner_le_norm (𝕜 := ℂ) ((1 - Q) x) x)
    have hp := norm_pos_iff.2 hx0
    simp only [one_mul]
    nlinarith
  letI := hN
  exact Submodule.finiteDimensional_of_le (negativeSpace Q).le_topologicalClosure

theorem repair_apply_eq_zero_on_range (Q : E →L[ℂ] E) {x : E}
    (hx : x ∈ negativeSpace Q) (hzero : repair Q x = 0) : x = 0 := by
  obtain ⟨y, hy⟩ := hx
  change repair Q y = x at hy
  have hself : inner ℂ x x = 0 := by
    calc
      _ = inner ℂ (repair Q y) x := by rw [hy]
      _ = inner ℂ y (repair Q x) := (repair_positive Q).inner_left_eq_inner_right y x
      _ = 0 := by rw [hzero, inner_zero_right]
  exact inner_self_eq_zero.1 hself

theorem repair_inner_pos_on_range (Q : E →L[ℂ] E) {x : E}
    (hx : x ∈ negativeSpace Q) (hx0 : x ≠ 0) : 0 < (inner ℂ (repair Q x) x).re := by
  apply lt_of_le_of_ne ((repair_positive Q).re_inner_nonneg_left x)
  intro hzero
  have hi : inner ℂ (repair Q x) x = 0 := by
    apply Complex.ext
    · exact hzero.symm
    · exact ((Complex.nonneg_iff).1 ((repair_positive Q).inner_nonneg_left x)).2.symm
  have hz : inner ℂ x (repair Q x) = 0 := by
    rw [← inner_conj_symm, hi, map_zero]
  exact hx0 (repair_apply_eq_zero_on_range Q hx
    ((repair_positive Q).apply_eq_zero_of_inner_eq_zero hz))

theorem negativeSpace_strict (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q) {x : E}
    (hx : x ∈ negativeSpace Q) (hx0 : x ≠ 0) : (inner ℂ (Q x) x).re < 0 := by
  rw [source_apply_negative Q hQ hx, inner_neg_left, Complex.neg_re]
  exact neg_neg_of_pos (repair_inner_pos_on_range Q hx hx0)

theorem repair_zero_of_orthogonal (Q : E →L[ℂ] E) {x : E}
    (hx : x ∈ (negativeSpace Q)ᗮ) : repair Q x = 0 := by
  have hinner : inner ℂ (repair Q x) x = 0 :=
    (Submodule.mem_orthogonal _ _).1 hx _ ⟨x, rfl⟩
  apply (repair_positive Q).apply_eq_zero_of_inner_eq_zero
  rw [← inner_conj_symm, hinner, map_zero]

theorem nonnegative_on_orthogonal (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q) {x : E}
    (hx : x ∈ (negativeSpace Q)ᗮ) : 0 ≤ (inner ℂ (Q x) x).re := by
  have hp := (repaired_positive Q hQ).re_inner_nonneg_left x
  change 0 ≤ (inner ℂ ((Q + repair Q) x) x).re at hp
  simpa only [add_apply, repair_zero_of_orthogonal Q hx, add_zero] using hp

theorem repair_eq_zero_iff (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q) :
    repair Q = 0 ↔ Q.IsPositive := by
  exact (CFC.negPart_eq_zero_iff Q hQ).trans (ContinuousLinearMap.nonneg_iff_isPositive Q)

end GaloisForLFunctions.HTGeometry.PaperNegativePart
