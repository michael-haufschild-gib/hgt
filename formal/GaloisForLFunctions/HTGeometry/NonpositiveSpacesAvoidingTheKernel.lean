import GaloisForLFunctions.HTGeometry.PaperNegativePartInertia

/-!
# Nonpositive spaces avoiding the kernel

The canonical negative-part repair injects every nonpositive subspace
disjoint from the operator kernel into the negative spectral space.
This includes null directions whose pairing with the ambient space is nonzero.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PaperNegativePart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Nonpositive directions cost negative rank unless they lie in the full kernel. -/
theorem nonpositive_subspace_dimension_le (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q)
    [FiniteDimensional ℂ (negativeSpace Q)] (W : Submodule ℂ E)
    (hW : ∀ x ∈ W, (inner ℂ (Q x) x).re ≤ 0)
    (hker : ∀ x ∈ W, Q x = 0 → x = 0) :
    FiniteDimensional ℂ W ∧ Module.finrank ℂ W ≤ negativeRank Q := by
  let L : W →ₗ[ℂ] negativeSpace Q :=
    ((repair Q).toLinearMap.comp W.subtype).codRestrict _ (fun x => ⟨x, rfl⟩)
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hC : repair Q (x : E) = 0 := congrArg Subtype.val hx
    have hp := repaired_positive Q hQ
    have hre : (inner ℂ ((Q + repair Q) (x : E)) (x : E)).re = 0 := by
      have hnonpos : (inner ℂ ((Q + repair Q) (x : E)) (x : E)).re ≤ 0 := by
        rw [add_apply, hC, add_zero]
        exact hW x x.property
      exact le_antisymm hnonpos (hp.re_inner_nonneg_left x)
    have hi : inner ℂ ((Q + repair Q) (x : E)) (x : E) = 0 := by
      apply Complex.ext
      · exact hre
      · exact ((Complex.nonneg_iff).1 (hp.inner_nonneg_left x)).2.symm
    have hz := hp.apply_eq_zero_of_inner_eq_zero
      (show inner ℂ (x : E) ((Q + repair Q) (x : E)) = 0 by
        rw [← inner_conj_symm, hi, map_zero])
    rw [add_apply, hC, add_zero] at hz
    exact Subtype.ext (hker x x.property hz)
  exact ⟨FiniteDimensional.of_injective L hinj, LinearMap.finrank_le_finrank_of_injective hinj⟩

/-- Negative spectral vectors cannot belong to the kernel. -/
theorem negativeSpace_disjoint_ker (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q) :
    Disjoint (negativeSpace Q) Q.toLinearMap.ker := by
  rw [Submodule.disjoint_def]
  intro x hx hker
  by_contra hx0
  have h := negativeSpace_strict Q hQ hx hx0
  change Q x = 0 at hker
  simpa only [hker, inner_zero_left, Complex.zero_re, lt_self_iff_false] using h

/-- The negative space plus the kernel is nonpositive, including all null modes. -/
theorem nonpositive_on_negativeSpace_sup_ker (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q)
    {x : E} (hx : x ∈ negativeSpace Q ⊔ Q.toLinearMap.ker) :
    (inner ℂ (Q x) x).re ≤ 0 := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
  change Q v = 0 at hv
  have hcross : inner ℂ (Q u) v = 0 := by
    calc inner ℂ (Q u) v = inner ℂ u (Q v) := hQ.isSymmetric u v
      _ = 0 := by rw [hv, inner_zero_right]
  simp only [map_add, hv, add_zero, inner_add_right, hcross, add_zero]
  by_cases hu0 : u = 0
  · simp only [hu0, map_zero, inner_zero_left, Complex.zero_re, le_refl]
  · exact (negativeSpace_strict Q hQ hu hu0).le

/-- Identity minus compact has finite-dimensional kernel. -/
theorem finiteDimensional_kernel_of_one_sub_compact (Q : E →L[ℂ] E)
    (hc : IsCompactOperator (1 - Q : E →L[ℂ] E)) :
    FiniteDimensional ℂ Q.toLinearMap.ker := by
  apply finiteDimensional_of_isCompactOperator_of_bounded_below hc Q.toLinearMap.ker
    Q.isClosed_ker (c := 1) zero_lt_one
  intro x hx
  change Q x = 0 at hx
  simp only [sub_apply, one_apply_eq_self, hx, sub_zero, one_mul, le_refl]

/-- A nonpositive vector orthogonal to the negative space must be a null mode. -/
theorem apply_eq_zero_of_nonpositive_orthogonal (Q : E →L[ℂ] E)
    (hQ : IsSelfAdjoint Q) {x : E} (hx : x ∈ (negativeSpace Q)ᗮ)
    (hq : (inner ℂ (Q x) x).re ≤ 0) : Q x = 0 := by
  have hC := repair_zero_of_orthogonal Q hx
  have hp := repaired_positive Q hQ
  have hre : (inner ℂ ((Q + repair Q) x) x).re = 0 := by
    have hnonpos : (inner ℂ ((Q + repair Q) x) x).re ≤ 0 := by
      rw [add_apply, hC, add_zero]
      exact hq
    exact le_antisymm hnonpos (hp.re_inner_nonneg_left x)
  have hi : inner ℂ ((Q + repair Q) x) x = 0 := by
    apply Complex.ext
    · exact hre
    · exact ((Complex.nonneg_iff).1 (hp.inner_nonneg_left x)).2.symm
  have hz := hp.apply_eq_zero_of_inner_eq_zero
    (show inner ℂ x ((Q + repair Q) x) = 0 by
      rw [← inner_conj_symm, hi, map_zero])
  simpa only [add_apply, hC, add_zero] using hz

end GaloisForLFunctions.HTGeometry.PaperNegativePart
