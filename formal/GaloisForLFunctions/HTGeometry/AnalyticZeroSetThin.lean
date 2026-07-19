import GaloisForLFunctions.HTGeometry.DenseGoodShiftSet

/-!
# Zero sets of analytic functions are thin

An analytic function on a preconnected open set that is nonzero somewhere has a zero set with empty
interior, and its complement is dense.  This packages the identity theorem in the form the
degeneracy analysis uses: a degeneracy locus arising as the zero set of a single analytic quantity
cannot be fat, whatever else is true of it.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The zero set of a nonzero analytic function has empty interior.** -/
theorem interior_zeroSet_eq_empty_of_analytic
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    {z₁ : ℂ} (hfz₁ : f z₁ ≠ 0) :
    interior {z : ℂ | f z = 0} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro z₀ hz₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior z₀ hz₀
  obtain ⟨z, hdist, hne⟩ :=
    exists_ne_zero_on_line hf hfz₁ z₀ hε
  have hzint : z ∈ interior {w : ℂ | f w = 0} :=
    hball (by simpa [Metric.mem_ball] using hdist)
  have hzmem : z ∈ {w : ℂ | f w = 0} := interior_subset hzint
  exact hne hzmem

/-- The complement of the zero set of a nonzero analytic function is dense. -/
theorem dense_compl_zeroSet_of_analytic
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    {z₁ : ℂ} (hfz₁ : f z₁ ≠ 0) :
    Dense {z : ℂ | f z ≠ 0} := by
  have h := interior_eq_empty_iff_dense_compl.1 (interior_zeroSet_eq_empty_of_analytic hf hfz₁)
  simpa using h

/-- **A single analytic degeneracy cannot block a whole line.**  If a quantity restricted to a
translation line is analytic and nonzero somewhere, the shifts of that line at which it degenerates
have empty interior — so degeneracy along the line is confined to isolated points. -/
theorem interior_lineDegeneracy_eq_empty
    {S : Type*} (act : ℂ → S → S) (val : S → ℂ) (s : S)
    (hline : AnalyticOnNhd ℂ (fun t => val (act t s)) Set.univ)
    {t₁ : ℂ} (hne : val (act t₁ s) ≠ 0) :
    interior {t : ℂ | val (act t s) = 0} = ∅ :=
  interior_zeroSet_eq_empty_of_analytic hline hne

end

end GaloisForLFunctions.HTGeometry
