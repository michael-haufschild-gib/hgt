import GaloisForLFunctions.HTGeometry.TorusChartFundamentalGroup

/-!
# A bounded representative of the chosen generator of `π₁(ℂˣ)`

Every fundamental-group class has a literal path representative.  Compactness of that path
also permits a nonzero scalar multiple lying strictly inside the complex unit disk.  This is the
small meridian used to keep simultaneous source-chart coordinates nonvanishing.
-/

namespace GaloisForLFunctions.HTGeometry

open Path unitInterval

noncomputable section

/-- A literal loop representing the canonical-by-choice generator of `π₁(ℂˣ, 1)`. -/
noncomputable def complexUnitsFundamentalGeneratorPath : Path (1 : Units ℂ) 1 :=
  Classical.choose (Path.Homotopic.Quotient.mk_surjective
    complexUnitsFundamentalGenerator)

theorem complexUnitsFundamentalGeneratorPath_mk :
    Path.Homotopic.Quotient.mk complexUnitsFundamentalGeneratorPath =
      complexUnitsFundamentalGenerator :=
  Classical.choose_spec (Path.Homotopic.Quotient.mk_surjective
    complexUnitsFundamentalGenerator)

/-- Every loop in `ℂˣ` admits a nonzero scalar multiple whose complex norm is pointwise
strictly less than one. -/
theorem exists_scale_mul_complexUnitsPath_norm_lt_one
    (g : Path (1 : Units ℂ) 1) :
    ∃ epsilon : ℂ, epsilon ≠ 0 ∧ ∀ t, ‖epsilon * (g t : ℂ)‖ < 1 := by
  let f : unitInterval → ℝ := fun t ↦ ‖(g t : ℂ)‖
  have hf : Continuous f := by fun_prop
  obtain ⟨tmax, _htmax, hmax⟩ :=
    isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.continuousOn
  let M : ℝ := f tmax
  have hM : 0 ≤ M := norm_nonneg _
  have hbound : ∀ t, f t ≤ M := by
    intro t
    exact hmax (Set.mem_univ t)
  refine ⟨((M + 1 : ℝ) : ℂ)⁻¹, ?_, ?_⟩
  · exact inv_ne_zero (by exact_mod_cast (by positivity : M + 1 ≠ 0))
  · intro t
    rw [norm_mul, norm_inv, Complex.norm_real]
    have hpos : 0 < M + 1 := by linarith
    rw [Real.norm_of_nonneg (le_of_lt hpos)]
    calc
      (M + 1)⁻¹ * ‖(g t : ℂ)‖ ≤ (M + 1)⁻¹ * M := by
        gcongr
        exact hbound t
      _ < 1 := by
        rw [inv_mul_lt_one₀ hpos]
        linarith

end

end GaloisForLFunctions.HTGeometry
