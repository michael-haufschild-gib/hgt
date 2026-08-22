import GaloisForLFunctions.HTGeometry.HaferkampFlattenedTerminalPhaseChart

/-!
# Real differential rank of the simultaneous terminal-phase chart

The full real Fréchet derivative has the selected terminal tangents as its
coordinate images. Complex independence of those tangents therefore yields
the Appendix-B real rank lower bound.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace BackwardsLightCone

/-- Complex independence of the terminal tangents also gives their real
linear independence. -/
theorem TerminalBlockPrefixAssembly.linearIndependent_terminalPhaseTangents
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone 1 labels)
    (hlabels : LinearIndependent ℂ (fun i : Fin labels.length =>
      finitePauliMatrix (labels.get i))) :
    LinearIndependent ℝ (fun i =>
      Complex.I • haferkampUnitaryListCoordinateOutput assembly.liftedWord
        (assembly.terminalIndices i)
        (finitePauliMatrix (Function.update (fun _ => none) root (some 2)))) := by
  exact LinearIndependent.restrict_scalars' ℝ
    ((assembly.linearIndependent_terminalCoordinateCurveTangents hlabels).1)

/-- The real tangent map of the simultaneous terminal-phase chart has range
dimension at least the number of selected terminal directions. -/
theorem TerminalBlockPrefixAssembly.finrank_range_ge_terminalPhaseTangents
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone 1 labels)
    (hlabels : LinearIndependent ℂ (fun i : Fin labels.length =>
      finitePauliMatrix (labels.get i))) :
    labels.length ≤ Module.finrank ℝ assembly.terminalPhaseTangentMap.range := by
  let D : (Fin labels.length → ℝ) →L[ℝ]
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ := assembly.terminalPhaseTangentMap
  change labels.length ≤ Module.finrank ℝ D.range
  have htangents := assembly.linearIndependent_terminalPhaseTangents hlabels
  have hsingle (i : Fin labels.length) :
      D (Pi.single i 1) =
        Complex.I • haferkampUnitaryListCoordinateOutput assembly.liftedWord
          (assembly.terminalIndices i)
          (finitePauliMatrix (Function.update (fun _ => none) root (some 2))) := by
    change assembly.terminalPhaseTangentMap (Pi.single i 1) = _
    simp [terminalPhaseTangentMap]
  have himages : LinearIndependent ℝ (fun i => D (Pi.single i 1)) := by
    simpa only [hsingle] using htangents
  let values : Fin labels.length → D.range :=
    fun i => ⟨D (Pi.single i 1), ⟨Pi.single i 1, rfl⟩⟩
  have hcomp : LinearIndependent ℝ (D.range.subtype ∘ values) := by
    simpa [values, Function.comp_def] using himages
  have hvalues : LinearIndependent ℝ values :=
    LinearIndependent.of_comp D.range.subtype hcomp
  calc
    labels.length = (Set.range values).finrank ℝ := by
      simpa using (linearIndependent_iff_card_eq_finrank_span.mp hvalues)
    _ = Module.finrank ℝ (Submodule.span ℝ (Set.range values)) := rfl
    _ ≤ Module.finrank ℝ D.range := Submodule.finrank_le _

/-- The actual real Fréchet derivative of the simultaneous chart has rank at
least the number of selected terminal directions. -/
theorem TerminalBlockPrefixAssembly.finrank_range_ge_terminalPhaseContraction_fderiv
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone 1 labels)
    (hlabels : LinearIndependent ℂ (fun i : Fin labels.length =>
      finitePauliMatrix (labels.get i))) :
    labels.length ≤ Module.finrank ℝ
      (fderiv ℝ (fun x => (assembly.terminalPhaseLiftedWord x).reverse.prod) 0).range := by
  have hderiv := assembly.hasFDerivAt_terminalPhaseContraction_zero.fderiv
  rw [hderiv]
  exact assembly.finrank_range_ge_terminalPhaseTangents hlabels

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
