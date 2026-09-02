import GaloisForLFunctions.HTGeometry.TorusChartCoverGeneratorRigidity

/-!
# Closed lifts fix covering monodromy

A closed loop in any space mapping to the total space of a cover supplies a closed lift of its
projected base loop.  Uniqueness of covering lifts therefore says that the projected monodromy
fixes the selected sheet.
-/

namespace GaloisForLFunctions.HTGeometry

open Path

universe u v

variable {X : Type u} {E : Type v} {k : ℕ}
  [TopologicalSpace X] [TopologicalSpace E]
  (p : E → ComplexTorusAffineChart k) (cov : IsCoveringMap p)
  (f : X → E) (hf : Continuous f)

/-- **A closed lift fixes monodromy.**  The class of a closed source loop, projected through a map
to the total space of a cover, fixes the corresponding point of the cover fibre. -/
theorem covering_monodromy_fixed_of_closed_lift
    (x : X) (hx : p (f x) = (1 : ComplexTorusAffineChart k))
    (delta : Path.Homotopic.Quotient x x) :
    cov.monodromy
      ((delta.map ((⟨p, cov.continuous⟩ : C(E, ComplexTorusAffineChart k)).comp
        ⟨f, hf⟩)).cast hx.symm hx.symm)
      (⟨f x, by simpa using hx⟩ : p ⁻¹' {(1 : ComplexTorusAffineChart k)}) =
      ⟨f x, by simpa using hx⟩ := by
  let Gamma : Path.Homotopic.Quotient (f x) (f x) := delta.map ⟨f, hf⟩
  apply cov.monodromy_eq_of_map_eq Gamma
  have hmap := (Path.Homotopic.Quotient.map_comp
    (p := delta) (f := ⟨f, hf⟩) (g := ⟨p, cov.continuous⟩)).symm
  simpa [Gamma] using hmap

/-- Closed-lift monodromy, with the projected source map supplied by name.  The equality is
eliminated before path casts are formed, avoiding any dependent rewriting at call sites. -/
theorem covering_monodromy_fixed_of_closed_lift_of_eq
    (q : C(X, ComplexTorusAffineChart k))
    (hq : q = (⟨p, cov.continuous⟩ : C(E, ComplexTorusAffineChart k)).comp ⟨f, hf⟩)
    (x : X) (hx : q x = (1 : ComplexTorusAffineChart k))
    (delta : Path.Homotopic.Quotient x x) :
    cov.monodromy ((delta.map q).cast hx.symm hx.symm)
      (⟨f x, by simpa [hq] using hx⟩ : p ⁻¹' {(1 : ComplexTorusAffineChart k)}) =
      ⟨f x, by simpa [hq] using hx⟩ := by
  subst q
  exact covering_monodromy_fixed_of_closed_lift p cov f hf x hx delta

end GaloisForLFunctions.HTGeometry
