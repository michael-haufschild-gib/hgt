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

/-- Fixed monodromy at an arbitrary basepoint transports along a connector.  Two conjugate loops
therefore fix the same transported sheet in the connector's source fibre. -/
theorem covering_monodromy_two_conjugates_fixed_transport
    {Z : Type u} {E : Type v} [TopologicalSpace Z] [TopologicalSpace E]
    {p : E → Z} (cov : IsCoveringMap p) {x₀ y : Z}
    (alpha : Path.Homotopic.Quotient x₀ y) (eY : p ⁻¹' {y})
    (deltaFirst deltaSecond : Path.Homotopic.Quotient y y)
    (hfixFirst : cov.monodromy deltaFirst eY = eY)
    (hfixSecond : cov.monodromy deltaSecond eY = eY)
    (gFirst gSecond : Path.Homotopic.Quotient x₀ x₀)
    (hfirst : alpha.trans (deltaFirst.trans alpha.symm) = gFirst)
    (hsecond : alpha.trans (deltaSecond.trans alpha.symm) = gSecond) :
    ∃ e : p ⁻¹' {x₀},
      cov.monodromy gFirst e = e ∧ cov.monodromy gSecond e = e := by
  obtain ⟨e, he⟩ := (cov.monodromy_bijective alpha).2 eY
  have hinv : cov.monodromy alpha.symm eY = e := by
    rw [← he, ← cov.monodromy_trans_apply]
    simpa using congrFun cov.monodromy_refl e
  have hconjFirst :
      cov.monodromy (alpha.trans (deltaFirst.trans alpha.symm)) e = e := by
    calc
      _ = cov.monodromy (deltaFirst.trans alpha.symm)
          (cov.monodromy alpha e) := cov.monodromy_trans_apply _ _ _
      _ = cov.monodromy (deltaFirst.trans alpha.symm) eY := by rw [he]
      _ = cov.monodromy alpha.symm (cov.monodromy deltaFirst eY) :=
        cov.monodromy_trans_apply _ _ _
      _ = cov.monodromy alpha.symm eY := by rw [hfixFirst]
      _ = e := hinv
  have hconjSecond :
      cov.monodromy (alpha.trans (deltaSecond.trans alpha.symm)) e = e := by
    calc
      _ = cov.monodromy (deltaSecond.trans alpha.symm)
          (cov.monodromy alpha e) := cov.monodromy_trans_apply _ _ _
      _ = cov.monodromy (deltaSecond.trans alpha.symm) eY := by rw [he]
      _ = cov.monodromy alpha.symm (cov.monodromy deltaSecond eY) :=
        cov.monodromy_trans_apply _ _ _
      _ = cov.monodromy alpha.symm eY := by rw [hfixSecond]
      _ = e := hinv
  refine ⟨e, ?_, ?_⟩
  · rw [← hfirst]
    exact hconjFirst
  · rw [← hsecond]
    exact hconjSecond

variable {X : Type u} {E : Type v} {k : ℕ}
  [TopologicalSpace X] [TopologicalSpace E]
  (p : E → ComplexTorusAffineChart k) (cov : IsCoveringMap p)
  (f : X → E) (hf : Continuous f)

/-- A closed source loop fixes the selected sheet in the fibre over its actual projected
basepoint. -/
theorem covering_monodromy_fixed_of_closed_lift_at
    (x : X) (delta : Path.Homotopic.Quotient x x) :
    cov.monodromy
      (delta.map ((⟨p, cov.continuous⟩ : C(E, ComplexTorusAffineChart k)).comp
        ⟨f, hf⟩))
      (⟨f x, rfl⟩ : p ⁻¹' {p (f x)}) = ⟨f x, rfl⟩ := by
  let Gamma : Path.Homotopic.Quotient (f x) (f x) := delta.map ⟨f, hf⟩
  apply cov.monodromy_eq_of_map_eq Gamma
  have hmap := (Path.Homotopic.Quotient.map_comp
    (p := delta) (f := ⟨f, hf⟩) (g := ⟨p, cov.continuous⟩)).symm
  simpa [Gamma] using hmap

/-- Arbitrary-basepoint closed-lift monodromy with the projected source map supplied by name. -/
theorem covering_monodromy_fixed_of_closed_lift_at_of_eq
    (q : C(X, ComplexTorusAffineChart k))
    (hq : q = (⟨p, cov.continuous⟩ : C(E, ComplexTorusAffineChart k)).comp ⟨f, hf⟩)
    (x : X) (delta : Path.Homotopic.Quotient x x) :
    cov.monodromy (delta.map q)
      (⟨f x, by simpa [hq]⟩ : p ⁻¹' {q x}) =
      ⟨f x, by simpa [hq]⟩ := by
  subst q
  exact covering_monodromy_fixed_of_closed_lift_at p cov f hf x delta

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
