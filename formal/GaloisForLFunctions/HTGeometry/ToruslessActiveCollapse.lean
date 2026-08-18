import GaloisForLFunctions.HTGeometry.ActiveQuasiAbelianPaletteHierarchy

/-!
# Where the active condition is vacuous

The active quotient is the quotient by the maximal compact complex subgroup.  When that subgroup is
trivial — the torusless case, of which the periodic-pencil quotient `ℂ*` is the model — the active
quotient is injective, so active faithfulness of a facet lattice is equivalent to faithfulness in
the full period quotient.

Consequently the quasi-Abelian and the active quasi-Abelian conditions differ only where some facet
quotient carries a positive-dimensional compact complex subtorus, and the two intrinsic dimensions
collapse on any class of palettes that is torusless at every facet.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A quotient map whose kernel is the trivial subgroup is injective. -/
theorem injective_of_ker_eq_bot {X Act : Type*} [AddCommGroup X] [AddCommGroup Act]
    (q : X →+ Act) (S : AddSubgroup X) (hker : ∀ x, q x = 0 ↔ x ∈ S) (hS : S = ⊥) :
    Function.Injective q := by
  refine (injective_iff_map_eq_zero q).mpr ?_
  intro x hx
  have hmem : x ∈ S := (hker x).mp hx
  rw [hS] at hmem
  simpa using hmem

/-- **The active condition is vacuous on a torusless quotient.**  With trivial compact shadow,
active faithfulness of a lattice is the same as faithfulness in the full period quotient. -/
theorem activeFaithful_iff_faithful_of_compactShadow_eq_bot
    {W X Act L : Type*} [AddCommGroup W] [AddCommGroup X] [AddCommGroup Act] [AddCommGroup L]
    (quotientMap : W →+ X) (activeQuotient : X →+ Act) (compactShadow : AddSubgroup X)
    (hker : ∀ x, activeQuotient x = 0 ↔ x ∈ compactShadow)
    (hS : compactShadow = ⊥) (lattice : L →+ W) :
    Function.Injective (activeQuotient.comp (quotientMap.comp lattice)) ↔
      Function.Injective (quotientMap.comp lattice) := by
  have hinj : Function.Injective activeQuotient :=
    injective_of_ker_eq_bot activeQuotient compactShadow hker hS
  constructor
  · intro h a b hab
    exact h (congrArg activeQuotient hab)
  · intro h a b hab
    exact h (hinj hab)

/-- On a torusless facet presentation the active quotient is injective. -/
theorem ActiveQuasiAbelianFacetPresentation.activeQuotient_injective_of_compactShadow_eq_bot
    {alpha : Type} [DecidableEq alpha] {F : Finset alpha}
    {d : ℕ} {a : alpha → Fin d → ℂ}
    (P : ActiveQuasiAbelianFacetPresentation alpha F d a)
    (hS : letI := P.addCommGroupX; P.compactShadow = ⊥) :
    letI := P.addCommGroupX
    letI := P.addCommGroupActive
    Function.Injective P.activeQuotient := by
  letI := P.addCommGroupX
  letI := P.addCommGroupActive
  exact injective_of_ker_eq_bot P.activeQuotient P.compactShadow P.activeQuotient_ker hS

/-- **Collapse on a torusless class.**  If every quasi-Abelian palette dimension of a complex is
also an active palette dimension — which is what torusless facet quotients give, since there the
active clause is implied by the lattice injectivity the quasi-Abelian palette already carries —
then the two intrinsic dimensions are equal. -/
theorem quasiAbelianPaletteDimension_eq_activeQuasiAbelianPaletteDimension_of_lift
    (alpha : Type) [Fintype alpha] [DecidableEq alpha]
    (facets : Finset (Finset alpha))
    (hlift : ∀ d, QuasiAbelianPaletteRealizable alpha facets d →
      ActiveQuasiAbelianPaletteRealizable.{0} alpha facets d) :
    quasiAbelianPaletteDimension alpha facets =
      activeQuasiAbelianPaletteDimension.{0} alpha facets := by
  have hset : {d | QuasiAbelianPaletteRealizable alpha facets d}
      = {d | ActiveQuasiAbelianPaletteRealizable.{0} alpha facets d} := by
    ext d
    exact ⟨hlift d, fun h => quasiAbelianPaletteRealizable_of_activeQuasiAbelianPaletteRealizable h⟩
  rw [quasiAbelianPaletteDimension, activeQuasiAbelianPaletteDimension, hset]

end

end GaloisForLFunctions.HTGeometry
