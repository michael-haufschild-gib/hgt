import GaloisForLFunctions.HTGeometry.NonautonomousFiniteCascadeTerminalWimanValuation
import GaloisForLFunctions.HTGeometry.ABHN.LaurentSeriesFiniteLocalField
import GaloisForLFunctions.HTGeometry.ValuationSubringResidueComapMap

/-!
# Exact residue coefficient of the terminal Wiman unit

The outer Laurent residue of a power-series unit is its literal constant coefficient.  Pulling
the outer valuation back along any field embedding transports this identity to the source
residue field.  This records the inner Wiman coefficient before any terminal-inward refinement.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped LaurentSeries

noncomputable section

/-- The canonical residue equivalence sends a power series, viewed inside the standard Laurent
valuation ring, to its constant coefficient. -/
theorem laurentSeriesResidueFieldEquiv_residue_coe
    (F : Type*) [Field F] (p : PowerSeries F)
    (hp : algebraMap (PowerSeries F) (LaurentSeries F) p ∈
      laurentSeriesValuationSubring F) :
    ABHN.laurentSeriesResidueFieldEquiv F
        (IsLocalRing.residue (laurentSeriesValuationSubring F)
          (⟨algebraMap (PowerSeries F) (LaurentSeries F) p, hp⟩ :
            laurentSeriesValuationSubring F)) =
      PowerSeries.constantCoeff p := by
  apply ABHN.laurentSeriesResidueFieldEquiv_residue_powerSeries

/-- The canonical Laurent residue equivalence sends an integral coefficient constant to that
coefficient. -/
theorem laurentSeriesResidueFieldEquiv_residue_algebraMap
    (F : Type*) [Field F] (c : F)
    (hc : algebraMap F (LaurentSeries F) c ∈
      laurentSeriesValuationSubring F) :
    ABHN.laurentSeriesResidueFieldEquiv F
        (IsLocalRing.residue (laurentSeriesValuationSubring F)
          (⟨algebraMap F (LaurentSeries F) c, hc⟩ :
            laurentSeriesValuationSubring F)) = c := by
  let p : PowerSeries F := PowerSeries.C c
  have hconst : algebraMap F (LaurentSeries F) c =
      HahnSeries.single 0 c := by
    change HahnSeries.ofPowerSeries ℤ F
        (algebraMap F (PowerSeries F) c) = HahnSeries.single 0 c
    rw [PowerSeries.algebraMap_apply]
    simp
  have hpconst : algebraMap (PowerSeries F) (LaurentSeries F) p =
      HahnSeries.single 0 c := by
    change HahnSeries.ofPowerSeries ℤ F (PowerSeries.C c) =
      HahnSeries.single 0 c
    rw [HahnSeries.ofPowerSeries_C, HahnSeries.C_apply]
  have hp : algebraMap (PowerSeries F) (LaurentSeries F) p ∈
      laurentSeriesValuationSubring F := by
    rw [hpconst, ← hconst]
    exact hc
  have heq : (⟨algebraMap F (LaurentSeries F) c, hc⟩ :
      laurentSeriesValuationSubring F) =
      ⟨algebraMap (PowerSeries F) (LaurentSeries F) p, hp⟩ := by
    apply Subtype.ext
    exact hconst.trans hpconst.symm
  rw [heq]
  simpa [p] using laurentSeriesResidueFieldEquiv_residue_coe F p hp

/-- Faithful coefficient realization of the residue field of an exact pullback of the outer
terminal Laurent valuation. -/
noncomputable def firstOrderTerminalCoefficientResidueEmbedding
    {E : Type*} [Field E] (phi : E →+* FirstOrderTerminalLaurentField) :
    IsLocalRing.ResidueField
        ((laurentSeriesValuationSubring
          FirstOrderTerminalCoefficientField).comap phi) →+*
      FirstOrderTerminalCoefficientField :=
  (ABHN.laurentSeriesResidueFieldEquiv
      FirstOrderTerminalCoefficientField).toRingHom.comp
    (valuationSubringResidueMapOfComapEq phi
      ((laurentSeriesValuationSubring
        FirstOrderTerminalCoefficientField).comap phi)
      (laurentSeriesValuationSubring FirstOrderTerminalCoefficientField) rfl)

/-- The coefficient realization of a pulled-back outer residue field is injective. -/
theorem firstOrderTerminalCoefficientResidueEmbedding_injective
    {E : Type*} [Field E] (phi : E →+* FirstOrderTerminalLaurentField) :
    Function.Injective (firstOrderTerminalCoefficientResidueEmbedding phi) :=
  RingHom.injective _

/-- A chosen exact prolongation of the inner Laurent valuation to its algebraic closure, which is
the terminal coefficient field. -/
noncomputable def firstOrderTerminalInnerValuationSubring :
    ValuationSubring FirstOrderTerminalCoefficientField :=
  (exists_valuationSubring_extension_comap_eq
    (laurentSeriesValuationSubring ℂ)
    (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField)).choose

/-- The chosen inner coefficient valuation contracts to exactly the standard Laurent valuation. -/
theorem firstOrderTerminalInnerValuationSubring_comap :
    firstOrderTerminalInnerValuationSubring.comap
        (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField) =
      laurentSeriesValuationSubring ℂ :=
  (exists_valuationSubring_extension_comap_eq
    (laurentSeriesValuationSubring ℂ)
    (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField)).choose_spec

/-- Inner Wiman valuation pulled back to the residue field of a literal terminal component. -/
noncomputable def firstOrderTerminalPulledInnerResidueValuationSubring
    {E : Type*} [Field E] (phi : E →+* FirstOrderTerminalLaurentField) :
    ValuationSubring
      (IsLocalRing.ResidueField
        ((laurentSeriesValuationSubring
          FirstOrderTerminalCoefficientField).comap phi)) :=
  firstOrderTerminalInnerValuationSubring.comap
    (firstOrderTerminalCoefficientResidueEmbedding phi)

/-- Membership in the pulled-back inner residue valuation is literal coefficient-field
integrality. -/
theorem mem_firstOrderTerminalPulledInnerResidueValuationSubring_iff
    {E : Type*} [Field E] (phi : E →+* FirstOrderTerminalLaurentField)
    (x : IsLocalRing.ResidueField
      ((laurentSeriesValuationSubring
        FirstOrderTerminalCoefficientField).comap phi)) :
    x ∈ firstOrderTerminalPulledInnerResidueValuationSubring phi ↔
      firstOrderTerminalCoefficientResidueEmbedding phi x ∈
        firstOrderTerminalInnerValuationSubring := by
  rfl

/-- Integrality of an embedded inner Laurent element is reflected exactly by the chosen algebraic
closure prolongation. -/
theorem algebraMap_mem_firstOrderTerminalInnerValuationSubring_iff
    (x : LaurentSeries ℂ) :
    algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField x ∈
        firstOrderTerminalInnerValuationSubring ↔
      x ∈ laurentSeriesValuationSubring ℂ := by
  change x ∈ firstOrderTerminalInnerValuationSubring.comap
      (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField) ↔ _
  rw [firstOrderTerminalInnerValuationSubring_comap]

/-- Along an exact pullback of the outer terminal Laurent valuation, the residue of an element
mapped to a power-series unit is exactly that unit's constant coefficient. -/
theorem firstOrderTerminalResidue_coefficient
    {E : Type*} [Field E]
    (φ : E →+* FirstOrderTerminalLaurentField) (x : E)
    (z : PowerSeries FirstOrderTerminalCoefficientField)
    (hx : φ x = algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
      FirstOrderTerminalLaurentField z)
    (hxA : x ∈ (laurentSeriesValuationSubring
      FirstOrderTerminalCoefficientField).comap φ) :
    let A := (laurentSeriesValuationSubring
      FirstOrderTerminalCoefficientField).comap φ
    ABHN.laurentSeriesResidueFieldEquiv FirstOrderTerminalCoefficientField
      (valuationSubringResidueMapOfComapEq φ A
        (laurentSeriesValuationSubring FirstOrderTerminalCoefficientField) rfl
        (IsLocalRing.residue A (⟨x, hxA⟩ : A))) =
      PowerSeries.constantCoeff z := by
  dsimp only
  rw [valuationSubringResidueMapOfComapEq_residue]
  rw [show (⟨φ x, by exact hxA⟩ :
      laurentSeriesValuationSubring FirstOrderTerminalCoefficientField) =
        ⟨algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
          FirstOrderTerminalLaurentField z, by simpa [← hx] using hxA⟩ by
      apply Subtype.ext
      exact hx]
  exact laurentSeriesResidueFieldEquiv_residue_coe _ z _

/-- The coefficient realization sends the residue of a source power-series unit to its literal
constant coefficient. -/
theorem firstOrderTerminalCoefficientResidueEmbedding_residue_coe
    {E : Type*} [Field E] (phi : E →+* FirstOrderTerminalLaurentField)
    (x : E) (z : PowerSeries FirstOrderTerminalCoefficientField)
    (hx : phi x = algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
      FirstOrderTerminalLaurentField z)
    (hxA : x ∈ (laurentSeriesValuationSubring
      FirstOrderTerminalCoefficientField).comap phi) :
    firstOrderTerminalCoefficientResidueEmbedding phi
        (IsLocalRing.residue
          ((laurentSeriesValuationSubring
            FirstOrderTerminalCoefficientField).comap phi)
          (⟨x, hxA⟩ : (laurentSeriesValuationSubring
            FirstOrderTerminalCoefficientField).comap phi)) =
      PowerSeries.constantCoeff z := by
  exact firstOrderTerminalResidue_coefficient phi x z hx hxA

/-- The coefficient realization sends the residue of a source element mapped to an outer
coefficient constant to that literal coefficient. -/
theorem firstOrderTerminalCoefficientResidueEmbedding_residue_algebraMap
    {E : Type*} [Field E] (phi : E →+* FirstOrderTerminalLaurentField)
    (x : E) (c : FirstOrderTerminalCoefficientField)
    (hx : phi x = algebraMap FirstOrderTerminalCoefficientField
      FirstOrderTerminalLaurentField c)
    (hxA : x ∈ (laurentSeriesValuationSubring
      FirstOrderTerminalCoefficientField).comap phi) :
    firstOrderTerminalCoefficientResidueEmbedding phi
        (IsLocalRing.residue
          ((laurentSeriesValuationSubring
            FirstOrderTerminalCoefficientField).comap phi)
          (⟨x, hxA⟩ : (laurentSeriesValuationSubring
            FirstOrderTerminalCoefficientField).comap phi)) = c := by
  change ABHN.laurentSeriesResidueFieldEquiv FirstOrderTerminalCoefficientField
      (valuationSubringResidueMapOfComapEq phi
        ((laurentSeriesValuationSubring
          FirstOrderTerminalCoefficientField).comap phi)
        (laurentSeriesValuationSubring FirstOrderTerminalCoefficientField) rfl
        (IsLocalRing.residue
          ((laurentSeriesValuationSubring
            FirstOrderTerminalCoefficientField).comap phi)
          (⟨x, hxA⟩ : (laurentSeriesValuationSubring
            FirstOrderTerminalCoefficientField).comap phi))) = c
  rw [valuationSubringResidueMapOfComapEq_residue]
  have hc : algebraMap FirstOrderTerminalCoefficientField
      FirstOrderTerminalLaurentField c ∈
        laurentSeriesValuationSubring FirstOrderTerminalCoefficientField := by
    simpa [← hx] using hxA
  have heq : (⟨phi x, by exact hxA⟩ :
      laurentSeriesValuationSubring FirstOrderTerminalCoefficientField) =
      ⟨algebraMap FirstOrderTerminalCoefficientField
        FirstOrderTerminalLaurentField c, hc⟩ := by
    apply Subtype.ext
    exact hx
  rw [heq]
  exact laurentSeriesResidueFieldEquiv_residue_algebraMap
    FirstOrderTerminalCoefficientField c hc

/-- The pulled-back inner Wiman valuation prolongs exactly from a terminal-component residue field
to the residue field of every exact outer valuation prolongation. -/
theorem exists_firstOrderTerminalPulledInnerResidueValuation_extension
    {E K : Type*} [Field E] [Field K]
    (phi : E →+* FirstOrderTerminalLaurentField) (g : E →+* K)
    (B : ValuationSubring K)
    (hB : B.comap g = (laurentSeriesValuationSubring
      FirstOrderTerminalCoefficientField).comap phi) :
    let A := (laurentSeriesValuationSubring
      FirstOrderTerminalCoefficientField).comap phi
    ∃ C : ValuationSubring (IsLocalRing.ResidueField B),
      C.comap (valuationSubringResidueMapOfComapEq g A B hB) =
        firstOrderTerminalPulledInnerResidueValuationSubring phi := by
  dsimp only
  exact exists_valuationSubring_extension_comap_eq
    (firstOrderTerminalPulledInnerResidueValuationSubring phi)
    (valuationSubringResidueMapOfComapEq g _ B hB)

/-- The same source residue class simultaneously remembers its exact Wiman coefficient in the
outer Laurent residue field and becomes the literal residue of the corresponding element in every
exact valuation prolongation. -/
theorem firstOrderTerminalResidue_coefficient_and_extension
    {E K : Type*} [Field E] [Field K]
    (φ : E →+* FirstOrderTerminalLaurentField) (g : E →+* K)
    (B : ValuationSubring K)
    (x : E) (z : PowerSeries FirstOrderTerminalCoefficientField)
    (hx : φ x = algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
      FirstOrderTerminalLaurentField z)
    (hxA : x ∈ (laurentSeriesValuationSubring
      FirstOrderTerminalCoefficientField).comap φ)
    (hB : B.comap g = (laurentSeriesValuationSubring
      FirstOrderTerminalCoefficientField).comap φ) :
    let A := (laurentSeriesValuationSubring
      FirstOrderTerminalCoefficientField).comap φ
    let hxB : g x ∈ B := by
      change x ∈ B.comap g
      rw [hB]
      exact hxA
    ABHN.laurentSeriesResidueFieldEquiv FirstOrderTerminalCoefficientField
        (valuationSubringResidueMapOfComapEq φ A
          (laurentSeriesValuationSubring FirstOrderTerminalCoefficientField) rfl
          (IsLocalRing.residue A (⟨x, hxA⟩ : A))) =
      PowerSeries.constantCoeff z ∧
    valuationSubringResidueMapOfComapEq g A B hB
        (IsLocalRing.residue A (⟨x, hxA⟩ : A)) =
      IsLocalRing.residue B (⟨g x, hxB⟩ : B) := by
  dsimp only
  constructor
  · exact firstOrderTerminalResidue_coefficient φ x z hx hxA
  · exact valuationSubringResidueMapOfComapEq_residue g _ B hB x hxA

end

end GaloisForLFunctions.HTGeometry
