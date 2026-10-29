import GaloisForLFunctions.HTGeometry.LoopEisenstein.SL2RootSplittings
import GaloisForLFunctions.HTGeometry.MilnorKTameValuation
import GaloisForLFunctions.HTGeometry.ABHN.LaurentSeriesFiniteLocalField

/-!
# The central extension of formal Laurent SL₂

The Laurent-series valuation and its proved residue-field equivalence give an
actual tame homomorphism `K₂(F((X))) → Fˣ`. Pushing the proved Kubota cocycle
through this homomorphism constructs a group with central kernel exactly `Fˣ`.
No symbol law or extension exactness is supplied as an assumption.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable (F : Type*) [Field F]

/-- The tame homomorphism for the actual Laurent-series valuation, with values
in the coefficient field through its canonical residue identification. -/
def laurentTameHom : MilnorKDeg (LaurentSeries F) 2 →+ Additive Fˣ :=
  (MonoidHom.toAdditive
    (Units.map (ABHN.laurentSeriesResidueFieldEquiv F).toMonoidHom)).comp
      (tameHomOfValuation
        (Valued.v : Valuation (LaurentSeries F) (WithZero (Multiplicative ℤ))))

/-- The concrete tame symbol on two invertible Laurent series. -/
def laurentTameSymbol (a b : (LaurentSeries F)ˣ) : Fˣ :=
  Units.map (ABHN.laurentSeriesResidueFieldEquiv F).toMonoidHom
    ((tameDataOfValuation
      (Valued.v : Valuation (LaurentSeries F) (WithZero (Multiplicative ℤ)))).tame a b)

@[simp] theorem laurentTameHom_symbol (a b : (LaurentSeries F)ˣ) :
    laurentTameHom F (milnorSym2 (LaurentSeries F) a b) =
      Additive.ofMul (laurentTameSymbol F a b) := by
  change (MonoidHom.toAdditive
      (Units.map (ABHN.laurentSeriesResidueFieldEquiv F).toMonoidHom))
    (tameHomOfValuation
      (Valued.v : Valuation (LaurentSeries F) (WithZero (Multiplicative ℤ)))
        (milnorClassDeg (LaurentSeries F) 2 ⟨[a, b], rfl⟩)) = _
  rw [tameHomOfValuation_symbol]
  rfl

/-- The central extension of the full formal Laurent-series special linear group. -/
abbrev LoopSL2 := SL2SymbolExtension (laurentTameHom F)

namespace LoopSL2

/-- Projection onto the ordinary Laurent-series matrices. -/
def projection : LoopSL2 F →* SL2 (LaurentSeries F) :=
  SL2SymbolExtension.projection (laurentTameHom F)

theorem projection_surjective : Function.Surjective (projection F) :=
  SL2SymbolExtension.projection_surjective (laurentTameHom F)

/-- The coefficient units form the actual, injective central subgroup. -/
def centralEmbedding : Fˣ →* LoopSL2 F where
  toFun u := ⟨1, Additive.ofMul u⟩
  map_one' := rfl
  map_mul' u v := by
    change SL2SymbolExtension.centralEmbedding (laurentTameHom F)
        (Multiplicative.ofAdd (Additive.ofMul u) * Multiplicative.ofAdd (Additive.ofMul v)) =
      SL2SymbolExtension.centralEmbedding (laurentTameHom F)
        (Multiplicative.ofAdd (Additive.ofMul u)) *
      SL2SymbolExtension.centralEmbedding (laurentTameHom F)
        (Multiplicative.ofAdd (Additive.ofMul v))
    exact map_mul _ _ _

theorem centralEmbedding_injective : Function.Injective (centralEmbedding F) := by
  intro u v h
  exact Additive.ofMul.injective (congrArg SL2SymbolExtension.centralCoord h)

@[simp] theorem projection_centralEmbedding (u : Fˣ) :
    projection F (centralEmbedding F u) = 1 := rfl

theorem centralEmbedding_mem_center (u : Fˣ) :
    centralEmbedding F u ∈ Subgroup.center (LoopSL2 F) := by
  rw [Subgroup.mem_center_iff]
  intro g
  exact (SL2SymbolExtension.centralEmbedding_commute
    (Multiplicative.ofAdd (Additive.ofMul u)) g).symm

/-- The central kernel is exactly the coefficient field's unit group. -/
theorem projection_ker_eq_range : (projection F).ker = (centralEmbedding F).range := by
  ext g
  constructor
  · intro hg
    refine ⟨g.centralCoord.toMul, ?_⟩
    apply SL2SymbolExtension.ext
    · exact hg.symm
    · rfl
  · rintro ⟨u, rfl⟩
    rfl

/-- Read the central coordinate multiplicatively. -/
def centralCoordinate (g : LoopSL2 F) : Fˣ := g.centralCoord.toMul

/-- The multiplication law has the literal tame symbol as its central factor. -/
theorem centralCoordinate_mul (g h : LoopSL2 F) :
    centralCoordinate F (g * h) = centralCoordinate F g * centralCoordinate F h *
      laurentTameSymbol F
        (kubotaUnit (g.base * h.base) / kubotaUnit g.base)
        (kubotaUnit (g.base * h.base) / kubotaUnit h.base) := by
  change (g.centralCoord + h.centralCoord +
    laurentTameHom F (kubotaCocycle g.base h.base)).toMul = _
  rw [kubotaCocycle, laurentTameHom_symbol]
  rfl

/-- The full upper Laurent root group, with its canonical splitting. -/
def upperRoot : Multiplicative (LaurentSeries F) →* LoopSL2 F :=
  SL2SymbolExtension.upperRoot (laurentTameHom F)

/-- The full lower Laurent root group, with its canonical splitting. -/
def lowerRoot : Multiplicative (LaurentSeries F) →* LoopSL2 F :=
  SL2SymbolExtension.lowerRoot (laurentTameHom F)

/-- The coroot section of the Laurent torus. -/
def diagonalSection (a : (LaurentSeries F)ˣ) : LoopSL2 F :=
  SL2SymbolExtension.sectionOf (laurentTameHom F) (sl2Diagonal a)

/-- The Laurent torus section has precisely the inverse tame-symbol defect. -/
theorem diagonalSection_mul (a b : (LaurentSeries F)ˣ) :
    diagonalSection F a * diagonalSection F b =
      centralEmbedding F (laurentTameSymbol F a b)⁻¹ * diagonalSection F (a * b) := by
  have h := SL2SymbolExtension.diagonal_section_mul (laurentTameHom F) a b
  rw [laurentTameHom_symbol] at h
  exact h

end LoopSL2

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
