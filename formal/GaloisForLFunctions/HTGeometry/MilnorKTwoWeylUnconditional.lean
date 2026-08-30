import GaloisForLFunctions.HTGeometry.MilnorKTwoSpinWeylFieldAction


/-!
# Unconditional Milnor Weyl group

The zero and nonzero values of `{-1,-1}` exhaust all fields. Packaging both constructions
behind one carrier produces premise-free `MilnorW F`, together with a central injective
homomorphism from Milnor `K₂(F)`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry
namespace MilnorDiagonalExtension

universe u

variable {F : Type u} [Field F]

local instance milnorKTwoWeylUnconditionalLocalInst1 : DecidableEq (MilnorKDeg F 2) := Classical.decEq _

structure MilnorWPackage (F : Type u) [Field F] where
  W : Type u
  [groupW : Group W]
  centralIncl : Multiplicative (MilnorKDeg F 2) →* W
  centralIncl_injective : Function.Injective centralIncl
  centralIncl_mem_center : ∀ z, centralIncl z ∈ Subgroup.center W
  diagonalIncl : MilnorDiagonalExtension F 4 →* W
  weylGenerator : ∀ (i j : Fin 4), i ≠ j → W

noncomputable def milnorWZeroPackage
    (he : fin4MinusOneSymbol F = 0) : MilnorWPackage F where
  W := MilnorWZero he
  centralIncl := milnorWZeroCentralIncl he
  centralIncl_injective := milnorWZeroCentralIncl_injective he
  centralIncl_mem_center := milnorWZeroCentralIncl_mem_center he
  diagonalIncl := AmalgamatedSemidirect.inl
    (fin4MilnorH0 (F := F))
    (fin4MilnorH0ToFieldSignedWeyl (F := F))
    (fieldSignedWeylActionHom (F := F))
    (fieldSignedWeylCompatible he)
  weylGenerator := fun i j hij => AmalgamatedSemidirect.inr
    (fin4MilnorH0 (F := F))
    (fin4MilnorH0ToFieldSignedWeyl (F := F))
    (fieldSignedWeylActionHom (F := F))
    (fieldSignedWeylCompatible he)
    (MilnorSpinWeyl.fieldWeylGeneratorSigned (F := F) i j hij)

noncomputable def milnorWNonzeroPackage
    (he : fin4MinusOneSymbol F ≠ 0) : MilnorWPackage F where
  W := MilnorSpinWeyl.MilnorWNonzero he
  centralIncl := MilnorSpinWeyl.milnorWNonzeroCentralIncl he
  centralIncl_injective := MilnorSpinWeyl.milnorWNonzeroCentralIncl_injective he
  centralIncl_mem_center := MilnorSpinWeyl.milnorWNonzeroCentralIncl_mem_center he
  diagonalIncl := AmalgamatedSemidirect.inl
    (fin4MilnorH0 (F := F))
    (fin4MilnorH0ToSpinWeyl he)
    (MilnorSpinWeyl.spinWeylActionHom (F := F))
    (MilnorSpinWeyl.spinWeylCompatible he)
  weylGenerator := fun i j hij => AmalgamatedSemidirect.inr
    (fin4MilnorH0 (F := F))
    (fin4MilnorH0ToSpinWeyl he)
    (MilnorSpinWeyl.spinWeylActionHom (F := F))
    (MilnorSpinWeyl.spinWeylCompatible he)
    (MilnorSpinWeyl.weylLiftSpinWeyl i j hij)

/-- Milnor's group package, selected from two exhaustive symbol branches. -/
noncomputable def milnorWPackage (F : Type u) [Field F] : MilnorWPackage F :=
  if he : fin4MinusOneSymbol F = 0 then milnorWZeroPackage he
  else milnorWNonzeroPackage he

/-- Milnor's unconditional group `W`. -/
noncomputable abbrev MilnorW (F : Type u) [Field F] : Type u :=
  (milnorWPackage F).W

noncomputable instance : Group (MilnorW F) :=
  (milnorWPackage F).groupW

noncomputable def milnorWCentralIncl :
    Multiplicative (MilnorKDeg F 2) →* MilnorW F :=
  (milnorWPackage F).centralIncl

/-- Canonical copy of Milnor's diagonal extension inside the unconditional Weyl extension. -/
noncomputable def milnorWDiagonalIncl :
    MilnorDiagonalExtension F 4 →* MilnorW F :=
  (milnorWPackage F).diagonalIncl

/-- Canonical normalized Weyl generator in Milnor's unconditional extension. -/
noncomputable def milnorWWeylGenerator
    (i j : Fin 4) (hij : i ≠ j) : MilnorW F :=
  (milnorWPackage F).weylGenerator i j hij

theorem milnorWCentralIncl_injective :
    Function.Injective (milnorWCentralIncl (F := F)) :=
  (milnorWPackage F).centralIncl_injective

theorem milnorWCentralIncl_mem_center
    (z : Multiplicative (MilnorKDeg F 2)) :
    milnorWCentralIncl (F := F) z ∈ Subgroup.center (MilnorW F) :=
  (milnorWPackage F).centralIncl_mem_center z

end MilnorDiagonalExtension
end GaloisForLFunctions.HTGeometry

end
