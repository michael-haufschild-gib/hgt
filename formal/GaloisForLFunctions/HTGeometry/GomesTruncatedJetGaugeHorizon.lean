import GaloisForLFunctions.HTGeometry.GomesTruncatedJetNilpotentHorizon
import GaloisForLFunctions.HTGeometry.GomesTruncatedJetGaugeSplitting

/-!
# Geometric horizon restriction on the actual gauge groups

Restriction of the joint algebra induces a map of its actual matrix units.
It retains their scalar character, so it restricts further to the complete
unipotent gauge subgroups.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- Restrict any actual two-clock gauge transformation through the geometric horizon map. -/
def gomesTruncatedJetGaugeHorizon (n r : ℕ) (z : ℂ) :
    gomesTruncatedJetGaugeGroup (n + r) z →* gomesTruncatedJetGaugeGroup n z :=
  (gomesTruncatedJetInternalUnitsEquiv n z).toMonoidHom.comp
    ((Units.map (gomesTruncatedJetHorizonRestriction n r z).toMonoidHom).comp
      (gomesTruncatedJetInternalUnitsEquiv (n + r) z).symm.toMonoidHom)

/-- The actual gauge restriction is the literal upper-left block of its matrix. -/
theorem gomesTruncatedJetGaugeHorizon_apply (n r : ℕ) (z : ℂ)
    (u : gomesTruncatedJetGaugeGroup (n + r) z) (i j : Fin (n + 1)) :
    (gomesTruncatedJetGaugeHorizon n r z u).val.val i j =
      u.val.val (Fin.castLE (Nat.add_le_add_right (Nat.le_add_right n r) 1) i)
        (Fin.castLE (Nat.add_le_add_right (Nat.le_add_right n r) 1) j) :=
  gomesTruncatedJetHorizonRestriction_apply n r z
    ((gomesTruncatedJetInternalUnitsEquiv (n + r) z).symm u).val i j

/-- Every actual scalar gauge character survives restriction unchanged. -/
theorem gomesTruncatedJetGaugeHorizon_character (n r : ℕ) (z : ℂ)
    (u : gomesTruncatedJetGaugeGroup (n + r) z) :
    gomesTruncatedJetGaugeCharacter n z (gomesTruncatedJetGaugeHorizon n r z u) =
      gomesTruncatedJetGaugeCharacter (n + r) z u := by
  apply Units.ext
  exact gomesTruncatedJetGaugeHorizon_apply n r z u 0 0

/-- Restrict the complete unipotent gauge group to any lower horizon. -/
def gomesTruncatedJetUnipotentHorizon (n r : ℕ) (z : ℂ) :
    gomesTruncatedJetUnipotentGroup (n + r) z →* gomesTruncatedJetUnipotentGroup n z where
  toFun u := ⟨gomesTruncatedJetGaugeHorizon n r z u.val, by
    change gomesTruncatedJetGaugeCharacter n z _ = 1
    rw [gomesTruncatedJetGaugeHorizon_character]
    exact u.property⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (gomesTruncatedJetGaugeHorizon n r z)
  map_mul' u v := by
    apply Subtype.ext
    exact map_mul (gomesTruncatedJetGaugeHorizon n r z) u.val v.val

/-- The unipotent restriction uses exactly the actual gauge horizon map. -/
theorem gomesTruncatedJetUnipotentHorizon_val (n r : ℕ) (z : ℂ)
    (u : gomesTruncatedJetUnipotentGroup (n + r) z) :
    (gomesTruncatedJetUnipotentHorizon n r z u).val = gomesTruncatedJetGaugeHorizon n r z u.val := rfl

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
