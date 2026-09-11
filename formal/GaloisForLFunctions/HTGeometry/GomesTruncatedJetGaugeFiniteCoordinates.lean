import GaloisForLFunctions.HTGeometry.GomesTruncatedJetGaugeLogCoordinates
import Mathlib.Data.Fintype.EquivFin

/-!
# Standard finite-dimensional coordinates for every actual clock gauge group

Positive resonant weights give exactly `n / orderOf z` additive coordinates.
Reindexing the established logarithmic chart yields a group equivalence with
nonzero complex scalars times an ordinary finite complex coordinate space.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- Positive resonant weights admit exactly the established number of finite coordinates. -/
def gomesTruncatedJetPositiveIndexEquivFin (n : ℕ) (z : ℂ) :
    GomesTruncatedJetPositiveResonantIndex n z ≃ Fin (n / orderOf z) := by
  classical
  exact Fintype.equivFinOfCardEq (gomesTruncatedJetPositiveResonantIndex_card n z)

/-- Reindex the intrinsic resonant coordinates by an ordinary finite index type. -/
def gomesTruncatedJetPositiveCoordinateReindex (n : ℕ) (z : ℂ) :
    (GomesTruncatedJetPositiveResonantIndex n z → ℂ) ≃ₗ[ℂ] (Fin (n / orderOf z) → ℂ) where
  toFun f i := f ((gomesTruncatedJetPositiveIndexEquivFin n z).symm i)
  invFun g k := g (gomesTruncatedJetPositiveIndexEquivFin n z k)
  left_inv f := by funext k; exact congrArg f ((gomesTruncatedJetPositiveIndexEquivFin n z).symm_apply_apply k)
  right_inv g := by funext i; exact congrArg g ((gomesTruncatedJetPositiveIndexEquivFin n z).apply_symm_apply i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual gauge group is complex units times an additive complex space of dimension `n / orderOf z`. -/
def gomesTruncatedJetGaugeFiniteCoordinates (n : ℕ) (z : ℂ) :
    gomesTruncatedJetGaugeGroup n z ≃* ℂˣ × Multiplicative (Fin (n / orderOf z) → ℂ) :=
  (gomesTruncatedJetGaugeLogCoordinates n z).trans
    (MulEquiv.prodCongr (MulEquiv.refl ℂˣ)
      (AddEquiv.toMultiplicative (gomesTruncatedJetPositiveCoordinateReindex n z).toAddEquiv))

/-- The standard finite chart retains the actual scalar character. -/
theorem gomesTruncatedJetGaugeFiniteCoordinates_fst (n : ℕ) (z : ℂ)
    (u : gomesTruncatedJetGaugeGroup n z) :
    (gomesTruncatedJetGaugeFiniteCoordinates n z u).1 = gomesTruncatedJetGaugeCharacter n z u := rfl

/-- Standard finite coordinates are actual resonant entries of the normalized matrix logarithm. -/
theorem gomesTruncatedJetGaugeFiniteCoordinates_snd (n : ℕ) (z : ℂ)
    (u : gomesTruncatedJetGaugeGroup n z) (i : Fin (n / orderOf z)) :
    Multiplicative.toAdd (gomesTruncatedJetGaugeFiniteCoordinates n z u).2 i =
      (gomesTruncatedJetUnipotentLogarithm n z (gomesTruncatedJetUnipotentPart n z u)).val.val
        0 ((gomesTruncatedJetPositiveIndexEquivFin n z).symm i).val.val := rfl

/-- Arbitrary standard finite coordinates reconstruct the unique actual gauge matrix. -/
theorem gomesTruncatedJetGaugeFiniteCoordinates_symm (n : ℕ) (z : ℂ) (c : ℂˣ)
    (a : Fin (n / orderOf z) → ℂ) :
    (gomesTruncatedJetGaugeFiniteCoordinates n z).symm (c, Multiplicative.ofAdd a) =
      gomesTruncatedJetScalarSection n z c *
        (gomesTruncatedJetUnipotentExponential n z
          ((gomesTruncatedJetNilpotentLinearEquiv n z).symm
            ((gomesTruncatedJetPositiveCoordinateReindex n z).symm a))).val := by
  change (gomesTruncatedJetGaugeLogCoordinates n z).symm
    (c, Multiplicative.ofAdd ((gomesTruncatedJetPositiveCoordinateReindex n z).symm a)) = _
  exact gomesTruncatedJetGaugeLogCoordinates_symm n z c _

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
