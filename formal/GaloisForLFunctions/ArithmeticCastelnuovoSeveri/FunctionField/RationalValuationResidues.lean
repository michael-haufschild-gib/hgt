import GaloisForLFunctions.HTGeometry.DedekindResidueFieldAtPlace

/-!
# Constant residues under changes of valuation chart

The residue map on constants agrees with the constant map into a finite
prime quotient. Pullback along a constant-field isomorphism preserves
surjectivity of this map, hence rationality of the place.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open IsDedekindDomain
open GaloisForLFunctions.HTGeometry

/-- Constants in a valuation ring, represented as valuation integers. -/
def valuationConstantHom {K L : Type*} [Field K] [Field L] [Algebra K L]
    (W : ValuationSubring L) (hK : ∀ a : K, algebraMap K L a ∈ W) : K →+* W :=
  (algebraMap K L).codRestrict W.toSubring hK

/-- The residue map on the constant field of a valuation. -/
def valuationConstantResidue {K L : Type*} [Field K] [Field L] [Algebra K L]
    (W : ValuationSubring L) (hK : ∀ a : K, algebraMap K L a ∈ W) :
    K →+* IsLocalRing.ResidueField W :=
  (IsLocalRing.residue W).comp (valuationConstantHom W hK)

/-- Constants are integers at every finite place of a Dedekind algebra. -/
theorem heightOne_constants_mem {K B L : Type*} [Field K] [CommRing B] [IsDedekindDomain B]
    [Field L] [Algebra K B] [Algebra B L] [Algebra K L] [IsScalarTower K B L]
    [IsFractionRing B L] (w : HeightOneSpectrum B) (a : K) :
    algebraMap K L a ∈ (w.valuation L).valuationSubring := by
  rw [IsScalarTower.algebraMap_apply K B L]
  exact algebraMap_mem_valuationSubringAtPlace L w _

/-- Constant rationality of a finite valuation is exactly surjectivity onto the prime quotient. -/
theorem heightOne_constant_residue_surjective_iff
    {K B L : Type*} [Field K] [CommRing B] [IsDedekindDomain B]
    [Field L] [Algebra K B] [Algebra B L] [Algebra K L] [IsScalarTower K B L]
    [IsFractionRing B L] (w : HeightOneSpectrum B) :
    Function.Surjective (valuationConstantResidue (w.valuation L).valuationSubring
      (heightOne_constants_mem (K := K) w)) ↔
      Function.Surjective (algebraMap K (B ⧸ w.asIdeal)) := by
  let e := residueFieldAtPlaceEquiv L w
  have hcompat (a : K) : e (valuationConstantResidue (w.valuation L).valuationSubring
      (heightOne_constants_mem (K := K) w) a) = algebraMap K (B ⧸ w.asIdeal) a := by
    have hi : valuationConstantHom (w.valuation L).valuationSubring
        (heightOne_constants_mem (K := K) w) a = placeIntegerElt L w (algebraMap K B a) :=
      Subtype.ext (IsScalarTower.algebraMap_apply K B L a)
    change e (IsLocalRing.residue _ (valuationConstantHom _ _ a)) = _
    rw [hi]
    exact residueFieldAtPlaceEquiv_residue L w (algebraMap K B a)
  constructor
  · intro h y
    obtain ⟨a, ha⟩ := h (e.symm y)
    exact ⟨a, (hcompat a).symm.trans ((congrArg e ha).trans (e.apply_symm_apply y))⟩
  · intro h y
    obtain ⟨a, ha⟩ := h (e y)
    exact ⟨a, e.injective ((hcompat a).trans ha)⟩

/-- Pulling a valuation ring back along a field isomorphism preserves the ring itself up to isomorphism. -/
def valuationComapRingEquiv {L L' : Type*} [Field L] [Field L']
    (e : L ≃+* L') (W : ValuationSubring L') : W.comap e.toRingHom ≃+* W where
  toFun x := ⟨e x, x.property⟩
  invFun y := ⟨e.symm y, by change e (e.symm y) ∈ W; rw [e.apply_symm_apply]; exact y.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul e (x : L) (y : L))
  map_add' x y := Subtype.ext (map_add e (x : L) (y : L))

/-- A constant-field isomorphism preserves rationality of valuation residues. -/
theorem valuationConstantResidue_comap_surjective_iff
    {K L L' : Type*} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
    (e : L ≃ₐ[K] L') (W : ValuationSubring L')
    (hK : ∀ a : K, algebraMap K L' a ∈ W) :
    Function.Surjective (valuationConstantResidue (W.comap e.toRingHom)
      (fun a => show e (algebraMap K L a) ∈ W by rw [e.commutes]; exact hK a)) ↔
      Function.Surjective (valuationConstantResidue W hK) := by
  let eW := valuationComapRingEquiv e.toRingEquiv W
  let eκ := IsLocalRing.ResidueField.mapEquiv eW
  have hcompat (a : K) : eκ (valuationConstantResidue (W.comap e.toRingHom)
      (fun a => show e (algebraMap K L a) ∈ W by rw [e.commutes]; exact hK a) a) =
        valuationConstantResidue W hK a := by
    change IsLocalRing.residue W (eW (valuationConstantHom _ _ a)) =
      IsLocalRing.residue W (valuationConstantHom W hK a)
    congr 1
    exact Subtype.ext (e.commutes a)
  constructor
  · intro h y
    obtain ⟨a, ha⟩ := h (eκ.symm y)
    exact ⟨a, (hcompat a).symm.trans ((congrArg eκ ha).trans (eκ.apply_symm_apply y))⟩
  · intro h y
    obtain ⟨a, ha⟩ := h (eκ y)
    exact ⟨a, eκ.injective ((hcompat a).trans ha)⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
