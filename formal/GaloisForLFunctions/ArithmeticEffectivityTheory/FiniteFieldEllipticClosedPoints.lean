import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticIdealNorm
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Actual affine points and closed places of the elliptic curve

The coordinate algebra represents the affine point equation. Over a finite
extension every point map has a nonzero prime kernel, and its residue-field
embeddings describe the fibre over that closed place.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open Polynomial IsDedekindDomain
noncomputable section

variable (E : Type*) [Field E] [Algebra Constants E]

/-- The literal affine equation of the fixed elliptic curve. -/
abbrev AffinePoints := {xy : E × E // xy.2 ^ 2 = aeval xy.1 cubic}

/-- Evaluation at an actual affine point. -/
def affinePointHom (p : AffinePoints E) : A →ₐ[Constants] E :=
  AdjoinRoot.liftAlgHom curve.toAffine.polynomial (aeval p.1.1) p.1.2 (by
    rw [curve_polynomial]
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    exact sub_eq_zero.mpr p.2)

@[simp] theorem affinePointHom_xA (p : AffinePoints E) :
    affinePointHom E p xA = p.1.1 := by
  unfold affinePointHom xA
  change (AdjoinRoot.liftAlgHom _ _ _ _) ((AdjoinRoot.of _) X) = _
  rw [AdjoinRoot.liftAlgHom_of, aeval_X]

@[simp] theorem affinePointHom_yA (p : AffinePoints E) :
    affinePointHom E p yA = p.1.2 := by
  unfold affinePointHom yA
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The two coordinate values determine an algebra map out of the curve. -/
theorem coordinateRingAlgHom_ext {f g : A →ₐ[Constants] E}
    (hx : f xA = g xA) (hy : f yA = g yA) : f = g := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    exact hx
  · exact hy

/-- Every coordinate-algebra map evaluates at its own two coordinates. -/
def affinePointsAlgHomEquiv : AffinePoints E ≃ (A →ₐ[Constants] E) where
  toFun := affinePointHom E
  invFun f := ⟨(f xA, f yA), by
    have h := congrArg f relationA
    simpa only [map_pow, map_sub, cubic, aeval_X] using h⟩
  left_inv p := Subtype.ext (Prod.ext (affinePointHom_xA E p) (affinePointHom_yA E p))
  right_inv f := coordinateRingAlgHom_ext E
    (affinePointHom_xA E _) (affinePointHom_yA E _)

/-- The projective point set adds exactly the unique point at infinity. -/
def pointsAlgHomEquiv : Points E ≃ Option (A →ₐ[Constants] E) :=
  (pointsEquiv E).trans (Equiv.optionCongr (affinePointsAlgHomEquiv E))

instance coordinateRingAlgHom_finite [Finite E] : Finite (A →ₐ[Constants] E) :=
  Finite.of_injective (affinePointsAlgHomEquiv E).symm
    (affinePointsAlgHomEquiv E).symm.injective

theorem card_points_eq_card_algHom [Finite E] :
    Nat.card (Points E) = Nat.card (A →ₐ[Constants] E) + 1 := by
  letI := Fintype.ofFinite E
  letI := Fintype.ofFinite (A →ₐ[Constants] E)
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (pointsAlgHomEquiv E),
    Fintype.card_option, Nat.card_eq_fintype_card]

/-- A point over a finite extension determines an actual nonzero affine prime. -/
def affinePointPlace [Finite E] (f : A →ₐ[Constants] E) : HeightOneSpectrum A where
  asIdeal := RingHom.ker f
  isPrime := RingHom.ker_isPrime f
  ne_bot := by
    intro h
    letI : Finite A := Finite.of_injective f ((RingHom.injective_iff_ker_eq_bot f).mpr h)
    exact Infinite.false (inferInstance : Infinite A)

/-- Residue degree of an actual closed affine place. -/
def affinePlaceDegree (v : HeightOneSpectrum A) : ℕ :=
  Module.finrank Constants (A ⧸ v.asIdeal)

instance affinePlaceResidue_field (v : HeightOneSpectrum A) : Field (A ⧸ v.asIdeal) :=
  Ideal.Quotient.field v.asIdeal

instance affinePlaceResidue_finite (v : HeightOneSpectrum A) : Finite (A ⧸ v.asIdeal) :=
  affine_quotient_finite v.asIdeal v.ne_bot

instance affinePlaceResidue_finiteDimensional (v : HeightOneSpectrum A) :
    Module.Finite Constants (A ⧸ v.asIdeal) :=
  affine_quotient_finiteDimensional v.asIdeal v.ne_bot

theorem affinePlaceDegree_pos (v : HeightOneSpectrum A) : 0 < affinePlaceDegree v :=
  Module.finrank_pos

theorem affineIdealNorm_eq_pow_degree (v : HeightOneSpectrum A) :
    affineIdealNorm v.asIdeal = 3 ^ affinePlaceDegree v :=
  (FiniteField.pow_finrank_eq_natCard 3 (A ⧸ v.asIdeal)).symm

private theorem affinePointPlace_comp_mk [Finite E] (v : HeightOneSpectrum A)
    (g : (A ⧸ v.asIdeal) →ₐ[Constants] E) :
    affinePointPlace E (g.comp (Ideal.Quotient.mkₐ Constants v.asIdeal)) = v := by
  apply HeightOneSpectrum.ext
  ext a
  change g (Ideal.Quotient.mk v.asIdeal a) = 0 ↔ a ∈ v.asIdeal
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply g.toRingHom.injective
    exact h.trans (map_zero g).symm
  · intro h
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

/-- Points over a fixed closed place are exactly its residue-field embeddings. -/
def affinePointFiberEquiv [Finite E] (v : HeightOneSpectrum A) :
    {f : A →ₐ[Constants] E // affinePointPlace E f = v} ≃
      ((A ⧸ v.asIdeal) →ₐ[Constants] E) where
  toFun f := Ideal.Quotient.liftₐ v.asIdeal f.1 (by
    intro a ha
    have hk : RingHom.ker f.1 = v.asIdeal :=
      congrArg HeightOneSpectrum.asIdeal f.2
    exact RingHom.mem_ker.mp (hk.symm ▸ ha))
  invFun g := ⟨g.comp (Ideal.Quotient.mkₐ Constants v.asIdeal),
    affinePointPlace_comp_mk E v g⟩
  left_inv f := by
    apply Subtype.ext
    exact AlgHom.ext fun a => rfl
  right_inv g := by
    apply Ideal.Quotient.algHom_ext Constants
    exact AlgHom.ext fun a => rfl

/-- The finite set of actual places supporting points over the extension. -/
def affinePlacesOver [Finite E] : Finset (HeightOneSpectrum A) := by
  classical
  letI := Fintype.ofFinite (A →ₐ[Constants] E)
  exact Finset.univ.image (affinePointPlace E)

theorem mem_affinePlacesOver_iff [Finite E] (v : HeightOneSpectrum A) :
    v ∈ affinePlacesOver E ↔ affinePlaceDegree v ∣ Module.finrank Constants E := by
  classical
  unfold affinePlacesOver
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  change (∃ f, affinePointPlace E f = v) ↔
    Module.finrank Constants (A ⧸ v.asIdeal) ∣ Module.finrank Constants E
  rw [← FiniteField.nonempty_algHom_iff_finrank_dvd
    (F := Constants) (K := A ⧸ v.asIdeal) (L := E)]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨affinePointFiberEquiv E v ⟨f, hf⟩⟩
  · rintro ⟨g⟩
    exact ⟨((affinePointFiberEquiv E v).symm g).1,
      ((affinePointFiberEquiv E v).symm g).2⟩

/-- Only finitely many actual places have degree dividing a fixed extension degree. -/
theorem finite_affinePlaces_degree_dvd [Finite E] :
    {v : HeightOneSpectrum A | affinePlaceDegree v ∣ Module.finrank Constants E}.Finite := by
  apply (affinePlacesOver E).finite_toSet.subset
  intro v hv
  exact (mem_affinePlacesOver_iff E v).mpr hv

private def affinePointPlaceOver [Finite E] (f : A →ₐ[Constants] E) : affinePlacesOver E := by
  classical
  letI := Fintype.ofFinite (A →ₐ[Constants] E)
  refine ⟨affinePointPlace E f, ?_⟩
  unfold affinePlacesOver
  exact Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩

private def affinePointPlaceOverFiberEquiv [Finite E] (v : affinePlacesOver E) :
    {f : A →ₐ[Constants] E // affinePointPlaceOver E f = v} ≃
      ((A ⧸ v.1.asIdeal) →ₐ[Constants] E) :=
  (Equiv.subtypeEquivRight fun _ =>
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩).trans
      (affinePointFiberEquiv E v.1)

/-- Each degree-dividing closed point contributes its full residue degree. -/
theorem card_points_eq_closed_place_sum [Finite E] :
    Nat.card (Points E) =
      (∑ v : affinePlacesOver E, affinePlaceDegree v.1) + 1 := by
  classical
  letI := Fintype.ofFinite (A →ₐ[Constants] E)
  letI (v : affinePlacesOver E) :=
    Fintype.ofFinite {f : A →ₐ[Constants] E // affinePointPlaceOver E f = v}
  have hcount : Fintype.card (A →ₐ[Constants] E) =
      ∑ v : affinePlacesOver E,
        Fintype.card {f : A →ₐ[Constants] E // affinePointPlaceOver E f = v} := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv (affinePointPlaceOver E)).symm
  have hcard : Nat.card (A →ₐ[Constants] E) =
      ∑ v : affinePlacesOver E, affinePlaceDegree v.1 := by
    calc
      _ = ∑ v : affinePlacesOver E,
          Nat.card {f : A →ₐ[Constants] E // affinePointPlaceOver E f = v} := by
        simpa only [Fintype.card_eq_nat_card] using hcount
      _ = _ := by
        apply Finset.sum_congr rfl
        intro v _
        exact (Nat.card_congr (affinePointPlaceOverFiberEquiv E v)).trans
          (FiniteField.natCard_algHom_of_finrank_dvd
            (F := Constants) (K := A ⧸ v.1.asIdeal) (L := E)
            ((mem_affinePlacesOver_iff E v.1).mp v.2))
  rw [card_points_eq_card_algHom E]
  exact congrArg (fun n : ℕ => n + 1) hcard

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.pointsAlgHomEquiv
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.card_points_eq_card_algHom
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.affinePointFiberEquiv
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.mem_affinePlacesOver_iff
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.card_points_eq_closed_place_sum
