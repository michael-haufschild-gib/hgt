import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.PolynomialFiniteQuotients
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.FiniteTypeAlgebraPoints
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic

/-!
# Closed points of finite polynomial orders

For a Dedekind domain finite free over `K[X]`, a point over a finite field
extension has a nonzero prime kernel. Its fibre consists of residue-field
embeddings. Consequently, a closed point contributes its residue degree
exactly when that degree divides the extension degree.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolynomialOrderClosedPoints
open Polynomial IsDedekindDomain
variable (K B : Type*) [Field K] [CommRing B]
    [IsDedekindDomain B] [Infinite B] [Algebra K B] [Algebra K[X] B]
    [IsScalarTower K K[X] B] [Module.Finite K[X] B]

local instance polynomialOrderFiniteType : Algebra.FiniteType K B :=
  Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType K K[X])
    (inferInstance : Algebra.FiniteType K[X] B)

variable (E : Type*) [Field E] [Algebra K E] [Finite E]

/-- The closed prime defined by an algebra point over finite constants. -/
def pointPlace (f : B →ₐ[K] E) : HeightOneSpectrum B where
  asIdeal := RingHom.ker f
  isPrime := RingHom.ker_isPrime f
  ne_bot := by
    intro h
    letI : Finite B := Finite.of_injective f ((RingHom.injective_iff_ker_eq_bot f).mpr h)
    exact Infinite.false (inferInstance : Infinite B)

/-- Degree of a closed prime over the constant field. -/
def placeDegree (v : HeightOneSpectrum B) : ℕ := Module.finrank K (B ⧸ v.asIdeal)

instance residueField (v : HeightOneSpectrum B) : Field (B ⧸ v.asIdeal) :=
  Ideal.Quotient.field v.asIdeal

include K in
omit [Infinite B] in
/-- The residue field of each nonzero prime is finite. -/
theorem residueFinite [Finite K] [Module.Free K[X] B]
    (v : HeightOneSpectrum B) : Finite (B ⧸ v.asIdeal) :=
  polynomialOrder_quotient_finite K B v.asIdeal v.ne_bot

instance residueFiniteDimensional [Module.Free K[X] B] (v : HeightOneSpectrum B) :
    Module.Finite K (B ⧸ v.asIdeal) :=
  polynomialOrder_quotient_finiteDimensional K B v.asIdeal v.ne_bot

omit [Infinite B] in
theorem placeDegree_pos [Module.Free K[X] B] (v : HeightOneSpectrum B) : 0 < placeDegree K B v :=
  Module.finrank_pos

omit [Algebra K[X] B] [IsScalarTower K K[X] B] [Module.Finite K[X] B] in
private theorem pointPlace_comp_mk (v : HeightOneSpectrum B)
    (g : (B ⧸ v.asIdeal) →ₐ[K] E) :
    pointPlace K B E (g.comp (Ideal.Quotient.mkₐ K v.asIdeal)) = v := by
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

/-- The point fibre is the set of embeddings of the actual residue field. -/
def pointFiberEquiv (v : HeightOneSpectrum B) :
    {f : B →ₐ[K] E // pointPlace K B E f = v} ≃ ((B ⧸ v.asIdeal) →ₐ[K] E) where
  toFun f := Ideal.Quotient.liftₐ v.asIdeal f.1 (by
    intro a ha
    have hk : RingHom.ker f.1 = v.asIdeal := congrArg HeightOneSpectrum.asIdeal f.2
    exact RingHom.mem_ker.mp (hk.symm ▸ ha))
  invFun g := ⟨g.comp (Ideal.Quotient.mkₐ K v.asIdeal), pointPlace_comp_mk K B E v g⟩
  left_inv f := by
    apply Subtype.ext
    exact AlgHom.ext fun a => rfl
  right_inv g := by
    apply Ideal.Quotient.algHom_ext K
    exact AlgHom.ext fun a => rfl

/-- The finite set of closed primes supporting points over the extension. -/
def placesOver : Finset (HeightOneSpectrum B) := by
  classical
  letI := Fintype.ofFinite (B →ₐ[K] E)
  exact Finset.univ.image (pointPlace K B E)

theorem mem_placesOver_iff (v : HeightOneSpectrum B) :
    v ∈ placesOver K B E ↔ placeDegree K B v ∣ Module.finrank K E := by
  classical
  unfold placesOver
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  change (∃ f, pointPlace K B E f = v) ↔
    Module.finrank K (B ⧸ v.asIdeal) ∣ Module.finrank K E
  rw [← FiniteField.nonempty_algHom_iff_finrank_dvd
    (F := K) (K := B ⧸ v.asIdeal) (L := E)]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨pointFiberEquiv K B E v ⟨f, hf⟩⟩
  · rintro ⟨g⟩
    exact ⟨((pointFiberEquiv K B E v).symm g).1,
      ((pointFiberEquiv K B E v).symm g).2⟩

/-- There are finitely many closed primes whose degrees divide this extension degree. -/
theorem finite_places_degree_dvd :
    {v : HeightOneSpectrum B | placeDegree K B v ∣ Module.finrank K E}.Finite := by
  apply (placesOver K B E).finite_toSet.subset
  intro v hv
  exact (mem_placesOver_iff K B E v).mpr hv

private def pointPlaceOver (f : B →ₐ[K] E) : placesOver K B E := by
  classical
  letI := Fintype.ofFinite (B →ₐ[K] E)
  refine ⟨pointPlace K B E f, ?_⟩
  unfold placesOver
  exact Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩

private def pointPlaceOverFiberEquiv (v : placesOver K B E) :
    {f : B →ₐ[K] E // pointPlaceOver K B E f = v} ≃ ((B ⧸ v.1.asIdeal) →ₐ[K] E) :=
  (Equiv.subtypeEquivRight fun _ =>
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩).trans
      (pointFiberEquiv K B E v.1)

/-- The actual point count is the sum of residue degrees over the degree-dividing primes. -/
theorem card_algHom_eq_closed_place_sum :
    Nat.card (B →ₐ[K] E) = ∑ v : placesOver K B E, placeDegree K B v.1 := by
  classical
  letI := Fintype.ofFinite (B →ₐ[K] E)
  letI (v : placesOver K B E) :=
    Fintype.ofFinite {f : B →ₐ[K] E // pointPlaceOver K B E f = v}
  have hcount : Fintype.card (B →ₐ[K] E) =
      ∑ v : placesOver K B E,
        Fintype.card {f : B →ₐ[K] E // pointPlaceOver K B E f = v} := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv (pointPlaceOver K B E)).symm
  calc
    _ = ∑ v : placesOver K B E,
        Nat.card {f : B →ₐ[K] E // pointPlaceOver K B E f = v} := by
      simpa only [Fintype.card_eq_nat_card] using hcount
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      exact (Nat.card_congr (pointPlaceOverFiberEquiv K B E v)).trans
        (FiniteField.natCard_algHom_of_finrank_dvd
          (F := K) (K := B ⧸ v.1.asIdeal) (L := E)
          ((mem_placesOver_iff K B E v.1).mp v.2))

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolynomialOrderClosedPoints
