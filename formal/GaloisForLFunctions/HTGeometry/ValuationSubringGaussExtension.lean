import GaloisForLFunctions.HTGeometry.ValuationSubringExtension
import Mathlib

/-!
# Gauss extension of valuation subrings

An arbitrary valuation subring extends across one free transcendental adjunction with exact
contraction and with the new generator a valuation unit.  The construction localizes the
polynomial ring over the source valuation ring at the kernel of coefficientwise residue
reduction, then applies Krull domination.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

set_option maxHeartbeats 1000000

private noncomputable def gaussResiduePolynomialMap
    {E : Type u} [Field E] (A : ValuationSubring E) :
    Polynomial A →+* Polynomial (IsLocalRing.ResidueField A) :=
  Polynomial.mapRingHom (IsLocalRing.residue A)

private noncomputable def gaussResiduePrime
    {E : Type u} [Field E] (A : ValuationSubring E) : Ideal (Polynomial A) :=
  RingHom.ker (gaussResiduePolynomialMap A)

private noncomputable instance gaussResiduePrime_isPrime
    {E : Type u} [Field E] (A : ValuationSubring E) :
    (gaussResiduePrime A).IsPrime :=
  RingHom.ker_isPrime (gaussResiduePolynomialMap A)

private abbrev gaussLocalRing
    {E : Type u} [Field E] (A : ValuationSubring E) : Type u :=
  @Localization.AtPrime (Polynomial A) _ (gaussResiduePrime A)
    (gaussResiduePrime_isPrime A)

private noncomputable instance (priority := high) gaussLocalRingSemiring
    {E : Type u} [Field E] (A : ValuationSubring E) :
    Semiring (gaussLocalRing A) :=
  (inferInstance : CommRing (gaussLocalRing A)).toSemiring

private noncomputable def gaussCoefficientToLocal
    {E : Type u} [Field E] (A : ValuationSubring E) :
    A →+* gaussLocalRing A :=
  (algebraMap (Polynomial A) (gaussLocalRing A)).comp Polynomial.C

private noncomputable instance gaussCoefficientToLocal_isLocalHom
    {E : Type u} [Field E] (A : ValuationSubring E) :
    IsLocalHom (gaussCoefficientToLocal A) := by
  refine ⟨fun a ha => ?_⟩
  have hcompl :
      Polynomial.C a ∈ (gaussResiduePrime A).primeCompl :=
    (IsLocalization.AtPrime.isUnit_to_map_iff
      (gaussLocalRing A) (gaussResiduePrime A) (Polynomial.C a)).mp ha
  have hres : IsLocalRing.residue A a ≠ 0 := by
    intro hzero
    apply hcompl
    change gaussResiduePolynomialMap A (Polynomial.C a) = 0
    simp [gaussResiduePolynomialMap, hzero]
  by_contra hnotunit
  exact hres ((IsLocalRing.residue_eq_zero_iff a).2
    ((IsLocalRing.mem_maximalIdeal a).2 hnotunit))

private noncomputable def gaussPolynomialToRatFunc
    {E : Type u} [Field E] (A : ValuationSubring E) :
    Polynomial A →+* RatFunc E :=
  (algebraMap (Polynomial E) (RatFunc E)).comp
    (Polynomial.mapRingHom A.subtype)

private theorem gaussPolynomialToRatFunc_ne_zero
    {E : Type u} [Field E] (A : ValuationSubring E)
    (p : Polynomial A) (hp : p ≠ 0) :
    gaussPolynomialToRatFunc A p ≠ 0 := by
  intro hzero
  have hmap : Polynomial.map A.subtype p = 0 :=
    (RatFunc.algebraMap_injective E) (by
      simpa [gaussPolynomialToRatFunc] using hzero)
  have hsubtype : Function.Injective A.subtype := by
    intro x y hxy
    exact Subtype.ext hxy
  apply hp
  apply Polynomial.map_injective A.subtype hsubtype
  simpa using hmap

private noncomputable def gaussLocalToRatFunc
    {E : Type u} [Field E] (A : ValuationSubring E) :
    gaussLocalRing A →+* RatFunc E :=
  IsLocalization.lift (g := gaussPolynomialToRatFunc A)
    (fun y : (gaussResiduePrime A).primeCompl =>
    isUnit_iff_ne_zero.mpr
      (gaussPolynomialToRatFunc_ne_zero A y
        (by
          intro hy
          have hyP : (y : Polynomial A) ∈ gaussResiduePrime A := by
            rw [hy]
            exact (gaussResiduePrime A).zero_mem
          have hyNot : (y : Polynomial A) ∉ gaussResiduePrime A := y.2
          exact hyNot hyP)))

private theorem gaussLocalToRatFunc_coefficient
    {E : Type u} [Field E] (A : ValuationSubring E) (a : A) :
    gaussLocalToRatFunc A (gaussCoefficientToLocal A a) =
      algebraMap E (RatFunc E) (a : E) := by
  simp [gaussLocalToRatFunc, gaussCoefficientToLocal,
    gaussPolynomialToRatFunc]

private theorem gaussLocalToRatFunc_X
    {E : Type u} [Field E] (A : ValuationSubring E) :
    gaussLocalToRatFunc A
        (algebraMap (Polynomial A) (gaussLocalRing A) Polynomial.X) =
      RatFunc.X := by
  simp [gaussLocalToRatFunc, gaussPolynomialToRatFunc]

/-- Exact Gauss extension of an arbitrary valuation ring to one rational variable. -/
theorem exists_ratFunc_valuationSubring_gaussExtension
    {E : Type u} [Field E] (A : ValuationSubring E) :
    ∃ B : ValuationSubring (RatFunc E),
      B.comap (algebraMap E (RatFunc E)) = A ∧
      RatFunc.X ∈ B ∧ RatFunc.X⁻¹ ∈ B := by
  obtain ⟨B, hmem, hlocal⟩ :=
    IsLocalRing.exists_factor_valuationRing (gaussLocalToRatFunc A)
  have hcoeff : ∀ a : A, algebraMap E (RatFunc E) (a : E) ∈ B := by
    intro a
    rw [← gaussLocalToRatFunc_coefficient A a]
    exact hmem (gaussCoefficientToLocal A a)
  have hEA : ∀ x : E, algebraMap E (RatFunc E) x ∈ B ↔ x ∈ A := by
    intro x
    constructor
    · intro hx
      by_contra hnot
      have hxinvA : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hnot
      have hx0 : x ≠ 0 := by
        intro hx0
        subst x
        exact hnot A.zero_mem
      have hinvMem : algebraMap E (RatFunc E) x⁻¹ ∈ B :=
        hcoeff ⟨x⁻¹, hxinvA⟩
      have hunit : IsUnit
          (⟨algebraMap E (RatFunc E) x⁻¹, hinvMem⟩ : B.toSubring) := by
        refine isUnit_iff_exists_inv.mpr
          ⟨⟨algebraMap E (RatFunc E) x, hx⟩, ?_⟩
        apply Subtype.ext
        simp [hx0]
      have hcLocal : IsLocalHom
          (((gaussLocalToRatFunc A).codRestrict B.toSubring hmem).comp
            (gaussCoefficientToLocal A)) := inferInstance
      have hsourceUnit : IsUnit (⟨x⁻¹, hxinvA⟩ : A) := by
        apply hcLocal.map_nonunit (⟨x⁻¹, hxinvA⟩ : A)
        convert hunit using 1
        apply Subtype.ext
        exact gaussLocalToRatFunc_coefficient A ⟨x⁻¹, hxinvA⟩
      obtain ⟨u, hu⟩ := hsourceUnit
      have huE : ((u : A) : E) = x⁻¹ := congrArg Subtype.val hu
      have huInvE : ((↑(u⁻¹) : A) : E) = x := by
        change A.subtype (↑(u⁻¹) : A) = x
        rw [map_units_inv A.subtype u]
        have huE' : A.subtype (u : A) = x⁻¹ := huE
        rw [huE', inv_inv]
      apply hnot
      rw [← huInvE]
      exact (↑(u⁻¹) : A).2
    · intro hx
      exact hcoeff ⟨x, hx⟩
  have hX : RatFunc.X ∈ B := by
    rw [← gaussLocalToRatFunc_X A]
    exact hmem (algebraMap (Polynomial A) (gaussLocalRing A) Polynomial.X)
  have hXunit : IsUnit
      (algebraMap (Polynomial A) (gaussLocalRing A) Polynomial.X) := by
    apply (IsLocalization.AtPrime.isUnit_to_map_iff
      (gaussLocalRing A) (gaussResiduePrime A) Polynomial.X).2
    intro hXker
    change gaussResiduePolynomialMap A Polynomial.X = 0 at hXker
    simpa [gaussResiduePolynomialMap] using hXker
  obtain ⟨u, hu⟩ := hXunit
  have hXinvLocal :
      gaussLocalToRatFunc A (↑(u⁻¹) : gaussLocalRing A) ∈ B :=
    hmem (↑(u⁻¹) : gaussLocalRing A)
  have hXinv : RatFunc.X⁻¹ ∈ B := by
    have huMap : gaussLocalToRatFunc A (u : gaussLocalRing A) = RatFunc.X := by
      rw [hu]
      exact gaussLocalToRatFunc_X A
    have hEq : gaussLocalToRatFunc A (↑(u⁻¹) : gaussLocalRing A) =
        RatFunc.X⁻¹ := by
      rw [map_units_inv (gaussLocalToRatFunc A) u, huMap]
    rw [← hEq]
    exact hXinvLocal
  refine ⟨B, ?_, hX, hXinv⟩
  apply SetLike.ext
  intro x
  exact hEA x

/-- A valuation extends across a free transcendental adjunction while remaining trivial on the
new generator and contracting exactly to the original valuation. -/
theorem exists_valuationSubring_extension_transcendental_unit
    {E K : Type u} [Field E] [Field K] [Algebra E K]
    (A : ValuationSubring E) (x : K) (hx : Transcendental E x) :
    ∃ B : ValuationSubring K,
      B.comap (algebraMap E K) = A ∧ x ∈ B ∧ x⁻¹ ∈ B := by
  obtain ⟨A₀, hA₀, hX, hXinv⟩ :=
    exists_ratFunc_valuationSubring_gaussExtension A
  let L : IntermediateField E K := IntermediateField.adjoin E {x}
  let e : RatFunc E ≃ₐ[E] L :=
    RatFunc.algEquivOfTranscendental x hx
  let f : RatFunc E →+* K :=
    L.val.toRingHom.comp e.toRingHom
  obtain ⟨B, hB⟩ := exists_valuationSubring_extension_comap_eq A₀ f
  have hfC (c : E) :
      f (algebraMap E (RatFunc E) c) = algebraMap E K c := by
    change ((e (algebraMap E (RatFunc E) c) : L) : K) =
      algebraMap E K c
    rw [e.commutes]
    rfl
  have hfX : f RatFunc.X = x := by
    exact RatFunc.algEquivOfTranscendental_X x hx
  have hfXinv : f RatFunc.X⁻¹ = x⁻¹ := by
    calc
      f (RatFunc.X⁻¹) = (f RatFunc.X)⁻¹ := map_inv₀ f RatFunc.X
      _ = x⁻¹ := by rw [hfX]
  have hcomap : B.comap (algebraMap E K) = A := by
    apply SetLike.ext
    intro c
    change algebraMap E K c ∈ B ↔ c ∈ A
    rw [← hfC c]
    change c ∈ (B.comap f).comap (algebraMap E (RatFunc E)) ↔ c ∈ A
    rw [hB, hA₀]
  have hxB : x ∈ B := by
    rw [← hfX]
    change RatFunc.X ∈ B.comap f
    rw [hB]
    exact hX
  have hxinvB : x⁻¹ ∈ B := by
    rw [← hfXinv]
    change RatFunc.X⁻¹ ∈ B.comap f
    rw [hB]
    exact hXinv
  exact ⟨B, hcomap, hxB, hxinvB⟩

/-- A valuation extends across a finite algebraically independent family while remaining trivial
on every generator and contracting exactly to the source valuation. -/
theorem exists_valuationSubring_extension_fin_algebraicIndependent_units
    {E K : Type u} [Field E] [Field K] [Algebra E K]
    {n : ℕ} (A : ValuationSubring E) (x : Fin n → K)
    (hx : AlgebraicIndependent E x) :
    ∃ B : ValuationSubring K,
      B.comap (algebraMap E K) = A ∧
      ∀ i, x i ∈ B ∧ (x i)⁻¹ ∈ B := by
  induction n generalizing K with
  | zero =>
      obtain ⟨B, hB⟩ :=
        exists_valuationSubring_extension_comap_eq A (algebraMap E K)
      exact ⟨B, hB, fun i => Fin.elim0 i⟩
  | succ n ih =>
      let s : Set (Fin (n + 1)) := Set.range Fin.castSucc
      let L : IntermediateField E K := IntermediateField.adjoin E (x '' s)
      letI : IsScalarTower E L K :=
        IsScalarTower.of_algebraMap_eq fun _ => rfl
      let y : Fin n → L := fun i =>
        ⟨x i.castSucc, IntermediateField.subset_adjoin E _
          ⟨i.castSucc, Set.mem_range_self i, rfl⟩⟩
      have hy : AlgebraicIndependent E y := by
        apply AlgebraicIndependent.of_comp L.val
        simpa [y, Function.comp_def] using
          hx.comp Fin.castSucc (Fin.castSucc_injective n)
      obtain ⟨A_L, hA_L, hyUnits⟩ := ih y hy
      have hlast : (Fin.last n : Fin (n + 1)) ∉ s := by
        rintro ⟨i, hi⟩
        exact (Fin.castSucc_lt_last i).ne hi
      have ht : Transcendental L (x (Fin.last n)) := by
        change Transcendental (IntermediateField.adjoin E (x '' s))
          (x (Fin.last n))
        rw [IntermediateField.transcendental_adjoin_iff]
        exact hx.transcendental_adjoin hlast
      obtain ⟨B, hB, hlastB, hlastInvB⟩ :=
        exists_valuationSubring_extension_transcendental_unit
          A_L (x (Fin.last n)) ht
      have hcomap : B.comap (algebraMap E K) = A := by
        rw [← hA_L, ← hB]
        apply SetLike.ext
        intro z
        change algebraMap E K z ∈ B ↔
          algebraMap L K (algebraMap E L z) ∈ B
        rw [IsScalarTower.algebraMap_apply E L K]
      refine ⟨B, hcomap, fun i => ?_⟩
      by_cases hi : i = Fin.last n
      · subst i
        exact ⟨hlastB, hlastInvB⟩
      · let j : Fin n := ⟨i, by
          have hiLe : i.val ≤ n := Nat.le_of_lt_succ i.isLt
          exact lt_of_le_of_ne hiLe (by
            intro hin
            apply hi
            apply Fin.ext
            simpa using hin)⟩
        have hji : j.castSucc = i := Fin.ext rfl
        obtain ⟨hyj, hyjInv⟩ := hyUnits j
        have hyjB : algebraMap L K (y j) ∈ B := by
          change y j ∈ B.comap (algebraMap L K)
          rw [hB]
          exact hyj
        have hyjInvB : (algebraMap L K (y j))⁻¹ ∈ B := by
          rw [← map_inv₀]
          change (y j)⁻¹ ∈ B.comap (algebraMap L K)
          rw [hB]
          exact hyjInv
        simpa [y, hji] using And.intro hyjB hyjInvB

end

end GaloisForLFunctions.HTGeometry
